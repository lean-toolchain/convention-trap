import ConventionTrap

/-!
# `lake exe trap-report`

```
lake exe trap-report [--modules <Mod,...>] [--decls <Name,...>] [--mode ci|editor]
                     [--format md|json|both] [--out-dir trap-report/] [--fail-on error|warning|never]
                     [--no-witness] [--no-benign] [--no-self-guard] [--unfold-depth N]
```
Exit codes: 0 ok · 1 `--fail-on` met · 2 usage error · 4 target not built / import failed.
-/

open Lean Meta Elab ConventionTrap

structure Args where
  modules : Array Name := #[]
  decls : Array Name := #[]
  mode : Mode := .ci
  format : String := "both"
  outDir : System.FilePath := "trap-report"
  failOn : String := "error"
  witness : Bool := true
  benign : Bool := true
  selfGuard : Bool := true
  unfoldDepth : Option Nat := none
  /-- Modules to import (default: `modules`). With `--prefix`, decls are selected by module prefix. -/
  imports : Array Name := #[]
  prefixes : Array Name := #[]
  /-- `--shard k/n`: keep targets whose hash ≡ k (mod n). -/
  shard : Nat × Nat := (0, 1)
  /-- `--sample-mod m`: keep targets whose hash ≡ 0 (mod m) (after sharding, independent hash). -/
  sampleMod : Nat := 1
  progress : Bool := false
  trustProofs : Bool := true

def usage : String :=
  "usage: trap-report [--modules M,...] [--decls N,...] [--mode ci|editor] [--format md|json|both]\n" ++
  "                   [--out-dir DIR] [--fail-on error|warning|never]\n" ++
  "                   [--no-witness] [--no-benign] [--no-self-guard] [--unfold-depth N]\n" ++
  "                   [--import M,...] [--prefix P,...] [--shard K/N] [--sample-mod M] [--progress] [--no-trust-proofs]"

def splitNames (s : String) : Array Name :=
  (s.splitOn ",").toArray.filter (!·.isEmpty) |>.map String.toName

partial def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--modules" :: v :: rest, a => parseArgs rest { a with modules := splitNames v }
  | "--decls" :: v :: rest, a => parseArgs rest { a with decls := splitNames v }
  | "--mode" :: v :: rest, a => match Mode.ofString? v with
    | some m => parseArgs rest { a with mode := m }
    | none => .error s!"bad --mode {v}"
  | "--format" :: v :: rest, a =>
    if ["md", "json", "both"].contains v then parseArgs rest { a with format := v }
    else .error s!"bad --format {v}"
  | "--out-dir" :: v :: rest, a => parseArgs rest { a with outDir := v }
  | "--fail-on" :: v :: rest, a =>
    if ["error", "warning", "never"].contains v then parseArgs rest { a with failOn := v }
    else .error s!"bad --fail-on {v}"
  | "--no-witness" :: rest, a => parseArgs rest { a with witness := false }
  | "--no-benign" :: rest, a => parseArgs rest { a with benign := false }
  | "--no-self-guard" :: rest, a => parseArgs rest { a with selfGuard := false }
  | "--unfold-depth" :: v :: rest, a => match v.toNat? with
    | some n => parseArgs rest { a with unfoldDepth := some n }
    | none => .error s!"bad --unfold-depth {v}"
  | "--import" :: v :: rest, a => parseArgs rest { a with imports := splitNames v }
  | "--prefix" :: v :: rest, a => parseArgs rest { a with prefixes := splitNames v }
  | "--shard" :: v :: rest, a => match v.splitOn "/" with
    | [k, n] => match k.toNat?, n.toNat? with
      | some k, some n => if k < n then parseArgs rest { a with shard := (k, n) } else .error s!"bad --shard {v}"
      | _, _ => .error s!"bad --shard {v}"
    | _ => .error s!"bad --shard {v}"
  | "--sample-mod" :: v :: rest, a => match v.toNat? with
    | some m => if m > 0 then parseArgs rest { a with sampleMod := m } else .error "bad --sample-mod"
    | none => .error s!"bad --sample-mod {v}"
  | "--no-trust-proofs" :: rest, a => parseArgs rest { a with trustProofs := false }
  | "--progress" :: rest, a => parseArgs rest { a with progress := true }
  | x :: _, _ => .error s!"unknown argument {x}"

/-- Modules built in `./.lake/build/lib/lean` (the current package). -/
partial def builtModules : IO (Array Name) := do
  let root : System.FilePath := ".lake/build/lib/lean"
  unless ← root.pathExists do return #[]
  let files ← root.walkDir
  let mut out := #[]
  for f in files do
    if f.extension == some "olean" then
      let rel := (f.toString.drop (root.toString.length + 1)).toString
      let comps := (rel.dropEnd 6).toString.splitOn "/"
      let n := comps.foldl (fun acc c => Name.str acc c) Name.anonymous
      unless n == `Main || (`ConventionTrap).isPrefixOf n do out := out.push n
  return out.qsort Name.lt

def modPath (m : Name) : String :=
  "/".intercalate (m.components.map (·.toString)) ++ ".lean"

def gitCommit : IO (Option String) := do
  try
    let o ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
    return if o.exitCode == 0 then some o.stdout.trimAscii.toString else none
  catch _ => return none

def mathlibCommit : IO (Option String) := do
  try
    let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile "lake-manifest.json")
    let pkgs ← IO.ofExcept <| j.getObjValAs? (Array Json) "packages"
    for p in pkgs do
      if (p.getObjValAs? String "name").toOption == some "mathlib" then
        return (p.getObjValAs? String "rev").toOption
    return none
  catch _ => return none

def isChecked (env : Environment) (n : Name) (ci : ConstantInfo) : MetaM Bool := do
  if n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n then return false
  if ← isInstance n then return false
  match ci with
  | .thmInfo _ | .axiomInfo _ => return true
  | .defnInfo d => forallTelescopeReducing d.type fun _ b => return (← whnfR b).isProp
  | _ => return false

unsafe def main (argv : List String) : IO UInt32 := do
  let args ← match parseArgs argv {} with
    | .ok a => pure a
    | .error e => IO.eprintln s!"{e}\n{usage}"; return 2
  let modules ← if args.modules.isEmpty && args.prefixes.isEmpty then builtModules else pure args.modules
  let imports := if args.imports.isEmpty then modules else args.imports
  if imports.isEmpty then
    IO.eprintln "trap-report: no modules (build the target first or pass --modules)"; return 4
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← try importModules (imports.map ({ module := · })) {} (trustLevel := 1024) (loadExts := true)
    catch e => IO.eprintln s!"trap-report: import failed: {e}"; return 4
  let modSet := modules.foldl (fun s m => s.insert m) ({} : Std.HashSet Name)
  let cfg : TrapConfig := {
    mode := args.mode, trustProofs := args.trustProofs, witness := args.witness, benign := args.benign, selfGuard := args.selfGuard,
    unfoldDepth := args.unfoldDepth.getD (if args.mode == .ci then 2 else 1),
    showUnknown := args.mode == .ci }
  let opts : Options := {}
  let coreCtx : Core.Context := {
    fileName := "<trap-report>", fileMap := default, options := opts, maxHeartbeats := 0 }
  let job : TermElabM Report := do
    let env ← getEnv
    let mut targets : Array (Name × Name) := #[]
    for (n, ci) in env.constants.map₁.toList do
      let some idx := env.getModuleIdxFor? n | continue
      let mod := env.header.moduleNames[idx.toNat]!
      unless modSet.contains mod || args.prefixes.any (·.isPrefixOf mod) do continue
      let h := hash n
      unless (h % args.shard.2.toUInt64).toNat == args.shard.1 do continue
      unless (mixHash h 0x9e3779b97f4a7c15 % args.sampleMod.toUInt64) == 0 do continue
      unless args.decls.isEmpty || args.decls.contains n do continue
      if ← isChecked env n ci then targets := targets.push (n, mod)
    targets := targets.qsort fun a b => Name.lt a.1 b.1
    let mut findings := #[]
    let mut benign := #[]
    let mut unknown := #[]
    let mut suppressed := #[]
    let mut discharged := 0
    let total := targets.size
    let mut i := 0
    for (n, mod) in targets do
      i := i + 1
      if args.progress && (total ≤ 500 || i % 200 == 0) then
        IO.println s!"trap-report: {i}/{total} ({n})"
        (← IO.getStdout).flush
      let res ← try analyzeDecl n cfg catch _ => pure {}
      discharged := discharged + res.discharged
      let file := modPath mod
      let (start, stop) ← match ← findDeclarationRanges? n with
        | some r => pure (Pos2.mk r.selectionRange.pos.line r.selectionRange.pos.column,
                          Pos2.mk r.selectionRange.endPos.line r.selectionRange.endPos.column)
        | none => pure (⟨0, 0⟩, ⟨0, 0⟩)
      let sup := getSuppression env n
      let mut hidden := 0
      for f in res.findings do
        let rf : ReportFinding := { finding := f, file, start, stop }
        if sup.any (·.1.contains f.kind) && f.verdict != .benign then
          hidden := hidden + 1
          continue
        match f.verdict, f.severity with
        | .benign, _ => benign := benign.push rf
        | .unknown, .info => unknown := unknown.push rf
        | _, _ => findings := findings.push rf
      if let some (kinds, reason) := sup then
        suppressed := suppressed.push { decl := n, kinds, reason, file, findings := hidden }
    return {
      inputs := { repo := "", commit := none, toolchain := Lean.versionString,
                  mathlibCommit := none, mode := args.mode }
      declsChecked := targets.size, discharged, findings, benign, unknown, suppressed }
  let (report, _) ← (job.run'.run').toIO coreCtx { env }
  let cwd ← IO.currentDir
  let report := { report with inputs := { report.inputs with
    repo := cwd.fileName.getD cwd.toString, commit := ← gitCommit, mathlibCommit := ← mathlibCommit } }
  IO.FS.createDirAll args.outDir
  if args.format != "md" then
    IO.FS.writeFile (args.outDir / "report.json") (report.toJson.pretty ++ "\n")
  if args.format != "json" then
    IO.FS.writeFile (args.outDir / "report.md") report.toMarkdown
  let errors := report.findings.filter (·.finding.severity == .error) |>.size
  let warnings := report.findings.filter (·.finding.severity == .warning) |>.size
  IO.println s!"trap-report: {report.declsChecked} decls, {errors} errors, {warnings} warnings, {report.unknown.size} unknown, {report.benign.size} benign, {report.discharged} discharged, {report.suppressed.size} suppressed → {args.outDir}"
  let fail : Bool := match args.failOn with
    | "error" => errors > 0
    | "warning" => errors + warnings > 0
    | _ => false
  return if fail then 1 else 0
