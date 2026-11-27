import ConventionTrap.Analyze

/-!
# CI report `trap/report@1` (JSON + Markdown)
-/

namespace ConventionTrap
open Lean

structure Pos2 where
  line : Nat
  col : Nat
  deriving Inhabited

structure ReportFinding where
  finding : Finding
  file : String
  start : Pos2
  stop : Pos2
  deriving Inhabited

structure SuppressedEntry where
  decl : Name
  kinds : Array TrapKind
  reason : String
  file : String
  findings : Nat

structure ReportInputs where
  repo : String
  commit : Option String
  toolchain : String
  mathlibCommit : Option String
  mode : Mode

structure Report where
  inputs : ReportInputs
  declsChecked : Nat
  discharged : Nat
  findings : Array ReportFinding
  benign : Array ReportFinding
  unknown : Array ReportFinding
  suppressed : Array SuppressedEntry

def toolVersion : String := "0.1.0"

def optStr : Option String → Json
  | some s => Json.str s
  | none => Json.null

def findingJson (r : ReportFinding) : Json :=
  let f := r.finding
  Json.mkObj [
    ("decl", Json.str f.decl.toString),
    ("file", Json.str r.file),
    ("range", Json.mkObj [
      ("start", Json.mkObj [("line", r.start.line), ("col", r.start.col)]),
      ("end", Json.mkObj [("line", r.stop.line), ("col", r.stop.col)])]),
    ("kind", Json.str f.kind.toString),
    ("severity", Json.str f.severity.toString),
    ("verdict", Json.str f.verdict.toString),
    ("expr_pp", Json.str f.exprPP),
    ("condition_pp", optStr f.conditionPP),
    ("counterexample", if f.counterexample.isEmpty then Json.null else
      Json.mkObj (f.counterexample.toList.map fun (k, v) => (k, Json.str v))),
    ("tactics_tried", Json.arr (f.tacticsTried.map Json.str)),
    ("message", Json.str f.message)]

def sortFindings (xs : Array ReportFinding) : Array ReportFinding :=
  xs.qsort fun a b =>
    if a.file != b.file then a.file < b.file
    else if a.start.line != b.start.line then a.start.line < b.start.line
    else if a.start.col != b.start.col then a.start.col < b.start.col
    else if a.finding.kind.toString != b.finding.kind.toString then
      a.finding.kind.toString < b.finding.kind.toString
    else a.finding.exprPP < b.finding.exprPP

def Report.toJson (r : Report) : Json :=
  let errors := r.findings.filter (·.finding.severity == .error)
  let warnings := r.findings.filter (·.finding.severity == .warning)
  Json.mkObj [
    ("schema", "trap/report@1"),
    ("tool", Json.mkObj [("name", "convention-trap"), ("version", toolVersion)]),
    ("inputs", Json.mkObj [
      ("repo", Json.str r.inputs.repo), ("commit", optStr r.inputs.commit),
      ("toolchain", Json.str r.inputs.toolchain),
      ("mathlib_commit", optStr r.inputs.mathlibCommit),
      ("mode", Json.str r.inputs.mode.toString)]),
    ("summary", Json.mkObj [
      ("decls_checked", r.declsChecked), ("errors", errors.size), ("warnings", warnings.size),
      ("unknown", r.unknown.size), ("benign", r.benign.size),
      ("suppressed", r.suppressed.size), ("discharged", r.discharged)]),
    ("findings", Json.arr ((sortFindings r.findings).map findingJson)),
    ("unknown", Json.arr ((sortFindings r.unknown).map findingJson)),
    ("benign", Json.arr ((sortFindings r.benign).map findingJson)),
    ("suppressed", Json.arr (r.suppressed.map fun s => Json.mkObj [
      ("decl", Json.str s.decl.toString), ("file", Json.str s.file),
      ("kinds", Json.arr (s.kinds.map (Json.str ·.toString))),
      ("reason", Json.str s.reason), ("findings", s.findings)])),
    ("timeouts", Json.arr ((sortFindings (r.findings ++ r.unknown)).filter (·.finding.timeout)
      |>.map fun x => Json.mkObj [("decl", Json.str x.finding.decl.toString),
        ("kind", Json.str x.finding.kind.toString), ("condition_pp", optStr x.finding.conditionPP)]))]

def mdEscape (s : String) : String :=
  (s.replace "|" "\\|").replace "\n" " "

def firstLine (s : String) : String := (s.splitOn "\n").headD s

def Report.toMarkdown (r : Report) : String := Id.run do
  let fs := sortFindings r.findings
  let errors := fs.filter (·.finding.severity == .error)
  let warnings := fs.filter (·.finding.severity == .warning)
  let mut out := "# Convention trap report\n\n"
  out := out ++ s!"**{errors.size} errors · {warnings.size} warnings · {r.unknown.size} unknown · " ++
    s!"{r.suppressed.size} suppressed** — {r.declsChecked} declarations checked, " ++
    s!"{r.discharged} sites discharged, {r.benign.size} benign (mode `{r.inputs.mode.toString}`)\n\n"
  out := out ++ "## Errors (statement is false)\n\n"
  if errors.isEmpty then out := out ++ "_none_\n\n" else
    out := out ++ "| decl | location | kind | counterexample | message |\n|---|---|---|---|---|\n"
    for e in errors do
      let f := e.finding
      let cx := ", ".intercalate (f.counterexample.toList.map fun (k, v) => s!"{k} = {v}")
      out := out ++ s!"| `{f.decl}` | {e.file}:{e.start.line} | {f.kind} | {cx} | {mdEscape (firstLine f.message)} |\n"
    out := out ++ "\n"
  out := out ++ "## Warnings\n\n"
  if warnings.isEmpty then out := out ++ "_none_\n\n" else
    let files := warnings.foldl (fun acc w => if acc.contains w.file then acc else acc.push w.file) #[]
    for file in files do
      out := out ++ s!"### {file}\n\n| decl | line | kind | expression | unproved condition | example |\n|---|---|---|---|---|---|\n"
      for w in warnings.filter (·.file == file) do
        let f := w.finding
        let cx := ", ".intercalate (f.counterexample.toList.map fun (k, v) => s!"{k} = {v}")
        out := out ++ s!"| `{f.decl}` | {w.start.line} | {f.kind} | `{mdEscape f.exprPP}` | `{mdEscape (f.conditionPP.getD "")}` | {cx} |\n"
      out := out ++ "\n"
  if !r.unknown.isEmpty then
    out := out ++ "## Unknown (condition neither proved nor witnessed)\n\n| decl | location | kind | expression | condition |\n|---|---|---|---|---|\n"
    for u in sortFindings r.unknown do
      let f := u.finding
      out := out ++ s!"| `{f.decl}` | {u.file}:{u.start.line} | {f.kind} | `{mdEscape f.exprPP}` | `{mdEscape (f.conditionPP.getD "")}` |\n"
    out := out ++ "\n"
  out := out ++ "## Suppressed (`@[trap_ok]`)\n\n"
  if r.suppressed.isEmpty then out := out ++ "_none_\n" else
    out := out ++ "| decl | kinds | reason | hidden findings |\n|---|---|---|---|\n"
    for s in r.suppressed do
      let ks := ", ".intercalate (s.kinds.toList.map (·.toString))
      out := out ++ s!"| `{s.decl}` | {ks} | {mdEscape s.reason} | {s.findings} |\n"
  return out

end ConventionTrap
