import ConventionTrap.Analyze
import ConventionTrap.Options

/-!
# The convention trap linter (editor and `lake build` diagnostics)

Checked declarations: `theorem`, `lemma`, and `def`/`abbrev` whose value is a `Prop`.
`instance` and `example` are skipped. Only the statement is inspected, never the proof.

* counterexample → `error`
* reachable (concrete witness) → linter `warning` (with the disable note)
* unknown → `info` when `showUnknown` (warning in baseline mode `witness := false`)
* benign / safe → nothing
-/

namespace ConventionTrap
open Lean Elab Command Linter Meta

def sigKinds : List SyntaxNodeKind :=
  [``Lean.Parser.Command.declSig, ``Lean.Parser.Command.optDeclSig]

/-- `(declId, signature)` pairs of a declaration command, skipping `instance`/`example`. -/
def declTargets (stx : Syntax) : Array (Syntax × Syntax) := Id.run do
  let k := stx.getKind
  unless k == ``Lean.Parser.Command.declaration || k.getString! == "lemma" do return #[]
  let decl := if k == ``Lean.Parser.Command.declaration then stx[1] else stx
  if decl.getKind == ``Lean.Parser.Command.instance ||
     decl.getKind == ``Lean.Parser.Command.example then return #[]
  let some declId := decl.find? (·.isOfKind ``Lean.Parser.Command.declId) | return #[]
  let some sig := decl.find? (fun s => sigKinds.contains s.getKind) | return #[]
  return #[(declId, sig)]

def sliceSource (src : String) (a b : String.Pos.Raw) : String :=
  String.fromUTF8! (src.toUTF8.extract a.byteIdx b.byteIdx)

def inRange (inner outer : Syntax) : Bool :=
  match inner.getPos? true, inner.getTailPos? true, outer.getPos?, outer.getTailPos? with
  | some a, some b, some c, some d => c.byteIdx ≤ a.byteIdx && b.byteIdx ≤ d.byteIdx
  | _, _, _, _ => false

/-- Find the syntax of the trap subexpression in the signature via the info trees. -/
def locateFinding (f : Finding) (sig : Syntax) : CommandElabM (Option Syntax) := do
  if f.head.isAnonymous then return none
  let trees ← getInfoTrees
  let mut cands : Array (ContextInfo × TermInfo) := #[]
  for t in trees do
    cands := t.foldInfo (init := cands) fun ctx info acc =>
      match info with
      | .ofTermInfo ti => if inRange ti.stx sig then acc.push (ctx, ti) else acc
      | _ => acc
  for (ctx, ti) in cands do
    let check : MetaM Bool := do
      let e ← instantiateMVars ti.expr
      if e.consumeMData.getAppFn.constName? != some f.head then return false
      return (← ppStr e) == f.exprPP
    let ok : Bool ← try ctx.runMetaM ti.lctx check catch _ => pure false
    if ok then return some ti.stx
  return none

/-- Binder names written in the signature (before the colon). -/
def sigBinderNames (sig : Syntax) : Array Name := Id.run do
  let binders := sig[0]
  let mut out := #[]
  for b in binders.getArgs do
    for s in b.getArgs do
      for id in s.getArgs.push s do
        if id.isIdent then out := out.push id.getId
  return out

/-- Signature text with extra hypotheses inserted before the `:`. -/
def suggestedSignature (sig : Syntax) (hyps : Array (String × String)) : CommandElabM (Option String) := do
  let src := (← getFileMap).source
  let some s := sig.getPos? | return none
  let some e := sig.getTailPos? | return none
  let typeSpec := sig[1]
  let some t := typeSpec.getPos? | return none
  let binderText := (sliceSource src s t).trimAsciiEnd.toString
  let typeText := sliceSource src t e
  let extra := " ".intercalate (hyps.toList.map fun (n, h) => s!"({n} : {h})")
  let sep := if binderText.isEmpty then "" else " "
  return some s!"{binderText}{sep}{extra} {typeText}"

def emitFinding (f : Finding) (declId sig : Syntax) (cfg : TrapConfig) : CommandElabM Unit := do
  let show? := match f.verdict with
    | .false_ | .reachable => true
    | .unknown => !cfg.witness || cfg.showUnknown || f.timeout
    | .benign | .safe => false
  unless show? do return
  let ref := (← locateFinding f sig).getD declId
  match f.severity with
  | .error => logErrorAt ref f.message
  | .warning => logLint linter.conventionTrap ref f.message
  | .info => logInfoAt ref f.message
  -- quick fix: add hypotheses (only if every variable is a signature binder)
  if !f.suggestedHyps.isEmpty then
    let names := sigBinderNames sig
    if f.suggestVars.all names.contains then
      let hyps := if f.kind == .natZero then
          f.suggestedHyps.zipWith (fun h n => (s!"h_pos_{n}", h)) f.suggestVars
        else f.suggestedHyps.map (("h_trap", ·))
      if let some newSig ← suggestedSignature sig hyps then
        liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion sig
          (newSig : Lean.Meta.Tactic.TryThis.SuggestionText) (origSpan? := some sig)
          (header := s!"빠른 수정 [{f.kind}]: ")

def conventionTrapLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterValue linter.conventionTrap (← getLinterOptions) do return
    if (← get).messages.hasErrors then return
    let targets := declTargets stx
    if targets.isEmpty then return
    let cfg := configOfOptions (← getOptions)
    for (declId, sig) in targets do
      let some name ← (try some <$> liftCoreM (realizeGlobalConstNoOverload declId[0])
          catch _ => pure none) | continue
      let suppressed := (getSuppression (← getEnv) name).map (·.1) |>.getD #[]
      let res ← liftTermElabM <| analyzeDecl name cfg
      for f in res.findings do
        unless suppressed.contains f.kind do
          emitFinding f declId sig cfg

initialize addLinter conventionTrapLinter

end ConventionTrap

namespace ConventionTrap
open Lean Elab Command

/-- `#trap_check foo` prints every finding of `foo` (including benign/unknown) in compact form,
followed by the number of discharged sites. Used for tests and debugging. -/
syntax (name := trapCheck) "#trap_check " ident : command

@[command_elab trapCheck] def elabTrapCheck : CommandElab := fun stx => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let cfg := configOfOptions (← getOptions)
  let res ← liftTermElabM <| analyzeDecl name cfg
  let lines := res.findings.map fun f =>
    let cx := if f.counterexample.isEmpty then "" else
      " {" ++ ", ".intercalate (f.counterexample.toList.map fun (k, v) => s!"{k}={v}") ++ "}"
    let cond := match f.conditionPP with | some c => s!" ⊢ {c}" | none => ""
    s!"{f.kind} {f.verdict.toString}: {f.exprPP}{cond}{cx}"
  let sup := match getSuppression (← getEnv) name with
    | some (ks, r) => s!"\nsuppressed {ks.map (·.toString)}: {r}" | none => ""
  logInfoAt stx[1] m!"{"\n".intercalate lines.toList}{if lines.isEmpty then "" else "\n"}discharged: {res.discharged}{sup}"

end ConventionTrap
