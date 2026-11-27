import ConventionTrap.Detect
import ConventionTrap.Solve
import ConventionTrap.Suppress

/-!
# `analyzeDecl`: detect → discharge → benign → witness, plus whole-statement refutation

Verdicts (algorithm-improvements.md):
* `safe`      condition proved from local hypotheses — not reported (counted in `discharged`)
* `benign`    statement still provable in the junk region — hidden, kept for the CI report
* `reachable` concrete values satisfy every hypothesis and break the condition — warning
* `unknown`   neither — info (warning when witness search is disabled, i.e. baseline mode)
* `false_`    counterexample to the whole statement — error (`natZero` / `falseStatement`)
-/

namespace ConventionTrap
open Lean Meta Elab Term

structure AnalysisResult where
  findings : Array Finding := #[]
  discharged : Nat := 0
  deriving Inhabited

def junkDescription : TrapKind → String
  | .natSub | .natSubHyp | .expTrunc | .castSub => "0으로 잘립니다"
  | .div => "0입니다 (x / 0 = 0, 0⁻¹ = 0)"
  | .intDiv => "버림한 몫이 됩니다"
  | .modZero => "a % 0 = a 입니다"
  | .intDivNeg => "-∞ 방향으로 내림됩니다 (예: -7 / 2 = -4)"
  | .realDomain => "Mathlib 관례값입니다 (√x = 0 (x < 0), log 0 = 0, log (-x) = log x)"
  | .rpow => "음수 밑에서 복소 정의의 실수부가 됩니다"
  | .intToNat => "0입니다"
  | .natZero | .falseStatement => ""

def assignStr (σ : Array (Name × Candidate)) : String :=
  ", ".intercalate (σ.toList.map fun (n, c) => s!"{n} = {c.display}")

def searchCfg (cfg : TrapConfig) (forWitness : Bool) : SearchCfg :=
  let ci := cfg.mode == .ci
  { natBase := if forWitness then #[0, 1, 2] else if ci then #[0, 1, 2, 3, 4] else #[0, 1]
    intBase := if forWitness then #[-1, 0, 1, 2] else if ci then #[-2, -1, 0, 1, 2] else #[-1, 0, 1]
    allowReal := forWitness
    maxVars := cfg.refuteMaxVars
    maxTuples := if ci then 4096 else 256
    seed := cfg.plausibleSeed
    heartbeats := min cfg.heartbeats 5000 }

/-- Analyze one trap site. Returns `none` when safe. -/
def analyzeSite (decl : Name) (site : TrapSite) (cfg : TrapConfig) (budgetLeft : Bool) :
    TermElabM (Option Finding) := do
  let base : Finding := {
    decl, kind := site.kind, severity := .warning, verdict := .unknown, exprPP := site.exprPP,
    conditionPP := some site.condPP, message := "", head := site.head,
    suggestedHyps := if site.suggestable then #[site.condPP] else #[],
    suggestVars := site.condVars }
  let head := s!"[{site.kind}] {site.exprPP} : {site.typePP} 는 {site.violPP}일 때 {junkDescription site.kind}"
  if !budgetLeft then
    return some { base with
      timeout := true, message := s!"{head}. 선언당 시간 예산을 넘어 {site.condPP}를 증명하지 않았습니다." }
  -- 1. discharge
  let mut tried := #[]
  let mut timedOut := false
  for t in cfg.tacticList do
    let some tac ← dischargeTactic t | continue
    tried := tried.push t.toString
    let r ← tryClose site.goal tac cfg.heartbeats
    if r.closed then return none
    timedOut := timedOut || r.timedOut
  let triedJoined := ", ".intercalate tried.toList
  let triedStr := s!"시도: {triedJoined} (각 실패)"
  let base := { base with tacticsTried := tried, timeout := timedOut }
  -- 2. benign
  if cfg.benign then
    if let some bg := site.benignGoal? then
      for tac in ← benignTactics do
        if (← tryClose bg tac cfg.heartbeats).closed then
          return some { base with
            verdict := .benign, severity := .info, message := s!"{head}. 그러나 그 영역에서도 명제가 성립합니다 (benign)." }
  -- 3. witness
  if cfg.witness then
    if let some σ ← findAssignment site.goal (searchCfg cfg true) then
      return some { base with
        verdict := .reachable, severity := .warning, counterexample := σ.map fun (n, c) => (n.toString, c.display),
        message := s!"{head}. 가정에서 {site.condPP}를 증명하지 못했습니다.\n  예: {assignStr σ} 일 때 가정을 모두 만족하고 {site.violPP} 입니다.\n  {triedStr}" }
  let sev := if cfg.witness then Severity.info else .warning
  return some { base with
    verdict := .unknown, severity := sev, message := s!"{head}. 가정에서 {site.condPP}를 증명하지 못했습니다 (반례 값도 찾지 못함).\n  {triedStr}" }

/-- Whole-statement refutation (natZero / falseStatement). -/
def refute (decl : Name) (stmt : Expr) (cfg : TrapConfig) : TermElabM (Option Finding) := do
  unless cfg.enabled .natZero do return none
  let some σ ← findAssignment stmt (searchCfg cfg false) | return none
  let zeros := σ.filter fun (_, c) => c.isZero
  let kind := if zeros.isEmpty then TrapKind.falseStatement else .natZero
  let zeroHyps := ", ".intercalate (zeros.toList.map fun (n, _) => s!"0 < {n}")
  let hint := if zeros.isEmpty then "" else s!" {zeroHyps} 를 의도했나요?"
  return some {
    decl, kind, severity := .error, verdict := .false_, exprPP := ← ppStr stmt,
    counterexample := σ.map fun (n, c) => (n.toString, c.display),
    message := s!"[{kind}] 명제가 거짓입니다: {assignStr σ} 에서 결론이 거짓입니다.{hint}",
    suggestedHyps := zeros.map fun (n, _) => s!"0 < {n}",
    suggestVars := zeros.map (·.1) }

/-- The statement checked for a constant: theorem type, or body of a Prop-valued def. -/
def statementOf (ci : ConstantInfo) : MetaM (Option (Expr × Bool)) := do
  match ci with
  | .thmInfo t => return some (t.type, t.value.hasSorry)
  | .axiomInfo a => return some (a.type, true)
  | .defnInfo d =>
    let isPropDef ← forallTelescopeReducing d.type fun _ b => return (← whnfR b).isProp
    if isPropDef then
      let body ← lambdaTelescope d.value fun xs b => mkForallFVars xs b
      return some (body, false)
    return none
  | _ => return none

def analyzeStatement (decl : Name) (stmt : Expr) (tryRefute : Bool) (cfg : TrapConfig) :
    TermElabM AnalysisResult := do
  let sites ← detect stmt {
    selfGuard := cfg.selfGuard, benign := cfg.benign,
    unfoldDepth := cfg.unfoldDepth, enabled := cfg.enabled }
  let mut res : AnalysisResult := {}
  let mut used := 0
  for site in sites do
    let budgetLeft := cfg.mode == .ci || used + cfg.heartbeats ≤ cfg.declBudget
    used := used + cfg.heartbeats
    match ← analyzeSite decl site cfg budgetLeft with
    | none => res := { res with discharged := res.discharged + 1 }
    | some f => res := { res with findings := res.findings.push f }
  -- Shared subexpressions are analysed at every occurrence (each has its own hypotheses)
  -- but reported once, keeping the most severe verdict.
  let rank : Verdict → Nat
    | .false_ => 4 | .reachable => 3 | .unknown => 2 | .benign => 1 | .safe => 0
  let mut merged : Array Finding := #[]
  for f in res.findings do
    match merged.findIdx? (fun g => g.kind == f.kind && g.exprPP == f.exprPP) with
    | some i => if rank f.verdict > rank merged[i]!.verdict then merged := merged.set! i f
    | none => merged := merged.push f
  res := { res with findings := merged }
  if tryRefute then
    if let some f ← refute decl stmt cfg then
      res := { res with findings := #[f] ++ res.findings }
  return res

/-- Analyze a declaration. Refutation is attempted only when the statement is not proved
(it uses `sorry`, or is an axiom): a sorry-free theorem cannot have a counterexample. -/
def analyzeDecl (declName : Name) (cfg : TrapConfig) : TermElabM AnalysisResult := do
  let some ci := (← getEnv).find? declName | return {}
  let some (stmt, unproved) ← statementOf ci | return {}
  -- A Prop definition asserts nothing, so "still true in the junk region" is no evidence of
  -- harmlessness: benign classification only applies to claimed statements.
  let cfg := if ci.isDefinition then { cfg with benign := false } else cfg
  analyzeStatement declName stmt unproved cfg

end ConventionTrap
