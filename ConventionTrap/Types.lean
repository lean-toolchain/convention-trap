import Lean

/-!
# Convention Trap Detector: core types

`TrapKind` identifiers are shared by messages, attributes, options and JSON output.
-/

namespace ConventionTrap
open Lean

/-- Kinds of Mathlib convention traps (MVP list). -/
inductive TrapKind where
  | natSub | natSubHyp | div | intDiv | modZero | intDivNeg | realDomain | rpow
  | castSub | natZero | intToNat | expTrunc | falseStatement | trivialWitness
  | sSupInf | card | diam | deriv | piOrder | finWrap | zmodZero
  deriving Inhabited, BEq, DecidableEq, Repr, Hashable, Ord

namespace TrapKind

def all : Array TrapKind :=
  #[natSub, natSubHyp, div, intDiv, modZero, intDivNeg, realDomain, rpow, castSub, natZero,
    intToNat, expTrunc, falseStatement, trivialWitness,
    sSupInf, card, diam, deriv, piOrder, finWrap, zmodZero]

def toString : TrapKind → String
  | natSub => "natSub" | natSubHyp => "natSubHyp" | div => "div" | intDiv => "intDiv"
  | modZero => "modZero" | intDivNeg => "intDivNeg" | realDomain => "realDomain"
  | rpow => "rpow" | castSub => "castSub" | natZero => "natZero" | intToNat => "intToNat"
  | expTrunc => "expTrunc" | falseStatement => "falseStatement"
  | trivialWitness => "trivialWitness"
  | sSupInf => "sSupInf" | card => "card" | diam => "diam" | deriv => "deriv"
  | piOrder => "piOrder" | finWrap => "finWrap" | zmodZero => "zmodZero"

instance : ToString TrapKind := ⟨TrapKind.toString⟩

def ofString? (s : String) : Option TrapKind := all.find? (·.toString == s)

/-- Option that toggles this kind. Several kinds share an umbrella option (PRD's six groups). -/
def optionName : TrapKind → Name
  | natSubHyp | expTrunc => `linter.conventionTrap.natSub
  | modZero | intDivNeg => `linter.conventionTrap.intDiv
  | rpow | intToNat => `linter.conventionTrap.realDomain
  | falseStatement | trivialWitness => `linter.conventionTrap.natZero
  | sSupInf | card | diam | deriv => `linter.conventionTrap.junkFun
  | piOrder | finWrap | zmodZero => `linter.conventionTrap.leanOps
  | k => `linter.conventionTrap ++ Name.mkSimple k.toString

/-- Kinds whose variables are sets/functions: no concrete witness can be built, so an unproved
condition that is not benign is reported as a warning directly. -/
def isStructural : TrapKind → Bool
  | sSupInf | card | diam | deriv | piOrder | finWrap => true
  | _ => false

/-- Is this kind decided only by refutation (no syntactic site)? -/
def isRefutation : TrapKind → Bool
  | natZero | falseStatement => true
  | _ => false

end TrapKind

inductive Severity where
  | error | warning | info
  deriving Inhabited, BEq, Repr

def Severity.toString : Severity → String
  | .error => "error" | .warning => "warning" | .info => "info"

/-- Verdict of a trap site (algorithm-improvements.md). -/
inductive Verdict where
  | safe | benign | reachable | unknown | false_
  deriving Inhabited, BEq, Repr

def Verdict.toString : Verdict → String
  | .safe => "safe" | .benign => "benign" | .reachable => "reachable"
  | .unknown => "unknown" | .false_ => "false"

inductive Mode where
  | editor | ci
  deriving Inhabited, BEq, Repr

def Mode.ofString? : String → Option Mode
  | "editor" => some .editor | "ci" => some .ci | _ => none

def Mode.toString : Mode → String
  | .editor => "editor" | .ci => "ci"

structure TrapConfig where
  /-- Budget per condition, in `maxHeartbeats` units (×1000). -/
  heartbeats      : Nat := 20000
  /-- Tactics tried in order. Empty means "mode default". -/
  tactics         : Array Name := #[]
  refuteMaxVars   : Nat := 4
  plausibleSeed   : Nat := 0
  unfoldDepth     : Nat := 1
  enabled         : TrapKind → Bool := fun _ => true
  mode            : Mode := .editor
  witness         : Bool := true
  benign          : Bool := true
  selfGuard       : Bool := true
  showUnknown     : Bool := false
  /-- Total budget per declaration in editor mode (sites × heartbeats). -/
  declBudget      : Nat := 200000
  deriving Inhabited

def TrapConfig.tacticList (cfg : TrapConfig) : Array Name :=
  if !cfg.tactics.isEmpty then cfg.tactics
  else match cfg.mode with
    | .editor => #[`assumption, `omega, `positivity]
    | .ci => #[`assumption, `omega, `positivity, `linarith, `nlinarith, `simp_arith, `grind]

/-- One reported (or suppressed / benign) result. -/
structure Finding where
  decl          : Name
  kind          : TrapKind
  severity      : Severity
  verdict       : Verdict
  exprPP        : String
  conditionPP   : Option String := none
  counterexample : Array (String × String) := #[]
  tacticsTried  : Array String := #[]
  message       : String
  timeout       : Bool := false
  /-- Hypotheses (as source text) the quick fix proposes to add. -/
  suggestedHyps : Array String := #[]
  /-- Names of variables that a suggestion refers to (must be signature binders). -/
  suggestVars   : Array Name := #[]
  /-- Head constant of the trap subexpression (for locating syntax). -/
  head          : Name := .anonymous
  deriving Inhabited

end ConventionTrap
