import Lean
import ConventionTrap.Types

namespace ConventionTrap
open Lean

register_option linter.conventionTrap : Bool := {
  defValue := true, descr := "enable the convention trap linter" }
register_option linter.conventionTrap.natSub : Bool := {
  defValue := true, descr := "convention trap: natural subtraction (natSub, natSubHyp, expTrunc)" }
register_option linter.conventionTrap.div : Bool := {
  defValue := true, descr := "convention trap: division by zero in fields" }
register_option linter.conventionTrap.intDiv : Bool := {
  defValue := true, descr := "convention trap: ℕ/ℤ division and modulo (intDiv, modZero, intDivNeg)" }
register_option linter.conventionTrap.realDomain : Bool := {
  defValue := true, descr := "convention trap: Real.sqrt/log/rpow domains, Int.toNat" }
register_option linter.conventionTrap.castSub : Bool := {
  defValue := true, descr := "convention trap: cast of a truncated subtraction" }
register_option linter.conventionTrap.natZero : Bool := {
  defValue := true, descr := "convention trap: counterexample at 0 (natZero, falseStatement)" }
register_option linter.conventionTrap.heartbeats : Nat := {
  defValue := 20000, descr := "convention trap: heartbeat budget per condition" }
register_option linter.conventionTrap.mode : String := {
  defValue := "editor", descr := "convention trap: \"editor\" or \"ci\"" }
register_option linter.conventionTrap.witness : Bool := {
  defValue := true, descr := "convention trap: search concrete witnesses (reachable vs unknown)" }
register_option linter.conventionTrap.benign : Bool := {
  defValue := true, descr := "convention trap: hide sites whose junk value does not change truth" }
register_option linter.conventionTrap.selfGuard : Bool := {
  defValue := true, descr := "convention trap: let a hypothesis guard the trap inside itself" }
register_option linter.conventionTrap.unfoldDepth : Nat := {
  defValue := 1, descr := "convention trap: unfold local Prop definitions in hypotheses" }
register_option linter.conventionTrap.showUnknown : Bool := {
  defValue := false, descr := "convention trap: show sites that could be neither proved nor witnessed" }

/-- Read a `TrapConfig` from options. -/
def configOfOptions (o : Options) : TrapConfig :=
  let mode := (Mode.ofString? (linter.conventionTrap.mode.get o)).getD .editor
  let enabledGroup (n : Name) : Bool := o.getBool n true
  { heartbeats := linter.conventionTrap.heartbeats.get o
    mode
    enabled := fun k => enabledGroup k.optionName
    witness := linter.conventionTrap.witness.get o
    benign := linter.conventionTrap.benign.get o
    selfGuard := linter.conventionTrap.selfGuard.get o
    unfoldDepth := o.get `linter.conventionTrap.unfoldDepth (if mode == .ci then 2 else 1 : Nat)
    showUnknown := o.getBool `linter.conventionTrap.showUnknown (mode == .ci)
    refuteMaxVars := 4 }

end ConventionTrap
