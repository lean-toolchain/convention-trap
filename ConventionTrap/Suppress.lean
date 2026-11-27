import Lean
import ConventionTrap.Types

/-!
# `@[trap_ok kind+ "reason"]`

Turns off the given trap kinds for one declaration. A reason is mandatory.
-/

namespace ConventionTrap
open Lean

syntax (name := trap_ok) "trap_ok" (ppSpace ident)+ ppSpace str : attr

initialize trapOkAttr : ParametricAttribute (Array TrapKind × String) ←
  registerParametricAttribute {
    name := `trap_ok
    descr := "suppress convention trap findings for this declaration (reason required)"
    getParam := fun _ stx => do
      match stx with
      | `(attr| trap_ok $ks* $r:str) =>
        let reason := r.getString
        if reason.trimAscii.isEmpty then
          throwErrorAt r "trap_ok: 이유가 필요합니다 (empty reason)"
        let kindList := ", ".intercalate (TrapKind.all.map (·.toString)).toList
        let kinds ← ks.mapM fun k => do
          match TrapKind.ofString? k.getId.toString with
          | some kind => pure kind
          | none => throwErrorAt k "trap_ok: 알 수 없는 함정 종류 '{k.getId}'. 가능한 값: {kindList}"
        return (kinds, reason)
      | _ => throwError "trap_ok: 형식은 `trap_ok <TrapKind>+ \"<이유>\"` 입니다" }

def getSuppression (env : Environment) (decl : Name) : Option (Array TrapKind × String) :=
  trapOkAttr.getParam? env decl

end ConventionTrap
