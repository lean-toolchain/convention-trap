import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ConventionTrap.Types

/-!
# Detect: trap sites and their safe local hypotheses (algorithm.md §1–2)

The statement is traversed once. At every trap site we build a *closed* goal
`∀ scope, hyps → cond` where `scope` is every binder in scope and `hyps` are the
facts usable at that position:

* Prop binders / implication premises above the site,
* the sibling of a conjunction in positive position,
* the branch condition of `if`,
* `i ∈ s` for the bound variable of `Finset.sum`/`Finset.prod`,
* derived facts (`Nat.Prime p → 2 ≤ p`, `x ∈ range n → x < n`, …) and local
  Prop definitions unfolded `unfoldDepth` times.

Safety rules: sites inside a data binder's type only see binders before it (no
circularity), and facts are never extracted under `¬` or from premises' insides.
-/

namespace ConventionTrap
open Lean Meta

structure TrapSite where
  kind : TrapKind
  exprPP : String
  typePP : String
  condPP : String
  violPP : String
  head : Name
  /-- Closed goal `∀ scope, hyps → cond`. -/
  goal : Expr
  /-- Closed goal `∀ scope, hyps → ¬cond → atom` (junk region keeps truth), if applicable. -/
  benignGoal? : Option Expr := none
  /-- User names of variables in `cond`. -/
  condVars : Array Name := #[]
  /-- All variables of `cond` are leading binders of the declaration. -/
  suggestable : Bool := false
  deriving Inhabited

structure DetectCfg where
  selfGuard : Bool := true
  benign : Bool := true
  unfoldDepth : Nat := 1
  enabled : TrapKind → Bool := fun _ => true

structure Ctx where
  scope : Array Expr := #[]
  hyps : Array Expr := #[]
  /-- Positive position (facts may be extracted). -/
  pos : Bool := true
  /-- The hypothesis whose inside we are visiting (for self-guard). -/
  inHyp : Option Expr := none
  inExp : Bool := false
  /-- Still in the leading binder prefix of the statement. -/
  atTop : Bool := true
  topVars : Array FVarId := #[]
  /-- At statement level (not inside a term). -/
  inStmt : Bool := true
  /-- Innermost atomic proposition containing the current position. -/
  atom : Option Expr := none

abbrev DetectM := ReaderT DetectCfg <| StateRefT (Array TrapSite) MetaM

/-- Modules whose definitions are *not* unfolded (library code). -/
def libraryRoots : List Name :=
  [`Init, `Std, `Lean, `Mathlib, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets]

def isLocalDef (c : Name) : MetaM Bool := do
  let env ← getEnv
  match env.getModuleIdxFor? c with
  | none => return true
  | some idx =>
    let mod := env.header.moduleNames[idx.toNat]!
    return !libraryRoots.any (·.isPrefixOf mod)

/-- Facts usable from hypothesis `h` (including `h` itself). -/
partial def expandFacts (h : Expr) (depth : Nat) : MetaM (Array Expr) := do
  let h := h.consumeMData
  let mut out := #[h]
  try
    if h.isAppOfArity ``And 2 then
      return out ++ (← expandFacts h.appFn!.appArg! depth) ++ (← expandFacts h.appArg! depth)
    if h.isAppOfArity ``Nat.Prime 1 then
      out := out.push (← mkAppM ``LE.le #[mkNatLit 2, h.appArg!])
    if h.isAppOfArity ``Membership.mem 5 then
      let args := h.getAppArgs
      for (s, x) in [(args[3]!, args[4]!), (args[4]!, args[3]!)] do
        if s.isAppOfArity ``Finset.range 1 then
          out := out.push (← mkAppM ``LT.lt #[x, s.appArg!])
        if s.isAppOfArity ``Finset.Icc 5 || s.isAppOfArity ``Finset.Ioc 5 then
          let sa := s.getAppArgs
          out := out.push (← mkAppM ``LE.le #[x, sa[4]!])
          out := out.push (← mkAppM (if s.isAppOf ``Finset.Icc then ``LE.le else ``LT.lt) #[sa[3]!, x])
        if s.isAppOfArity ``Finset.Ico 5 then
          let sa := s.getAppArgs
          out := out.push (← mkAppM ``LT.lt #[x, sa[4]!])
          out := out.push (← mkAppM ``LE.le #[sa[3]!, x])
    if h.isAppOfArity ``Finset.Nonempty 2 then
      out := out.push (← mkAppM ``LT.lt #[mkNatLit 0, ← mkAppM ``Finset.card #[h.appArg!]])
    if depth > 0 then
      if let some c := h.getAppFn.constName? then
        if (← getEnv).find? c |>.any (·.isDefinition) then
          if ← isLocalDef c then
            if let some h' ← unfoldDefinition? h then
              out := out ++ (← expandFacts h'.headBeta (depth - 1))
  catch _ => pure ()
  return out

def ppStr (e : Expr) : MetaM String := do
  let s := toString (← ppExpr e)
  return " ".intercalate (s.splitToList Char.isWhitespace |>.filter (!·.isEmpty))

def zeroOf (α : Expr) : MetaM Expr := mkAppOptM ``OfNat.ofNat #[α, mkRawNatLit 0, none]

def addHyp (ctx : Ctx) (h : Expr) : DetectM Ctx := do
  let facts ← expandFacts h (← read).unfoldDepth
  return { ctx with hyps := ctx.hyps ++ facts }

def recordSite (ctx : Ctx) (kind : TrapKind) (e cond viol : Expr) : DetectM Unit := do
  let cfg ← read
  unless cfg.enabled kind do return
  let exprPP ← ppStr e
  let condPP ← ppStr cond
  let mut hyps := ctx.hyps
  if cfg.selfGuard then
    if let some h := ctx.inHyp then hyps := hyps.push h
  let mkGoal (concl : Expr) : MetaM Expr := do
    let body ← hyps.foldrM (fun h acc => mkArrow h acc) concl
    mkForallFVars ctx.scope body
  let goal ← mkGoal cond
  let mut benignGoal? := none
  if cfg.benign && ctx.pos && ctx.inHyp.isNone then
    if let some a := ctx.atom then
      benignGoal? := some (← mkGoal (← mkArrow (mkNot cond) a))
  let fvs := (collectFVars {} cond).fvarIds
  let condVars ← fvs.mapM (·.getUserName)
  let suggestable := fvs.all ctx.topVars.contains
  modify (·.push {
    kind, exprPP, condPP, head := e.getAppFn.constName?.getD .anonymous, goal, benignGoal?,
    condVars, suggestable,
    typePP := ← ppStr (← inferType e), violPP := ← ppStr viol })

def isNatTy (e : Expr) : Bool := e.consumeMData.isConstOf ``Nat
def isIntTy (e : Expr) : Bool := e.consumeMData.isConstOf ``Int
def isRealTy (e : Expr) : Bool := e.consumeMData.isConstOf ``Real

def hasGroupWithZero (α : Expr) : MetaM Bool := do
  try return (← synthInstance? (← mkAppM ``GroupWithZero #[α])).isSome
  catch _ => return false

def isNatSub (e : Expr) : Bool :=
  let e := e.consumeMData
  e.isAppOfArity ``HSub.hSub 6 && isNatTy e.getAppArgs[0]! && isNatTy e.getAppArgs[1]!

/-- Report trap patterns at `e`. Returns the arguments to keep visiting (or `none` = all). -/
def checkPatterns (e : Expr) (ctx : Ctx) : DetectM (Option (Array Expr)) := do
  let args := e.getAppArgs
  let some c := e.getAppFn.constName? | return none
  match c, args.size with
  | ``HSub.hSub, 6 =>
    if isNatSub e then
      let kind := if ctx.inHyp.isSome then .natSubHyp else if ctx.inExp then .expTrunc else .natSub
      recordSite ctx kind e (← mkAppM ``LE.le #[args[5]!, args[4]!])
        (← mkAppM ``LT.lt #[args[4]!, args[5]!])
    return none
  | ``Nat.cast, 3 =>
    let x := args[2]!.consumeMData
    if isNatSub x then
      let xa := x.getAppArgs
      recordSite ctx .castSub e (← mkAppM ``LE.le #[xa[5]!, xa[4]!])
        (← mkAppM ``LT.lt #[xa[4]!, xa[5]!])
      return some #[xa[4]!, xa[5]!]
    return none
  | ``HDiv.hDiv, 6 =>
    let α := args[0]!
    let (x, y) := (args[4]!, args[5]!)
    if isNatTy α || isIntTy α then
      recordSite ctx .intDiv e (← mkAppM ``Dvd.dvd #[y, x]) (mkNot (← mkAppM ``Dvd.dvd #[y, x]))
      if isIntTy α then
        let z ← zeroOf α
        recordSite ctx .intDivNeg e
          (← mkAppM ``And #[← mkAppM ``LE.le #[z, x], ← mkAppM ``LT.lt #[z, y]])
          (← mkAppM ``Or #[← mkAppM ``LT.lt #[x, z], ← mkAppM ``LE.le #[y, z]])
    else if args[1]! == α && (← hasGroupWithZero α) then
      let z ← zeroOf α
      recordSite ctx .div e (← mkAppM ``Ne #[y, z]) (← mkEq y z)
    return none
  | ``Inv.inv, 3 =>
    let α := args[0]!
    if ← hasGroupWithZero α then
      let z ← zeroOf α
      recordSite ctx .div e (← mkAppM ``Ne #[args[2]!, z]) (← mkEq args[2]! z)
    return none
  | ``HMod.hMod, 6 =>
    let α := args[0]!
    if isNatTy α || isIntTy α then
      let z ← zeroOf α
      recordSite ctx .modZero e (← mkAppM ``Ne #[args[5]!, z]) (← mkEq args[5]! z)
    return none
  | ``Real.sqrt, 1 =>
    let z ← zeroOf (mkConst ``Real)
    recordSite ctx .realDomain e (← mkAppM ``LE.le #[z, args[0]!]) (← mkAppM ``LT.lt #[args[0]!, z])
    return none
  | ``Real.log, 1 =>
    let z ← zeroOf (mkConst ``Real)
    recordSite ctx .realDomain e (← mkAppM ``LT.lt #[z, args[0]!]) (← mkAppM ``LE.le #[args[0]!, z])
    return none
  | ``HPow.hPow, 6 =>
    if isRealTy args[0]! && isRealTy args[1]! then
      let z ← zeroOf (mkConst ``Real)
      recordSite ctx .rpow e (← mkAppM ``LE.le #[z, args[4]!]) (← mkAppM ``LT.lt #[args[4]!, z])
    return none
  | ``Int.toNat, 1 =>
    let z ← zeroOf (mkConst ``Int)
    recordSite ctx .intToNat e (← mkAppM ``LE.le #[z, args[0]!]) (← mkAppM ``LT.lt #[args[0]!, z])
    return none
  | _, _ => return none

mutual

partial def visitBinder (n : Name) (bi : BinderInfo) (d b : Expr) (ctx : Ctx) (bodyIsStmt : Bool)
    (extraHyp : Option (Expr → MetaM Expr) := none) : DetectM Unit := do
  withLocalDecl n bi d fun x => do
    let isP ← isProp d
    let mut ctx := { ctx with
      scope := ctx.scope.push x
      topVars := if ctx.atTop then ctx.topVars.push x.fvarId! else ctx.topVars
      inStmt := bodyIsStmt
      atom := if bodyIsStmt then none else ctx.atom }
    if isP then ctx ← addHyp ctx d
    if let some mk := extraHyp then ctx ← addHyp ctx (← mk x)
    visit (b.instantiate1 x) ctx

partial def visit (e : Expr) (ctx : Ctx) : DetectM Unit := do
  let e := e.consumeMData
  match e with
  | .forallE n d b bi =>
    let isP ← isProp d
    -- binder type: hypothesis inside (self-guard applies) or data type (no self).
    visit d { ctx with pos := false, inHyp := if isP then some d else none, inStmt := isP,
                       atom := none, atTop := false, inExp := false }
    if isP && !b.hasLooseBVars then
      let ctx' ← addHyp { ctx with atom := none } d
      visit b ctx'
    else
      visitBinder n bi d b ctx true
  | .lam n d b bi =>
    visitBinder n bi d b { ctx with atTop := false } ctx.inStmt
  | .letE _ _ v b _ => visit (b.instantiate1 v) ctx
  | .proj _ _ s => visit s { ctx with atTop := false, inStmt := false }
  | .app .. =>
    let ctx := { ctx with atTop := false }
    let args := e.getAppArgs
    let fn := e.getAppFn
    match fn.constName?, args.size with
    | some ``Not, 1 => visit args[0]! { ctx with pos := false, atom := none }
    | some ``And, 2 =>
      if ctx.pos && ctx.inHyp.isNone then
        visit args[0]! (← addHyp { ctx with atom := none } args[1]!)
        visit args[1]! (← addHyp { ctx with atom := none } args[0]!)
      else
        visit args[0]! { ctx with atom := none }
        visit args[1]! { ctx with atom := none }
    | some ``Or, 2 | some ``Iff, 2 =>
      visit args[0]! { ctx with atom := none }
      visit args[1]! { ctx with atom := none }
    | some ``Exists, 2 => visit args[1]! { ctx with atom := none }
    | some ``ite, 5 =>
      let c := args[1]!
      visit c { ctx with pos := false, inStmt := false }
      visit args[3]! (← addHyp ctx c)
      visit args[4]! (← addHyp ctx (mkNot c))
    | some ``Finset.sum, 5 | some ``Finset.prod, 5 =>
      let s := args[3]!
      visit s { ctx with inStmt := false }
      match args[4]!.consumeMData with
      | .lam n d b bi =>
        visitBinder n bi d b { ctx with inStmt := false } false
          (some fun i => mkAppM ``Membership.mem #[s, i])
      | f => visit f { ctx with inStmt := false }
    | _, _ =>
      let mut ctx := ctx
      if ctx.inStmt && ctx.atom.isNone then
        if ← isProp e then ctx := { ctx with atom := some e }
      let keep ← checkPatterns e ctx
      let tctx := { ctx with inStmt := false }
      match keep with
      | some xs => for x in xs do visit x tctx
      | none =>
        let finfo ← getFunInfoNArgs fn args.size
        let isPowNat := fn.isConstOf ``HPow.hPow && args.size == 6 && isNatTy args[1]!
        for h : i in [0:args.size] do
          let isInst := finfo.paramInfo[i]?.any (·.isInstImplicit)
          if isInst then continue
          let a := args[i]
          if ← isType' a then continue
          visit a { tctx with inExp := isPowNat && i == 5 }
  | _ => pure ()

partial def isType' (e : Expr) : DetectM Bool := do
  try
    let t ← whnfR (← inferType e)
    return t.isSort
  catch _ => return false

end

/-- Collect trap sites of a statement. -/
def detect (stmt : Expr) (cfg : DetectCfg) : MetaM (Array TrapSite) := do
  let ((), sites) ← (visit stmt {}).run cfg |>.run #[]
  return sites

end ConventionTrap
