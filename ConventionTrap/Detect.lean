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
  /-- Remaining unfoldings of local (non-library) definitions applied in the statement. -/
  unfoldLeft : Nat := 0

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

def finBound? (ty : Expr) : Option Expr :=
  let ty := ty.consumeMData
  if ty.isAppOfArity ``Fin 1 then some ty.appArg! else none

/-- `Fin.val` of a `Fin` term, or the ℕ literal itself for a numeral. -/
def finValOf (x : Expr) : MetaM Expr := do
  let x := x.consumeMData
  if x.isAppOfArity ``OfNat.ofNat 3 then
    if let some k := x.getAppArgs[1]!.rawNatLit? then return mkNatLit k
  mkAppM ``Fin.val #[x]

def zmodModulus? (ty : Expr) : Option Expr :=
  let ty := ty.consumeMData
  if ty.isAppOfArity `ZMod 1 then
    let n := ty.appArg!
    if (n.rawNatLit?.isSome || n.nat?.isSome) then none else some n
  else none

def isNatSub (e : Expr) : Bool :=
  let e := e.consumeMData
  e.isAppOfArity ``HSub.hSub 6 && isNatTy e.getAppArgs[0]! && isNatTy e.getAppArgs[1]!

/-- Report trap patterns at `e`. Returns the arguments to keep visiting (or `none` = all). -/
def checkPatterns (e : Expr) (ctx : Ctx) : DetectM (Option (Array Expr)) := do
  let args := e.getAppArgs
  let some c := e.getAppFn.constName? | return none
  match c, args.size with
  | ``HSub.hSub, 6 =>
    if let some _ := finBound? args[0]! then
      let cond ← mkAppM ``LE.le #[← finValOf args[5]!, ← finValOf args[4]!]
      recordSite ctx .finWrap e cond (mkNot cond)
    if isNatSub e then
      let kind := if ctx.inHyp.isSome then .natSubHyp else if ctx.inExp then .expTrunc else .natSub
      recordSite ctx kind e (← mkAppM ``LE.le #[args[5]!, args[4]!])
        (← mkAppM ``LT.lt #[args[4]!, args[5]!])
    return none
  | ``Int.cast, 3 =>
    if let some n := zmodModulus? args[0]! then
      let cond ← mkAppM ``Ne #[n, ← zeroOf (← inferType n)]
      recordSite ctx .zmodZero e cond (mkNot cond)
    return none
  | ``Nat.cast, 3 =>
    if let some n := zmodModulus? args[0]! then
      let cond ← mkAppM ``Ne #[n, ← zeroOf (← inferType n)]
      recordSite ctx .zmodZero e cond (mkNot cond)
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
  | `Real.logb, 2 =>
    let z ← zeroOf (mkConst ``Real)
    recordSite ctx .realDomain e (← mkAppM ``LT.lt #[z, args[1]!]) (← mkAppM ``LE.le #[args[1]!, z])
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
  | ``HAdd.hAdd, 6 =>
    if let some n := finBound? args[0]! then
      let sum ← mkAppM ``HAdd.hAdd #[← finValOf args[4]!, ← finValOf args[5]!]
      let cond ← mkAppM ``LT.lt #[sum, n]
      recordSite ctx .finWrap e cond (mkNot cond)
    return none
  | ``LT.lt, 4 =>
    let t ← whnfR args[0]!
    if let .forallE n d _ _ := t then
      unless (← isProp t) do
        let cond ← withLocalDeclD n d fun i => do
          mkForallFVars #[i] (← mkAppM ``LT.lt #[mkApp args[2]! i, mkApp args[3]! i])
        recordSite ctx .piOrder e cond (mkNot cond)
    return none
  | `InfSet.sInf, 3 | `SupSet.sSup, 3 =>
    let α := args[0]!
    let S := args[2]!
    let isInf := c == `InfSet.sInf
    if isNatTy α then
      let cond ← if isInf then mkAppM ``Set.Nonempty #[S] else mkAppM ``BddAbove #[S]
      recordSite ctx .sSupInf e cond (mkNot cond)
    else if isRealTy α then
      let cond ← mkAppM ``And #[← mkAppM ``Set.Nonempty #[S],
        ← mkAppM (if isInf then ``BddBelow else ``BddAbove) #[S]]
      recordSite ctx .sSupInf e cond (mkNot cond)
    return none
  | `iSup, 4 | `iInf, 4 =>
    let α := args[0]!
    let isInf := c == `iInf
    if isNatTy α || isRealTy α then
      let rng ← mkAppM ``Set.range #[args[3]!]
      let bdd ← mkAppM (if isInf then ``BddBelow else ``BddAbove) #[rng]
      let cond ← if isRealTy α then mkAppM ``And #[← mkAppM ``Nonempty #[args[1]!], bdd] else pure bdd
      unless isNatTy α && isInf do
        recordSite ctx .sSupInf e cond (mkNot cond)
    return none
  | `Set.ncard, 2 =>
    let cond ← mkAppM ``Set.Finite #[args[1]!]
    recordSite ctx .card e cond (mkNot cond)
    return none
  | `Nat.card, 1 =>
    let cond ← mkAppM ``Finite #[args[0]!]
    recordSite ctx .card e cond (mkNot cond)
    return none
  | `Metric.diam, 3 =>
    let cond ← mkAppM `Bornology.IsBounded #[args[2]!]
    recordSite ctx .diam e cond (mkNot cond)
    return none
  | `MeasureTheory.integral, 7 =>
    if ctx.pos && ctx.inHyp.isNone then
      let cond ← mkAppM `MeasureTheory.Integrable #[args[6]!, args[5]!]
      recordSite ctx .integral e cond (mkNot cond)
    return none
  | `intervalIntegral, 7 =>
    if ctx.pos && ctx.inHyp.isNone then
      let cond ← mkAppM `IntervalIntegrable #[args[3]!, args[6]!, args[4]!, args[5]!]
      recordSite ctx .integral e cond (mkNot cond)
    return none
  | `tsum, 6 =>
    if ctx.pos && ctx.inHyp.isNone then
      let cond ← mkAppM `Summable #[args[4]!, args[5]!]
      recordSite ctx .tsum e cond (mkNot cond)
    return none
  | `Summable, 6 =>
    -- `Summable` is unconditional (absolute, in ℝ) summability: an alternating series that
    -- only converges conditionally is *not* summable.
    let f := args[4]!
    let alternating := (f.find? fun t =>
      t.isAppOfArity ``HPow.hPow 6 && (t.getAppArgs[4]!.consumeMData.isAppOfArity ``Neg.neg 3)).isSome
    if alternating then
      let cond ← withLocalDeclD `k (← inferType f).bindingDomain! fun k => do
        mkAppM ``Summable #[← mkLambdaFVars #[k] (← mkAppM ``Norm.norm #[mkApp f k])]
      recordSite ctx .tsum e cond (mkNot cond)
    return none
  | `deriv, 8 =>
    let cond ← mkAppM `DifferentiableAt #[args[0]!, args[6]!, args[7]!]
    recordSite ctx .deriv e cond (mkNot cond)
    return none
  | _, _ => return none

/-- Binder names conventionally used for real constants (`∃ c > 0, …`). -/
def realConstNames : List String := ["c", "C", "ε", "δ", "K", "κ"]

/-- `0 < x` or `x > 0`. -/
def isPosConstraint (p x : Expr) : Bool :=
  let p := p.consumeMData
  (p.isAppOfArity ``LT.lt 4 && p.appArg! == x) || (p.isAppOfArity ``GT.gt 4 && p.appFn!.appArg! == x)

/-- Premises `P₁ → … → Pₙ → B` (non-dependent Prop arrows) in front of `e`. -/
partial def leadingPremises (e : Expr) : MetaM (Array Expr) := do
  match e.consumeMData with
  | .forallE _ d b _ =>
    if !b.hasLooseBVars && (← isProp d) then return #[d] ++ (← leadingPremises b) else return #[]
  | _ => return #[]

/-- A guard-like premise: `a ≠ b`, `0 < a`, `a > 0`, `0 ≤ a`. -/
def isGuardLike (p : Expr) : Bool :=
  let p := p.consumeMData
  p.isAppOfArity ``Ne 3 || p.isAppOfArity ``LT.lt 4 || p.isAppOfArity ``GT.gt 4 ||
    p.isAppOfArity ``LE.le 4 || (p.isAppOfArity ``Not 1 && p.appArg!.consumeMData.isAppOfArity ``Eq 3)

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
        -- Guarded conjunction: whatever the polarity, if the left conjunct is false the
        -- conjunction is false regardless of the right one, so the right side may assume it.
        visit args[0]! { ctx with atom := none }
        visit args[1]! (← addHyp { ctx with atom := none } args[0]!)
    | some ``Or, 2 =>
      visit args[0]! { ctx with atom := none }
      visit args[1]! { ctx with atom := none }
    | some ``Iff, 2 =>
      -- Guard inside one side only: `A ↔ (g → B)`. When `g` fails that side is vacuously true,
      -- which forces the other side.
      let ps0 ← leadingPremises args[0]!
      let ps1 ← leadingPremises args[1]!
      for (ps, other) in [(ps0, ps1), (ps1, ps0)] do
        if other.isEmpty then
          for g in ps.filter isGuardLike do
            recordSite { ctx with atom := none } .guardScope g g (mkNot g)
      visit args[0]! { ctx with atom := some e }
      visit args[1]! { ctx with atom := some e }
    | some ``Exists, 2 =>
      if let .lam n d b bi := args[1]!.consumeMData then
        if isNatTy d && realConstNames.contains n.eraseMacroScopes.toString then
          withLocalDecl n bi d fun x => do
            let body := (b.instantiate1 x).consumeMData
            if body.isAppOfArity ``And 2 && isPosConstraint body.appFn!.appArg! x then
              recordSite { ctx with scope := ctx.scope.push x, atom := none } .litNat x
                (mkConst ``False) (mkConst ``True)
      visit args[1]! { ctx with atom := none }
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
      -- Local (project) definitions applied here: also check their body, instantiated.
      if ctx.unfoldLeft > 0 then
        if let some c := fn.constName? then
          if (← getEnv).find? c |>.any (·.isDefinition) then
            if ← isLocalDef c then
              if let some e' ← (try unfoldDefinition? e catch _ => pure none) then
                visit e'.headBeta { ctx with unfoldLeft := ctx.unfoldLeft - 1 }
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
  let ((), sites) ← (visit stmt { unfoldLeft := cfg.unfoldDepth }).run cfg |>.run #[]
  return sites

end ConventionTrap
