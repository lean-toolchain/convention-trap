import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ConventionTrap.Types

/-!
# Closed-goal solving and concrete-value search

* `tryClose` runs one tactic on a closed goal without leaking state or messages.
* `findAssignment` searches small concrete values for the data binders of a closed
  `∀`-statement such that every premise holds and the conclusion is refuted.
  It is used both for whole-statement refutation (`natZero`, `falseStatement`)
  and for condition-violation witnesses (`reachable`).
-/

namespace ConventionTrap
open Lean Meta Elab Term

/-- Result of one tactic attempt. -/
structure TacResult where
  closed : Bool
  timedOut : Bool := false

/-- Run `tac` on a fresh goal `goalTy` (must be closed). State and messages are restored. -/
def tryClose (goalTy : Expr) (tac : TSyntax `tactic) (heartbeats : Nat) : TermElabM TacResult := do
  let saved ← saveState
  let msgs := (← getThe Core.State).messages
  let res ← tryCatchRuntimeEx
    (do
      let mvar ← mkFreshExprMVar goalTy
      let rem ← withTheReader Core.Context (fun c => { c with maxHeartbeats := heartbeats * 1000 }) <|
        withCurrHeartbeats <| withoutErrToSorry <|
          Tactic.run mvar.mvarId! (Tactic.evalTactic tac)
      let v ← instantiateMVars mvar
      pure { closed := rem.isEmpty && !v.hasSorry && !v.hasSyntheticSorry : TacResult })
    (fun ex => pure { closed := false, timedOut := ex.isMaxHeartbeat })
  saved.restore (restoreInfo := true)
  modifyThe Core.State fun s => { s with messages := msgs }
  return res

/-- Tactic script used to discharge a condition goal `∀ scope, hyps → cond`. -/
def dischargeTactic : Name → TermElabM (Option (TSyntax `tactic))
  | `assumption => some <$> `(tactic| (intros; assumption))
  | `omega => some <$> `(tactic| (intros; omega))
  | `positivity => some <$> `(tactic| (intros; positivity))
  | `linarith => some <$> `(tactic| (intros; simp only [Set.mem_Ioi, Set.mem_Ici, Set.mem_Ioo, Set.mem_Icc, Set.mem_Ioc, Set.mem_Ico] at *; linarith))
  | `nlinarith => some <$> `(tactic| (intros; nlinarith [sq_nonneg (0 : ℕ)]))
  | `simp_arith => some <$> `(tactic| (intros; simp_all +arith; done))
  | `simp => some <$> `(tactic| (intros; simp_all; done))
  | `grind => some <$> `(tactic| (intros; grind))
  | `norm_num => some <$> `(tactic| (intros; norm_num at *; done))
  | _ => pure none

/-- Extra discharge tactics for structural conditions (finiteness, boundedness, differentiability,
nonemptiness): instances, `Set.toFinite`, `fun_prop`, and simp with the hypotheses. -/
def structuralTactics : TermElabM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| (intros; infer_instance)),
    ← `(tactic| (intros; exact Set.toFinite _)),
    ← `(tactic| (intros; fun_prop)),
    ← `(tactic| (intros; first | exact HasDerivAt.differentiableAt (by assumption) | exact DifferentiableOn.differentiableAt (by assumption) (by assumption))),
    ← `(tactic| (intros; refine ⟨?_, ?_⟩ <;>
        first | infer_instance | assumption | exact ⟨_, ‹_›⟩ | (simp_all; done))),
    ← `(tactic| (intros; first
        | exact Metric.isBounded_Icc _ _ | exact Metric.isBounded_Ico _ _
        | exact Metric.isBounded_Ioc _ _ | exact Metric.isBounded_Ioo _ _
        | exact Set.Finite.isBounded (Set.toFinite _) | exact Bornology.isBounded_empty)),
    ← `(tactic| (intros; simp_all; done)),
    ← `(tactic| (intros; aesop))]

/-- Tactics used to show that a statement is *still true* in the junk region (benign). -/
def benignTactics : TermElabM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| (intros; omega)),
    ← `(tactic| (intros; simp_all [Nat.card_pos_iff]; done)),
    ← `(tactic| (intros; simp_all [Nat.sub_eq_zero_of_le, div_zero, inv_zero, zero_div,
        Nat.div_zero, Int.ediv_zero, Nat.mod_zero, Int.emod_zero,
        Real.sqrt_eq_zero_of_nonpos, Real.log_zero, Int.toNat_of_nonpos,
        Nat.div_mul_le_self, Nat.mod_le, Nat.div_le_self, Int.toNat_le]; done)),
    ← `(tactic| (intros; positivity))]

/-- Tactics to prove a closed decidable-ish fact (`decide`, then `norm_num`). -/
def closedFactTactics : TermElabM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| decide),
    ← `(tactic| norm_num [Real.sqrt_eq_zero_of_nonpos, Real.log_zero, Real.log_neg_eq_log,
        Nat.sub_eq_zero_of_le, Int.toNat_of_nonpos])]

def proveClosedFact (p : Expr) (hb : Nat) : TermElabM Bool := do
  for tac in ← closedFactTactics do
    if (← tryClose p tac hb).closed then return true
  return false

/-! ## Concrete values -/

inductive VarSort where
  | nat | int | real | bool
  deriving BEq, Inhabited

def varSort? (ty : Expr) : MetaM (Option VarSort) := do
  let ty ← instantiateMVars ty
  if ty.isConstOf ``Nat then return some .nat
  if ty.isConstOf ``Int then return some .int
  if ty.isConstOf ``Real || ty.isConstOf ``Rat then return some .real
  if ty.isConstOf ``Bool then return some .bool
  return none

structure Candidate where
  expr : Expr
  display : String
  isZero : Bool
  deriving Inhabited

def natCand (n : Nat) : Candidate := ⟨mkNatLit n, toString n, n == 0⟩

def intCand (i : Int) : MetaM Candidate := do
  let abs := mkNumeral (mkConst ``Int) i.natAbs
  let e ← if i < 0 then mkAppM ``Neg.neg #[← abs] else abs
  return ⟨e, toString i, i == 0⟩

/-- Real/rational candidates: −1, 0, 1/2, 1, 2 (algorithm-improvements.md). -/
def realCands (ty : Expr) : MetaM (Array Candidate) := do
  let n (k : Nat) := mkNumeral ty k
  let one ← n 1
  let two ← n 2
  return #[⟨← mkAppM ``Neg.neg #[one], "-1", false⟩, ⟨← n 0, "0", true⟩,
    ⟨← mkAppM ``HDiv.hDiv #[one, two], "1/2", false⟩, ⟨one, "1", false⟩, ⟨two, "2", false⟩]

/-- Natural-number literals appearing in `e` (bounded). -/
def collectLiterals (e : Expr) : Array Nat :=
  let rec go (e : Expr) (fuel : Nat) (acc : Array Nat) : Array Nat :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      match e with
      | .lit (.natVal n) => if n ≤ 1000 && !acc.contains n then acc.push n else acc
      | .app f a => go a fuel (go f fuel acc)
      | .lam _ d b _ | .forallE _ d b _ => go b fuel (go d fuel acc)
      | .letE _ t v b _ => go b fuel (go v fuel (go t fuel acc))
      | .mdata _ b => go b fuel acc
      | .proj _ _ b => go b fuel acc
      | _ => acc
  go e 10000 #[]

structure SearchCfg where
  natBase : Array Nat
  intBase : Array Int
  allowReal : Bool
  maxVars : Nat
  maxTuples : Nat
  seed : Nat
  heartbeats : Nat

def candidatesFor (s : VarSort) (ty : Expr) (lits : Array Nat) (cfg : SearchCfg) :
    MetaM (Option (Array Candidate)) := do
  match s with
  | .nat =>
    let mut vals := cfg.natBase
    for c in lits do
      for v in [c - 1, c, c + 1] do
        unless vals.contains v do vals := vals.push v
    vals := vals.qsort (· < ·)
    return some (vals.map natCand)
  | .int =>
    let mut vals := cfg.intBase
    for c in lits do
      for v in [(c : Int) - 1, c, c + 1] do
        unless vals.contains v do vals := vals.push v
    vals := vals.qsort (· < ·)
    return some (← vals.mapM intCand)
  | .bool => return some #[⟨mkConst ``false, "false", false⟩, ⟨mkConst ``true, "true", false⟩]
  | .real => if cfg.allowReal then some <$> realCands ty else return none

/-- Deterministic linear congruential generator (stand-in for Plausible's random search). -/
def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- All index tuples ordered by (number of zeros desc, lexicographic), or a seeded sample. -/
def enumerateTuples (lists : Array (Array Candidate)) (maxTuples seed : Nat) : Array (Array Nat) :=
  let sizes := lists.map (·.size)
  let total := sizes.foldl (· * ·) 1
  if total ≤ maxTuples then
    let all := (List.range total).toArray.map fun k => Id.run do
      let mut k := k
      let mut idx : Array Nat := #[]
      for s in sizes.reverse do
        idx := idx.push (k % s)
        k := k / s
      return idx.reverse
    let zeros (t : Array Nat) : Nat :=
      (t.zipIdx.filter fun (i, j) => (lists[j]!)[i]!.isZero).size
    all.qsort fun a b =>
      let za := zeros a; let zb := zeros b
      if za != zb then za > zb else compareLex a b
  else Id.run do
    let mut out : Array (Array Nat) := #[sizes.map fun _ => 0]
    let mut st := seed + 1
    for _ in [0:maxTuples] do
      let mut t : Array Nat := #[]
      for s in sizes do
        st := lcg st
        t := t.push (st % s)
      out := out.push t
    return out
where
  compareLex (a b : Array Nat) : Bool := Id.run do
    for (x, y) in a.zip b do
      if x < y then return true
      if x > y then return false
    return false

/-- Instantiate the data binders of `ty` with `vals` in order, checking premises on the way.
Returns `true` iff all premises hold and the conclusion is refuted. -/
partial def checkAssignment (ty : Expr) (vals : List Expr) (hb : Nat) : TermElabM Bool := do
  match ty.consumeMData, vals with
  | .forallE _ d b _, vals =>
    if ← isProp d then
      if b.hasLooseBVars then return false
      unless ← proveClosedFact d hb do return false
      checkAssignment b vals hb
    else match vals with
      | v :: vs => checkAssignment (b.instantiate1 v) vs hb
      | [] => proveClosedFact (mkNot ty) hb
  | concl, [] => proveClosedFact (mkNot concl) hb
  | _, _ :: _ => return false

/-- Simplify a closed statement before searching values:
1. a premise `∀ ys, f ys = rhs` (with `f` a binder not occurring in `rhs`) defines `f`:
   substitute `f := fun ys => rhs` and drop the premise;
2. keep only the data binders connected to the conclusion through premises, and the premises
   among them (closed premises are kept). Disconnected premises are assumed satisfiable. -/
def reduceStatement (ty : Expr) : MetaM Expr :=
  forallTelescope ty fun xs concl => do
    let mut fs : Array Expr := #[]
    let mut lams : Array Expr := #[]
    let mut defPremises : Array Expr := #[]
    for p in xs do
      let pt ← inferType p
      unless ← isProp pt do continue
      let r? ← forallTelescope pt fun ys b => do
        let b := b.consumeMData
        unless b.isAppOfArity ``Eq 3 && ys.size > 0 do return none
        let lhs := b.appFn!.appArg!
        let rhs := b.appArg!
        let f := lhs.getAppFn
        unless f.isFVar && xs.contains f && lhs.getAppArgs == ys do return none
        if rhs.containsFVar f.fvarId! then return none
        return some (f, ← mkLambdaFVars ys rhs)
      if let some (f, lam) := r? then
        unless fs.contains f do
          fs := fs.push f; lams := lams.push lam; defPremises := defPremises.push p
    let subst (e : Expr) : MetaM Expr := do
      if fs.isEmpty then return e
      Core.betaReduce (e.replaceFVars fs lams)
    let concl' ← subst concl
    let mut dataVars : Array Expr := #[]
    let mut premises : Array Expr := #[]
    for x in xs do
      if fs.contains x || defPremises.contains x then continue
      let t ← inferType x
      if ← isProp t then
        let t' ← subst t
        -- premises that mention other proofs are dropped
        unless (← (collectFVars {} t').fvarIds.anyM fun v => do isProp (← v.getType)) do
          premises := premises.push t'
      else dataVars := dataVars.push x
    let fvarsOf (e : Expr) : Array FVarId := (collectFVars {} e).fvarIds
    let mut comp : Array FVarId := (fvarsOf concl').filter fun v => dataVars.any (·.fvarId! == v)
    let mut keep : Array Bool := premises.map fun pr => (fvarsOf pr).isEmpty
    let mut changed := true
    while changed do
      changed := false
      for h : i in [0:premises.size] do
        if keep[i]! then continue
        let vs := fvarsOf premises[i]
        if vs.any comp.contains then
          keep := keep.set! i true
          for v in vs do
            unless comp.contains v do comp := comp.push v; changed := true
    let vars := dataVars.filter fun x => comp.contains x.fvarId!
    let kept := (premises.zip keep).filterMap fun (pr, k) => if k then some pr else none
    let body ← kept.foldrM (fun pr acc => mkArrow pr acc) concl'
    mkForallFVars vars body

/-- Search an assignment of the leading data binders of the closed statement `ty`
under which every premise holds and the conclusion is false. -/
def findAssignment (ty : Expr) (cfg : SearchCfg) :
    TermElabM (Option (Array (Name × Candidate))) := do
  let ty ← try reduceStatement ty catch _ => pure ty
  let binders ← forallTelescope ty fun xs _ => do
    let mut out : Array (Name × Expr × Bool) := #[]
    for x in xs do
      let t ← inferType x
      let isP ← isProp t
      out := out.push ((← x.fvarId!.getUserName), t, isP)
    return out
  let data := binders.filter (!·.2.2)
  if data.isEmpty then
    return if ← checkAssignment ty [] cfg.heartbeats then some #[] else none
  if data.size > cfg.maxVars then return none
  let lits := collectLiterals ty
  let mut lists : Array (Array Candidate) := #[]
  for (_, t, _) in data do
    if t.hasLooseBVars || t.hasFVar then return none
    let some s ← varSort? t | return none
    let some cs ← candidatesFor s t lits cfg | return none
    lists := lists.push cs
  for tuple in enumerateTuples lists cfg.maxTuples cfg.seed do
    let cands := tuple.zipIdx.map fun (i, j) => (lists[j]!)[i]!
    if ← checkAssignment ty (cands.map (·.expr)).toList cfg.heartbeats then
      return some ((data.map (·.1)).zip cands)
  return none

end ConventionTrap
