import Mathlib
import ConventionTrap

/-!
# Real incidents (reproductions)

Statements taken from fix commits / misformalization issues of miniF2F-lean4, PutnamBench and
Formal Conjectures (see `real-cases/cases.md` for links). Naming read by `scripts/eval.py`:

* `pos_<kind>_<id>` — the *buggy* version; `<kind>` is the trap that caused the bug. Kinds that are
  not implemented yet (`logb`, `natCard`, `sSup`, `deriv`, `trivialWitness`, …) can never be
  matched and count as misses on purpose: they measure what remains to be built.
* `neg_<id>` — the *fixed* version; must not be flagged.

Faithfulness: `[exact]` = statement copied (only syntax updated for current Mathlib);
`[model]` = project-specific definitions replaced by variables/hypotheses with the same shape.
-/

set_option linter.conventionTrap false
set_option warn.sorry false

open Real Nat Finset

namespace Real

/-! ## miniF2F-lean4 commit 1be24b7 ("Fix 7 erroneous theorem formalizations") -/

/-- [exact] mathd_numbertheory_618: n = 0 is a counterexample (fix: add `n > 0`). -/
theorem pos_natZero_mf618 (n : ℕ) (p : ℕ → ℕ) (h₀ : ∀ x, p x = x ^ 2 - x + 41)
    (h₁ : 1 < Nat.gcd (p n) (p (n + 1))) : 41 ≤ n := sorry
theorem neg_mf618 (n : ℕ) (hn : n > 0) (p : ℕ → ℕ) (h₀ : ∀ x, p x = x ^ 2 - x + 41)
    (h₁ : 1 < Nat.gcd (p n) (p (n + 1))) : 41 ≤ n := sorry

/-- [exact] amc12a_2020_p10: at n = 1, `logb _ 1 = 0` and `log 0 = 0` satisfy h₁ (fix: `1 < n`). -/
theorem pos_logb_mf2020p10 (n : ℕ) (h₀ : 0 < n)
    (h₁ : Real.logb 2 (Real.logb 16 n) = Real.logb 4 (Real.logb 4 n)) :
    (Nat.digits 10 n).sum = 13 := sorry
theorem neg_mf2020p10 (n : ℕ) (h₀ : 1 < n)
    (h₁ : Real.logb 2 (Real.logb 16 n) = Real.logb 4 (Real.logb 4 n)) :
    (Nat.digits 10 n).sum = 13 := sorry

/-- [exact] amc12a_2021_p25: N = 0 gives f 0 = 0/0 = 0 (fix: `N > 0`). -/
theorem pos_natZero_mf2021p25 (N : ℕ) (f : ℕ → ℝ)
    (h₀ : ∀ n, 0 < n → f n = ((Nat.divisors n).card) / (n ^ ((1 : ℝ) / 3)))
    (h₁ : ∀ n ≠ N, 0 < n → f n < f N) : (Nat.digits 10 N).sum = 9 := sorry

/-- [exact] imo_1982_p1: `f (m+n) - f m - f n` truncates in ℕ (fix: compare in ℤ). -/
theorem pos_natSubHyp_mf1982p1 (f : ℕ → ℕ)
    (h₀ : ∀ m n, (0 < m ∧ 0 < n) → f (m + n) - f m - f n = 0 ∨ f (m + n) - f m - f n = 1)
    (h₁ : f 2 = 0) (h₂ : 0 < f 3) (h₃ : f 9999 = 3333) : f 1982 = 660 := sorry
theorem neg_mf1982p1 (f : ℕ → ℕ)
    (h₀ : ∀ m n, (0 < m ∧ 0 < n) →
      (f (m + n) : ℤ) - f m - f n = 0 ∨ (f (m + n) : ℤ) - f m - f n = 1)
    (h₁ : f 2 = 0) (h₂ : 0 < f 3) (h₃ : f 9999 = 3333) : f 1982 = 660 := sorry

/-! ## PutnamBench commits 25bc648, abbb648 -/

/-- [model] putnam_1999_b3: `1/2 ≤ m/n` is ℕ division (fix: cast to ℝ). Conclusion simplified. -/
theorem pos_intDiv_pb1999b3 (S : ℝ → ℝ → ℝ)
    (hS : S = fun x y => ∑' m : ℕ, ∑' n : ℕ,
      if (m > 0 ∧ n > 0 ∧ 1/2 ≤ m/n ∧ m/n ≤ 2) then x^m * y^n else 0) : S 0 0 = 0 := sorry
theorem neg_pb1999b3 (S : ℝ → ℝ → ℝ)
    (hS : S = fun x y => ∑' m : ℕ, ∑' n : ℕ,
      if (m > 0 ∧ n > 0 ∧ (1 : ℝ)/2 ≤ (m : ℝ)/n ∧ (m : ℝ)/n ≤ 2) then x^m * y^n else 0) :
    S 0 0 = 0 := sorry

/-- [exact] putnam_1968_b4: `x - 1/x` is integrated over a ball containing 0, where 1/0 = 0. -/
theorem pos_div_pb1968b4 (f : ℝ → ℝ) (hf : Continuous f) :
    ∃ r : ℝ, Filter.Tendsto (fun y => ∫ x in Metric.ball 0 y, f (x - 1/x)) Filter.atTop (nhds r) ∧
      Filter.Tendsto (fun y => ∫ x in Metric.ball 0 y, f x) Filter.atTop (nhds r) := sorry

/-- [model] putnam_1977_a2: the `≠ 0` guards sit inside the `↔`, so a = 0 makes the RHS vacuous. -/
theorem pos_guardScope_pb1977a2 (sol : ℝ → ℝ → ℝ → ℝ → Prop) :
    ∀ a b c d : ℝ, sol a b c d ↔
      a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 → (a + b + c = d ∧ 1 / a + 1 / b + 1 / c = 1 / d) := sorry

/-- [model] putnam_1977_b6: `Nat.card H = 0` for infinite H (fix: `[Finite H]`). -/
theorem pos_card_pb1977b6 (G : Type) [Group G] (H : Subgroup G) (h : ℕ) (hh : h = Nat.card H) :
    3 * h ^ 2 ≥ 0 := sorry

/-- [exact shape] putnam_2005_a3: `deriv g z = 0` also holds where g is not differentiable. -/
theorem pos_deriv_pb2005a3 (g : ℂ → ℂ) (z : ℂ) (hz : z ≠ 0 ∧ deriv g z = 0) : ‖z‖ = 1 := sorry

/-- [model] putnam_2011_a1: `0 < l` for `l : Fin n → ℕ` is the Pi order (∃ i, 0 < l i). -/
theorem pos_piOrder_pb2011a1 (n : ℕ) (l : Fin n → ℕ) (hl : 0 < l) : ∀ i, 0 < l i := sorry

/-- [model] putnam_1968_a3: `i + 1` on `Fin (2^n)` wraps around. -/
theorem pos_finWrap_pb1968a3 (n : ℕ) (s : Fin (2 ^ n) → ℕ) :
    ∀ i : Fin (2 ^ n), i + 1 < 2 ^ n → s i ≤ s (i + 1) := sorry

/-! ## Formal Conjectures misformalization issues -/

/-- [model] #6473 erdos_748: `2 ^ (n / 2)` floors n/2 in ℕ. -/
theorem pos_intDiv_fc6473 (f : ℕ → ℕ) : ∀ᶠ n : ℕ in Filter.atTop, 2 ^ (n / 2) ≤ f n := sorry
theorem neg_fc6473 (f : ℕ → ℕ) : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ^ ((n : ℝ) / 2) ≤ f n := sorry

/-- [model] #6467 erdos_44: `N.sqrt / 2 ≤ A.card` computed in ℕ. -/
theorem pos_intDiv_fc6467 (N : ℕ) : ∃ A ⊆ Finset.Icc 1 N, N.sqrt / 2 ≤ A.card := sorry
theorem neg_fc6467 (N : ℕ) : ∃ A ⊆ Finset.Icc 1 N, Real.sqrt N / 2 ≤ (A.card : ℝ) := sorry

/-- [model] #6479 GraphConjecture141: `(G.girth / 2 : ℤ)` floors. -/
@[trap_ok natZero "[model] 결론을 단순화해서 생긴 반례라 측정에서 뺀다"]
theorem pos_intDiv_fc6479 (girth lam tree : ℕ) : (girth / 2 : ℤ) - 1 + lam ≤ tree := sorry
@[trap_ok natZero "[model] 결론을 단순화해서 생긴 반례라 측정에서 뺀다"]
theorem neg_fc6479 (girth lam tree : ℕ) : (girth : ℝ) / 2 - 1 + lam ≤ tree := sorry

/-- [model] #5668 erdos_830: `(1 / 2) * card` is formed in ℕ, so `A x = 0` (a non-Prop def). -/
noncomputable def fc5668_A (x : ℝ) : ℝ :=
  ((1 / 2 * ((Finset.range ⌊x⌋₊).filter (fun n => n % 7 = 3)).card : ℕ) : ℝ)
theorem pos_intDiv_fc5668 (x : ℝ) (hx : 284 ≤ x) : 1 ≤ fc5668_A x := sorry

/-- [model] #5660 erdos_564: unannotated `c` elaborates as ℕ (no junk value; type inference). -/
theorem pos_litNat_fc5660 (R : ℕ → ℕ) : ∃ c > 0, ∀ n, 2 ^ (2 ^ (c * n)) ≤ R n := sorry

/-- [model] #1343 erdos_366: existential trivially witnessed by n = 0. -/
def Full3 (n : ℕ) : Prop := ∀ p, p.Prime → p ∣ n → p ^ 3 ∣ n
theorem pos_trivialWitness_fc1343 : ∃ n : ℕ, Full3 n ∧ Full3 (n + 1) := sorry

/-- [model] #5026 OEIS/211417: `∃ D : ℤ` is witnessed by D = 0. -/
theorem pos_trivialWitness_fc5026 (x y : ℕ → ℤ) : ∃ D : ℤ, ∀ n : ℕ, x n ∣ D * y n := sorry

/-- [model] #6563 OEIS/105751: `∃ n, p ∣ a n` witnessed by the zero term a 0 = 0. -/
theorem pos_trivialWitness_fc6563 (a : ℕ → ℤ) (ha : a 0 = 0) (p : ℕ) (hp : p.Prime) :
    ∃ n : ℕ, (p : ℤ) ∣ a n := sorry

/-- [model] #5664 erdos_692: `Set.ncard` of an infinite set is 0. -/
theorem pos_card_fc5664 (S : ℕ → Set ℕ) : ∀ᶠ n : ℕ in Filter.atTop, n ≤ (S n).ncard := sorry

/-- [model] #5657 erdos_505: `Metric.diam` of an unbounded set is 0. -/
theorem pos_diam_fc5657 (S : Set ℝ) (F : ℕ → Set ℝ) (hF : ∀ i, Metric.diam (F i) < Metric.diam S) :
    S ⊆ ⋃ i, F i := sorry

/-- [model] d995ef5d green_22: `9 ≤ sInf {…}` with `sInf ∅ = 0` in ℕ. -/
theorem pos_sSupInf_fcd995ef5d (P : ℕ → Prop) : 9 ≤ sInf {N | P N} := sorry

/-- [model] #5637 erdos_321: `Real.log^[k]` iterates can go negative (`log x = log |x|`). -/
theorem pos_realDomain_fc5637 (N : ℝ) (r : ℕ) (h : 1 ≤ Real.log^[2 * r] N) :
    0 < Real.log (Real.log N) := sorry

/-- [model] #4979 erdos_15: `Summable` is unconditional (absolute) summability. -/
theorem pos_summable_fc4979 : Summable (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * (k + 1) / (k + 2)) := sorry

/-- [model] #5654 erdos_486: `ZMod 0 = ℤ` is included when every modulus n is quantified. -/
theorem pos_zmodZero_fc5654 (X : (n : ℕ) → Set (ZMod n)) (m : ℕ) : ∀ n : ℕ, (m : ZMod n) ∉ X n := sorry

end Real
