import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import ConventionTrap

/-!
# Seed corpus (testing.md)

Naming convention read by `scripts/eval.py`:
* `pos_<kind>_<n>` — must be flagged with `<kind>` (error or warning)
* `neg_<n>`        — must not be flagged at all (errors/warnings)

Origins: `known_*` are the PRD's known incidents; `mut` = Mathlib lemma with its guard removed
(mutation synthesis); `cat` = trap-catalog.md example; `neg` = Mathlib-style guarded statements.
This is a small seed set, not the 1,300-item labelled corpus the PRD targets.
-/

set_option linter.conventionTrap false
set_option warn.sorry false

namespace Corpus

/-! ## Known incidents -/
/-- Buzzard's two-line FLT (false: a = b = c = 0). -/
theorem pos_natZero_known_flt : ∀ a b c n : ℕ, 2 < n → a ^ n + b ^ n ≠ c ^ n := sorry
/-- miniF2F `imo_2001_p6` as originally stated (natural subtraction inside a hypothesis). -/
theorem pos_natSubHyp_known_imo2001p6 (a b c d : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : d < c) (h₂ : c < b) (h₃ : b < a)
    (h₄ : a * c + b * d = (b + d + a - c) * (b + d + c - a)) : ¬ Nat.Prime (a * b + c * d) := sorry

/-! ## Mutations (guard removed) -/
theorem pos_natSub_mut1 (n m : ℕ) : n - m + m = n := sorry
theorem pos_natSub_mut2 (n : ℕ) : n - 1 + 1 = n := sorry
theorem pos_natSub_mut3 (a b c : ℕ) : a - b - c = a - (b + c) + 0 ∧ a - b + b = a := sorry
theorem pos_div_mut1 (a : ℝ) : a * a⁻¹ = 1 := sorry
theorem pos_div_mut2 (a b : ℝ) : a / b * b = a := sorry
theorem pos_div_mut3 (a b c : ℚ) : a / c + b / c = (a + b) / c ∧ c / c = 1 := sorry
theorem pos_intDiv_mut1 (a b : ℕ) : b * (a / b) = a := sorry
theorem pos_intDiv_mut2 (a b : ℤ) : a / b * b = a := sorry
theorem pos_modZero_mut1 (a b : ℕ) : a % b < b := sorry
theorem pos_modZero_mut2 (a b : ℤ) : a % b < b := sorry
theorem pos_realDomain_mut1 (x : ℝ) : Real.sqrt x * Real.sqrt x = x := sorry
theorem pos_realDomain_mut2 (x : ℝ) : Real.exp (Real.log x) = x := sorry
theorem pos_realDomain_mut3 (x y : ℝ) : Real.log (x * y) = Real.log x + Real.log y + 0 * Real.sqrt (x - y) := sorry
theorem pos_castSub_mut1 (n m : ℕ) : ((n - m : ℕ) : ℝ) = n - m := sorry
theorem pos_castSub_mut2 (n : ℕ) : ((n - 1 : ℕ) : ℤ) + 1 = n := sorry
theorem pos_intToNat_mut1 (z : ℤ) : (z.toNat : ℤ) = z := sorry
theorem pos_expTrunc_mut1 (a m n : ℕ) : a ^ (m - n) * a ^ n = a ^ m := sorry
theorem pos_rpow_mut1 (x : ℝ) : (x ^ (1/2 : ℝ)) ^ 2 = x := sorry

/-! ## Catalog examples -/
theorem pos_div_cat (x : ℝ) : x / x = 1 := sorry
theorem pos_intDivNeg_cat (a b : ℤ) : (-a) / b = -(a / b) := sorry
theorem pos_natZero_cat1 : ∀ n : ℕ, (n - 1) + 1 = n := sorry
theorem pos_natZero_cat2 : ∀ a b : ℕ, a ∣ b → a ≤ b := sorry
theorem pos_natZero_cat3 : ∀ n : ℕ, 0 < n * n := sorry

/-! ## Negatives: guarded / safe statements (shapes taken from Mathlib lemmas) -/
theorem neg_1 (n m : ℕ) (h : m ≤ n) : n - m + m = n := Nat.sub_add_cancel h
theorem neg_2 (n : ℕ) (h : 0 < n) : n - 1 + 1 = n := Nat.sub_add_cancel h
theorem neg_3 (a : ℝ) (h : a ≠ 0) : a * a⁻¹ = 1 := mul_inv_cancel₀ h
theorem neg_4 (a b : ℝ) (h : b ≠ 0) : a / b * b = a := div_mul_cancel₀ a h
theorem neg_5 (a b : ℕ) (h : b ∣ a) : b * (a / b) = a := Nat.mul_div_cancel' h
theorem neg_6 (a b : ℕ) (h : 0 < b) : a % b < b := Nat.mod_lt a h
theorem neg_7 (x : ℝ) (h : 0 ≤ x) : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt h
theorem neg_8 (x : ℝ) (h : 0 < x) : Real.exp (Real.log x) = x := Real.exp_log h
theorem neg_9 (n m : ℕ) (h : m ≤ n) : ((n - m : ℕ) : ℝ) = n - m := Nat.cast_sub h
theorem neg_10 (z : ℤ) (h : 0 ≤ z) : (z.toNat : ℤ) = z := Int.toNat_of_nonneg h
theorem neg_11 (a m n : ℕ) (h : n ≤ m) : a ^ (m - n) * a ^ n = a ^ m := by
  rw [← pow_add, Nat.sub_add_cancel h]
theorem neg_12 (a b : ℕ) : a - b ≤ a := Nat.sub_le a b
theorem neg_13 (a b : ℕ) : a / b * b ≤ a := Nat.div_mul_le_self a b
theorem neg_14 (a b : ℕ) : a % b ≤ a := Nat.mod_le a b
theorem neg_15 (p : ℕ) (hp : p.Prime) : p - 1 + 1 = p := by have := hp.two_le; omega
theorem neg_16 (n : ℕ) : ∑ i ∈ Finset.range n, (n - i) = ∑ i ∈ Finset.range n, (n - i) := rfl
theorem neg_17 (a b : ℕ) (h : a - b = 1) : a = b + 1 := by omega
theorem neg_18 (x : ℝ) (hx : 0 < x) : x / x = 1 := div_self hx.ne'
theorem neg_19 (n : ℕ) (hn : 2 ≤ n) : (n - 2) + 2 = n := by omega
theorem neg_20 (a b : ℕ) (hab : b < a) : 0 < a - b := Nat.sub_pos_of_lt hab
theorem neg_21 : ∀ a b c n : ℕ, 0 < a → 0 < b → 0 < c → 2 < n → a ^ n + b ^ n ≠ c ^ n := sorry
theorem neg_22 (x : ℝ) : Real.sqrt (x ^ 2) = |x| := Real.sqrt_sq_eq_abs x
theorem neg_23 (x : ℝ) : Real.sqrt (x ^ 2 + 1) ^ 2 = x ^ 2 + 1 := Real.sq_sqrt (by positivity)
theorem neg_24 (n : ℕ) : n / 1 = n := Nat.div_one n
theorem neg_25 (x : ℝ) (h : 1 < x) : 0 < Real.log x := Real.log_pos h
theorem neg_26 (a b : ℤ) (hb : 0 < b) : a % b < b := Int.emod_lt_of_pos a hb
theorem neg_27 (n : ℕ) (h : n ≠ 0) : n - 1 < n := by omega
theorem neg_28 (a b : ℕ) (h₁ : 0 < a) (h₂ : a < b) : b - a < b := by omega
theorem neg_29 (x y : ℝ) (hy : 0 < y) : x / y * y = x := div_mul_cancel₀ x hy.ne'
theorem neg_30 (k : ℕ) : (2 * k + 2) - 2 = 2 * k := by omega

end Corpus
