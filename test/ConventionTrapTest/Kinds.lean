import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import ConventionTrap

/-!
Unit tests per trap kind (testing.md): for each kind
(a) no condition → reported, (b) condition as hypothesis → silent,
(c) condition derivable by omega → silent, (d) condition as premise → silent.
`#trap_check` prints every finding (including benign / unknown) and the discharged count.
-/

set_option linter.conventionTrap false
set_option warn.sorry false

namespace T

/-! ## natSub -/
theorem natSub_a (a b : ℕ) : (a - b) + b = a := sorry
theorem natSub_b (a b : ℕ) (h : b ≤ a) : (a - b) + b = a := by omega
theorem natSub_c (a b : ℕ) (h : b < a) : (a - b) + b = a := by omega
theorem natSub_d (a b : ℕ) : b ≤ a → (a - b) + b = a := by omega

/--
info: natZero false: ∀ (a b : ℕ), a - b + b = a {a=0, b=1}
natSub reachable: a - b ⊢ b ≤ a {a=0, b=1}
discharged: 0
-/
#guard_msgs in #trap_check natSub_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check natSub_b
/-- info: discharged: 1 -/
#guard_msgs in #trap_check natSub_c
/-- info: discharged: 1 -/
#guard_msgs in #trap_check natSub_d

/-! ## natSubHyp (self-guard, improvement 3) -/
theorem natSubHyp_a (a b : ℕ) (h : a - b < 3) : a < b + 3 := sorry
theorem natSubHyp_safe (a b : ℕ) (h : a - b = 1) : a = b + 1 := by omega

/--
info: natSubHyp reachable: a - b ⊢ b ≤ a {a=0, b=1}
discharged: 0
-/
#guard_msgs in #trap_check natSubHyp_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check natSubHyp_safe

/-! ## div (fields) -/
theorem div_a : ∀ x : ℝ, x / x = 1 := sorry
theorem div_b (x : ℝ) (hx : x ≠ 0) : x / x = 1 := div_self hx
theorem div_c (x : ℝ) (hx : 0 < x) : x / x = 1 := div_self hx.ne'
theorem div_d : ∀ x : ℝ, x ≠ 0 → x / x = 1 := fun _ hx => div_self hx
theorem inv_a (x : ℝ) : x * x⁻¹ = 1 := sorry

/--
info: div reachable: x / x ⊢ x ≠ 0 {x=0}
discharged: 0
-/
#guard_msgs in #trap_check div_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check div_b
/-- info: discharged: 1 -/
#guard_msgs in #trap_check div_c
/-- info: discharged: 1 -/
#guard_msgs in #trap_check div_d
/--
info: div reachable: x⁻¹ ⊢ x ≠ 0 {x=0}
discharged: 0
-/
#guard_msgs in #trap_check inv_a

/-! ## intDiv / modZero -/
theorem intDiv_a (a b : ℕ) : a / b * b = a := sorry
theorem intDiv_b (a b : ℕ) (h : b ∣ a) : a / b * b = a := Nat.div_mul_cancel h
theorem intDiv_benign (a b : ℕ) : a / b * b ≤ a := Nat.div_mul_le_self a b
theorem mod_a : ∀ a b : ℕ, a % b < b := sorry
theorem mod_b (a b : ℕ) (hb : 0 < b) : a % b < b := Nat.mod_lt _ hb
theorem mod_d : ∀ a b : ℕ, 0 < b → a % b < b := fun _ _ hb => Nat.mod_lt _ hb

/--
info: natZero false: ∀ (a b : ℕ), a / b * b = a {a=1, b=0}
intDiv reachable: a / b ⊢ b ∣ a {a=1, b=0}
discharged: 0
-/
#guard_msgs in #trap_check intDiv_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check intDiv_b
/--
info: intDiv benign: a / b ⊢ b ∣ a
discharged: 0
-/
#guard_msgs in #trap_check intDiv_benign
/--
info: natZero false: ∀ (a b : ℕ), a % b < b {a=0, b=0}
modZero reachable: a % b ⊢ b ≠ 0 {b=0}
discharged: 0
-/
#guard_msgs in #trap_check mod_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check mod_b
/-- info: discharged: 1 -/
#guard_msgs in #trap_check mod_d

/-! ## intDivNeg (editor ℤ range {-1,0,1} cannot refute; CI mode does) -/
theorem intDivNeg_a (a b : ℤ) : (-a) / b = -(a / b) := sorry
theorem intDivNeg_b (a b : ℤ) (_ha : 0 ≤ a) (_hb : 0 < b) (h : b ∣ a) : a / b * b = a :=
  Int.ediv_mul_cancel h

/--
info: intDiv reachable: -a / b ⊢ b ∣ -a {a=-1, b=0}
intDivNeg reachable: -a / b ⊢ 0 ≤ -a ∧ 0 < b {a=0, b=0}
intDiv reachable: a / b ⊢ b ∣ a {a=-1, b=0}
intDivNeg reachable: a / b ⊢ 0 ≤ a ∧ 0 < b {a=0, b=0}
discharged: 0
-/
#guard_msgs in #trap_check intDivNeg_a
/-- info: discharged: 2 -/
#guard_msgs in #trap_check intDivNeg_b

/-! ## realDomain / rpow -/
theorem sqrt_a : ∀ x : ℝ, Real.sqrt x ^ 2 = x := sorry
theorem sqrt_d : ∀ x : ℝ, 0 ≤ x → Real.sqrt x ^ 2 = x := fun _ hx => Real.sq_sqrt hx
theorem log_a : ∀ x : ℝ, Real.exp (Real.log x) = x := sorry
theorem log_d : ∀ x : ℝ, 0 < x → Real.exp (Real.log x) = x := fun _ hx => Real.exp_log hx
theorem rpow_a : ∀ x : ℝ, (x ^ (1/3 : ℝ)) ^ 3 = x := sorry
theorem rpow_d : ∀ x : ℝ, 0 ≤ x → (x ^ (1/3 : ℝ)) ^ (3 : ℝ) = x := sorry

/--
info: realDomain reachable: √x ⊢ 0 ≤ x {x=-1}
discharged: 0
-/
#guard_msgs in #trap_check sqrt_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check sqrt_d
/--
info: realDomain reachable: Real.log x ⊢ 0 < x {x=0}
discharged: 0
-/
#guard_msgs in #trap_check log_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check log_d
/--
info: rpow reachable: x ^ (1 / 3) ⊢ 0 ≤ x {x=-1}
discharged: 1
-/
#guard_msgs in #trap_check rpow_a
/-- info: discharged: 3 -/
#guard_msgs in #trap_check rpow_d

/-! ## castSub -/
theorem castSub_a (n : ℕ) : ((n - 1 : ℕ) : ℝ) = n - 1 := sorry
theorem castSub_d (n : ℕ) : 1 ≤ n → ((n - 1 : ℕ) : ℝ) = n - 1 := fun h => by push_cast [h]; ring

/--
info: natZero false: ∀ (n : ℕ), ↑(n - 1) = ↑n - 1 {n=0}
castSub reachable: ↑(n - 1) ⊢ 1 ≤ n {n=0}
discharged: 0
-/
#guard_msgs in #trap_check castSub_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check castSub_d

/-! ## intToNat -/
theorem toNat_a (z : ℤ) : (z.toNat : ℤ) = z := sorry
theorem toNat_d (z : ℤ) (h : 0 ≤ z) : (z.toNat : ℤ) = z := Int.toNat_of_nonneg h

/--
info: falseStatement false: ∀ (z : ℤ), ↑z.toNat = z {z=-1}
intToNat reachable: z.toNat ⊢ 0 ≤ z {z=-1}
discharged: 0
-/
#guard_msgs in #trap_check toNat_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check toNat_d

/-! ## expTrunc -/
theorem exp_a (a n k : ℕ) : a ^ (n - k) * a ^ k = a ^ n := sorry
theorem exp_d (a n k : ℕ) (h : k ≤ n) : a ^ (n - k) * a ^ k = a ^ n := by
  rw [← pow_add, Nat.sub_add_cancel h]

/--
info: natZero false: ∀ (a n k : ℕ), a ^ (n - k) * a ^ k = a ^ n {a=0, n=0, k=1}
expTrunc reachable: n - k ⊢ k ≤ n {n=0, k=1}
discharged: 0
-/
#guard_msgs in #trap_check exp_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check exp_d

/-! ## facts: Nat.Prime, Finset.range, local definitions (improvement 4) -/
theorem prime_d (p : ℕ) (hp : p.Prime) : (p - 1) + 1 = p := by have := hp.two_le; omega
theorem range_d (n : ℕ) : ∑ i ∈ Finset.range n, (n - i) = ∑ i ∈ Finset.range n, (n - i) := rfl

def IsGood (n : ℕ) : Prop := 0 < n ∧ n % 2 = 1
theorem good_d (n : ℕ) (h : IsGood n) : (n - 1) + 1 = n := by unfold IsGood at h; omega

/-- info: discharged: 1 -/
#guard_msgs in #trap_check prime_d
/-- info: discharged: 2 -/
#guard_msgs in #trap_check range_d
/-- info: discharged: 1 -/
#guard_msgs in #trap_check good_d

/-! ## circularity: a data binder's own type cannot justify the trap inside it -/
theorem fin_circ (n k : ℕ) (x : Fin (n - k)) : (x : ℕ) < n := sorry

/--
info: natSub reachable: n - k ⊢ k ≤ n {n=0, k=1}
discharged: 0
-/
#guard_msgs in #trap_check fin_circ

/-! ## polarity: under `¬` only the guarded-conjunction rule applies (left guards right) -/
theorem neg_pol (a b : ℕ) : ¬ (b ≤ a ∧ a - b = 5) ∨ a - b + b = a := sorry

/--
info: natSub reachable: a - b ⊢ b ≤ a {a=0, b=1}
discharged: 1
-/
#guard_msgs in #trap_check neg_pol

/-! ## proofs are not inspected -/
theorem in_proof (a : ℕ) : a + 0 = a := by
  have : a - a = 0 := Nat.sub_self a
  omega

/-- info: discharged: 0 -/
#guard_msgs in #trap_check in_proof

end T
