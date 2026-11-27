import Mathlib
import ConventionTrap

/-! Unit tests for the junk-function and Lean-operation kinds (`#trap_check`). -/

set_option linter.conventionTrap false
set_option warn.sorry false

namespace NK

/-! ## sSupInf -/
theorem sInf_a (S : Set ℕ) : sInf S ∈ S := sorry
theorem sInf_b (S : Set ℕ) (h : S.Nonempty) : sInf S ∈ S := Nat.sInf_mem h
theorem sSup_a (S : Set ℝ) (x : ℝ) (hx : x ∈ S) : x ≤ sSup S := sorry
theorem sSup_b (S : Set ℝ) (x : ℝ) (hx : x ∈ S) (hb : BddAbove S) : x ≤ sSup S := le_csSup hb hx
theorem iSup_a (f : ℕ → ℝ) (i : ℕ) : f i ≤ ⨆ j, f j := sorry
theorem iSup_b (f : ℕ → ℝ) (i : ℕ) (hb : BddAbove (Set.range f)) : f i ≤ ⨆ j, f j := le_ciSup hb i
theorem sInf_icc (a b : ℕ) (h : a ≤ b) : sInf (Set.Icc a b) = a := sorry

/-! ## card -/
theorem ncard_a (S : Set ℕ) (x : ℕ) (hx : x ∈ S) : 0 < S.ncard := sorry
theorem ncard_b (S : Set ℕ) (hS : S.Finite) (x : ℕ) (hx : x ∈ S) : 0 < S.ncard := Set.ncard_pos hS |>.mpr ⟨x, hx⟩
theorem ncard_fin (n : ℕ) : (Set.Iio n).ncard = n := sorry
theorem natCard_a (α : Type) [Nonempty α] : 0 < Nat.card α := sorry
theorem natCard_b (α : Type) [Finite α] [Nonempty α] : 0 < Nat.card α := Nat.card_pos
theorem natCard_fin (n : ℕ) : Nat.card (Fin n) = n := Nat.card_eq_fintype_card.trans (Fintype.card_fin n)

/-! ## diam -/
theorem diam_a (S : Set ℝ) (x y : ℝ) (hx : x ∈ S) (hy : y ∈ S) : dist x y ≤ Metric.diam S := sorry
theorem diam_b (S : Set ℝ) (hS : Bornology.IsBounded S) (x y : ℝ) (hx : x ∈ S) (hy : y ∈ S) :
    dist x y ≤ Metric.diam S := Metric.dist_le_diam_of_mem hS hx hy
theorem diam_icc (a b : ℝ) (h : a ≤ b) : Metric.diam (Set.Icc a b) = b - a := Real.diam_Icc h

/-! ## deriv -/
theorem deriv_a (f : ℝ → ℝ) (x : ℝ) : HasDerivAt f (deriv f x) x := sorry
theorem deriv_b (f : ℝ → ℝ) (x : ℝ) (hf : DifferentiableAt ℝ f x) : HasDerivAt f (deriv f x) x :=
  hf.hasDerivAt
theorem deriv_sq (x : ℝ) : deriv (fun y => y ^ 2) x = 2 * x := by simp

/-! ## piOrder -/
theorem pi_a (n : ℕ) (l : Fin n → ℕ) (hl : 0 < l) : ∀ i, 0 < l i := sorry
theorem pi_b (n : ℕ) (l : Fin n → ℕ) (hl : ∀ i, 0 < l i) : ∀ i, 0 < l i := hl
theorem pi_le (n : ℕ) (l m : Fin n → ℕ) (h : l ≤ m) (i : Fin n) : l i ≤ m i := h i

/-! ## finWrap -/
theorem fin_a (n : ℕ) (i : Fin (n + 1)) : (i + 1 : Fin (n + 1)).val = i.val + 1 := sorry
theorem fin_b (n : ℕ) (i : Fin (n + 1)) (h : i.val + 1 < n + 1) :
    (i + 1 : Fin (n + 1)).val = i.val + 1 := sorry

/-! ## zmodZero -/
theorem zmod_a (n m : ℕ) (h : (m : ZMod n) = 0) : n ∣ m := sorry
theorem zmod_b (n m : ℕ) (hn : n ≠ 0) (h : (m : ZMod n) = 0) : n ∣ m := sorry
theorem zmod_lit (m : ℕ) (h : (m : ZMod 5) = 0) : 5 ∣ m := sorry

end NK
/--
info: sSupInf unknown: sInf S ⊢ S.Nonempty
discharged: 0
-/
#guard_msgs in #trap_check NK.sInf_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check NK.sInf_b
/--
info: sSupInf unknown: sSup S ⊢ S.Nonempty ∧ BddAbove S
discharged: 0
-/
#guard_msgs in #trap_check NK.sSup_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check NK.sSup_b
/--
info: sSupInf unknown: ⨆ j, f j ⊢ Nonempty ℕ ∧ BddAbove (Set.range fun j => f j)
discharged: 0
-/
#guard_msgs in #trap_check NK.iSup_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check NK.iSup_b
/-- info: discharged: 1 -/
#guard_msgs in #trap_check NK.sInf_icc
/--
info: card unknown: S.ncard ⊢ S.Finite
discharged: 0
-/
#guard_msgs in #trap_check NK.ncard_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check NK.ncard_b
/-- info: discharged: 1 -/
#guard_msgs in #trap_check NK.ncard_fin
/--
info: card unknown: Nat.card α ⊢ Finite α
discharged: 0
-/
#guard_msgs in #trap_check NK.natCard_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check NK.natCard_b
/-- info: discharged: 1 -/
#guard_msgs in #trap_check NK.natCard_fin
/--
info: diam unknown: Metric.diam S ⊢ Bornology.IsBounded S
discharged: 0
-/
#guard_msgs in #trap_check NK.diam_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check NK.diam_b
/-- info: discharged: 1 -/
#guard_msgs in #trap_check NK.diam_icc
/--
info: deriv unknown: deriv f x ⊢ DifferentiableAt ℝ f x
discharged: 0
-/
#guard_msgs in #trap_check NK.deriv_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check NK.deriv_b
/-- info: discharged: 1 -/
#guard_msgs in #trap_check NK.deriv_sq
/--
info: piOrder unknown: 0 < l ⊢ ∀ (a : Fin n), 0 a < l a
discharged: 0
-/
#guard_msgs in #trap_check NK.pi_a
/-- info: discharged: 0 -/
#guard_msgs in #trap_check NK.pi_b
/-- info: discharged: 0 -/
#guard_msgs in #trap_check NK.pi_le
/--
info: finWrap unknown: i + 1 ⊢ ↑i + 1 < n + 1
discharged: 0
-/
#guard_msgs in #trap_check NK.fin_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check NK.fin_b
/--
info: zmodZero reachable: ↑m ⊢ n ≠ 0 {n=0, m=0}
discharged: 0
-/
#guard_msgs in #trap_check NK.zmod_a
/-- info: discharged: 1 -/
#guard_msgs in #trap_check NK.zmod_b
/-- info: discharged: 0 -/
#guard_msgs in #trap_check NK.zmod_lit


namespace NoiseRegression

theorem deriv_from_hasDerivAt (f : ℝ → ℝ) (x y : ℝ) (h : HasDerivAt f y x) :
    deriv f x = y := h.deriv
/-- info: discharged: 1 -/
#guard_msgs in #trap_check deriv_from_hasDerivAt

set_option linter.conventionTrap.mode "ci" in
theorem sqrt_from_Ioi (x : ℝ) (h : x ∈ Set.Ioi 0) : Real.sqrt x ^ 2 = x :=
  Real.sq_sqrt (le_of_lt h)
/-- info: discharged: 1 -/
set_option linter.conventionTrap.mode "ci" in
#guard_msgs in #trap_check sqrt_from_Ioi

end NoiseRegression

/--
info: card benign: Nat.card α ⊢ Finite α
discharged: 0
-/
#guard_msgs in #trap_check Nat.card_pos_iff
