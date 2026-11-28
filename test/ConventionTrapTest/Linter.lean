import ConventionTrap

/-!
Linter-level tests: severities, message format, quick-fix text, `@[trap_ok]`, and that
proof bodies / `example` are never inspected.
-/

set_option warn.sorry false

namespace L

/--
error: [natZero] 명제가 거짓입니다: a = 0, b = 10 에서 결론이 거짓입니다. 0 < a 를 의도했나요?
---
info: 빠른 수정 [natZero]: 
  [apply] (a b : ℕ) (h : a + b = 10) (h_pos_a : 0 < a) : (a - b) + b = a
---
warning: [natSub] a - b : ℕ 는 a < b일 때 0으로 잘립니다. 가정에서 b ≤ a를 증명하지 못했습니다.
  예: a = 0, b = 10 일 때 가정을 모두 만족하고 a < b 입니다.
  시도: assumption, omega, positivity (각 실패)

Note: This linter can be disabled with `set_option linter.conventionTrap false`
---
info: 빠른 수정 [natSub]: 
  [apply] (a b : ℕ) (h : a + b = 10) (h_trap : b ≤ a) : (a - b) + b = a
-/
#guard_msgs in
theorem natSub_warn (a b : ℕ) (h : a + b = 10) : (a - b) + b = a := sorry

-- Silent: the condition follows from `h` by omega.
#guard_msgs in
theorem natSub_ok (a b : ℕ) (h : b < a) : (a - b) + b = a := by omega

/--
error: [natZero] 명제가 거짓입니다: a = 0, b = 0, c = 0, n = 3 에서 결론이 거짓입니다. 0 < a, 0 < b, 0 < c 를 의도했나요?
-/
#guard_msgs in
theorem flt : ∀ a b c n : ℕ, 2 < n → a ^ n + b ^ n ≠ c ^ n := sorry

#guard_msgs in
theorem flt_pos : ∀ a b c n : ℕ, 0 < a → 0 < b → 0 < c → 2 < n → a ^ n + b ^ n ≠ c ^ n := sorry

-- Real variables: refutation is skipped (only ℕ/ℤ/Bool are enumerated).
#guard_msgs in
theorem real_skip (x : ℝ) (hx : 0 < x) : x ^ 2 + 1 ≠ 0 := sorry

-- `@[trap_ok]` with a reason silences the kind.
#guard_msgs in
@[trap_ok natSub "truncated difference is intended here"]
theorem natSub_intended (a b : ℕ) : a - b ≤ a + 1 := by omega

/-- error: trap_ok: 이유가 필요합니다 (empty reason) -/
#guard_msgs in
@[trap_ok natSub ""]
theorem natSub_noreason (a b : ℕ) : a - b ≤ a + 1 := by omega

/--
error: trap_ok: 알 수 없는 함정 종류 'bogus'. 가능한 값: natSub, natSubHyp, div, intDiv, modZero, intDivNeg, realDomain, rpow, castSub, natZero, intToNat, expTrunc, falseStatement, trivialWitness, sSupInf, card, diam, deriv, piOrder, finWrap, zmodZero, integral, tsum, guardScope, litNat, trivialProof
-/
#guard_msgs in
@[trap_ok bogus "x"]
theorem bad_kind (a b : ℕ) : a - b ≤ a + 1 := by omega

-- Junk use inside a proof is legitimate and not reported.
#guard_msgs in
theorem in_proof (a : ℕ) : a + 0 = a := by
  have : a - (a + 1) = 0 := by omega
  omega

-- `example` is not checked.
#guard_msgs in
example (a b : ℕ) : (a - b) + b = a := sorry

-- Prop-valued definitions are checked for sites, never refuted.
/--
warning: [div] 1 / x : ℝ 는 x = 0일 때 0입니다 (x / 0 = 0, 0⁻¹ = 0). 가정에서 x ≠ 0를 증명하지 못했습니다.
  예: x = 0 일 때 가정을 모두 만족하고 x = 0 입니다.
  시도: assumption, omega, positivity (각 실패)

Note: This linter can be disabled with `set_option linter.conventionTrap false`
---
info: 빠른 수정 [div]: 
  [apply] (x : ℝ) (h_trap : x ≠ 0) : Prop
-/
#guard_msgs in
def Recip (x : ℝ) : Prop := 1 / x < 2

-- Per-kind option.
#guard_msgs in
set_option linter.conventionTrap.natSub false in
theorem natSub_off (a b : ℕ) : (a - b) * 2 = 2 * a - 2 * b := by omega

-- Benign: in the junk region (b > a) the statement still holds, so nothing is shown.
#guard_msgs in
theorem benign_le (a b : ℕ) : a - b ≤ a := Nat.sub_le a b

-- Baseline mode (`witness false`): unproved conditions are warnings without examples.
/--
warning: [natSub] a - b : ℕ 는 a < b일 때 0으로 잘립니다. 가정에서 b ≤ a를 증명하지 못했습니다 (반례 값도 찾지 못함).
  시도: assumption, omega, positivity (각 실패)

Note: This linter can be disabled with `set_option linter.conventionTrap false`
---
info: 빠른 수정 [natSub]: 
  [apply] (a b : ℕ) (h_trap : b ≤ a) : (a - b) + b = a
-/
#guard_msgs in
set_option linter.conventionTrap.witness false in
set_option linter.conventionTrap.natZero false in
theorem natSub_baseline (a b : ℕ) : (a - b) + b = a := sorry

end L
