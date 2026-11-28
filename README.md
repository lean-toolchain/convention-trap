# convention-trap

Lean 4 linter + CI report that flags theorem **statements** whose meaning was changed by a
Mathlib convention (junk value): truncated `ℕ` subtraction, `x / 0 = 0`, `√(-1) = 0`,
`a % 0 = a`, `ℕ` containing 0, …

Spec: [`../idea-research/valid/convention-trap-detector`](../idea-research/valid/convention-trap-detector/README.md)
(design docs in `design/`).

## How it decides
For every trap site in the statement (never the proof):

1. **Detect** (`ConventionTrap/Detect.lean`) — pattern on elaborated `Expr`; collect the
   hypotheses usable *at that position* (binders, implication premises, positive `∧` siblings,
   `if` branches, `i ∈ s` in `∑`/`∏`, derived facts like `Nat.Prime p → 2 ≤ p`, local Prop
   definitions unfolded). Circularity (`x : Fin (n - k)`) and polarity (`¬`) rules apply.
2. **Discharge** — prove the needed condition with `assumption, omega, positivity`
   (CI adds `linarith, simp_all +arith, grind`) under a heartbeat budget → `safe`, silent.
3. **Benign** — if the statement is still provable in the junk region → hidden (CI report only).
4. **Witness** — concrete values satisfying all hypotheses and breaking the condition →
   **warning** with the example (`reachable`). Otherwise `unknown` (info; shown in CI).
5. **Refute** (`natZero` / `falseStatement`) — only for statements that are *not* proved
   (`sorry`/axiom): enumerate small ℕ/ℤ/Bool values (0 first) → **error**.

Kinds: `natSub natSubHyp div intDiv modZero intDivNeg realDomain rpow castSub natZero intToNat
expTrunc falseStatement trivialWitness` and junk-function / Lean-operation kinds
`sSupInf card diam deriv piOrder finWrap zmodZero integral tsum guardScope litNat trivialProof` (set/function conditions: an unproved, non-benign
condition is a warning directly, since no concrete witness can be built).

## Use
```toml
[[require]]
name = "convention-trap"
path = "../convention-trap-detector"   # or git
```
`import ConventionTrap` — the linter is on by default.

```
warning: [natSub] a - b : ℕ 는 a < b일 때 0으로 잘립니다. 가정에서 b ≤ a를 증명하지 못했습니다.
  예: a = 0, b = 1 일 때 가정을 모두 만족하고 a < b 입니다.
  시도: assumption, omega, positivity (각 실패)
빠른 수정 [natSub]: (a b : ℕ) (h_trap : b ≤ a) : …
error: [natZero] 명제가 거짓입니다: a = 0, b = 0, c = 0, n = 3 에서 결론이 거짓입니다. 0 < a, 0 < b, 0 < c 를 의도했나요?
```

Options: `linter.conventionTrap`, per group `.natSub .div .intDiv .realDomain .castSub .natZero`,
`.junkFun`, `.leanOps`, `.heartbeats`, `.mode` (`"editor"`/`"ci"`), `.witness`, `.benign`, `.selfGuard`,
`.unfoldDepth`, `.showUnknown`.

Suppress with a mandatory reason:
```lean
@[trap_ok natSub "truncated difference is intended"]
theorem foo ...
```

`#trap_check foo` prints all verdicts (incl. benign/unknown) for debugging.

### CI report
```
lake build && scripts/trap-report [--modules M,...] [--decls N,...] [--mode ci|editor]
  [--format md|json|both] [--out-dir trap-report] [--fail-on error|warning|never]
  [--no-witness] [--no-benign] [--no-self-guard] [--unfold-depth N]
```
Writes `trap-report/report.json` (`trap/report@1`) and `report.md`. Exit 0/1/2/4.
Other repos without modification: `scripts/trap-report-external.sh <repo> <Lib>` (exit 3 on
unsupported toolchain, 4 on build failure).

## Tests
```
lake build ConventionTrapTest          # #guard_msgs unit tests (Kinds, Linter, Corpus)
scripts/trap-report --modules ConventionTrapTest.Corpus --out-dir /tmp/tr
python3 scripts/eval.py /tmp/tr/report.json
```

## Benchmark results

A *misformalized statement* here is a theorem statement that compiles but means something other
than intended because of a Mathlib convention (e.g. `0 - 1 = 0` in `ℕ`, `x / 0 = 0`).

| Metric | Data | Result |
|---|---|---|
| **Detection rate on misformalized statements** — statements that other projects later found to be wrong and fixed, checked in their *pre-fix* form: does the tool warn? | 25 statements from miniF2F, PutnamBench and Formal Conjectures | **22 / 25 (88%)** |
| **Warning rate on correct statements** — theorems already proved and reviewed, so none should be misformalized: how often does the tool warn? | all 257,221 Mathlib declarations | **10 declarations (0.004%)** |

Mathlib v4.36.0, measured by the CI workflows `ci` and `mathlib-noise`.

**Misformalized statements** (`test/ConventionTrapTest/Real.lean`; sources and per-case notes in
[`real-cases/README.md`](real-cases/README.md)). Missed:
- miniF2F `amc12a_2021_p25`: the function is only specified for `0 < n`, so no counterexample value is found.
- miniF2F `imo_1982_p1`: values of `f m` are not searched as witnesses.
- Formal Conjectures #6467: needs evaluating a statement that quantifies over subsets, which is
  skipped to avoid exponential blowup.

**Correct statements.** All 10 flagged Mathlib declarations are Prop definitions that use a junk
value on purpose (`Nat.ModEq`, `Int.ModEq`, `LiouvilleWith`, `Nat.ProbablePrime`, …), plus one
lemma whose existential is witnessed by `0`. Proved theorems are trusted: a theorem proved without
a guard is true in the junk case too, so it cannot be misformalized
(`linter.conventionTrap.trustProofs`).

**Limits.** 25 cases is small (one or two per trap kind), so the detection rate has a wide error
margin. Some cases are simplified models of the original project definitions (`[model]` in the
file). Mathlib contains no misformalized statements, so it measures warnings, not detection.

**Reproduce.** Run the `ci` workflow (detection rate in the job summary) and `mathlib-noise` with
`sample_mod=1` (artifact `mathlib-noise`: `noise.json`, `review-sample.md`).

## Deviations from the design (deliberate / MVP)
- `trap-report` runs through the Lean interpreter (`lean --run`) instead of `lake exe`: a native
  executable linking Mathlib would compile all of Mathlib to C.
- The randomized fallback beyond the exhaustive range uses a seeded LCG sampler, not Plausible.
- Quick fix offers "add hypothesis" only (no "change to ℤ"); offered only when every variable of
  the condition is a signature binder.
- The corpus is a seed set (see `test/ConventionTrapTest/Corpus.lean`), not the 1,300-item
  double-labelled corpus; Mathlib-wide noise and 1,000-theorem latency runs are not done yet.
- Pinned to Mathlib `v4.36.0` / Lean `v4.36.0`.
