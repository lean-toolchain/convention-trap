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

## Measured on real incidents
See [`real-cases/README.md`](real-cases/README.md): 25 buggy / 7 fixed statements from miniF2F,
PutnamBench and Formal Conjectures — currently 22/25 flagged by default, 0/7 false positives.

## Measured on Mathlib (false-positive test)
All 257,221 Mathlib declarations (CI workflow `mathlib-noise`): warnings on 10 (0.004%), all
intentional junk-value Prop definitions. Proved theorems are trusted (`linter.conventionTrap.trustProofs`).

## Measured on the seed corpus (25 positive / 30 negative, `test/ConventionTrapTest/Corpus.lean`)
| configuration | recall | negatives flagged | worst per-kind FP rate |
|---|---|---|---|
| full, `--mode ci` | 24/25 (96%) | 0/30 | 0% |
| full, `--mode editor` | 24/25 (96%) | 0/30 | 0% |
| baseline (`--no-witness --no-benign --no-self-guard --unfold-depth 0`) | 25/25 | 4/30 | 50% (natSubHyp) |

The miss is miniF2F IMO 2001 P6: its hypothesis `h₄` does imply the guard, but only via nonlinear
reasoning, so the site is `unknown` (listed in the CI report's `unknown` section, hidden in the editor).
Buzzard's FLT statement is reported as `error [natZero]` with `a = b = c = 0, n = 3`.

## Deviations from the design (deliberate / MVP)
- `trap-report` runs through the Lean interpreter (`lean --run`) instead of `lake exe`: a native
  executable linking Mathlib would compile all of Mathlib to C.
- The randomized fallback beyond the exhaustive range uses a seeded LCG sampler, not Plausible.
- Quick fix offers "add hypothesis" only (no "change to ℤ"); offered only when every variable of
  the condition is a signature binder.
- The corpus is a seed set (see `test/ConventionTrapTest/Corpus.lean`), not the 1,300-item
  double-labelled corpus; Mathlib-wide noise and 1,000-theorem latency runs are not done yet.
- Pinned to Mathlib `v4.36.0` / Lean `v4.36.0`.
