# Adversarial Critique -- 2026-03-12 UTC (Cycle 118, Hostile Review)

## Verdict: CONDITIONAL ACCEPT

---

## 0. CI Status

Commit f43e39c: **SUCCESS** (run 22982420111).
Commit 75bae98: initial run **FAILED** with `elan` infrastructure error (`failed to parse latest release tag`) — not a code issue. Re-run 22982955021 **in progress**. Local `lake build` passes.

`lean_verify` on all 4 main theorems — only standard axioms (propext, Classical.choice, Quot.sound). **Clean.**

---

## 1. Sorry's

**0 sorry's** across 32 files (10,202 lines). No `admit`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque`. **Sound.**

---

## 2. Hidden Axioms

All four main theorems verified with only standard axioms. No `set_option linter.all false`. **Sound.**

---

## 3. Circularity

Import DAG acyclic. **Sound.**

---

## 4. Hypothesis Audit

All 13 hypotheses necessary and independent. Counterexamples documented. **Sound.**

---

## 5. Mathematical Correctness

**Sound.** `CoulombConcreteTheorem42_roundtrip` now includes temperature uniqueness — a strict improvement over cycle 117.

---

## 6. Code Quality

### 6a. maxHeartbeats overrides

**2 remaining:**
- `NewtonianPotential.lean:85` — `set_option maxHeartbeats 800000 in`
- `TorusIntegration.lean:87` — `set_option maxHeartbeats 400000 in`

Both now have explanatory comments (fixed in cycle 117). **ISSUE (Low).**

### 6b. Files over 500 lines

| File | Lines |
|------|-------|
| Section3Helpers.lean | 613 |
| CoulombFluxConv.lean | 560 |
| CoulombNonvacuous.lean | 527 |
| Defs.lean | 510 |

**ISSUE (Low): 4 files over 500 lines.**

### 6c. Line length violations (> 100 chars)

| File | Count |
|------|-------|
| Section3Helpers.lean | 1 |

**Down from 14 (cycle 116) to 1. ISSUE (Low).**

### 6d. Linter warnings — CoulombPSD.lean

CoulombPSD.lean has **12 warnings** that were NOT caught in cycles 116-117:

| Warning | Count |
|---------|-------|
| Unused simp arguments | 7 |
| Unused variables (`hf_smooth`) | 2 |
| Multi-goal tactic issues | 3 |

**ISSUE (Medium): 12 linter warnings in CoulombPSD.lean.** This file was never checked in previous cycles.

### 6e. CoulombNonvacuous.lean unused variables

2 warnings for `hT` (line 24) and `hν` (line 338). These document physical constraints and are acceptable.

---

## 7. Documentation Lies

MEMORY.md line counts are approximately correct after cycle 117 fix. No material discrepancies found.

---

## 8. Generalization Opportunities

### 8a. Weaken velocity smoothness from C∞ to C³ (Medium)

The abstract theorem requires only `ContDiff ℝ 3`. The concrete theorem uses `ContDiff ℝ ⊤`. Could weaken without changing proof substance. Touches all 12 Coulomb files.

### 8b. ~~CoulombNonvacuous should apply main theorem~~ **FIXED** in cycle 116.

### 8c. Extract Gaussian integral lemmas to a reusable module (Medium)

`integral_coord_mul_equilibriumMaxwellian_eq_zero` and `integral_equilibriumMaxwellian` use general techniques (odd symmetry, Fubini factorization) that could be generalized.

### 8d. Extend kernel coverage beyond Coulomb (Medium-Hard)

Only Coulomb instantiated. Maxwell molecules (Ψ = const) would be ~100 lines.

### 8e. ~~Roundtrip lacks uniqueness~~ **FIXED** in cycle 117.

---

## 9. Mathlib Upstreamability

1. **n-dimensional Gaussian integral** — Fubini + `integral_fintype_prod_eq_prod` pattern
2. **`inverse_poly_integrable`** — `(1+‖v‖)⁻ᴺ` integrability for N > dim
3. **`norm_fderiv_eq_iteratedFDeriv_one`** — fderiv/iteratedFDeriv relation
4. **Schwartz decay extraction lemmas**

---

## Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 6a | 2 maxHeartbeats overrides (800000 + 400000) | Low | Open |
| 6b | 4 files over 500 lines (Section3Helpers at 613) | Low | Open |
| 6c | 1 long line in Section3Helpers | Low | Open |
| 6d | 12 linter warnings in CoulombPSD.lean | Medium | **NEW** |
| 8a | Hypothesis 4 could weaken to ContDiff ℝ 3 | Low | Open |
| 8c | Gaussian integral lemmas not generalized | Low | Open |
| 8d | Only Coulomb kernel instantiated | Low | Open |
| 9 | Mathlib PR candidates (4 lemmas) | Low | Open |

---

## Verdict: CONDITIONAL ACCEPT

0 sorry's, 0 non-standard axioms, 32 files, 10,202 lines. Full round-trip with uniqueness proved.

**Condition for full ACCEPT:** Fix 12 linter warnings in CoulombPSD.lean (issue 6d).
