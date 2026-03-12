# Adversarial Critique -- 2026-03-12 UTC (Cycle 119, Hostile Review)

## Verdict: CONDITIONAL ACCEPT

---

## 0. CI Status

Local `lake build` passes. Last CI success: commit f43e39c (run 22982420111). Current changes not yet pushed.

`lean_verify` on all 4 main theorems — only standard axioms (propext, Classical.choice, Quot.sound). **Clean.**

---

## 1. Sorry's

**0 sorry's** across 32 files (10,203 lines). No `admit`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque`. **Sound.**

---

## 2. Hidden Axioms

All four main theorems verified with only standard axioms. No `set_option linter.all false`. **Sound.**

---

## 3. Circularity

Import DAG acyclic. **Sound.**

---

## 4. Hypothesis Audit

All 13 hypotheses necessary and independent. Hypothesis 4 (velocity smoothness) now correctly requires only `ContDiff ℝ 3` — matching the abstract theorem. **Improved from cycle 118.**

---

## 5. Mathematical Correctness

**Sound.** Velocity smoothness weakened from C∞ to C³ in cycle 119, matching the abstract theorem's actual requirements. This is a strict improvement.

---

## 6. Code Quality

### 6a. maxHeartbeats overrides

**2 remaining:**
- `NewtonianPotential.lean:85` — `set_option maxHeartbeats 800000 in`
- `TorusIntegration.lean:87` — `set_option maxHeartbeats 400000 in`

Both have explanatory comments. **ISSUE (Low).**

### 6b. Files over 500 lines

| File | Lines |
|------|-------|
| Section3Helpers.lean | 615 |
| CoulombFluxConv.lean | 560 |
| CoulombNonvacuous.lean | 527 |
| Defs.lean | 510 |

**ISSUE (Low): 4 files over 500 lines.**

### 6c. Line length violations (> 100 chars)

| File | Count |
|------|-------|
| Section3Helpers.lean | 1 |

**ISSUE (Low).**

### 6d. Linter warnings — Section3Helpers.lean

Section3Helpers.lean has **11 warnings**:

| Warning | Count |
|---------|-------|
| Unused simp arguments | 8 |
| Unused variables (`hf_smooth`) | 2 |
| `ring` suggestions to use `ring_nf` | (informational, not warnings) |

**ISSUE (Medium): 11 linter warnings in Section3Helpers.lean.**

### ~~6d (old). Linter warnings — CoulombPSD.lean~~ **FIXED** in cycle 119 (ContDiff change resolved them).

### 6e. CoulombNonvacuous.lean unused variables

2 warnings for `hT` (line 24) and `hν` (line 338). These document physical constraints and are acceptable.

---

## 7. Documentation Lies

MEMORY.md line counts approximately correct. No material discrepancies.

---

## 8. Generalization Opportunities

### ~~8a. Weaken velocity smoothness from C∞ to C³~~ **FIXED** in cycle 119.

### 8b. ~~CoulombNonvacuous should apply main theorem~~ **FIXED** in cycle 116.

### 8c. Extract Gaussian integral lemmas to a reusable module (Medium)

`integral_coord_mul_equilibriumMaxwellian_eq_zero` and `integral_equilibriumMaxwellian` use general techniques (odd symmetry, Fubini factorization) that could be generalized.

### 8d. Extend kernel coverage beyond Coulomb (Medium-Hard)

Only Coulomb instantiated. Maxwell molecules (Ψ = const) would be ~100 lines.

### 8e. ~~Roundtrip lacks uniqueness~~ **FIXED** in cycle 117.

### 8f. Weaken spatial smoothness from C∞ to finite order (Medium)

The concrete theorem still uses `ContDiff ℝ ⊤` for spatial smoothness in several places. Could potentially weaken to `ContDiff ℝ k` for some finite k.

### 8g. ContDiff ℝ ⊤ in non-Coulomb files (Low)

TorusInstance (9 occurrences), TorusIntegration (1), IteratedDerivHelpers (3) still use `ContDiff ℝ ⊤`. These are for spatial smoothness / torus structure and may be inherent, but worth auditing.

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
| 6b | 4 files over 500 lines (Section3Helpers at 615) | Low | Open |
| 6c | 1 long line in Section3Helpers | Low | Open |
| 6d | 11 linter warnings in Section3Helpers.lean | Medium | **Open** |
| 8c | Gaussian integral lemmas not generalized | Low | Open |
| 8d | Only Coulomb kernel instantiated | Low | Open |
| 8f | Spatial smoothness could weaken from C∞ | Low | Open |
| 9 | Mathlib PR candidates (4 lemmas) | Low | Open |

---

## Verdict: CONDITIONAL ACCEPT

0 sorry's, 0 non-standard axioms, 32 files, 10,203 lines. Full round-trip with uniqueness proved. Velocity smoothness correctly weakened to C³.

**Condition for full ACCEPT:** Fix 11 linter warnings in Section3Helpers.lean (issue 6d).
