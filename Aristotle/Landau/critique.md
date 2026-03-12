# Adversarial Critique -- 2026-03-12 UTC (Cycle 117, Hostile Review)

## Verdict: CONDITIONAL ACCEPT

---

## 0. CI Status

`lean-action@v1` (lake build) on commit 230054f: **SUCCESS** (run 22981560306).
Commit f43e39c (cycle 116): CI run 22982420111 **in progress** at time of writing. Local `lake build` passes. Previous CI passed.

`lean_verify` on all 4 main theorems — only standard axioms:
- `VML.CoulombConcreteTheorem42`: propext, Classical.choice, Quot.sound. **Clean.**
- `VML.CoulombConcreteTheorem42_unique_T`: same. **Clean.**
- `VML.CoulombConcreteTheorem42_nonvacuous`: same. **Clean.**
- `VML.CoulombConcreteTheorem42_roundtrip`: same. **Clean.**

`Aristotle.lean` imports both `CoulombConcreteTheorem42` and `CoulombNonvacuous`. Default build covers all 4 theorems.

---

## 1. Sorry's

**0 sorry's** across 32 files (10,188 lines). The only occurrences of "sorry" are in documentation comments. No `admit`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque` found.

---

## 2. Hidden Axioms

All four main theorems verified with only standard axioms (propext, Classical.choice, Quot.sound). No non-standard axioms. No `set_option linter.all false` anywhere. **Sound.**

---

## 3. Circularity

Import DAG remains acyclic. `CoulombNonvacuous.lean` imports `CoulombConcreteTheorem42` (needed for the round-trip theorem). No circular imports. **Sound.**

---

## 4. Hypothesis Audit

Same as cycle 116. All 13 hypotheses are necessary and independent. Counterexamples for independence of hGradBound and hLogGrowth are documented in the docstring. **Sound.**

---

## 5. Mathematical Correctness

**Sound.** No changes to the abstract proof chain since cycle 116. The new `CoulombConcreteTheorem42_roundtrip` is a trivial composition of `_nonvacuous` + `CoulombConcreteTheorem42`. No new mathematical content.

---

## 6. Code Quality

### 6a. maxHeartbeats overrides

**2 remaining:**
- `NewtonianPotential.lean:86` — `set_option maxHeartbeats 800000 in`
- `TorusIntegration.lean:85` — `set_option maxHeartbeats 400000 in`

**ISSUE (Low): 2 maxHeartbeats overrides remain.** The 800000 in NewtonianPotential is at the threshold.

### 6b. Files over 500 lines

| File | Lines |
|------|-------|
| Section3Helpers.lean | 613 |
| CoulombFluxConv.lean | 560 |
| CoulombNonvacuous.lean | 519 |
| Defs.lean | 510 |

CoulombNonvacuous grew from ~500 to 519 with the round-trip theorem addition. Four files now exceed 500 lines.

### 6c. Line length violations (> 100 chars)

| File | Count |
|------|-------|
| CoulombPSDHelpers.lean | 2 |
| Section3Helpers.lean | 1 |

**Down from 14 to 3.** CoulombFluxConv and CoulombNonvacuous long lines were fixed in cycle 116.

**ISSUE (Low): 3 long lines remain across 2 files.**

### 6d. Linter warnings — widespread

Cycle 116 fixed CoulombNonvacuous.lean simp warnings and deprecated API. But **many other files have linter warnings** that were not reported in cycle 116's critique:

| File | Warning Count | Types |
|------|---------------|-------|
| NewtonianPotential.lean | ~20+ | unused simp args, unused variables (`hf_smooth`), multi-goal tactics, `ring_nf` suggestions |
| TorusIntegration.lean | ~8 | deprecated `integral_mul_left` (3x), unused simp args, multi-goal tactics |
| CoulombPSDHelpers.lean | ~6 | `show` → `change`, unused simp args (`sub_eq_zero`, `hp_ne`) |
| CoulombFluxBound.lean | ~5 | `show` → `change` |
| CoulombFluxConv.lean | 2 | unused variable `hM`, `abel_nf` suggestion |
| Section3Helpers.lean | ~4 | `ring_nf` suggestions |

**ISSUE (Medium): ~45+ linter warnings across 6 files.** The cycle 116 cleanup only addressed CoulombNonvacuous — the other files were never checked. NewtonianPotential.lean alone has ~20+ warnings.

### 6e. Deprecated API usage

TorusIntegration.lean uses `MeasureTheory.integral_mul_left` (deprecated) at lines 349, 353, 357. Should use `MeasureTheory.integral_const_mul`.

**ISSUE (Low): 3 deprecated API usages in TorusIntegration.lean.**

---

## 7. Documentation Lies

### 7a. MEMORY.md line counts

| File | MEMORY.md | Actual | Off by |
|------|-----------|--------|--------|
| CoulombFluxDiff.lean | ~250 | 320 | +70 (28%) |
| CoulombConcreteTheorem42.lean | ~233 | 241 | +8 |
| CoulombNonvacuous.lean | ~500 | 519 | +19 |
| CoulombFluxConv.lean | ~550 | 560 | +10 |

**ISSUE (Low): CoulombFluxDiff line count is materially wrong (250 vs 320).** The others are within acceptable approximation range.

### 7b. MEMORY.md total line count

MEMORY.md says "~10,150 lines". Actual: 10,188. Close enough.

---

## 8. Generalization Opportunities

### 8a. Weaken velocity smoothness from C∞ to C³ (Feasible)

The abstract theorem requires only `ContDiff ℝ 3`. The concrete theorem uses `ContDiff ℝ ⊤` and downcasts via `.of_le le_top`. Weakening to `ContDiff ℝ 3` would make the statement tighter without changing the proof substance. **Feasibility: change hypothesis + update `.of_le le_top` → `.of_le (by norm_num)` in all 12 Coulomb files. Medium effort due to breadth.**

### 8b. ~~CoulombNonvacuous should apply main theorem~~ **FIXED** in cycle 116.

`CoulombConcreteTheorem42_roundtrip` now demonstrates the full round-trip.

### 8c. Extract Gaussian integral lemmas to a reusable module (Medium)

`integral_coord_mul_equilibriumMaxwellian_eq_zero` and `integral_equilibriumMaxwellian` are specific to `equilibriumMaxwellian` but the underlying techniques are general. A Mathlib-quality version would work for arbitrary product Gaussians on `Fin n → ℝ`.

### 8d. Extend kernel coverage beyond Coulomb (Medium-Hard)

Only Coulomb (Ψ = r⁻³) is instantiated. Maxwell molecules (Ψ = const) would be a quick win (~100 lines) demonstrating generality. Hard spheres (Ψ = r) would be more interesting.

### 8e. Strengthen uniqueness: unique equilibrium temperature for given density (Easy)

`CoulombConcreteTheorem42_unique_T` already proves T uniqueness, but `CoulombConcreteTheorem42_roundtrip` does NOT include uniqueness in its conclusion. Could strengthen roundtrip to also assert uniqueness. **Feasibility: ~5 lines.**

---

## 9. Mathlib Upstreamability

1. **n-dimensional Gaussian integral** — Fubini + `integral_fintype_prod_eq_prod` + `integral_gaussian` pattern. Not in Mathlib. Would need generalization from `Fin 3 → ℝ` to `Fin n → ℝ`.
2. **`inverse_poly_integrable`** (SchwartzDecayDefs.lean) — `(1+‖v‖)⁻ᴺ` integrability for N > dim. General and useful.
3. **`norm_fderiv_eq_iteratedFDeriv_one`** (IteratedDerivHelpers.lean) — fderiv/iteratedFDeriv relation.
4. **Schwartz decay extraction lemmas** — `schwartz_pointwise_decay`, `schwartz_fderiv_component_decay`.

---

## Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 6a | 2 maxHeartbeats overrides (800000 + 400000) | Low | Open |
| 6b | 4 files over 500 lines (Section3Helpers at 613) | Low | Open |
| 6c | 3 long lines across 2 files | Low | Open |
| 6d | ~45+ linter warnings across 6 files | Medium | **NEW** |
| 6e | 3 deprecated `integral_mul_left` in TorusIntegration | Low | **NEW** |
| 7a | CoulombFluxDiff line count wrong in MEMORY.md (250→320) | Low | **NEW** |
| 8a | Hypothesis 4 could weaken to ContDiff ℝ 3 | Low | Open |
| 8c | Gaussian integral lemmas not generalized | Low | Open |
| 8d | Only Coulomb kernel instantiated | Low | Open |
| 8e | Roundtrip theorem lacks uniqueness | Low | **NEW** |
| 9 | Mathlib PR candidates (4 lemmas) | Low | Open |

---

## Verdict: CONDITIONAL ACCEPT

The formalization is mathematically sound, fully verified by the Lean 4 kernel:
- **0 sorry's** across 32 files, 10,188 lines
- **0 non-standard axioms** (verified by `lean_verify` on all 4 main theorems)
- **2 `maxHeartbeats` overrides** (400000 + 800000)
- **CI passing** (lean-action succeeded on commit 230054f; f43e39c in progress)
- **Full round-trip** demonstrated (cycle 116 fix)

The main new finding is **~45+ linter warnings** across 6 files that were never addressed — cycle 116 only cleaned CoulombNonvacuous. NewtonianPotential.lean alone has ~20+ warnings including unused variables, unused simp args, and multi-goal tactic warnings.

**Condition for full ACCEPT:** Fix the ~45 linter warnings across the 6 affected files (issue 6d). The remaining issues are cosmetic or enhancement-level.
