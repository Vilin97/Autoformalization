# Adversarial Critique -- 2026-03-12 UTC (Cycle 116, Hostile Review)

## Verdict: CONDITIONAL ACCEPT

---

## 0. CI Status

`lean-action@v1` (lake build) on commit 230054f: **SUCCESS** (run 22981560306).

`lean_verify` on `VML.CoulombConcreteTheorem42`: propext, Classical.choice, Quot.sound. **Clean.**
`lean_verify` on `VML.CoulombConcreteTheorem42_unique_T`: same. **Clean.**
`lean_verify` on `VML.CoulombConcreteTheorem42_nonvacuous`: same. **Clean.**

`Aristotle.lean` imports both `CoulombConcreteTheorem42` and `CoulombNonvacuous`. Default build covers both. **Fixed** from cycle 115.

---

## 1. Sorry's

**0 sorry's** across 32 files (10,147 lines). The only occurrences of "sorry" are in documentation comments. No `admit`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque` found.

---

## 2. Hidden Axioms

All three main theorems verified with only standard axioms (propext, Classical.choice, Quot.sound). No non-standard axioms. **Sound.**

---

## 3. Circularity

Import DAG remains acyclic. `CoulombNonvacuous.lean` is now in the default build target (Aristotle.lean). No circular imports. **Sound.**

---

## 4. Hypothesis Audit

Same as cycle 115. All 13 hypotheses are necessary and independent. Counterexamples for independence of hGradBound and hLogGrowth are documented. **Sound.**

---

## 5. Mathematical Correctness

**Sound.** No changes to the abstract proof chain. Two new lemmas in CoulombNonvacuous.lean are mathematically correct:

- `integral_coord_mul_equilibriumMaxwellian_eq_zero`: Uses `integral_neg_eq_self` to show ∫ vᵢ * eM(v) dv = 0 by odd symmetry. Correct.
- `integral_equilibriumMaxwellian`: Uses Fubini (`integral_fintype_prod_eq_prod`) + `integral_gaussian` to show ∫ eM(v) dv = ρ. The algebra is verified by Lean. Correct.

---

## 6. Code Quality

### 6a. maxHeartbeats overrides

**2 remaining:**
- `NewtonianPotential.lean:86` — `set_option maxHeartbeats 800000 in`
- `TorusIntegration.lean:85` — `set_option maxHeartbeats 400000 in`

**ISSUE (Low): 2 maxHeartbeats overrides remain.** The 800000 in NewtonianPotential is at the threshold. Both should be investigated for simplification.

### 6b. Files over 500 lines

| File | Lines |
|------|-------|
| Section3Helpers.lean | 613 |
| CoulombFluxConv.lean | 540 |
| Defs.lean | 510 |

CoulombFluxConv grew from ~373 to 540 lines during the Mathlib v4.24.0 fix. The `inv_norm_bounded_integrable` helper and the expanded `hasFDerivAt` proof added ~170 lines. Acceptable but approaching the boundary.

### 6c. Line length violations (> 100 chars)

| File | Count |
|------|-------|
| CoulombFluxConv.lean | 10 |
| CoulombPSDHelpers.lean | 2 |
| CoulombNonvacuous.lean | 1 |
| Section3Helpers.lean | 1 |

**ISSUE (Low): 14 long lines across 4 files.** CoulombFluxConv accounts for 10 of them — these were introduced during the Mathlib v4.24.0 fix and should be reformatted.

### 6d. Unused simp arguments

CoulombNonvacuous.lean has ~20 linter warnings for unused simp arguments (`fderiv_const`, `Function.comp`, `ContinuousLinearMap.sum_apply`, etc.) and 1 deprecated `Matrix.mulVec_smul_assoc`. These are cosmetic but noisy.

**ISSUE (Low): ~20 unused simp argument warnings in CoulombNonvacuous.lean.** Clean up by removing unused arguments from simp calls.

### 6e. Deprecated API usage

CoulombNonvacuous.lean:447 uses `Matrix.mulVec_smul_assoc` which is deprecated in favor of `Matrix.mulVec_smul`.

**ISSUE (Low): 1 deprecated Mathlib API usage in CoulombNonvacuous.lean:447.**

---

## 7. Documentation Lies

### 7a. Defs.lean:378 docstring

Line 378 now correctly states "hSpatialVelocityFubini requires joint integrability". **Fixed** from cycle 115.

### 7b. MEMORY.md line counts

MEMORY.md line counts are approximate and noted as such. However, CoulombNonvacuous is listed as "~351 lines" but is now 498. CoulombFluxConv is listed as "~373 lines" but is now 540.

**ISSUE (Low): MEMORY.md line counts for CoulombNonvacuous and CoulombFluxConv are stale.**

---

## 8. Generalization Opportunities

### 8a. Weaken velocity smoothness from C∞ to C³ (Feasible)

The abstract theorem requires only `ContDiff ℝ 3`. The concrete theorem uses `ContDiff ℝ ⊤` and downcasts via `.of_le le_top`. This is an honest design choice documented in the docstring, but the hypothesis COULD be weakened to `ContDiff ℝ 3` without changing any proof. This would make the theorem statement tighter. **Feasibility: 1 line change + verify.**

### 8b. CoulombNonvacuous should apply the main theorem (Medium)

`CoulombConcreteTheorem42_nonvacuous` proves all 13 hypotheses are simultaneously satisfiable but does NOT actually apply `CoulombConcreteTheorem42` to derive the conclusion. A stronger statement would be:

```lean
theorem CoulombConcreteTheorem42_nonvacuous' :
    ∃ f E B ν ρ_ion, <all hypotheses> ∧
    ∃ T_eq B₀, 0 < T_eq ∧ <conclusion holds>
```

This would demonstrate the full round-trip: hypotheses are satisfiable AND the conclusion holds. **Feasibility: ~10 lines, import CoulombConcreteTheorem42.**

### 8c. Extract Gaussian integral lemmas to a reusable module (Low)

`integral_coord_mul_equilibriumMaxwellian_eq_zero` and `integral_equilibriumMaxwellian` are specific to `equilibriumMaxwellian` but the techniques (odd symmetry, Fubini factorization of product Gaussians) are general. Could be generalized to:

```lean
lemma integral_coord_mul_gaussian_eq_zero (b : ℝ) (hb : 0 < b) (i : Fin n) :
    ∫ v : Fin n → ℝ, v i * exp (-b * ‖v‖^2) = 0
```

**Feasibility: Medium. Would be a good Mathlib PR candidate.**

### 8d. Extend kernel coverage beyond Coulomb (Hard)

The abstract `Theorem42` works for any kernel satisfying `VelocityDecayConditions`. The concrete instantiation covers only Coulomb (Ψ(r) = r⁻³). Other physically relevant kernels:
- Maxwell molecules: Ψ = const (trivial, all integrability conditions immediate)
- Hard spheres: Ψ(r) = r (bounded, should be easier than Coulomb)
- Soft potentials: Ψ(r) = r^γ for -3 < γ < 0

Maxwell molecules would be a quick win (~100 lines). **Feasibility: Low effort for Maxwell, medium for hard spheres.**

---

## 9. Mathlib Upstreamability

1. **`integral_gaussian` factorization pattern** — the Fubini + `integral_fintype_prod_eq_prod` pattern for n-dimensional Gaussian integrals is reusable and not in Mathlib.
2. **`inverse_poly_integrable`** (SchwartzDecayDefs.lean) — `(1+‖v‖)⁻ᴺ` integrability for N > dim.
3. **`norm_fderiv_eq_iteratedFDeriv_one`** (IteratedDerivHelpers.lean) — fderiv/iteratedFDeriv relation.
4. **Schwartz decay extraction lemmas** — `schwartz_pointwise_decay`, `schwartz_fderiv_component_decay`.

---

## Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 6a | 2 maxHeartbeats overrides (800000 + 400000) | Low | Open |
| 6c | 14 long lines across 4 files (10 in CoulombFluxConv) | Low | Open |
| 6d | ~20 unused simp arg warnings in CoulombNonvacuous | Low | **NEW** |
| 6e | 1 deprecated API (mulVec_smul_assoc) | Low | **NEW** |
| 7b | MEMORY.md line counts stale for 2 files | Low | Open |
| 8a | Hypothesis 4 could weaken to ContDiff ℝ 3 | Low | Open |
| 8b | CoulombNonvacuous should apply main theorem | Low | Open |
| 8c | Gaussian integral lemmas not generalized | Low | **NEW** |
| 8d | Only Coulomb kernel instantiated | Low | Open |
| 9 | Mathlib PR candidates (4 lemmas) | Low | Open |

---

## Verdict: CONDITIONAL ACCEPT

The formalization is mathematically sound, fully verified by the Lean 4 kernel:
- **0 sorry's** across 32 files, 10,147 lines
- **0 non-standard axioms** (verified by `lean_verify` on all 3 main theorems)
- **2 `maxHeartbeats` overrides** (400000 + 800000)
- **CI passing** (lean-action succeeded on commit 230054f)
- **CoulombNonvacuous in default build** (fixed from cycle 115)

All open issues are Low severity. None affects soundness. The main actionable items are:
1. Clean up ~20 unused simp warnings in CoulombNonvacuous.lean
2. Fix deprecated `mulVec_smul_assoc` → `mulVec_smul`
3. Fix 14 long lines (mostly in CoulombFluxConv.lean)

**Condition for full ACCEPT:** Fix items 1-3 above (cosmetic cleanup).
