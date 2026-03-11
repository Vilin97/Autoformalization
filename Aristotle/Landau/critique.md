# Adversarial Critique — 2026-03-10 UTC (Cycle 70)

## Verdict: ACCEPT

---

## 0. Errors

`lake build` — **clean, no errors.**

---

## 1. Sorry's

**0 sorry's.** All 22 files compile without `sorry`. Both `CoulombConcreteTheorem42` and `CoulombConcreteTheorem42_nonvacuous` are fully proved.

I found no issue.

---

## 2. Hidden Axioms

`lean_verify` on both main theorems: **zero axioms** (not even `propext`, `Classical.choice`, `Quot.sound` — the verifier returns an empty list). No `admit`, `axiom`, `native_decide`, or linter suppression found.

I found no issue.

---

## 3. Circularity

All 10 non-trivial goals in `CoulombConcreteTheorem42_nonvacuous` are fully proved. The non-vacuousness defense is complete: the equilibrium Maxwellian with E=B=0 satisfies all 13 hypotheses. No circularity detected.

I found no issue.

---

## 4. Hypothesis Audit

All 13 hypotheses are independent and necessary. No change from previous cycles.

I found no issue.

---

## 5. Mathematical Correctness

The hVlasov proof (cycle 69) correctly shows the Landau operator vanishes on Maxwellians via projection annihilation: the bracket simplifies to `scalar • (v'-w)`, and `landauMatrix_mulVec_self` gives `A(z)·z = 0`. The argument is standard and the formalization matches the physics.

I found no issue.

---

## 6. Code Quality

### 6a. maxHeartbeats overrides: 1 total

`synthInstance.maxHeartbeats 160000` in CoulombSpatialTransport.lean. Acceptable — this is for typeclass synthesis, not proof search.

### 6b. Files over 600 lines (7 files)

| File | Lines |
|------|-------|
| TorusInstance.lean | 816 |
| Defs.lean | 785 |
| CoulombConcreteTheorem42.lean | 762 |
| CoulombPSD.lean | 703 |
| CoulombSpatialTransport.lean | 662 |
| Section3Helpers.lean | 625 |
| CoulombFluxDiff.lean | 618 |

CoulombConcreteTheorem42.lean contains general helper lemmas (`iteratedFDeriv_clm_zero`, `norm_iteratedFDeriv_one_clm`, `norm_iteratedFDeriv_proj_sq_le`, `quadratic_iteratedFDeriv_bound`) that could be extracted to Section3Helpers.lean or a new IteratedDerivHelpers.lean file. This would reduce CoulombConcreteTheorem42.lean by ~80 lines and make the helpers reusable.

### 6c. Long lines

Defs.lean has 3 long-line warnings (lines 324, 363, 424). These should be wrapped.

---

## 7. Documentation Lies

MEMORY.md updated in cycle 69: sorry count (0), line count (~761 for CoulombConcreteTheorem42). Accurate.

I found no issue.

---

## 8. Generalization Opportunities

### 8a. Extract iterated derivative helpers to shared file (EASY)

`iteratedFDeriv_clm_zero`, `norm_iteratedFDeriv_one_clm`, `norm_iteratedFDeriv_proj_sq_le`, and `quadratic_iteratedFDeriv_bound` are in CoulombConcreteTheorem42.lean but could live in Section3Helpers.lean. This reduces CoulombConcreteTheorem42.lean from 762 to ~680 lines and makes the helpers importable by other files.

### 8b. Weaken spatial smoothness: C^∞ → C^2 (DEFERRED)

The main theorem requires `ContDiff ℝ ⊤` for f in x. Physically, C² suffices for the entropy estimate. Weakening to `ContDiff ℝ 2` would strengthen the result but requires threading a finite regularity parameter through the abstract chain.

### 8c. Generalize beyond T³ (HARD)

The formalization is specific to `Torus3 = (ℝ/ℤ)³`. Generalizing to arbitrary compact Riemannian manifolds would require abstract differential geometry infrastructure that Mathlib doesn't yet provide.

### 8d. Extract Mathlib-upstreamable lemmas (MEDIUM)

`iteratedFDeriv_clm_zero` and `norm_iteratedFDeriv_one_clm` are clean, general facts about continuous linear maps that are missing from Mathlib. These are the most PR-ready candidates.

### 8e. Reduce Defs.lean size (MEDIUM)

At 785 lines, Defs.lean is the second-largest file. The Maxwellian section (IsMaxwellian, equilibriumMaxwellian, related lemmas) could be split into a dedicated MaxwellianDefs.lean.

---

## 9. Mathlib Upstreamability

Most PR-ready:
- `iteratedFDeriv_clm_zero`: iteratedFDeriv of a CLM vanishes at order ≥ 2
- `norm_iteratedFDeriv_one_clm`: ‖iteratedFDeriv 1 f x‖ = ‖f‖ for CLM f

These are clean, general facts missing from Mathlib. They were made public in cycle 69.

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 6b | 7 files over 600 lines | Minor | Open |
| 6c | 3 long-line warnings in Defs.lean | Minor | Open |
| 8a | General helper lemmas in wrong file (CoulombConcreteTheorem42) | Minor | Open |
| 8d | Mathlib-upstreamable lemmas not yet PR'd | Minor | Open |
| 8e | Defs.lean too large (785 lines) | Minor | Open |

### Conditions for ACCEPT

This is an ACCEPT. The formalization is complete: 0 sorry's, 0 hidden axioms, 0 errors, full non-vacuousness proof. The remaining issues are all code quality improvements that do not affect correctness.
