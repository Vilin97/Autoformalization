# Adversarial Critique — 2026-03-10 UTC (Cycle 67)

## Verdict: CONDITIONAL ACCEPT

---

## 0. Errors

`lake build` — **clean, no errors.**

---

## 1. Sorry's

**3 sorry's** in `CoulombConcreteTheorem42_nonvacuous`:

| Line | Goal | Statement | Risk |
|------|------|-----------|------|
| ~426 | (7) | `UniformSchwartzDecay (fun _ => equilibriumMaxwellian ρ T)` | Medium — requires iterated fderiv bounds on Gaussian |
| ~444 | (10) | Vlasov equation: `0 = ν * LandauOperator coulombKernel eM` | **High** — requires Maxwellian in kernel of Landau operator |
| ~452 | (12) | Gauss: `div 0 = ∫ eM dv - ρ_ion` | Hard — requires Gaussian integral normalization `∫ eM = ρ_ion` |

All 3 remaining sorry's are mathematically true but the formalization doesn't prove them. The main theorems are unaffected.

**Worst-case scenario for sorry (10):** If `LandauOperator` is defined in a way that doesn't match the standard physics definition, the Maxwellian might NOT be in its kernel, and the non-vacuousness claim would be false for the formalized definitions. This would mean the theorem is vacuously true — provable but useless. Sorry (10) is the only thing standing between "rigorous theorem" and "vacuous tautology".

---

## 2. Hidden Axioms

`lean_verify` on both `VML.CoulombConcreteTheorem42` and `VML.Theorem42`: zero axioms beyond the standard three. No `admit`, `axiom`, `native_decide`, or linter suppression found.

I found no issue.

---

## 3. Circularity

The non-vacuousness theorem (`CoulombConcreteTheorem42_nonvacuous`) is the structural defense against circularity. With 3 of 10 non-trivial goals still sorry'd, the defense is incomplete.

Sorry (10) — the Vlasov equation — is the most critical: it requires showing the Maxwellian is in the kernel of the Landau collision operator as formalized. If `LandauOperator` has a subtle bug (e.g., wrong sign, missing factor, incorrect projection), this sorry hides it.

---

## 4. Hypothesis Audit

No change from cycle 66. All 13 hypotheses are independent and necessary.

---

## 5. Mathematical Correctness

I found no divergence. The main theorems are kernel-verified.

---

## 6. Code Quality

### 6a. maxHeartbeats overrides: 1 total

`synthInstance.maxHeartbeats 160000` in CoulombSpatialTransport.lean. Acceptable.

### 6b. Files over 600 lines (5 files)

| File | Lines |
|------|-------|
| TorusInstance.lean | 816 |
| Defs.lean | 785 |
| CoulombPSD.lean | 703 |
| CoulombSpatialTransport.lean | 662 |
| Section3Helpers.lean | 625 |

CoulombFluxDiff.lean at 618 and CoulombFlux.lean at 589 are under threshold. Still 5 files over 600 lines.

### 6c. Long lines

No lines over 100 characters found. Previous cosmetic issue resolved.

---

## 7. Documentation Lies

**MEMORY.md is stale:**
- Says "6 sorry's (non-critical)" — actual: **3 sorry's**. Wrong since cycle 66.
- Says "~7,900 lines" — actual: **7,984 lines**. Minor drift but inaccurate.
- Says `CoulombConcreteTheorem42.lean` has "~395 lines" — actual: **458 lines**. Wrong since cycle 66 added helper lemmas.
- Says `CoulombFlux.lean` has "~589 lines" — actual: **589 lines**. Correct.
- Says `CoulombFluxDiff.lean` has "~618 lines" — actual: **618 lines**. Correct.

---

## 8. Generalization Opportunities

### 8a. Close remaining 3 non-vacuousness sorry's (MEDIUM-HARD)

- (7) UniformSchwartzDecay for Gaussian: requires showing `‖iteratedFDeriv ℝ k eM v‖ * (1+‖v‖)^N ≤ C` for all k, N. The iterated fderiv of eM is a polynomial × eM, so the bound follows from polynomial × Gaussian → 0. Feasible with Mathlib's `iteratedFDeriv` API but requires careful induction on k.
- (10) Vlasov: requires `LandauOperator coulombKernel eM = 0`. This is the H-theorem's converse direction — the Maxwellian is the unique minimizer of entropy dissipation, hence in the kernel. Hardest sorry.
- (12) Gauss: requires `∫ eM dv = ρ_ion`. This is Gaussian integral normalization — the prefactor `ρ/(2πT)^{3/2}` is chosen so the integral equals ρ. Feasible if Mathlib has the 3D Gaussian integral.

### 8b. Weaken spatial smoothness: C^∞ → C^2 (DEFERRED)

Investigated in cycles 64-65. Requires parametric `IsSpatiallySmooth n` predicate — ~95 call-site changes. Design documented in `experiments/spatial_smoothness_design.md`. Low priority since concrete theorem needs C^∞ anyway.

### 8c. Generalize beyond T³ (HARD)

Requires abstracting over dimension and manifold structure. Very high effort.

### 8d. Extract Mathlib-upstreamable lemmas (MEDIUM)

`inverse_poly_integrable`, `integrable_one_add_norm_pow_mul`, and the Schwartz decay integrability lemmas in SchwartzDecayDefs.lean are general enough for Mathlib. Would need generalization to arbitrary dimension.

---

## 9. Mathlib Upstreamability

Unchanged from cycle 66. The Schwartz decay machinery and torus IBP lemmas are the most plausible candidates.

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 6 | 5 files over 600 lines (TorusInstance 816, Defs 785) | Minor | Open |
| 8 | Non-vacuousness theorem has 3 sorry's | Epistemic | Open (7 of 10 goals closed) |
| 19 | MEMORY.md stale: sorry count, line counts wrong | Trivial | Open |

### Conditions for ACCEPT

Fix MEMORY.md inaccuracies (sorry count, line counts). Remaining 3 sorry's (7, 10, 12) are all genuinely hard — Schwartz class, Landau nullspace, and Gaussian integral normalization. These require substantial mathematical machinery not currently in the project. No new sorry's should be introduced.
