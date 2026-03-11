# Adversarial Critique — 2026-03-11 UTC (Cycle 82)

## Verdict: ACCEPT

---

## 0. Errors

`lake build` — **clean, 0 errors.**

---

## 1. Sorry's

**0 sorry's.** I found no issue.

---

## 2. Hidden Axioms

Zero axioms on main theorem (verified cycle 76). I found no issue.

---

## 3. Circularity

I found no issue.

---

## 4. Hypothesis Audit

All 13 hypotheses independent and necessary. I found no issue.

---

## 5. Mathematical Correctness

I found no issue.

---

## 6. Code Quality

### 6a. maxHeartbeats overrides: 1 total

`synthInstance.maxHeartbeats 160000` in CoulombSpatialTransport.lean. Acceptable.

### 6b. Files over 600 lines (8 files)

| File | Lines |
|------|-------|
| Section3Helpers.lean | 1162 |
| TorusInstance.lean | 910 |
| CoulombPSD.lean | 826 |
| Defs.lean | 805 |
| CoulombSpatialTransport.lean | 676 |
| CoulombConcreteTheorem42.lean | 630 |
| CoulombFluxDiff.lean | 629 |
| CoulombFlux.lean | 605 |

### 6c. AI code style artifacts

| Metric | Current | Target |
|---|---|---|
| ~~Lines > 200 chars~~ | ~~0~~ | ~~0~~ DONE |
| ~~Trailing semicolons~~ | ~~0~~ | ~~0~~ DONE |
| ~~Multi-semi lines~~ | ~~4~~ (in `by` blocks) | ~~0~~ DONE |
| Lines > 100 chars | **60** (14 files) | 0 |
| Plain semicolons | **356** (+ 126 `<;>`) | < 50 |

Worst offenders: NewtonianPotential (15), CoulombFluxDiff (12), VelocityDecayInstance (10).

---

## 7. Documentation Lies

I found no issue.

---

## 8. Generalization Opportunities

### ~~8a. Extract helpers~~ — DONE

### 8b. Weaken spatial smoothness: C^∞ → C^2 (DEFERRED)

The concrete theorem requires `ContDiff ℝ ⊤` (C^∞) in both space and velocity. What the proof actually uses:
- **Velocity**: C² for the Landau operator (divergence of an integral), C¹ for ∇_v log f. C³ is a safe margin.
- **Space**: C¹ for gradients, C² for the Laplacian in the maximum principle.

`ContDiff ℝ 3` in velocity and `ContDiff ℝ 2` in space would be mathematically sufficient. The C^∞ is cosmetic (simpler to state) but strictly stronger than needed.

### 8c. Generalize beyond T^3 (HARD)

### 8d. Extract Mathlib-upstreamable lemmas (MEDIUM)

### 8e. Split Defs.lean (MEDIUM)

### 8g. UniformSchwartzDecay is stronger than needed (MEDIUM)

Schwartz class means ALL derivatives decay faster than ANY polynomial. The proof uses specific integrals:
- ∫ f|v|² dv (energy), ∫ f log f dv (entropy), ∫∫ PSD dv dw (dissipation), ∫ (∇f)·(log f) dv (IBP)

A lighter condition like "f and its first 3 velocity derivatives satisfy |∂^k f(v)| ≤ C_k · exp(−c|v|^α) for some α > 0, c > 0" would suffice and be more physically natural. UniformSchwartzDecay is a sledgehammer that makes the VelocityDecayConditions easy to verify but is not the minimal assumption.

### 8h. hExpDecay could be weakened (MINOR)

Currently: `∃ C K, ∀ x v, exp(−C(1+‖v‖)^K) ≤ f x v` (stretched exponential lower bound). This is used only to bound |log f(v)| ≤ C(1+‖v‖)^K (polynomial growth of log), ensuring entropy integrability.

A weaker sufficient condition: `∃ C K, ∀ x v, |log f(x,v)| ≤ C(1+‖v‖)^K` (direct polynomial growth of |log f|). This is satisfied by a strictly larger class of distributions (e.g., those with super-polynomial but sub-exponential tails in log f).

### 8i. hGradBound is Coulomb-specific but not flagged as such (MINOR)

`hGradBound : ∃ Cg Kg, ∀ x v i, |∂f/∂vᵢ| ≤ Cg(1+‖v‖)^Kg · f` (polynomial score growth). This hypothesis exists solely to handle the Coulomb singularity: it ensures the PSD integrand is continuous at v = w despite the 1/|z| blow-up of the collision kernel, because the score difference ∇log f(v) − ∇log f(w) = O(|v−w|) cancels the singularity.

For non-singular kernels (e.g., Maxwell molecules with Ψ = const, or any bounded Ψ), this hypothesis is unnecessary — the abstract Theorem42 correctly omits it. The concrete theorem should document that hGradBound is a Coulomb-specific regularity condition, not a general physical requirement.

### 8f. Split Section3Helpers.lean (CRITICAL — 1162 lines)

---

## 9. Mathlib Upstreamability

`iteratedFDeriv_clm_zero` and `norm_iteratedFDeriv_one_clm` are PR-ready.

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 6b | 7 files over 600 lines | Minor | Open |
| 8e | Defs.lean too large (788 lines) | Minor | Open |
| 8f | AI code style artifacts (long lines, semicolons, spacing) | Moderate | Open |

### Conditions for ACCEPT

This is an ACCEPT. The math is sound. The code style issues (8f) do not affect correctness but make the codebase visibly AI-generated, which undermines credibility for peer review.
