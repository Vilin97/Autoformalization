# Adversarial Critique — 2026-03-11 UTC (Cycle 84)

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
| Section3Helpers.lean | 1020 |
| TorusInstance.lean | 910 |
| CoulombPSD.lean | 826 |
| CoulombSpatialTransport.lean | 676 |
| CoulombFluxDiff.lean | 640 |
| CoulombConcreteTheorem42.lean | 639 |
| Defs.lean | 634 |
| CoulombFlux.lean | 607 |

---

## 7. Documentation Lies

I found no issue.

---

## 8. Generalization Opportunities

### ~~8a. Extract helpers~~ — DONE

### 8b. Weaken regularity: C^∞ → optimal (DEFERRED)

The concrete theorem requires `ContDiff ℝ ⊤` (C^∞) in both space and velocity. The optimal regularity, confirmed by Gemini DeepThink's independent analysis, is:

- **Distribution f**: f ∈ C¹(T³ × ℝ³) with ∇²_v f ∈ C⁰. That is: C¹ jointly in (x,v), plus second velocity derivatives exist and are continuous.
- **Fields E, B**: E, B ∈ C¹(T³; ℝ³).

What the proof actually uses at each step:
- **Landau operator** (divergence of integral): C² in v (need ∂²f/∂v²)
- **∇_v log f**: C¹ in v (need ∂f/∂v + f > 0)
- **Spatial gradient ∇_x f**: C¹ in x
- **Maximum principle** (Δ log n at extremum): C² in x for log n, but log n = a(x) + const where a comes from the Maxwellian; a inherits regularity from f, so C¹ of f in x gives C¹ of a, and we need C² of a. This forces f ∈ C² in x — **or** the maximum principle can be applied to the PB equation T Δ(log n) = n − ρ_ion directly, where C¹ of ∇ log n suffices since ∇ log n = E/T.
- **Killing equation**: C¹ of b(x) (drift), which inherits from C¹ of f in x
- **Curl, divergence of E, B**: C¹ of E, B

In Lean terms: `ContDiff ℝ 2 (f x)` in velocity, `ContDiff ℝ 1` in space (or jointly C¹ with continuous second velocity derivatives), and `ContDiff ℝ 1` for E, B components. The current C^∞ is ~3 regularity levels stronger than needed.

### 8c. Generalize beyond T^3 (HARD)

### 8d. Extract Mathlib-upstreamable lemmas (MEDIUM)

### ~~8e. Split Defs.lean~~ — DONE (805 → 634 + 189)

### ~~8f. Split Section3Helpers.lean~~ — DONE (1162 → 1020 + 158)

### 8g. UniformSchwartzDecay is stronger than needed (MEDIUM)

Schwartz class means ALL derivatives decay faster than ANY polynomial. The proof uses specific integrals:
- ∫ f|v|² dv (energy), ∫ f log f dv (entropy), ∫∫ PSD dv dw (dissipation), ∫ (∇f)·(log f) dv (IBP)

A lighter condition like "f and its first 3 velocity derivatives satisfy |∂^k f(v)| ≤ C_k · exp(−c|v|^α) for some α > 0, c > 0" would suffice and be more physically natural. UniformSchwartzDecay is a sledgehammer that makes the VelocityDecayConditions easy to verify but is not the minimal assumption.

### ~~8h. hExpDecay weakened to hLogGrowth~~ — DONE

Replaced `∃ C K, ∀ x v, exp(−C(1+‖v‖)^K) ≤ f x v` (stretched exponential lower bound) with the strictly weaker `∃ C_log K_log, ∀ x v, |log f(x,v)| ≤ C_log*(1+‖v‖)^K_log` (polynomial growth of |log f|). This is satisfied by a strictly larger class of distributions.

### 8i. hGradBound is Coulomb-specific but not flagged as such (MINOR)

`hGradBound : ∃ Cg Kg, ∀ x v i, |∂f/∂vᵢ| ≤ Cg(1+‖v‖)^Kg · f` (polynomial score growth). This hypothesis exists solely to handle the Coulomb singularity: it ensures the PSD integrand is continuous at v = w despite the 1/|z| blow-up of the collision kernel, because the score difference ∇log f(v) − ∇log f(w) = O(|v−w|) cancels the singularity.

For non-singular kernels (e.g., Maxwell molecules with Ψ = const, or any bounded Ψ), this hypothesis is unnecessary — the abstract Theorem42 correctly omits it. The concrete theorem should document that hGradBound is a Coulomb-specific regularity condition, not a general physical requirement.

---

## 9. Mathlib Upstreamability

`iteratedFDeriv_clm_zero` and `norm_iteratedFDeriv_one_clm` are PR-ready (generalized to `𝕜`).

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 6b | 8 files over 600 lines (Section3Helpers 1020) | High | Open |
| ~~8e~~ | ~~Defs.lean split~~ | ~~Minor~~ | ~~Done~~ |
| ~~8f~~ | ~~Section3Helpers.lean split~~ | ~~High~~ | ~~Done~~ |

### Conditions for ACCEPT

ACCEPT. All issues are code quality / style.
