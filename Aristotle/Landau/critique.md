# Adversarial Critique — 2026-03-11 UTC (Cycle 89)

## Verdict: ACCEPT

---

## 0. Errors

`lake build` — **clean, 0 errors.**

---

## 1. Sorry's

**0 sorry's.** I found no issue.

---

## 2. Hidden Axioms

Zero axioms on main theorem `CoulombConcreteTheorem42_unique` (verified cycle 89 via `lean_verify`). I found no issue.

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

### 6b. Files over 600 lines (5 files)

| File | Lines |
|------|-------|
| CoulombSpatialTransport.lean | 676 |
| CoulombConcreteTheorem42.lean | 653 |
| CoulombFluxDiff.lean | 640 |
| Defs.lean | 634 |
| CoulombFlux.lean | 607 |

Down from 6 files last cycle (CoulombPSD 826→496+348).

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

### 8c. Generalize beyond T^3 (HARD)

### 8d. Extract Mathlib-upstreamable lemmas (MEDIUM)

`iteratedFDeriv_clm_zero` and `norm_iteratedFDeriv_one_clm` are PR-ready (generalized to `𝕜`).

### ~~8e. Split Defs.lean~~ — DONE (805 → 634 + 189)

### ~~8f. Split Section3Helpers.lean~~ — DONE (1162 → 596 + 160 + 446)

### 8g. UniformSchwartzDecay stronger than needed (MEDIUM — ANALYZED)

Analysis complete (cycle 88): the proof only uses velocity derivatives up to order 2 (k ≤ 2). A weaker `UniformC2Decay` condition would suffice. See `experiments/weaken_schwartz_decay.md`. Implementation deferred — mechanical but touches ~10 files.

### ~~8h. hExpDecay weakened to hLogGrowth~~ — DONE

### 8i. hGradBound is Coulomb-specific but not flagged as such (MINOR — DOCUMENTED)

Already documented in the CoulombConcreteTheorem42 docstring.

---

## 9. Mathlib Upstreamability

`iteratedFDeriv_clm_zero` and `norm_iteratedFDeriv_one_clm` are PR-ready (generalized to `𝕜`).

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 6b | 5 files over 600 lines | Medium | Open |
| 8b | Weaken regularity C^∞ → optimal | Medium | Deferred |
| 8d | Mathlib PR for helper lemmas | Low | Open |
| 8g | UniformSchwartzDecay stronger than needed | Medium | Analyzed, impl deferred |

### Conditions for ACCEPT

ACCEPT. All remaining issues are code quality / generalization. No correctness concerns.
