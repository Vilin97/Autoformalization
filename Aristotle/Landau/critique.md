# Adversarial Critique — 2026-03-11 UTC (Cycle 93)

## Verdict: ACCEPT

---

## 0. Errors

`lake build` — **clean, 0 errors.**

---

## 1. Sorry's

**0 sorry's.** I found no issue.

---

## 2. Hidden Axioms

Zero axioms on `CoulombConcreteTheorem42` and `CoulombConcreteTheorem42_nonvacuous` (verified via `lean_verify` this cycle). I found no issue.

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

`synthInstance.maxHeartbeats 160000` in CoulombForceTransport.lean. Acceptable (typeclass diamond workaround).

### 6b. Files over 600 lines (1 file)

| File | Lines |
|------|-------|
| Defs.lean | 634 |

Can't be split per user preference. No change from last cycle.

### 6c. Long proofs (3 proofs over 200 lines)

| File | Proof | Lines |
|------|-------|-------|
| CoulombPSD.lean | `fubini_double_integrable_coulomb` | ~312 |
| CoulombConcreteTheorem42.lean | `CoulombConcreteTheorem42` | ~235 |
| CoulombFluxDiff.lean | `coulomb_flux_deriv_schwartz_decay` | ~231 |

All three are single extended calculations. `fubini_double_integrable_coulomb` is the most concerning at 312 lines — it might benefit from extracting helper lemmas for the inner/outer integrability steps. The other two are natural monoliths.

---

## 7. Documentation Lies

I found no issue.

---

## 8. Generalization Opportunities

### ~~8a. Extract helpers~~ — DONE

### ~~8b. Weaken regularity: C^∞ → optimal~~ — ANALYZED (cycle 90)

ContDiff ℝ ⊤ is necessary for Coulomb. See `experiments/contdiff_regularity_analysis.md`.

### 8c. Generalize beyond T^3 (HARD)

### 8d. Extract Mathlib-upstreamable lemmas (MEDIUM)

`iteratedFDeriv_clm_zero` confirmed not in Mathlib (loogle, cycle 91). PR-ready. See `experiments/mathlib_pr_candidates.md`.

### ~~8e. Split Defs.lean~~ — DONE

### ~~8f. Split Section3Helpers.lean~~ — DONE

### ~~8g. UniformSchwartzDecay → k ≤ 2~~ — DONE (cycle 89)

### ~~8h. hExpDecay weakened to hLogGrowth~~ — DONE

### 8i. hGradBound is Coulomb-specific (MINOR — DOCUMENTED)

### 8j. lean-lsp build desync (PERSISTENT)

The lean-lsp MCP rebuilds from source and hits errors in IteratedDerivHelpers, TorusIntegration, GaussianHelpers that don't reproduce with `lake build`. `lean_verify` still works for some theorems but fails for others. `lake build` remains authoritative.

---

## 9. Mathlib Upstreamability

`iteratedFDeriv_clm_zero` is PR-ready. See `experiments/mathlib_pr_candidates.md`.

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 6b | 1 file over 600 lines | Low | Open (Defs.lean, can't split) |
| 6c | 3 proofs over 200 lines | Low | Open (monoliths, `fubini_double` splittable) |
| 8c | Generalize beyond T^3 | Low | Deferred (hard) |
| 8d | Mathlib PR for helper lemmas | Low | Open |
| 8j | lean-lsp build desync | Low | Open (tooling) |

### Conditions for ACCEPT

ACCEPT. All remaining issues are low severity — code quality, generalization, tooling. No correctness concerns.
