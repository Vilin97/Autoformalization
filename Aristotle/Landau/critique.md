# Adversarial Critique — 2026-03-11 UTC (Cycle 95)

## Verdict: ACCEPT

---

## 0. Errors

`lake build Aristotle/Landau/main/CoulombConcreteTheorem42.lean` — **clean, 0 errors.**

---

## 1. Sorry's

**0 sorry's.** I found no issue.

---

## 2. Hidden Axioms

`lean_verify` on `CoulombConcreteTheorem42`: **0 axioms** (beyond `propext`, `Classical.choice`, `Quot.sound`). Same for `CoulombConcreteTheorem42_nonvacuous`. I found no issue.

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

`synthInstance.maxHeartbeats 160000` in CoulombForceTransport.lean. Acceptable.

### 6b. Files over 600 lines (1 file)

| File | Lines |
|------|-------|
| Defs.lean | 634 |

Can't be split per user preference.

### 6c. Long proofs (3 proofs over 200 lines)

| File | Proof | Lines |
|------|-------|-------|
| CoulombPSD.lean | `fubini_double_integrable_coulomb` | ~286 |
| CoulombFluxDiff.lean | `coulomb_flux_deriv_schwartz_decay` | ~231 |
| CoulombConcreteTheorem42.lean | `CoulombConcreteTheorem42` | ~222 |

`fubini_double` down from ~293 last cycle (hpf_decay deduplication). The pointwise bound `h_pw_bound` (~49 lines, starting ~line 310) and the integration bound `h_int_bound` (~61 lines, starting ~line 360) remain natural extraction candidates.

---

## 7. Documentation Lies

MEMORY.md says "22 files, ~8,700 lines". Actual: **31 files, 9,518 lines**. Stale.

---

## 8. Generalization Opportunities

### ~~8a. Extract helpers~~ — DONE

### ~~8b. Weaken regularity: C^∞ → optimal~~ — ANALYZED (cycle 90)

### 8c. Generalize beyond T^3 (HARD)

### 8d. Extract Mathlib-upstreamable lemmas (MEDIUM)

5 PR candidates identified in `experiments/mathlib_pr_candidates.md`: `iteratedFDeriv_clm_zero`, `norm_iteratedFDeriv_one_clm`, `integrable_one_add_norm_pow_mul`, `integrable_of_schwartz_bound`, `schwartz_poly_weighted_decay`. The latter 3 were generalized to arbitrary normed spaces in cycle 94.

### ~~8e–8h~~ — DONE

### 8i. hGradBound is Coulomb-specific (MINOR — DOCUMENTED)

### 8j. lean-lsp build desync (PERSISTENT)

The lean-lsp MCP rebuilds from source and hits errors in IteratedDerivHelpers, TorusIntegration, GaussianHelpers that don't reproduce with `lake build`. Confirmed persistent.

---

## 9. Mathlib Upstreamability

5 candidates documented in `experiments/mathlib_pr_candidates.md`. `iteratedFDeriv_clm_zero` is the strongest candidate (genuinely new, fully generalized).

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 6b | 1 file over 600 lines | Low | Open (Defs.lean, can't split) |
| 6c | 3 proofs over 200 lines | Low | Open (`fubini_double` splittable) |
| 7 | MEMORY.md stale line counts | Low | Open |
| 8c | Generalize beyond T^3 | Low | Deferred (hard) |
| 8d | Mathlib PR for helper lemmas | Low | Open (5 candidates) |
| 8j | lean-lsp build desync | Low | Open (tooling, persistent) |

### Conditions for ACCEPT

ACCEPT. All remaining issues are low severity. No correctness concerns.
