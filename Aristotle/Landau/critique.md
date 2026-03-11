# Adversarial Critique — 2026-03-10 UTC (Cycle 68)

## Verdict: CONDITIONAL ACCEPT

---

## 0. Errors

`lake build` — **clean, no errors.**

---

## 1. Sorry's

**2 sorry's** in `CoulombConcreteTheorem42_nonvacuous`:

| Line | Goal | Statement | Risk |
|------|------|-----------|------|
| ~429 | (7) hDecay | `∀ N k, ∃ C > 0, ∀ x v, ‖iteratedFDeriv ℝ k eM v‖ * (1+‖v‖)^N ≤ C` | Medium — needs polynomial×Gaussian bound + `norm_iteratedFDeriv_comp_le` |
| ~452 | (10) | Vlasov equation: `0 = ν * LandauOperator coulombKernel eM` | **High** — requires Maxwellian in kernel of Landau operator |

Note: (7) was decomposed in cycle 67 — `hGradDecay` is proved, only `hDecay` remains sorry'd.

~~(12) Gauss~~ — **closed** in cycle 67 via `simp` (divergence of zero simplifies).

**Worst-case scenario for sorry (10):** If `LandauOperator` is defined in a way that doesn't match the standard physics definition, the non-vacuousness claim would be false. Sorry (10) is the only thing standing between "rigorous theorem" and "vacuous tautology".

---

## 2. Hidden Axioms

`lean_verify` on both main theorems: zero axioms beyond the standard three. No `admit`, `axiom`, `native_decide`, or linter suppression found.

I found no issue.

---

## 3. Circularity

With 8 of 10 non-trivial goals proved, the non-vacuousness defense is substantially complete. The critical gap is sorry (10) — the Vlasov equation.

---

## 4. Hypothesis Audit

No change. All 13 hypotheses are independent and necessary.

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

### 6c. Long lines

No lines over 100 characters found.

---

## 7. Documentation Lies

MEMORY.md updated in cycle 67: sorry count (2), line counts (~8,000, ~460 for CoulombConcreteTheorem42). Accurate.

I found no issue.

---

## 8. Generalization Opportunities

### 8a. Close remaining 2 non-vacuousness sorry's (MEDIUM-HARD)

- (7) hDecay: `‖iteratedFDeriv ℝ k eM v‖ * (1+‖v‖)^N ≤ C`. Strategy: use `norm_iteratedFDeriv_comp_le` (Mathlib) for the iterated derivative bound, plus `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero` for the polynomial×Gaussian bound. Sub-lemmas identified in cycle 67.
- (10) Vlasov: `LandauOperator coulombKernel eM = 0`. Hardest sorry — requires collision operator analysis.

### 8b. Weaken spatial smoothness: C^∞ → C^2 (DEFERRED)

### 8c. Generalize beyond T³ (HARD)

### 8d. Extract Mathlib-upstreamable lemmas (MEDIUM)

---

## 9. Mathlib Upstreamability

Unchanged. Schwartz decay machinery and torus IBP lemmas are most plausible candidates.

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 6 | 5 files over 600 lines (TorusInstance 816, Defs 785) | Minor | Open |
| 8 | Non-vacuousness theorem has 2 sorry's | Epistemic | Open (8 of 10 goals closed) |

### Conditions for ACCEPT

Close sorry (7) hDecay (polynomial×Gaussian bound). Sorry (10) is genuinely hard and may require extended effort. No new sorry's should be introduced.
