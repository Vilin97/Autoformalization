# Adversarial Critique — 2026-03-10 UTC (Cycle 71)

## Verdict: ACCEPT

---

## 0. Errors

`lake build` — **clean, no errors.**

---

## 1. Sorry's

**0 sorry's.** All 22 files compile without `sorry`.

I found no issue.

---

## 2. Hidden Axioms

`lean_verify` on both main theorems: **zero axioms**. No `admit`, `axiom`, `native_decide`, or linter suppression found.

I found no issue.

---

## 3. Circularity

All 10 non-trivial goals in `CoulombConcreteTheorem42_nonvacuous` fully proved. No circularity.

I found no issue.

---

## 4. Hypothesis Audit

All 13 hypotheses are independent and necessary.

I found no issue.

---

## 5. Mathematical Correctness

I found no issue.

---

## 6. Code Quality

### 6a. maxHeartbeats overrides: 1 total

`synthInstance.maxHeartbeats 160000` in CoulombSpatialTransport.lean. Acceptable.

### 6b. Files over 600 lines (7 files)

| File | Lines |
|------|-------|
| TorusInstance.lean | 816 |
| Defs.lean | 788 |
| CoulombConcreteTheorem42.lean | 742 |
| CoulombPSD.lean | 703 |
| CoulombSpatialTransport.lean | 662 |
| Section3Helpers.lean | 647 |
| CoulombFluxDiff.lean | 618 |

**TorusInstance.lean (816)** is the largest. It contains the concrete FlatTorus3 instance with all 23 property proofs. Splitting would require a new file for torus-specific lemmas (e.g., IBP, Stokes, Fubini proofs) vs the instance itself.

**Defs.lean (788)** contains definitions, VelocityDecayConditions, FlatTorus3 typeclass, and Maxwellian defs. The Maxwellian section (~150 lines) could be split to MaxwellianDefs.lean.

### 6c. Long lines

~~3 long-line warnings in Defs.lean~~ — Fixed in cycle 70.

---

## 7. Documentation Lies

I found no issue.

---

## 8. Generalization Opportunities

### 8a. Extract remaining helpers from CoulombConcreteTheorem42 (EASY)

`norm_iteratedFDeriv_proj_sq_le` and `quadratic_iteratedFDeriv_bound` (~80 lines) remain in CoulombConcreteTheorem42.lean. These are polynomial/quadratic derivative bounds, not Coulomb-specific. Moving them would reduce the file to ~660 lines.

### 8b. Weaken spatial smoothness: C^∞ → C^2 (DEFERRED)

### 8c. Generalize beyond T³ (HARD)

### 8d. Extract Mathlib-upstreamable lemmas (MEDIUM)

`iteratedFDeriv_clm_zero` and `norm_iteratedFDeriv_one_clm` (now in Section3Helpers) are PR-ready for Mathlib.

### 8e. Split Defs.lean (MEDIUM)

Extract Maxwellian definitions and lemmas (~150 lines) to MaxwellianDefs.lean. Would bring Defs.lean under 650 lines.

---

## 9. Mathlib Upstreamability

Most PR-ready:
- `iteratedFDeriv_clm_zero`: iteratedFDeriv of a CLM vanishes at order ≥ 2
- `norm_iteratedFDeriv_one_clm`: ‖iteratedFDeriv 1 f x‖ = ‖f‖ for CLM f

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 6b | 7 files over 600 lines | Minor | Open |
| 8a | Remaining derivative helpers in wrong file | Minor | Open |
| 8e | Defs.lean too large (788 lines) | Minor | Open |

### Conditions for ACCEPT

This is an ACCEPT. All remaining issues are minor code quality improvements.
