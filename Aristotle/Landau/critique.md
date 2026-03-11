# Adversarial Critique — 2026-03-10 UTC (Cycle 65)

## Verdict: CONDITIONAL ACCEPT

Cycle 64 eliminated all 36 deprecated `refine'`, fixed MEMORY.md, added `equilibriumMaxwellian_pos` and `CoulombConcreteTheorem42_nonvacuous` (with 10 sorry's). The non-vacuousness theorem is a welcome structural addition addressing the most important weakness, but it's mostly sorry'd.

---

## 0. Errors

`lake build` — **clean, no errors.**

---

## 1. Sorry's

**6 sorry's** in `CoulombConcreteTheorem42_nonvacuous`. Hypotheses (3)-(6) and (13) are proved. Sorry's remain for (7)-(12): Schwartz decay, exp lower bound, gradient bound, Vlasov, Ampere, Gauss.

These sorry's are in a non-critical theorem (the main theorems `CoulombConcreteTheorem42` and `Theorem42` remain 0-sorry). Still, 10 sorry's in a theorem claiming "non-vacuousness" undermine that claim — you can't claim non-vacuousness when you haven't proved it.

---

## 2. Hidden Axioms

Standard axioms only. I found no issue.

---

## 3. Circularity

`CoulombConcreteTheorem42_nonvacuous` partially addresses this (when proved). Currently sorry'd, so the circularity concern is acknowledged but not yet resolved.

---

## 4. Hypothesis Audit

No change from cycle 64. All 13 hypotheses are independent and necessary.

---

## 5. Mathematical Correctness

I found no divergence. The main theorems are kernel-verified.

---

## 6. Code Quality

### 6a. Deprecated `refine'`: 0 remaining

All 36 occurrences eliminated in cycle 64. **RESOLVED.**

### 6b. maxHeartbeats overrides: 1 total

`synthInstance.maxHeartbeats 160000` in CoulombSpatialTransport.lean. Acceptable.

### 6c. Files over 600 lines (6 files)

| File | Lines |
|------|-------|
| TorusInstance.lean | 816 |
| Defs.lean | 785 |
| CoulombPSD.lean | 703 |
| CoulombSpatialTransport.lean | 662 |
| Section3Helpers.lean | 625 |
| CoulombFluxDiff.lean | 618 |

Defs.lean grew from 776 to 785 (new `equilibriumMaxwellian_pos`). Still 6 files over 600.

---

## 7. Documentation Lies

MEMORY.md updated in cycle 64. Now says 22 files, ~7,838 lines. Actual: 22 files, 7,888 lines (drift from new code). Minor.

---

## 8. Generalization Opportunities

### 8a. Weaken spatial smoothness: C^∞ → C¹ (BLOCKED)

Investigated in cycle 64: `hDiff_grad` in FlatTorus3 requires same smoothness level for gradient components. Would need two-level predicate. Deferred.

### 8b. Prove non-vacuousness sorry's (10 remaining) (MEDIUM)

Close the 10 sorry's in `CoulombConcreteTheorem42_nonvacuous`. Most are routine (Gaussian is Schwartz, score is polynomial, Vlasov reduces to 0=0 for equilibrium).

### 8c. Generalize beyond T³ (HARD)

Unchanged.

---

## 9. Mathlib Upstreamability

Unchanged from cycle 64.

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 6 | 6 files over 600 lines (TorusInstance 816, Defs 785) | Minor | Open |
| 8 | Non-vacuousness theorem has 6 sorry's | Epistemic | Open (4 closed cycle 65) |
| 16 | ~~36 deprecated refine'~~ | ~~Minor~~ | **RESOLVED** (cycle 64) |
| 18 | Cosmetic: multiGoal violations, long lines | Trivial | Open |
| 19 | ~~MEMORY.md stale~~ | ~~Trivial~~ | **RESOLVED** (cycle 64) |
| 21 | C^∞ spatial smoothness overkill (blocked by typeclass) | Minor | Deferred |

### Conditions for ACCEPT

Close at least 2 sorry's in the non-vacuousness theorem (#8), or make progress on file splitting (#6).
