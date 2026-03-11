# Adversarial Critique — 2026-03-10 UTC (Cycle 76)

## Verdict: ACCEPT

---

## 0. Errors

`lake build Aristotle.Landau.main.CoulombConcreteTheorem42` — **clean, 0 errors.** Forced rebuild of TorusDefs.lean and Section3Helpers.lean (deleted .olean, rebuilt) — also clean.

---

## 1. Sorry's

**0 sorry's.** I found no issue.

---

## 2. Hidden Axioms

`lean_verify` on `VML.coulomb_concrete_theorem42`: `{"axioms":[],"warnings":[]}`. Zero axioms beyond the standard Lean 4 kernel axioms. No `admit`, `axiom`, `native_decide`, or `Decidable.decide` in any source file. I found no issue.

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

### 6b. Files over 600 lines (7 files)

| File | Lines |
|------|-------|
| Section3Helpers.lean | 944 |
| TorusInstance.lean | 815 |
| Defs.lean | 788 |
| CoulombPSD.lean | 711 |
| CoulombSpatialTransport.lean | 670 |
| CoulombConcreteTheorem42.lean | 623 |
| CoulombFluxDiff.lean | 616 |

Section3Helpers.lean has grown to **944 lines** (from 770 last cycle) — the mega-line breaking added indentation lines. It is now the longest file and urgently needs splitting.

### 6c. AI code style artifacts

| Metric | Current | Target |
|---|---|---|
| Lines > 200 chars | **22** (4 files) | 0 |
| Lines > 100 chars | **222** (17 files) | 0 |
| Semicolons (`;`) | **1095** (21 files) | < 50 |
| Max line length | **458** (CoulombPSD) | < 120 |

Worst offenders for long lines (> 200 chars): CoulombPSD (7), TorusInstance (7), Section3 (4), VelocityDecayInstance (4).

Worst offenders for lines > 100 chars: Section3Helpers (65), CoulombPSD (46), TorusInstance (41), NewtonianPotential (18).

---

## 7. Documentation Lies

MEMORY.md says Section3Helpers.lean is ~770 lines. It is actually **944 lines**. MEMORY.md says CoulombFlux.lean is ~616 lines; it is actually **597 lines**. These are stale.

---

## 8. Generalization Opportunities

### ~~8a. Extract helpers from CoulombConcreteTheorem42~~ — DONE (cycles 70-71)

### 8b. Weaken spatial smoothness: C^∞ → C^2 (DEFERRED)

### 8c. Generalize beyond T^3 (HARD)

### 8d. Extract Mathlib-upstreamable lemmas (MEDIUM)

### 8e. Split Defs.lean (MEDIUM)

### 8f. Split Section3Helpers.lean (NEW — HIGH PRIORITY)

At 944 lines, Section3Helpers.lean is now the longest file. It contains both Gaussian-specific helpers (equilibrium Maxwellian) and general iterated-derivative helpers (iteratedFDeriv for CLMs). These are logically independent and should be in separate files.

---

## 9. Mathlib Upstreamability

`iteratedFDeriv_clm_zero` and `norm_iteratedFDeriv_one_clm` (in Section3Helpers) are PR-ready.

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 6b | 7 files over 600 lines (Section3Helpers now 944) | Moderate | Open |
| 6c | 22 mega-lines (4 files), 222 lines >100 chars, 1095 semicolons | Moderate | Open |
| 7 | MEMORY.md line counts stale | Minor | Open |
| 8e | Defs.lean too large (788 lines) | Minor | Open |
| 8f | Section3Helpers.lean too large (944 lines) | Moderate | **New** |

### Conditions for ACCEPT

ACCEPT. All issues are code quality / style.
