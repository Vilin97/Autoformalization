# Adversarial Critique — 2026-03-10 UTC (Cycle 72)

## Verdict: ACCEPT

---

## 0. Errors

`lake build` — **clean, no errors.**

---

## 1. Sorry's

**0 sorry's.** I found no issue.

---

## 2. Hidden Axioms

Zero axioms on both main theorems (verified cycle 70). I found no issue.

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
| TorusInstance.lean | 816 |
| Defs.lean | 788 |
| Section3Helpers.lean | 757 |
| CoulombPSD.lean | 703 |
| CoulombSpatialTransport.lean | 662 |
| CoulombConcreteTheorem42.lean | 636 |
| CoulombFluxDiff.lean | 618 |

**Splitting candidates** (in priority order):
1. **Defs.lean (788)**: The Maxwellian section (IsMaxwellian, equilibriumMaxwellian, fderiv lemma, ~100 lines) could move to a new MaxwellianDefs.lean. Clean cut — Maxwellian defs are only used by CoulombConcreteTheorem42 and Section3Helpers.
2. **TorusInstance.lean (816)**: The FlatTorus3 instance (lines ~684-816) could be split from the helper lemmas (IBP, Stokes, Fubini proofs, lines 1-683). But this is a harder split.

---

## 7. Documentation Lies

I found no issue.

---

## 8. Generalization Opportunities

### ~~8a. Extract helpers from CoulombConcreteTheorem42~~ — DONE (cycles 70-71)

### 8b. Weaken spatial smoothness: C^∞ → C^2 (DEFERRED)

### 8c. Generalize beyond T³ (HARD)

### 8d. Extract Mathlib-upstreamable lemmas (MEDIUM)

### 8e. Split Defs.lean (MEDIUM)

---

## 8f. Code Style (AI Fingerprints)

Compared against two human-written Lean 4 formalizations of comparable scope:
- [Sphere Packing](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean) (22k LOC, 1615 decls, 89 files)
- [Brownian Motion](https://github.com/RemyDegenne/brownian-motion) (15k LOC, 956 decls, 50+ files)

| Metric | Aristotle | Sphere Packing | Brownian Motion |
|---|---|---|---|
| Max line length | **697** | 195 | 259 |
| Lines > 200 chars | **60** | **0** | 4 |
| Trailing semicolons | **352** | 34 | 4 |
| Spaces inside parens `( foo )` | **114** | 3 | 1 |
| Module docstrings `/-! -/` | **0** | 81 | 42 |
| Copyright headers | **0** | 36 | 38 |
| Lines/declaration | **33.9** | 13.9 | 15.5 |

**Diagnosis**: The codebase has unmistakable AI-generation artifacts.

1. **Mega-lines**: 60 lines exceed 200 chars (worst: 697). Human Lean projects cap at ~120. These are multi-tactic chains crammed onto one line (e.g., `CoulombPSD.lean` landau_bound proof).
2. **Trailing semicolons**: 352 occurrences. Idiomatic Lean uses one tactic per line with structured indentation, not `;` chains. Human projects have near-zero.
3. **Spaces inside parentheses**: `( foo )` instead of `(foo)` — 114 occurrences vs. ~0 in human code. Dead giveaway.
4. **No module docstrings**: Zero `/-! ... -/` headers. Every file in the human projects has one explaining purpose and contents.
5. **No copyright headers**: Standard in collaborative Lean. Missing here.
6. **Bloated proofs**: 33.9 lines/declaration vs. ~14 in human projects. AI inlines everything instead of decomposing into small helper lemmas.

**Priority fixes** (by impact):
1. Break lines > 100 chars (especially the 60 lines > 200 chars)
2. Replace trailing `;` with structured `<;>` or newline-separated tactics
3. Remove spaces inside parens: `( foo )` → `(foo)`
4. Add `/-! ... -/` module docstrings to all 22 files
5. Decompose long proofs into smaller lemmas

---

## 9. Mathlib Upstreamability

`iteratedFDeriv_clm_zero` and `norm_iteratedFDeriv_one_clm` (in Section3Helpers) are PR-ready.

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 6b | 7 files over 600 lines | Minor | Open |
| 8e | Defs.lean too large (788 lines) | Minor | Open |
| 8f | AI code style artifacts (long lines, semicolons, spacing) | Moderate | Open |

### Conditions for ACCEPT

This is an ACCEPT. The math is sound. The code style issues (8f) do not affect correctness but make the codebase visibly AI-generated, which undermines credibility for peer review.
