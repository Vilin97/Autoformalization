# Plan — Cycle 61

## Status summary

- **Sorry count**: 0
- **Files**: 21 files, 7,850 lines
- **Heartbeat overrides**: 1 (`synthInstance.maxHeartbeats 160000`)
- **Linter suppressions**: 0
- **lean_verify**: both theorems clean
- **Critique verdict**: CONDITIONAL ACCEPT (condition: fix unused simp args in Defs.lean)

## Active multi-cycle strategies

None yet. This is the first plan.md.

## This cycle's work items

### 1. Fix unused simp args in Defs.lean (`/simplify`)
- **Why**: Defs.lean is imported by every file. ~8 unused simp arg warnings there affect the whole chain. This is the blocking ACCEPT condition.
- **Approach**: Read each warning, remove the unused argument, rebuild.
- **Files**: `Aristotle/Landau/main/Defs.lean`

### 2. Fix deprecated `integral_mul_right` (`/simplify`)
- **Why**: Trivial, one-line fix. Will break on next Mathlib update.
- **Approach**: Replace `integral_mul_right` with `integral_mul_const` at Defs.lean:419.
- **Files**: `Aristotle/Landau/main/Defs.lean`

### 3. Prove uniqueness of T_eq (`/strengthen`)
- **Why**: Rated EASY in critique. The conclusion asserts `∃ T_eq` but not `∃! T_eq`. Uniqueness follows from the Gaussian integral being strictly monotone in T and normalization ∫ f = ρ_ion.
- **Approach**: Add a uniqueness lemma, then strengthen the conclusion of CoulombConcreteTheorem42 (or add a corollary). This may require Mathlib's `integral_gaussian` or monotonicity results.
- **Files**: `Aristotle/Landau/main/CoulombConcreteTheorem42.lean`, possibly `Defs.lean` or a new helper

## Backlog

| Issue | Category | Step | Notes |
|-------|----------|------|-------|
| #7: hGradBound derivable | Epistemic | `/strengthen` | Medium-High effort. Requires formalizing compactness argument for exp-polynomial bounds. |
| #8: No non-equilibrium VDC instance | Epistemic | `/strengthen` | The single most important structural weakness per critique. Hard: requires constructing a non-trivial solution. |
| #9: C^∞ → C^k | Epistemic | `/strengthen` | Medium effort. Audit every ContDiff usage across the chain. |
| #6: 5 files over 600 lines | Code quality | `/simplify` | TorusInstance (1162) most pressing. Large effort to split well. |
| #16: ~40 unused simp args (Section3Helpers) | Code quality | `/simplify` | Tedious but low risk. Do after Defs.lean is clean. |
| #18: Style issues in Section3Helpers | Code quality | `/simplify` | refine' → refine, multiGoal fixes, long lines. |
