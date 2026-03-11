# Plan — Cycle 91

## Status summary

- **Sorry count**: 0
- **Files**: 29 files, ~9,521 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Split CoulombFlux.lean (607 lines) (`/simplify`)
- **What**: CoulombFlux.lean is the last remaining Coulomb file over 600 lines. Split the flux measurability / integrability helpers from the flux component bounds and log-integrability results.
- **Why**: Issue 6b. Reduces files over 600 lines from 3 to 2 (Defs.lean 634 and CoulombConcreteTheorem42 653 are harder to split).

### 2. Extract Lorentz HasFDerivAt helper in Section4.lean (`/simplify`)
- **What**: Issue 6d. `lorentz_force_div_zero` and `lorentz_partial_diag_zero` duplicate identical `HasFDerivAt` computations for all 3 Lorentz force components (~18 lines). Extract a shared helper lemma.
- **Why**: Reduces code duplication, makes Section4 more maintainable.

### 3. Prepare Mathlib PR for helper lemmas (`/strengthen`)
- **What**: Issue 8d. `iteratedFDeriv_clm_zero` and `norm_iteratedFDeriv_one_clm` are PR-ready. Prepare standalone files with Mathlib-style proofs and documentation.
- **Why**: Community contribution, validates our helpers against Mathlib standards.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 2 files over 600 lines (after splitting CoulombFlux) | Defs.lean + CoulombConcreteTheorem42 — hard to split |
| 6c | 2 proofs over 100 lines | transport_entropy_from_vlasov, polynomial_identity_from_vlasov — natural monoliths |
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | Community — in progress |
