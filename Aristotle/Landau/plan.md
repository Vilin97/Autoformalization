# Plan — Cycle 72

## Status summary

- **Sorry count**: 0
- **Files**: 22 files, ~8,300 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Split Maxwellian section from Defs.lean (`/simplify`)
- **What**: Extract `IsMaxwellian`, `equilibriumMaxwellian`, `fderiv_equilibriumMaxwellian`, and related lemmas to a new `MaxwellianDefs.lean`
- **Why**: Reduces Defs.lean from 788 to ~680 lines. Maxwellian defs are only needed by CoulombConcreteTheorem42 and Section3Helpers.
- Fixes critique issue 8e

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 7 files over 600 lines | Code quality — ongoing |
| 8b | Weaken C^∞ → C^2 | Epistemic — hard |
| 8c | Generalize beyond T³ | Epistemic — hard |
| 8d | Mathlib PR for helper lemmas | Community |
