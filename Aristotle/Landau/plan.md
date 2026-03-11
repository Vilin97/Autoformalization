# Plan — Cycle 82

## Status summary

- **Sorry count**: 0
- **Files**: 22 files, ~9,296 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Break remaining lines >100 chars (`/simplify`)
- **What**: Break the 60 remaining lines >100ch in the 14 remaining files. Top targets: NewtonianPotential (15), CoulombFluxDiff (12), VelocityDecayInstance (10), Section3 (5), Section5 (4).
- **Why**: After cycle 81 cleared the 3 worst files, only 60 long lines remain. Clearing them would bring the project to 0 lines >100ch.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 8 files over 600 lines | Code quality — ongoing |
| 6c | 356 plain semicolons | Code style — diminishing returns |
| 8b | Weaken C^∞ → C^2 | Epistemic — hard |
| 8c | Generalize beyond T^3 | Epistemic — hard |
| 8d | Mathlib PR for helper lemmas | Community |
| 8e | Split Defs.lean | Code quality |
| 8f | Split Section3Helpers.lean (1162 lines) | Code quality |
