# Plan — Cycle 76

## Status summary

- **Sorry count**: 0
- **Files**: 22 files, ~8,682 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Break mega-lines in remaining 4 files (`/simplify`)
- **What**: Break the 22 lines > 200 chars in CoulombPSD (7), TorusInstance (7), Section3 (4), VelocityDecayInstance (4)
- **Why**: After cycles 74-75 cleaned Section3Helpers and NewtonianPotential, these 4 files remain. Clearing them brings mega-line count to 0.
- **Approach**: Read each mega-line, break `;`-separated tactics onto separate lines. Verify build after each file.

### 2. Update stale MEMORY.md line counts (`/log`)
- **What**: Fix Section3Helpers (770 → 944), CoulombFlux (616 → 597), and other drifted counts
- **Why**: Critique flagged documentation lies

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 7 files over 600 lines | Code quality — ongoing |
| 6c | 1095 semicolons | Code style — future cycles |
| 6c | 222 lines > 100 chars | Code style — future cycles |
| 8b | Weaken C^∞ → C^2 | Epistemic — hard |
| 8c | Generalize beyond T^3 | Epistemic — hard |
| 8d | Mathlib PR for helper lemmas | Community |
| 8e | Split Defs.lean | Code quality |
| 8f | Split Section3Helpers.lean (944 lines) | Code quality — new |
