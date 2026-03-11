# Plan — Cycle 77

## Status summary

- **Sorry count**: 0
- **Files**: 22 files, ~8,785 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Begin semicolon cleanup (`/simplify`)
- **What**: Start removing unnecessary semicolons in the worst-offending files. Target: TorusInstance (257 semis), Section3Helpers (214 semis), CoulombPSD (159 semis).
- **Why**: 1092 semicolons is the largest remaining code style issue. Semicolons between independent tactics on separate lines are unnecessary noise.
- **Approach**: For each file, replace `;\n` (semicolon at end of line before newline) with `\n`. Verify build after each file. Do NOT touch semicolons within single lines (e.g. `<;>` or tactic chains).

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 7 files over 600 lines | Code quality — ongoing |
| 6c | 206 lines > 100 chars | Code style — future cycles |
| 6c | ~800 remaining semicolons (after this cycle) | Code style — future cycles |
| 8b | Weaken C^∞ → C^2 | Epistemic — hard |
| 8c | Generalize beyond T^3 | Epistemic — hard |
| 8d | Mathlib PR for helper lemmas | Community |
| 8e | Split Defs.lean | Code quality |
| 8f | Split Section3Helpers.lean (944 lines) | Code quality |
