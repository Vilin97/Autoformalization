# Plan — Cycle 78

## Status summary

- **Sorry count**: 0
- **Files**: 22 files, ~8,785 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Break long lines with semicolons (`/simplify`)
- **What**: For lines > 100 chars that contain mid-line semicolons, break the semicolon-separated tactics onto separate lines. Target files: Section3Helpers, NewtonianPotential, Defs.
- **Why**: Simultaneously reduces both the >100 char line count (205) and the semicolon count (625). This is the highest-leverage cleanup remaining.
- **Approach**: For each file, find lines >100 chars containing `;`, break at `;` boundaries onto separate indented lines. Verify build after each file.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 7 files over 600 lines | Code quality — ongoing |
| 6c | Remaining short-line semicolons after this cycle | Code style — future |
| 8b | Weaken C^∞ → C^2 | Epistemic — hard |
| 8c | Generalize beyond T^3 | Epistemic — hard |
| 8d | Mathlib PR for helper lemmas | Community |
| 8e | Split Defs.lean | Code quality |
| 8f | Split Section3Helpers.lean (944 lines) | Code quality |
