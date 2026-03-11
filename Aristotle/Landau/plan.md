# Plan — Cycle 81

## Status summary

- **Sorry count**: 0
- **Files**: 22 files, ~9,056 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Break lines >100 chars in worst files (`/simplify`)
- **What**: Break lines exceeding 100 chars at natural points (after commas, type annotations, tactic arguments). Target: Section3Helpers (49), CoulombPSD (42), TorusInstance (32).
- **Why**: 183 lines exceed the 100-char Mathlib style limit. All remaining long lines are non-semicolon (long type signatures, `have` statements, complex tactic arguments). These are the 3 worst files with 123 of the 183 long lines.
- **Approach**: Break at natural boundaries: after `:=`, after commas in arguments, after `→`, inside long `simp [...]` lists. Verify build after each file.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 8 files over 600 lines | Code quality — ongoing |
| 6c | 358 plain semicolons | Code style — diminishing returns |
| 8b | Weaken C^∞ → C^2 | Epistemic — hard |
| 8c | Generalize beyond T^3 | Epistemic — hard |
| 8d | Mathlib PR for helper lemmas | Community |
| 8e | Split Defs.lean | Code quality |
| 8f | Split Section3Helpers.lean (1027 lines) | Code quality |
