# Plan — Cycle 98

## Status summary

- **Sorry count**: 0
- **Files**: 31 files, 9,522 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Extract `hIBP_f_dg` from CoulombConcreteTheorem42 (`/simplify`)
- **What**: Issue 6c. Extract the 43-line inline `hIBP_f_dg` proof (flux_i * score_i integrability, lines 101-143) into a standalone lemma in CoulombFluxBound.lean.
- **Why**: CoulombConcreteTheorem42 is ~223 lines. Extracting this block saves ~40 lines, bringing it under 200. This is the last proof over 200 lines.

### 2. Check unused imports (`/simplify`)
- **What**: Check if any lean files have unused imports that could be trimmed.
- **Why**: Carried over from previous cycles.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 1 file over 600 lines | Defs.lean, can't split per user pref |
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | 5 candidates ready |
| 8j | lean-lsp build desync | Persistent tooling issue |
