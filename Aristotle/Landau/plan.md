# Plan — Cycle 97

## Status summary

- **Sorry count**: 0
- **Files**: 31 files, 9,535 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Extract `coulomb_entry_conv_uniform_bound` helper (`/simplify`)
- **What**: Issue 6c. Extract the repeated "Coulomb convolution of Schwartz function is uniformly bounded" pattern from `coulomb_flux_deriv_schwartz_decay` (hK_sup ~15 lines + hL_sup ~24 lines) into a shared helper.
- **Why**: Reduces `coulomb_flux_deriv_schwartz_decay` from ~231 to ~209 lines.

### 2. Check unused imports (`/simplify`)
- **What**: Check if any lean files have unused imports that could be trimmed.
- **Why**: Carried over from previous cycles.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 1 file over 600 lines | Defs.lean, can't split per user pref |
| 6c | 2 proofs over 200 lines | `coulomb_flux_deriv` being shortened this cycle |
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | 5 candidates ready |
| 8j | lean-lsp build desync | Persistent tooling issue |
