# Plan — Cycle 96

## Status summary

- **Sorry count**: 0
- **Files**: 31 files, 9,532 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Extract `fubini_double_integral_bound` helper (`/simplify`)
- **What**: Issue 6c. Extract the ~61-line `h_int_bound` block (lines ~318-378 of CoulombPSD.lean) as a standalone lemma. This bounds `∫_w ‖F(v,w)‖ ≤ C_out * (1+‖v‖)^{2Kg} * f(v)`.
- **Why**: Biggest remaining extractable block from `fubini_double_integrable_coulomb` (~241 lines). Would reduce it to ~180 lines.

### 2. Investigate unused imports (`/simplify`)
- **What**: Check if any lean files have unused imports that could be trimmed.
- **Why**: Cleaner dependency graph. Carried over from cycle 94-95.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 1 file over 600 lines | Defs.lean, can't split per user pref |
| 6c | 3 proofs over 200 lines | `fubini_double` being shortened this cycle |
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | 5 candidates ready |
| 8j | lean-lsp build desync | Persistent tooling issue |
