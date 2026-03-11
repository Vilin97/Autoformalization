# Plan — Cycle 110

## Status summary

- **Sorry count**: 0
- **Files**: 32 files, 9,562 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Eliminate all remaining `aesop` from codebase (`/simplify`)
- **What**: Issue 6i. 9 `aesop` calls across CoulombPSDHelpers (2), NewtonianPotential (4), CoulombFlux (2), SchwartzDecayDefs (1). All replacements already verified via `lean_multi_attempt`.
- **Why**: Completes the systematic `aesop` elimination started in cycle 107.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6d | 3 proofs over 150 lines | Low — all under 200, diminishing returns |
| 6h | 103 `simp +decide` calls | Low — most in Fin 3 case analysis |
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | 5 candidates ready |
| 8j | lean-lsp build desync | Persistent tooling issue |
