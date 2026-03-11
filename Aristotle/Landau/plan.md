# Plan — Cycle 105

## Status summary

- **Sorry count**: 0
- **Files**: 32 files, 9,538 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending
- **Dead code**: 0 unused lemmas (208 checked)

## This cycle's work items

### 1. Shorten `coulomb_flux_deriv_schwartz_decay` calc chain (`/simplify`)
- **What**: Issue 6d. The calc chain (lines 112-170) has a verbose triangle-inequality + norm_smul step (lines 112-137, ~26 lines) that could be tightened by combining the two calc steps into one. The mechanical `simp [norm_smul, Real.norm_eq_abs]` after the triangle inequality can be fused with it.
- **Why**: Reduces the longest remaining proof. Even 10 lines saved is worthwhile.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6d | 2 proofs over 150 lines | Low — diminishing returns |
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | 5 candidates ready |
| 8j | lean-lsp build desync | Persistent tooling issue |
