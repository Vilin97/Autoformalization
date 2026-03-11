# Plan — Cycle 93

## Status summary

- **Sorry count**: 0
- **Files**: 31 files, ~9,520 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Split `fubini_double_integrable_coulomb` (`/simplify`)
- **What**: Issue 6c. At ~312 lines, this is the longest proof in the project. Extract helper lemmas for the inner integrability bound, the outer integrability bound, and the product-space integrability step into standalone lemmas in CoulombPSD.lean (or a new CoulombFubini.lean if needed).
- **Why**: The 312-line monolith is the most actionable code quality issue remaining.

### 2. Fix lean-lsp build desync (`/simplify`)
- **What**: Issue 8j. The lean-lsp MCP fails on IteratedDerivHelpers, TorusIntegration, GaussianHelpers. Previous `lake clean` + rebuild didn't fix it. Try `lake build` first, then `lean_build` to force LSP resync.
- **Why**: Blocks `lean_verify` for some theorems.

### 3. Investigate weakening `coulomb_flux_deriv_schwartz_decay` hypotheses (`/strengthen`)
- **What**: Check if `coulomb_flux_deriv_schwartz_decay` (CoulombFluxDiff.lean) uses more Schwartz regularity than needed for its role in the proof chain.
- **Why**: Consistent weakening pattern from cycles 89-92.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 1 file over 600 lines | Defs.lean, can't split per user pref |
| 6c | 3 proofs over 200 lines | `fubini_double` being split this cycle |
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | Community — ready |
| 8j | lean-lsp build desync | Tooling issue |
