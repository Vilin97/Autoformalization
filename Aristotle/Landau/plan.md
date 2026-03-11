# Plan — Cycle 103

## Status summary

- **Sorry count**: 0
- **Files**: 32 files, 9,543 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Extract `entropy_dissipation_continuous_coulomb` from CoulombConcreteTheorem42.lean (`/simplify`)
- **What**: The `hD_cont` field (lines 192-233, ~42 lines) is a self-contained proof that `fun x => entropyDissipation coulombKernel (f x)` is continuous, deriving it from the Vlasov equation. Extract it as a standalone lemma in `CoulombFluxDiff.lean` (or a new small file), reducing `CoulombConcreteTheorem42` from 188 to ~150 lines.
- **Why**: Issue 6d — reduces 4th longest proof below 150-line threshold. The logic is reusable and currently buried inside the VelocityDecayConditions construction.

### 2. Clean up stale comments in CoulombPSD.lean (`/simplify`)
- **What**: Issue 6e. Remove ~20 lines of scratch-work comments in `fubini_double_integrable_coulomb` (lines 191-215) that describe intermediate bounds but don't add value over the actual code.
- **Why**: Reduces noise and brings `fubini_double_integrable_coulomb` closer to 150 lines.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6d | 4 proofs over 150 lines | Low — all under 200 |
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | 5 candidates ready |
| 8j | lean-lsp build desync | Persistent tooling issue |
