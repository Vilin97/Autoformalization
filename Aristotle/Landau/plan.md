# Plan — Cycle 92

## Status summary

- **Sorry count**: 0
- **Files**: 30 files, ~9,520 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Fix lean-lsp build desync (`/simplify`)
- **What**: Issue 8j. The lean-lsp MCP reports errors in IteratedDerivHelpers, TorusIntegration, GaussianHelpers that don't reproduce with `lake build`. Likely needs `lake clean` + `lake exe cache get` + rebuild to resync Mathlib oleans.
- **Why**: Blocks `lean_verify` and other LSP tools needed for critique.

### 2. Split CoulombConcreteTheorem42.lean (653 lines) (`/simplify`)
- **What**: Issue 6b. The only remaining splittable file over 600 lines (Defs.lean can't be split per user preference). Extract the VelocityDecayConditions proof block (which constructs the 19-field instance) into a separate file, keeping the final theorem assembly in the main file.
- **Why**: Last achievable file size reduction.

### 3. Weaken `hg_schwartz` in `coulomb_flux_component_bound` (`/strengthen`)
- **What**: `coulomb_flux_component_bound` in CoulombFluxBound.lean takes `hg_schwartz : ∀ N k, ...` (all derivatives), but only uses k=0 and k=1 decay. Weaken to match the k≤2 pattern used elsewhere.
- **Why**: Consistency with the UniformSchwartzDecay weakening done in cycle 89.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 2 files over 600 lines | Defs.lean hard to split (user pref), CoulombConcreteTheorem42 being split this cycle |
| 6c | 2 proofs over 100 lines | Natural monoliths, low ROI to split |
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | Community — ready |
