# Plan — Cycle 94

## Status summary

- **Sorry count**: 0
- **Files**: 31 files, 9,517 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Extract `fubini_double_pointwise_bound` helper (`/simplify`)
- **What**: Issue 6c. Extract the ~49-line `h_pw_bound` block (lines ~340-390 of CoulombPSD.lean) as a standalone lemma. This is the pointwise bound |F(v,w)| ≤ 3Cg(1+‖v‖)^Kg * ‖v-w‖⁻¹ * Σ_j (...). Also consider extracting the integration bound `h_int_bound` (~61 lines).
- **Why**: Most actionable reduction of the 293-line `fubini_double_integrable_coulomb` proof.

### 2. Deduplicate `hpf_decay` pattern (`/simplify`)
- **What**: The "polynomial-weighted Schwartz decay" `hpf_decay` pattern (lines ~70-75 in CoulombPSD.lean) appears identically in `psd_outer_integrable_coulomb` and `fubini_double_integrable_coulomb`. Extract as `schwartz_poly_weighted_decay` helper in SchwartzDecayDefs.lean.
- **Why**: Further deduplication following cycle 93's pattern.

### 3. Investigate unused imports (`/simplify`)
- **What**: Check if any lean files have unused imports that could be trimmed.
- **Why**: Cleaner dependency graph, potentially faster builds.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 1 file over 600 lines | Defs.lean, can't split per user pref |
| 6c | 3 proofs over 200 lines | `fubini_double` being shortened this cycle |
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | Community — ready |
| 8j | lean-lsp build desync | Persistent tooling issue |
