# Plan — Cycle 111

## Status summary

- **Sorry count**: 0
- **Files**: 32 files, ~9,575 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending
- **`simp +decide`**: 69 (critique said 103 — stale count)

## This cycle's work items

### 1. Tighten `simp +decide` in targeted files (`/simplify`)
- **What**: Issue 6h. Reduce unnecessary `+decide` dischargers where plain `simp` or `simp only [...]` suffices. Focus on files with highest counts: TorusIntegration (24), Section3Helpers (20), GaussianHelpers (11).
- **Approach**: Use `lean_multi_attempt` to test if `simp` without `+decide` works for each call. Replace where possible.
- **Note**: Many `+decide` are legitimate for `Fin 3` index equality. Only remove where truly unnecessary.

### 2. Update stale critique count (`/simplify`)
- **What**: Issue 7 (documentation lies). Critique says 103 `simp +decide` but actual count is 69.
- **Approach**: Fix in the `/critique` update at end of cycle.

### 3. Mathematical strengthening: `IsMaxwellian` characterization (`/strengthen`)
- **What**: Add `IsMaxwellian.unique` — if `f = g` and both are Maxwellian, their parameters agree. This strengthens the API beyond `params_unique` (which only covers the exponent equality).
- **Alternative**: Add `IsMaxwellian.integrable` — Maxwellians are integrable (Gaussian integral converges).

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6d | 3 proofs over 150 lines | Low — all under 200, diminishing returns |
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | 5 candidates ready |
| 8j | lean-lsp build desync | Persistent tooling issue |
