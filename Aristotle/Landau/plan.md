# Plan — Cycle 108

## Status summary

- **Sorry count**: 0
- **Files**: 32 files, 9,536 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Replace remaining `aesop` calls in Section3Helpers.lean (`/simplify`)
- **What**: Issue 6g follow-up. 2 `aesop` calls remain in `affine_gradient_antiderivative` (lines 450, 455). Replace with targeted tactics.
- **Why**: Continues the systematic aesop→simp migration started in cycle 107.

### 2. Tighten `simp +decide` in `analysis_fluxFactor` and `analysis_scalarFactor` (`/simplify`)
- **What**: Issue 6h. The first two Aristotle proofs (lines 24-62) use `simp +decide` broadly. Test whether `simp only [...]` with explicit lemma lists works.
- **Why**: These short proofs (~25 lines each) are good candidates for making simp calls more targeted without high risk.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6d | 3 proofs over 150 lines | Low — all under 200, diminishing returns |
| 6h | 35 `simp +decide` calls | Low — most in Fin 3 case analysis |
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | 5 candidates ready |
| 8j | lean-lsp build desync | Persistent tooling issue |
