# Plan — Cycle 95

## Status summary

- **Sorry count**: 0
- **Files**: 31 files, 9,518 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Extract `fubini_double_pointwise_bound` helper (`/simplify`)
- **What**: Issue 6c. Extract the ~49-line `h_pw_bound` block (starting ~line 310 of CoulombPSD.lean) as a standalone lemma. This is the pointwise bound |F(v,w)| ≤ 3Cg(1+‖v‖)^Kg * ‖v-w‖⁻¹ * Σ_j (...).
- **Why**: Most actionable reduction of the 286-line `fubini_double_integrable_coulomb` proof. Was planned last cycle but hpf_decay deduplication was done instead.

### 2. Fix stale MEMORY.md counts (`/simplify`)
- **What**: Issue 7. Update MEMORY.md "22 files, ~8,700 lines" → "31 files, ~9,500 lines".
- **Why**: Documentation accuracy.

### 3. Investigate unused imports (`/simplify`)
- **What**: Check if any lean files have unused imports that could be trimmed.
- **Why**: Cleaner dependency graph, potentially faster builds. Carried over from cycle 94.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 1 file over 600 lines | Defs.lean, can't split per user pref |
| 6c | 3 proofs over 200 lines | `fubini_double` being shortened this cycle |
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | 5 candidates ready |
| 8j | lean-lsp build desync | Persistent tooling issue |
