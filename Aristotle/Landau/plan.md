# Plan — Cycle 100

## Status summary

- **Sorry count**: 0
- **Files**: 31 files, 9,537 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Move FlatTorus3 lemmas out of Defs.lean (`/simplify`)
- **What**: Issue 6b. Defs.lean is 634 lines (only file over 600). Move the ~180 lines of FlatTorus3 derived lemmas (hSpatialMul through maxwellian_params_isSpatiallyDiff, lines 452-631) to a new `FlatTorus3Lemmas.lean`. Keep definitions, the class itself, instances, and spatialIntegral in Defs.lean.
- **Why**: Gets Defs.lean under 600 lines (~454 after extraction). The user said "moving lemmas out is OK but definitions must stay together."
- **Consumers**: Section4, Section6, Section7, VMLInputDerive, Theorem42 — all need `import Aristotle.Landau.main.FlatTorus3Lemmas` added.

### 2. Update stale line counts in MEMORY.md (`/simplify`)
- **What**: MEMORY.md says "22 files, ~8,700 lines" but we have 31 files, 9,537 lines. Several file line counts are also stale.
- **Why**: Documentation accuracy (issue 7 in critique pattern).

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | 5 candidates ready |
| 8j | lean-lsp build desync | Persistent tooling issue |
