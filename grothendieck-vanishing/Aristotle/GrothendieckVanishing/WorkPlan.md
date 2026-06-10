# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-05T01:15Z

## Status Summary

- **Sorry count**: 0 — FULLY PROVED
- **Axioms**: 0 (verified by `lean_verify`)
- **Files**: 20 `.lean` in `main/`, ~5844 total lines
- **CI**: Last run PASSED. PR #13 open with auto-merge.
- **Critique verdict**: CONDITIONAL ACCEPT — code quality issues remain
- **Blueprint**: Infrastructure created (content.tex, deploy.yml updated), not yet live (deploys on merge to `grothendieck-vanishing`)

## This Cycle's Work Items

### 1. Delete dead code: `CohomologyIso.lean` (`/cleanup`)
- File is not imported by any other file in the project.
- Contains `cohomologyPresheafTopEquiv` which is never referenced.
- Remove the file entirely and remove it from `main.lean` file listing comment.

### 2. Clean stale Aristotle tracking (`/cleanup`)
- `aristotle-jobs.json` has a completed job entry. Clear it.

### 3. Fix MEMORY.md stale Mathlib version (`/simplify`)
- MEMORY.md says `v4.24.0`, actual is `v4.28.0`. Update.

### 4. Commit and push (`/commit`)
- Commit blueprint + cleanup + critique + plan.

## Backlog

- **P3**: `FiniteGeneratorReduction.lean` at 624 lines (exceeds 600 soft limit). Split into two files. Not urgent — the file is well-organized with clear section markers.
- **P3**: 3 files use blanket `import Mathlib`. Replace with targeted imports. Risk: may break if we miss a dependency. Defer to a dedicated cleanup cycle.
- **P4**: Generalize coefficient category from `AddCommGrpCat` to arbitrary Grothendieck abelian.
- **P4**: Strengthen `Subsingleton` to `IsZero`.
- **P4**: Upstream lemmas to Mathlib (`FlasqueVanishing`, `isFlasque_filtered_colimit`, `PresheafFilteredColimit`, `ConstantSheafFlasque`).
