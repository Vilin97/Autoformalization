# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-02T18:25Z

## Status Summary
- **CI**: GREEN (latest push in_progress, previous green)
- **Heartbeat overrides**: 0
- **Sorry count**: 1 in IrreducibleStep.lean (`ext_comm_filtered_colimit_mono`, line 1245)
- **Files**: 15 files under `main/`, ~5079 lines
- **New this session**: `sheafH_vanishing_cascade` proved in GrothendieckVanishing.lean

## Remaining Sorry (1)

### `ext_comm_filtered_colimit_mono` (line 1227)
**Genuine Mathlib API gap**: Ext^n(Z,-) preserves filtered colimits of mono diagrams.

After extensive analysis (documented in proofs.md), all dimension-shifting approaches
fail at degree ≥ 2 because cohomological vanishing does not propagate to subsheaves.
The correct proof requires Čech cohomology, universal δ-functors, or Godement resolution,
none of which are in Mathlib v4.28.0.

## This Cycle's Work Items

### 1. Fix documentation issues (P3, `/simplify`)
- Fix "ONLY axiom" → "ONLY sorry" in IrreducibleStep.lean:1236
- Fix "m₀ ≥ 1" → remove constraint in GrothendieckVanishing.lean docstring
- Fix CLAUDE.md: remove nonexistent FiniteGeneratorReduction.lean from tree
- Fix CLAUDE.md: remove stale heartbeat reference

### 2. Address dead cascade code (P2, `/simplify`)
- Either integrate cascade into main proof OR remove `private` and add `#check`
  to make them reachable. Best: keep the theorems but make them non-private, since
  they are correct infrastructure that may be used in future restructuring.

### 3. Submit sorry to Aristotle (P1, `/submit-aristotle`)
- The sorry has NOT been submitted with the current formulation. Submit it.
  Previous Aristotle attempts used different formulations and all failed, but
  the current statement is cleaner.

### 4. Attempt sorry proof (P0, `/prove`)
- Try the n=0 case directly using objectwise colimits (sheaf-specific)
- Even partial progress (proving n=0, n=1) is valuable for decomposition

## Backlog

| Priority | Item |
|----------|------|
| P2 | Split IrreducibleStep.lean (1582 lines → ≤1000) |
| P1 | Docs/blueprint 404 — needs deploy workflow |
| P3 | Clean up aristotle-jobs.json (many stale entries) |
