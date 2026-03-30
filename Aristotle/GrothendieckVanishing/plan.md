# Work Plan — Grothendieck Vanishing

**Updated**: 2026-03-30T18:00Z

## Status Summary
- **Sorry count**: 2 (both in IrreducibleStep.lean, both Mathlib gaps)
- **Files**: 14 files, ~4137 lines
- **CI**: 2 runs in progress after perf decomposition
- **Peak heartbeats**: 3,200,000 (down from 12,800,000)

## Active multi-cycle strategies
- Both sorry's are confirmed Mathlib gaps. Aristotle failed (4 attempts total).
- Manual proof of subsheaf_contains requires stalk-level sheaf algebra.
- Filtered colimit sorry requires missing Mathlib LES infrastructure.

## This cycle's work items

1. **Fix CLAUDE.md** (P4, `/simplify`): Update stale "sole gap in Setup.lean" text.
2. **Fix main.lean docstring** (P4, `/simplify`): Clarify sorry count.
3. **Monitor CI** (step 5): Confirm green after perf decomposition.

## Backlog
- Decompose remaining 3.2M heartbeat proofs (P3)
- Split SetupCore.lean (1061 → 2 files) (P3)
- Manual subsheaf_contains proof attempt (P1, hard)
- Extract FlasqueVanishing for Mathlib PR (P3)
