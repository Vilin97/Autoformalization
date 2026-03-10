# Plan — Cycle 63

## Status summary

- **Sorry count**: 0
- **Files**: 21 files, 7,895 lines
- **Heartbeat overrides**: 1 (`synthInstance.maxHeartbeats 160000`)
- **Linter warnings**: CLEAN (no unused simp/vars/refine'). Only cosmetic: long lines, multiGoal.
- **Critique verdict**: CONDITIONAL ACCEPT (no blocking conditions)

## Active multi-cycle strategies

### C^∞ → C^k weakening (audited cycle 62, not yet started)
C³ velocity + C¹ spatial suffices. ~80 occurrences across 15 files. Implementation strategy: start with velocity regularity in the abstract chain, leave spatial for later.

### Split TorusInstance.lean (not yet started)
1,162 lines. Extract Torus3 type definition + basic infrastructure into separate file.

## This cycle's work items

### 1. Split TorusInstance.lean (`/simplify`)
- **Why**: Critique #6. Largest file at 1,162 lines, nearly 2x the next largest.
- **Approach**: Extract the `Torus3` type definition, `periodicLift`, `torusGradX`/`torusDivX`/`torusCurlX` operators, and basic lemmas into `TorusDefs.lean`. Keep the FlatTorus3 instance proofs in `TorusInstance.lean`.
- **Files**: `Aristotle/Landau/main/TorusInstance.lean` → split into `TorusDefs.lean` + `TorusInstance.lean`

### 2. Begin C^∞ → C³ for velocity (`/strengthen`)
- **Why**: Critique #9. The smoothness audit identifies C³ as sufficient for velocity.
- **Approach**: Start with the abstract chain. Change `hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x)` to `ContDiff ℝ 3` in Theorem42 and VMLSteadyState, then fix downstream breakage.
- **Risk**: High — may cascade through many files. If it gets stuck, document findings and revert.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| #6: 4 remaining files over 600 lines | Code quality | After TorusInstance split |
| #8: No non-equilibrium VDC instance | Epistemic | Hard |
| #9: C^∞ → C^k full implementation | Epistemic | Multi-cycle |
| #18: multiGoal violations, long lines | Cosmetic | Low priority |
