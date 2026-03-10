# Plan — Cycle 64

## Status summary

- **Sorry count**: 0
- **Files**: 22 files, 7,838 lines
- **Heartbeat overrides**: 1 (`synthInstance.maxHeartbeats 160000`)
- **Deprecated `refine'`**: 36 uses across 5 files
- **Critique verdict**: CONDITIONAL ACCEPT

## Active multi-cycle strategies

### C^∞ → C^k weakening
Velocity smoothness weakened to C³ in cycle 63 (DONE). Spatial smoothness still C^∞ — C¹ suffices but requires changing `IsSpatiallyDiff` in the `FlatTorus3` typeclass. Deferred to backlog.

## This cycle's work items

### 1. Replace 36 deprecated `refine'` with `refine` (`/simplify`)
- **Why**: Critique #16. `refine'` is deprecated in Lean 4. 36 uses across 5 files.
- **Files**: CoulombPSD.lean (13), TorusInstance.lean (10), NewtonianPotential.lean (8), Section3Helpers.lean (4), SchwartzDecayDefs.lean (1)
- **Approach**: Mechanical replacement. `refine'` → `refine` with `?_` placeholders where needed.

### 2. Fix MEMORY.md (`/simplify`)
- **Why**: Critique #19. Says 21 files — now 22.
- **Approach**: Update file count and line counts.

### 3. Strengthen: make progress on one epistemic/generalization issue (`/strengthen`)
- **Why**: Critique conditions require progress on #6, #8, or #21.
- **Options (pick one)**:
  - Split Defs.lean (776 lines) — extract VMLInput/VMLSteadyState structures into separate file
  - Begin spatial smoothness weakening (C^∞ → C¹) — requires typeclass change, high risk

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| #6: 6 files over 600 lines | Code quality | TorusInstance 816, Defs 776, CoulombPSD 703 |
| #8: No non-equilibrium VDC instance | Epistemic | Hard |
| #18: multiGoal violations, long lines | Cosmetic | Low priority |
| #21: C^∞ spatial smoothness overkill | Epistemic | Requires typeclass change |
