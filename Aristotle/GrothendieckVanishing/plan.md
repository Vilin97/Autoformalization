# Work Plan — Grothendieck Vanishing

**Updated**: 2026-03-29T16:50Z

## Status Summary

- **Sorry count**: 1 (`IrreduciblePosVanishing` at Setup.lean:95)
- **Files**: 13 in `main/`, compiling locally but **CI BROKEN for 3 commits**
- **Root cause of CI failure**: SetupCore.lean never committed, Setup.lean refactoring never staged
- **Aristotle API**: returning 500 errors; 3 jobs submitted but status unknown

## Priority Actions (This Cycle)

### 1. (P0) Fix stale comments + commit the refactoring — FIX CI
**Files**: SetupCore.lean (untracked), Setup.lean (modified), ReducibleVanishing.lean (modified)
**Action**: Fix stale comments at SetupCore.lean:211,751, then stage all three files and commit.
**Step**: `/cleanup` + `/commit`

### 2. (P0) Verify build locally before committing
**Action**: Run `lake env lean` on Setup.lean to confirm the refactored state compiles.
**Step**: `/prove` (verification only)

### 3. (P1) Attempt IrreduciblePosVanishing directly
**File**: Setup.lean:95
**Approach**: The sorry needs Hartshorne Steps 3-5. Rather than waiting for Aristotle:
- The current proof already has: proper closed Z ⊊ X, dim Z < dim X, ClosedImmissionSES, pushforward vanishing.
- The gap is: kernel vanishing (`hKer`). The kernel K has stalks zero on Z but support closure = X.
- Direct approach: try to prove `hKer` by showing K admits a filtration by subsheaves of `zeroOutsideInt` type, each of which vanishes by the SES `0 → Z_U → Z_X → Z_Y → 0`.
- This is hard and likely multi-cycle. Decompose into sub-lemmas.
**Step**: `/prove`

## Active Multi-Cycle Strategies

### Strategy A: IrreduciblePosVanishing via Hartshorne Steps 3-5
**Status**: 3 Aristotle jobs submitted (4e978c1c, 6eb803e4, f3ae1cd9), API returning 500s.
**Parallel work**: Attempt direct proof decomposition:
1. SES `0 → Z_U → Z_X → Z_Y → 0` (uses zeroOutsideInt infrastructure in ZeroOutside.lean)
2. Z_X flasque vanishing (proved: constantSheaf_cohomology_vanishing)
3. Z_Y vanishing by IH (pushforward from lower-dim space)
4. Kernel of F → i_*i^*F reduces to quotients of Z_U (Hartshorne Steps 3-4)

### Strategy B: Heartbeat reduction (ongoing)
**Target**: Reduce all `maxHeartbeats` to ≤ 800000.
**Priority**: P1 for 12.8M and 6.4M; P2 for 3.2M locations.
**Approach**: Profile with `lean_profile_proof`, extract intermediate lemmas, simplify tactic blocks.

## Backlog

- Split SetupCore.lean (1027 lines) into smaller files (P2)
- Universe polymorphism for main theorem (P3)
- Generalize from AddCommGrpCat to ModuleCat R (P3)
- PR `cohomologyPresheafTopEquiv` and `subsingleton_ext_of_ses` to Mathlib (P4)
- Update GrothendieckVanishing.lean:8 docstring (P4)
