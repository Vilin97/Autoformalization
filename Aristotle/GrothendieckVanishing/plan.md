# Work Plan — Grothendieck Vanishing

**Updated**: 2026-03-30T04:00Z

## Status Summary
- **Sorry count**: 3 (decomposed from 1)
- **Files**: 14, ~3686 lines
- **CI**: 3 runs in-progress

## This cycle's work items

1. **Move sorry lemmas + IrreduciblePosVanishing to IrreducibleStep.lean** (`/prove`)
   Fix the circular dependency: Setup.lean → sorry lemmas need IrreducibleStep tools.
   Move `zeroOutsideInt_cohomology_vanishing`, `epiImage_zeroOutsideInt_vanishing`,
   `directLimit_cohomology_vanishing`, `irreduciblePos_kernel_subsingleton`,
   `IrreduciblePosVanishing` from Setup.lean to IrreducibleStep.lean.
   Keep `irreduciblePos_pushforward_subsingleton` and `exists_closed_subset_lt_dim`
   in Setup.lean.

2. **Prove `zeroOutsideInt_cohomology_vanishing`** (`/prove`)
   Uses `zeroOutsideInt_vanishing` (already in IrreducibleStep) + cokernel vanishing
   at degree m-1. The cokernel vanishing at m-1 ≥ dim X is provable by inlining the
   `cokernel_openHom_vanishing` argument with the weaker hypothesis.

## Backlog
- Prove `epiImage_zeroOutsideInt_vanishing` (Step 4: subsheaf structure of Z_V)
- Prove `directLimit_cohomology_vanishing` (Step 3A: Hartshorne 2.8-2.9)
- Reduce heartbeats in stalk_zero_of_ses_g_iso, cokernel_stalk_zero_V

---
## Previous Status Summary

- **Sorry count**: 1 (`IrreduciblePosVanishing` at Setup.lean:95)
- **Files**: 13 in `main/`
- **CI**: Fix committed (029fae5), run 23713895270 in-progress
- **Aristotle API**: was returning 500/502; 3 jobs submitted, status unknown

## Priority Actions (This Cycle)

### 1. (P0) Verify CI passes on 029fae5
**Action**: Check CI run 23713895270 result.
**Step**: `/critique`

### 2. (P1) Check Aristotle jobs + attempt IrreduciblePosVanishing
**Step**: `/check-aristotle` + `/prove`

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
