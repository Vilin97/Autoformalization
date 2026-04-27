# Cycle 7 Report

## What Was Done

- Reverted the CohomologyAPI dimension-shift wrapper cluster from presheaf-plus-`IsSheaf`
  packaging to bundled `TopCat.Sheaf` arguments.
- Updated the active call sites in `FlasqueVanishing.lean` and `IrreducibleStep.lean`
  to pass bundled short complexes and sheaf morphisms directly.
- Deleted the unused reverse injective dimension-shift declaration requested by the cycle.

## What Changed

- Replaced `sheafH_dimension_shift_of_mono_presheaf` with
  `sheafH_dimension_shift_of_mono`, taking `{F G : TopCat.Sheaf ... X}` and
  `(f : F ⟶ G)` directly.
- Replaced `sheafH_dimension_shift_presheaf` with
  `sheafH_dimension_shift_of_injective`, taking `{S : ShortComplex (TopCat.Sheaf ... X)}`
  and `S.ShortExact` directly.
- Replaced `sheafH_dimension_shift_X₃_of_locallySurjective_presheaf` with
  `sheafH_dimension_shift_X₃_of_locallySurjective`, taking a sheaf morphism directly.
- Deleted `sheafH_dimension_shift_X₃_presheaf`.
- Deleted the now-single-use wrapper `sheafH_dimension_shift_X₃_of_both_presheaf` by
  calling `ext_dimension_shift_X₃` directly inside the locally-surjective theorem.
- Removed the local presheaf-mono conversion in `zeroOutsideInt_vanishing`.
- Removed the redundant bundled-injective instance in `sheafH_subsingleton_of_flasque`.

## Verification Performed

- `lake env lean Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`
- `lake build Aristotle.GrothendieckVanishing.main.CohomologyAPI`
- `lake build`
- `rg` confirmed the old `_presheaf` dimension-shift names are gone from `main`.
- Lean LSP `lean_goal` was used to inspect the new mono dimension-shift proof state.

## LOC

- Normalized LOC before: `5927`
- Normalized LOC after: `5779`
- Normalized LOC delta: `-148`
- Raw `wc -l` of `main/*.lean` before: `6972`
- Raw `wc -l` of `main/*.lean` after: `6809`
- Raw delta: `-163`

## What Remains

- The broader Phase-1 tree-wide target of raw `main/*.lean` below `6500` is not complete;
  this cycle stayed within the requested dimension-shift cluster scope.
