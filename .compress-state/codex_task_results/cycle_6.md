# Cycle 6 Report

## What Was Done

- Reverted the closed-immersion API cluster from presheaf-plus-`IsSheaf` arguments to bundled sheaf arguments.
- Removed obsolete `_presheaf` public names in the closed-inclusion counit and closed-immersion cohomology step.
- Updated the direct downstream call sites in `IrreducibleStep.lean` and `GrothendieckVanishing.lean` to reuse existing bundled sheaves.
- Removed two local `S.X₁` sheaf repackaging blocks and shortened the `PushforwardHIso` induction setup.

## What Changed

- Renamed/de-presheafed:
  - `closedIncl_counit_isIso_presheaf` -> `closedIncl_counit_isIso`
  - `subsingleton_sheafH_of_closedImmersion_middle_presheaf` -> `subsingleton_sheafH_of_closedImmersion_middle`
- Changed to bundled sheaf arguments:
  - `closedIncl_counit_isIso`
  - `closedIncl_unit_stalk_isIso`
  - `epi_unit_of_closedImmersion`
  - `closedImmersionSES`
  - `closedImmersionSES_shortExact`
  - `PushforwardHIso`
  - `subsingleton_sheafH_of_closedImmersion_middle`
- Updated affected call sites in:
  - `IrreducibleStep.lean`
  - `GrothendieckVanishing.lean`

## Verification

- `lake env lean Aristotle/GrothendieckVanishing/main/ClosedImmersion.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/ClosedImmersionCohomology.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`
- `lake build`
- Lean LSP: `lean_goal` confirmed the simplified `IsZero S.X₁` proof in `IrreducibleStep.lean` closes directly.
- `rg -n "^\\s*(sorry|admit|axiom)\\b" Aristotle/GrothendieckVanishing/main` found no proof placeholders or axioms.
- Stale-name scan found no remaining scoped uses of the removed `_presheaf` names.

## LOC

- Normalized LOC before: 5945
- Normalized LOC after: 5927
- Normalized delta: -18
- Raw `main/*.lean` wc before: 6989
- Raw `main/*.lean` wc after: 6972
- Raw delta: -17

## What Remains

- The broader Phase-1 raw target of `<6500` for all `main/*.lean` remains open.
- Remaining presheaf-plus-`IsSheaf` APIs in the pushforward exactness and filtered-colimit areas are outside this cycle's closed-immersion cohomology scope.
