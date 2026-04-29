# Cycle 9 Results

## What was done

Reverted the cokernel stalk-zero cluster in `CohomologyAPI.lean` from presheaf-plus-`IsSheaf` arguments to bundled sheaf arguments, then updated the two direct callers in `IrreducibleStep.lean`.

## What changed

- Renamed and sheaf-reverted `stalk_zero_of_g_is_cokernel_of_stalk_epi_presheaf` to `stalk_zero_of_g_is_cokernel_of_stalk_epi`.
- The new theorem takes `{S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}` and an `IsColimit (CokernelCofork.ofπ S.g S.zero)` directly.
- Reworked `cokernel_stalk_zero_of_stalk_surj` to take bundled sheaves `{F G : TopCat.Sheaf ...}` and a bundled morphism `f : F -> G`.
- Deleted unused declaration `stalk_zero_of_shortExact_cokernel_presheaf`.
- Updated the two `IrreducibleStep.lean` callers to pass bundled sheaf morphisms directly.

## Verification

- `rg` before edits showed the deleted short-exact wrapper was definition-only and `cokernel_stalk_zero_of_stalk_surj` had the two expected callers.
- `lake env lean Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`
- `lake build Aristotle.GrothendieckVanishing.main.CohomologyAPI`
- `lake env lean Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`
- `lake build Aristotle.GrothendieckVanishing.main.IrreducibleStep`
- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`
- `lake build`
- `rg -n "^[[:space:]]*(sorry|admit|axiom)\\b|:= by[[:space:]]*(sorry|admit)\\b" Aristotle/GrothendieckVanishing/main || true` returned no results.
- Post-edit `rg` confirms `stalk_zero_of_shortExact_cokernel_presheaf` and `stalk_zero_of_g_is_cokernel_of_stalk_epi_presheaf` are gone.

## LOC

- Normalized LOC before: 5708
- Normalized LOC after: 5632
- Normalized LOC delta: -76
- Raw `wc -l` of `main/*.lean` before: 6735
- Raw `wc -l` of `main/*.lean` after: 6654
- Raw delta: -81

## What remains

The broad Phase-1 target is not complete: raw `main/*.lean` is now 6654, still above the 6500 checklist threshold. Further sheaf reversion in the remaining presheaf-boundary APIs is still needed.
