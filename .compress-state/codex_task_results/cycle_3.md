# Cycle 3 Report

## What was done

- Reverted the `FlasqueVanishing.lean` short-complex/flasque-vanishing cluster from presheaf plus `IsSheaf` packaging to bundled `TopCat.Sheaf` arguments.
- Updated the direct call sites in `PresheafFilteredColimitCore.lean`, `PresheafFilteredColimit.lean`, `IrreducibleStep.lean`, and `GrothendieckVanishing.lean`.

## What changed

- Deleted `sheafShortComplexOfPresheaf`, `sheafShortComplexOfPresheaf_f_val`, `sheafShortComplexOfPresheaf_g_val`, and `sheafShortComplexOfPresheaf_shortExact_of_shortExact`.
- Replaced `sections_exact_of_shortExact_presheaf` with sheaf-level `sections_exact_of_shortExact`.
- Replaced `epi_app_of_shortExact_of_epi_restrictions_presheaf` with `epi_app_of_shortExact_of_epi_restrictions`.
- Replaced `epi_app_of_shortExact_flasque_presheaf` with `epi_app_of_shortExact_flasque`.
- Replaced `isFlasque_X₃_of_shortExact_presheaf` with `isFlasque_X₃_of_shortExact`.
- Replaced `sheafH_subsingleton_H1_of_flasque_presheaf` with `sheafH_subsingleton_H1_of_flasque`.
- Replaced `sheafH_subsingleton_of_flasque_presheaf` with `sheafH_subsingleton_of_flasque`.
- Simplified the `FlasqueVanishing` instance to call the bundled sheaf theorem directly.
- Removed local presheaf rebundling at the external call sites that already had bundled sheaves.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`
- `lake build`

The colimit file checks still emit existing lint warnings, but no errors.

## Metrics

- Normalized LOC before: 6165
- Normalized LOC after: 6062
- Normalized LOC delta: -103
- Raw `wc -l` of `main/*.lean` before: 7235
- Raw `wc -l` of `main/*.lean` after: 7120
- Raw `wc -l` delta: -115

## What remains

- The global raw `main/*.lean` count is still above the later 6500 target.
- Remaining Phase 1 work is outside this cycle's scope: additional presheaf-boundary sheaf reversion in the filtered-colimit and closed-immersion files.
