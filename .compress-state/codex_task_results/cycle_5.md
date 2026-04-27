# Cycle 5 Report

## What Was Done

- Reverted the filtered-colimit flasque API from a presheaf diagram plus stage/point sheaf proofs to a bundled sheaf diagram:
  `isFlasque_filtered_colimit_presheaf` -> `isFlasque_filtered_colimit`.
- Updated both flasque-colimit call sites to pass `F := Inj`, `c := injCocone`, and `hc := colimit.isColimit Inj` directly.
- Reverted the public filtered-colimit cohomology endpoint from presheaf packaging to bundled sheaves:
  `sheafH_preserves_filtered_colimits_presheaf` -> `sheafH_preserves_filtered_colimits`.
- Updated `cohomology_vanishing_of_finitelyGenerated_vanishing` to call the bundled endpoint directly on `finsetGenFunctor hK`.
- Deleted unused declaration `sheafH_preserves_filtered_colimits_presheaf_hom_epi`.

## What Changed

- Renamed/de-presheafed:
  - `isFlasque_filtered_colimit_presheaf`
  - `sheafH_preserves_filtered_colimits_presheaf`
- Deleted:
  - `sheafH_preserves_filtered_colimits_presheaf_hom_epi`
- Removed call-site scaffolding:
  - explicit `CreatesColimit Inj` blocks around flasque-colimit calls
  - explicit `sheafToPresheaf.mapCocone` / `isColimitOfPreserves` / `hY` / `hc_pt` argument blocks at the updated public endpoint caller

## Verification

- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean`
- `lake build`
- Confirmed the deleted epi wrapper is absent with:
  `rg -n "^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafH_preserves_filtered_colimits_presheaf_hom_epi\\b" Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`

## LOC

- Normalized LOC before: 5971
- Normalized LOC after: 5945
- Normalized delta: -26
- Raw `main/*.lean` wc before: 7020
- Raw `main/*.lean` wc after: 6989
- Raw delta: -31

## What Remains

- The broader Phase-1 raw target of `<6500` for all `main/*.lean` remains open; this cycle stayed within the scoped filtered-colimit API changes and did not touch the broader `ClosedImmersion*` / `IrreducibleStep` sheaf-reversion work.
