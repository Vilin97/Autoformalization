# Cycle 2 Report

## What Was Done

- Reverted the remaining successor-map API cluster in `CohomologyAPI.lean` from presheaf/sheafness triples to bundled short exact complexes of sheaves.
- Reverted the `H¹` cokernel isomorphism and naturality cluster to bundled `ShortComplex (TopCat.Sheaf AddCommGrpCat X)` arguments.
- Updated direct callers in:
  - `PresheafFilteredColimitCore.lean`
  - `PresheafFilteredColimit.lean`
  - `ClosedImmersionCohomology.lean`
- Extended the same sheaf-level reversion to the adjacent `H¹` top-sections vanishing cluster and one direct dimension-shift wrapper to bring `CohomologyAPI.lean` below the requested raw-line gate.
- Updated `FlasqueVanishing.lean` callers of the deleted `H¹` top-sections wrappers.

## What Changed

- Renamed/replaced:
  - `sheafH_succ_map_presheaf` -> `sheafH_succ_map`
  - `sheafH_succ_map_presheaf_apply` -> `sheafH_succ_map_apply`
  - `sheafH_succ_map_exists_preimage_of_subsingleton_middle_presheaf` -> `sheafH_succ_map_exists_preimage_of_subsingleton_middle`
  - `sheafH_succ_map_presheaf_natural_of_map_eq` -> `sheafH_succ_map_natural_of_map_eq`
  - `sheafH1_cokernel_iso_of_subsingleton_middle_presheaf` -> `sheafH1_cokernel_iso_of_subsingleton_middle`
  - `sheafH1_cokernel_iso_of_subsingleton_middle_presheaf_hom_π` -> `sheafH1_cokernel_iso_of_subsingleton_middle_hom_π`
  - `sheafH1_cokernel_iso_of_subsingleton_middle_presheaf_natural` -> `sheafH1_cokernel_iso_of_subsingleton_middle_natural`
  - `epi_app_top_of_subsingleton_sheafH1_presheaf` -> `epi_app_top_of_subsingleton_sheafH1`
  - `sheafH0_surj_of_epi_app_top_presheaf` -> `sheafH0_surj_of_epi_app_top`
  - `sheafH_subsingleton_H1_via_surj_presheaf` -> `sheafH_subsingleton_H1_via_surj`
  - `sheafH_subsingleton_H1_via_epi_app_top_presheaf` -> `sheafH_subsingleton_H1_via_epi_app_top`
  - `sheafH_subsingleton_H1_of_injective_of_epi_app_top_presheaf` -> `sheafH_subsingleton_H1_of_injective_of_epi_app_top`
  - `sheafH_dimension_shift_of_both_presheaf` -> `sheafH_dimension_shift_of_both`
- Deleted the now-duplicate presheaf wrappers rather than leaving compatibility shims.
- Deleted single-use presheaf naturality plumbing:
  - `sheafCohomologyFunctor_map_extClass_naturality_presheaf`
  - `sheafCohomologyFunctor_map_succ_of_map_eq_presheaf`
- Call sites now pass existing `ShortComplex` values, short exact proofs, and `ShortComplex.Hom`s directly instead of rebuilding `Sheaf.Hom.mk`, `.cond`, `.val`, and component commutativity proofs.

## Verification Performed

- `lake env lean Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/ClosedImmersionCohomology.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean`
- `lake build`
- Checked for actual `sorry` / `admit` / `axiom` declarations with `rg`; none found.

The filtered-colimit files still emit existing linter warnings, but all checks and the full build passed.

## LOC

- Normalized LOC before: `6666`
- Normalized LOC after: `6165`
- Normalized delta: `-501`

- Raw `wc -l Aristotle/GrothendieckVanishing/main/*.lean` before: `7763`
- Raw `wc -l Aristotle/GrothendieckVanishing/main/*.lean` after: `7235`
- Raw delta: `-528`

- `CohomologyAPI.lean` raw before: `1609`
- `CohomologyAPI.lean` raw after: `1193`
- `CohomologyAPI.lean` normalized before: `1362`
- `CohomologyAPI.lean` normalized after: `973`

## What Remains

- Several dimension-shift and stalk/vanishing APIs still use presheaf/sheafness triples where a bundled sheaf or short complex should suffice.
- The filtered-colimit files retain unrelated linter warnings that predate this cycle.
