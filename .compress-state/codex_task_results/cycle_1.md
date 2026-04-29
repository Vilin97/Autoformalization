# Cycle 1 Report

## What Was Done

- Replaced the successor connecting isomorphism cluster in
  `Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean` with bundled
  `ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)` arguments.
- Updated the direct callers in
  `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean` and
  `Aristotle/GrothendieckVanishing/main/ClosedImmersionCohomology.lean` to pass
  existing bundled short complexes and short-exact proofs.

## What Changed

- Renamed and rewrote:
  - `sheafH_extClassAddEquiv_of_subsingleton_middle_presheaf` to
    `sheafH_extClassAddEquiv_of_subsingleton_middle` (private).
  - `sheafH_extClassAddEquiv_of_subsingleton_middle_presheaf_apply` to
    `sheafH_extClassAddEquiv_of_subsingleton_middle_apply` (private).
  - `sheafH_succ_iso_of_subsingleton_middle_presheaf` to
    `sheafH_succ_iso_of_subsingleton_middle`.
  - `sheafH_succ_iso_of_subsingleton_middle_presheaf_hom_apply` to
    `sheafH_succ_iso_of_subsingleton_middle_hom_apply` (private).
  - `sheafH_succ_iso_of_subsingleton_middle_presheaf_natural` to
    `sheafH_succ_iso_of_subsingleton_middle_natural`.
- Deleted same-cluster single-use/unused wrappers:
  - `sheafH_succ_map_presheaf_eq_succ_iso_hom`
  - `sheafH_exists_preimage_of_subsingleton_middle_presheaf`
- Removed repeated reconstructed presheaf zero proofs at the updated call sites by using
  already available bundled short complexes such as
  `sheafH_filtered_colimit_succ_stage_shortExact`,
  `sheafH_filtered_colimit_succ_shortExact`,
  `sheafH_filtered_colimit_succ_stage_map_hom`, and
  `sheafH_filtered_colimit_succ_stage_hom`.

## Verification Performed

- `lake env lean Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/ClosedImmersionCohomology.lean`
- `lake build`

All completed successfully. `lake build` emitted existing linter warnings in unrelated
files and in unchanged parts of `PresheafFilteredColimitCore.lean`.

## Normalized LOC

- Before: `7016`
- After: `6666`
- Delta: `-350`

Changed-file normalized deltas:

- `CohomologyAPI.lean`: `1515 -> 1362` (`-153`)
- `PresheafFilteredColimitCore.lean`: `985 -> 794` (`-191`)
- `ClosedImmersionCohomology.lean`: `151 -> 145` (`-6`)

## Raw `wc -l` For `main/*.lean`

- Before total: `8127`
- After total: `7763`
- Delta: `-364`

Changed-file raw deltas:

- `CohomologyAPI.lean`: `1776 -> 1609` (`-167`)
- `PresheafFilteredColimitCore.lean`: `1110 -> 919` (`-191`)
- `ClosedImmersionCohomology.lean`: `180 -> 174` (`-6`)

## What Remains

- `CohomologyAPI.lean` is still above the checklist threshold (`1609` raw lines,
  not yet `< 1200`).
- Earlier presheaf-boundary naturality and successor-map wrappers still use the
  `(F : Presheaf X) (hF : F.IsSheaf)` style and are candidates for later Phase 1
  sheaf-reversion cycles.
