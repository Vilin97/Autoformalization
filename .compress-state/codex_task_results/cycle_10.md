# Cycle 10 Results

## What was done

Completed the filtered-colimit Phase-1 sheafification in `PresheafFilteredColimitCore.lean`
and `PresheafFilteredColimit.lean`. The public comparison API and its private induction
proofs now work directly with bundled sheaf diagrams and sheaf cocones.

## What changed

- Renamed and sheafified:
  - `sheafH_filtered_colimit_succ_inj_subsingleton_presheaf` to
    `sheafH_filtered_colimit_succ_inj_subsingleton`.
  - `sheafH_filtered_colimit_surj_presheaf` to `sheafH_filtered_colimit_surj`.
  - `sheafH_filtered_colimit_comparison_succ_compatibility_presheaf` to the sheaf-level
    `sheafH_filtered_colimit_comparison_succ_compatibility`.
- Made `sheafH_filtered_colimit_comparison` primary at the sheaf level, defined directly
  by `colimit.desc`.
- Deleted the presheaf boundary shims:
  - `sheafH_filtered_colimit_presheafDiagram`
  - `sheafH_filtered_colimit_presheafCocone`
  - `sheafH_filtered_colimit_presheafDiagram_sheafToPresheaf`
  - `sheafH_filtered_colimit_presheafCocone_sheafToPresheaf`
  - `sheafH_presheafDiagram`
  - `sheafH_presheafDiagram_sheafToPresheaf`
  - `sheafH_filtered_colimit_comparison_presheaf`
  - `colimit_ι_sheafH_filtered_colimit_comparison_presheaf`
  - `sheafH_filtered_colimit_comparison_sheafToPresheaf`
  - `sheafH_filtered_colimit_presheafCocone_isColimit`
- Reworked the degree `0`, degree `1`, and successor-step comparison-isomorphism proofs
  in `PresheafFilteredColimit.lean` to prove `IsIso` for `sheafH_filtered_colimit_comparison`
  directly.
- Updated the stale module note in `FinitelyGeneratedVanishing.lean`.

## Verification

- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`
- `lake build Aristotle.GrothendieckVanishing.main.PresheafFilteredColimitCore`
- `lake build Aristotle.GrothendieckVanishing.main.PresheafFilteredColimit`
- `lake build`
- `rg -n "^[[:space:]]*(sorry|admit|axiom)\\b|:= by[[:space:]]*(sorry|admit)\\b" Aristotle/GrothendieckVanishing/main || true`
  returned no results.
- Old filtered-colimit presheaf-boundary shim names no longer occur under
  `Aristotle/GrothendieckVanishing/main`.

## LOC

- Normalized LOC: `5632` before, `5295` after, delta `-337`.
- Raw `normalized_loc.py --raw` total: `6654` before, `6275` after, delta `-379`.
- Raw `wc -l Aristotle/GrothendieckVanishing/main/*.lean`: `6654` before, `6275` after,
  delta `-379`.

## What remains

The Phase-1 target for this cycle is met: raw `main/*.lean` LOC is below `6500`.
Further sheaf reversion remains possible in other files, but this cycle stayed scoped to
the filtered-colimit boundary layer.
