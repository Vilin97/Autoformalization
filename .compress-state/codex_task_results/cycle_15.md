# Cycle 15 Results

## What was done

- Verified `sheafCohomologyFunctor_map_succ_of_map_eq_presheaf` was already absent from `Aristotle/GrothendieckVanishing/main`.
- Deleted unused public API from `CohomologyAPI.lean`.
- Updated the two downstream simp call sites to unfold `sheafCohomologyFunctor` directly.

## What changed

- Deleted `sheafH_subsingleton_of_isEmpty`.
- Kept `sheafH_subsingleton_of_isEmpty_presheaf`; `GrothendieckVanishing.lean` still uses it.
- Deleted `sheafCohomologyFunctor_obj`.
- Replaced `sheafCohomologyFunctor_obj` with `sheafCohomologyFunctor` in:
  - `FinitelyGeneratedVanishing.lean`
  - `ClosedImmersionCohomology.lean`

## Verification performed

- `rg -n "sheafCohomologyFunctor_map_succ_of_map_eq_presheaf|sheafCohomologyFunctor_obj|sheafH_subsingleton_of_isEmpty\\b" Aristotle/GrothendieckVanishing/main`
  - No matches.
- `lake env lean Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/ClosedImmersionCohomology.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`
- `lake build`
  - Passed. It emitted existing unrelated linter warnings in other files.

## Metrics

- Normalized LOC before: `5234`
- Normalized LOC after: `5225`
- Normalized LOC delta: `-9`
- Raw `wc -l` total for `Aristotle/GrothendieckVanishing/main/*.lean` before: `6202`
- Raw `wc -l` total for `Aristotle/GrothendieckVanishing/main/*.lean` after: `6187`
- Raw `wc -l` delta: `-15`

## What remains

- No blocker from this cycle.
- The deleted names are no longer referenced in `Aristotle/GrothendieckVanishing/main`.
