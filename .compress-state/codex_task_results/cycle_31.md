# Cycle 31

## What was done

Sheaf-reverted the empty-space cohomology vanishing theorem in
`Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`.

## What changed

- Renamed `sheafH_subsingleton_of_isEmpty_presheaf` to
  `sheafH_subsingleton_of_isEmpty`.
- Changed the theorem API from `{F : TopCat.Presheaf ... X} (hF : F.IsSheaf)` to
  `(F : TopCat.Sheaf AddCommGrpCat.{u} X)`.
- Changed the conclusion to `Subsingleton (Sheaf.H F n)`.
- Inlined the one-use zero-sheaf proof directly into
  `sheafH_subsingleton_of_isZero`.
- Updated the sole call site in `GrothendieckVanishing.lean` to pass the bundled
  sheaf `Fsh`.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`
- `lake build Aristotle.GrothendieckVanishing.main.CohomologyAPI`
- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`
- `lake build`

The full build passed. It emitted only pre-existing linter warnings in unrelated
files.

## LOC

- Normalized LOC before: `4889`
- Normalized LOC after: `4888`
- Normalized LOC delta: `-1`
- Raw `wc -l` for `main/*.lean` before: `5765`
- Raw `wc -l` for `main/*.lean` after: `5763`

## What remains

The old `_presheaf` theorem name has no remaining references in `main/*.lean`.
The audit's generated `ZeroOutside` declarations were intentionally left
untouched per the cycle scope.
