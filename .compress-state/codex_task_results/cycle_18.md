# Cycle 18 Report

## What was done

Deleted the unused `TopCat.Sheaf.family*` wrapper layer from
`Aristotle/GrothendieckVanishing/main/GeneratedSubsheaf.lean`.

## What changed

Deleted declarations:

- `TopCat.Sheaf.familyImageι`
- `TopCat.Sheaf.familyImage_ι_eq`
- `TopCat.Sheaf.familyGeneratorMap`
- `TopCat.Sheaf.familyGeneratedSheaf`
- `TopCat.Sheaf.familyGeneratedSheafι`
- `TopCat.Sheaf.familyGeneratedSheaf_ι_eq`

`TopCat.Sheaf.familyMap` and `TopCat.Sheaf.familyImage` were left intact.
The module doc comment was updated to stop advertising the deleted declarations.

## Verification performed

- `rg -n '\bfamilyImageι\b|\bfamilyImage_ι_eq\b|\bfamilyGeneratorMap\b|\bfamilyGeneratedSheaf\b|\bfamilyGeneratedSheafι\b|\bfamilyGeneratedSheaf_ι_eq\b' Aristotle/GrothendieckVanishing/main`
  - Before: matches only in `GeneratedSubsheaf.lean`.
  - After: no matches.
- `lake env lean Aristotle/GrothendieckVanishing/main/GeneratedSubsheaf.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/ZeroOutsideFinset.lean`
- `lake build`

All Lean checks and the full build completed successfully.

## LOC

- Normalized LOC before: `5185`
- Normalized LOC after: `5151`
- Normalized LOC delta: `-34`
- Raw `wc -l` of `main/*.lean` before: `6127`
- Raw `wc -l` of `main/*.lean` after: `6077`
- Raw line delta: `-50`

## What remains

Nothing remains for this cycle's targeted unused declaration block.
