# Cycle 26

## What was done

- Merged the finite-generator transition API out of `ZeroOutsideFinset.lean` into `GeneratedSubsheaf.lean`.
- Updated `FinitelyGeneratedVanishing.lean` to import `GeneratedSubsheaf.lean` directly.
- Removed the stale `ZeroOutsideFinset` import from `GrothendieckVanishingOverview.lean`.
- Deleted `Aristotle/GrothendieckVanishing/main/ZeroOutsideFinset.lean`.

## What changed

- Moved, without renaming:
  - `TopCat.Presheaf.finsetCoproductInclGen`
  - `TopCat.Presheaf.finsetImageInclGen`
  - `TopCat.Presheaf.finsetImageInclGen_comp_ι`
  - `TopCat.Presheaf.finsetImageInclGen_mono`
- Deleted the standalone `ZeroOutsideFinset.lean` module boilerplate/import layer.
- No theorem statements or call sites were changed by this cycle beyond the import updates.
- Pre-existing working-tree edits in touched files were left as-is.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/GeneratedSubsheaf.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishingOverview.lean`
- `lake build`
- `rg "\\b(sorry|admit|axiom)\\b" Aristotle --glob '*.lean'` only reported existing comment text.

## Normalized LOC

- Before: 4956
- After: 4946
- Delta: -10

## Raw `wc -l` for `main/*.lean`

- Before: 5847
- After: 5822
- Delta: -25

## What remains

- The structural file-deletion item is complete. Remaining compress-loop work is outside this cycle's scope.
