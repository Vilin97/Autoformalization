## What was done

Golfed `_root_.isZero_zeroOutsideInt_bot` in
`Aristotle/GrothendieckVanishing/main/ZeroOutside.lean`.

## What changed

- Replaced the local duplicate zero-stalks-to-zero-sheaf construction with the
  existing `sheaf_isZero_of_zero_stalks` lemma.
- Swapped the import from `ClosedImmersion` to `CohomologyAPI`, which already
  imports `ClosedImmersion` and provides `sheaf_isZero_of_zero_stalks`.
- No declarations were renamed, deleted, or newly introduced.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/ZeroOutside.lean`
- `lake build`

Both completed successfully. The build reported existing linter warnings in
several files, including pre-existing warnings in `ZeroOutside.lean`, but no
errors.

## Normalized LOC

- Before: `4145`
- After: `4125`
- Delta: `-20`

Command used:
`python3.9 scripts/normalized_loc.py --per-file --raw`

## Raw `wc -l` of `main/*.lean`

- Before total: `5054`
- After total: `5034`
- Delta: `-20`

`ZeroOutside.lean` changed from `448` raw lines to `428` raw lines.

## What remains

Nothing remains for this scoped cycle item.
