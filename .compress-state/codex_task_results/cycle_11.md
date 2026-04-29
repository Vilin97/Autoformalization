# Cycle 11 Results

## What was done
- Deleted two unused public declarations from `Aristotle/GrothendieckVanishing/main/ClosedImmersion.lean`.
- Left `set_range_closedIncl` in place because it is still used by `closedIncl_map_eq_bot_of_le_compl`.

## What changed
- Deleted `TopCat.coe_closedIncl`.
- Deleted `TopCat.closedIncl_image_map_eq_inter`.
- No declarations were renamed, inlined, or golfed.

## Verification performed
- `rg -n "coe_closedIncl|closedIncl_image_map_eq_inter" Aristotle/GrothendieckVanishing/main`
  returned no matches.
- `lake env lean Aristotle/GrothendieckVanishing/main/ClosedImmersion.lean`
  passed.
- `lake build` passed.

## Normalized LOC
- Before: 5295
- After: 5286
- Delta: -9

## Raw `wc -l` for `main/*.lean`
- Before: 6275
- After: 6264
- Delta: -11

## What remains
- Nothing remains for this cycle's scoped checklist items.
