# Cycle 21

## What was done

Deleted the unused sheaf-level successor connecting morphism naturality theorem from
`Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`.

## What changed

- Deleted public theorem `sheafH_succ_map_natural_of_map_eq`.
- Removed its entry from the `CohomologyAPI.lean` module result list so the stale name no longer appears.
- No declarations were renamed, inlined, or golfed.

## Verification performed

- `rg "sheafH_succ_map_natural_of_map_eq" Aristotle/GrothendieckVanishing/main`
  returned no matches.
- `lake env lean Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`
  passed.
- `lake build` passed.

## Normalized LOC

- Before: 5027
- After: 5014
- Delta: -13

## Raw `wc -l` of `main/*.lean`

- Before: 5939
- After: 5920
- Delta: -19

## What remains

No blocker from this cycle. Remaining compression work is outside this scoped
unused-declaration deletion.
