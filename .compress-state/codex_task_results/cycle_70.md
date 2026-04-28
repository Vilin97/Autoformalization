## What was done

Golfed `closedIncl_unit_stalk_isIso` in
`Aristotle/GrothendieckVanishing/main/ClosedImmersion.lean`.

## What changed

- Added proof-local aliases for the closed inclusion and presheaf pullback.
- Replaced the long `presheafToSheaf ... .map ... .val` occurrences with
  Mathlib's `sheafifyMap`.
- Collapsed the stalk naturality rewrite into a single local `hnat_stalk`.
- Replaced the two `toSheafify` stalk-isomorphism instances for `P1` and `P2`
  with one local instance family.
- No declarations were renamed, deleted, or added.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/ClosedImmersion.lean`
- `lake build` was not run; this was a proof-body-only golf with no import,
  rename, deletion, or attribute change.

## Normalized LOC

- Before: 4260
- After: 4252
- Delta: -8

## Raw `wc -l` for `main/*.lean`

- Before: 5162
- After: 5154
- Delta: -8

## What remains

No blocker. Further compression in this proof would likely need a stronger
stalk/sheafification helper or a reusable Mathlib lemma; the remaining local
`IsIso` instance plumbing was tested and is still needed by typeclass search.
