# Cycle 86

## What was done

Golfed `toPlus_surjective_of_firstPlus` in
`Aristotle/GrothendieckVanishing/main/ConstantSheafFlasque.lean`.

## What changed

- Collapsed the one-use local `hkey` proof into the nonempty branch by proving the
  reversed goal directly after `symm`.
- Inlined the one-use local `R` relation and `hZne` nonempty proof into the
  `x.condition` / `toPlus_injective_of_const` path.
- Combined the adjacent rewrite steps through `toPlus_naturality_const`.
- Folded the empty-open branch's `Set.not_nonempty_iff_eq_empty` rewrite into the
  `Opens.ext` proof.
- No declarations were renamed, deleted, or added.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/ConstantSheafFlasque.lean`
- `python3.9 scripts/normalized_loc.py --per-file --raw` before and after
- `wc -l Aristotle/GrothendieckVanishing/main/*.lean` before and after
- `lake build` was not run because only a local proof body changed.

## Normalized LOC

- Before: 4097 total normalized LOC
- After: 4087 total normalized LOC
- Delta: -10

`ConstantSheafFlasque.lean` normalized LOC went from 173 to 163.

## Raw main LOC

- Before: 5008 raw lines across `Aristotle/GrothendieckVanishing/main/*.lean`
- After: 4998 raw lines across `Aristotle/GrothendieckVanishing/main/*.lean`
- Delta: -10

`ConstantSheafFlasque.lean` raw `wc -l` went from 184 to 174.

## What remains

Nothing remains for the scoped cycle target.
