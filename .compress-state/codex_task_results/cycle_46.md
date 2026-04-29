# Cycle 46

## What was done

Golfed `finsetGenCocone_isColimit` in
`Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean`.

## What changed

- Reused `(finsetGenCocone hK).ι` in the mono proof instead of rebuilding the
  same natural transformation as a local `α`.
- Removed the now-unused bundled sheaf local `Ksh`.
- Replaced the explicit `change`/`rw [Limits.image.fac]` factorization block in
  `hfac` with `ext σ` and one `simp` over the cocone and generator maps.
- Kept the final mono+epi-to-iso argument, but split the instance setup without
  tactic stacking.

No declarations were renamed, deleted, or added.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean`

`lake build` was not run because this cycle only changed one proof body.

## Normalized LOC

- Before: `4546`
- After: `4533`
- Delta: `-13`

## Raw `wc -l` of `main/*.lean`

- Before: `5436`
- After: `5426`
- Delta: `-10`

## What remains

Nothing remains for the scoped target. Further compression would need a separate
pass over another proof or structural item.
