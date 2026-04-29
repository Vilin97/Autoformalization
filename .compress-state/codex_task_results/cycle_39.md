## What was done

Golfed `sheafH_filtered_colimit_comparison_one_iso_hom` in
`Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`.

## What changed

- Replaced the `comparisonOne` staging alias with a direct `change`.
- Removed the proof-local `stageShort`, `stageIsoH1`, and `stageHom` aliases by using
  the corresponding `stageIso` component and stage lemmas directly.
- Inlined the one-use `hstage_cok` proof into the final `congrArg`.
- Folded the one-use `hfunctorCok` rewrite into the cokernel rewrite chain.
- Converted the local `hInj` and `h_mid` `intro` blocks in the target theorem to
  parameterized local facts.

No declarations were renamed or deleted, and no public API changed.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`

`lake build` was not run; this cycle only changed one proof body.

## Normalized LOC

- Before: `4700`
- After: `4682`
- Delta: `-18`

## Raw `wc -l` of `main/*.lean`

- Before: `5581`
- After: `5563`
- Delta: `-18`

## What remains

Nothing known for this cycle. Further compression would need a new target or a
separate pass over remaining long proofs.
