## What was done

Golfed the proof body of `sheafH_filtered_colimit_comparison_one_iso_hom` in
`Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`.

## What changed

- Inlined local setup helpers `sectionsColimit`, `sectionIso`, `Sh`, and `stageIso`.
- Removed redundant named arguments in the `h_colim`, `mapIso`, `globalIso`, boundary-square, and `PreservesCokernel.iso` calls.
- Shortened the `hπ` subproof by using the `Iso.comp_inv_eq` proof term directly.
- No declarations were renamed, deleted, or added in Lean.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
- `lake build` was not run; this was a proof-body-only change with no file/import/declaration deletion.

## Normalized LOC

- Before: `4338`
- After: `4328`
- Delta: `-10`

## Raw `wc -l` of `main/*.lean`

- Before: `5239`
- After: `5229`
- Delta: `-10`

## What remains

The theorem still has a nontrivial cokernel comparison calculation around `hstage`; further shrink would likely need a reusable existing lemma or a cleaner Mathlib rewrite path for that cokernel square.
