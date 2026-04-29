## What Was Done

Golfed `sheafH_filtered_colimit_comparison_one_iso_hom` in
`Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`.

## What Changed

- Removed the local `simpa` wrapper around `mapIso`; the boundary square now supplies the
  `cokernel.mapIso` compatibility term directly.
- Removed the local `simpa` wrapper around `globalIso`; the global cokernel iso has the needed
  aliased type directly.
- Replaced the explicit `change` of the comparison iso hom with
  `dsimp [sheafH_filtered_colimit_comparison_one_iso]`.
- Let the `stageCokMap` commutativity proof use `congrArg ... stageHom.comm₂₃.symm` directly.
- Let `hnat` use `sheafH1_cokernel_iso_of_subsingleton_middle_natural` directly instead of a
  `simpa` over the local aliases.
- Moved the terminal cokernel cancellation calculation into a named local equality `hstage`,
  then used that equality in the final `simpa`.

No declarations were renamed, deleted, or added.

## Verification Performed

- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
- `python3.9 scripts/normalized_loc.py --per-file --raw`
- `wc -l Aristotle/GrothendieckVanishing/main/*.lean`

`lake build` was not run because the change stayed inside one proof body and did not rename,
delete, add imports, or change a `@[simp]` theorem statement.

## Normalized LOC

- Before: 4425 total, 516 in `PresheafFilteredColimit.lean`
- After: 4413 total, 504 in `PresheafFilteredColimit.lean`
- Delta: -12 total, -12 in `PresheafFilteredColimit.lean`

## Raw `wc -l` of `main/*.lean`

- Before: 5322 total, 558 in `PresheafFilteredColimit.lean`
- After: 5310 total, 546 in `PresheafFilteredColimit.lean`
- Delta: -12 total, -12 in `PresheafFilteredColimit.lean`

## What Remains

The proof still has unavoidable categorical bookkeeping around `hstage`, especially the
`PreservesCokernel.π_iso_hom` conversion and the final cokernel cancellation. Further shortening
would likely need a reusable existing lemma or a broader refactor outside this cycle's scope.
