## What was done

Golfed the proof body of `sheafH_filtered_colimit_comparison_one_iso_hom` in
`Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`.

## What changed

- Kept the naturality equality local to the proof but shortened its target with an inferred
  stage-isomorphism factor.
- Inlined the single-use `hstage` equality into the final `congrArg`.
- Inlined the single-use cokernel `π` equality into the `rw` list inside that proof.
- No declarations were renamed, deleted, or added.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
- `python3.9 scripts/normalized_loc.py --per-file --raw` before and after
- `wc -l Aristotle/GrothendieckVanishing/main/*.lean` before and after
- `rg -n --glob '*.lean' "\\bsorry\\b|\\badmit\\b|\\baxiom\\b" Aristotle`
  only found existing doc/comment mentions.

`lake build` was not run because this cycle only changed one proof body and did not add,
delete, rename, or retag Lean declarations.

## Normalized LOC

- Before: `4291` total normalized LOC
- After: `4284` total normalized LOC
- Delta: `-7`

`PresheafFilteredColimit.lean` moved from `482` to `475` normalized LOC.

## Raw `wc -l` of `main/*.lean`

- Before: `5193`
- After: `5186`
- Delta: `-7`

`PresheafFilteredColimit.lean` moved from `524` to `517` raw lines.

## What remains

The proof still needs the local `stageCokMap` and `globalIso` names plus the explicit
`h_colim` setup; a larger reduction likely needs a different structural helper or a
stronger cokernel-preservation rewrite lemma, not another local proof-only golf.
