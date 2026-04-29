## What was done

Golfed `sheafH_filtered_colimit_comparison_one_iso_hom` in
`Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`.

## What changed

- Inlined the one-use `hc_psh_inj` and `hc_psh_q` proof locals into the section-colimit witnesses.
- Named the repeated presheaf and top-evaluation functors as local two-use aliases (`toPsh`, `evTop`).
- Removed the local `qCocone` alias from this theorem by using `stageHom.τ₂` and `stageHom.τ₃` for the stage cokernel map.
- Reused a local `stageHom` in both the stage cokernel square and the naturality comparison.
- Trimmed redundant simp inputs in the `stageCokMap` and `hnat` subproofs.
- Consolidated the terminal cokernel `rw` block so the `mapIso`/`π_desc` rewrites happen in one pass.
- No declarations were renamed, deleted, or added.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
- `lake build` was not run; the theorem statement, imports, attributes, and declaration names were unchanged.

## Normalized LOC

- Before: `4463` total normalized LOC; `PresheafFilteredColimit.lean` was `542`.
- After: `4451` total normalized LOC; `PresheafFilteredColimit.lean` is `530`.
- Delta: `-12` total normalized LOC.

## Raw `wc -l` for `main/*.lean`

- Before: `5360` total raw LOC; `PresheafFilteredColimit.lean` was `584`.
- After: `5348` total raw LOC; `PresheafFilteredColimit.lean` is `572`.
- Delta: `-12` total raw LOC.

## What remains

The proof still has a nontrivial final cokernel calculation around
`PreservesCokernel.π_iso_hom_assoc`, `cokernel.mapIso_hom`, and
`cokernel.π_desc`. I did not introduce a single-use helper for it.
