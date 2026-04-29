## What was done

Golfed `sheafH_filtered_colimit_comparison_one_iso_hom` in
`Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`.

## What changed

- No declarations were renamed or deleted.
- Added local abbreviations inside the proof for the sheaf category, preserved
  section colimits, section colimit isomorphisms, top evaluation of sheaf
  morphisms, and the cokernel functor isomorphism.
- Replaced the duplicated `isColimitOfPreserves evTop (isColimitOfPreserves
  toPsh ...)` setup for the injective and quotient diagrams with one local
  `sectionsColimit`.
- Replaced duplicated `coconePointUniqueUpToIso` plumbing with one local
  `sectionIso`.
- Tightened the `stageCokMap`, `hnat`, and `hstage` blocks, including naming
  the cokernel projection rewrite as `hπ` instead of using an inline `show`.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
- `python3.9 scripts/normalized_loc.py --per-file --raw` before and after
- `wc -l Aristotle/GrothendieckVanishing/main/*.lean` before and after
- `lake build` was not run; this was a proof-only edit in one existing file.

## Normalized LOC

- Before: `4387`
- After: `4375`
- Delta: `-12`

## Raw `main/*.lean` wc -l

- Before: `5284`
- After: `5272`
- Delta: `-12`

## What remains

No blocker remains for this cycle. Further compression in this proof would
likely require a broader refactor of the colimit/cokernel comparison setup.
