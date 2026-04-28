## What was done

- Reverted `sheafH0EquivSections_presheaf` to the bundled-sheaf definition
  `sheafH0EquivSections`.
- Updated all callers in `CohomologyAPI.lean` and `PresheafFilteredColimit.lean`
  to pass bundled sheaves instead of `.cond`.
- Reused `sheafH0NatIsoSections` in the degree-zero filtered-colimit comparison,
  replacing two duplicated `NatIso.ofComponents` blocks.

## What changed

- Renamed/deleted: `sheafH0EquivSections_presheaf` was removed and replaced by
  `sheafH0EquivSections (F : TopCat.Sheaf AddCommGrpCat.{u} X)`.
- Updated: `sheafH0EquivSections_natural` now states naturality using the
  bundled-sheaf equivalence directly.
- Updated: H1 cokernel and naturality call sites now use
  `sheafH0EquivSections S.Xᵢ`, `sheafH0EquivSections F`, etc.
- Compressed: the two local `h0Iso` definitions in
  `PresheafFilteredColimit.lean` now use
  `Functor.isoWhiskerLeft Ysh (sheafH0NatIsoSections (X := X))`.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
- `lake build`
- `rg -n "sheafH0EquivSections_presheaf" Aristotle` returned no matches.

The filtered-colimit file still reports only pre-existing linter warnings.

## Metrics

- Normalized LOC before: `4924`
- Normalized LOC after: `4914`
- Normalized LOC delta: `-10`
- Raw `wc -l` for `Aristotle/GrothendieckVanishing/main/*.lean` before: `5802`
- Raw `wc -l` for `Aristotle/GrothendieckVanishing/main/*.lean` after: `5792`
- Raw `wc -l` delta: `-10`

## What remains

- Other remaining `_presheaf` declarations were left untouched.
- Existing linter warnings in filtered-colimit and zero-outside files remain.
