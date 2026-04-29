## What was done

Factored the duplicated degree-0 filtered-colimit/global-sections setup in
`Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`.

## What changed

- Added private helper `sheafH_filtered_colimit_zero_sections_iso`, packaging:
  - the `sectionsFunctor` abbreviation,
  - the `H^0`-to-sections natural isomorphism,
  - the sheaf-to-presheaf `CreatesColimit` instance,
  - the preserved presheaf colimit,
  - the evaluated global-sections `IsColimit`.
- Rewrote `sheafH_filtered_colimit_comparison_zero_iso` to compose that helper
  with `sheafH0EquivSections`.
- Rewrote `sheafH_filtered_colimit_comparison_zero_iso_hom` to unfold the helper
  instead of reconstructing the same colimit evidence.

No public declarations were renamed or deleted.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
- `lake build` was not run because no public names, imports, or Lean files were
  added/deleted/renamed.

## Normalized LOC

- Before: `4125`
- After: `4115`
- Delta: `-10`

## Raw `wc -l` of `main/*.lean`

- Before: `5034`
- After: `5026`
- Delta: `-8`

## What remains

Other repeated blocks remain outside this cycle's scope.
