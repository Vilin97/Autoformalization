# Cycle 27 Results

## What was done

- Reverted `sheafH0EquivSections_presheaf_natural` to a bundled-sheaf naturality lemma named `sheafH0EquivSections_natural`.
- Updated the eight live call sites in `CohomologyAPI.lean` and `PresheafFilteredColimit.lean` to pass sheaf morphisms directly.
- Left `sheafH0EquivSections_presheaf` unchanged, as requested.

## What changed

- Renamed/reshaped:
  - `sheafH0EquivSections_presheaf_natural`
  - to `sheafH0EquivSections_natural`
- Removed local packaging in the naturality proof:
  - `Fsh`
  - `Gsh`
  - `fsh`
- Removed call-site bridge proofs of the form:
  - `(Sheaf.Hom.mk S.g.val : S.X₂ ⟶ S.X₃) = S.g`
  - `(Sheaf.Hom.mk f.val : F ⟶ G) = f`
  - `(Sheaf.Hom.mk φ.τ₃.val : S₁.X₃ ⟶ S₂.X₃) = φ.τ₃`
- Updated callers to use `S.g`, `f`, `φ.τ₃`, `Ysh.map f`, and `csh.ι.app j` directly.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`
  - passed
- `lake build Aristotle.GrothendieckVanishing.main.CohomologyAPI`
  - passed; used to refresh the built import after the public declaration rename
- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
  - passed with existing linter warnings
- `lake build`
  - passed with existing linter warnings

## Normalized LOC

- Before: 4946
- After: 4924
- Delta: -22

## Raw `wc -l` for `Aristotle/GrothendieckVanishing/main/*.lean`

- Before: 5822
- After: 5802
- Delta: -20

## What remains

- `sheafH0EquivSections_presheaf` is still the presheaf-boundary equivalence wrapper and remains a possible later sheaf-reversion target.
- Existing linter warnings in unrelated areas remain.
