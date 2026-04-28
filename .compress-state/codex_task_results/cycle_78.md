# Cycle 78 Results

## What was done

- Removed the two `@[simps]` annotations in `Aristotle/GrothendieckVanishing/main/ZeroOutside.lean` that generated unused public declarations.
- Replaced local proof dependencies on generated projection lemmas with direct unfolding/simplification of `zeroOutside`.

## What changed

- Deleted generated declarations by removing their generation points:
  - `TopCat.Presheaf.zeroOutside_obj`
  - `TopCat.Presheaf.zeroOutside_map`
  - `TopCat.Presheaf.zeroOutside_openHom_app`
- Updated local proofs that had depended on generated simp lemmas:
  - `Presheaf.zeroOutside.generator` now unfolds `zeroOutside` and `constZ`.
  - `Presheaf.zeroOutside.sHom` now unfolds `zeroOutside` and `constZ` in the `eqToHom` proof.
  - `Presheaf.zeroOutside.sHom` disambiguates `ConcreteCategory.comp_apply`.
  - `Presheaf.zeroOutside.sHom_app_generator` no longer mentions `zeroOutside_obj`.
  - `Presheaf.zeroOutside.resGen_eqToHom_eq_one` no longer mentions `zeroOutside_map`.

## Verification performed

- `rg -n "zeroOutside_(obj|map|openHom_app)" Aristotle/GrothendieckVanishing/main/ZeroOutside.lean` found no remaining references.
- `lake env lean Aristotle/GrothendieckVanishing/main/ZeroOutside.lean` passed.
- `lake build` passed.

## Normalized LOC

- Before: `4205`
- After: `4203`
- Delta: `-2`

## Raw `wc -l` of `main/*.lean`

- Before: `5107`
- After: `5105`
- Delta: `-2`

## What remains

- Nothing blocked in this cycle. The targeted generated unused declarations are gone.
