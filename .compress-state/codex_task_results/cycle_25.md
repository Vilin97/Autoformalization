# Cycle 25 Results

## What was done

- Eliminated `Aristotle/GrothendieckVanishing/main/ULiftInt.lean`.
- Removed the `ULiftInt` imports from `CohomologyAPI.lean` and `ZeroOutside.lean`.
- Replaced all remaining uses of `AddCommGrpCat.uliftZMultiplesAddEquiv` and
  `uliftZMultiplesAddEquiv_symm_apply` with Mathlib's `uliftZMultiplesHom`
  and `AddCommGrpCat.homAddEquiv`.

## What changed

- Deleted declarations:
  - `AddCommGrpCat.uliftZMultiplesAddEquiv`
  - `AddCommGrpCat.uliftZMultiplesAddEquiv_symm_apply`
- Inlined / replaced:
  - `sheafH0EquivSections_presheaf` now composes `homAddEquiv` with a local
    `AddEquiv.mk'` wrapper around `uliftZMultiplesHom`.
  - `zeroOutside.sHom.app` now builds the section morphism directly with
    `AddCommGrpCat.ofHom (uliftZMultiplesHom ...)`.
  - The two old rewrite calls in `zeroOutside.sHom` and the old rewrite in
    `sHom_app_generator` are gone; the direct morphism lets `simp` close the
    naturality branch.

## Verification performed

- `lean_loogle "ULift ℤ →+ _ ≃+ _"`
- `lean_leansearch "ULift Int additive equivalence AddCommGrpCat morphisms determined by image of one"`
- `lean_local_search "uliftZMultiples"`
- `lake env lean Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/ZeroOutside.lean`
- `lake build`
- `rg -n "uliftZMultiplesAddEquiv|uliftZMultiplesAddEquiv_symm_apply|ULiftInt" Aristotle/GrothendieckVanishing/main`
  - No matches.
- `rg -n "\bsorry\b|\badmit\b|\baxiom\b" Aristotle --glob '*.lean'`
  - Matches were only prose/comment occurrences.
- `git diff --check`

## Normalized LOC

- Before: `4978`
- After: `4956`
- Delta: `-22`

## Raw `wc -l` for `main/*.lean`

- Before: `5879`
- After: `5847`
- Delta: `-32`

## What remains

- No project references to `ULiftInt` or the deleted `uliftZMultiplesAddEquiv`
  declarations remain.
- Mathlib does not appear to expose the exact additive equivalence
  `(AddCommGrpCat.of (ULift ℤ) ⟶ G) ≃+ G`; the one remaining additive wrapper is
  local to `sheafH0EquivSections_presheaf`.
