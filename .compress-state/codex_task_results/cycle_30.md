# Cycle 30

## What was done

- Reverted the zero-sheaf cohomology API from the presheaf-boundary theorem
  `sheafH_subsingleton_of_isZero_presheaf` to the bundled-sheaf theorem
  `sheafH_subsingleton_of_isZero`.
- Updated the direct callers in:
  - `CohomologyAPI.lean`
  - `FinitelyGeneratedVanishing.lean`
  - `IrreducibleStep.lean`
  - `GrothendieckVanishing.lean`

## What changed

- Renamed/deleted:
  - Deleted `sheafH_subsingleton_of_isZero_presheaf`.
  - Added `sheafH_subsingleton_of_isZero` with argument
    `{F : TopCat.Sheaf AddCommGrpCat.{u} X} (hzero : IsZero F)`.
- Simplified the empty-space theorem's internal call to use the bundled zero-sheaf theorem.
- Simplified callers by passing already bundled sheaves directly:
  - `TopCat.Presheaf.finsetGeneratedSheaf hK ∅`
  - `S.X₁`
  - `(⟨R, hRsh⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)`
  - `(⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)`

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`
- `lake build`
- `rg "sheafH_subsingleton_of_isZero_presheaf" Aristotle`

The full build completed successfully. It replayed pre-existing linter warnings in
unmodified files such as `ZeroOutside.lean` and filtered colimit files.

## LOC

- Normalized LOC before: `4891`
- Normalized LOC after: `4889`
- Normalized LOC delta: `-2`

- Raw `wc -l Aristotle/GrothendieckVanishing/main/*.lean` before: `5768`
- Raw `wc -l Aristotle/GrothendieckVanishing/main/*.lean` after: `5765`
- Raw LOC delta: `-3`

## What remains

- `sheafH_subsingleton_of_isEmpty_presheaf` remains in its presheaf-boundary form by scope.
- Generated `zeroOutside` projection/simp audit rows were not touched.
