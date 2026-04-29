# Cycle 29

## What was done

- Replaced the presheaf-boundary theorem
  `subsingleton_sheafH_of_shortExact_middle_presheaf` with the bundled-sheaf theorem
  `subsingleton_sheafH_of_shortExact_middle`.
- Updated the three external callers in:
  - `ClosedImmersionCohomology.lean`
  - `FinitelyGeneratedVanishing.lean`
  - `IrreducibleStep.lean`

## What changed

- Renamed/deleted:
  - Deleted `subsingleton_sheafH_of_shortExact_middle_presheaf`.
  - Added `subsingleton_sheafH_of_shortExact_middle` with arguments
    `{F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) [Mono f]`.
- Simplified the theorem body by constructing the cokernel short complex directly from
  `f`, removing the local `fsh : ⟨F, hF⟩ ⟶ ⟨G, hG⟩` bridge and the theorem-internal
  presheaf-to-sheaf mono conversion.
- Simplified callers:
  - `ClosedImmersionCohomology.lean`: uses `S.f` and `cokernel S.f` directly; removed
    the `Mono S.f.val` bridge and `Sheaf.Hom.mk S.f.val` packaging.
  - `FinitelyGeneratedVanishing.lean`: uses `SC.f` directly; removed the old
    `Functor.map_mono ... SC.f` instance for `SC.f.val`.
  - `IrreducibleStep.lean`: names the bundled morphism `jsh := Sheaf.Hom.mk j` once,
    then uses `jsh` for `cokernel`, stalk cokernel support, and the middle-term theorem.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/ClosedImmersionCohomology.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`
- `lake build`

The full build completed successfully. It replayed pre-existing linter warnings in
unmodified files such as `ZeroOutside.lean` and filtered colimit files.

## LOC

- Normalized LOC before: `4914`
- Normalized LOC after: `4891`
- Normalized LOC delta: `-23`

- Raw `wc -l Aristotle/GrothendieckVanishing/main/*.lean` before: `5792`
- Raw `wc -l Aristotle/GrothendieckVanishing/main/*.lean` after: `5768`
- Raw LOC delta: `-24`

## What remains

- The other remaining `_presheaf` wrappers were intentionally left out of scope for this cycle.
- ZeroOutside generated projection/simps audit rows remain skipped per strategy.
