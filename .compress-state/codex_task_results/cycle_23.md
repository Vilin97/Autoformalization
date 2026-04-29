# Cycle 23 Report

## What Was Done

- Collapsed `IsFlasqueSheaf` from a one-field class to a reducible predicate abbreviation:
  `∀ {U V : Opens X} (i : U ⟶ V), Epi (F.val.map i.op)`.
- Removed class-style use sites: no remaining `[IsFlasqueSheaf ...]` binders, local `haveI`/`letI`
  flasque instances, or `IsFlasqueSheaf.epi_map` projection calls.
- Threaded flasque proofs explicitly through the affected vanishing and filtered-colimit lemmas.

## What Changed

- `IsFlasqueSheaf` is now an `abbrev`, so the generated class projection/recursor artifacts are gone.
- `isFlasque_of_injective`, `isFlasqueSheaf_zeroOutsideInt_top`, and `FlasqueVanishing` were changed
  from instances to ordinary theorems.
- `epi_app_of_shortExact_flasque`, `isFlasque_X₃_of_shortExact`,
  `sheafH_subsingleton_H1_of_flasque`, and `sheafH_subsingleton_of_flasque` now take explicit
  flasque proofs.
- Updated callers in:
  `FlasqueVanishing`, `ConstantSheafFlasque`, `IrreducibleStep`,
  `PresheafFilteredColimitCore`, `PresheafFilteredColimit`,
  `ClosedImmersionCohomology`, and `GrothendieckVanishing`.

## Verification

- `lake env lean Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/ConstantSheafFlasque.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/ClosedImmersionCohomology.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`
- `lake build`

All checks passed. Existing warnings remain in unrelated/local lines.

## LOC

- Normalized LOC before: `5002`
- Normalized LOC after: `4983`
- Normalized LOC delta: `-19`
- Raw `wc -l Aristotle/GrothendieckVanishing/main/*.lean` before: `5902`
- Raw `wc -l Aristotle/GrothendieckVanishing/main/*.lean` after: `5886`
- Raw delta: `-16`

## What Remains

- No remaining `class IsFlasqueSheaf`.
- No remaining class-projection use sites for `IsFlasqueSheaf.epi_map`.
- Further compression would need a separate target; this cycle stayed scoped to the flasque class collapse.
