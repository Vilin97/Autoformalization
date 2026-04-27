# Cycle 19 Report

## What was done

Deleted the unused `Epi f` wrapper theorem from
`Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`.

## What changed

Deleted declaration:

- `epiImage_zeroOutsideInt_vanishing`

Kept `epiImage_zeroOutsideInt_vanishing_of_locallySurjective` intact; it remains
defined and is still used by `IrreduciblePosVanishing`.

## Verification performed

- `rg -n '\bepiImage_zeroOutsideInt_vanishing\b' Aristotle/GrothendieckVanishing/main`
  - Before: one match, the wrapper declaration itself.
  - After: no matches.
- `rg -n 'epiImage_zeroOutsideInt_vanishing_of_locallySurjective' Aristotle/GrothendieckVanishing/main`
  - After: definition and one call site remain.
- `lake env lean Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`
- `lake build`

All Lean checks and the full build completed successfully.

## LOC

- Normalized LOC before: `5151`
- Normalized LOC after: `5131`
- Normalized LOC delta: `-20`
- Raw `wc -l` of `main/*.lean` before: `6077`
- Raw `wc -l` of `main/*.lean` after: `6056`
- Raw line delta: `-21`

## What remains

Nothing remains for this cycle's targeted unused declaration.
