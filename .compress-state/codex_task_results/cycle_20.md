# Cycle 20

## What Was Done

- Deleted the unused public theorem `sheafH_filtered_colimit_surj`.
- Removed doc/comment mentions that named the deleted theorem.

## What Changed

- Deleted declaration:
  - `sheafH_filtered_colimit_surj` from `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean`
- Updated stale documentation in:
  - `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean`
  - `Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean`

## Verification Performed

- `rg -n "\bsheafH_filtered_colimit_surj\b" Aristotle/GrothendieckVanishing/main`
  - Before: theorem declaration plus two doc/comment mentions.
  - After: no matches.
- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean`
  - Passed with existing linter warnings.
- `lake env lean Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean`
  - Passed.
- `lake build`
  - Passed.

## Normalized LOC

- Before: `5115`
- After: `5027`
- Delta: `-88`

## Raw `wc -l` for `main/*.lean`

- Before: `6034`
- After: `5939`
- Delta: `-95`

## What Remains

- Other unused declarations mentioned in the cycle strategy were intentionally left untouched for separate audit-driven cycles.
