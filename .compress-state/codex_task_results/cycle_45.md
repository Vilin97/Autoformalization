# Cycle 45 Results

## What was done

Golfed `PushforwardHIso` in `Aristotle/GrothendieckVanishing/main/ClosedImmersionCohomology.lean`.

## What changed

- Inlined the one-use `topIso` in the degree-zero branch.
- Added local reusable facts `hSE`, `hSrcSub`, and `hTgtSub` for the repeated short-exact and middle-term cohomology hypotheses.
- Inlined the one-use `hH1_src`, `hH1_tgt`, `hShift_src`, and `hShift_tgt` isomorphism lets into the final compositions.
- No declarations were renamed or deleted, and no public signatures changed.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/ClosedImmersionCohomology.lean`
- `python3.9 scripts/normalized_loc.py --per-file --raw` before and after
- `wc -l Aristotle/GrothendieckVanishing/main/*.lean` before and after

`lake build` was not run because this was a proof-body-only edit with no import, rename, deletion, or file graph change.

## Normalized LOC

- Before: `4566`
- After: `4546`
- Delta: `-20`

For `ClosedImmersionCohomology.lean` specifically: `123 -> 103`, delta `-20`.

## Raw `wc -l` of `main/*.lean`

- Before: `5456`
- After: `5436`
- Delta: `-20`

For `ClosedImmersionCohomology.lean` specifically: `154 -> 134`, delta `-20`.

## What remains

`PushforwardHIso` is shorter and still compiles. Further compression, if desired, would likely need a different target rather than more local reshaping of this proof.
