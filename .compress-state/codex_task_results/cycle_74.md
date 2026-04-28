# Cycle 74

## What was done

Golfed the proof of `ReducibleVanishing` in
`Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`.

## What changed

- Removed the local `comps`, `comps_def`, `hcover`, and `hcomp_irred` setup by
  calling the finite-components induction directly on `hfin.toFinset`.
- Rewrote the kernel induction witness in term style, avoiding the separate
  `apply`/`intro` plumbing.
- Inlined the `hx'` finite-union complement witness into the
  `stalk_zero_of_shortExact_kernel` call.
- Passed `hker` directly to `subsingleton_sheafH_of_closedImmersion_middle`.
- Shortened the irreducible subspace branch by using a one-line `haveI` and
  direct `exact ih_irred ...`.

No declarations were renamed, deleted, or added.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`
- `lake build` was not run; this was a proof-body-only edit with no file/import
  add, delete, or rename.

## Normalized LOC

- Before: 4224 total normalized LOC
- After: 4216 total normalized LOC
- Delta: -8

`GrothendieckVanishing.lean` went from 130 to 122 normalized LOC.

## Raw `wc -l` for `main/*.lean`

- Before: 5126 total raw lines
- After: 5118 total raw lines
- Delta: -8

`GrothendieckVanishing.lean` went from 152 to 144 raw lines.

## What remains

The target proof still contains the local `GZ` and `S` abbreviations because
they keep repeated closed-immersion/pullback terms from expanding at the call
sites. Further reductions here likely need a different proof shape rather than
more local plumbing cleanup.
