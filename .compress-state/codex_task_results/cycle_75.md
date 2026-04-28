# Cycle 75

## What was done

Golfed `exists_section_generating_stalks` in
`Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`.

## What changed

- Replaced the hand-built coefficient subgroup `H_at` with a comap of
  `(i_x x).range` along the additive hom `n ↦ n • gen_at x hx`.
- Added the corresponding `AddMonoidHom.mk'_apply` rewrite in the existing
  `Presheaf.germ_eq` transport block.

No declarations were renamed, deleted, or added.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`
- `lake build` was not run; this was a proof-body-only edit with no file/import
  add, delete, rename, or attribute change.

## Normalized LOC

- Before: 4216 total normalized LOC
- After: 4212 total normalized LOC
- Delta: -4

`IrreducibleStep.lean` went from 405 to 401 normalized LOC.

## Raw `wc -l` for `main/*.lean`

- Before: 5118 total raw lines
- After: 5114 total raw lines
- Delta: -4

`IrreducibleStep.lean` went from 491 to 487 raw lines.

## What remains

The rest of `exists_section_generating_stalks` is still dominated by the
`germ_eq` transport and the cyclic-generator helper. I did not find a shorter
Mathlib replacement for the positive generator extraction during this cycle.
