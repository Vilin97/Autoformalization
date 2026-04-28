# Cycle 50

## What Was Done

Golfed `exists_section_generating_stalks` in
`Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`.

## What Changed

- Replaced the `ha_mem` + `abs_choice` split in `H_at_cyclic` with a direct
  proof that `|a|` lies in the mapped cyclic subgroup, using
  `Int.sign_mul_self_eq_abs`.
- Inlined the one-use local `hcoeff_const` theorem at the final `x hxW`
  branch, producing `hcoeff_x` directly.
- Shortened the coefficient-constancy proof by applying `hW_eq` through
  `congrArg` on the germ map and simplifying the restriction germs.
- Replaced the manual `change`/`rw`/`exact_mod_cast` integer comparison in
  `hd_x_eq` with `Int.le_toNat`.
- Replaced a terminal `omega` contradiction with `ne_of_gt hd_pos`.

No declarations were renamed or deleted, and no public signatures changed.

## Verification

- `lake env lean Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`
- `python3.9 scripts/normalized_loc.py --per-file --raw`
- `wc -l Aristotle/GrothendieckVanishing/main/*.lean`
- `rg -n "\\b(sorry|admit|axiom)\\b" -g '*.lean' Aristotle || true`
  showed only comment/docstring mentions.

`lake build` was not run because this cycle only changed one proof body.

## LOC

- Normalized LOC before: `4487`
- Normalized LOC after: `4478`
- Delta: `-9`

- Raw `wc -l` of `main/*.lean` before: `5380`
- Raw `wc -l` of `main/*.lean` after: `5370`
- Delta: `-10`

`IrreducibleStep.lean` normalized LOC went from `479` to `470`; raw LOC went
from `565` to `555`.

## What Remains

The proof still has sizeable local cyclic-subgroup and minimality plumbing.
Further savings may be possible in the remaining `H_at_cyclic` divisibility
extraction and the final `hi_inj` witness, but the main one-use local helper
and the manual integer cast block have been removed.
