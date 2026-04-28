# Cycle 41

## What was done

Golfed `exists_section_generating_stalks` in
`Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`.

## What changed

- Compressed the `H_at_cyclic` block:
  - shortened the `a ≠ 0` contradiction;
  - destructed the `ULift` map witness directly for `ha_mem`;
  - replaced the second sign split with Mathlib `abs_dvd`.
- Compressed `mk_P` by replacing the explicit divisibility witness extraction with one `simpa`.
- Inlined the nontrivial-subgroup witnesses using `AddSubgroup.ne_bot_iff_exists_ne_zero`.
- Simplified the tail transport:
  - inlined `hd_in_Hx`/`hHx_ne`;
  - used `ne_of_gt hd_pos` for the nonzero witness;
  - pushed the final `congrArg ULift.down` equality into the final rewrite.
- No declaration names, signatures, imports, attributes, or generated `@[simps]` equations were changed.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`
- `python3.9 scripts/normalized_loc.py --per-file --raw` before and after
- `wc -l Aristotle/GrothendieckVanishing/main/*.lean` before and after

`lake build` was not run because this cycle only changed one proof body and did not change declarations/imports/files/attributes.

## LOC

- Normalized LOC before: `4661`
- Normalized LOC after: `4637`
- Normalized LOC delta: `-24`
- Raw `wc -l` of `main/*.lean` before: `5542`
- Raw `wc -l` of `main/*.lean` after: `5527`
- Raw `wc -l` delta: `-15`

## What remains

The theorem still has long local shrinking and germ-transport blocks around `germ_eq`/`hcoeff_const`; those may have further savings, but this cycle stayed within the targeted cyclic-subgroup, minimal-generator, and final divisibility transport blocks.
