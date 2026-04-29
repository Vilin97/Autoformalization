## What Was Done

Golfed `exists_section_generating_stalks` in `Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`.

## What Changed

- Replaced manual `AddSubgroup` map/bottom reasoning in `H_at_cyclic` with `AddSubgroup.mem_map_equiv` and `AddSubgroup.map_eq_bot_iff_of_injective`.
- Collapsed the divisibility transport branch in `H_at_cyclic` by rewriting membership through `AddSubgroup.mem_map_equiv`.
- Turned `H_at_cyclic` and `mk_P` proof-intro wrappers into direct function proofs.
- Removed the proof-local `d_nat` and `d_gen_res` staging definitions by inlining their expressions.
- Shortened the final minimality handoff for `hd_x_eq` and the closing `rw`.

No declarations were renamed, deleted, or added.

## Verification Performed

- `lake env lean Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`
- `rg -n "\b(sorry|admit|axiom)\b" Aristotle --glob '*.lean' || true`

`lake build` was not run because this was a proof-only edit with no Lean file add/delete/rename, import change, or declaration deletion.

## Normalized LOC

- Before: `4413` total normalized LOC (`IrreducibleStep.lean`: `458`)
- After: `4401` total normalized LOC (`IrreducibleStep.lean`: `446`)
- Delta: `-12`

## Raw `wc -l` of `main/*.lean`

- Before: `5310` total raw lines (`IrreducibleStep.lean`: `543`)
- After: `5298` total raw lines (`IrreducibleStep.lean`: `531`)
- Delta: `-12`

## What Remains

Further compression in this proof would likely require finding a stronger subgroup/divisibility lemma or a broader restructuring of the minimality argument. No blocker remains from this cycle.
