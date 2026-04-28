## What was done

Golfed `exists_section_generating_stalks` in `Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`.

## What changed

- Shortened the local stalk-map injectivity proof by using a dependent `have hi_inj (x : X)` and letting Lean infer mono components.
- Folded the `cyclic_generator_of_coeff` subgroup-generator bullets into the constructor proof, with a direct contradiction from `d ∈ H_at x hx` when the cyclic generator is zero.
- Replaced the long germ-equality rewrite chain with a short rewrite to the known stalk coefficient followed by `simpa`.
- Replaced the final one-use `obtain ⟨k₀, rfl⟩` with `Exists.imp`.

No declarations were renamed, deleted, or added.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`
- `python3.9 scripts/normalized_loc.py --per-file --raw`
- `wc -l Aristotle/GrothendieckVanishing/main/*.lean`
- `rg "\b(sorry|admit)\b" Aristotle/GrothendieckVanishing/main/*.lean || true` only found an existing comment.
- `rg "\baxiom\b" Aristotle/GrothendieckVanishing/main/*.lean || true` only found an existing prose comment about TR3.

`lake build` was not run because the cycle only changed one proof body and did not touch imports or declaration boundaries.

## Normalized LOC

- Before: `4212` total, `401` in `IrreducibleStep.lean`
- After: `4207` total, `396` in `IrreducibleStep.lean`
- Delta: `-5` total

## Raw `wc -l` of `main/*.lean`

- Before: `5114`
- After: `5109`
- Delta: `-5`

## What remains

The target proof still has dense stalk/germ transport near the final minimality argument, but the remaining locals are used more than once or preserve important readability. No further single-site helper was introduced.
