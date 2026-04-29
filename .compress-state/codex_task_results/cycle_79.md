## What was done

- Hoisted the repeated filtered-colimit comparison context in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean` into a narrow `FilteredColimitComparison` section.
- Shared section variables now cover `X`, `J'`, `Ysh`, `csh`, and `hcsh`; `include hcsh` preserves proof-only dependence for the `IsIso` helper theorems.

## What changed

- Removed the repeated context binders from:
  - `sheafH_filtered_colimit_comparison_one_iso`
  - `sheafH_filtered_colimit_comparison_one_iso_hom`
  - `sheafH_filtered_colimit_comparison_zero_iso`
  - `sheafH_filtered_colimit_comparison_zero_iso_hom`
  - `sheafH_filtered_colimit_comparison_isIso_zero`
  - `sheafH_filtered_colimit_comparison_isIso_one`
  - `sheafH_filtered_colimit_comparison_isIso_succ_succ`
- No declarations were renamed, deleted, inlined, or proof-golfed.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
- `lake build`

Both commands completed successfully. `lake build` emitted pre-existing linter warnings in other files.

## Normalized LOC

- Before: `4203`
- After: `4182`
- Delta: `-21`

`PresheafFilteredColimit.lean` normalized count changed from `475` to `454`.

## Raw `wc -l` for `main/*.lean`

- Before: `5105`
- After: `5087`
- Delta: `-18`

`PresheafFilteredColimit.lean` raw line count changed from `517` to `499`.

## What remains

- No blocker remains from this cycle. Further compression should move to the next backlog item; this cycle only handled the repeated comparison-context hoist.
