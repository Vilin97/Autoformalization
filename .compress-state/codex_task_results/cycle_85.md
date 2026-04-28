## Cycle 85

### What Was Done

Sheaf-reverted the final `GrothendieckVanishing` interface cluster in
`Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`.

### What Changed

- `ReducibleVanishing` now takes `F : TopCat.Sheaf AddCommGrpCat.{u} X`.
- `irreducible_dim_zero_vanishing` now takes a bundled sheaf and no longer
  builds a local `Fsh` wrapper.
- `grothendieck_vanishing_of_irreducible` now takes bundled sheaves in both
  its main argument and irreducible induction callback.
- `GrothendieckVanishing` and its well-founded induction predicate now quantify
  `F : TopCat.Sheaf AddCommGrpCat.{u} X` directly.
- The remaining presheaf-level boundary is only the existing
  `IrreduciblePosVanishing` / `VanishingIH` callback, where the sheaf argument is
  unpacked as `G.val` and `G.cond`.

No declarations were renamed, deleted, or inlined in this cycle.

### Verification

- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishingOverview.lean`
- `lake build`

`lake build` completed successfully. It replayed existing unrelated linter
warnings in older files.

### LOC

- Normalized LOC before: `4104`
- Normalized LOC after: `4097`
- Normalized LOC delta: `-7`
- Raw `wc -l` of `main/*.lean` before: `5015`
- Raw `wc -l` of `main/*.lean` after: `5008`
- Raw `wc -l` delta: `-7`

### What Remains

`IrreduciblePosVanishing` and `VanishingIH` are still presheaf-level, as required
by the cycle scope limit. Main raw LOC remains just above 5000.
