# Cycle 77 Report

## What was done

Removed the two targeted `@[simps]` attributes from `ZeroOutside.lean` so Lean no longer generates the unused public declarations:

- `TopCat.Presheaf.zeroOutside.sHom_app`
- `TopCat.Sheaf.zeroOutsideInt.sHom_val`

## What changed

- Deleted the `@[simps]` line immediately before `TopCat.Presheaf.zeroOutside.sHom`.
- Deleted the `@[simps]` line immediately before `TopCat.Sheaf.zeroOutsideInt.sHom`.
- No declarations were renamed, inlined, or otherwise changed.

## Verification performed

- `rg -n "zeroOutside\\.sHom_app\\b|zeroOutsideInt\\.sHom_val\\b" Aristotle/GrothendieckVanishing/main`
  - No references found.
- `lake env lean Aristotle/GrothendieckVanishing/main/ZeroOutside.lean`
  - Succeeded, with pre-existing lint warnings.
- `lake build`
  - Succeeded, with pre-existing lint warnings.

## Normalized LOC

- Before: 4207 normalized, 5109 raw reported by `scripts/normalized_loc.py`
- After: 4205 normalized, 5107 raw reported by `scripts/normalized_loc.py`
- Delta: -2 normalized, -2 raw reported by `scripts/normalized_loc.py`

## Raw `wc -l` for `main/*.lean`

- Before: 5109
- After: 5107
- Delta: -2

## What remains

Nothing remains for this cycle. The other `ZeroOutside` generated declarations were intentionally left untouched because they still have explicit source references.
