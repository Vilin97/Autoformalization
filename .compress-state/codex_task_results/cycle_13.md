# Cycle 13 Report

## What was done

Deleted the unused sheaf-level theorem
`epi_app_top_of_subsingleton_sheafH1` from
`Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`.

## What changed

- Deleted `epi_app_top_of_subsingleton_sheafH1`.
- Removed its stale entry from the `CohomologyAPI.lean` module doc.
- Kept the adjacent `sheafH0_surj_of_epi_app_top` API intact.
- No private helper declarations were solely dependent on the deleted theorem.

## Verification performed

- Before deletion, `rg -n "\bepi_app_top_of_subsingleton_sheafH1(_presheaf)?\b" Aristotle/GrothendieckVanishing/main`
  found only the module-doc entry and the theorem declaration.
- After deletion, the same `rg` command returned no matches.
- `lake env lean Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`
  succeeded.
- `lake build` succeeded. It reported existing linter warnings in untouched files.
- `rg -n "(:=|by)\s*(sorry|admit)\b|^\s*axiom\b" Aristotle/GrothendieckVanishing/main`
  returned no matches.

## Normalized LOC

- Before: `5260`
- After: `5245`
- Delta: `-15`

Command run before and after:

```bash
python3.9 scripts/normalized_loc.py --per-file --raw
```

For the modified file, `CohomologyAPI.lean` changed from `728` normalized lines
to `713` normalized lines.

## Raw `wc -l` for `main/*.lean`

- Before total: `6235`
- After total: `6216`
- Delta: `-19`

For the modified file, `CohomologyAPI.lean` changed from `925` raw lines to
`906` raw lines.

Command run before and after:

```bash
wc -l Aristotle/GrothendieckVanishing/main/*.lean
```

## What remains

Nothing remains for this scoped cycle item.
