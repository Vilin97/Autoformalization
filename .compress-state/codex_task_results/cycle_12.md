# Cycle 12 Report

## What was done

Deleted the unused public wrapper theorem `epi_pushforward_map_closedIncl` from
`Aristotle/GrothendieckVanishing/main/ClosedImmersion.lean`.

## What changed

- Deleted `epi_pushforward_map_closedIncl`.
- Kept `epi_pushforward_map_closedIncl_of_locallySurjective`; it is still used by
  `closedIncl_pushforward_preservesEpis`.
- No helper declarations became newly single-use or unreachable from this deletion.

## Verification performed

- `rg -n "epi_pushforward_map_closedIncl\\b" Aristotle/GrothendieckVanishing/main`
  returned no matches after the deletion.
- `lake env lean Aristotle/GrothendieckVanishing/main/ClosedImmersion.lean`
  succeeded.
- `lake build` succeeded. It reported existing linter warnings in untouched files.

## Normalized LOC

- Before: `5286`
- After: `5260`
- Delta: `-26`

Command run before and after:

```bash
python3.9 scripts/normalized_loc.py --per-file --raw
```

## Raw `wc -l` for `main/*.lean`

- Before total: `6264`
- After total: `6235`
- Delta: `-29`

For the modified file, `ClosedImmersion.lean` changed from `521` raw lines to
`492` raw lines.

Command run before and after:

```bash
wc -l Aristotle/GrothendieckVanishing/main/*.lean
```

## What remains

Nothing remains for this scoped cycle item.
