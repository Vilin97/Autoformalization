# Cycle 4 Report

## What Was Done

Deleted the remaining unused Flasque presheaf-boundary wrapper pair from
`Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean`.

Before editing, `rg -n "sheafH_subsingleton_H1_of_flasque_of_epi_app_top(_map)?_presheaf" Aristotle/GrothendieckVanishing/main`
showed only the two declarations and the local self-call from the map wrapper
to the non-map wrapper. No external caller existed.

## What Changed

- Deleted `sheafH_subsingleton_H1_of_flasque_of_epi_app_top_presheaf`.
- Deleted `sheafH_subsingleton_H1_of_flasque_of_epi_app_top_map_presheaf`.
- Deleted their attached docstrings.
- No replacement `_presheaf` wrapper was introduced.
- No call-site rewrite was needed because the names had no real caller outside
  the deleted local wrapper chain.

## Verification Performed

- `lake env lean Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`
- `lake build`

All verification passed. Some pre-existing linter warnings were emitted in
filtered-colimit and other downstream files during these checks.

## Normalized LOC

- Before: 6062 normalized, 7120 raw
- After: 5971 normalized, 7020 raw
- Delta: -91 normalized, -100 raw

## Raw `main/*.lean` `wc -l`

- Before: 7120
- After: 7020
- Delta: -100

## What Remains

The scoped Flasque pair for this cycle is gone. The broader Phase-1 target of
getting total raw `main/*.lean` LOC below 6500 is not yet complete; remaining
compression must come from later scoped reversion/deletion work in other files.
