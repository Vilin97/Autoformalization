# Cycle 22

## What was done

Deleted the two audit-listed unused public theorem wrappers in
`Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean`.

## What changed

- Deleted `sheafH_filtered_colimit_succ_eta_val_comp_cokernel_pi`.
- Deleted `sheafH_filtered_colimit_succ_iota_val_comp_cokernel_pi`.
- Deleted the now-superfluous local `omit [IsFiltered J'] in` attached only to the first theorem.
- Left neighboring filtered-colimit definitions and exactness statements unchanged.

## Verification performed

- `rg "sheafH_filtered_colimit_succ_(eta|iota)_val_comp_cokernel_pi" Aristotle/GrothendieckVanishing/main`
  found no remaining references after deletion.
- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean`
  passed, with pre-existing linter warnings.
- `lake build` passed, with pre-existing linter warnings.

## Normalized LOC

- Before: 5014 normalized LOC; 5920 raw `wc -l` total from the script.
- After: 5002 normalized LOC; 5902 raw `wc -l` total from the script.
- Delta: -12 normalized LOC; -18 raw `wc -l`.

## Raw `wc -l` of `main/*.lean`

- Before: 5920
- After: 5902
- Delta: -18

## What remains

Nothing remains for this scoped deletion cycle.
