# Cycle 14 results

## What was done

Deleted the three scoped unused public declarations from
`Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`.

## What changed

- Deleted `sheafCohomologyFunctor_additive`.
- Deleted `sheafH0NatIsoSections_hom_app`.
- Deleted `sheafH0NatIsoSections_inv_app`.
- No helper cascade was needed.
- `sheafCohomologyFunctor_obj` was left untouched because it still has downstream uses.

## Verification performed

- `rg -n "sheafCohomologyFunctor_additive|sheafH0NatIsoSections_hom_app|sheafH0NatIsoSections_inv_app" Aristotle/GrothendieckVanishing/main`
  - No matches after deletion.
- `lake env lean Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`
  - Passed.
- `lake build`
  - Passed. The build emitted existing linter warnings in other files, but no errors.

Lean LSP MCP proof-search tools were not used because this cycle only deleted unused declarations and did not require proof search.

## Normalized LOC

- Before: `5245`
- After: `5234`
- Delta: `-11`

## Raw `wc -l` for `main/*.lean`

- Before: `6216`
- After: `6202`
- Delta: `-14`

## What remains

Nothing blocked in this scoped cycle. Further deletion of `sheafCohomologyFunctor_obj` remains out of scope because it has known proof mentions in downstream files.
