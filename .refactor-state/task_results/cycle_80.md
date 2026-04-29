# Cycle 80 Results

## What was done

Two changes in `ClosedImmersionCohomology.lean`:

### Change 1: Golf `pushforward_closedIncl_stalk_eq_zero` (−5 lines)

Replaced the verbose `IsZero.eq_of_src` + `calc` + `ConcreteCategory.id_apply` chain
(12 lines) with `AddCommGrpCat.subsingleton_of_isZero` + `Subsingleton.eq_zero` pattern
(7 lines). This matches the established idiom used in `SheafStalkAlgebra.lean` and
`FlasqueVanishing.lean`.

### Change 2: Add `closedIncl_pushforward_preservesEpis` instance + simplify `closedIncl_pushforward_shortExact` (−2 lines net)

- **New instance** `closedIncl_pushforward_preservesEpis`: wraps the existing
  `epi_pushforward_map_closedIncl` theorem as a `Functor.PreservesEpimorphisms` instance.
  This is an API improvement (Principle 1): downstream code can now use `Functor.map_epi`
  and `inferInstance` instead of manually invoking `epi_pushforward_map_closedIncl`.

- **Simplified `closedIncl_pushforward_shortExact`**: from 13 lines to 6 lines in the body,
  using `Functor.map_mono`/`Functor.map_epi` (the latter now auto-resolved via the new
  `PreservesEpimorphisms` instance).

## Net impact

- **−7 lines** (327 → 320)
- **1 new API instance** (`closedIncl_pushforward_preservesEpis`)
- **0 sorry's, 0 axioms** maintained

## What worked

- `Subsingleton.eq_zero` pattern cleanly replaces the `IsZero.eq_of_src` + `calc` chain
- `Functor.map_epi` works once the explicit `Mono`/`Epi` instances are provided via
  `haveI`, since `(S.map F).g` doesn't definitionally reduce to `F.map S.g`

## Files modified

- `Aristotle/GrothendieckVanishing/main/ClosedImmersionCohomology.lean`

## Verification

- `lake env lean ClosedImmersionCohomology.lean` — clean
- `lake env lean IrreducibleStep.lean` — clean
- `lake env lean SheafStalkAlgebra.lean` — clean (only linter warnings, pre-existing)
- `lake env lean GrothendieckVanishing.lean` — clean

## Follow-up

None required. The `closedIncl_pushforward_preservesEpis` instance is self-contained and
the golf is complete.
