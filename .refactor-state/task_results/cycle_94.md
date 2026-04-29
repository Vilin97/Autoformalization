# Cycle 94 Result

## What was done

Replaced 2 of 5 explicit `FlasqueVanishing` calls with `inferInstance`, partially
completing the `IsFlasqueSheaf` class integration started in cycle 27.

## Changes

| File | Line | Before | After |
|------|------|--------|-------|
| IrreducibleStep.lean | 342 | `exact FlasqueVanishing X F m` | `exact inferInstance` |
| PresheafFilteredColimit.lean | 508 | `have hI := FlasqueVanishing X injCocone.pt n` | `have hI : Subsingleton (...) := inferInstance` |

## What didn't work

3 sites could not use `inferInstance` — instance resolution failed:
- **SheafStalkAlgebra.lean:50** — `ext_dimension_shift` takes `Subsingleton` as explicit arg;
  Lean can't synthesize the instance in that argument position.
- **ClosedImmersionCohomology.lean:233,242** — same issue with `subsingleton_H1_via_surj`
  and `ext_dimension_shift`. The `Subsingleton (Abelian.Ext ...)` type doesn't match
  `Subsingleton (Sheaf.H ...)` syntactically during instance search, even though they're
  definitionally equal.

Root cause: `FlasqueVanishing` provides `Subsingleton (Sheaf.H F (n+1))`, but these
call sites need `Subsingleton (Abelian.Ext Z F (n+1))` where `Sheaf.H` unfolds to
`Abelian.Ext`. Instance resolution doesn't unfold abbrevs aggressively enough.

## Files modified

- `Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`
- `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`

## Follow-up

3 explicit `FlasqueVanishing` calls remain (SheafStalkAlgebra:50,
ClosedImmersionCohomology:233,242). These could be addressed by either:
1. Making `Subsingleton` args instance-implicit in `ext_dimension_shift` /
   `subsingleton_H1_via_surj` (API change, separate cycle)
2. Adding a `@[reducible]` annotation on `Sheaf.H` so instance search unfolds it
