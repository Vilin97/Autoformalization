# Cycle 47 Results

## What was done

Attempted to delete 3 cached `inferInstanceAs` instances from ZeroOutside.lean and FlasqueVanishing.lean. All three turned out to be genuinely needed — **no changes committed**.

## What didn't work

All three cached instances are required because `TopCat.Sheaf` (an abbreviation for `CategoryTheory.Sheaf (Opens.grothendieckTopology X) C`) and `constantSheaf` don't unfold sufficiently for Lean's instance search:

1. **`Abelian (TopCat.Sheaf AddCommGrpCat X)`** (ZeroOutside.lean): Deleting it caused cascading failures in FlasqueVanishing.lean and all downstream files — `IsGrothendieckAbelian`, `EnoughInjectives`, `HasExt`, and many proofs all depend on this instance.

2. **`IsGrothendieckAbelian (TopCat.Sheaf AddCommGrpCat X)`** (FlasqueVanishing.lean): Deleting it caused `EnoughInjectives` synthesis failure at `sheafHasExt`.

3. **`constantSheaf.Additive`** (FlasqueVanishing.lean): Deleting it caused synthesis failure in CohomologyAPI.lean at `sheafH0EquivSections` which uses `constantSheafAdj.homAddEquiv`.

## Root cause

`TopCat.Sheaf` is defined as:
```
abbrev TopCat.Sheaf C X := CategoryTheory.Sheaf (Opens.grothendieckTopology X) C
```

Despite being an `abbrev`, Lean's instance search does not always unfold it deeply enough to match instances registered for `CategoryTheory.Sheaf`. The `inferInstanceAs` bridges are genuinely needed to connect the two.

Similarly, `constantSheaf` unfolds to `Functor.const ⋙ presheafToSheaf`, and `Additive` for the composition requires explicit bridging.

## Files modified

None (all changes reverted).

## Follow-up

These cached instances are **not** removable without changes to Mathlib's instance infrastructure (e.g., registering instances directly on `TopCat.Sheaf`). This task should be removed from the refactoring backlog.
