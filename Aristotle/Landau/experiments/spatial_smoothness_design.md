# Spatial Smoothness Weakening: C^∞ → C^2

## Problem

The `FlatTorus3` typeclass uses `IsSpatiallyDiff : (X → ℝ) → Prop` as a monomorphic
predicate. In the concrete instance, `IsSpatiallyDiff f = ContDiff ℝ ⊤ (periodicLift f)`.

The field `hDiff_grad` requires closure under differentiation:
```
hDiff_grad : ∀ f i, IsSpatiallyDiff f → IsSpatiallyDiff (gradX f · i)
```
Since `gradX f` is morally `fderiv (periodicLift f)`, this requires:
- `ContDiff ℝ n (periodicLift f)` → `ContDiff ℝ n (fderiv (periodicLift f) · eᵢ)`
- But `fderiv` drops one derivative: `ContDiff ℝ n f → ContDiff ℝ (n-1) (fderiv f)`
- So `ContDiff ℝ n → ContDiff ℝ n` via differentiation only works for `n = ⊤`.

## What the proof actually needs

Audit of all `hDiff_grad` usage sites:

| File | Usage | What it really needs |
|------|-------|---------------------|
| CoulombConcreteTheorem42:229 | `hDiff_continuous (hDiff_grad ...)` | Continuity of gradient (C^1 of f suffices) |
| CoulombSpatialTransport:476,515,654 | Same pattern | Continuity of gradient |
| VMLInputDerive:163 | Passed to `hKillingToHarmonic` | `IsSpatiallyDiff` of gradient components |
| Section8:30 | Passed to `hCurlZeroDivZeroHarmonic` | C^1 of gradient (= C^2 of original) |

The concrete `torus_hCurlZeroDivZeroHarmonic` only needs `ContDiff ℝ 1` for F
and `ContDiff ℝ 1` for `gradX F`. This means **C^2 of the original function suffices**.

## Proposed fix: parametric smoothness level

Replace the monomorphic predicate with a parametric one:
```lean
IsSpatiallySmooth : ℕ∞ → (X → ℝ) → Prop
```

Then `hDiff_grad` becomes:
```lean
hDiff_grad : ∀ n f i, IsSpatiallySmooth (n+1) f → IsSpatiallySmooth n (gradX f · i)
```

Each field specifies the minimum level it needs:
- `hDiff_continuous : ∀ f, IsSpatiallySmooth 1 f → Continuous f`
- `hDiff_const : ∀ c, IsSpatiallySmooth n (fun _ => c)` (for all n)
- `hIBP_spatial : ... IsSpatiallySmooth 1 φ → IsSpatiallySmooth 1 ψ → ...`
- `hCurlZeroDivZeroHarmonic : ... IsSpatiallySmooth 1 (F · i) → IsSpatiallySmooth 1 (gradX (F · i) · j) → ...`

The main theorem would require `IsSpatiallySmooth 2` for f and `IsSpatiallySmooth 1` for B.
The concrete theorem for Coulomb would keep `ContDiff ℝ ⊤` (Schwartz needs it).

## Blast radius estimate

- ~50 occurrences of `IsSpatiallyDiff` in Defs.lean
- ~20 occurrences across Section2-8, VMLInputDerive, Theorem42
- ~15 occurrences in CoulombConcreteTheorem42, CoulombSpatialTransport
- ~10 occurrences in TorusInstance
- Total: ~95 changes

## Conclusion

The weakening is mathematically sound (C^2 spatial smoothness is sufficient) but
requires significant refactoring (~95 call sites). The parametric design is cleaner
than a two-level predicate approach. This is a multi-session effort best attempted
when no other work is pending.

Priority: Low. The concrete theorem still needs C^∞ for Schwartz, so the
weakening only benefits the abstract chain. Impact is theoretical (hypothesis
minimality), not practical.
