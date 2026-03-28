# Work Plan — Grothendieck Vanishing

**Updated**: 2026-03-28T10:00Z

## Status Summary

- **Sorry count**: 1 (`FlasqueVanishing` in Setup.lean)
- **Files**: 9 in `main/`, all compiling cleanly
- **All other theorems**: fully proved (no sorry's)

## Architecture

FlasqueVanishing (the single sorry) is the full Grothendieck vanishing statement:
for Noetherian X, any sheaf F, and n > dim X, Sheaf.H F n = 0.

ReducibleVanishing and IrreduciblePosVanishing are trivial corollaries.
DimZeroVanishing is proved independently via projectivity of the constant sheaf
(bypasses FlasqueVanishing entirely).

## What Would Be Needed to Prove FlasqueVanishing

The full proof (Hartshorne III.2.7) requires infrastructure not yet in Mathlib v4.28:

1. **Extension by zero (j_!)** for open embeddings of sheaf categories
2. **Proposition 2.9**: cohomology commutes with filtered colimits on Noetherian spaces
3. **Derived adjunction**: Ext_X(Z, i_*G, n) ≅ Ext_Y(Z_Y, G, n) for closed i: Y ↪ X
4. **The closed-open complement SES**: 0 → j_!(F|_U) → F → i_*(F|_Z) → 0

Any combination of these (plus the existing Ext LES in Mathlib) would close the sorry.

## Independently Proved Results (sorry-free)

- `HasSeparator AddCommGrpCat` — ULift ℤ is a separator
- `constantSheaf_flasque_of_irreducible` — constant sheaf on irreducible space is flasque
- `cohomologyPresheafTopEquiv` — H'(⊤, F) ≅ H(F) (resolves Mathlib TODO)
- `subsingleton_ext_of_ses` — abstract LES vanishing from short exact sequences
- `grothendieck_vanishing_dim_zero` — dim 0 case via projectivity (no FlasqueVanishing needed)
- `sheaf_isZero_of_isEmpty` — sheaves on empty spaces are zero
- `topologicalKrullDim_lt_of_isIrreducible_of_isClosed` — dimension inequality
- `GrothendieckVanishing` — main theorem (well-founded induction assembling all pieces)

## Backlog (nice-to-have)

- PR `cohomologyPresheafTopEquiv` and `subsingleton_ext_of_ses` to Mathlib
- Reduce heartbeats in ConstantSheafFlasque.lean (currently up to 1,600,000)
- Generalize from AddCommGrpCat to ModuleCat R
