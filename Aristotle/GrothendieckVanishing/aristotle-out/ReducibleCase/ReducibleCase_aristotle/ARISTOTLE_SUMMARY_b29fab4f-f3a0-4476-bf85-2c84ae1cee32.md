# Summary of changes
## Summary

The `sorry` in `sheaf_H_subsingleton_of_reducible` **cannot be filled** with current Mathlib infrastructure (v4.28.0). I performed a thorough analysis of all three suggested approaches and documented the precise blockers in a detailed module docstring in `ReducibleCase.lean`.

### Analysis of the three suggested approaches

1. **Mayer-Vietoris** (`Opens.mayerVietorisSquare`): The Mayer-Vietoris LES in Mathlib (`MayerVietorisSquare.sequence_exact`) operates on `Sheaf.H'` (the cohomology presheaf), not on `Sheaf.H` (global sheaf cohomology). The identification `H'(⊤, F) ≅ H(F)` is explicitly listed as a **TODO** in `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`. Without it, the Mayer-Vietoris sequence cannot yield information about `Sheaf.H`.

2. **Induction on irreducible components** (`NoetherianSpace.finite_irreducibleComponents`): While the finiteness of irreducible components is available, the inductive step still requires relating `H^n(X, F)` to cohomology on sub-decompositions via an exact sequence — which requires extension by zero (`j_!`).

3. **Covariant Ext LES** (`Ext.covariantSequence_exact`): This IS available in Mathlib and provides the long exact sequence for Ext groups from any short exact sequence of sheaves. However, to *use* it for Grothendieck vanishing, one must construct the closed-open complement exact sequence `0 → j_!(F|_U) → F → i_*(F|_Z) → 0`, which requires `j_!`.

### Three critical missing pieces in Mathlib

1. **Extension by zero (`j_!`)** for open embeddings of sheaf categories
2. **The closed-open complement exact sequence** `0 → j_!(F|_U) → F → i_*(F|_Z) → 0`
3. **The identification `H'(⊤, F) ≅ H(F)`** connecting the cohomology presheaf to global cohomology

Any ONE of these (combined with the existing Ext LES) would unblock the proof.

The file compiles cleanly with the single `sorry`, and the detailed mathematical explanation is in the module docstring above the theorem.