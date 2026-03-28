import Mathlib

universe u

open CategoryTheory TopologicalSpace Limits

instance : HasSeparator AddCommGrpCat.{u} where
  hasSeparator := by
    use AddCommGrpCat.of (ULift ℤ)
    intro A B f g h; simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, forall_eq',
      ULift.forall]
    intro x; specialize h (AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun y => y • x) fun y z => by simp only [add_smul])) 1; aesop

instance : IsGrothendieckAbelian.{u} AddCommGrpCat.{u} where

instance (X : TopCat.{u}) : Abelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

instance (X : TopCat.{u}) : IsGrothendieckAbelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (IsGrothendieckAbelian (CategoryTheory.Sheaf _ _))

set_option synthInstance.maxHeartbeats 80000

/-!
## Grothendieck Vanishing — Reducible Case (Hartshorne III.2.7, Step 1)

### Statement

For a nonempty Noetherian space `X` that is **not** irreducible, sheaf cohomology
`Sheaf.H F n` vanishes (is a subsingleton) for `n > dim X`, assuming vanishing already
holds for all irreducible spaces of dimension `≤ dim X`.

### Why this sorry cannot be filled with current Mathlib (as of v4.28.0)

The standard proof (Hartshorne, III.2.7) proceeds as follows:

1. Since `X` is not irreducible, decompose `X = Y₁ ∪ Z` where `Y₁` is an irreducible
   component and `Z = closure(X \ Y₁)` is a proper closed subset.
2. Let `U = X \ Z` (open) and `i : Z ↪ X` (closed embedding). Construct the
   **short exact sequence of sheaves on X**:
   ```
   0 → j_!(F|_U) → F → i_*(F|_Z) → 0
   ```
   where `j_!` is **extension by zero** (the left adjoint of restriction `j^*` for the
   open embedding `j : U ↪ X`).
3. Apply the **covariant long exact sequence of Ext** (which IS in Mathlib as
   `Ext.covariantSequence_exact`) to this short exact sequence, obtaining:
   ```
   ⋯ → Ext(ℤ_X, j_!(F|_U), n) → Ext(ℤ_X, F, n) → Ext(ℤ_X, i_*(F|_Z), n) → ⋯
   ```
4. Show that `Ext(ℤ_X, j_!(F|_U), n) ≅ H^n(U, F|_U)` and
   `Ext(ℤ_X, i_*(F|_Z), n) ≅ H^n(Z, F|_Z)`, then apply `ih_irred` (for Y₁ ⊇ U)
   and induction on the number of components (for Z).

### Three critical pieces missing from Mathlib

**1. Extension by zero (`j_!`)**: The functor `j_! : Sh(U) → Sh(X)` for an open
embedding `j : U ↪ X` is not defined in Mathlib. For sheaves of abelian groups on a
topological space, `(j_! F)(V) = F(V)` if `V ⊆ U` and `0` otherwise (then sheafify).
Equivalently, `(j_! F)_x = F_x` if `x ∈ U` and `0` otherwise.

**2. The closed-open complement exact sequence**: The short exact sequence
`0 → j_!(F|_U) → F → i_*(F|_Z) → 0` requires `j_!` to even state.

**3. The identification `H'(⊤, F) ≅ H(F)`**: Mathlib defines:
  - `Sheaf.H F n = Ext(constantSheaf(ℤ), F, n)` (global cohomology)
  - `Sheaf.H' F n U = Ext(freeAbSheaf(yoneda(U)), F, n)` (cohomology presheaf)
  The Mayer-Vietoris LES in Mathlib (`MayerVietorisSquare.sequence_exact`) works with
  `H'`, not `H`. Identifying `H'(⊤, F) ≅ H(F)` is listed as a TODO in
  `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.

### Why the suggested alternative approaches fail

**Mayer-Vietoris for open covers** (`Opens.mayerVietorisSquare`):
The Mayer-Vietoris LES in Mathlib gives exactness for `H'` (cohomology presheaf), not
for global `H`. Even if we found opens `U, V` with `U ⊔ V = ⊤`, we would need the
identification `H'(⊤, F) ≅ H(F)` (missing piece #3). Moreover, for the inductive step,
we'd need `H'(U, F) ≅ H(F|_U)` to apply `ih_irred` to the restrictions, which is
another unformalized identification.

**Induction on irreducible components** (`NoetherianSpace.finite_irreducibleComponents`):
This gives `Set.Finite (irreducibleComponents X)`, but the inductive step still requires
relating `H^n(X, F)` to `H^n(Y₁, -)` and `H^n(Z, -)` via an exact sequence — which
brings us back to needing `j_!`.

**Covariant Ext LES** (`Ext.covariantSequence_exact`):
This IS in Mathlib and gives the LES
`Ext(ℤ, S.X₁, n) → Ext(ℤ, S.X₂, n) → Ext(ℤ, S.X₃, n) → ⋯`
for any short exact `S` in the sheaf category. But to USE it for Grothendieck vanishing,
we need to construct the short exact sequence `0 → j_!(F|_U) → F → i_*(F|_Z) → 0`,
which requires `j_!` (missing piece #1).

### What would be needed to fill this sorry

Any ONE of the following would suffice (combined with the existing Ext LES):
- Define `j_!` for open embeddings and prove the closed-open complement exact sequence
- Formalize the identification `H'(⊤, F) ≅ H(F)` (to use Mayer-Vietoris for `H'`)
- Formalize Čech cohomology and prove it agrees with derived functor cohomology for
  paracompact or Noetherian spaces
-/
theorem sheaf_H_subsingleton_of_reducible
    (X : TopCat.{u}) [NoetherianSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hNotIrred : ¬ IrreducibleSpace X) [Nonempty X]
    (ih_irred : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      [IrreducibleSpace Y] (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y ≤ topologicalKrullDim X →
      n > topologicalKrullDim Y → Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H F n) := by
  /- BLOCKED: This sorry cannot be filled without infrastructure that is not yet in Mathlib.
     See the module docstring above for a detailed analysis of:
     - Why the standard proof requires extension by zero (j_!)
     - Why the three suggested alternative approaches (Mayer-Vietoris, induction on
       components, covariant Ext LES) all ultimately reduce to needing j_!
     - What specific Mathlib additions would unblock this proof

     The covariant Ext LES (`Ext.covariantSequence_exact`) IS available in Mathlib,
     and the Mayer-Vietoris LES for `H'` (`MayerVietorisSquare.sequence_exact`) IS
     available. The bottleneck is constructing the right short exact sequence of sheaves
     (requires j_!) or identifying `H' ⊤` with `H` (a TODO in Mathlib). -/
  sorry
