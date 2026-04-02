-- Harmonic `generalize_proofs` tactic
import Mathlib

/-!
# Ext vanishing passes through filtered colimits of monomorphisms

In a Grothendieck abelian category, if `K = colim K_j` (filtered colimit with mono
transition maps) and `Ext^n(Z, K_j) = 0` for all `j`, then `Ext^n(Z, K) = 0`.

## Key available Mathlib tools:
- `IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono`: Hom(X,-) preserves
  colimits of mono diagrams (gives the n=0 case)
- `IsGrothendieckAbelian.ab5OfSize`: filtered colimits are exact
- `IsGrothendieckAbelian.enoughInjectives`: enough injectives exist
- `Ext.covariant_sequence_exact₁/₂`: LES for Ext
- `Ext.subsingleton_of_injective`: Ext^n(Z, I) = 0 for injective I, n ≥ 1

## Proof strategy:
Induction on n. Base case (n=0): use `preservesColimit_coyoneda_obj_of_mono`.
Inductive step: for each j, embed K_j ↪ I_j (injective). Use dimension shifting
via LES: Ext^n(Z, K_j) ≅ Ext^{n-1}(Z, I_j/K_j). The system {I_j/K_j} inherits
the vanishing, and by IH we conclude.
-/

universe u v w

open CategoryTheory Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
  [IsGrothendieckAbelian.{w} C] [HasExt.{max u v} C]

theorem ext_vanishing_of_filtered_colimit_vanishing
    {J : Type w} [SmallCategory J] [IsFiltered J]
    (Y : J ⥤ C) (c : Cocone Y) (hc : IsColimit c)
    [∀ (j j' : J) (φ : j ⟶ j'), Mono (Y.map φ)]
    (Z : C) (n : ℕ)
    (hvan : ∀ j, Subsingleton (Ext Z (Y.obj j) n)) :
    Subsingleton (Ext Z c.pt n) := by
  sorry
