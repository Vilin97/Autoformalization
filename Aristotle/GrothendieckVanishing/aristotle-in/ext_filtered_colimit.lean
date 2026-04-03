-- Harmonic `generalize_proofs` tactic
import Mathlib

/-!
# Ext vanishing passes through filtered colimits

In a Grothendieck abelian category, if `K = colim K_j` (filtered colimit) and
`Ext^n(Z, K_j) = 0` for all `j`, and `Hom(Z, -)` universally transfers subsingleton
for filtered colimits, then `Ext^n(Z, K) = 0`.

## Key Mathlib tools:
- `IsGrothendieckAbelian.ab5OfSize`: filtered colimits are exact
- `IsGrothendieckAbelian.enoughInjectives`: enough injectives exist
- `Ext.covariant_sequence_exact₁/₃`: LES for Ext
- `Ext.subsingleton_of_injective`: Ext^n(Z, I) = 0 for injective I, n ≥ 1
- `IsFiltered.max/leftToMax/rightToMax`: filtered diagram structure
- `cokernel.map/cokernel.π_desc/cokernel.condition`: cokernel API

## Proof strategy:
Induction on n with n quantified BEFORE J (so IH is universal over all filtered diagrams).
Base case (n=0): use hHom_univ + Ext.homEquiv₀.
Inductive step: embed c.pt ↪ I (injective), form quotient functor j ↦ cokernel(c.ι.app j ≫ ι),
show it's a colimit (by AB5), show per-j vanishing (by LES), apply IH.
-/

universe u v w

open CategoryTheory Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
  [IsGrothendieckAbelian.{w} C] [HasExt.{max u v} C]

theorem ext_vanishing_of_filtered_colimit
    (Z : C)
    (hHom_univ : ∀ {J : Type w} [SmallCategory J] [IsFiltered J]
      (Y : J ⥤ C) (c : Cocone Y), IsColimit c →
      (∀ j, Subsingleton (Z ⟶ Y.obj j)) → Subsingleton (Z ⟶ c.pt))
    (n : ℕ) {J : Type w} [SmallCategory J] [IsFiltered J]
    (Y : J ⥤ C) (c : Cocone Y) (hc : IsColimit c)
    (hvan : ∀ j, Subsingleton (Ext Z (Y.obj j) n)) :
    Subsingleton (Ext Z c.pt n) := by
  sorry
