-- Harmonic `generalize_proofs` tactic
import Mathlib

/-!
# Sheaf cohomology commutes with filtered colimits on Noetherian spaces

On a Noetherian topological space X, if F = colim F_j is a filtered colimit of sheaves
and H^n(X, F_j) = 0 for all j, then H^n(X, F) = 0.

This is the derived functor commutation theorem for the global sections functor Γ:
R^n Γ preserves filtered colimits.

## Proof strategy (any of these should work):

### Strategy A: Via AB5 + sections
1. Show filtered presheaf colimits of sheaves are sheaves (AB5 for Noetherian spaces:
   sheaf condition = finite limit, filtered colimits commute with finite limits)
2. This gives CreatesColimit for sheafToPresheaf on filtered diagrams
3. Combined with evaluation preserving colimits: sections at each U are colimits
4. Use this to show Γ preserves filtered colimits, then bootstrap to R^n Γ

### Strategy B: Via Čech cohomology
1. On Noetherian spaces, use finite open covers
2. Čech complex terms are finite products of sections → commute with filtered colimits
3. Čech cohomology = derived functor cohomology (comparison theorem)

### Strategy C: Direct via injective resolutions
1. For each F_j, take injective resolution I_j^*
2. colim I_j^* is an injective resolution of colim F_j (AB5 + filtered colimits of
   injectives are injective in Grothendieck abelian categories)
3. H^n(colim F_j) = H^n(Γ(colim I_j^*)) = H^n(colim Γ(I_j^*))
   = colim H^n(Γ(I_j^*)) = colim H^n(F_j) = 0

## Relevant Mathlib tools:
- `Sheaf.createsColimitOfIsSheaf`: creates colimit if presheaf colimit is a sheaf
- `evaluation_preservesColimit`: evaluation at U preserves colimits
- `IsGrothendieckAbelian.ab5OfSize`: filtered colimits are exact
- `Concrete.isColimit_exists_rep`: elements of concrete colimits factor through pieces
- `NoetherianSpace`: every open cover has a finite subcover
-/

universe u

open CategoryTheory TopologicalSpace Limits Opposite

theorem sheafH_preserves_filtered_colimits
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c')
    (n : ℕ)
    (hvan : ∀ j, Subsingleton (Sheaf.H (Y'.obj j) n)) :
    Subsingleton (Sheaf.H c'.pt n) := by
  sorry
