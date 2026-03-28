import Mathlib

-- Harmonic `generalize_proofs` tactic

universe u

open CategoryTheory TopologicalSpace Limits

instance : HasSeparator AddCommGrpCat.{u} where
  hasSeparator := by
    use AddCommGrpCat.of (ULift ℤ)
    intro A B f g h
    simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, forall_eq',
      ULift.forall]
    intro x
    specialize h (AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun y => y • x) fun y z => by simp only [add_smul])) 1
    aesop

instance : IsGrothendieckAbelian.{u} AddCommGrpCat.{u} where

instance (X : TopCat.{u}) : Abelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

instance (X : TopCat.{u}) : IsGrothendieckAbelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (IsGrothendieckAbelian (CategoryTheory.Sheaf _ _))

set_option synthInstance.maxHeartbeats 80000 in
/-- Grothendieck's vanishing theorem (Hartshorne III, Theorem 2.7).

    For a Noetherian topological space X of dimension d, and any sheaf F
    of abelian groups on X, H^n(X, F) = 0 for all n > d.

    IMPORTANT: flasque → injective is FALSE (ℤ on point is flasque but not injective).
    The correct approach uses:
    1. Induction on topologicalKrullDim X (well-founded on WithBot ℕ∞)
    2. Dim 0 case: constant sheaf is projective → Ext vanishes (already proved elsewhere)
    3. Irreducible dim ≥ 1: needs closed-open SES with j_! or Mayer-Vietoris
    4. Reducible: induction on irreducible components

    Key Mathlib tools:
    - Ext covariant LES: Ext.covariant_sequence_exact₁, covariantSequence_exact
    - Mayer-Vietoris: Opens.mayerVietorisSquare
    - IsPushout.exact_shortComplex for exact sequences from pushout squares
    - Sheaf pushforward: TopCat.Sheaf.pushforward for continuous maps
    - NoetherianSpace.finite_irreducibleComponents
    - HasProjectiveDimensionLT.subsingleton for Ext vanishing

    Alternative approaches that DON'T need j_!:
    - Čech-to-derived spectral sequence (not in Mathlib)
    - Direct limit approach via Prop 2.9 (not in Mathlib)
    - Noetherian induction on closed subsets with the Ext LES -/
theorem FlasqueVanishing (X : TopCat.{u}) [NoetherianSpace X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (hn : n > topologicalKrullDim X) :
    Subsingleton (Sheaf.H F n) := by
  sorry
