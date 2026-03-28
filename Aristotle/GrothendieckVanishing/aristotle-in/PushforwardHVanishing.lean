-- Harmonic `generalize_proofs` tactic
import Mathlib

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

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
  inferInstanceAs (Abelian (Sheaf _ _))

instance (X : TopCat.{u}) : IsGrothendieckAbelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (IsGrothendieckAbelian (Sheaf _ _))

/-- Pushforward along closed immersion preserves cohomological vanishing.

    KEY FACT: (i_*G)(⊤_X) = G(⊤_Z) by rfl for closed immersion i : Z ↪ X.
    Also: (i_*g)(⊤_X) = g(⊤_Z) by rfl for morphisms g on Z.

    Proof approach: For n ≥ 1, take injective presentation on Z:
    0 → G → I_Z → Q_Z → 0. If i_* is exact, this gives SES on X:
    0 → i_*G → i_*I_Z → i_*Q_Z → 0.
    i_*I_Z is flasque (pushforward preserves flasqueness since I_Z is
    injective hence flasque). By FlasqueVanishing, H^m(X, i_*I_Z) = 0
    for m ≥ 1. The LES + Γ equality + induction gives the result.

    Alternative: Use Ext adjunction Ext^n(Z_X, i_*G) ≅ Ext^n(Z_Z, G) via
    the Hom identity Hom(Z_X, i_*G) = Hom(M, Γ_X(i_*G)) = Hom(M, G(⊤_Z))
    = Hom(Z_Z, G) and derived functor comparison. -/
set_option synthInstance.maxHeartbeats 80000 in
theorem PushforwardHVanishing
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    [NoetherianSpace X]
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)) (n : ℕ)
    (h : Subsingleton (Sheaf.H G n)) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) n) := by
  sorry
