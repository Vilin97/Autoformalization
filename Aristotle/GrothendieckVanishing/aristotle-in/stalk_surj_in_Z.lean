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

/-- For x ∈ Z, the stalk map of the adjunction unit η : F → i_*(i^*F) is surjective.

    The proof uses:
    1. stalkPushforward is an iso for inducing maps (stalkPushforward_iso_of_isInducing)
    2. The composition η_stalk ≫ stalkPushforward = pullbackStalkIso (an iso)
    3. Surjective(composition) + Injective(stalkPushforward) → Surjective(η_stalk)

    For step 2: stalkPushforward_germ gives the germ-level compatibility.
    At germs: η_stalk sends germ_U(t) to germ_U(η(U)(t)).
    stalkPushforward sends germ_U(η(U)(t)) to germ_{i⁻¹(U)}(η(U)(t)).
    And pullbackStalkIso sends germ_U(t) to germ_{i⁻¹(U)}(presheaf_pullback_unit(t)).
    These should be equal since η(U)(t) is the pushforward-pullback adjunction unit
    which at the presheaf level IS the restriction/pullback map.
-/
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 80000 in
theorem stalk_surj_unit_in_Z
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    [NoetherianSpace X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (x : X) (hxZ : x ∈ Z) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i
    Function.Surjective
      (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (adj.unit.app F).val)) := by
  sorry
