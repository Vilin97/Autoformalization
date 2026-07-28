/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.UniversalCoverDominatesPerfectCover

/-!
# Automorphisms of universal central extensions

An automorphism of the target of a universal central extension lifts
uniquely to its source.  Twisting the target projection makes this a direct
application of the universal property.  Uniqueness then proves that the
lifts form a group homomorphism.

For a perfect central cover of a nonabelian simple group, every
automorphism of the cover induces an automorphism of the simple quotient.
The universal lift of that quotient automorphism intertwines the canonical
map from the universal cover with the original cover automorphism.
-/

noncomputable section

open Subgroup QuotientGroup
open scoped IsMulCommutative

universe u

namespace McKayConjecture
namespace GroupTheory

namespace CentralExtension

variable {U S : Type u} [Group U] [Group S]

/-- Twist the projection of a central extension by a target
automorphism. -/
def targetTwist
    (E : CentralExtension U S) (β : MulAut S) :
    CentralExtension U S where
  projection :=
    β.symm.toMonoidHom.comp E.projection
  surjective :=
    β.symm.surjective.comp E.surjective
  ker_le_center := by
    intro u hu
    apply E.ker_le_center
    rw [MonoidHom.mem_ker] at hu ⊢
    change β.symm (E.projection u) = 1 at hu
    apply β.symm.injective
    simpa using hu

@[simp]
theorem targetTwist_projection_apply
    (E : CentralExtension U S) (β : MulAut S) (u : U) :
    (E.targetTwist β).projection u =
      β.symm (E.projection u) :=
  rfl

end CentralExtension

namespace UniversalCentralExtension

variable {U S : Type u} [Group U] [Group S]

/-- The homomorphism obtained by applying universality to the projection
twisted by `β`. -/
def targetAutomorphismLiftHom
    (E : UniversalCentralExtension U S) (β : MulAut S) :
    U →* U :=
  Classical.choose
    (E.lift U (E.toCentralExtension.targetTwist β))

/-- The lifted homomorphism induces `β` on the target. -/
theorem projection_targetAutomorphismLiftHom
    (E : UniversalCentralExtension U S) (β : MulAut S) :
    E.toCentralExtension.projection.comp
        (E.targetAutomorphismLiftHom β) =
      β.toMonoidHom.comp
        E.toCentralExtension.projection := by
  ext u
  have h :=
    DFunLike.congr_fun
      (Classical.choose_spec
        (E.lift U
          (E.toCentralExtension.targetTwist β))).1 u
  change
    β.symm
        (E.toCentralExtension.projection
          (E.targetAutomorphismLiftHom β u)) =
      E.toCentralExtension.projection u at h
  exact β.symm.injective (by simpa using h)

/-- Uniqueness of the lift in the form convenient for computations. -/
theorem targetAutomorphismLiftHom_unique
    (E : UniversalCentralExtension U S) (β : MulAut S)
    (f : U →* U)
    (hf :
      E.toCentralExtension.projection.comp f =
        β.toMonoidHom.comp
          E.toCentralExtension.projection) :
    f = E.targetAutomorphismLiftHom β := by
  apply
    (Classical.choose_spec
      (E.lift U
        (E.toCentralExtension.targetTwist β))).2
  ext u
  change
    β.symm
        (E.toCentralExtension.projection (f u)) =
      E.toCentralExtension.projection u
  have hu := DFunLike.congr_fun hf u
  change
    E.toCentralExtension.projection (f u) =
      β (E.toCentralExtension.projection u) at hu
  rw [hu, β.symm_apply_apply]

/-- The lift of the identity is the identity. -/
theorem targetAutomorphismLiftHom_one
    (E : UniversalCentralExtension U S) :
    E.targetAutomorphismLiftHom 1 =
      MonoidHom.id U := by
  symm
  apply E.targetAutomorphismLiftHom_unique 1
  ext u
  rfl

/-- Universal lifts respect multiplication of target automorphisms. -/
theorem targetAutomorphismLiftHom_mul
    (E : UniversalCentralExtension U S)
    (β γ : MulAut S) :
    E.targetAutomorphismLiftHom (β * γ) =
      (E.targetAutomorphismLiftHom β).comp
        (E.targetAutomorphismLiftHom γ) := by
  symm
  apply E.targetAutomorphismLiftHom_unique (β * γ)
  ext u
  calc
    E.toCentralExtension.projection
          (E.targetAutomorphismLiftHom β
            (E.targetAutomorphismLiftHom γ u)) =
        β
          (E.toCentralExtension.projection
            (E.targetAutomorphismLiftHom γ u)) := by
      have h :=
        DFunLike.congr_fun
          (E.projection_targetAutomorphismLiftHom β)
          (E.targetAutomorphismLiftHom γ u)
      simpa only [
        MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom] using h
    _ =
        β
          (γ (E.toCentralExtension.projection u)) := by
      have h :=
        DFunLike.congr_fun
          (E.projection_targetAutomorphismLiftHom γ) u
      change
        E.toCentralExtension.projection
            (E.targetAutomorphismLiftHom γ u) =
          γ (E.toCentralExtension.projection u) at h
      rw [h]
    _ =
        (β * γ)
          (E.toCentralExtension.projection u) :=
      rfl

/-- The canonical lift as an automorphism of the universal cover. -/
def targetAutomorphismLift
    (E : UniversalCentralExtension U S) (β : MulAut S) :
    MulAut U where
  toFun := E.targetAutomorphismLiftHom β
  invFun := E.targetAutomorphismLiftHom β⁻¹
  left_inv u := by
    have h :=
      congrArg (fun f : U →* U ↦ f u)
        (E.targetAutomorphismLiftHom_mul β⁻¹ β)
    simpa [E.targetAutomorphismLiftHom_one] using h.symm
  right_inv u := by
    have h :=
      congrArg (fun f : U →* U ↦ f u)
        (E.targetAutomorphismLiftHom_mul β β⁻¹)
    simpa [E.targetAutomorphismLiftHom_one] using h.symm
  map_mul' :=
    (E.targetAutomorphismLiftHom β).map_mul

@[simp]
theorem targetAutomorphismLift_apply
    (E : UniversalCentralExtension U S)
    (β : MulAut S) (u : U) :
    E.targetAutomorphismLift β u =
      E.targetAutomorphismLiftHom β u :=
  rfl

/-- Canonical lifting is a homomorphism of automorphism groups. -/
def targetAutomorphismLiftMonoidHom
    (E : UniversalCentralExtension U S) :
    MulAut S →* MulAut U where
  toFun := E.targetAutomorphismLift
  map_one' := by
    ext u
    exact
      congrArg (fun f : U →* U ↦ f u)
        E.targetAutomorphismLiftHom_one
  map_mul' β γ := by
    ext u
    exact
      congrArg (fun f : U →* U ↦ f u)
        (E.targetAutomorphismLiftHom_mul β γ)

/-- The canonical automorphism lift commutes with projection. -/
theorem projection_targetAutomorphismLift
    (E : UniversalCentralExtension U S)
    (β : MulAut S) (u : U) :
    E.toCentralExtension.projection
        (E.targetAutomorphismLift β u) =
      β (E.toCentralExtension.projection u) :=
  DFunLike.congr_fun
    (E.projection_targetAutomorphismLiftHom β) u

end UniversalCentralExtension

namespace CentralExtension

variable {A S : Type u} [Group A] [Group S]

/-- An automorphism of a central cover induces an automorphism of its
centerless simple target. -/
def inducedTargetAutomorphism
    (F : CentralExtension A S)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S)
    (α : MulAut A) :
    MulAut S :=
  let e := F.quotientCenterEquiv hs hnoncomm
  e.symm.trans <|
    (QuotientGroup.congr
      (Subgroup.center A) (Subgroup.center A)
      α (map_center_mulEquiv α)).trans e

/-- The induced target automorphism is characterized by commuting with the
cover projection. -/
theorem inducedTargetAutomorphism_projection
    (F : CentralExtension A S)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S)
    (α : MulAut A) (a : A) :
    F.inducedTargetAutomorphism hs hnoncomm α
        (F.projection a) =
      F.projection (α a) := by
  let e := F.quotientCenterEquiv hs hnoncomm
  change
    e
        (QuotientGroup.congr
          (Subgroup.center A) (Subgroup.center A)
          α (map_center_mulEquiv α)
          (e.symm (F.projection a))) =
      F.projection (α a)
  have ha :
      e.symm (F.projection a) =
        QuotientGroup.mk a := by
    apply e.injective
    rw [e.apply_symm_apply]
    rfl
  rw [ha]
  rfl

/-- Passage from cover automorphisms to target automorphisms is a group
homomorphism. -/
def inducedTargetAutomorphismMonoidHom
    (F : CentralExtension A S)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S) :
    MulAut A →* MulAut S where
  toFun := F.inducedTargetAutomorphism hs hnoncomm
  map_one' := by
    ext s
    obtain ⟨a, rfl⟩ := F.surjective s
    rw [F.inducedTargetAutomorphism_projection]
    rfl
  map_mul' α β := by
    ext s
    obtain ⟨a, rfl⟩ := F.surjective s
    calc
      F.inducedTargetAutomorphism hs hnoncomm (α * β)
            (F.projection a) =
          F.projection ((α * β) a) :=
        F.inducedTargetAutomorphism_projection
          hs hnoncomm (α * β) a
      _ = F.projection (α (β a)) :=
        rfl
      _ =
          F.inducedTargetAutomorphism hs hnoncomm α
            (F.projection (β a)) :=
        (F.inducedTargetAutomorphism_projection
          hs hnoncomm α (β a)).symm
      _ =
          F.inducedTargetAutomorphism hs hnoncomm α
            (F.inducedTargetAutomorphism hs hnoncomm β
              (F.projection a)) := by
        exact congrArg
          (F.inducedTargetAutomorphism hs hnoncomm α)
          (F.inducedTargetAutomorphism_projection
            hs hnoncomm β a).symm
      _ =
          (F.inducedTargetAutomorphism hs hnoncomm α *
            F.inducedTargetAutomorphism hs hnoncomm β)
              (F.projection a) :=
        rfl

end CentralExtension

namespace UniversalCentralExtension

variable {U S A : Type u}
variable [Group U] [Group S] [Group A]

/-- The universal lift of the target automorphism induced by `α`
intertwines the canonical map to the central cover with `α`. -/
theorem targetAutomorphismLift_intertwines_mapToCentralExtension
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S)
    (α : MulAut A) :
    (E.mapToCentralExtension F).comp
        (E.targetAutomorphismLift
          (F.inducedTargetAutomorphism hs hnoncomm α)).toMonoidHom =
      α.toMonoidHom.comp
        (E.mapToCentralExtension F) := by
  let β : MulAut S :=
    F.inducedTargetAutomorphism hs hnoncomm α
  let T : CentralExtension A S :=
    F.targetTwist β
  let f : U →* A :=
    (E.mapToCentralExtension F).comp
      (E.targetAutomorphismLift β).toMonoidHom
  let g : U →* A :=
    α.toMonoidHom.comp (E.mapToCentralExtension F)
  have hf :
      T.projection.comp f =
        E.toCentralExtension.projection := by
    ext u
    change
      β.symm
          (F.projection
            (E.mapToCentralExtension F
              (E.targetAutomorphismLift β u))) =
        E.toCentralExtension.projection u
    have hmap :=
      DFunLike.congr_fun
        (E.mapToCentralExtension_commutes F)
        (E.targetAutomorphismLift β u)
    change
      F.projection
          (E.mapToCentralExtension F
            (E.targetAutomorphismLift β u)) =
        E.toCentralExtension.projection
          (E.targetAutomorphismLift β u) at hmap
    rw [hmap, E.projection_targetAutomorphismLift,
      β.symm_apply_apply]
  have hg :
      T.projection.comp g =
        E.toCentralExtension.projection := by
    ext u
    change
      β.symm
          (F.projection
            (α (E.mapToCentralExtension F u))) =
        E.toCentralExtension.projection u
    rw [← F.inducedTargetAutomorphism_projection
      hs hnoncomm α]
    change
      β.symm
          (β
            (F.projection
              (E.mapToCentralExtension F u))) =
        E.toCentralExtension.projection u
    rw [β.symm_apply_apply]
    exact
      DFunLike.congr_fun
        (E.mapToCentralExtension_commutes F) u
  change f = g
  exact
    (E.mapToCentralExtension_unique T f hf).trans
      (E.mapToCentralExtension_unique T g hg).symm

end UniversalCentralExtension
end GroupTheory
end McKayConjecture
