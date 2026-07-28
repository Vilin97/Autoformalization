/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Index
import McKayConjecture.GroupTheory.LayerLocalNormalizerContainment
import McKayConjecture.GroupTheory.UniversalCentralExtension

/-!
# Sylow normalizers in finite-source central extensions

A surjective homomorphism with central kernel gives a bijection on Sylow
subgroups.  Thus a central extension `U → Q` with finite source has a unique
Sylow lift of every Sylow subgroup of `Q`.

The projection also maps the normalizer of the lifted Sylow subgroup onto the
normalizer downstairs.  Surjectivity is stronger than the general forward
normalizer containment: after choosing any lift of a target normalizer
element, uniqueness of the Sylow lift forces that element to normalize the
chosen source Sylow subgroup.  The restricted projection is itself a central
extension.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace GroupTheory
namespace CentralExtension

variable {U : Type u} {Q : Type v}
variable [Group U] [Group Q] [Finite U]
variable {p : ℕ} [Fact p.Prime]

/-- The bijection on Sylow subgroups induced by a finite-source central
extension. -/
def sylowMapEquiv (E : CentralExtension U Q) :
    Sylow p U ≃ Sylow p Q :=
  Equiv.ofBijective
    (Sylow.mapSurjective E.surjective)
    (Sylow.mapSurjective_bijective_of_ker_le_center
      E.surjective E.ker_le_center)

@[simp]
theorem sylowMapEquiv_apply
    (E : CentralExtension U Q) (P : Sylow p U) :
    E.sylowMapEquiv P =
      P.mapSurjective E.surjective :=
  rfl

/-- The unique Sylow subgroup of the source mapping onto `S`. -/
def sylowLift
    (E : CentralExtension U Q) (S : Sylow p Q) :
    Sylow p U :=
  E.sylowMapEquiv.symm S

@[simp]
theorem sylowLift_mapSurjective
    (E : CentralExtension U Q) (S : Sylow p Q) :
    (E.sylowLift S).mapSurjective E.surjective = S := by
  change
    E.sylowMapEquiv (E.sylowMapEquiv.symm S) = S
  exact E.sylowMapEquiv.apply_symm_apply S

/-- The underlying subgroup of the Sylow lift maps exactly to the requested
target Sylow subgroup. -/
@[simp]
theorem sylowLift_map
    (E : CentralExtension U Q) (S : Sylow p Q) :
    (E.sylowLift S : Subgroup U).map E.projection =
      (S : Subgroup Q) := by
  have h :=
    congrArg
      (fun R : Sylow p Q ↦ (R : Subgroup Q))
      (E.sylowLift_mapSurjective S)
  exact h

/-- Characterization of the unique Sylow lift. -/
theorem eq_sylowLift_iff_mapSurjective_eq
    (E : CentralExtension U Q) (S : Sylow p Q)
    (P : Sylow p U) :
    P = E.sylowLift S ↔
      P.mapSurjective E.surjective = S := by
  constructor
  · rintro rfl
    exact E.sylowLift_mapSurjective S
  · intro hP
    apply E.sylowMapEquiv.injective
    simpa using hP

/-- The central kernel is contained in the normalizer of every lifted Sylow
subgroup. -/
theorem ker_le_sylowLift_normalizer
    (E : CentralExtension U Q) (S : Sylow p Q) :
    E.projection.ker ≤
      Subgroup.normalizer (E.sylowLift S : Set U) :=
  E.ker_le_center.trans
    (Subgroup.center_le_normalizer
      (E.sylowLift S : Set U))

/-- The image of an element normalizing the Sylow lift normalizes the target
Sylow subgroup. -/
theorem projection_mem_sylowNormalizer
    (E : CentralExtension U Q) (S : Sylow p Q)
    (x :
      Subgroup.normalizer (E.sylowLift S : Set U)) :
    E.projection (x : U) ∈
      Subgroup.normalizer (S : Set Q) := by
  have hx :
      (x : U) • E.sylowLift S =
        E.sylowLift S :=
    Sylow.smul_eq_iff_mem_normalizer.mpr x.property
  have hmap :=
    congrArg
      (fun P : Sylow p U ↦
        P.mapSurjective E.surjective)
      hx
  rw [Sylow.mapSurjective_smul,
    E.sylowLift_mapSurjective] at hmap
  exact Sylow.smul_eq_iff_mem_normalizer.mp hmap

/-- The projection restricted from the lifted Sylow normalizer to the target
Sylow normalizer. -/
def sylowNormalizerProjection
    (E : CentralExtension U Q) (S : Sylow p Q) :
    Subgroup.normalizer (E.sylowLift S : Set U) →*
      Subgroup.normalizer (S : Set Q) :=
  (E.projection.domRestrict
      (Subgroup.normalizer
        (E.sylowLift S : Set U))).codRestrict
    (Subgroup.normalizer (S : Set Q))
    (E.projection_mem_sylowNormalizer S)

@[simp]
theorem sylowNormalizerProjection_apply_coe
    (E : CentralExtension U Q) (S : Sylow p Q)
    (x :
      Subgroup.normalizer (E.sylowLift S : Set U)) :
    ((E.sylowNormalizerProjection S x :
        Subgroup.normalizer (S : Set Q)) : Q) =
      E.projection (x : U) :=
  rfl

/-- Every target Sylow-normalizer element has a lift in the source
Sylow normalizer. -/
theorem sylowNormalizerProjection_surjective
    (E : CentralExtension U Q) (S : Sylow p Q) :
    Function.Surjective
      (E.sylowNormalizerProjection S) := by
  intro y
  obtain ⟨x, hx⟩ :=
    E.surjective (y : Q)
  have hxNormalizer :
      x ∈
        Subgroup.normalizer
          (E.sylowLift S : Set U) := by
    apply
      Sylow.mem_normalizer_of_mapSurjective_mem_normalizer_of_ker_le_center
        E.surjective E.ker_le_center
        (E.sylowLift S) x
    rw [E.sylowLift_mapSurjective, hx]
    exact y.property
  refine ⟨⟨x, hxNormalizer⟩, ?_⟩
  apply Subtype.ext
  exact hx

/-- The restricted normalizer projection has full range. -/
@[simp]
theorem sylowNormalizerProjection_range
    (E : CentralExtension U Q) (S : Sylow p Q) :
    (E.sylowNormalizerProjection S).range = ⊤ :=
  MonoidHom.range_eq_top.mpr
    (E.sylowNormalizerProjection_surjective S)

/-- The kernel of the restricted normalizer projection is exactly the
original extension kernel, viewed inside the source normalizer. -/
@[simp]
theorem sylowNormalizerProjection_ker
    (E : CentralExtension U Q) (S : Sylow p Q) :
    (E.sylowNormalizerProjection S).ker =
      E.projection.ker.subgroupOf
        (Subgroup.normalizer
          (E.sylowLift S : Set U)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
    Subtype.ext_iff]
  rfl

theorem sylowNormalizerProjection_ker_le_center
    (E : CentralExtension U Q) (S : Sylow p Q) :
    (E.sylowNormalizerProjection S).ker ≤
      Subgroup.center
        (Subgroup.normalizer
          (E.sylowLift S : Set U)) := by
  intro x hx
  have hxKer :
      (x : U) ∈ E.projection.ker := by
    have hxOne :
        E.projection (x : U) = 1 := by
      exact
        congrArg Subtype.val
          (MonoidHom.mem_ker.mp hx)
    exact MonoidHom.mem_ker.mpr hxOne
  have hxCenter :
      (x : U) ∈ Subgroup.center U :=
    E.ker_le_center hxKer
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact
    Subgroup.mem_center_iff.mp hxCenter (y : U)

/-- Restricting a finite-source central extension to corresponding Sylow
normalizers gives another central extension. -/
def sylowNormalizerCentralExtension
    (E : CentralExtension U Q) (S : Sylow p Q) :
    CentralExtension
      (Subgroup.normalizer
        (E.sylowLift S : Set U))
      (Subgroup.normalizer (S : Set Q)) where
  projection := E.sylowNormalizerProjection S
  surjective := E.sylowNormalizerProjection_surjective S
  ker_le_center :=
    E.sylowNormalizerProjection_ker_le_center S

@[simp]
theorem sylowNormalizerCentralExtension_projection
    (E : CentralExtension U Q) (S : Sylow p Q) :
    (E.sylowNormalizerCentralExtension S).projection =
      E.sylowNormalizerProjection S :=
  rfl

@[simp]
theorem sylowNormalizerCentralExtension_projection_apply_coe
    (E : CentralExtension U Q) (S : Sylow p Q)
    (x :
      Subgroup.normalizer (E.sylowLift S : Set U)) :
    (((E.sylowNormalizerCentralExtension S).projection x :
        Subgroup.normalizer (S : Set Q)) : Q) =
      E.projection (x : U) :=
  rfl

@[simp]
theorem sylowNormalizerCentralExtension_projection_range
    (E : CentralExtension U Q) (S : Sylow p Q) :
    (E.sylowNormalizerCentralExtension S).projection.range = ⊤ :=
  E.sylowNormalizerProjection_range S

@[simp]
theorem sylowNormalizerCentralExtension_projection_ker
    (E : CentralExtension U Q) (S : Sylow p Q) :
    (E.sylowNormalizerCentralExtension S).projection.ker =
      E.projection.ker.subgroupOf
        (Subgroup.normalizer
          (E.sylowLift S : Set U)) :=
  E.sylowNormalizerProjection_ker S

/-- The target Sylow normalizer order divides the lifted Sylow normalizer
order. -/
theorem sylowNormalizer_card_dvd
    (E : CentralExtension U Q) (S : Sylow p Q) :
    Nat.card (Subgroup.normalizer (S : Set Q)) ∣
      Nat.card
        (Subgroup.normalizer
          (E.sylowLift S : Set U)) :=
  Subgroup.card_dvd_of_surjective
    (E.sylowNormalizerProjection S)
    (E.sylowNormalizerProjection_surjective S)

/-- Exact cardinality comparison for corresponding Sylow normalizers. -/
theorem sylowNormalizer_card_eq
    (E : CentralExtension U Q) (S : Sylow p Q) :
    Nat.card
        (Subgroup.normalizer
          (E.sylowLift S : Set U)) =
      Nat.card E.projection.ker *
        Nat.card
          (Subgroup.normalizer (S : Set Q)) := by
  let f := E.sylowNormalizerProjection S
  calc
    Nat.card
          (Subgroup.normalizer
            (E.sylowLift S : Set U)) =
        Nat.card f.ker * f.ker.index :=
      f.ker.card_mul_index.symm
    _ = Nat.card f.ker * Nat.card f.range := by
      rw [Subgroup.index_ker]
    _ = Nat.card f.ker *
          Nat.card
            (Subgroup.normalizer (S : Set Q)) := by
      rw [E.sylowNormalizerProjection_range S,
        Subgroup.card_top]
    _ = Nat.card E.projection.ker *
          Nat.card
            (Subgroup.normalizer (S : Set Q)) := by
      rw [E.sylowNormalizerProjection_ker S]
      congr 1
      exact
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe
            (E.ker_le_sylowLift_normalizer S)).toEquiv

/-- Corresponding Sylow subgroups have equal ambient normalizer indices. -/
theorem sylowLift_normalizer_index_eq
    (E : CentralExtension U Q) (S : Sylow p Q) :
    (Subgroup.normalizer
        (E.sylowLift S : Set U)).index =
      (Subgroup.normalizer (S : Set Q)).index := by
  letI : Finite Q :=
    Finite.of_surjective E.projection E.surjective
  calc
    (Subgroup.normalizer
          (E.sylowLift S : Set U)).index =
        Nat.card (Sylow p U) :=
      (Sylow.card_eq_index_normalizer
        (E.sylowLift S)).symm
    _ = Nat.card (Sylow p Q) :=
      Nat.card_congr E.sylowMapEquiv
    _ = (Subgroup.normalizer (S : Set Q)).index :=
      Sylow.card_eq_index_normalizer S

end CentralExtension
end GroupTheory
end McKayConjecture
