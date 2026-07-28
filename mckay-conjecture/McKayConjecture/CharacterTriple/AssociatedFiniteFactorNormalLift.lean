/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorCentralExtensionCharacter
import McKayConjecture.CharacterTriple.FactorSetCentralExtensionCoefficient
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The normal-subgroup lift in an associated finite-factor extension

Fix a character triple `T = (A, N, θ)`, an associated projective
representation, and one association-preserving finite-factor normalization.
Because the associated factor is one whenever either argument lies in `N`,
the base lifts `(n, 1)` form an honest normal copy of `N` in the ambient
factor-set extension.

This file packages that copy, describes conjugation on it, and identifies the
full inverse image of `N` under the extension projection as the join (and
setwise product) of the normal lift with the central coefficient subgroup.
It also records the two restrictions of the honest extension character:
`θ` on the normal lift and the defining scalar character on coefficients.
-/

noncomputable section

open scoped Pointwise

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedProjectiveRepresentation
namespace AssociatedFiniteFactorNormalization

variable {A : Type} [Group A] [Finite A]
variable {T : CharacterTriple A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}
variable (R : AssociatedProjectiveRepresentation T V P)

open FactorSet

/-- The projection from the ambient finite-factor extension to the ambient
group of the character triple. -/
abbrev ambientFactorProjection
    (F : AssociatedFiniteFactorNormalization R) :
    F.AmbientFactorCentralExtensionGroup R →* A :=
  CentralExtensionGroup.projection
    F.factorSet (F.factorSet_isNormalized R)

/-- The canonical honest lift `n ↦ (n, 1)` of the distinguished normal
subgroup into the ambient finite-factor extension. -/
def ambientNormalSubgroupLift
    (F : AssociatedFiniteFactorNormalization R) :
    T.normalSubgroup →*
      F.AmbientFactorCentralExtensionGroup R where
  toFun n :=
    CentralExtensionGroup.mk
      F.factorSet (F.factorSet_isNormalized R) (n : A) 1
  map_one' := rfl
  map_mul' n m := by
    apply CentralExtensionGroup.ext
    · rfl
    · simp only [CentralExtensionGroup.coefficient_mul,
        CentralExtensionGroup.base_mk,
        CentralExtensionGroup.coefficient_mk, mul_one]
      rw [
        (F.factorSet_isQuotientCompatible R).factor_normal_left
          n (m : A)]

@[simp]
theorem ambientNormalSubgroupLift_apply
    (F : AssociatedFiniteFactorNormalization R)
    (n : T.normalSubgroup) :
    F.ambientNormalSubgroupLift R n =
      CentralExtensionGroup.mk
        F.factorSet (F.factorSet_isNormalized R) (n : A) 1 :=
  rfl

@[simp]
theorem ambientNormalSubgroupLift_base
    (F : AssociatedFiniteFactorNormalization R)
    (n : T.normalSubgroup) :
    CentralExtensionGroup.base
        F.factorSet (F.factorSet_isNormalized R)
        (F.ambientNormalSubgroupLift R n) =
      (n : A) :=
  rfl

@[simp]
theorem ambientNormalSubgroupLift_coefficient
    (F : AssociatedFiniteFactorNormalization R)
    (n : T.normalSubgroup) :
    CentralExtensionGroup.coefficient
        F.factorSet (F.factorSet_isNormalized R)
        (F.ambientNormalSubgroupLift R n) =
      1 :=
  rfl

@[simp]
theorem ambientFactorProjection_normalSubgroupLift
    (F : AssociatedFiniteFactorNormalization R)
    (n : T.normalSubgroup) :
    F.ambientFactorProjection R
        (F.ambientNormalSubgroupLift R n) =
      (n : A) :=
  rfl

/-- Multiplying a normal lift by a coefficient element simply records the
two coordinates. -/
@[simp]
theorem ambientNormalSubgroupLift_mul_coefficientEmbedding
    (F : AssociatedFiniteFactorNormalization R)
    (n : T.normalSubgroup)
    (c : rootsOfUnity (associatedFactorExponent T V) ℂ) :
    F.ambientNormalSubgroupLift R n *
        CentralExtensionGroup.coefficientEmbedding
          F.factorSet (F.factorSet_isNormalized R) c =
      CentralExtensionGroup.mk
        F.factorSet (F.factorSet_isNormalized R) (n : A) c := by
  apply CentralExtensionGroup.ext
  · simp
  · simp only [CentralExtensionGroup.coefficient_mul,
      ambientNormalSubgroupLift_base,
      ambientNormalSubgroupLift_coefficient,
      CentralExtensionGroup.coefficientEmbedding_apply,
      CentralExtensionGroup.base_mk,
      CentralExtensionGroup.coefficient_mk]
    rw [(F.factorSet_isNormalized R).2 (n : A)]
    simp

/-- Coefficients are central, so the reversed coordinate product gives the
same element. -/
@[simp]
theorem coefficientEmbedding_mul_ambientNormalSubgroupLift
    (F : AssociatedFiniteFactorNormalization R)
    (c : rootsOfUnity (associatedFactorExponent T V) ℂ)
    (n : T.normalSubgroup) :
    CentralExtensionGroup.coefficientEmbedding
          F.factorSet (F.factorSet_isNormalized R) c *
        F.ambientNormalSubgroupLift R n =
      CentralExtensionGroup.mk
        F.factorSet (F.factorSet_isNormalized R) (n : A) c := by
  apply CentralExtensionGroup.ext
  · simp
  · simp only [CentralExtensionGroup.coefficient_mul,
      CentralExtensionGroup.coefficientEmbedding_apply,
      CentralExtensionGroup.base_mk,
      CentralExtensionGroup.coefficient_mk,
      ambientNormalSubgroupLift_base,
      ambientNormalSubgroupLift_coefficient, mul_one]
    rw [(F.factorSet_isNormalized R).1 (n : A)]
    simp

/-- Projection recovers the normal-subgroup element, so the canonical lift is
injective. -/
theorem ambientNormalSubgroupLift_injective
    (F : AssociatedFiniteFactorNormalization R) :
    Function.Injective (F.ambientNormalSubgroupLift R) := by
  intro n m hnm
  apply Subtype.ext
  exact congrArg
    (CentralExtensionGroup.base
      F.factorSet (F.factorSet_isNormalized R)) hnm

/-- The normal element obtained by conjugating with the base coordinate of an
ambient extension element. -/
def ambientNormalConjugate
    (F : AssociatedFiniteFactorNormalization R)
    (x : F.AmbientFactorCentralExtensionGroup R)
    (n : T.normalSubgroup) :
    T.normalSubgroup :=
  ⟨CentralExtensionGroup.base
        F.factorSet (F.factorSet_isNormalized R) x *
      (n : A) *
      (CentralExtensionGroup.base
        F.factorSet (F.factorSet_isNormalized R) x)⁻¹,
    (inferInstance : T.normalSubgroup.Normal).conj_mem
      n n.property
      (CentralExtensionGroup.base
        F.factorSet (F.factorSet_isNormalized R) x)⟩

@[simp]
theorem ambientNormalConjugate_coe
    (F : AssociatedFiniteFactorNormalization R)
    (x : F.AmbientFactorCentralExtensionGroup R)
    (n : T.normalSubgroup) :
    (F.ambientNormalConjugate R x n : A) =
      CentralExtensionGroup.base
          F.factorSet (F.factorSet_isNormalized R) x *
        (n : A) *
        (CentralExtensionGroup.base
          F.factorSet (F.factorSet_isNormalized R) x)⁻¹ :=
  rfl

/-- Moving a lifted normal element past an arbitrary extension element
conjugates it by the base coordinate. -/
theorem mul_ambientNormalSubgroupLift
    (F : AssociatedFiniteFactorNormalization R)
    (x : F.AmbientFactorCentralExtensionGroup R)
    (n : T.normalSubgroup) :
    x * F.ambientNormalSubgroupLift R n =
      F.ambientNormalSubgroupLift R
          (F.ambientNormalConjugate R x n) *
        x := by
  apply CentralExtensionGroup.ext
  · simp [ambientNormalConjugate, mul_assoc]
  · simp only [CentralExtensionGroup.coefficient_mul,
      ambientNormalSubgroupLift_base,
      ambientNormalSubgroupLift_coefficient, mul_one]
    rw [
      (F.factorSet_isQuotientCompatible R).factor_normal_right
        (CentralExtensionGroup.base
          F.factorSet (F.factorSet_isNormalized R) x) n,
      (F.factorSet_isQuotientCompatible R).factor_normal_left
        (F.ambientNormalConjugate R x n)
        (CentralExtensionGroup.base
          F.factorSet (F.factorSet_isNormalized R) x)]

/-- Conjugation in the factor extension restricts to ordinary ambient
conjugation on the canonical normal lift. -/
@[simp]
theorem conjugate_ambientNormalSubgroupLift
    (F : AssociatedFiniteFactorNormalization R)
    (x : F.AmbientFactorCentralExtensionGroup R)
    (n : T.normalSubgroup) :
    x * F.ambientNormalSubgroupLift R n * x⁻¹ =
      F.ambientNormalSubgroupLift R
        (F.ambientNormalConjugate R x n) := by
  rw [F.mul_ambientNormalSubgroupLift R x n]
  simp

/-- The range of the canonical normal-subgroup lift is normal in the full
ambient factor extension. -/
instance ambientNormalSubgroupLift_range_normal
    (F : AssociatedFiniteFactorNormalization R) :
    (F.ambientNormalSubgroupLift R).range.Normal where
  conj_mem := by
    intro y hy x
    obtain ⟨n, rfl⟩ := hy
    refine ⟨F.ambientNormalConjugate R x n, ?_⟩
    exact (F.conjugate_ambientNormalSubgroupLift R x n).symm

/-- The coefficient subgroup of the ambient finite-factor extension. -/
abbrev ambientFactorCoefficientSubgroup
    (F : AssociatedFiniteFactorNormalization R) :
    Subgroup (F.AmbientFactorCentralExtensionGroup R) :=
  CentralExtensionGroup.coefficientSubgroup
    F.factorSet (F.factorSet_isNormalized R)

/-- The coefficient subgroup is normal, since it is central. -/
instance ambientFactorCoefficientSubgroup_normal
    (F : AssociatedFiniteFactorNormalization R) :
    (F.ambientFactorCoefficientSubgroup R).Normal where
  conj_mem := by
    intro z hz x
    have hzCenter :=
      CentralExtensionGroup.coefficientSubgroup_le_center
        F.factorSet (F.factorSet_isNormalized R) hz
    rw [(Subgroup.mem_center_iff.mp hzCenter) x, mul_assoc,
      mul_inv_cancel, mul_one]
    exact hz

/-- The full inverse image of the distinguished normal subgroup under the
ambient extension projection. -/
abbrev ambientNormalPreimage
    (F : AssociatedFiniteFactorNormalization R) :
    Subgroup (F.AmbientFactorCentralExtensionGroup R) :=
  T.normalSubgroup.comap (F.ambientFactorProjection R)

/-- Normal-lift and coefficient coordinates reconstruct every element lying
above the distinguished normal subgroup. -/
theorem ambientNormalSubgroupLift_mul_coefficientEmbedding_eq
    (F : AssociatedFiniteFactorNormalization R)
    (x : F.AmbientFactorCentralExtensionGroup R)
    (hx : x ∈ F.ambientNormalPreimage R) :
    F.ambientNormalSubgroupLift R
          ⟨CentralExtensionGroup.base
              F.factorSet (F.factorSet_isNormalized R) x,
            hx⟩ *
        CentralExtensionGroup.coefficientEmbedding
          F.factorSet (F.factorSet_isNormalized R)
          (CentralExtensionGroup.coefficient
            F.factorSet (F.factorSet_isNormalized R) x) =
      x := by
  apply CentralExtensionGroup.ext
  · simp
  · simp only [CentralExtensionGroup.coefficient_mul,
      ambientNormalSubgroupLift_base,
      ambientNormalSubgroupLift_coefficient,
      CentralExtensionGroup.coefficientEmbedding_apply,
      CentralExtensionGroup.base_mk,
      CentralExtensionGroup.coefficient_mk]
    rw [
      (F.factorSet_isQuotientCompatible R).factor_normal_left
        ⟨CentralExtensionGroup.base
            F.factorSet (F.factorSet_isNormalized R) x,
          hx⟩ (1 : A)]
    simp

/-- The full projection preimage of `N` is generated by the normal lift of
`N` and the central coefficient subgroup. -/
theorem ambientNormalPreimage_eq_sup
    (F : AssociatedFiniteFactorNormalization R) :
    F.ambientNormalPreimage R =
      (F.ambientNormalSubgroupLift R).range ⊔
        F.ambientFactorCoefficientSubgroup R := by
  apply le_antisymm
  · intro x hx
    have hn :
        F.ambientNormalSubgroupLift R
            ⟨CentralExtensionGroup.base
                F.factorSet (F.factorSet_isNormalized R) x,
              hx⟩ ∈
          (F.ambientNormalSubgroupLift R).range :=
      ⟨_, rfl⟩
    have hc :
        CentralExtensionGroup.coefficientEmbedding
            F.factorSet (F.factorSet_isNormalized R)
            (CentralExtensionGroup.coefficient
              F.factorSet (F.factorSet_isNormalized R) x) ∈
          F.ambientFactorCoefficientSubgroup R :=
      ⟨_, rfl⟩
    rw [← F.ambientNormalSubgroupLift_mul_coefficientEmbedding_eq R x hx]
    exact Subgroup.mul_mem _
      (show
        F.ambientNormalSubgroupLift R
            ⟨CentralExtensionGroup.base
                F.factorSet (F.factorSet_isNormalized R) x,
              hx⟩ ∈
          (F.ambientNormalSubgroupLift R).range ⊔
            F.ambientFactorCoefficientSubgroup R from
        (show
          (F.ambientNormalSubgroupLift R).range ≤
            (F.ambientNormalSubgroupLift R).range ⊔
              F.ambientFactorCoefficientSubgroup R from
          le_sup_left) hn)
      (show
        CentralExtensionGroup.coefficientEmbedding
            F.factorSet (F.factorSet_isNormalized R)
            (CentralExtensionGroup.coefficient
              F.factorSet (F.factorSet_isNormalized R) x) ∈
          (F.ambientNormalSubgroupLift R).range ⊔
            F.ambientFactorCoefficientSubgroup R from
        (show
          F.ambientFactorCoefficientSubgroup R ≤
            (F.ambientNormalSubgroupLift R).range ⊔
              F.ambientFactorCoefficientSubgroup R from
          le_sup_right) hc)
  · refine sup_le ?_ ?_
    · rintro x ⟨n, rfl⟩
      exact n.property
    · rintro x ⟨c, rfl⟩
      exact T.normalSubgroup.one_mem

/-- The normal lift lies in the full preimage of the distinguished normal
subgroup. -/
theorem ambientNormalSubgroupLift_range_le_preimage
    (F : AssociatedFiniteFactorNormalization R) :
    (F.ambientNormalSubgroupLift R).range ≤
      F.ambientNormalPreimage R := by
  rw [F.ambientNormalPreimage_eq_sup R]
  exact le_sup_left

/-- The coefficient subgroup lies in the full preimage of the distinguished
normal subgroup. -/
theorem ambientFactorCoefficientSubgroup_le_normalPreimage
    (F : AssociatedFiniteFactorNormalization R) :
    F.ambientFactorCoefficientSubgroup R ≤
      F.ambientNormalPreimage R := by
  rw [F.ambientNormalPreimage_eq_sup R]
  exact le_sup_right

/-- The normal lift and coefficient subgroup meet trivially. -/
theorem ambientNormalSubgroupLift_range_inf_coefficientSubgroup_eq_bot
    (F : AssociatedFiniteFactorNormalization R) :
    (F.ambientNormalSubgroupLift R).range ⊓
        F.ambientFactorCoefficientSubgroup R =
      ⊥ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨n, rfl⟩ := hx.1
    obtain ⟨c, hc⟩ := hx.2
    have hnCoe : (n : A) = 1 := by
      have hbase :=
        congrArg
          (CentralExtensionGroup.base
            F.factorSet (F.factorSet_isNormalized R)) hc
      simpa using hbase.symm
    have hn : n = 1 := by
      apply Subtype.ext
      exact hnCoe
    subst n
    rfl
  · exact bot_le

/-- Setwise product form of `ambientNormalPreimage_eq_sup`. -/
theorem coe_ambientNormalPreimage_eq_mul
    (F : AssociatedFiniteFactorNormalization R) :
    ((F.ambientNormalPreimage R :
        Subgroup (F.AmbientFactorCentralExtensionGroup R)) : Set _) =
      ((F.ambientNormalSubgroupLift R).range :
          Set (F.AmbientFactorCentralExtensionGroup R)) *
        (F.ambientFactorCoefficientSubgroup R :
          Set (F.AmbientFactorCentralExtensionGroup R)) := by
  rw [F.ambientNormalPreimage_eq_sup R]
  exact Subgroup.mul_normal
    (F.ambientNormalSubgroupLift R).range
    (F.ambientFactorCoefficientSubgroup R)

/-- The honest ambient extension character restricts to the distinguished
character of the triple along the canonical normal lift. -/
theorem ambientFactorCentralExtensionCharacter_isExtensionAlong_normalLift
    (F : AssociatedFiniteFactorNormalization R) :
    IrreducibleCharacter.IsExtensionAlong
      (F.ambientNormalSubgroupLift R) T.character
      (F.ambientFactorCentralExtensionCharacter R) := by
  intro n
  change
    (F.ambientFactorCentralExtensionCharacter R).values
        (CentralExtensionGroup.baseLift
          F.factorSet (F.factorSet_isNormalized R) (n : A)) =
      T.character.values n
  rw [F.ambientFactorCentralExtensionCharacter_values_baseLift R (n : A)]
  rw [← F.associated.restriction_apply n]
  exact congrFun F.associated.fdRestriction_character n

/-- Representation-level version of restriction to the canonical normal
lift. -/
@[simp]
theorem ambientFactorCentralExtensionRepresentation_normalLift
    (F : AssociatedFiniteFactorNormalization R)
    (n : T.normalSubgroup) :
    F.ambientFactorCentralExtensionRepresentation R
        (F.ambientNormalSubgroupLift R n) =
      (F.associated.restriction n : V →ₗ[ℂ] V) := by
  ext v
  change
    (1 : ℂ) • F.projective.operator (n : A) v =
      F.associated.restriction n v
  rw [one_smul, F.associated.restriction_apply]

@[simp]
theorem ambientFactorCentralExtensionCharacter_values_normalLift
    (F : AssociatedFiniteFactorNormalization R)
    (n : T.normalSubgroup) :
    (F.ambientFactorCentralExtensionCharacter R).values
        (F.ambientNormalSubgroupLift R n) =
      T.character.values n :=
  F.ambientFactorCentralExtensionCharacter_isExtensionAlong_normalLift R n

/-- Pointwise form of the defining scalar action on the coefficient copy. -/
@[simp]
theorem ambientFactorCentralExtensionCharacter_values_coefficientEmbedding
    (F : AssociatedFiniteFactorNormalization R)
    (c : rootsOfUnity (associatedFactorExponent T V) ℂ) :
    (F.ambientFactorCentralExtensionCharacter R).values
        (CentralExtensionGroup.coefficientEmbedding
          F.factorSet (F.factorSet_isNormalized R) c) =
      ((c : ℂˣ) : ℂ) *
        ((F.ambientFactorCentralExtensionCharacter R).degree : ℂ) :=
  F.ambientFactorCentralExtensionCharacter_hasCoefficientCharacter R c

end AssociatedFiniteFactorNormalization
end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
