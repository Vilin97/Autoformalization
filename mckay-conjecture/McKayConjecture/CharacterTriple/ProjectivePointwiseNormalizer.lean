/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveInteriorNormalizer

/-!
# Pointwise criteria for projective interior normalizers

For a finite group acting linearly on a module, a projective operator
normalizes the implementing-unit image as soon as conjugation sends each
implementing operator back into that image.  This condition is weaker than
supplying a compatible action by automorphisms of the group.

The especially useful fixed-action case follows from pointwise commutation.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

variable {K P G V : Type}
variable [Field K] [Group P] [Finite P] [Group G]
variable [AddCommGroup V] [Module K V]

/-- A projective action pointwise normalizes a linear action when conjugating
each implementing operator produces another implementing operator. -/
def PointwiseNormalizesLinearAction
    (Q : ProjectiveRepresentation K G V)
    (ρ : P →* (V ≃ₗ[K] V)) : Prop :=
  ∀ g p, ∃ p',
    Q.operator g * ρ p * (Q.operator g)⁻¹ = ρ p'

/-- Pointwise normalization puts every projective operator in the normalizer
of the implementing-unit image. -/
theorem operatorUnit_mem_linearActionUnit_normalizer_of_pointwise
    (Q : ProjectiveRepresentation K G V)
    (ρ : P →* (V ≃ₗ[K] V))
    (hnorm : Q.PointwiseNormalizesLinearAction ρ)
    (g : G) :
    operatorUnit (Q.operator g) ∈
      Subgroup.normalizer
        ((linearActionUnit ρ).range :
          Set (Module.End K V)ˣ) := by
  letI :
      Finite
        ((linearActionUnit ρ).range :
          Set (Module.End K V)ˣ) :=
    Set.finite_range (linearActionUnit ρ)
  apply Subgroup.mem_normalizer_fintype
  intro u hu
  rcases hu with ⟨p, rfl⟩
  obtain ⟨p', hp'⟩ := hnorm g p
  refine ⟨p', ?_⟩
  apply
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).injective
  simpa only [_root_.map_mul, _root_.map_inv,
    generalLinearEquiv_operatorUnit,
    generalLinearEquiv_linearActionUnit] using hp'.symm

omit [Finite P] in
/-- Pointwise commutation is a sufficient pointwise-normalization
condition. -/
theorem pointwiseNormalizesLinearAction_of_commutes
    (Q : ProjectiveRepresentation K G V)
    (ρ : P →* (V ≃ₗ[K] V))
    (hcomm :
      ∀ g p, Q.operator g * ρ p = ρ p * Q.operator g) :
    Q.PointwiseNormalizesLinearAction ρ := by
  intro g p
  refine ⟨p, ?_⟩
  calc
    Q.operator g * ρ p * (Q.operator g)⁻¹ =
        ρ p * Q.operator g * (Q.operator g)⁻¹ := by
          rw [hcomm g p]
    _ = ρ p := by simp

/-- A commuting projective operator normalizes the implementing-unit
image. -/
theorem operatorUnit_mem_linearActionUnit_normalizer_of_commutes
    (Q : ProjectiveRepresentation K G V)
    (ρ : P →* (V ≃ₗ[K] V))
    (hcomm :
      ∀ g p, Q.operator g * ρ p = ρ p * Q.operator g)
    (g : G) :
    operatorUnit (Q.operator g) ∈
      Subgroup.normalizer
        ((linearActionUnit ρ).range :
          Set (Module.End K V)ˣ) :=
  operatorUnit_mem_linearActionUnit_normalizer_of_pointwise
    Q ρ (Q.pointwiseNormalizesLinearAction_of_commutes ρ hcomm) g

variable [Fintype P]

/-- Bundle a normalized projective action satisfying the pointwise
normalization criterion as a lift in the endomorphism interior normalizer. -/
def toProjectiveNormalizerLiftOfPointwise
    (Q : ProjectiveRepresentation K G V)
    (ρ : P →* (V ≃ₗ[K] V))
    (hnorm : Q.PointwiseNormalizesLinearAction ρ)
    (hQ : Q.IsNormalized) :
    letI :=
      endomorphismConjugationMulSemiringAction ρ
    letI :=
      endomorphismConjugation_smulCommClass ρ
    Representation.ProjectiveNormalizerLift
      (k := K) (H := G)
      (interiorActionOfLinearAction ρ) := by
  letI :=
    endomorphismConjugationMulSemiringAction ρ
  letI :=
    endomorphismConjugation_smulCommClass ρ
  exact
    toProjectiveNormalizerLift Q
      (interiorActionOfLinearAction ρ)
      (operatorUnit_mem_linearActionUnit_normalizer_of_pointwise
        Q ρ hnorm)
      hQ

omit [Fintype P] in
/-- The pointwise-normalizer lift has the original projective factor
literally. -/
@[simp]
theorem toProjectiveNormalizerLiftOfPointwise_factor
    (Q : ProjectiveRepresentation K G V)
    (ρ : P →* (V ≃ₗ[K] V))
    (hnorm : Q.PointwiseNormalizesLinearAction ρ)
    (hQ : Q.IsNormalized)
    (g h : G) :
    letI :=
      endomorphismConjugationMulSemiringAction ρ
    letI :=
      endomorphismConjugation_smulCommClass ρ
    (Q.toProjectiveNormalizerLiftOfPointwise
      ρ hnorm hQ).factor g h =
      Q.factor g h :=
  rfl

/-- Bundle commuting normalized projective operators as an interior
normalizer lift. -/
def toProjectiveNormalizerLiftOfCommutes
    (Q : ProjectiveRepresentation K G V)
    (ρ : P →* (V ≃ₗ[K] V))
    (hcomm :
      ∀ g p, Q.operator g * ρ p = ρ p * Q.operator g)
    (hQ : Q.IsNormalized) :
    letI :=
      endomorphismConjugationMulSemiringAction ρ
    letI :=
      endomorphismConjugation_smulCommClass ρ
    Representation.ProjectiveNormalizerLift
      (k := K) (H := G)
      (interiorActionOfLinearAction ρ) :=
  Q.toProjectiveNormalizerLiftOfPointwise ρ
    (Q.pointwiseNormalizesLinearAction_of_commutes ρ hcomm) hQ

omit [Fintype P] in
/-- The commuting-normalizer lift also retains the original factor
literally. -/
@[simp]
theorem toProjectiveNormalizerLiftOfCommutes_factor
    (Q : ProjectiveRepresentation K G V)
    (ρ : P →* (V ≃ₗ[K] V))
    (hcomm :
      ∀ g p, Q.operator g * ρ p = ρ p * Q.operator g)
    (hQ : Q.IsNormalized)
    (g h : G) :
    letI :=
      endomorphismConjugationMulSemiringAction ρ
    letI :=
      endomorphismConjugation_smulCommClass ρ
    (Q.toProjectiveNormalizerLiftOfCommutes
      ρ hcomm hQ).factor g h =
      Q.factor g h :=
  rfl

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
