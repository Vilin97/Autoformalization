/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixTwoCTblLibCorrectedLocalRowIdentification
import McKayConjecture.InductiveMcKay.AutomorphismStabilizerCorrectionRowIndependence

/-!
# The corrected two-local semantic seed equations
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixTwoCorrectedLocalSeedEquationsFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

private def explicitQuaternionRotationCoordinate :
    AlternatingSixSchurCoordinates :=
  alternatingSixSchurAuditedPresentationGeneratorCoordinates 0 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0 *
    (alternatingSixSchurAuditedPresentationGeneratorCoordinates 1)⁻¹ *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 2 ^ (2 : ℤ)

private def explicitQuaternionReflectionCoordinate :
    AlternatingSixSchurCoordinates :=
  alternatingSixSchurAuditedPresentationGeneratorCoordinates 0 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 2

private def explicitAlphaTwoCorrectionCoordinate :
    AlternatingSixSchurCoordinates :=
  alternatingSixSchurAuditedCoordinate 100 0

private theorem explicitQuaternionRotationCoordinate_eq :
    explicitQuaternionRotationCoordinate =
      alternatingSixSchurAuditedCoordinate 18 2 := by
  decide

private theorem explicitQuaternionReflectionCoordinate_eq :
    explicitQuaternionReflectionCoordinate =
      alternatingSixSchurAuditedCoordinate 1 1 := by
  decide

private theorem alphaOne_explicitQuaternionRotationCoordinate :
    alternatingSixSchurAlphaOneEndomorphism
        explicitQuaternionRotationCoordinate =
      explicitQuaternionRotationCoordinate ^ 3 := by
  decide

private theorem alphaOne_explicitQuaternionReflectionCoordinate :
    alternatingSixSchurAlphaOneEndomorphism
        explicitQuaternionReflectionCoordinate =
      explicitQuaternionReflectionCoordinate := by
  decide

private theorem alphaTwo_explicitQuaternionRotationCoordinate :
    alternatingSixSchurAlphaTwoEndomorphism
        explicitQuaternionRotationCoordinate =
      alternatingSixSchurAuditedCoordinate 219 1 := by
  simp only [
    explicitQuaternionRotationCoordinate,
    map_mul,
    map_inv,
    map_zpow,
    alternatingSixSchurAlphaTwoEndomorphism_generator
  ]
  have hAB :
      alternatingSixSchurAlphaTwoGeneratorCoordinates 0 *
          alternatingSixSchurAlphaTwoGeneratorCoordinates 1 =
        alternatingSixSchurAuditedCoordinate 284 2 := by
    decide
  rw [hAB]
  have hABA :
      alternatingSixSchurAuditedCoordinate 284 2 *
          alternatingSixSchurAlphaTwoGeneratorCoordinates 0 =
        alternatingSixSchurAuditedCoordinate 298 0 := by
    decide
  rw [hABA]
  have hABABInv :
      alternatingSixSchurAuditedCoordinate 298 0 *
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 1)⁻¹ =
        alternatingSixSchurAuditedCoordinate 219 3 := by
    decide
  rw [hABABInv]
  have hKPow :
      alternatingSixSchurAlphaTwoGeneratorCoordinates 2 ^ (2 : ℤ) =
        alternatingSixSchurAuditedCoordinate 0 4 := by
    decide
  rw [hKPow]
  decide

private theorem alphaTwo_explicitQuaternionReflectionCoordinate :
    alternatingSixSchurAlphaTwoEndomorphism
        explicitQuaternionReflectionCoordinate =
      alternatingSixSchurAuditedCoordinate 317 0 := by
  decide

private theorem correctedAlphaTwo_explicitQuaternionRotationCoordinate :
    explicitAlphaTwoCorrectionCoordinate *
          alternatingSixSchurAlphaTwoEndomorphism
            explicitQuaternionRotationCoordinate *
        explicitAlphaTwoCorrectionCoordinate⁻¹ =
      explicitQuaternionRotationCoordinate := by
  rw [alphaTwo_explicitQuaternionRotationCoordinate]
  have hleft :
      explicitAlphaTwoCorrectionCoordinate *
          alternatingSixSchurAuditedCoordinate 219 1 =
        alternatingSixSchurAuditedCoordinate 110 5 := by
    decide
  rw [hleft]
  have hinv :
      explicitAlphaTwoCorrectionCoordinate⁻¹ =
        alternatingSixSchurAuditedCoordinate 108 4 := by
    decide
  rw [hinv]
  decide

private theorem correctedAlphaTwo_explicitQuaternionReflectionCoordinate :
    explicitAlphaTwoCorrectionCoordinate *
          alternatingSixSchurAlphaTwoEndomorphism
            explicitQuaternionReflectionCoordinate *
        explicitAlphaTwoCorrectionCoordinate⁻¹ =
      explicitQuaternionReflectionCoordinate *
        explicitQuaternionRotationCoordinate := by
  rw [alphaTwo_explicitQuaternionReflectionCoordinate]
  have hleft :
      explicitAlphaTwoCorrectionCoordinate *
          alternatingSixSchurAuditedCoordinate 317 0 =
        alternatingSixSchurAuditedCoordinate 130 0 := by
    decide
  rw [hleft]
  have hinv :
      explicitAlphaTwoCorrectionCoordinate⁻¹ =
        alternatingSixSchurAuditedCoordinate 108 4 := by
    decide
  rw [hinv]
  decide

private theorem quaternionFourToAlternatingSixSchur_a_one :
    quaternionFourToAlternatingSixSchur
        (QuaternionGroup.a (1 : ZMod 8)) =
      alternatingSixSchurTwoRotation := by
  simp only [
    quaternionFourToAlternatingSixSchur,
    QuaternionGroup.lift_apply_a
  ]
  simpa using
    QuaternionGroup.zmodPower_natCast
      alternatingSixSchurTwoRotation
      alternatingSixSchurTwoRotation_pow_eight 1

private theorem quaternionFourToAlternatingSixSchur_xa_zero :
    quaternionFourToAlternatingSixSchur
        (QuaternionGroup.xa (0 : ZMod 8)) =
      alternatingSixSchurTwoReflection := by
  simp only [
    quaternionFourToAlternatingSixSchur,
    QuaternionGroup.lift_apply_xa,
    QuaternionGroup.zmodPower_zero,
    mul_one
  ]

private theorem mulEquivPresentedGroup_explicitQuaternionRotationCoordinate :
    AlternatingSixSchurCoordinates.mulEquivPresentedGroup
        explicitQuaternionRotationCoordinate =
      alternatingSixSchurTwoRotation := by
  have hA :
      AlternatingSixSchurCoordinates.mulEquivPresentedGroup
          (alternatingSixSchurAuditedPresentationGeneratorCoordinates 0) =
        alternatingSixSchurPresentedA := by
    change
      AlternatingSixSchurCoordinates.mulEquivPresentedGroup
          alternatingSixSchurCoordinateA =
        alternatingSixSchurPresentedA
    rw [← alternatingSixSchurCoordinateA_preimage,
      MulEquiv.apply_symm_apply]
  have hB :
      AlternatingSixSchurCoordinates.mulEquivPresentedGroup
          (alternatingSixSchurAuditedPresentationGeneratorCoordinates 1) =
        alternatingSixSchurPresentedB := by
    change
      AlternatingSixSchurCoordinates.mulEquivPresentedGroup
          alternatingSixSchurCoordinateB =
        alternatingSixSchurPresentedB
    rw [← alternatingSixSchurCoordinateB_preimage,
      MulEquiv.apply_symm_apply]
  have hK :
      AlternatingSixSchurCoordinates.mulEquivPresentedGroup
          (alternatingSixSchurAuditedPresentationGeneratorCoordinates 2) =
        alternatingSixSchurPresentedK 0 := by
    change
      AlternatingSixSchurCoordinates.evaluate
          ⟨(0 : Fin 360), (1 : ZMod 6)⟩ =
        alternatingSixSchurPresentedK 0
    change
      alternatingSixSchurNormalElement 0 *
          AlternatingSixSchurCoordinates.centralValue 1 =
        alternatingSixSchurPresentedK 0
    rw [show alternatingSixSchurNormalElement 0 = 1 by rfl, one_mul]
    simpa [AlternatingSixSchurCoordinates.centralValue] using
      QuaternionGroup.zmodPower_natCast
        (alternatingSixSchurPresentedK 0)
        alternatingSixSchurPresentedK0_pow_six 1
  have hword :
      alternatingSixSchurWord alternatingSixSchurTwoRotationWord =
        alternatingSixSchurPresentedA *
          alternatingSixSchurPresentedB *
          alternatingSixSchurPresentedA *
          alternatingSixSchurPresentedB⁻¹ := by
    simp [
      alternatingSixSchurTwoRotationWord,
      alternatingSixSchurWord,
      FreeGroup.lift_mk,
      mul_assoc
    ]
  calc
    AlternatingSixSchurCoordinates.mulEquivPresentedGroup
          explicitQuaternionRotationCoordinate =
        alternatingSixSchurPresentedA *
              alternatingSixSchurPresentedB *
            alternatingSixSchurPresentedA *
          alternatingSixSchurPresentedB⁻¹ *
        alternatingSixSchurPresentedK 0 ^ (2 : ℤ) := by
      simp only [
        explicitQuaternionRotationCoordinate,
        map_mul,
        map_inv,
        map_zpow,
        hA,
        hB,
        hK
      ]
    _ =
        alternatingSixSchurRawTwoRotation *
          alternatingSixSchurTwoCentral ^ (2 : ℤ) := by
      rw [alternatingSixSchurRawTwoRotation,
        alternatingSixSchurTwoCentral, hword]
    _ = alternatingSixSchurTwoRotation := rfl

private theorem mulEquivPresentedGroup_explicitQuaternionReflectionCoordinate :
    AlternatingSixSchurCoordinates.mulEquivPresentedGroup
        explicitQuaternionReflectionCoordinate =
      alternatingSixSchurTwoReflection := by
  have hA :
      AlternatingSixSchurCoordinates.mulEquivPresentedGroup
          (alternatingSixSchurAuditedPresentationGeneratorCoordinates 0) =
        alternatingSixSchurPresentedA := by
    change
      AlternatingSixSchurCoordinates.mulEquivPresentedGroup
          alternatingSixSchurCoordinateA =
        alternatingSixSchurPresentedA
    rw [← alternatingSixSchurCoordinateA_preimage,
      MulEquiv.apply_symm_apply]
  have hK :
      AlternatingSixSchurCoordinates.mulEquivPresentedGroup
          (alternatingSixSchurAuditedPresentationGeneratorCoordinates 2) =
        alternatingSixSchurPresentedK 0 := by
    change
      AlternatingSixSchurCoordinates.evaluate
          ⟨(0 : Fin 360), (1 : ZMod 6)⟩ =
        alternatingSixSchurPresentedK 0
    change
      alternatingSixSchurNormalElement 0 *
          AlternatingSixSchurCoordinates.centralValue 1 =
        alternatingSixSchurPresentedK 0
    rw [show alternatingSixSchurNormalElement 0 = 1 by rfl, one_mul]
    simpa [AlternatingSixSchurCoordinates.centralValue] using
      QuaternionGroup.zmodPower_natCast
        (alternatingSixSchurPresentedK 0)
        alternatingSixSchurPresentedK0_pow_six 1
  simp only [
    explicitQuaternionReflectionCoordinate,
    map_mul,
    hA,
    hK,
    alternatingSixSchurTwoReflection,
    alternatingSixSchurTwoCentral
  ]

/-! ### The audited action on the explicit quaternion Sylow subgroup -/

private theorem quaternionFourToAlternatingSixUniversalCover_a_one :
    quaternionFourToAlternatingSixUniversalCover
        (QuaternionGroup.a (1 : ZMod 8)) =
      alternatingSixSchurCoordinatesEquivUniversalCover
        explicitQuaternionRotationCoordinate := by
  change
    alternatingSixSchurEquivUniversalCover
        (quaternionFourToAlternatingSixSchur
          (QuaternionGroup.a (1 : ZMod 8))) =
      alternatingSixSchurEquivUniversalCover
        (AlternatingSixSchurCoordinates.mulEquivPresentedGroup
          explicitQuaternionRotationCoordinate)
  rw [
    quaternionFourToAlternatingSixSchur_a_one,
    mulEquivPresentedGroup_explicitQuaternionRotationCoordinate
  ]

private theorem quaternionFourToAlternatingSixUniversalCover_xa_zero :
    quaternionFourToAlternatingSixUniversalCover
        (QuaternionGroup.xa (0 : ZMod 8)) =
      alternatingSixSchurCoordinatesEquivUniversalCover
        explicitQuaternionReflectionCoordinate := by
  change
    alternatingSixSchurEquivUniversalCover
        (quaternionFourToAlternatingSixSchur
          (QuaternionGroup.xa (0 : ZMod 8))) =
      alternatingSixSchurEquivUniversalCover
        (AlternatingSixSchurCoordinates.mulEquivPresentedGroup
          explicitQuaternionReflectionCoordinate)
  rw [
    quaternionFourToAlternatingSixSchur_xa_zero,
    mulEquivPresentedGroup_explicitQuaternionReflectionCoordinate
  ]

private def explicitAlphaTwoCorrection :
    AlternatingSixUniversalCover :=
  alternatingSixSchurCoordinatesEquivUniversalCover
    explicitAlphaTwoCorrectionCoordinate

private theorem transportedAlphaOne_explicitQuaternion_a_one :
    alternatingSixUniversalCoverTransportedAlphaOne
        (quaternionFourToAlternatingSixUniversalCover
          (QuaternionGroup.a (1 : ZMod 8))) =
      quaternionFourToAlternatingSixUniversalCover
          (QuaternionGroup.a (1 : ZMod 8)) ^ 3 := by
  rw [quaternionFourToAlternatingSixUniversalCover_a_one,
    alternatingSixUniversalCoverTransportedAlphaOne_apply,
    MulEquiv.symm_apply_apply, ← map_pow]
  exact congrArg alternatingSixSchurCoordinatesEquivUniversalCover
    alphaOne_explicitQuaternionRotationCoordinate

private theorem transportedAlphaOne_explicitQuaternion_xa_zero :
    alternatingSixUniversalCoverTransportedAlphaOne
        (quaternionFourToAlternatingSixUniversalCover
          (QuaternionGroup.xa (0 : ZMod 8))) =
      quaternionFourToAlternatingSixUniversalCover
        (QuaternionGroup.xa (0 : ZMod 8)) := by
  rw [quaternionFourToAlternatingSixUniversalCover_xa_zero,
    alternatingSixUniversalCoverTransportedAlphaOne_apply,
    MulEquiv.symm_apply_apply]
  exact congrArg alternatingSixSchurCoordinatesEquivUniversalCover
    alphaOne_explicitQuaternionReflectionCoordinate

private theorem correctedTransportedAlphaTwo_explicitQuaternion_a_one :
    (MulAut.conj explicitAlphaTwoCorrection *
        alternatingSixUniversalCoverTransportedAlphaTwo)
        (quaternionFourToAlternatingSixUniversalCover
          (QuaternionGroup.a (1 : ZMod 8))) =
      quaternionFourToAlternatingSixUniversalCover
        (QuaternionGroup.a (1 : ZMod 8)) := by
  rw [quaternionFourToAlternatingSixUniversalCover_a_one]
  simp only [MulAut.mul_apply, MulAut.conj_apply,
    alternatingSixUniversalCoverTransportedAlphaTwo_apply,
    MulEquiv.symm_apply_apply]
  rw [explicitAlphaTwoCorrection, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg alternatingSixSchurCoordinatesEquivUniversalCover
    correctedAlphaTwo_explicitQuaternionRotationCoordinate

private theorem correctedTransportedAlphaTwo_explicitQuaternion_xa_zero :
    (MulAut.conj explicitAlphaTwoCorrection *
        alternatingSixUniversalCoverTransportedAlphaTwo)
        (quaternionFourToAlternatingSixUniversalCover
          (QuaternionGroup.xa (0 : ZMod 8))) =
      quaternionFourToAlternatingSixUniversalCover
          (QuaternionGroup.xa (0 : ZMod 8)) *
        quaternionFourToAlternatingSixUniversalCover
          (QuaternionGroup.a (1 : ZMod 8)) := by
  rw [quaternionFourToAlternatingSixUniversalCover_xa_zero,
    quaternionFourToAlternatingSixUniversalCover_a_one]
  simp only [MulAut.mul_apply, MulAut.conj_apply,
    alternatingSixUniversalCoverTransportedAlphaTwo_apply,
    MulEquiv.symm_apply_apply]
  rw [explicitAlphaTwoCorrection, ← map_inv, ← map_mul, ← map_mul,
    ← map_mul]
  exact congrArg alternatingSixSchurCoordinatesEquivUniversalCover
    correctedAlphaTwo_explicitQuaternionReflectionCoordinate

private theorem explicitQuaternionRange_map_le_of_generators
    (β : MulAut AlternatingSixUniversalCover)
    (hRotation :
      β (quaternionFourToAlternatingSixUniversalCover
          (QuaternionGroup.a (1 : ZMod 8))) ∈
        quaternionFourToAlternatingSixUniversalCover.range)
    (hReflection :
      β (quaternionFourToAlternatingSixUniversalCover
          (QuaternionGroup.xa (0 : ZMod 8))) ∈
        quaternionFourToAlternatingSixUniversalCover.range) :
    quaternionFourToAlternatingSixUniversalCover.range.map
        (β : AlternatingSixUniversalCover →* AlternatingSixUniversalCover) ≤
      quaternionFourToAlternatingSixUniversalCover.range := by
  rintro y ⟨x, ⟨q, rfl⟩, rfl⟩
  rcases q with i | i
  · obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective i
    rw [← QuaternionGroup.a_one_pow k, map_pow, map_pow]
    exact
      quaternionFourToAlternatingSixUniversalCover.range.pow_mem
        hRotation k
  · obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective i
    have hxa :
        (QuaternionGroup.xa (k : ZMod 8) : QuaternionGroup 4) =
          QuaternionGroup.xa (0 : ZMod 8) *
            QuaternionGroup.a (1 : ZMod 8) ^ k := by
      simp
    rw [hxa, map_mul, map_mul, map_pow, map_pow]
    exact
      quaternionFourToAlternatingSixUniversalCover.range.mul_mem
        hReflection
        (quaternionFourToAlternatingSixUniversalCover.range.pow_mem
          hRotation k)

private theorem transportedAlphaOne_explicitQuaternionSylow_smul :
    alternatingSixUniversalCoverTransportedAlphaOne •
        alternatingSixUniversalCoverQuaternionSylowTwo =
      alternatingSixUniversalCoverQuaternionSylowTwo := by
  apply Sylow.ext
  have hle :
      (((alternatingSixUniversalCoverTransportedAlphaOne •
          alternatingSixUniversalCoverQuaternionSylowTwo) :
        Sylow 2 AlternatingSixUniversalCover) :
          Subgroup AlternatingSixUniversalCover) ≤
        alternatingSixUniversalCoverQuaternionSylowTwo := by
    change
      quaternionFourToAlternatingSixUniversalCover.range.map
          (alternatingSixUniversalCoverTransportedAlphaOne :
            AlternatingSixUniversalCover →* AlternatingSixUniversalCover) ≤
        quaternionFourToAlternatingSixUniversalCover.range
    apply explicitQuaternionRange_map_le_of_generators
    · rw [transportedAlphaOne_explicitQuaternion_a_one]
      exact
        quaternionFourToAlternatingSixUniversalCover.range.pow_mem
          ⟨QuaternionGroup.a (1 : ZMod 8), rfl⟩ 3
    · rw [transportedAlphaOne_explicitQuaternion_xa_zero]
      exact ⟨QuaternionGroup.xa (0 : ZMod 8), rfl⟩
  exact
    ((alternatingSixUniversalCoverTransportedAlphaOne •
        alternatingSixUniversalCoverQuaternionSylowTwo).is_maximal'
      alternatingSixUniversalCoverQuaternionSylowTwo.isPGroup' hle).symm

private theorem correctedTransportedAlphaTwo_explicitQuaternionSylow_smul :
    (MulAut.conj explicitAlphaTwoCorrection *
        alternatingSixUniversalCoverTransportedAlphaTwo) •
        alternatingSixUniversalCoverQuaternionSylowTwo =
      alternatingSixUniversalCoverQuaternionSylowTwo := by
  apply Sylow.ext
  have hle :
      ((((MulAut.conj explicitAlphaTwoCorrection *
            alternatingSixUniversalCoverTransportedAlphaTwo) •
          alternatingSixUniversalCoverQuaternionSylowTwo) :
        Sylow 2 AlternatingSixUniversalCover) :
          Subgroup AlternatingSixUniversalCover) ≤
        alternatingSixUniversalCoverQuaternionSylowTwo := by
    change
      quaternionFourToAlternatingSixUniversalCover.range.map
          ((MulAut.conj explicitAlphaTwoCorrection *
            alternatingSixUniversalCoverTransportedAlphaTwo) :
            AlternatingSixUniversalCover →* AlternatingSixUniversalCover) ≤
        quaternionFourToAlternatingSixUniversalCover.range
    apply explicitQuaternionRange_map_le_of_generators
    · rw [correctedTransportedAlphaTwo_explicitQuaternion_a_one]
      exact ⟨QuaternionGroup.a (1 : ZMod 8), rfl⟩
    · rw [correctedTransportedAlphaTwo_explicitQuaternion_xa_zero]
      exact
        quaternionFourToAlternatingSixUniversalCover.range.mul_mem
          ⟨QuaternionGroup.xa (0 : ZMod 8), rfl⟩
          ⟨QuaternionGroup.a (1 : ZMod 8), rfl⟩
  exact
    (((MulAut.conj explicitAlphaTwoCorrection *
          alternatingSixUniversalCoverTransportedAlphaTwo) •
        alternatingSixUniversalCoverQuaternionSylowTwo).is_maximal'
      alternatingSixUniversalCoverQuaternionSylowTwo.isPGroup' hle).symm

/-! ### Transport from the explicit Sylow subgroup to the fixed one -/

private def fixedToExplicitSylowConjugator :
    AlternatingSixUniversalCover :=
  Classical.choose
    (MulAction.exists_smul_eq
      AlternatingSixUniversalCover
      (alternatingSixUniversalCoverSylow 2)
      alternatingSixUniversalCoverQuaternionSylowTwo)

private theorem fixedToExplicitSylowConjugator_smul :
    fixedToExplicitSylowConjugator •
        alternatingSixUniversalCoverSylow 2 =
      alternatingSixUniversalCoverQuaternionSylowTwo :=
  Classical.choose_spec
    (MulAction.exists_smul_eq
      AlternatingSixUniversalCover
      (alternatingSixUniversalCoverSylow 2)
      alternatingSixUniversalCoverQuaternionSylowTwo)

private def fixedAlphaOneCorrection :
    AlternatingSixUniversalCover :=
  fixedToExplicitSylowConjugator⁻¹ *
    alternatingSixUniversalCoverTransportedAlphaOne
      fixedToExplicitSylowConjugator

private def fixedAlphaTwoCorrection :
    AlternatingSixUniversalCover :=
  fixedToExplicitSylowConjugator⁻¹ *
      explicitAlphaTwoCorrection *
    alternatingSixUniversalCoverTransportedAlphaTwo
      fixedToExplicitSylowConjugator

private theorem transported_correction_smul
    (P Q : Sylow 2 AlternatingSixUniversalCover)
    (a : MulAut AlternatingSixUniversalCover)
    (h g : AlternatingSixUniversalCover)
    (hPQ : h • P = Q)
    (hgQ : (MulAut.conj g * a) • Q = Q) :
    (h⁻¹ * g * a h) • (a • P) = P := by
  have haut :
      MulAut.conj (h⁻¹ * g * a h) * a =
        MulAut.conj h⁻¹ * (MulAut.conj g * a) * MulAut.conj h := by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  calc
    (h⁻¹ * g * a h) • (a • P) =
        (MulAut.conj (h⁻¹ * g * a h) * a) • P := by
      rw [Sylow.smul_def, mul_smul]
    _ =
        (MulAut.conj h⁻¹ * (MulAut.conj g * a) *
          MulAut.conj h) • P := by rw [haut]
    _ =
        h⁻¹ • ((MulAut.conj g * a) • (h • P)) := by
      simp only [mul_smul, Sylow.smul_def]
    _ = h⁻¹ • ((MulAut.conj g * a) • Q) := by rw [hPQ]
    _ = h⁻¹ • Q := by rw [hgQ]
    _ = P := by
      rw [← hPQ, ← mul_smul]
      simp

private theorem fixedAlphaOneCorrection_smul :
    fixedAlphaOneCorrection •
        (alternatingSixUniversalCoverTransportedAlphaOne •
          alternatingSixUniversalCoverSylow 2) =
      alternatingSixUniversalCoverSylow 2 := by
  simpa [fixedAlphaOneCorrection] using
    transported_correction_smul
      (alternatingSixUniversalCoverSylow 2)
      alternatingSixUniversalCoverQuaternionSylowTwo
      alternatingSixUniversalCoverTransportedAlphaOne
      fixedToExplicitSylowConjugator
      1
      fixedToExplicitSylowConjugator_smul
      (by simpa using
        transportedAlphaOne_explicitQuaternionSylow_smul)

private theorem fixedAlphaTwoCorrection_smul :
    fixedAlphaTwoCorrection •
        (alternatingSixUniversalCoverTransportedAlphaTwo •
          alternatingSixUniversalCoverSylow 2) =
      alternatingSixUniversalCoverSylow 2 := by
  simpa [fixedAlphaTwoCorrection] using
    transported_correction_smul
      (alternatingSixUniversalCoverSylow 2)
      alternatingSixUniversalCoverQuaternionSylowTwo
      alternatingSixUniversalCoverTransportedAlphaTwo
      fixedToExplicitSylowConjugator
      explicitAlphaTwoCorrection
      fixedToExplicitSylowConjugator_smul
      correctedTransportedAlphaTwo_explicitQuaternionSylow_smul

private def explicitFixedAlphaOneStabilizer :
    SylowAutStabilizer (alternatingSixUniversalCoverSylow 2) :=
  SylowAutStabilizer.correctedWithConjugator
    (alternatingSixUniversalCoverSylow 2)
    alternatingSixUniversalCoverTransportedAlphaOne
    fixedAlphaOneCorrection
    fixedAlphaOneCorrection_smul

private def explicitFixedAlphaTwoStabilizer :
    SylowAutStabilizer (alternatingSixUniversalCoverSylow 2) :=
  SylowAutStabilizer.correctedWithConjugator
    (alternatingSixUniversalCoverSylow 2)
    alternatingSixUniversalCoverTransportedAlphaTwo
    fixedAlphaTwoCorrection
    fixedAlphaTwoCorrection_smul

/-! ### Public computational milestones -/

/-- On the explicit generalized-quaternion Sylow subgroup, the first
audited automorphism sends the rotation generator to its third power and
fixes the reflection generator. -/
theorem alternatingSixTwoAlphaOne_explicitQuaternionGeneratorAction :
    alternatingSixUniversalCoverTransportedAlphaOne
        (quaternionFourToAlternatingSixUniversalCover
          (QuaternionGroup.a (1 : ZMod 8))) =
        quaternionFourToAlternatingSixUniversalCover
            (QuaternionGroup.a (1 : ZMod 8)) ^ 3 ∧
      alternatingSixUniversalCoverTransportedAlphaOne
        (quaternionFourToAlternatingSixUniversalCover
          (QuaternionGroup.xa (0 : ZMod 8))) =
        quaternionFourToAlternatingSixUniversalCover
          (QuaternionGroup.xa (0 : ZMod 8)) :=
  ⟨transportedAlphaOne_explicitQuaternion_a_one,
    transportedAlphaOne_explicitQuaternion_xa_zero⟩

/-- There is an explicit inner correction of the second audited
automorphism which fixes the quaternion rotation generator and shears the
reflection generator by that rotation.  The corrected automorphism
stabilizes the whole explicit Sylow subgroup. -/
theorem alternatingSixTwo_exists_explicitQuaternionAlphaTwoCorrection :
    ∃ g : AlternatingSixUniversalCover,
      (MulAut.conj g *
          alternatingSixUniversalCoverTransportedAlphaTwo) •
          alternatingSixUniversalCoverQuaternionSylowTwo =
        alternatingSixUniversalCoverQuaternionSylowTwo ∧
      (MulAut.conj g *
          alternatingSixUniversalCoverTransportedAlphaTwo)
          (quaternionFourToAlternatingSixUniversalCover
            (QuaternionGroup.a (1 : ZMod 8))) =
        quaternionFourToAlternatingSixUniversalCover
          (QuaternionGroup.a (1 : ZMod 8)) ∧
      (MulAut.conj g *
          alternatingSixUniversalCoverTransportedAlphaTwo)
          (quaternionFourToAlternatingSixUniversalCover
            (QuaternionGroup.xa (0 : ZMod 8))) =
        quaternionFourToAlternatingSixUniversalCover
            (QuaternionGroup.xa (0 : ZMod 8)) *
          quaternionFourToAlternatingSixUniversalCover
            (QuaternionGroup.a (1 : ZMod 8)) :=
  ⟨explicitAlphaTwoCorrection,
    correctedTransportedAlphaTwo_explicitQuaternionSylow_smul,
    correctedTransportedAlphaTwo_explicitQuaternion_a_one,
    correctedTransportedAlphaTwo_explicitQuaternion_xa_zero⟩

/-- Both audited automorphisms have concrete corrections carrying their
images of the project's fixed Sylow subgroup back to that subgroup. -/
theorem alternatingSixTwo_exists_fixedSylowCorrections :
    (∃ g : AlternatingSixUniversalCover,
        g • (alternatingSixUniversalCoverTransportedAlphaOne •
          alternatingSixUniversalCoverSylow 2) =
            alternatingSixUniversalCoverSylow 2) ∧
      (∃ g : AlternatingSixUniversalCover,
        g • (alternatingSixUniversalCoverTransportedAlphaTwo •
          alternatingSixUniversalCoverSylow 2) =
            alternatingSixUniversalCoverSylow 2) :=
  ⟨⟨fixedAlphaOneCorrection, fixedAlphaOneCorrection_smul⟩,
    ⟨fixedAlphaTwoCorrection, fixedAlphaTwoCorrection_smul⟩⟩

end InductiveMcKay
end McKayConjecture
