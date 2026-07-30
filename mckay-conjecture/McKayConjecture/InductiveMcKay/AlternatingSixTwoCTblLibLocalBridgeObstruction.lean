/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixTwoCTblLibParameterizedRowBridge
import McKayConjecture.GroupTheory.AlternatingSixSchurFiveNormalizerDicyclic

/-!
# Local obstructions to the engineered two-local CTblLib position data

The local position equivalence in the central-block CTblLib identification
was engineered only so that transport of the audited candidate recovers the
existing central-block row matching.  At CT position one it assigns cyclic
`C₃` coordinate one.  Both audited local target positions retain that
coordinate.

The genuine corrected outer actions behave differently.  Each audited outer
automorphism inverts the order-six ambient center; the inner Sylow correction
does not change this action.  Consequently restriction to the actual
two-normalizer inverts its central `C₃` coordinate, and a row with coordinate
one takes the inverse primitive-third-root value.  This differs from every
audited target row at position one, whose coordinate remains one.  Thus both
local bridge propositions for the engineered identification are false.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixTwoLocalBridgeObstructionFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

private def coordinateCentralGenerator :
    AlternatingSixUniversalCover :=
  alternatingSixSchurCoordinatesEquivUniversalCover
    (alternatingSixSchurAuditedPresentationGeneratorCoordinates 2)

private theorem coordinateCentralGenerator_mem_center :
    coordinateCentralGenerator ∈
      Subgroup.center AlternatingSixUniversalCover := by
  apply MulEquivClass.apply_mem_center
    alternatingSixSchurCoordinatesEquivUniversalCover
  have hcoordinate :
      alternatingSixSchurAuditedPresentationGeneratorCoordinates 2 =
        AlternatingSixSchurCoordinates.mulEquivPresentedGroup.symm
          alternatingSixSchurFiveCentral := by
    apply AlternatingSixSchurCoordinates.mulEquivPresentedGroup.injective
    rw [MulEquiv.apply_symm_apply]
    exact alternatingSixSchurAuditedPresentationGenerator_evaluate 2
  rw [hcoordinate]
  exact
    MulEquivClass.apply_mem_center
      AlternatingSixSchurCoordinates.mulEquivPresentedGroup.symm
      alternatingSixSchurFiveCentral_mem_center

private theorem orderOf_coordinateCentralGenerator :
    orderOf coordinateCentralGenerator = 6 := by
  rw [coordinateCentralGenerator,
    alternatingSixSchurCoordinatesEquivUniversalCover.orderOf_eq]
  have hcoordinate :
      alternatingSixSchurAuditedPresentationGeneratorCoordinates 2 =
        AlternatingSixSchurCoordinates.mulEquivPresentedGroup.symm
          alternatingSixSchurFiveCentral := by
    apply AlternatingSixSchurCoordinates.mulEquivPresentedGroup.injective
    rw [MulEquiv.apply_symm_apply]
    exact alternatingSixSchurAuditedPresentationGenerator_evaluate 2
  rw [hcoordinate,
    AlternatingSixSchurCoordinates.mulEquivPresentedGroup.symm.orderOf_eq]
  change orderOf alternatingSixSchurFiveCentral = 6
  exact orderOf_alternatingSixSchurFiveCentral

private theorem transportedAlphaOne_coordinateCentralGenerator :
    alternatingSixUniversalCoverTransportedAlphaOne
        coordinateCentralGenerator =
      coordinateCentralGenerator⁻¹ := by
  rw [coordinateCentralGenerator,
    alternatingSixUniversalCoverTransportedAlphaOne_apply,
    alternatingSixSchurCoordinatesEquivUniversalCover.symm_apply_apply]
  change
    alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurAlphaOneEndomorphism
          (alternatingSixSchurAuditedPresentationGeneratorCoordinates 2)) =
      _
  rw [alternatingSixSchurAlphaOneEndomorphism_generator]
  calc
    alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurAlphaOneGeneratorCoordinates 2) =
      alternatingSixSchurCoordinatesEquivUniversalCover
        ((alternatingSixSchurAuditedPresentationGeneratorCoordinates 2)⁻¹) := by
          congr 1
    _ = _ := map_inv _ _

private theorem transportedAlphaTwo_coordinateCentralGenerator :
    alternatingSixUniversalCoverTransportedAlphaTwo
        coordinateCentralGenerator =
      coordinateCentralGenerator⁻¹ := by
  rw [coordinateCentralGenerator,
    alternatingSixUniversalCoverTransportedAlphaTwo_apply,
    alternatingSixSchurCoordinatesEquivUniversalCover.symm_apply_apply]
  change
    alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurAlphaTwoEndomorphism
          (alternatingSixSchurAuditedPresentationGeneratorCoordinates 2)) =
      _
  rw [alternatingSixSchurAlphaTwoEndomorphism_generator]
  calc
    alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurAlphaTwoGeneratorCoordinates 2) =
      alternatingSixSchurCoordinatesEquivUniversalCover
        ((alternatingSixSchurAuditedPresentationGeneratorCoordinates 2)⁻¹) := by
          congr 1
    _ = _ := map_inv _ _

private theorem center_eq_zpowers_coordinateCentralGenerator :
    Subgroup.center AlternatingSixUniversalCover =
      Subgroup.zpowers coordinateCentralGenerator := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · exact Subgroup.zpowers_le_of_mem coordinateCentralGenerator_mem_center
  · rw [Nat.card_zpowers, orderOf_coordinateCentralGenerator,
      alternatingSixHopfKernelHasOrderSix.center]

private theorem transportedAlphaOne_inverts_center
    (x : AlternatingSixUniversalCover)
    (hx : x ∈ Subgroup.center AlternatingSixUniversalCover) :
    alternatingSixUniversalCoverTransportedAlphaOne x = x⁻¹ := by
  rw [center_eq_zpowers_coordinateCentralGenerator] at hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [map_zpow, transportedAlphaOne_coordinateCentralGenerator]
  simp

private theorem transportedAlphaTwo_inverts_center
    (x : AlternatingSixUniversalCover)
    (hx : x ∈ Subgroup.center AlternatingSixUniversalCover) :
    alternatingSixUniversalCoverTransportedAlphaTwo x = x⁻¹ := by
  rw [center_eq_zpowers_coordinateCentralGenerator] at hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [map_zpow, transportedAlphaTwo_coordinateCentralGenerator]
  simp

private def modelCentralThreeGenerator :
    AlternatingSixTwoNormalizerModel :=
  (Multiplicative.ofAdd (1 : ZMod 3), 1)

private def actualNormalizerCentralThreeGenerator :
    SylowNormalizer (alternatingSixUniversalCoverSylow 2) :=
  alternatingSixTwoNormalizerModelEquivUniversalCoverNormalizer
    modelCentralThreeGenerator

private theorem actualNormalizerCentralThreeGenerator_val_mem_center :
    (actualNormalizerCentralThreeGenerator :
        AlternatingSixUniversalCover) ∈
      Subgroup.center AlternatingSixUniversalCover := by
  unfold actualNormalizerCentralThreeGenerator modelCentralThreeGenerator
  simp only [
    alternatingSixTwoNormalizerModelEquivUniversalCoverNormalizer,
    MulEquiv.trans_apply,
    alternatingSixUniversalCoverTwoNormalizerInternalProductEquiv,
    MulEquiv.ofBijective_apply,
    alternatingSixUniversalCoverTwoNormalizerProductHom
  ]
  change
    (((quaternionFourEquivAlternatingSixUniversalCoverSylowTwoInNormalizer
          (1 : QuaternionGroup 4) :
        alternatingSixUniversalCoverSylowTwoInNormalizer) :
          SylowNormalizer (alternatingSixUniversalCoverSylow 2)) *
      ((cyclicThreeEquivAlternatingSixUniversalCoverCentralThreeInTwoNormalizer
          (Multiplicative.ofAdd (1 : ZMod 3)) :
        alternatingSixUniversalCoverCentralThreeInTwoNormalizer) :
          SylowNormalizer (alternatingSixUniversalCoverSylow 2)) :
        AlternatingSixUniversalCover) ∈
      Subgroup.center AlternatingSixUniversalCover
  simpa using
    alternatingSixUniversalCoverCentralThree_le_center
      (cyclicThreeEquivAlternatingSixUniversalCoverCentralThreeInTwoNormalizer
        (Multiplicative.ofAdd (1 : ZMod 3))).2

private theorem correctedAlphaOne_inverts_actualNormalizerCentralThreeGenerator :
    ((alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
        (alternatingSixUniversalCoverSylow 2) :
      MulAut AlternatingSixUniversalCover)
        actualNormalizerCentralThreeGenerator) =
      (actualNormalizerCentralThreeGenerator :
        AlternatingSixUniversalCover)⁻¹ := by
  rw [alternatingSixUniversalCoverCorrectedAlphaOneStabilizer_coe]
  change
    _ *
      alternatingSixUniversalCoverTransportedAlphaOne
        (actualNormalizerCentralThreeGenerator :
          AlternatingSixUniversalCover) *
      _⁻¹ =
    _
  rw [transportedAlphaOne_inverts_center _
    actualNormalizerCentralThreeGenerator_val_mem_center]
  have hcomm :=
    Subgroup.mem_center_iff.mp
      (Subgroup.inv_mem _
        actualNormalizerCentralThreeGenerator_val_mem_center)
      (SylowAutStabilizer.correctionConjugator
        (alternatingSixUniversalCoverSylow 2)
        alternatingSixUniversalCoverTransportedAlphaOne)
  rw [hcomm]
  group

private theorem correctedAlphaTwo_inverts_actualNormalizerCentralThreeGenerator :
    ((alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
        (alternatingSixUniversalCoverSylow 2) :
      MulAut AlternatingSixUniversalCover)
        actualNormalizerCentralThreeGenerator) =
      (actualNormalizerCentralThreeGenerator :
        AlternatingSixUniversalCover)⁻¹ := by
  rw [alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer_coe]
  change
    _ *
      alternatingSixUniversalCoverTransportedAlphaTwo
        (actualNormalizerCentralThreeGenerator :
          AlternatingSixUniversalCover) *
      _⁻¹ =
    _
  rw [transportedAlphaTwo_inverts_center _
    actualNormalizerCentralThreeGenerator_val_mem_center]
  have hcomm :=
    Subgroup.mem_center_iff.mp
      (Subgroup.inv_mem _
        actualNormalizerCentralThreeGenerator_val_mem_center)
      (SylowAutStabilizer.correctionConjugator
        (alternatingSixUniversalCoverSylow 2)
        alternatingSixUniversalCoverTransportedAlphaTwo)
  rw [hcomm]
  group

private theorem alphaOneNormalizerRestriction_symm_generator :
    (SylowAutStabilizer.normalizerRestrictionHom
      (alternatingSixUniversalCoverSylow 2)
      (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
        (alternatingSixUniversalCoverSylow 2))).symm
        actualNormalizerCentralThreeGenerator =
      actualNormalizerCentralThreeGenerator⁻¹ := by
  apply
    (SylowAutStabilizer.normalizerRestrictionHom
      (alternatingSixUniversalCoverSylow 2)
      (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
        (alternatingSixUniversalCoverSylow 2))).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [SylowAutStabilizer.normalizerRestrictionHom_apply_coe]
  symm
  change
    ((alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
        (alternatingSixUniversalCoverSylow 2) :
      MulAut AlternatingSixUniversalCover)
        (actualNormalizerCentralThreeGenerator :
          AlternatingSixUniversalCover)⁻¹) =
      (actualNormalizerCentralThreeGenerator :
        AlternatingSixUniversalCover)
  rw [map_inv,
    correctedAlphaOne_inverts_actualNormalizerCentralThreeGenerator,
    inv_inv]

private theorem alphaTwoNormalizerRestriction_symm_generator :
    (SylowAutStabilizer.normalizerRestrictionHom
      (alternatingSixUniversalCoverSylow 2)
      (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
        (alternatingSixUniversalCoverSylow 2))).symm
        actualNormalizerCentralThreeGenerator =
      actualNormalizerCentralThreeGenerator⁻¹ := by
  apply
    (SylowAutStabilizer.normalizerRestrictionHom
      (alternatingSixUniversalCoverSylow 2)
      (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
        (alternatingSixUniversalCoverSylow 2))).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [SylowAutStabilizer.normalizerRestrictionHom_apply_coe]
  symm
  change
    ((alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
        (alternatingSixUniversalCoverSylow 2) :
      MulAut AlternatingSixUniversalCover)
        (actualNormalizerCentralThreeGenerator :
          AlternatingSixUniversalCover)⁻¹) =
      (actualNormalizerCentralThreeGenerator :
        AlternatingSixUniversalCover)
  rw [map_inv,
    correctedAlphaTwo_inverts_actualNormalizerCentralThreeGenerator,
    inv_inv]

private theorem actualCharacter_values_generator
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    (alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r).1.values
        actualNormalizerCentralThreeGenerator =
      (CyclicThree.thirdRootParameter r.1 : ℂ) := by
  rw [actualNormalizerCentralThreeGenerator,
    alternatingSixTwoActualNormalizerPPrimeCharacterEquiv_values]
  change
    (alternatingSixTwoModelNormalizerPPrimeCharacterEquiv r).1.values
        (Multiplicative.ofAdd (1 : ZMod 3),
          QuaternionGroup.a (0 : ZMod 8)) =
      _
  calc
    _ =
        (CyclicThree.linearHom r.1
          (Multiplicative.ofAdd (1 : ZMod 3)) : ℂ) *
          (QuaternionGroupFour.signParameter r.2.1 ^ (0 : ℕ) : ℂˣ) :=
      alternatingSixTwoModelNormalizerPPrimeCharacterEquiv_values_a
        r (Multiplicative.ofAdd (1 : ZMod 3)) 0
    _ = _ := by
      rw [CyclicThree.linearHom_generator]
      simp

private theorem actualCharacter_values_generator_inv
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    (alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r).1.values
        actualNormalizerCentralThreeGenerator⁻¹ =
      ((CyclicThree.thirdRootParameter r.1 : ℂ)⁻¹) := by
  rw [actualNormalizerCentralThreeGenerator, ← map_inv,
    alternatingSixTwoActualNormalizerPPrimeCharacterEquiv_values]
  change
    (alternatingSixTwoModelNormalizerPPrimeCharacterEquiv r).1.values
        (modelCentralThreeGenerator⁻¹) =
      _
  rw [show
      modelCentralThreeGenerator⁻¹ =
        (Multiplicative.ofAdd (-(1 : ZMod 3)), 1) by
      rfl,
    ]
  change
    (alternatingSixTwoModelNormalizerPPrimeCharacterEquiv r).1.values
        (Multiplicative.ofAdd (-(1 : ZMod 3)),
          QuaternionGroup.a (0 : ZMod 8)) =
      _
  calc
    _ =
        (CyclicThree.linearHom r.1
          (Multiplicative.ofAdd (-(1 : ZMod 3))) : ℂ) *
          (QuaternionGroupFour.signParameter r.2.1 ^ (0 : ℕ) : ℂˣ) :=
      alternatingSixTwoModelNormalizerPPrimeCharacterEquiv_values_a
        r (Multiplicative.ofAdd (-(1 : ZMod 3))) 0
    _ = _ := by
      rw [show
          (Multiplicative.ofAdd (-(1 : ZMod 3))) =
            (Multiplicative.ofAdd (1 : ZMod 3))⁻¹ by
          rfl,
        map_inv, CyclicThree.linearHom_generator]
      simp

private theorem primitiveThirdRootParameter_one_ne_two :
    (CyclicThree.thirdRootParameter (1 : Fin 3) : ℂ) ≠
      (CyclicThree.thirdRootParameter (2 : Fin 3) : ℂ) := by
  intro h
  have hu :
      CyclicThree.thirdRootParameter (1 : Fin 3) =
        CyclicThree.thirdRootParameter (2 : Fin 3) :=
    Units.ext h
  exact (by decide : (1 : Fin 3) ≠ 2)
    (CyclicThree.thirdRootParameter_injective hu)

private theorem primitiveThirdRootParameter_one_inv :
    (CyclicThree.thirdRootParameter (1 : Fin 3) : ℂ)⁻¹ =
      (CyclicThree.thirdRootParameter (2 : Fin 3) : ℂ) := by
  have hu :
      (CyclicThree.thirdRootParameter (1 : Fin 3))⁻¹ =
        CyclicThree.thirdRootParameter (2 : Fin 3) := by
    change (CyclicThree.primitiveThirdRootUnit ^ 1)⁻¹ =
      CyclicThree.primitiveThirdRootUnit ^ 2
    rw [pow_one]
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ]
    exact CyclicThree.primitiveThirdRootUnit_pow_three
  simpa using congrArg Units.val hu

private theorem correctedAlphaOne_smul_actualCharacter_values_generator
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    ((alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
          (alternatingSixUniversalCoverSylow 2)) •
        alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r).1.values
          actualNormalizerCentralThreeGenerator =
      (CyclicThree.thirdRootParameter r.1 : ℂ)⁻¹ := by
  rw [SylowAutStabilizer.smul_normalizer_pPrime_values,
    alphaOneNormalizerRestriction_symm_generator,
    actualCharacter_values_generator_inv]

private theorem correctedAlphaTwo_smul_actualCharacter_values_generator
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    ((alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
          (alternatingSixUniversalCoverSylow 2)) •
        alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r).1.values
          actualNormalizerCentralThreeGenerator =
      (CyclicThree.thirdRootParameter r.1 : ℂ)⁻¹ := by
  rw [SylowAutStabilizer.smul_normalizer_pPrime_values,
    alphaTwoNormalizerRestriction_symm_generator,
    actualCharacter_values_generator_inv]

/-! ### Reusable central-coordinate action API -/

/-- The distinguished generator of the central `C₃` factor in the actual
Sylow-two normalizer. -/
def alternatingSixTwoActualNormalizerCentralThreeGenerator :
    SylowNormalizer (alternatingSixUniversalCoverSylow 2) :=
  actualNormalizerCentralThreeGenerator

/-- An enumerated actual-normalizer row evaluates on the central `C₃`
generator by its cyclic coordinate. -/
theorem
    alternatingSixTwoActualNormalizerCharacter_values_centralThreeGenerator
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    (alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r).1.values
        alternatingSixTwoActualNormalizerCentralThreeGenerator =
      (CyclicThree.thirdRootParameter r.1 : ℂ) := by
  simpa [alternatingSixTwoActualNormalizerCentralThreeGenerator] using
    actualCharacter_values_generator r

/-- The first corrected outer action inverts the value of every
actual-normalizer row on the central `C₃` generator. -/
theorem
    alternatingSixTwoCorrectedAlphaOne_smul_character_values_centralThreeGenerator
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    ((alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
          (alternatingSixUniversalCoverSylow 2)) •
        alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r).1.values
          alternatingSixTwoActualNormalizerCentralThreeGenerator =
      (CyclicThree.thirdRootParameter r.1 : ℂ)⁻¹ := by
  simpa [alternatingSixTwoActualNormalizerCentralThreeGenerator] using
    correctedAlphaOne_smul_actualCharacter_values_generator r

/-- The second corrected outer action inverts the value of every
actual-normalizer row on the central `C₃` generator. -/
theorem
    alternatingSixTwoCorrectedAlphaTwo_smul_character_values_centralThreeGenerator
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    ((alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
          (alternatingSixUniversalCoverSylow 2)) •
        alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r).1.values
          alternatingSixTwoActualNormalizerCentralThreeGenerator =
      (CyclicThree.thirdRootParameter r.1 : ℂ)⁻¹ := by
  simpa [alternatingSixTwoActualNormalizerCentralThreeGenerator] using
    correctedAlphaTwo_smul_actualCharacter_values_generator r

private theorem ctblLibTwo_candidate_symm_one :
    alternatingSixCTblLibTwoPPrimeActionData.candidate.symm (1 : Fin 12) =
      (1 : Fin 12) := by
  apply alternatingSixCTblLibTwoPPrimeActionData.candidate.injective
  rw [alternatingSixCTblLibTwoPPrimeActionData.candidate.apply_symm_apply]
  rfl

private theorem ctblLibTwo_candidate_symm_two :
    alternatingSixCTblLibTwoPPrimeActionData.candidate.symm (2 : Fin 12) =
      (2 : Fin 12) := by
  apply alternatingSixCTblLibTwoPPrimeActionData.candidate.injective
  rw [alternatingSixCTblLibTwoPPrimeActionData.candidate.apply_symm_apply]
  rfl

private theorem centralBlock_localPosition_one :
    (alternatingSixTwoCentralBlockCTblLibRowIdentification
        |>.localPositionEquiv) (1 : Fin 12) =
      ((1 : Fin 3), ((0 : Fin 2), (0 : Fin 2))) := by
  change
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        (alternatingSixAmbientTwoPPrimeRowIndexEquiv
          (alternatingSixCTblLibTwoPPrimeActionData.candidate.symm 1)) =
      _
  rw [ctblLibTwo_candidate_symm_one]
  rfl

private theorem centralBlock_localAlphaOne_one :
    (alternatingSixTwoCentralBlockCTblLibRowIdentification
        |>.localPositionEquiv)
          (alternatingSixCTblLibTwoPPrimeActionData.localAlphaOne
            (1 : Fin 12)) =
      ((1 : Fin 3), ((0 : Fin 2), (0 : Fin 2))) := by
  change
    (alternatingSixTwoCentralBlockCTblLibRowIdentification
        |>.localPositionEquiv) (1 : Fin 12) =
      _
  exact centralBlock_localPosition_one

private theorem centralBlock_localAlphaTwo_one :
    (alternatingSixTwoCentralBlockCTblLibRowIdentification
        |>.localPositionEquiv)
          (alternatingSixCTblLibTwoPPrimeActionData.localAlphaTwo
            (1 : Fin 12)) =
      ((1 : Fin 3), ((0 : Fin 2), (1 : Fin 2))) := by
  change
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        (alternatingSixAmbientTwoPPrimeRowIndexEquiv
          (alternatingSixCTblLibTwoPPrimeActionData.candidate.symm 2)) =
      _
  rw [ctblLibTwo_candidate_symm_two]
  rfl

/-- At CT position one the first audited local target retains cyclic
coordinate one, while the genuine corrected first action inverts it. -/
theorem
    alternatingSixTwoCentralBlockCTblLibRowIdentification_not_localAlphaOneBridge :
    ¬ (alternatingSixTwoCentralBlockCTblLibRowIdentification
        |>.LocalCorrectedAlphaOneBridge) := by
  intro h
  have hrow := h (1 : Fin 12)
  rw [centralBlock_localPosition_one,
    centralBlock_localAlphaOne_one] at hrow
  have hcharacter :=
    alternatingSixTwoActualNormalizerRowPermutation_character
      (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
        (alternatingSixUniversalCoverSylow 2))
      ((1 : Fin 3), ((0 : Fin 2), (0 : Fin 2)))
  have hrowActual :
      alternatingSixTwoActualNormalizerRowPermutation
          (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
            (alternatingSixUniversalCoverSylow 2))
          ((1 : Fin 3), ((0 : Fin 2), (0 : Fin 2))) =
        ((1 : Fin 3), ((0 : Fin 2), (0 : Fin 2))) := by
    simpa [alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation]
      using hrow
  rw [hrowActual] at hcharacter
  have hvalue :=
    congrArg
      (fun χ :
          PPrimeIrreducibleCharacter
            (SylowNormalizer (alternatingSixUniversalCoverSylow 2)) 2 =>
        χ.1.values actualNormalizerCentralThreeGenerator)
      hcharacter
  rw [actualCharacter_values_generator,
    correctedAlphaOne_smul_actualCharacter_values_generator,
    primitiveThirdRootParameter_one_inv] at hvalue
  exact primitiveThirdRootParameter_one_ne_two hvalue

/-- At CT position one the second audited local target also retains cyclic
coordinate one, while the genuine corrected second action inverts it. -/
theorem
    alternatingSixTwoCentralBlockCTblLibRowIdentification_not_localAlphaTwoBridge :
    ¬ (alternatingSixTwoCentralBlockCTblLibRowIdentification
        |>.LocalCorrectedAlphaTwoBridge) := by
  intro h
  have hrow := h (1 : Fin 12)
  rw [centralBlock_localPosition_one,
    centralBlock_localAlphaTwo_one] at hrow
  have hcharacter :=
    alternatingSixTwoActualNormalizerRowPermutation_character
      (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
        (alternatingSixUniversalCoverSylow 2))
      ((1 : Fin 3), ((0 : Fin 2), (0 : Fin 2)))
  have hrowActual :
      alternatingSixTwoActualNormalizerRowPermutation
          (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
            (alternatingSixUniversalCoverSylow 2))
          ((1 : Fin 3), ((0 : Fin 2), (0 : Fin 2))) =
        ((1 : Fin 3), ((0 : Fin 2), (1 : Fin 2))) := by
    simpa [alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation]
      using hrow
  rw [hrowActual] at hcharacter
  have hvalue :=
    congrArg
      (fun χ :
          PPrimeIrreducibleCharacter
            (SylowNormalizer (alternatingSixUniversalCoverSylow 2)) 2 =>
        χ.1.values actualNormalizerCentralThreeGenerator)
      hcharacter
  rw [actualCharacter_values_generator,
    correctedAlphaTwo_smul_actualCharacter_values_generator,
    primitiveThirdRootParameter_one_inv] at hvalue
  exact primitiveThirdRootParameter_one_ne_two hvalue

end InductiveMcKay
end McKayConjecture
