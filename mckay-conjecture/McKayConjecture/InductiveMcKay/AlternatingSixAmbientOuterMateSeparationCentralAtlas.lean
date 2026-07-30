/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeSixCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeTenCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P1ClassValues
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P11ClassValues
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerSevenClassValues
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerTwoClassValues
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasDegreeTwelveTraceSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterMateSeparationDegreeThreeEight
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow24ClassValues
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow25ClassValues

/-!
# Central-shift and ATLAS mate-separating values

Central shifts of the `B` and `AB` representatives resolve the degree-three,
degree-six, and degree-ten signatures.  The same calculation on the four
ATLAS degree-twelve rows gives their two outer permutations.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev classRepresentative (i : Fin 31) :
    AlternatingSixUniversalCover :=
  alternatingSixUniversalCoverClassRepresentative i

private theorem degreeSixNegativeValue_eq_pairedValue :
    -alternatingSixCyclotomicValue
        [(-1, 5), (-1, 15), (1, 25)] =
      alternatingSixCyclotomicValue
        [(1, 5), (1, 15), (-1, 25)] := by
  simp [alternatingSixCyclotomicValue]
  ring

/-- The central shift of the row-12 `B` value differs from the competing
row-14 `B` value. -/
theorem alternatingSixAmbientAlphaOneRow12_mateTestValue_ne :
    (FDRep.of
        (alternatingSixAmbientRow12MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 12) ≠
      (FDRep.of
        (alternatingSixAmbientRow14MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 9) := by
  let C :=
    alternatingSixAmbientInitialOrdinaryCharacterRowCertificate
      .row12 (by decide)
  have hshift := C.irreducibleCharacter_values_classRepresentative_twelve
  rw [C.characterRowCertificate.irreducibleCharacter_values_apply,
    C.characterRowCertificate.irreducibleCharacter_values_apply] at hshift
  change
    (FDRep.of
        (alternatingSixAmbientRow12MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 12) =
      (alternatingSixComplexCyclotomicRoot ^ 20) ^ 3 *
        (FDRep.of
          (alternatingSixAmbientRow12MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 9) at hshift
  rw [hshift]
  simp only [classRepresentative]
  rw [← alternatingSixAmbientCanonicalGeneratorB_eq_classRepresentative]
  rw [← alternatingSixAmbientRow12CharacterRowCertificate_representation,
    ← alternatingSixAmbientRow14CharacterRowCertificate_representation]
  rw [show
      (alternatingSixComplexCyclotomicRoot ^ 20) ^ 3 = -1 by
        rw [← pow_mul, show 20 * 3 = 60 by norm_num,
          alternatingSixComplexCyclotomicRoot_pow_sixty],
    alternatingSixAmbientRow12_character_generatorB,
    alternatingSixAmbientRow14_character_generatorB]
  intro hequal
  apply alternatingSixAmbientDegreeSixPairedGeneratorValues_ne
  calc
    alternatingSixCyclotomicValue
          [(-1, 5), (-1, 15), (1, 25)] =
        -alternatingSixCyclotomicValue
          [(-1, 5), (-1, 15), (1, 25)] := by
      simpa only [neg_mul, one_mul] using hequal.symm
    _ =
        alternatingSixCyclotomicValue
          [(1, 5), (1, 15), (-1, 25)] :=
      degreeSixNegativeValue_eq_pairedValue

/-- The central shift of the row-14 `B` value differs from the competing
row-12 `B` value. -/
theorem alternatingSixAmbientAlphaOneRow14_mateTestValue_ne :
    (FDRep.of
        (alternatingSixAmbientRow14MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 12) ≠
      (FDRep.of
        (alternatingSixAmbientRow12MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 9) := by
  let C :=
    alternatingSixAmbientInitialOrdinaryCharacterRowCertificate
      .row14 (by decide)
  have hshift := C.irreducibleCharacter_values_classRepresentative_twelve
  rw [C.characterRowCertificate.irreducibleCharacter_values_apply,
    C.characterRowCertificate.irreducibleCharacter_values_apply] at hshift
  change
    (FDRep.of
        (alternatingSixAmbientRow14MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 12) =
      (alternatingSixComplexCyclotomicRoot ^ 100) ^ 3 *
        (FDRep.of
          (alternatingSixAmbientRow14MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 9) at hshift
  rw [hshift]
  simp only [classRepresentative]
  rw [← alternatingSixAmbientCanonicalGeneratorB_eq_classRepresentative]
  rw [← alternatingSixAmbientRow14CharacterRowCertificate_representation,
    ← alternatingSixAmbientRow12CharacterRowCertificate_representation]
  rw [show
      (alternatingSixComplexCyclotomicRoot ^ 100) ^ 3 = -1 by
        rw [← pow_mul, show 100 * 3 = 300 by norm_num,
          pow_eq_pow_mod 300
            alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one]
        norm_num
        exact alternatingSixComplexCyclotomicRoot_pow_sixty,
    alternatingSixAmbientRow14_character_generatorB,
    alternatingSixAmbientRow12_character_generatorB]
  intro hequal
  apply alternatingSixAmbientDegreeSixPairedGeneratorValues_ne
  calc
    alternatingSixCyclotomicValue
          [(-1, 5), (-1, 15), (1, 25)] =
        -alternatingSixCyclotomicValue
          [(-1, 5), (-1, 15), (1, 25)] := by
      simpa only [neg_mul, one_mul] using hequal.symm
    _ =
        alternatingSixCyclotomicValue
          [(1, 5), (1, 15), (-1, 25)] :=
      degreeSixNegativeValue_eq_pairedValue

/-- For the second action, the row-12 `B` value differs from the competing
row-15 value. -/
theorem alternatingSixAmbientAlphaTwoRow12_mateTestValue_ne :
    alternatingSixAmbientRow12CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorB ≠
      alternatingSixAmbientRow15CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorB := by
  rw [alternatingSixAmbientRow12_character_generatorB,
    alternatingSixAmbientRow15_character_generatorB]
  exact alternatingSixAmbientDegreeSixPairedGeneratorValues_ne

/-- For the second action, the row-14 `B` value differs from the competing
row-13 value. -/
theorem alternatingSixAmbientAlphaTwoRow14_mateTestValue_ne :
    alternatingSixAmbientRow14CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorB ≠
      alternatingSixAmbientRow13CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorB := by
  rw [alternatingSixAmbientRow14_character_generatorB,
    alternatingSixAmbientRow13_character_generatorB]
  exact alternatingSixAmbientDegreeSixPairedGeneratorValues_ne

/-- The row-24 central shift at class 12 differs from its unshifted class-9
value, as needed for the first action. -/
theorem alternatingSixAmbientAlphaOneRow24_mateTestValue_ne :
    (FDRep.of
        (alternatingSixAmbientRow24MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 12) ≠
      (FDRep.of
        (alternatingSixAmbientRow24MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 9) := by
  simp only [classRepresentative]
  change
    (FDRep.of
        (alternatingSixAmbientRow24ClassMatrixCertificate
          |>.universalCoverRepresentation)).character
          (alternatingSixSchurCoordinatesEquivUniversalCover
            (alternatingSixSchurClassRepresentative 12)) ≠
      (FDRep.of
        (alternatingSixAmbientRow24ClassMatrixCertificate
          |>.universalCoverRepresentation)).character
          (alternatingSixSchurCoordinatesEquivUniversalCover
            (alternatingSixSchurClassRepresentative 9))
  rw [alternatingSixAmbientRow24_character_classRepresentative,
    alternatingSixAmbientRow24_character_classRepresentative]
  change
    -alternatingSixAmbientRow24Gamma ≠
      alternatingSixAmbientRow24Gamma
  intro hequal
  apply alternatingSixAmbientDegreeSixPairedGeneratorValues_ne
  calc
    alternatingSixCyclotomicValue
          [(-1, 5), (-1, 15), (1, 25)] =
        -alternatingSixCyclotomicValue
          [(-1, 5), (-1, 15), (1, 25)] := by
      simpa [alternatingSixAmbientRow24Gamma] using hequal.symm
    _ =
        alternatingSixCyclotomicValue
          [(1, 5), (1, 15), (-1, 25)] :=
      degreeSixNegativeValue_eq_pairedValue

/-- The class-9 values distinguish rows 24 and 25 for the second action. -/
theorem alternatingSixAmbientAlphaTwoRow24_mateTestValue_ne :
    (FDRep.of
        (alternatingSixAmbientRow24MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 9) ≠
      (FDRep.of
        (alternatingSixAmbientRow25MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 9) := by
  simp only [classRepresentative]
  change
    (FDRep.of
        (alternatingSixAmbientRow24ClassMatrixCertificate
          |>.universalCoverRepresentation)).character
          (alternatingSixSchurCoordinatesEquivUniversalCover
            (alternatingSixSchurClassRepresentative 9)) ≠
      (FDRep.of
        (alternatingSixAmbientRow25ClassMatrixCertificate
          |>.universalCoverRepresentation)).character
          (alternatingSixSchurCoordinatesEquivUniversalCover
            (alternatingSixSchurClassRepresentative 9))
  rw [alternatingSixAmbientRow24_character_classRepresentative,
    alternatingSixAmbientRow25_character_classRepresentative]
  change
    alternatingSixAmbientRow24Gamma ≠
      alternatingSixAmbientRow25Gamma
  simpa [
    alternatingSixAmbientRow24Gamma,
    alternatingSixAmbientRow25Gamma
  ] using alternatingSixAmbientDegreeSixPairedGeneratorValues_ne

/-- The power-one `AB²` value differs from the competing power-eleven
`AB` value for the first action. -/
theorem alternatingSixAmbientAlphaOneAtlasPowerOne_mateTestValue_ne :
    (FDRep.of
        (alternatingSixAmbientAtlas12P1ClassMatrixCertificate
          |>.universalCoverRepresentation)).character
          (classRepresentative 21) ≠
      (FDRep.of
        (alternatingSixAmbientAtlas12P11ClassMatrixCertificate
          |>.universalCoverRepresentation)).character
          (classRepresentative 15) := by
  simp only [classRepresentative,
    alternatingSixUniversalCoverClassRepresentative]
  rw [alternatingSixAmbientAtlas12P1_character_classRepresentative,
    alternatingSixAmbientAtlas12P11_character_classRepresentative]
  change
    alternatingSixAmbientAtlas12P1Beta ≠
      alternatingSixAmbientAtlas12P11Alpha
  have hpair :=
    alternatingSixAmbientAtlas12Power2_matrixAB_trace_ne_power11_matrixAB_trace
  rw [alternatingSixAmbientAtlas12Power2_matrixAB_trace,
    alternatingSixAmbientAtlas12Power11_matrixAB_trace] at hpair
  simpa [
    alternatingSixAmbientAtlas12P1Beta,
    alternatingSixAmbientAtlas12P11Alpha
  ] using hpair

/-- The power-two `AB²` value differs from the competing power-seven
`AB` value for the first action. -/
theorem alternatingSixAmbientAlphaOneAtlasPowerTwo_mateTestValue_ne :
    (FDRep.of
        (alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate
          |>.universalCoverRepresentation)).character
          (classRepresentative 21) ≠
      (FDRep.of
        (alternatingSixAmbientAtlasTwelvePowerSevenClassMatrixCertificate
          |>.universalCoverRepresentation)).character
          (classRepresentative 15) := by
  simp only [classRepresentative,
    alternatingSixUniversalCoverClassRepresentative]
  rw [
    alternatingSixAmbientAtlasTwelvePowerTwo_character_classRepresentative,
    alternatingSixAmbientAtlasTwelvePowerSeven_character_classRepresentative
  ]
  change
    alternatingSixAmbientAtlasTwelvePowerTwoBeta ≠
      alternatingSixAmbientAtlasTwelvePowerSevenAlpha
  have hpair :=
    alternatingSixAmbientAtlas12Power1_matrixAB_trace_ne_power7_matrixAB_trace
  rw [alternatingSixAmbientAtlas12Power1_matrixAB_trace,
    alternatingSixAmbientAtlas12Power7_matrixAB_trace] at hpair
  simpa [
    alternatingSixAmbientAtlasTwelvePowerTwoBeta,
    alternatingSixAmbientAtlasTwelvePowerSevenAlpha
  ] using hpair

/-- Four central shifts turn the power-one `AB` value into the
power-eleven `AB` value. -/
theorem alternatingSixAmbientAtlasPowerOne_centralFourth_mul_alpha :
    alternatingSixAmbientAtlas12P1Eta ^ 4 *
        alternatingSixAmbientAtlas12P1Alpha =
      alternatingSixAmbientAtlas12P11Alpha := by
  change
    (alternatingSixComplexCyclotomicRoot ^ 20) ^ 4 *
        alternatingSixCyclotomicValue
          [(-1, 0), (-1, 4), (1, 8), (1, 12),
            (1, 16), (-1, 28)] =
      alternatingSixCyclotomicValue [(1, 4), (-1, 16)]
  rw [← pow_mul]
  norm_num
  linear_combination
    (-alternatingSixComplexCyclotomicRoot ^ 76 +
      alternatingSixComplexCyclotomicRoot ^ 72 -
      alternatingSixComplexCyclotomicRoot ^ 68 +
      alternatingSixComplexCyclotomicRoot ^ 64 +
      alternatingSixComplexCyclotomicRoot ^ 44 -
      alternatingSixComplexCyclotomicRoot ^ 40 +
      alternatingSixComplexCyclotomicRoot ^ 36 -
      alternatingSixComplexCyclotomicRoot ^ 32 +
      alternatingSixComplexCyclotomicRoot ^ 28 -
      alternatingSixComplexCyclotomicRoot ^ 20 +
      alternatingSixComplexCyclotomicRoot ^ 16 -
      alternatingSixComplexCyclotomicRoot ^ 12 +
      alternatingSixComplexCyclotomicRoot ^ 8 -
      alternatingSixComplexCyclotomicRoot ^ 4) *
        alternatingSixComplexCyclotomicRoot_relation

/-- Four central shifts turn the power-two `AB` value into the power-seven
`AB` value. -/
theorem alternatingSixAmbientAtlasPowerTwo_centralFourth_mul_alpha :
    alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 4 *
        alternatingSixAmbientAtlasTwelvePowerTwoAlpha =
      alternatingSixAmbientAtlasTwelvePowerSevenAlpha := by
  rw [←
    alternatingSixAmbientAtlasTwelvePowerTwo_root_pow_hundred]
  change
    (alternatingSixComplexCyclotomicRoot ^ 100) ^ 4 *
        alternatingSixCyclotomicValue
          [(-1, 0), (-1, 4), (1, 16), (1, 20)] =
      alternatingSixCyclotomicValue
        [(1, 0), (1, 4), (-1, 8), (-1, 12), (-1, 16),
          (-1, 20), (1, 28)]
  rw [← pow_mul]
  rw [pow_eq_pow_mod 400
    alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one]
  norm_num
  linear_combination
    (alternatingSixComplexCyclotomicRoot ^ 28 +
      alternatingSixComplexCyclotomicRoot ^ 16 -
      alternatingSixComplexCyclotomicRoot ^ 12 +
      alternatingSixComplexCyclotomicRoot ^ 8 - 1) *
        alternatingSixComplexCyclotomicRoot_relation

/-- The centrally shifted power-one value differs from the competing
power-two value for the second action. -/
theorem alternatingSixAmbientAlphaTwoAtlasPowerOne_mateTestValue_ne :
    (FDRep.of
        (alternatingSixAmbientAtlas12P1ClassMatrixCertificate
          |>.universalCoverRepresentation)).character
          (classRepresentative 19) ≠
      (FDRep.of
        (alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate
          |>.universalCoverRepresentation)).character
          (classRepresentative 15) := by
  simp only [classRepresentative,
    alternatingSixUniversalCoverClassRepresentative]
  rw [alternatingSixAmbientAtlas12P1_character_classRepresentative,
    alternatingSixAmbientAtlasTwelvePowerTwo_character_classRepresentative]
  change
    alternatingSixAmbientAtlas12P1Eta ^ 4 *
        alternatingSixAmbientAtlas12P1Alpha ≠
      alternatingSixAmbientAtlasTwelvePowerTwoAlpha
  rw [alternatingSixAmbientAtlasPowerOne_centralFourth_mul_alpha]
  have hpair :=
    alternatingSixAmbientAtlas12Power2_matrixAB_trace_ne_power11_matrixAB_trace
  rw [alternatingSixAmbientAtlas12Power2_matrixAB_trace,
    alternatingSixAmbientAtlas12Power11_matrixAB_trace] at hpair
  simpa [
    alternatingSixAmbientAtlasTwelvePowerTwoAlpha,
    alternatingSixAmbientAtlas12P11Alpha
  ] using hpair.symm

/-- The centrally shifted power-two value differs from the competing
power-one value for the second action. -/
theorem alternatingSixAmbientAlphaTwoAtlasPowerTwo_mateTestValue_ne :
    (FDRep.of
        (alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate
          |>.universalCoverRepresentation)).character
          (classRepresentative 19) ≠
      (FDRep.of
        (alternatingSixAmbientAtlas12P1ClassMatrixCertificate
          |>.universalCoverRepresentation)).character
          (classRepresentative 15) := by
  simp only [classRepresentative,
    alternatingSixUniversalCoverClassRepresentative]
  rw [
    alternatingSixAmbientAtlasTwelvePowerTwo_character_classRepresentative,
    alternatingSixAmbientAtlas12P1_character_classRepresentative
  ]
  change
    alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 4 *
        alternatingSixAmbientAtlasTwelvePowerTwoAlpha ≠
      alternatingSixAmbientAtlas12P1Alpha
  rw [alternatingSixAmbientAtlasPowerTwo_centralFourth_mul_alpha]
  have hpair :=
    alternatingSixAmbientAtlas12Power1_matrixAB_trace_ne_power7_matrixAB_trace
  rw [alternatingSixAmbientAtlas12Power1_matrixAB_trace,
    alternatingSixAmbientAtlas12Power7_matrixAB_trace] at hpair
  simpa [
    alternatingSixAmbientAtlas12P1Alpha,
    alternatingSixAmbientAtlasTwelvePowerSevenAlpha
  ] using hpair.symm

/-- Four shifts by the positive order-three scalar turn the row-02 `AB`
value into the row-04 value. -/
theorem alternatingSixAmbientRow02_centralFourth_mul_generatorAB :
    (alternatingSixComplexCyclotomicRoot ^ 80) ^ 4 *
        alternatingSixCyclotomicValue
          [(-1, 0), (-1, 4), (1, 8), (1, 12),
            (1, 16), (-1, 28)] =
      alternatingSixCyclotomicValue [(1, 4), (-1, 16)] := by
  have hfactor :
      (alternatingSixComplexCyclotomicRoot ^ 80) ^ 4 =
        (alternatingSixComplexCyclotomicRoot ^ 20) ^ 4 := by
    rw [← pow_mul, ← pow_mul]
    rw [pow_eq_pow_mod 320
      alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one]
  rw [hfactor]
  exact alternatingSixAmbientAtlasPowerOne_centralFourth_mul_alpha

/-- Four shifts by the negative order-three scalar turn the row-04 `AB`
value into the row-02 value. -/
theorem alternatingSixAmbientRow04_centralFourth_mul_generatorAB :
    (alternatingSixComplexCyclotomicRoot ^ 40) ^ 4 *
        alternatingSixCyclotomicValue [(1, 4), (-1, 16)] =
      alternatingSixCyclotomicValue
        [(-1, 0), (-1, 4), (1, 8), (1, 12),
          (1, 16), (-1, 28)] := by
  rw [← pow_mul]
  rw [pow_eq_pow_mod 160
    alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one]
  norm_num
  linear_combination
    (-alternatingSixComplexCyclotomicRoot ^ 24 +
      alternatingSixComplexCyclotomicRoot ^ 20 -
      alternatingSixComplexCyclotomicRoot ^ 16 +
      alternatingSixComplexCyclotomicRoot ^ 12 -
      alternatingSixComplexCyclotomicRoot ^ 8 + 1) *
        alternatingSixComplexCyclotomicRoot_relation

/-- The centrally shifted row-02 value differs from the competing row-05
value for the second action. -/
theorem alternatingSixAmbientAlphaTwoRow02_mateTestValue_ne :
    (FDRep.of
        (alternatingSixAmbientRow02MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 19) ≠
      (FDRep.of
        (alternatingSixAmbientRow05MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 15) := by
  let C :=
    alternatingSixAmbientInitialOrdinaryCharacterRowCertificate
      .row02 (by decide)
  have hshift := C.irreducibleCharacter_values_classRepresentative_nineteen
  rw [C.characterRowCertificate.irreducibleCharacter_values_apply,
    C.characterRowCertificate.irreducibleCharacter_values_apply] at hshift
  change
    (FDRep.of
        (alternatingSixAmbientRow02MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 19) =
      (alternatingSixComplexCyclotomicRoot ^ 80) ^ 4 *
        (FDRep.of
          (alternatingSixAmbientRow02MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 15) at hshift
  rw [hshift]
  simp only [classRepresentative]
  rw [← alternatingSixAmbientCanonicalGeneratorAB_eq_classRepresentative]
  rw [← alternatingSixAmbientRow02CharacterRowCertificate_representation,
    ← alternatingSixAmbientRow05CharacterRowCertificate_representation]
  rw [alternatingSixAmbientRow02_character_generatorAB,
    alternatingSixAmbientRow05_character_generatorAB,
    alternatingSixAmbientRow02_centralFourth_mul_generatorAB]
  intro hequal
  apply alternatingSixAmbientRow04Row05DifferencePolynomial_ne_zero
  rw [← sub_eq_zero.mpr hequal]
  simp [
    alternatingSixAmbientRow04Row05DifferencePolynomial,
    alternatingSixCyclotomicValue
  ]
  ring

/-- The centrally shifted row-04 value differs from the competing row-03
value for the second action. -/
theorem alternatingSixAmbientAlphaTwoRow04_mateTestValue_ne :
    (FDRep.of
        (alternatingSixAmbientRow04MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 19) ≠
      (FDRep.of
        (alternatingSixAmbientRow03MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 15) := by
  let C :=
    alternatingSixAmbientInitialOrdinaryCharacterRowCertificate
      .row04 (by decide)
  have hshift := C.irreducibleCharacter_values_classRepresentative_nineteen
  rw [C.characterRowCertificate.irreducibleCharacter_values_apply,
    C.characterRowCertificate.irreducibleCharacter_values_apply] at hshift
  change
    (FDRep.of
        (alternatingSixAmbientRow04MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 19) =
      (alternatingSixComplexCyclotomicRoot ^ 40) ^ 4 *
        (FDRep.of
          (alternatingSixAmbientRow04MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 15) at hshift
  rw [hshift]
  simp only [classRepresentative]
  rw [← alternatingSixAmbientCanonicalGeneratorAB_eq_classRepresentative]
  rw [← alternatingSixAmbientRow04CharacterRowCertificate_representation,
    ← alternatingSixAmbientRow03CharacterRowCertificate_representation]
  rw [alternatingSixAmbientRow04_character_generatorAB,
    alternatingSixAmbientRow03_character_generatorAB,
    alternatingSixAmbientRow04_centralFourth_mul_generatorAB]
  intro hequal
  apply alternatingSixAmbientRow02Row03DifferencePolynomial_ne_zero
  rw [← sub_eq_zero.mpr hequal]
  simp [
    alternatingSixAmbientRow02Row03DifferencePolynomial,
    alternatingSixCyclotomicValue
  ]
  ring

end InductiveMcKay
end McKayConjecture
