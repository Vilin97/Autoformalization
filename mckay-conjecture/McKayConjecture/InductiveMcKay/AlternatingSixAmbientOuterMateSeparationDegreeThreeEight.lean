/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeThreeCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeEightCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientInitialOrdinaryCharacters
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterClassValueTransport
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterDegreeEightABSquaredValues
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterDegreeThreeABSquaredValues

/-!
# Degree-three and degree-eight mate-separating values

The first outer automorphism exchanges the `AB` and `AB²` class families.
For the second automorphism, the class-19 central shift is trivial on the
relevant degree-eight central scalars.  These exact values resolve the four
degree-three and four degree-eight rows.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev classRepresentative (i : Fin 31) :
    AlternatingSixUniversalCover :=
  alternatingSixUniversalCoverClassRepresentative i

/-- The distinguished primitive 120th root has sixtieth power `-1`. -/
theorem alternatingSixComplexCyclotomicRoot_pow_sixty :
    alternatingSixComplexCyclotomicRoot ^ 60 = -1 := by
  rw [alternatingSixComplexCyclotomicRoot, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 1
  all_goals ring_nf

/-- Under the first outer action, the row-02 value at `AB²` differs from
the competing row-04 value at `AB`. -/
theorem alternatingSixAmbientAlphaOneRow02_mateTestValue_ne :
    (FDRep.of
        (alternatingSixAmbientRow02MatrixCertificate.universalCoverRepresentation)).character
          alternatingSixAmbientCanonicalGeneratorABSquared ≠
      (FDRep.of
        (alternatingSixAmbientRow04MatrixCertificate.universalCoverRepresentation)).character
          alternatingSixAmbientCanonicalGeneratorAB := by
  rw [← alternatingSixAmbientRow02CharacterRowCertificate_representation,
    ← alternatingSixAmbientRow04CharacterRowCertificate_representation,
    alternatingSixAmbientRow02_character_generatorABSquared,
    alternatingSixAmbientRow04_character_generatorAB]
  intro hequal
  apply alternatingSixAmbientRow04Row05DifferencePolynomial_ne_zero
  rw [← sub_eq_zero.mpr hequal.symm]
  simp [
    alternatingSixAmbientRow04Row05DifferencePolynomial,
    alternatingSixCyclotomicValue
  ]
  ring

/-- Under the first outer action, the row-04 value at `AB²` differs from
the competing row-02 value at `AB`. -/
theorem alternatingSixAmbientAlphaOneRow04_mateTestValue_ne :
    (FDRep.of
        (alternatingSixAmbientRow04MatrixCertificate.universalCoverRepresentation)).character
          alternatingSixAmbientCanonicalGeneratorABSquared ≠
      (FDRep.of
        (alternatingSixAmbientRow02MatrixCertificate.universalCoverRepresentation)).character
          alternatingSixAmbientCanonicalGeneratorAB := by
  rw [← alternatingSixAmbientRow04CharacterRowCertificate_representation,
    ← alternatingSixAmbientRow02CharacterRowCertificate_representation,
    alternatingSixAmbientRow04_character_generatorABSquared,
    alternatingSixAmbientRow02_character_generatorAB]
  intro hequal
  apply alternatingSixAmbientRow02Row03DifferencePolynomial_ne_zero
  rw [← sub_eq_zero.mpr hequal.symm]
  simp [
    alternatingSixAmbientRow02Row03DifferencePolynomial,
    alternatingSixCyclotomicValue
  ]
  ring

/-- Under the first outer action, row 16 takes at `AB²` a value different
from its own value at `AB`. -/
theorem alternatingSixAmbientAlphaOneRow16_mateTestValue_ne :
    (FDRep.of
        (alternatingSixAmbientRow16MatrixCertificate.universalCoverRepresentation)).character
          alternatingSixAmbientCanonicalGeneratorABSquared ≠
      (FDRep.of
        (alternatingSixAmbientRow16MatrixCertificate.universalCoverRepresentation)).character
          alternatingSixAmbientCanonicalGeneratorAB := by
  rw [← alternatingSixAmbientRow16CharacterRowCertificate_representation,
    alternatingSixAmbientRow16_character_generatorABSquared,
    alternatingSixAmbientRow16_character_generatorAB]
  intro hequal
  apply alternatingSixAmbientRow16Row17DifferencePolynomial_ne_zero
  rw [← sub_eq_zero.mpr hequal.symm]
  simp [
    alternatingSixAmbientRow16Row17DifferencePolynomial,
    alternatingSixCyclotomicValue
  ]
  ring

/-- Under the first outer action, row 18 takes at `AB²` a value different
from its own value at `AB`. -/
theorem alternatingSixAmbientAlphaOneRow18_mateTestValue_ne :
    (FDRep.of
        (alternatingSixAmbientRow18MatrixCertificate.universalCoverRepresentation)).character
          alternatingSixAmbientCanonicalGeneratorABSquared ≠
      (FDRep.of
        (alternatingSixAmbientRow18MatrixCertificate.universalCoverRepresentation)).character
          alternatingSixAmbientCanonicalGeneratorAB := by
  letI :
      Nonempty (Fin (.row18 : AlternatingSixAmbientOrdinaryRow).dimension) :=
    Fin.pos_iff_nonempty.mp
      (.row18 : AlternatingSixAmbientOrdinaryRow).dimension_pos
  rw [
    alternatingSixAmbientRow18MatrixCertificate
      |>.universalCoverRepresentation_character_generatorABSquared,
    alternatingSixAmbientRow18MatrixCertificate
      |>.universalCoverRepresentation_character_generatorAB
  ]
  change
    (alternatingSixFiveAmbient_row18_matrixA *
          alternatingSixFiveAmbient_row18_matrixB *
          alternatingSixFiveAmbient_row18_matrixB).trace ≠
      (alternatingSixFiveAmbient_row18_matrixA *
          alternatingSixFiveAmbient_row18_matrixB).trace
  rw [alternatingSixAmbientRow18_matrixABSquared_trace,
    alternatingSixAmbientRow18_matrixAB_trace]
  intro hequal
  apply alternatingSixAmbientRow18Row19DifferencePolynomial_ne_zero
  rw [← sub_eq_zero.mpr hequal.symm]
  simp [
    alternatingSixAmbientRow18Row19DifferencePolynomial,
    alternatingSixCyclotomicValue
  ]
  ring

/-- The `AB` values distinguish rows 16 and 17 for the second action. -/
theorem alternatingSixAmbientAlphaTwoRow16_mateTestValue_ne :
    alternatingSixAmbientRow16CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorAB ≠
      alternatingSixAmbientRow17CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorAB := by
  rw [alternatingSixAmbientRow16_character_generatorAB,
    alternatingSixAmbientRow17_character_generatorAB]
  intro hequal
  apply alternatingSixAmbientRow16Row17DifferencePolynomial_ne_zero
  rw [← sub_eq_zero.mpr hequal]
  simp [
    alternatingSixAmbientRow16Row17DifferencePolynomial,
    alternatingSixCyclotomicValue
  ]
  ring

/-- The `AB` values distinguish rows 18 and 19 for the second action. -/
theorem alternatingSixAmbientAlphaTwoRow18_mateTestValue_ne :
    (FDRep.of
        (alternatingSixAmbientRow18MatrixCertificate.universalCoverRepresentation)).character
          alternatingSixAmbientCanonicalGeneratorAB ≠
      (FDRep.of
        (alternatingSixAmbientRow19MatrixCertificate.universalCoverRepresentation)).character
          alternatingSixAmbientCanonicalGeneratorAB := by
  letI :
      Nonempty (Fin (.row18 : AlternatingSixAmbientOrdinaryRow).dimension) :=
    Fin.pos_iff_nonempty.mp
      (.row18 : AlternatingSixAmbientOrdinaryRow).dimension_pos
  letI :
      Nonempty (Fin (.row19 : AlternatingSixAmbientOrdinaryRow).dimension) :=
    Fin.pos_iff_nonempty.mp
      (.row19 : AlternatingSixAmbientOrdinaryRow).dimension_pos
  rw [
    alternatingSixAmbientRow18MatrixCertificate
      |>.universalCoverRepresentation_character_generatorAB,
    alternatingSixAmbientRow19MatrixCertificate
      |>.universalCoverRepresentation_character_generatorAB
  ]
  change
    (alternatingSixFiveAmbient_row18_matrixA *
          alternatingSixFiveAmbient_row18_matrixB).trace ≠
      (alternatingSixFiveAmbient_row19_matrixA *
          alternatingSixFiveAmbient_row19_matrixB).trace
  exact
    alternatingSixAmbientRow18_matrixAB_trace_ne_row19_matrixAB_trace

/-- The class-19 value of row 16 differs from the competing row-17
class-15 value. -/
theorem alternatingSixAmbientAlphaTwoRow16_classMateTestValue_ne :
    (FDRep.of
        (alternatingSixAmbientRow16MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 19) ≠
      (FDRep.of
        (alternatingSixAmbientRow17MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 15) := by
  let C :=
    alternatingSixAmbientInitialOrdinaryCharacterRowCertificate
      .row16 (by decide)
  have hshift := C.irreducibleCharacter_values_classRepresentative_nineteen
  rw [C.characterRowCertificate.irreducibleCharacter_values_apply,
    C.characterRowCertificate.irreducibleCharacter_values_apply] at hshift
  change
    (FDRep.of
        (alternatingSixAmbientRow16MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 19) =
      (alternatingSixComplexCyclotomicRoot ^ 0) ^ 4 *
        (FDRep.of
          (alternatingSixAmbientRow16MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 15) at hshift
  simp only [pow_zero, one_pow, one_mul] at hshift
  rw [hshift]
  simpa only [classRepresentative,
    ← alternatingSixAmbientCanonicalGeneratorAB_eq_classRepresentative,
    alternatingSixAmbientRow16CharacterRowCertificate_representation,
    alternatingSixAmbientRow17CharacterRowCertificate_representation] using
    alternatingSixAmbientAlphaTwoRow16_mateTestValue_ne

/-- The class-19 value of row 18 differs from the competing row-19
class-15 value. -/
theorem alternatingSixAmbientAlphaTwoRow18_classMateTestValue_ne :
    (FDRep.of
        (alternatingSixAmbientRow18MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 19) ≠
      (FDRep.of
        (alternatingSixAmbientRow19MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 15) := by
  let C :=
    alternatingSixAmbientInitialOrdinaryCharacterRowCertificate
      .row18 (by decide)
  have hshift := C.irreducibleCharacter_values_classRepresentative_nineteen
  rw [C.characterRowCertificate.irreducibleCharacter_values_apply,
    C.characterRowCertificate.irreducibleCharacter_values_apply] at hshift
  change
    (FDRep.of
        (alternatingSixAmbientRow18MatrixCertificate.universalCoverRepresentation)).character
          (classRepresentative 19) =
      (alternatingSixComplexCyclotomicRoot ^ 60) ^ 4 *
        (FDRep.of
          (alternatingSixAmbientRow18MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 15) at hshift
  rw [show
      (alternatingSixComplexCyclotomicRoot ^ 60) ^ 4 = 1 by
        rw [alternatingSixComplexCyclotomicRoot_pow_sixty]
        norm_num] at hshift
  simp only [one_mul] at hshift
  rw [hshift]
  simpa only [classRepresentative,
    ← alternatingSixAmbientCanonicalGeneratorAB_eq_classRepresentative] using
    alternatingSixAmbientAlphaTwoRow18_mateTestValue_ne

end InductiveMcKay
end McKayConjecture
