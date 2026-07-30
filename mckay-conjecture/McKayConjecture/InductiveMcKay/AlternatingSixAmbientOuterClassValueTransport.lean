/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InnerAutomorphism
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterClassActionUniversal
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassRepresentativeMatrixEvaluation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterSelectedClassRepresentatives

/-!
# Class-value transport for the ambient outer-row proof

The audited class index is complete: equal indices are equivalent to
conjugacy.  Consequently irreducible-character values can be transported
using only class-index calculations.  Two small matrix lemmas also record
the central shifts of the `B` and `AB` representatives used by the outer
automorphisms.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- Two canonical-cover elements with the same audited class index are
conjugate. -/
theorem alternatingSixUniversalCover_isConj_of_classIndex_eq
    {x y : AlternatingSixUniversalCover}
    (hindex :
      alternatingSixUniversalCoverClassIndex x =
        alternatingSixUniversalCoverClassIndex y) :
    IsConj x y := by
  let coordinateEquiv :=
    alternatingSixSchurCoordinatesEquivUniversalCover
  let xCoordinate := coordinateEquiv.symm x
  let yCoordinate := coordinateEquiv.symm y
  have hcoordinateIndex :
      alternatingSixSchurClassIndex xCoordinate =
        alternatingSixSchurClassIndex yCoordinate := by
    simpa [alternatingSixUniversalCoverClassIndex, xCoordinate,
      yCoordinate, coordinateEquiv] using hindex
  have hx :
      IsConj
        (alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex xCoordinate))
        xCoordinate :=
    isConj_iff.mpr
      ⟨alternatingSixSchurClassConjugator xCoordinate,
        alternatingSixSchurClassConjugator_spec xCoordinate⟩
  have hy :
      IsConj
        (alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex yCoordinate))
        yCoordinate :=
    isConj_iff.mpr
      ⟨alternatingSixSchurClassConjugator yCoordinate,
        alternatingSixSchurClassConjugator_spec yCoordinate⟩
  have hxy : IsConj xCoordinate yCoordinate := by
    exact hx.symm.trans (hcoordinateIndex ▸ hy)
  simpa [xCoordinate, yCoordinate, coordinateEquiv] using
    coordinateEquiv.toMonoidHom.map_isConj hxy

/-- Irreducible-character values depend only on the audited class index. -/
theorem alternatingSixIrreducibleCharacter_values_eq_of_classIndex_eq
    (χ : IrreducibleCharacter AlternatingSixUniversalCover)
    {x y : AlternatingSixUniversalCover}
    (hindex :
      alternatingSixUniversalCoverClassIndex x =
        alternatingSixUniversalCoverClassIndex y) :
    χ.values x = χ.values y :=
  IrreducibleCharacter.values_eq_of_isConj χ
    (alternatingSixUniversalCover_isConj_of_classIndex_eq hindex)

/-- Pullback by the first automorphism sends a value on a checked
representative to the value on the inverse-permuted representative. -/
theorem
    alternatingSixUniversalCoverAlphaOneAutomorphism_smul_values_representative
    (χ : IrreducibleCharacter AlternatingSixUniversalCover)
    (i : Fin 31) :
    (alternatingSixUniversalCoverAlphaOneAutomorphism • χ).values
        (alternatingSixUniversalCoverClassRepresentative i) =
      χ.values
        (alternatingSixUniversalCoverClassRepresentative
          (alternatingSixSchurAlphaOneClassIndexAction.symm i)) := by
  rw [IrreducibleCharacter.smul_values]
  apply alternatingSixIrreducibleCharacter_values_eq_of_classIndex_eq
  rw [
    alternatingSixUniversalCoverAlphaOneAutomorphism_symm_classIndex,
    alternatingSixUniversalCoverClassIndex_representative,
    alternatingSixUniversalCoverClassIndex_representative
  ]

/-- Pullback by the second automorphism sends a value on a checked
representative to the value on the inverse-permuted representative. -/
theorem
    alternatingSixUniversalCoverAlphaTwoAutomorphism_smul_values_representative
    (χ : IrreducibleCharacter AlternatingSixUniversalCover)
    (i : Fin 31) :
    (alternatingSixUniversalCoverAlphaTwoAutomorphism • χ).values
        (alternatingSixUniversalCoverClassRepresentative i) =
      χ.values
        (alternatingSixUniversalCoverClassRepresentative
          (alternatingSixSchurAlphaTwoClassIndexAction.symm i)) := by
  rw [IrreducibleCharacter.smul_values]
  apply alternatingSixIrreducibleCharacter_values_eq_of_classIndex_eq
  rw [
    alternatingSixUniversalCoverAlphaTwoAutomorphism_symm_classIndex,
    alternatingSixUniversalCoverClassIndex_representative,
    alternatingSixUniversalCoverClassIndex_representative
  ]

/-- Values on checked representative 28 agree with values on the positive
state-77 separator belonging to that class. -/
theorem alternatingSixIrreducibleCharacter_values_representative_twentyEight
    (χ : IrreducibleCharacter AlternatingSixUniversalCover) :
    χ.values (alternatingSixUniversalCoverClassRepresentative 28) =
      χ.values alternatingSixAmbientCanonicalSeparator := by
  apply alternatingSixIrreducibleCharacter_values_eq_of_classIndex_eq
  rw [alternatingSixUniversalCoverClassIndex_representative,
    alternatingSixAmbientCanonicalSeparator_classIndex]

/-- Values on checked representative 30 agree with values on the positive
state-79 separator belonging to that class. -/
theorem alternatingSixIrreducibleCharacter_values_representative_thirty
    (χ : IrreducibleCharacter AlternatingSixUniversalCover) :
    χ.values (alternatingSixUniversalCoverClassRepresentative 30) =
      χ.values alternatingSixAmbientCanonicalSecondSeparator := by
  apply alternatingSixIrreducibleCharacter_values_eq_of_classIndex_eq
  rw [alternatingSixUniversalCoverClassIndex_representative,
    alternatingSixAmbientCanonicalSecondSeparator_classIndex]

namespace AlternatingSixAmbientOrdinaryCharacterRowCertificate

variable {row : AlternatingSixAmbientOrdinaryRow}
variable (C : AlternatingSixAmbientOrdinaryCharacterRowCertificate row)

private abbrev classRepresentative (i : Fin 31) :
    AlternatingSixUniversalCover :=
  alternatingSixUniversalCoverClassRepresentative i

/-- Representative `12` is `B` followed by the third power of the first
central scalar. -/
theorem irreducibleCharacter_values_classRepresentative_twelve :
    C.characterRowCertificate.irreducibleCharacter.values
        (classRepresentative 12) =
      (alternatingSixComplexCyclotomicRoot ^
          row.scalarPattern.exponent 0) ^ 3 *
        C.characterRowCertificate.irreducibleCharacter.values
          (classRepresentative 9) := by
  letI : Nonempty (Fin row.dimension) :=
    Fin.pos_iff_nonempty.mp row.dimension_pos
  rw [C.characterRowCertificate.irreducibleCharacter_values_apply,
    C.characterRowCertificate.irreducibleCharacter_values_apply]
  change
    (FDRep.of C.matrixRow.universalCoverRepresentation).character
        (classRepresentative 12) =
      _ *
        (FDRep.of C.matrixRow.universalCoverRepresentation).character
          (classRepresentative 9)
  simp only [classRepresentative,
    alternatingSixUniversalCoverClassRepresentative]
  rw [C.matrixRow.universalCoverRepresentation_character_classRepresentative,
    C.matrixRow.universalCoverRepresentation_character_classRepresentative]
  simp [AlternatingSixSchurMatrixRowCertificate.classRepresentativeGL,
    alternatingSixAmbientClassRepresentativeBaseWord,
    alternatingSixAmbientClassRepresentativeCentralExponent,
    AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
    C.relatorScalar_eq_scalarPattern]
  rw [show
    ((alternatingSixComplexCyclotomicRoot ^
          row.scalarPattern.exponent 0) •
        (1 : Matrix (Fin row.dimension) (Fin row.dimension) ℂ)) ^ 3 =
      (alternatingSixComplexCyclotomicRoot ^
          row.scalarPattern.exponent 0) ^ 3 •
        (1 : Matrix (Fin row.dimension) (Fin row.dimension) ℂ) by
      rw [show
          (alternatingSixComplexCyclotomicRoot ^
                row.scalarPattern.exponent 0) •
              (1 : Matrix (Fin row.dimension) (Fin row.dimension) ℂ) =
            algebraMap ℂ
              (Matrix (Fin row.dimension) (Fin row.dimension) ℂ)
              (alternatingSixComplexCyclotomicRoot ^
                row.scalarPattern.exponent 0) by
            rw [Algebra.algebraMap_eq_smul_one],
        ← map_pow, Algebra.algebraMap_eq_smul_one],
    Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
  rfl

/-- Representative `19` is `AB` followed by the fourth power of the first
central scalar. -/
theorem irreducibleCharacter_values_classRepresentative_nineteen :
    C.characterRowCertificate.irreducibleCharacter.values
        (classRepresentative 19) =
      (alternatingSixComplexCyclotomicRoot ^
          row.scalarPattern.exponent 0) ^ 4 *
        C.characterRowCertificate.irreducibleCharacter.values
          (classRepresentative 15) := by
  letI : Nonempty (Fin row.dimension) :=
    Fin.pos_iff_nonempty.mp row.dimension_pos
  rw [C.characterRowCertificate.irreducibleCharacter_values_apply,
    C.characterRowCertificate.irreducibleCharacter_values_apply]
  change
    (FDRep.of C.matrixRow.universalCoverRepresentation).character
        (classRepresentative 19) =
      _ *
        (FDRep.of C.matrixRow.universalCoverRepresentation).character
          (classRepresentative 15)
  simp only [classRepresentative,
    alternatingSixUniversalCoverClassRepresentative]
  rw [C.matrixRow.universalCoverRepresentation_character_classRepresentative,
    C.matrixRow.universalCoverRepresentation_character_classRepresentative]
  simp [AlternatingSixSchurMatrixRowCertificate.classRepresentativeGL,
    alternatingSixAmbientClassRepresentativeBaseWord,
    alternatingSixAmbientClassRepresentativeCentralExponent,
    AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
    C.relatorScalar_eq_scalarPattern]
  rw [show
    ((alternatingSixComplexCyclotomicRoot ^
          row.scalarPattern.exponent 0) •
        (1 : Matrix (Fin row.dimension) (Fin row.dimension) ℂ)) ^ 4 =
      (alternatingSixComplexCyclotomicRoot ^
          row.scalarPattern.exponent 0) ^ 4 •
        (1 : Matrix (Fin row.dimension) (Fin row.dimension) ℂ) by
      rw [show
          (alternatingSixComplexCyclotomicRoot ^
                row.scalarPattern.exponent 0) •
              (1 : Matrix (Fin row.dimension) (Fin row.dimension) ℂ) =
            algebraMap ℂ
              (Matrix (Fin row.dimension) (Fin row.dimension) ℂ)
              (alternatingSixComplexCyclotomicRoot ^
                row.scalarPattern.exponent 0) by
            rw [Algebra.algebraMap_eq_smul_one],
        ← map_pow, Algebra.algebraMap_eq_smul_one],
    Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
  rfl

end AlternatingSixAmbientOrdinaryCharacterRowCertificate
end InductiveMcKay
end McKayConjecture
