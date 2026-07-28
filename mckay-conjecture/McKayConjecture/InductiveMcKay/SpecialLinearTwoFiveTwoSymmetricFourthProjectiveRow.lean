/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveGeneralLinearInvariantRows
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveTwoSymmetricSquareProjectiveRows

/-!
# The symmetric-fourth-power projective row at `p = 2`

The degree-five ambient character is fixed by the outer automorphism and
is matched with the degree-three character of the binary-tetrahedral
normalizer.  Both have trivial central-involution scalar.  The common
general-linear cover therefore supplies the projective comparison.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeTwoForSymmetricFourthProjectiveRow :
    Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The degree-five row in the ambient odd-degree table. -/
def specialLinearTwoFiveTwoSymmetricFourthPPrimeRow :
    SpecialLinearTwoFivePPrimeCharacterRow 2 :=
  ⟨.symmetricFourthPower, by
    norm_num [specialLinearTwoFiveCharacterRowDegree]⟩

@[simp]
theorem specialLinearTwoFiveTwoMcKayRowEquiv_symmetricFourth :
    specialLinearTwoFiveTwoMcKayRowEquiv
        specialLinearTwoFiveTwoSymmetricFourthPPrimeRow =
      ⟨.threeDimensional, by
        norm_num [
          specialLinearTwoFiveTwoNormalizerCharacterRowDegree]⟩ :=
  rfl

/-- The matched local row is the explicit degree-three normalizer
character. -/
theorem specialLinearTwoFiveTwoSymmetricFourthLocalCharacter_eq :
    (specialLinearTwoFiveTwoEquivariantMcKayEquiv
      (specialLinearTwoFiveTwoPPrimeCharacterEquiv
        specialLinearTwoFiveTwoSymmetricFourthPPrimeRow)).1 =
      specialLinearTwoFiveTwoNormalizerThreeDimensionalCharacter := by
  change
    (specialLinearTwoFiveTwoCharacterTableCompletion
      |>.toEquivariantMcKayEquiv
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv
          specialLinearTwoFiveTwoSymmetricFourthPPrimeRow)).1 =
      specialLinearTwoFiveTwoNormalizerThreeDimensionalCharacter
  rw [
    SpecialLinearTwoFiveTwoCharacterTableCompletion.toEquivariantMcKayEquiv_apply_enumerated,
    specialLinearTwoFiveTwoMcKayRowEquiv_symmetricFourth]
  rfl

@[simp]
theorem specialLinearTwoFiveTwoSymmetricFourth_outer :
    specialLinearTwoFiveOuterCharacterRow
        .symmetricFourthPower =
      .symmetricFourthPower :=
  rfl

/-- The ambient degree-five character is invariant under the full
general-linear conjugation action. -/
theorem
    specialLinearTwoFiveTwoSymmetricFourth_generalLinear_invariant
    (u : GeneralLinearTwoFive)
    (g : SpecialLinearTwoFive) :
    (specialLinearTwoFiveTwoPPrimeCharacterEquiv
      specialLinearTwoFiveTwoSymmetricFourthPPrimeRow).1.values
        (generalLinearTwoFiveConjugation u g) =
      (specialLinearTwoFiveTwoPPrimeCharacterEquiv
        specialLinearTwoFiveTwoSymmetricFourthPPrimeRow).1.values g := by
  change
    (specialLinearTwoFiveIrreducibleCharacter
      .symmetricFourthPower).values
        (generalLinearTwoFiveConjugation u g) =
      (specialLinearTwoFiveIrreducibleCharacter
        .symmetricFourthPower).values g
  exact
    specialLinearTwoFive_irreducibleCharacter_generalLinear_invariant_of_outer_fixed
      .symmetricFourthPower
      specialLinearTwoFiveTwoSymmetricFourth_outer u g

/-- The central involution acts trivially on the degree-five ambient
row. -/
theorem specialLinearTwoFiveTwoSymmetricFourthAmbient_values_neg_one :
    (specialLinearTwoFiveTwoPPrimeCharacterEquiv
      specialLinearTwoFiveTwoSymmetricFourthPPrimeRow).1.values (-1) =
      ((specialLinearTwoFiveTwoPPrimeCharacterEquiv
        specialLinearTwoFiveTwoSymmetricFourthPPrimeRow).1.degree :
        ℂ) := by
  change
    (specialLinearTwoFiveIrreducibleCharacter
      .symmetricFourthPower).values
        (specialLinearTwoFiveConjugacyRepresentative 1) =
      ((specialLinearTwoFiveIrreducibleCharacter
        .symmetricFourthPower).degree : ℂ)
  rw [specialLinearTwoFiveIrreducibleCharacter_values_representative,
    specialLinearTwoFiveIrreducibleCharacter_degree]
  norm_num [specialLinearTwoFiveCharacterTableValue,
    binaryIcosahedralDefiningTrace,
    binaryIcosahedralSymmetricFourthPowerValue,
    specialLinearTwoFiveCharacterRowDegree]

/-- The central involution also acts trivially on the matched local
degree-three row. -/
theorem specialLinearTwoFiveTwoSymmetricFourthLocal_values_neg_one :
    (specialLinearTwoFiveTwoEquivariantMcKayEquiv
      (specialLinearTwoFiveTwoPPrimeCharacterEquiv
        specialLinearTwoFiveTwoSymmetricFourthPPrimeRow)).1.values
          (specialLinearTwoFiveCentralNegOneNormalizer
            specialLinearTwoFiveSylowTwo) =
      ((specialLinearTwoFiveTwoEquivariantMcKayEquiv
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv
          specialLinearTwoFiveTwoSymmetricFourthPPrimeRow)).1.degree :
        ℂ) := by
  rw [specialLinearTwoFiveTwoSymmetricFourthLocalCharacter_eq]
  rw [
    specialLinearTwoFiveTwoNormalizerThreeDimensionalCharacter_degree]
  change
    (specialLinearTwoFiveCharacterFDRep
      (.symmetricSquare 0)).character
        (specialLinearTwoFiveConjugacyRepresentative 1) =
      (3 : ℂ)
  rw [
    specialLinearTwoFiveCharacterFDRep_character_representative]
  norm_num [specialLinearTwoFiveCharacterTableValue,
    binaryIcosahedralDefiningTrace,
    binaryIcosahedralSymmetricSquareValue]

/-- Cross-multiplied central-scalar equality for the common cover. -/
theorem specialLinearTwoFiveTwoSymmetricFourth_centralCross :
    (specialLinearTwoFiveTwoPPrimeCharacterEquiv
      specialLinearTwoFiveTwoSymmetricFourthPPrimeRow).1.values (-1) *
        ((specialLinearTwoFiveTwoEquivariantMcKayEquiv
          (specialLinearTwoFiveTwoPPrimeCharacterEquiv
            specialLinearTwoFiveTwoSymmetricFourthPPrimeRow)).1.degree :
          ℂ) =
      (specialLinearTwoFiveTwoEquivariantMcKayEquiv
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv
          specialLinearTwoFiveTwoSymmetricFourthPPrimeRow)).1.values
            (specialLinearTwoFiveCentralNegOneNormalizer
              specialLinearTwoFiveSylowTwo) *
        ((specialLinearTwoFiveTwoPPrimeCharacterEquiv
          specialLinearTwoFiveTwoSymmetricFourthPPrimeRow).1.degree :
          ℂ) := by
  rw [specialLinearTwoFiveTwoSymmetricFourthAmbient_values_neg_one,
    specialLinearTwoFiveTwoSymmetricFourthLocal_values_neg_one]
  ring

/-- Projective compatibility for the degree-five row. -/
theorem specialLinearTwoFiveTwoSymmetricFourthRow_tripleCompatible :
    specialLinearTwoFiveTwoEquivariantMcKayEquiv
      |>.toExactNormalizerLocalCorrespondence.TripleCompatible
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv
          specialLinearTwoFiveTwoSymmetricFourthPPrimeRow) := by
  apply
    specialLinearTwoFiveTwoEquivariantMcKayEquiv
      |>.tripleCompatible_of_generalLinearCover
        specialLinearTwoFiveSylowTwo
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv
          specialLinearTwoFiveTwoSymmetricFourthPPrimeRow)
  · exact
      specialLinearTwoFiveTwoSymmetricFourth_generalLinear_invariant
  · exact specialLinearTwoFiveTwoSymmetricFourth_centralCross

/-- Concrete projective row data for the degree-five row. -/
def specialLinearTwoFiveTwoSymmetricFourthProjectiveRowData :
    ExactNormalizerProjectiveRowData
      specialLinearTwoFiveTwoEquivariantMcKayEquiv
      (specialLinearTwoFiveTwoPPrimeCharacterEquiv
        specialLinearTwoFiveTwoSymmetricFourthPPrimeRow) :=
  ExactNormalizerProjectiveRowData.ofTripleCompatible
    specialLinearTwoFiveTwoEquivariantMcKayEquiv
    (specialLinearTwoFiveTwoPPrimeCharacterEquiv
      specialLinearTwoFiveTwoSymmetricFourthPPrimeRow)
    specialLinearTwoFiveTwoSymmetricFourthRow_tripleCompatible

end InductiveMcKay
end McKayConjecture
