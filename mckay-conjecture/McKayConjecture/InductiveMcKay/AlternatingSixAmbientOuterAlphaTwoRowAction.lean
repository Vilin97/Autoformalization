/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterCentralAction
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterCompletedCharacterValues
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterMateSeparationValues
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterRowActionReduction

/-!
# Second ambient outer automorphism on ordinary rows

The state-77/state-79 separator pair resolves degrees four and five.  Exact
central shifts of `AB`, together with the remaining short-word values,
resolve every other repeated signature.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev completedTable :=
  alternatingSixAmbientOrdinaryCharacterTableCertificate

private abbrev classRepresentative (i : Fin 31) :
    AlternatingSixUniversalCover :=
  alternatingSixUniversalCoverClassRepresentative i

private abbrev alphaTwoAction (row : AlternatingSixAmbientOrdinaryRow) :
    AlternatingSixAmbientOrdinaryRow :=
  alternatingSixAmbientOrdinaryRowAutomorphismAction
    completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism row

private theorem alphaTwoClassIndexAction_symm_fifteen :
    alternatingSixSchurAlphaTwoClassIndexAction.symm 15 = 19 := by
  apply alternatingSixSchurAlphaTwoClassIndexAction.injective
  rw [Equiv.apply_symm_apply]
  rfl

private theorem alphaTwoClassIndexAction_symm_twentyEight :
    alternatingSixSchurAlphaTwoClassIndexAction.symm 28 = 30 := by
  apply alternatingSixSchurAlphaTwoClassIndexAction.injective
  rw [Equiv.apply_symm_apply]
  rfl

private theorem alphaTwoClassIndexAction_symm_nine :
    alternatingSixSchurAlphaTwoClassIndexAction.symm 9 = 9 := by
  apply alternatingSixSchurAlphaTwoClassIndexAction.injective
  rw [Equiv.apply_symm_apply]
  rfl

private theorem alphaTwoAction_row02 :
    alphaTwoAction .row02 = .row04 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
      .row02 .row04
      alternatingSixUniversalCoverAlphaTwoAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
        .row02 .row04 (classRepresentative 15)
    rw [
      alternatingSixUniversalCoverAlphaTwoAutomorphism_smul_values_representative
    ]
    rw [alphaTwoClassIndexAction_symm_fifteen]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row02).values
          (classRepresentative 19) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row05).values
          (classRepresentative 15)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientRow02MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 19) ≠
        (FDRep.of
          (alternatingSixAmbientRow05MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 15)
    exact alternatingSixAmbientAlphaTwoRow02_mateTestValue_ne

private theorem alphaTwoAction_row04 :
    alphaTwoAction .row04 = .row02 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
      .row04 .row02
      alternatingSixUniversalCoverAlphaTwoAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
        .row04 .row02 (classRepresentative 15)
    rw [
      alternatingSixUniversalCoverAlphaTwoAutomorphism_smul_values_representative
    ]
    rw [alphaTwoClassIndexAction_symm_fifteen]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row04).values
          (classRepresentative 19) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row03).values
          (classRepresentative 15)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientRow04MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 19) ≠
        (FDRep.of
          (alternatingSixAmbientRow03MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 15)
    exact alternatingSixAmbientAlphaTwoRow04_mateTestValue_ne

private theorem alphaTwoAction_row06 :
    alphaTwoAction .row06 = .row07 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
      .row06 .row07
      alternatingSixUniversalCoverAlphaTwoAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
        .row06 .row07 (classRepresentative 28)
    rw [
      alternatingSixUniversalCoverAlphaTwoAutomorphism_smul_values_representative
    ]
    rw [alphaTwoClassIndexAction_symm_twentyEight]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row06).values
          (classRepresentative 30) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row06).values
          (classRepresentative 28)
    rw [
      alternatingSixIrreducibleCharacter_values_representative_thirty,
      alternatingSixIrreducibleCharacter_values_representative_twentyEight,
      alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values
    ]
    change
      alternatingSixAmbientRow06CharacterRowCertificate.representation.character
          alternatingSixAmbientCanonicalSecondSeparator ≠
        alternatingSixAmbientRow06CharacterRowCertificate.representation.character
          alternatingSixAmbientCanonicalSeparator
    exact alternatingSixAmbientAlphaTwoRow06_mateTestValue_ne

private theorem alphaTwoAction_row08 :
    alphaTwoAction .row08 = .row09 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
      .row08 .row09
      alternatingSixUniversalCoverAlphaTwoAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
        .row08 .row09 (classRepresentative 28)
    rw [
      alternatingSixUniversalCoverAlphaTwoAutomorphism_smul_values_representative
    ]
    rw [alphaTwoClassIndexAction_symm_twentyEight]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row08).values
          (classRepresentative 30) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row08).values
          (classRepresentative 28)
    rw [
      alternatingSixIrreducibleCharacter_values_representative_thirty,
      alternatingSixIrreducibleCharacter_values_representative_twentyEight,
      alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values
    ]
    change
      alternatingSixAmbientRow08CharacterRowCertificate.representation.character
          alternatingSixAmbientCanonicalSecondSeparator ≠
        alternatingSixAmbientRow08CharacterRowCertificate.representation.character
          alternatingSixAmbientCanonicalSeparator
    exact alternatingSixAmbientAlphaTwoRow08_mateTestValue_ne

private theorem alphaTwoAction_row12 :
    alphaTwoAction .row12 = .row14 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
      .row12 .row14
      alternatingSixUniversalCoverAlphaTwoAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
        .row12 .row14 (classRepresentative 9)
    rw [
      alternatingSixUniversalCoverAlphaTwoAutomorphism_smul_values_representative
    ]
    rw [alphaTwoClassIndexAction_symm_nine]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row12).values
          (classRepresentative 9) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row15).values
          (classRepresentative 9)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientRow12MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 9) ≠
        (FDRep.of
          (alternatingSixAmbientRow15MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 9)
    simpa only [
      ← alternatingSixAmbientCanonicalGeneratorB_eq_classRepresentative,
      alternatingSixAmbientRow12CharacterRowCertificate_representation,
      alternatingSixAmbientRow15CharacterRowCertificate_representation
    ] using alternatingSixAmbientAlphaTwoRow12_mateTestValue_ne

private theorem alphaTwoAction_row14 :
    alphaTwoAction .row14 = .row12 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
      .row14 .row12
      alternatingSixUniversalCoverAlphaTwoAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
        .row14 .row12 (classRepresentative 9)
    rw [
      alternatingSixUniversalCoverAlphaTwoAutomorphism_smul_values_representative
    ]
    rw [alphaTwoClassIndexAction_symm_nine]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row14).values
          (classRepresentative 9) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row13).values
          (classRepresentative 9)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientRow14MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 9) ≠
        (FDRep.of
          (alternatingSixAmbientRow13MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 9)
    simpa only [
      ← alternatingSixAmbientCanonicalGeneratorB_eq_classRepresentative,
      alternatingSixAmbientRow14CharacterRowCertificate_representation,
      alternatingSixAmbientRow13CharacterRowCertificate_representation
    ] using alternatingSixAmbientAlphaTwoRow14_mateTestValue_ne

private theorem alphaTwoAction_row16 :
    alphaTwoAction .row16 = .row16 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
      .row16 .row16
      alternatingSixUniversalCoverAlphaTwoAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
        .row16 .row16 (classRepresentative 15)
    rw [
      alternatingSixUniversalCoverAlphaTwoAutomorphism_smul_values_representative
    ]
    rw [alphaTwoClassIndexAction_symm_fifteen]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row16).values
          (classRepresentative 19) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row17).values
          (classRepresentative 15)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientRow16MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 19) ≠
        (FDRep.of
          (alternatingSixAmbientRow17MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 15)
    exact alternatingSixAmbientAlphaTwoRow16_classMateTestValue_ne

private theorem alphaTwoAction_row18 :
    alphaTwoAction .row18 = .row18 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
      .row18 .row18
      alternatingSixUniversalCoverAlphaTwoAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
        .row18 .row18 (classRepresentative 15)
    rw [
      alternatingSixUniversalCoverAlphaTwoAutomorphism_smul_values_representative
    ]
    rw [alphaTwoClassIndexAction_symm_fifteen]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row18).values
          (classRepresentative 19) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row19).values
          (classRepresentative 15)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientRow18MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 19) ≠
        (FDRep.of
          (alternatingSixAmbientRow19MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 15)
    exact alternatingSixAmbientAlphaTwoRow18_classMateTestValue_ne

private theorem alphaTwoAction_row24 :
    alphaTwoAction .row24 = .row24 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
      .row24 .row24
      alternatingSixUniversalCoverAlphaTwoAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
        .row24 .row24 (classRepresentative 9)
    rw [
      alternatingSixUniversalCoverAlphaTwoAutomorphism_smul_values_representative
    ]
    rw [alphaTwoClassIndexAction_symm_nine]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row24).values
          (classRepresentative 9) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row25).values
          (classRepresentative 9)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientRow24MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 9) ≠
        (FDRep.of
          (alternatingSixAmbientRow25MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 9)
    exact alternatingSixAmbientAlphaTwoRow24_mateTestValue_ne

private theorem alphaTwoAction_atlasPowerOne :
    alphaTwoAction .atlasTwelvePowerOne =
      .atlasTwelvePowerEleven := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
      .atlasTwelvePowerOne .atlasTwelvePowerEleven
      alternatingSixUniversalCoverAlphaTwoAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
        .atlasTwelvePowerOne .atlasTwelvePowerEleven
        (classRepresentative 15)
    rw [
      alternatingSixUniversalCoverAlphaTwoAutomorphism_smul_values_representative
    ]
    rw [alphaTwoClassIndexAction_symm_fifteen]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character
          .atlasTwelvePowerOne).values (classRepresentative 19) ≠
        (completedTable.toFiniteCharacterTableCertificate.character
          .atlasTwelvePowerTwo).values (classRepresentative 15)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientAtlas12P1ClassMatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 19) ≠
        (FDRep.of
          (alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 15)
    exact alternatingSixAmbientAlphaTwoAtlasPowerOne_mateTestValue_ne

private theorem alphaTwoAction_atlasPowerTwo :
    alphaTwoAction .atlasTwelvePowerTwo =
      .atlasTwelvePowerSeven := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
      .atlasTwelvePowerTwo .atlasTwelvePowerSeven
      alternatingSixUniversalCoverAlphaTwoAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
        .atlasTwelvePowerTwo .atlasTwelvePowerSeven
        (classRepresentative 15)
    rw [
      alternatingSixUniversalCoverAlphaTwoAutomorphism_smul_values_representative
    ]
    rw [alphaTwoClassIndexAction_symm_fifteen]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character
          .atlasTwelvePowerTwo).values (classRepresentative 19) ≠
        (completedTable.toFiniteCharacterTableCertificate.character
          .atlasTwelvePowerOne).values (classRepresentative 15)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 19) ≠
        (FDRep.of
          (alternatingSixAmbientAtlas12P1ClassMatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 15)
    exact alternatingSixAmbientAlphaTwoAtlasPowerTwo_mateTestValue_ne

/-- The second canonical outer automorphism induces the advertised
permutation of all thirty-one completed ordinary rows. -/
theorem alternatingSixAmbientAlphaTwoOrdinaryRowAction_eq :
    ∀ row,
      alternatingSixAmbientOrdinaryRowAutomorphismAction
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          alternatingSixUniversalCoverAlphaTwoAutomorphism row =
        alternatingSixAmbientAlphaTwoOrdinaryRowAction row := by
  apply
    alternatingSixAmbientAlphaTwoOrdinaryRowAction_eq_of_mate_separation
      completedTable
      alternatingSixUniversalCoverAlphaTwoAutomorphism_symm_centralGenerator
  intro row hmate
  have hinjective :=
    alternatingSixAmbientOrdinaryRowAutomorphismAction_injective
      completedTable alternatingSixUniversalCoverAlphaTwoAutomorphism
  cases row with
  | row02 =>
      change alphaTwoAction .row02 ≠ .row05
      rw [alphaTwoAction_row02]
      decide
  | row03 =>
      change alphaTwoAction .row03 ≠ .row04
      intro h
      have hsources : (.row03 : AlternatingSixAmbientOrdinaryRow) = .row02 :=
        hinjective (h.trans alphaTwoAction_row02.symm)
      contradiction
  | row04 =>
      change alphaTwoAction .row04 ≠ .row03
      rw [alphaTwoAction_row04]
      decide
  | row05 =>
      change alphaTwoAction .row05 ≠ .row02
      intro h
      have hsources : (.row05 : AlternatingSixAmbientOrdinaryRow) = .row04 :=
        hinjective (h.trans alphaTwoAction_row04.symm)
      contradiction
  | row06 =>
      change alphaTwoAction .row06 ≠ .row06
      rw [alphaTwoAction_row06]
      decide
  | row07 =>
      change alphaTwoAction .row07 ≠ .row07
      intro h
      have hsources : (.row07 : AlternatingSixAmbientOrdinaryRow) = .row06 :=
        hinjective (h.trans alphaTwoAction_row06.symm)
      contradiction
  | row08 =>
      change alphaTwoAction .row08 ≠ .row08
      rw [alphaTwoAction_row08]
      decide
  | row09 =>
      change alphaTwoAction .row09 ≠ .row09
      intro h
      have hsources : (.row09 : AlternatingSixAmbientOrdinaryRow) = .row08 :=
        hinjective (h.trans alphaTwoAction_row08.symm)
      contradiction
  | row12 =>
      change alphaTwoAction .row12 ≠ .row15
      rw [alphaTwoAction_row12]
      decide
  | row13 =>
      change alphaTwoAction .row13 ≠ .row14
      intro h
      have hsources : (.row13 : AlternatingSixAmbientOrdinaryRow) = .row12 :=
        hinjective (h.trans alphaTwoAction_row12.symm)
      contradiction
  | row14 =>
      change alphaTwoAction .row14 ≠ .row13
      rw [alphaTwoAction_row14]
      decide
  | row15 =>
      change alphaTwoAction .row15 ≠ .row12
      intro h
      have hsources : (.row15 : AlternatingSixAmbientOrdinaryRow) = .row14 :=
        hinjective (h.trans alphaTwoAction_row14.symm)
      contradiction
  | row16 =>
      change alphaTwoAction .row16 ≠ .row17
      rw [alphaTwoAction_row16]
      decide
  | row17 =>
      change alphaTwoAction .row17 ≠ .row16
      intro h
      have hsources : (.row17 : AlternatingSixAmbientOrdinaryRow) = .row16 :=
        hinjective (h.trans alphaTwoAction_row16.symm)
      contradiction
  | row18 =>
      change alphaTwoAction .row18 ≠ .row19
      rw [alphaTwoAction_row18]
      decide
  | row19 =>
      change alphaTwoAction .row19 ≠ .row18
      intro h
      have hsources : (.row19 : AlternatingSixAmbientOrdinaryRow) = .row18 :=
        hinjective (h.trans alphaTwoAction_row18.symm)
      contradiction
  | row24 =>
      change alphaTwoAction .row24 ≠ .row25
      rw [alphaTwoAction_row24]
      decide
  | row25 =>
      change alphaTwoAction .row25 ≠ .row24
      intro h
      have hsources : (.row25 : AlternatingSixAmbientOrdinaryRow) = .row24 :=
        hinjective (h.trans alphaTwoAction_row24.symm)
      contradiction
  | atlasTwelvePowerOne =>
      change
        alphaTwoAction .atlasTwelvePowerOne ≠
          .atlasTwelvePowerTwo
      rw [alphaTwoAction_atlasPowerOne]
      decide
  | atlasTwelvePowerSeven =>
      change
        alphaTwoAction .atlasTwelvePowerSeven ≠
          .atlasTwelvePowerEleven
      intro h
      have hsources :
          (.atlasTwelvePowerSeven :
              AlternatingSixAmbientOrdinaryRow) =
            .atlasTwelvePowerOne :=
        hinjective (h.trans alphaTwoAction_atlasPowerOne.symm)
      contradiction
  | atlasTwelvePowerTwo =>
      change
        alphaTwoAction .atlasTwelvePowerTwo ≠
          .atlasTwelvePowerOne
      rw [alphaTwoAction_atlasPowerTwo]
      decide
  | atlasTwelvePowerEleven =>
      change
        alphaTwoAction .atlasTwelvePowerEleven ≠
          .atlasTwelvePowerSeven
      intro h
      have hsources :
          (.atlasTwelvePowerEleven :
              AlternatingSixAmbientOrdinaryRow) =
            .atlasTwelvePowerTwo :=
        hinjective (h.trans alphaTwoAction_atlasPowerTwo.symm)
      contradiction
  | row01 | row10 | row11 | row20 | row21 | row22 | row23
  | row30 | row31 =>
      simp [
        alternatingSixAmbientAlphaTwoOrdinaryRowAction,
        alternatingSixAmbientOrdinaryRowSignatureMate
      ] at hmate

end InductiveMcKay
end McKayConjecture
