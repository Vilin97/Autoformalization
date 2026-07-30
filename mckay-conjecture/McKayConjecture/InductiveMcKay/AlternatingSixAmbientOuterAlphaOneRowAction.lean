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
# First ambient outer automorphism on ordinary rows

Exact character values determine one source in every repeated
degree/central-scalar signature.  Injectivity of automorphism transport then
forces the mate source, yielding the complete named row permutation.
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

private abbrev alphaOneAction (row : AlternatingSixAmbientOrdinaryRow) :
    AlternatingSixAmbientOrdinaryRow :=
  alternatingSixAmbientOrdinaryRowAutomorphismAction
    completedTable alternatingSixUniversalCoverAlphaOneAutomorphism row

private theorem alphaOneClassIndexAction_symm_fifteen :
    alternatingSixSchurAlphaOneClassIndexAction.symm 15 = 21 := by
  apply alternatingSixSchurAlphaOneClassIndexAction.injective
  rw [Equiv.apply_symm_apply]
  rfl

private theorem alphaOneClassIndexAction_symm_twentyEight :
    alternatingSixSchurAlphaOneClassIndexAction.symm 28 = 28 := by
  apply alternatingSixSchurAlphaOneClassIndexAction.injective
  rw [Equiv.apply_symm_apply]
  rfl

private theorem alphaOneClassIndexAction_symm_nine :
    alternatingSixSchurAlphaOneClassIndexAction.symm 9 = 12 := by
  apply alternatingSixSchurAlphaOneClassIndexAction.injective
  rw [Equiv.apply_symm_apply]
  rfl

private theorem alphaOneAction_row02 :
    alphaOneAction .row02 = .row05 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
      .row02 .row05
      alternatingSixUniversalCoverAlphaOneAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
        .row02 .row05 (classRepresentative 15)
    rw [
      alternatingSixUniversalCoverAlphaOneAutomorphism_smul_values_representative
    ]
    rw [alphaOneClassIndexAction_symm_fifteen]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row02).values
          (classRepresentative 21) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row04).values
          (classRepresentative 15)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientRow02MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 21) ≠
        (FDRep.of
          (alternatingSixAmbientRow04MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 15)
    simpa only [
      ←
        alternatingSixAmbientCanonicalGeneratorABSquared_eq_classRepresentative,
      ← alternatingSixAmbientCanonicalGeneratorAB_eq_classRepresentative
    ] using alternatingSixAmbientAlphaOneRow02_mateTestValue_ne

private theorem alphaOneAction_row04 :
    alphaOneAction .row04 = .row03 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
      .row04 .row03
      alternatingSixUniversalCoverAlphaOneAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
        .row04 .row03 (classRepresentative 15)
    rw [
      alternatingSixUniversalCoverAlphaOneAutomorphism_smul_values_representative
    ]
    rw [alphaOneClassIndexAction_symm_fifteen]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row04).values
          (classRepresentative 21) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row02).values
          (classRepresentative 15)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientRow04MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 21) ≠
        (FDRep.of
          (alternatingSixAmbientRow02MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 15)
    simpa only [
      ←
        alternatingSixAmbientCanonicalGeneratorABSquared_eq_classRepresentative,
      ← alternatingSixAmbientCanonicalGeneratorAB_eq_classRepresentative
    ] using alternatingSixAmbientAlphaOneRow04_mateTestValue_ne

private theorem alphaOneAction_row06 :
    alphaOneAction .row06 = .row06 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
      .row06 .row06
      alternatingSixUniversalCoverAlphaOneAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
        .row06 .row06 (classRepresentative 28)
    rw [
      alternatingSixUniversalCoverAlphaOneAutomorphism_smul_values_representative
    ]
    rw [alphaOneClassIndexAction_symm_twentyEight]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row06).values
          (classRepresentative 28) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row07).values
          (classRepresentative 28)
    rw [
      alternatingSixIrreducibleCharacter_values_representative_twentyEight,
      alternatingSixIrreducibleCharacter_values_representative_twentyEight,
      alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values
    ]
    change
      alternatingSixAmbientRow06CharacterRowCertificate.representation.character
          alternatingSixAmbientCanonicalSeparator ≠
        alternatingSixAmbientRow07CharacterRowCertificate.representation.character
          alternatingSixAmbientCanonicalSeparator
    exact alternatingSixAmbientAlphaOneRow06_mateTestValue_ne

private theorem alphaOneAction_row08 :
    alphaOneAction .row08 = .row08 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
      .row08 .row08
      alternatingSixUniversalCoverAlphaOneAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
        .row08 .row08 (classRepresentative 28)
    rw [
      alternatingSixUniversalCoverAlphaOneAutomorphism_smul_values_representative
    ]
    rw [alphaOneClassIndexAction_symm_twentyEight]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row08).values
          (classRepresentative 28) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row09).values
          (classRepresentative 28)
    rw [
      alternatingSixIrreducibleCharacter_values_representative_twentyEight,
      alternatingSixIrreducibleCharacter_values_representative_twentyEight,
      alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values
    ]
    change
      alternatingSixAmbientRow08CharacterRowCertificate.representation.character
          alternatingSixAmbientCanonicalSeparator ≠
        alternatingSixAmbientRow09CharacterRowCertificate.representation.character
          alternatingSixAmbientCanonicalSeparator
    exact alternatingSixAmbientAlphaOneRow08_mateTestValue_ne

private theorem alphaOneAction_row12 :
    alphaOneAction .row12 = .row15 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
      .row12 .row15
      alternatingSixUniversalCoverAlphaOneAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
        .row12 .row15 (classRepresentative 9)
    rw [
      alternatingSixUniversalCoverAlphaOneAutomorphism_smul_values_representative
    ]
    rw [alphaOneClassIndexAction_symm_nine]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row12).values
          (classRepresentative 12) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row14).values
          (classRepresentative 9)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientRow12MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 12) ≠
        (FDRep.of
          (alternatingSixAmbientRow14MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 9)
    exact alternatingSixAmbientAlphaOneRow12_mateTestValue_ne

private theorem alphaOneAction_row14 :
    alphaOneAction .row14 = .row13 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
      .row14 .row13
      alternatingSixUniversalCoverAlphaOneAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
        .row14 .row13 (classRepresentative 9)
    rw [
      alternatingSixUniversalCoverAlphaOneAutomorphism_smul_values_representative
    ]
    rw [alphaOneClassIndexAction_symm_nine]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row14).values
          (classRepresentative 12) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row12).values
          (classRepresentative 9)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientRow14MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 12) ≠
        (FDRep.of
          (alternatingSixAmbientRow12MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 9)
    exact alternatingSixAmbientAlphaOneRow14_mateTestValue_ne

private theorem alphaOneAction_row16 :
    alphaOneAction .row16 = .row17 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
      .row16 .row17
      alternatingSixUniversalCoverAlphaOneAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
        .row16 .row17 (classRepresentative 15)
    rw [
      alternatingSixUniversalCoverAlphaOneAutomorphism_smul_values_representative
    ]
    rw [alphaOneClassIndexAction_symm_fifteen]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row16).values
          (classRepresentative 21) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row16).values
          (classRepresentative 15)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientRow16MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 21) ≠
        (FDRep.of
          (alternatingSixAmbientRow16MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 15)
    simpa only [
      ←
        alternatingSixAmbientCanonicalGeneratorABSquared_eq_classRepresentative,
      ← alternatingSixAmbientCanonicalGeneratorAB_eq_classRepresentative
    ] using alternatingSixAmbientAlphaOneRow16_mateTestValue_ne

private theorem alphaOneAction_row18 :
    alphaOneAction .row18 = .row19 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
      .row18 .row19
      alternatingSixUniversalCoverAlphaOneAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
        .row18 .row19 (classRepresentative 15)
    rw [
      alternatingSixUniversalCoverAlphaOneAutomorphism_smul_values_representative
    ]
    rw [alphaOneClassIndexAction_symm_fifteen]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row18).values
          (classRepresentative 21) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row18).values
          (classRepresentative 15)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientRow18MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 21) ≠
        (FDRep.of
          (alternatingSixAmbientRow18MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 15)
    simpa only [
      ←
        alternatingSixAmbientCanonicalGeneratorABSquared_eq_classRepresentative,
      ← alternatingSixAmbientCanonicalGeneratorAB_eq_classRepresentative
    ] using alternatingSixAmbientAlphaOneRow18_mateTestValue_ne

private theorem alphaOneAction_row24 :
    alphaOneAction .row24 = .row25 := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
      .row24 .row25
      alternatingSixUniversalCoverAlphaOneAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
        .row24 .row25 (classRepresentative 9)
    rw [
      alternatingSixUniversalCoverAlphaOneAutomorphism_smul_values_representative
    ]
    rw [alphaOneClassIndexAction_symm_nine]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character .row24).values
          (classRepresentative 12) ≠
        (completedTable.toFiniteCharacterTableCertificate.character .row24).values
          (classRepresentative 9)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientRow24MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 12) ≠
        (FDRep.of
          (alternatingSixAmbientRow24MatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 9)
    exact alternatingSixAmbientAlphaOneRow24_mateTestValue_ne

private theorem alphaOneAction_atlasPowerOne :
    alphaOneAction .atlasTwelvePowerOne =
      .atlasTwelvePowerTwo := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
      .atlasTwelvePowerOne .atlasTwelvePowerTwo
      alternatingSixUniversalCoverAlphaOneAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
        .atlasTwelvePowerOne .atlasTwelvePowerTwo
        (classRepresentative 15)
    rw [
      alternatingSixUniversalCoverAlphaOneAutomorphism_smul_values_representative
    ]
    rw [alphaOneClassIndexAction_symm_fifteen]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character
          .atlasTwelvePowerOne).values (classRepresentative 21) ≠
        (completedTable.toFiniteCharacterTableCertificate.character
          .atlasTwelvePowerEleven).values (classRepresentative 15)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientAtlas12P1ClassMatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 21) ≠
        (FDRep.of
          (alternatingSixAmbientAtlas12P11ClassMatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 15)
    exact alternatingSixAmbientAlphaOneAtlasPowerOne_mateTestValue_ne

private theorem alphaOneAction_atlasPowerTwo :
    alphaOneAction .atlasTwelvePowerTwo =
      .atlasTwelvePowerOne := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
      completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
      .atlasTwelvePowerTwo .atlasTwelvePowerOne
      alternatingSixUniversalCoverAlphaOneAutomorphism_symm_centralGenerator
  · rfl
  · rfl
  · apply
      alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
        completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
        .atlasTwelvePowerTwo .atlasTwelvePowerOne
        (classRepresentative 15)
    rw [
      alternatingSixUniversalCoverAlphaOneAutomorphism_smul_values_representative
    ]
    rw [alphaOneClassIndexAction_symm_fifteen]
    simp only [alternatingSixAmbientOrdinaryRowSignatureMate]
    change
      (completedTable.toFiniteCharacterTableCertificate.character
          .atlasTwelvePowerTwo).values (classRepresentative 21) ≠
        (completedTable.toFiniteCharacterTableCertificate.character
          .atlasTwelvePowerSeven).values (classRepresentative 15)
    rw [alternatingSixAmbientCompletedCharacter_values,
      alternatingSixAmbientCompletedCharacter_values]
    change
      (FDRep.of
          (alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 21) ≠
        (FDRep.of
          (alternatingSixAmbientAtlasTwelvePowerSevenClassMatrixCertificate
            |>.universalCoverRepresentation)).character
            (classRepresentative 15)
    exact alternatingSixAmbientAlphaOneAtlasPowerTwo_mateTestValue_ne

/-- The first canonical outer automorphism induces the advertised
permutation of all thirty-one completed ordinary rows. -/
theorem alternatingSixAmbientAlphaOneOrdinaryRowAction_eq :
    ∀ row,
      alternatingSixAmbientOrdinaryRowAutomorphismAction
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          alternatingSixUniversalCoverAlphaOneAutomorphism row =
        alternatingSixAmbientAlphaOneOrdinaryRowAction row := by
  apply
    alternatingSixAmbientAlphaOneOrdinaryRowAction_eq_of_mate_separation
      completedTable
      alternatingSixUniversalCoverAlphaOneAutomorphism_symm_centralGenerator
  intro row hmate
  have hinjective :=
    alternatingSixAmbientOrdinaryRowAutomorphismAction_injective
      completedTable alternatingSixUniversalCoverAlphaOneAutomorphism
  cases row with
  | row02 =>
      change alphaOneAction .row02 ≠ .row04
      rw [alphaOneAction_row02]
      decide
  | row03 =>
      change alphaOneAction .row03 ≠ .row05
      intro h
      have hsources : (.row03 : AlternatingSixAmbientOrdinaryRow) = .row02 :=
        hinjective (h.trans alphaOneAction_row02.symm)
      contradiction
  | row04 =>
      change alphaOneAction .row04 ≠ .row02
      rw [alphaOneAction_row04]
      decide
  | row05 =>
      change alphaOneAction .row05 ≠ .row03
      intro h
      have hsources : (.row05 : AlternatingSixAmbientOrdinaryRow) = .row04 :=
        hinjective (h.trans alphaOneAction_row04.symm)
      contradiction
  | row06 =>
      change alphaOneAction .row06 ≠ .row07
      rw [alphaOneAction_row06]
      decide
  | row07 =>
      change alphaOneAction .row07 ≠ .row06
      intro h
      have hsources : (.row07 : AlternatingSixAmbientOrdinaryRow) = .row06 :=
        hinjective (h.trans alphaOneAction_row06.symm)
      contradiction
  | row08 =>
      change alphaOneAction .row08 ≠ .row09
      rw [alphaOneAction_row08]
      decide
  | row09 =>
      change alphaOneAction .row09 ≠ .row08
      intro h
      have hsources : (.row09 : AlternatingSixAmbientOrdinaryRow) = .row08 :=
        hinjective (h.trans alphaOneAction_row08.symm)
      contradiction
  | row12 =>
      change alphaOneAction .row12 ≠ .row14
      rw [alphaOneAction_row12]
      decide
  | row13 =>
      change alphaOneAction .row13 ≠ .row15
      intro h
      have hsources : (.row13 : AlternatingSixAmbientOrdinaryRow) = .row12 :=
        hinjective (h.trans alphaOneAction_row12.symm)
      contradiction
  | row14 =>
      change alphaOneAction .row14 ≠ .row12
      rw [alphaOneAction_row14]
      decide
  | row15 =>
      change alphaOneAction .row15 ≠ .row13
      intro h
      have hsources : (.row15 : AlternatingSixAmbientOrdinaryRow) = .row14 :=
        hinjective (h.trans alphaOneAction_row14.symm)
      contradiction
  | row16 =>
      change alphaOneAction .row16 ≠ .row16
      rw [alphaOneAction_row16]
      decide
  | row17 =>
      change alphaOneAction .row17 ≠ .row17
      intro h
      have hsources : (.row17 : AlternatingSixAmbientOrdinaryRow) = .row16 :=
        hinjective (h.trans alphaOneAction_row16.symm)
      contradiction
  | row18 =>
      change alphaOneAction .row18 ≠ .row18
      rw [alphaOneAction_row18]
      decide
  | row19 =>
      change alphaOneAction .row19 ≠ .row19
      intro h
      have hsources : (.row19 : AlternatingSixAmbientOrdinaryRow) = .row18 :=
        hinjective (h.trans alphaOneAction_row18.symm)
      contradiction
  | row24 =>
      change alphaOneAction .row24 ≠ .row24
      rw [alphaOneAction_row24]
      decide
  | row25 =>
      change alphaOneAction .row25 ≠ .row25
      intro h
      have hsources : (.row25 : AlternatingSixAmbientOrdinaryRow) = .row24 :=
        hinjective (h.trans alphaOneAction_row24.symm)
      contradiction
  | atlasTwelvePowerOne =>
      change
        alphaOneAction .atlasTwelvePowerOne ≠
          .atlasTwelvePowerEleven
      rw [alphaOneAction_atlasPowerOne]
      decide
  | atlasTwelvePowerSeven =>
      change
        alphaOneAction .atlasTwelvePowerSeven ≠
          .atlasTwelvePowerTwo
      intro h
      have hsources :
          (.atlasTwelvePowerSeven :
              AlternatingSixAmbientOrdinaryRow) =
            .atlasTwelvePowerOne :=
        hinjective (h.trans alphaOneAction_atlasPowerOne.symm)
      contradiction
  | atlasTwelvePowerTwo =>
      change
        alphaOneAction .atlasTwelvePowerTwo ≠
          .atlasTwelvePowerSeven
      rw [alphaOneAction_atlasPowerTwo]
      decide
  | atlasTwelvePowerEleven =>
      change
        alphaOneAction .atlasTwelvePowerEleven ≠
          .atlasTwelvePowerOne
      intro h
      have hsources :
          (.atlasTwelvePowerEleven :
              AlternatingSixAmbientOrdinaryRow) =
            .atlasTwelvePowerTwo :=
        hinjective (h.trans alphaOneAction_atlasPowerTwo.symm)
      contradiction
  | row01 | row10 | row11 | row20 | row21 | row22 | row23
  | row30 | row31 =>
      simp [
        alternatingSixAmbientAlphaOneOrdinaryRowAction,
        alternatingSixAmbientOrdinaryRowSignatureMate
      ] at hmate

end InductiveMcKay
end McKayConjecture
