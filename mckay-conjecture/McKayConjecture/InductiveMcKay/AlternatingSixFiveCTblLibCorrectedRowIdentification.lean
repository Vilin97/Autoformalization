/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCTblLibCorrectedAtlasBlock
import McKayConjecture.InductiveMcKay.AlternatingSixThreeCTblLibAmbientValueBridges

/-!
# The corrected five-local CTblLib ambient row identification

The invariant-safe five-local orientation has the right degree and central
scalar at every position, but its degree-twelve block has the wrong internal
order.  The exact class-value calculation in
`AlternatingSixFiveCTblLibCorrectedAtlasBlock` determines the corrected final
block as

`[power 2, power 7, power 11, power 1]`.

Thus the corrected orientation differs from the invariant-safe orientation
only by interchanging positions `21` and `23`.  This file records the
resulting position equivalence and induced row identification.  It then
settles the two ambient generator bridges on every coordinate for which the
current completed-value API determines the genuine action, and reduces each
full bridge to an explicit residual set of positions.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveCorrectedRowIdentificationFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local notation "η₉" => alternatingSixAmbientRow21Eta

/-! ### Corrected finite position data -/

/-- The invariant-safe ambient orientation with its final degree-twelve
block put in the class-value-certified order. -/
def alternatingSixFiveCTblLibCorrectedAmbientPosition :
    Fin 24 → AlternatingSixAmbientPPrimeRowIndex 5 :=
  ![⟨.row01, by decide⟩,
    ⟨.row16, by decide⟩,
    ⟨.row17, by decide⟩,
    ⟨.row20, by decide⟩,
    ⟨.row06, by decide⟩,
    ⟨.row07, by decide⟩,
    ⟨.row18, by decide⟩,
    ⟨.row19, by decide⟩,
    ⟨.row04, by decide⟩,
    ⟨.row02, by decide⟩,
    ⟨.row05, by decide⟩,
    ⟨.row03, by decide⟩,
    ⟨.row11, by decide⟩,
    ⟨.row10, by decide⟩,
    ⟨.row22, by decide⟩,
    ⟨.row21, by decide⟩,
    ⟨.row14, by decide⟩,
    ⟨.row12, by decide⟩,
    ⟨.row15, by decide⟩,
    ⟨.row13, by decide⟩,
    ⟨.atlasTwelvePowerTwo, by decide⟩,
    ⟨.atlasTwelvePowerSeven, by decide⟩,
    ⟨.atlasTwelvePowerEleven, by decide⟩,
    ⟨.atlasTwelvePowerOne, by decide⟩]

/-- The corrected ambient orientation visits every five-prime row exactly
once. -/
theorem alternatingSixFiveCTblLibCorrectedAmbientPosition_bijective :
    Function.Bijective alternatingSixFiveCTblLibCorrectedAmbientPosition := by
  decide

/-- The corrected ambient position orientation as an equivalence. -/
def alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv :
    Fin 24 ≃ AlternatingSixAmbientPPrimeRowIndex 5 :=
  Equiv.ofBijective
    alternatingSixFiveCTblLibCorrectedAmbientPosition
    alternatingSixFiveCTblLibCorrectedAmbientPosition_bijective

/-- The corrected and invariant-safe orientations agree away from positions
`21` and `23`. -/
theorem
    alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv_eq_invariantSafe
    (i : Fin 24)
    (hi : i ≠ 21)
    (hi' : i ≠ 23) :
    alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv i =
      alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv i := by
  fin_cases i <;> simp_all [
    alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv,
    alternatingSixFiveCTblLibCorrectedAmbientPosition,
    alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv,
    alternatingSixFiveCTblLibInvariantSafeAmbientPosition
  ]

/-- The corrected final four positions are exactly the certified ATLAS
power order `2, 7, 11, 1`. -/
theorem alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv_atlasBlock
    (i : Fin 4) :
    (alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv
        ⟨20 + i, by omega⟩).1 =
      ![AlternatingSixAmbientOrdinaryRow.atlasTwelvePowerTwo,
        .atlasTwelvePowerSeven,
        .atlasTwelvePowerEleven,
        .atlasTwelvePowerOne] i := by
  fin_cases i <;> rfl

/-- Use the audited candidate and the existing central-block matching to
orient local rows after correcting the ambient degree-twelve block. -/
def alternatingSixFiveCTblLibCorrectedRowIdentification :
    AlternatingSixFiveCTblLibRowIdentification where
  ambientPositionEquiv :=
    alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv
  localPositionEquiv :=
    alternatingSixCTblLibFivePPrimeActionData.candidate.symm.trans
      (alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv.trans
        alternatingSixAmbientFivePPrimeCentralBlockRowEquiv)

/-- Transport through the corrected positions still recovers the proved
central-block ambient/local row matching. -/
theorem alternatingSixFiveCTblLibCorrectedRowIdentification_candidate :
    (alternatingSixFiveCTblLibCorrectedRowIdentification
      |>.candidateAmbientLocalRowEquiv) =
      alternatingSixAmbientFivePPrimeCentralBlockRowEquiv := by
  apply Equiv.ext
  intro r
  simp [
    AlternatingSixFiveCTblLibRowIdentification.candidateAmbientLocalRowEquiv,
    alternatingSixFiveCTblLibCorrectedRowIdentification
  ]

/-! ### Prime-independence of the underlying ordinary row action -/

/-- If one ordinary row belongs to two prime-away subtypes, an automorphism
moves its two subtype copies to the same underlying ordinary row. -/
theorem alternatingSixAmbientPPrimeRowPermutation_val_primeIndependent
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p q : ℕ)
    (a : MulAut AlternatingSixUniversalCover)
    (row : AlternatingSixAmbientOrdinaryRow)
    (hp : ¬p ∣ row.dimension)
    (hq : ¬q ∣ row.dimension) :
    (alternatingSixAmbientPPrimeRowPermutation T p a ⟨row, hp⟩).1 =
      (alternatingSixAmbientPPrimeRowPermutation T q a ⟨row, hq⟩).1 := by
  apply T.row_injective
  change
    T.toFiniteCharacterTableCertificate.character
        (alternatingSixAmbientPPrimeRowPermutation T p a ⟨row, hp⟩).1 =
      T.toFiniteCharacterTableCertificate.character
        (alternatingSixAmbientPPrimeRowPermutation T q a ⟨row, hq⟩).1
  have hpAction :=
    congrArg Subtype.val
      (alternatingSixAmbientPPrimeRowPermutation_character
        T p a (⟨row, hp⟩ : AlternatingSixAmbientPPrimeRowIndex p))
  have hqAction :=
    congrArg Subtype.val
      (alternatingSixAmbientPPrimeRowPermutation_character
        T q a (⟨row, hq⟩ : AlternatingSixAmbientPPrimeRowIndex q))
  simpa only [
    alternatingSixAmbientPPrimeCharacterEquiv_apply_val
  ] using hpAction.trans hqAction.symm

/-! ### Reusing completed semantic actions across prime-away subtypes -/

@[simp]
theorem alternatingSixFiveAmbientAlphaOneRow01_fixed :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row01, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row01, by decide⟩ := by
  apply Subtype.ext
  calc
    (alternatingSixAmbientPPrimeAlphaOneRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate 5
          (⟨.row01, by decide⟩ :
            AlternatingSixAmbientPPrimeRowIndex 5)).1 =
        (alternatingSixAmbientPPrimeAlphaOneRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate 3
          (⟨.row01, by decide⟩ :
            AlternatingSixAmbientPPrimeRowIndex 3)).1 :=
      alternatingSixAmbientPPrimeRowPermutation_val_primeIndependent
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5 3
        alternatingSixUniversalCoverTransportedAlphaOne .row01
        (by decide) (by decide)
    _ = .row01 := by
      simpa [alternatingSixAmbientPPrimeAlphaOneRowPermutation,
        alternatingSixThreeTrivialPPrimeRow] using
        congrArg Subtype.val
          (alternatingSixThreeAmbientTrivialRow_fixed
            alternatingSixUniversalCoverTransportedAlphaOne)

@[simp]
theorem alternatingSixFiveAmbientAlphaTwoRow01_fixed :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row01, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row01, by decide⟩ := by
  apply Subtype.ext
  calc
    (alternatingSixAmbientPPrimeAlphaTwoRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate 5
          (⟨.row01, by decide⟩ :
            AlternatingSixAmbientPPrimeRowIndex 5)).1 =
        (alternatingSixAmbientPPrimeAlphaTwoRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate 3
          (⟨.row01, by decide⟩ :
            AlternatingSixAmbientPPrimeRowIndex 3)).1 :=
      alternatingSixAmbientPPrimeRowPermutation_val_primeIndependent
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5 3
        alternatingSixUniversalCoverTransportedAlphaTwo .row01
        (by decide) (by decide)
    _ = .row01 := by
      simpa [alternatingSixAmbientPPrimeAlphaTwoRowPermutation,
        alternatingSixThreeTrivialPPrimeRow] using
        congrArg Subtype.val
          (alternatingSixThreeAmbientTrivialRow_fixed
            alternatingSixUniversalCoverTransportedAlphaTwo)

@[simp]
theorem alternatingSixFiveAmbientAlphaOneRow18_eq_row19 :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row18, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row19, by decide⟩ := by
  apply Subtype.ext
  exact
    (alternatingSixAmbientPPrimeRowPermutation_val_primeIndependent
      alternatingSixAmbientOrdinaryCharacterTableCertificate 5 3
      alternatingSixUniversalCoverTransportedAlphaOne .row18
      (by decide) (by decide)).trans
      (congrArg Subtype.val
        alternatingSixThreeAmbientAlphaOneRow18_eq_row19)

@[simp]
theorem alternatingSixFiveAmbientAlphaOneRow19_eq_row18 :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row19, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row18, by decide⟩ := by
  apply Subtype.ext
  exact
    (alternatingSixAmbientPPrimeRowPermutation_val_primeIndependent
      alternatingSixAmbientOrdinaryCharacterTableCertificate 5 3
      alternatingSixUniversalCoverTransportedAlphaOne .row19
      (by decide) (by decide)).trans
      (congrArg Subtype.val
        alternatingSixThreeAmbientAlphaOneRow19_eq_row18)

@[simp]
theorem alternatingSixFiveAmbientAlphaTwoRow18_fixed :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row18, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row18, by decide⟩ := by
  apply Subtype.ext
  exact
    (alternatingSixAmbientPPrimeRowPermutation_val_primeIndependent
      alternatingSixAmbientOrdinaryCharacterTableCertificate 5 3
      alternatingSixUniversalCoverTransportedAlphaTwo .row18
      (by decide) (by decide)).trans
      (congrArg Subtype.val
        alternatingSixThreeAmbientAlphaTwoRow18_fixed)

@[simp]
theorem alternatingSixFiveAmbientAlphaTwoRow19_fixed :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row19, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row19, by decide⟩ := by
  apply Subtype.ext
  exact
    (alternatingSixAmbientPPrimeRowPermutation_val_primeIndependent
      alternatingSixAmbientOrdinaryCharacterTableCertificate 5 3
      alternatingSixUniversalCoverTransportedAlphaTwo .row19
      (by decide) (by decide)).trans
      (congrArg Subtype.val
        alternatingSixThreeAmbientAlphaTwoRow19_fixed)

@[simp]
theorem alternatingSixFiveAmbientAlphaOneRow06_fixed :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row06, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row06, by decide⟩ := by
  apply Subtype.ext
  exact
    (alternatingSixAmbientPPrimeRowPermutation_val_primeIndependent
      alternatingSixAmbientOrdinaryCharacterTableCertificate 5 3
      alternatingSixUniversalCoverTransportedAlphaOne .row06
      (by decide) (by decide)).trans
      (congrArg Subtype.val
        alternatingSixThreeAmbientAlphaOneRow06_fixed)

@[simp]
theorem alternatingSixFiveAmbientAlphaOneRow07_fixed :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row07, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row07, by decide⟩ := by
  apply Subtype.ext
  exact
    (alternatingSixAmbientPPrimeRowPermutation_val_primeIndependent
      alternatingSixAmbientOrdinaryCharacterTableCertificate 5 3
      alternatingSixUniversalCoverTransportedAlphaOne .row07
      (by decide) (by decide)).trans
      (congrArg Subtype.val
        alternatingSixThreeAmbientAlphaOneRow07_fixed)

@[simp]
theorem alternatingSixFiveAmbientAlphaTwoRow06_eq_row07 :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row06, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row07, by decide⟩ := by
  apply Subtype.ext
  exact
    (alternatingSixAmbientPPrimeRowPermutation_val_primeIndependent
      alternatingSixAmbientOrdinaryCharacterTableCertificate 5 3
      alternatingSixUniversalCoverTransportedAlphaTwo .row06
      (by decide) (by decide)).trans
      (congrArg Subtype.val
        alternatingSixThreeAmbientAlphaTwoRow06_eq_row07)

@[simp]
theorem alternatingSixFiveAmbientAlphaTwoRow07_eq_row06 :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row07, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row06, by decide⟩ := by
  apply Subtype.ext
  exact
    (alternatingSixAmbientPPrimeRowPermutation_val_primeIndependent
      alternatingSixAmbientOrdinaryCharacterTableCertificate 5 3
      alternatingSixUniversalCoverTransportedAlphaTwo .row07
      (by decide) (by decide)).trans
      (congrArg Subtype.val
        alternatingSixThreeAmbientAlphaTwoRow07_eq_row06)

@[simp]
theorem alternatingSixFiveAmbientAlphaTwoRow16_fixed :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row16, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row16, by decide⟩ := by
  apply Subtype.ext
  exact
    (alternatingSixAmbientPPrimeRowPermutation_val_primeIndependent
      alternatingSixAmbientOrdinaryCharacterTableCertificate 5 3
      alternatingSixUniversalCoverTransportedAlphaTwo .row16
      (by decide) (by decide)).trans
      (congrArg Subtype.val
        alternatingSixThreeAmbientAlphaTwoRow16_fixed)

@[simp]
theorem alternatingSixFiveAmbientAlphaTwoRow17_fixed :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row17, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row17, by decide⟩ := by
  apply Subtype.ext
  exact
    (alternatingSixAmbientPPrimeRowPermutation_val_primeIndependent
      alternatingSixAmbientOrdinaryCharacterTableCertificate 5 3
      alternatingSixUniversalCoverTransportedAlphaTwo .row17
      (by decide) (by decide)).trans
      (congrArg Subtype.val
        alternatingSixThreeAmbientAlphaTwoRow17_fixed)

@[simp]
theorem alternatingSixFiveAmbientAlphaOneRow16_eq_row17 :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row16, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row17, by decide⟩ := by
  apply Subtype.ext
  exact
    (alternatingSixAmbientPPrimeRowPermutation_val_primeIndependent
      alternatingSixAmbientOrdinaryCharacterTableCertificate 5 3
      alternatingSixUniversalCoverTransportedAlphaOne .row16
      (by decide) (by decide)).trans
      (congrArg Subtype.val
        alternatingSixThreeAmbientAlphaOneRow16_eq_row17)

@[simp]
theorem alternatingSixFiveAmbientAlphaOneRow17_eq_row16 :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row17, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row16, by decide⟩ := by
  apply Subtype.ext
  exact
    (alternatingSixAmbientPPrimeRowPermutation_val_primeIndependent
      alternatingSixAmbientOrdinaryCharacterTableCertificate 5 3
      alternatingSixUniversalCoverTransportedAlphaOne .row17
      (by decide) (by decide)).trans
      (congrArg Subtype.val
        alternatingSixThreeAmbientAlphaOneRow17_eq_row16)

/-! ### Exact semantic action on the corrected ATLAS block -/

private theorem completed_atlasPowerOne_classRepresentative
    (j : Fin 31) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character
          .atlasTwelvePowerOne).values
        (alternatingSixUniversalCoverClassRepresentative j) =
      alternatingSixAmbientAtlas12P1ClassValue j := by
  rw [FiniteCharacterTableCertificate.character_values_apply]
  exact alternatingSixAmbientAtlas12P1_character_classRepresentative j

private theorem completed_atlasPowerTwo_classRepresentative
    (j : Fin 31) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character
          .atlasTwelvePowerTwo).values
        (alternatingSixUniversalCoverClassRepresentative j) =
      alternatingSixAmbientAtlasTwelvePowerTwoClassValue j := by
  rw [FiniteCharacterTableCertificate.character_values_apply]
  exact
    alternatingSixAmbientAtlasTwelvePowerTwo_character_classRepresentative j

private theorem completed_atlasPowerSeven_classRepresentative
    (j : Fin 31) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character
          .atlasTwelvePowerSeven).values
        (alternatingSixUniversalCoverClassRepresentative j) =
      alternatingSixAmbientAtlasTwelvePowerSevenClassValue j := by
  rw [FiniteCharacterTableCertificate.character_values_apply]
  exact
    alternatingSixAmbientAtlasTwelvePowerSeven_character_classRepresentative j

private theorem completed_atlasPowerEleven_classRepresentative
    (j : Fin 31) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character
          .atlasTwelvePowerEleven).values
        (alternatingSixUniversalCoverClassRepresentative j) =
      alternatingSixAmbientAtlas12P11ClassValue j := by
  rw [FiniteCharacterTableCertificate.character_values_apply]
  exact alternatingSixAmbientAtlas12P11_character_classRepresentative j

private theorem completed_row20_classRepresentative
    (j : Fin 31) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row20).values
        (alternatingSixUniversalCoverClassRepresentative j) =
      alternatingSixAmbientRow20ClassValue j := by
  rw [FiniteCharacterTableCertificate.character_values_apply]
  exact alternatingSixAmbientRow20_character_classRepresentative j

private theorem completed_row21_classRepresentative
    (j : Fin 31) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row21).values
        (alternatingSixUniversalCoverClassRepresentative j) =
      alternatingSixAmbientRow21ClassValue j := by
  rw [FiniteCharacterTableCertificate.character_values_apply]
  exact alternatingSixAmbientRow21_character_classRepresentative j

private theorem completed_row22_classRepresentative
    (j : Fin 31) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row22).values
        (alternatingSixUniversalCoverClassRepresentative j) =
      alternatingSixAmbientRow22ClassValue j := by
  rw [FiniteCharacterTableCertificate.character_values_apply]
  exact alternatingSixAmbientRow22_character_classRepresentative j

private theorem row21Eta_sq : η₉ ^ 2 = η₉ - 1 := by
  rw [alternatingSixAmbientRow21Eta, ← pow_mul]
  norm_num
  exact alternatingSixAmbientRow22_root_pow_forty

private theorem row22Eta_eq_row21Eta :
    alternatingSixAmbientRow22Eta = η₉ :=
  rfl

private theorem row21Eta_cube : η₉ ^ 3 = -1 := by
  rw [show η₉ ^ 3 = η₉ * η₉ ^ 2 by ring, row21Eta_sq]
  linear_combination row21Eta_sq

private theorem row21Eta_pow_four : η₉ ^ 4 = -η₉ := by
  rw [show η₉ ^ 4 = η₉ * η₉ ^ 3 by ring, row21Eta_cube]
  ring

private theorem row21Eta_pow_five : η₉ ^ 5 = 1 - η₉ := by
  calc
    η₉ ^ 5 = η₉ * η₉ ^ 4 := by ring
    _ = η₉ * -η₉ := by rw [row21Eta_pow_four]
    _ = -(η₉ ^ 2) := by ring
    _ = -(η₉ - 1) := by rw [row21Eta_sq]
    _ = 1 - η₉ := by ring

private theorem row21Eta_pow_six : η₉ ^ 6 = 1 := by
  rw [show η₉ ^ 6 = (η₉ ^ 3) ^ 2 by ring, row21Eta_cube]
  ring

private theorem neg_row21Eta_sq : (-η₉) ^ 2 = η₉ - 1 := by
  rw [neg_sq, row21Eta_sq]

private theorem neg_row21Eta_cube : (-η₉) ^ 3 = 1 := by
  rw [neg_pow, row21Eta_cube]
  norm_num

private theorem neg_row21Eta_pow_four : (-η₉) ^ 4 = -η₉ := by
  rw [show (-η₉) ^ 4 = (-η₉) ^ 3 * (-η₉) by ring,
    neg_row21Eta_cube, one_mul]

private theorem neg_row21Eta_pow_five : (-η₉) ^ 5 = η₉ - 1 := by
  rw [show (-η₉) ^ 5 = (-η₉) ^ 3 * (-η₉) ^ 2 by ring,
    neg_row21Eta_cube, neg_row21Eta_sq, one_mul]

private theorem row21Eta_sub_one_sq : (η₉ - 1) ^ 2 = -η₉ := by
  rw [← row21Eta_sq, ← pow_mul]
  norm_num
  exact row21Eta_pow_four

private theorem row21Eta_sub_one_cube : (η₉ - 1) ^ 3 = 1 := by
  rw [← row21Eta_sq, ← pow_mul]
  norm_num
  exact row21Eta_pow_six

private theorem row21Eta_sub_one_pow_four :
    (η₉ - 1) ^ 4 = η₉ - 1 := by
  rw [show (η₉ - 1) ^ 4 = (η₉ - 1) ^ 3 * (η₉ - 1) by ring,
    row21Eta_sub_one_cube, one_mul]

private theorem row21Eta_sub_one_pow_five :
    (η₉ - 1) ^ 5 = -η₉ := by
  rw [show (η₉ - 1) ^ 5 = (η₉ - 1) ^ 3 * (η₉ - 1) ^ 2 by ring,
    row21Eta_sub_one_cube, row21Eta_sub_one_sq, one_mul]

private theorem row22_to_row21_alphaOne_classValue
    (j : Fin 31) :
    alternatingSixAmbientRow21ClassValue j =
      alternatingSixAmbientRow22ClassValue
        (alternatingSixAlphaOneConjugacyClassPermutation.symm j) := by
  rw [alternatingSixAlphaOneConjugacyClassPermutation_symm_eq_vector]
  fin_cases j <;>
    simp [
      alternatingSixAlphaOneConjugacyClassVector,
      alternatingSixAmbientRow21ClassValue,
      alternatingSixAmbientRow22ClassValue,
      row22Eta_eq_row21Eta,
      row21Eta_sq,
      neg_row21Eta_cube,
      neg_row21Eta_pow_four,
      neg_row21Eta_pow_five,
      row21Eta_sub_one_sq,
      row21Eta_sub_one_cube,
      row21Eta_sub_one_pow_four,
      row21Eta_sub_one_pow_five
    ]
  all_goals
    ring_nf <;>
      try (rw [row21Eta_sq]; ring)

private theorem row22_to_row21_alphaTwo_classValue
    (j : Fin 31) :
    alternatingSixAmbientRow21ClassValue j =
      alternatingSixAmbientRow22ClassValue
        (alternatingSixAlphaTwoConjugacyClassPermutation.symm j) := by
  rw [alternatingSixAlphaTwoConjugacyClassPermutation_symm_eq_vector]
  fin_cases j <;>
    simp [
      alternatingSixAlphaTwoConjugacyClassVector,
      alternatingSixAmbientRow21ClassValue,
      alternatingSixAmbientRow22ClassValue,
      row22Eta_eq_row21Eta,
      row21Eta_sq,
      neg_row21Eta_cube,
      neg_row21Eta_pow_four,
      neg_row21Eta_pow_five,
      row21Eta_sub_one_sq,
      row21Eta_sub_one_cube,
      row21Eta_sub_one_pow_four,
      row21Eta_sub_one_pow_five
    ]
  all_goals
    ring_nf <;>
      try (rw [row21Eta_sq]; ring)

private theorem row21_to_row22_alphaOne_classValue
    (j : Fin 31) :
    alternatingSixAmbientRow22ClassValue j =
      alternatingSixAmbientRow21ClassValue
        (alternatingSixAlphaOneConjugacyClassPermutation.symm j) := by
  calc
    alternatingSixAmbientRow22ClassValue j =
        alternatingSixAmbientRow22ClassValue
          (alternatingSixAlphaOneConjugacyClassPermutation.symm
            (alternatingSixAlphaOneConjugacyClassPermutation.symm j)) := by
      rw [alternatingSixAlphaOneConjugacyClassPermutation_symm_symm]
    _ =
        alternatingSixAmbientRow21ClassValue
          (alternatingSixAlphaOneConjugacyClassPermutation.symm j) :=
      (row22_to_row21_alphaOne_classValue _).symm

private theorem row21_to_row22_alphaTwo_classValue
    (j : Fin 31) :
    alternatingSixAmbientRow22ClassValue j =
      alternatingSixAmbientRow21ClassValue
        (alternatingSixAlphaTwoConjugacyClassPermutation.symm j) := by
  calc
    alternatingSixAmbientRow22ClassValue j =
        alternatingSixAmbientRow22ClassValue
          (alternatingSixAlphaTwoConjugacyClassPermutation.symm
            (alternatingSixAlphaTwoConjugacyClassPermutation.symm j)) := by
      rw [alternatingSixAlphaTwoConjugacyClassPermutation_symm_symm]
    _ =
        alternatingSixAmbientRow21ClassValue
          (alternatingSixAlphaTwoConjugacyClassPermutation.symm j) :=
      (row22_to_row21_alphaTwo_classValue _).symm

private theorem correctedAlphaOneRow_eq_of_classValues
    (source target : AlternatingSixAmbientPPrimeRowIndex 5)
    (hValues :
      ∀ j : Fin 31,
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
            |>.toFiniteCharacterTableCertificate.character target.1).values
            (alternatingSixUniversalCoverClassRepresentative j) =
          (alternatingSixAmbientOrdinaryCharacterTableCertificate
              |>.toFiniteCharacterTableCertificate.character source.1).values
            (alternatingSixUniversalCoverClassRepresentative
              (alternatingSixAlphaOneConjugacyClassPermutation.symm j))) :
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 5) source =
      target := by
  apply Subtype.ext
  apply
    alternatingSixAmbientOrdinaryRow_eq_of_values_classRepresentative_eq
      alternatingSixAmbientOrdinaryCharacterTableCertificate
  intro j
  rw [alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq]
  exact
    (alternatingSixAmbientPPrimeAlphaOneRowPermutation_values_classRepresentative
      alternatingSixAmbientOrdinaryCharacterTableCertificate 5 source j).trans
      (hValues j).symm

private theorem correctedAlphaTwoRow_eq_of_classValues
    (source target : AlternatingSixAmbientPPrimeRowIndex 5)
    (hValues :
      ∀ j : Fin 31,
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
            |>.toFiniteCharacterTableCertificate.character target.1).values
            (alternatingSixUniversalCoverClassRepresentative j) =
          (alternatingSixAmbientOrdinaryCharacterTableCertificate
              |>.toFiniteCharacterTableCertificate.character source.1).values
            (alternatingSixUniversalCoverClassRepresentative
              (alternatingSixAlphaTwoConjugacyClassPermutation.symm j))) :
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 5) source =
      target := by
  apply Subtype.ext
  apply
    alternatingSixAmbientOrdinaryRow_eq_of_values_classRepresentative_eq
      alternatingSixAmbientOrdinaryCharacterTableCertificate
  intro j
  rw [alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq]
  exact
    (alternatingSixAmbientPPrimeAlphaTwoRowPermutation_values_classRepresentative
      alternatingSixAmbientOrdinaryCharacterTableCertificate 5 source j).trans
      (hValues j).symm

@[simp]
theorem alternatingSixFiveAmbientCorrectedAlphaOneRow20_fixed :
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 5)
        (⟨.row20, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row20, by decide⟩ := by
  apply correctedAlphaOneRow_eq_of_classValues
  intro j
  rw [completed_row20_classRepresentative,
    completed_row20_classRepresentative,
    alternatingSixAlphaOneConjugacyClassPermutation_symm_eq_vector]
  fin_cases j <;>
    rfl

@[simp]
theorem alternatingSixFiveAmbientCorrectedAlphaTwoRow20_fixed :
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 5)
        (⟨.row20, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row20, by decide⟩ := by
  apply correctedAlphaTwoRow_eq_of_classValues
  intro j
  rw [completed_row20_classRepresentative,
    completed_row20_classRepresentative,
    alternatingSixAlphaTwoConjugacyClassPermutation_symm_eq_vector]
  fin_cases j <;>
    rfl

@[simp]
theorem alternatingSixFiveAmbientCorrectedAlphaOneRow22_eq_row21 :
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 5)
        (⟨.row22, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row21, by decide⟩ := by
  apply correctedAlphaOneRow_eq_of_classValues
  intro j
  rw [completed_row21_classRepresentative,
    completed_row22_classRepresentative]
  exact row22_to_row21_alphaOne_classValue j

@[simp]
theorem alternatingSixFiveAmbientCorrectedAlphaOneRow21_eq_row22 :
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 5)
        (⟨.row21, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row22, by decide⟩ := by
  apply correctedAlphaOneRow_eq_of_classValues
  intro j
  rw [completed_row22_classRepresentative,
    completed_row21_classRepresentative]
  exact row21_to_row22_alphaOne_classValue j

@[simp]
theorem alternatingSixFiveAmbientCorrectedAlphaTwoRow22_eq_row21 :
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 5)
        (⟨.row22, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row21, by decide⟩ := by
  apply correctedAlphaTwoRow_eq_of_classValues
  intro j
  rw [completed_row21_classRepresentative,
    completed_row22_classRepresentative]
  exact row22_to_row21_alphaTwo_classValue j

@[simp]
theorem alternatingSixFiveAmbientCorrectedAlphaTwoRow21_eq_row22 :
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 5)
        (⟨.row21, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row22, by decide⟩ := by
  apply correctedAlphaTwoRow_eq_of_classValues
  intro j
  rw [completed_row22_classRepresentative,
    completed_row21_classRepresentative]
  exact row21_to_row22_alphaTwo_classValue j

/- These uncorrected aliases are the proof-irrelevance-friendly simp API used
below.  The corrected permutations are definitionally the same row actions,
but the generic reduction lemma rewrites them to the uncorrected names before
the concrete row facts can fire. -/

@[simp]
theorem alternatingSixFiveAmbientAlphaOneRow20_fixed :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row20, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row20, by decide⟩ := by
  simpa only [
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq
  ] using alternatingSixFiveAmbientCorrectedAlphaOneRow20_fixed

@[simp]
theorem alternatingSixFiveAmbientAlphaTwoRow20_fixed :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row20, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row20, by decide⟩ := by
  simpa only [
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq
  ] using alternatingSixFiveAmbientCorrectedAlphaTwoRow20_fixed

@[simp]
theorem alternatingSixFiveAmbientAlphaOneRow22_eq_row21 :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row22, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row21, by decide⟩ := by
  simpa only [
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq
  ] using alternatingSixFiveAmbientCorrectedAlphaOneRow22_eq_row21

@[simp]
theorem alternatingSixFiveAmbientAlphaOneRow21_eq_row22 :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row21, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row22, by decide⟩ := by
  simpa only [
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq
  ] using alternatingSixFiveAmbientCorrectedAlphaOneRow21_eq_row22

@[simp]
theorem alternatingSixFiveAmbientAlphaTwoRow22_eq_row21 :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row22, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row21, by decide⟩ := by
  simpa only [
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq
  ] using alternatingSixFiveAmbientCorrectedAlphaTwoRow22_eq_row21

@[simp]
theorem alternatingSixFiveAmbientAlphaTwoRow21_eq_row22 :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        (⟨.row21, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 5) =
      ⟨.row22, by decide⟩ := by
  simpa only [
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq
  ] using alternatingSixFiveAmbientCorrectedAlphaTwoRow21_eq_row22

/-- The first genuine corrected ambient generator agrees with the audited
permutation on all four corrected degree-twelve positions. -/
theorem alternatingSixFiveCTblLibCorrected_ambientAlphaOne_atlasBlock
    (i : Fin 24)
    (hi : 20 ≤ i.val) :
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 5)
        (alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv i) =
      alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv
        (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne i) := by
  have hiCases : i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 := by
    omega
  rcases hiCases with rfl | rfl | rfl | rfl
  · change
      alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 5)
          (⟨.atlasTwelvePowerTwo, by decide⟩ :
            AlternatingSixAmbientPPrimeRowIndex 5) =
        ⟨.atlasTwelvePowerOne, by decide⟩
    apply correctedAlphaOneRow_eq_of_classValues
    intro j
    rw [completed_atlasPowerOne_classRepresentative,
      completed_atlasPowerTwo_classRepresentative]
    exact alternatingSixAmbientAtlasTwelvePowerTwo_alphaOne_classValue j
  · change
      alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 5)
          (⟨.atlasTwelvePowerSeven, by decide⟩ :
            AlternatingSixAmbientPPrimeRowIndex 5) =
        ⟨.atlasTwelvePowerEleven, by decide⟩
    apply correctedAlphaOneRow_eq_of_classValues
    intro j
    rw [completed_atlasPowerEleven_classRepresentative,
      completed_atlasPowerSeven_classRepresentative]
    exact alternatingSixAmbientAtlasTwelvePowerSeven_alphaOne_classValue j
  · change
      alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 5)
          (⟨.atlasTwelvePowerEleven, by decide⟩ :
            AlternatingSixAmbientPPrimeRowIndex 5) =
        ⟨.atlasTwelvePowerSeven, by decide⟩
    apply correctedAlphaOneRow_eq_of_classValues
    intro j
    rw [completed_atlasPowerSeven_classRepresentative,
      completed_atlasPowerEleven_classRepresentative]
    exact alternatingSixAmbientAtlas12P11_alphaOne_classValue j
  · change
      alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 5)
          (⟨.atlasTwelvePowerOne, by decide⟩ :
            AlternatingSixAmbientPPrimeRowIndex 5) =
        ⟨.atlasTwelvePowerTwo, by decide⟩
    apply correctedAlphaOneRow_eq_of_classValues
    intro j
    rw [completed_atlasPowerTwo_classRepresentative,
      completed_atlasPowerOne_classRepresentative]
    exact alternatingSixAmbientAtlas12P1_alphaOne_classValue j

/-- The second genuine corrected ambient generator agrees with the audited
permutation on all four corrected degree-twelve positions. -/
theorem alternatingSixFiveCTblLibCorrected_ambientAlphaTwo_atlasBlock
    (i : Fin 24)
    (hi : 20 ≤ i.val) :
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 5)
        (alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv i) =
      alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv
        (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i) := by
  have hiCases : i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 := by
    omega
  rcases hiCases with rfl | rfl | rfl | rfl
  · change
      alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 5)
          (⟨.atlasTwelvePowerTwo, by decide⟩ :
            AlternatingSixAmbientPPrimeRowIndex 5) =
        ⟨.atlasTwelvePowerSeven, by decide⟩
    apply correctedAlphaTwoRow_eq_of_classValues
    intro j
    rw [completed_atlasPowerSeven_classRepresentative,
      completed_atlasPowerTwo_classRepresentative]
    exact alternatingSixAmbientAtlasTwelvePowerTwo_alphaTwo_classValue j
  · change
      alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 5)
          (⟨.atlasTwelvePowerSeven, by decide⟩ :
            AlternatingSixAmbientPPrimeRowIndex 5) =
        ⟨.atlasTwelvePowerTwo, by decide⟩
    apply correctedAlphaTwoRow_eq_of_classValues
    intro j
    rw [completed_atlasPowerTwo_classRepresentative,
      completed_atlasPowerSeven_classRepresentative]
    exact alternatingSixAmbientAtlasTwelvePowerSeven_alphaTwo_classValue j
  · change
      alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 5)
          (⟨.atlasTwelvePowerEleven, by decide⟩ :
            AlternatingSixAmbientPPrimeRowIndex 5) =
        ⟨.atlasTwelvePowerOne, by decide⟩
    apply correctedAlphaTwoRow_eq_of_classValues
    intro j
    rw [completed_atlasPowerOne_classRepresentative,
      completed_atlasPowerEleven_classRepresentative]
    exact alternatingSixAmbientAtlas12P11_alphaTwo_classValue j
  · change
      alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 5)
          (⟨.atlasTwelvePowerOne, by decide⟩ :
            AlternatingSixAmbientPPrimeRowIndex 5) =
        ⟨.atlasTwelvePowerEleven, by decide⟩
    apply correctedAlphaTwoRow_eq_of_classValues
    intro j
    rw [completed_atlasPowerEleven_classRepresentative,
      completed_atlasPowerOne_classRepresentative]
    exact alternatingSixAmbientAtlas12P1_alphaTwo_classValue j

/-! ### Exact residual seams -/

/-- The ten first-generator positions whose row pairs do not yet have
completed semantic value transport: `8..13` and `16..19`. -/
def AlternatingSixFiveCorrectedAlphaOneRemainingAmbientPosition
    (i : Fin 24) : Prop :=
  (8 ≤ i.val ∧ i.val < 14) ∨
    (16 ≤ i.val ∧ i.val < 20)

/-- The ten second-generator positions whose row pairs do not yet have
completed semantic value transport: `8..13` and `16..19`. -/
def AlternatingSixFiveCorrectedAlphaTwoRemainingAmbientPosition
    (i : Fin 24) : Prop :=
  (8 ≤ i.val ∧ i.val < 14) ∨
    (16 ≤ i.val ∧ i.val < 20)

instance :
    DecidablePred
      AlternatingSixFiveCorrectedAlphaOneRemainingAmbientPosition :=
  fun i => by
    unfold AlternatingSixFiveCorrectedAlphaOneRemainingAmbientPosition
    infer_instance

instance :
    DecidablePred
      AlternatingSixFiveCorrectedAlphaTwoRemainingAmbientPosition :=
  fun i => by
    unfold AlternatingSixFiveCorrectedAlphaTwoRemainingAmbientPosition
    infer_instance

/-- Exactly ten corrected positions remain for the first generator. -/
theorem
    alternatingSixFiveCorrectedAlphaOneRemainingAmbientPosition_card :
    Fintype.card
        {i : Fin 24 //
          AlternatingSixFiveCorrectedAlphaOneRemainingAmbientPosition i} =
      10 := by
  decide

/-- Exactly ten corrected positions remain for the second generator. -/
theorem
    alternatingSixFiveCorrectedAlphaTwoRemainingAmbientPosition_card :
    Fintype.card
        {i : Fin 24 //
          AlternatingSixFiveCorrectedAlphaTwoRemainingAmbientPosition i} =
      10 := by
  decide

private theorem correctedAlphaOne_remaining_or_resolved
    (i : Fin 24) :
    AlternatingSixFiveCorrectedAlphaOneRemainingAmbientPosition i ∨
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
      i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 14 ∨ i = 15 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 := by
  fin_cases i <;>
    simp [AlternatingSixFiveCorrectedAlphaOneRemainingAmbientPosition]

private theorem correctedAlphaTwo_remaining_or_resolved
    (i : Fin 24) :
    AlternatingSixFiveCorrectedAlphaTwoRemainingAmbientPosition i ∨
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
      i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 14 ∨ i = 15 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 := by
  fin_cases i <;>
    simp [AlternatingSixFiveCorrectedAlphaTwoRemainingAmbientPosition]

namespace AlternatingSixFiveCTblLibRowIdentification

variable (identification : AlternatingSixFiveCTblLibRowIdentification)

/-- First ambient bridge restricted to the exact ten positions not yet
settled by the completed value APIs. -/
def AmbientCorrectedAlphaOneBridgeOnCorrectedRemainingPositions : Prop :=
  ∀ i : Fin 24,
    AlternatingSixFiveCorrectedAlphaOneRemainingAmbientPosition i →
      alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 5)
          (identification.ambientPositionEquiv i) =
        identification.ambientPositionEquiv
          (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne i)

/-- Second ambient bridge restricted to the exact ten positions not yet
settled by the completed value APIs. -/
def AmbientCorrectedAlphaTwoBridgeOnCorrectedRemainingPositions : Prop :=
  ∀ i : Fin 24,
    AlternatingSixFiveCorrectedAlphaTwoRemainingAmbientPosition i →
      alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 5)
          (identification.ambientPositionEquiv i) =
        identification.ambientPositionEquiv
          (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i)

end AlternatingSixFiveCTblLibRowIdentification

private theorem corrected_ambientAlphaOne_resolved
    (i : Fin 24)
    (hi :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
      i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 14 ∨ i = 15 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23) :
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 5)
        (alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv i) =
      alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv
        (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne i) := by
  rcases hi with
    rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exact
        alternatingSixFiveCTblLibCorrected_ambientAlphaOne_atlasBlock _
          (by decide)
    | simp [
        alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv,
        alternatingSixFiveCTblLibCorrectedAmbientPosition,
        alternatingSixCTblLibFivePPrimeActionData
      ]

private theorem corrected_ambientAlphaTwo_resolved
    (i : Fin 24)
    (hi :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
      i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 14 ∨ i = 15 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23) :
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 5)
        (alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv i) =
      alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv
        (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i) := by
  rcases hi with
    rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exact
        alternatingSixFiveCTblLibCorrected_ambientAlphaTwo_atlasBlock _
          (by decide)
    | simp [
        alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv,
        alternatingSixFiveCTblLibCorrectedAmbientPosition,
        alternatingSixCTblLibFivePPrimeActionData
      ]

/-- The corrected first full ambient bridge is equivalent to exactly the
ten residual positions carrying rows `02..05`, `10/11`, and `12..15` in
the corrected orientation. -/
theorem
    alternatingSixFiveCTblLibCorrected_ambientAlphaOneBridge_iff_tenRemaining :
    (alternatingSixFiveCTblLibCorrectedRowIdentification
      |>.AmbientCorrectedAlphaOneBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate) ↔
      (alternatingSixFiveCTblLibCorrectedRowIdentification
        |>.AmbientCorrectedAlphaOneBridgeOnCorrectedRemainingPositions) := by
  constructor
  · intro h i _
    exact h i
  · intro h i
    rcases correctedAlphaOne_remaining_or_resolved i with hi | hi
    · exact h i hi
    · exact corrected_ambientAlphaOne_resolved i hi

/-- The corrected second full ambient bridge is equivalent to exactly the
ten residual positions carrying rows `02..05`, `10/11`, and `12..15` in
the corrected orientation. -/
theorem
    alternatingSixFiveCTblLibCorrected_ambientAlphaTwoBridge_iff_tenRemaining :
    (alternatingSixFiveCTblLibCorrectedRowIdentification
      |>.AmbientCorrectedAlphaTwoBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate) ↔
      (alternatingSixFiveCTblLibCorrectedRowIdentification
        |>.AmbientCorrectedAlphaTwoBridgeOnCorrectedRemainingPositions) := by
  constructor
  · intro h i _
    exact h i
  · intro h i
    rcases correctedAlphaTwo_remaining_or_resolved i with hi | hi
    · exact h i hi
    · exact corrected_ambientAlphaTwo_resolved i hi

end InductiveMcKay
end McKayConjecture
