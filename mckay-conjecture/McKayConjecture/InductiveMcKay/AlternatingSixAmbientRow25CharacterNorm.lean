/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientInverseClassTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow25ClassValues

/-!
# The class-value norm certificate for ambient row 25

The shared inverse-class permutation reduces the character self-pairing to
the one nonrational-looking value `Γ`. Its square is two by the degree-32
cyclotomic relation for the fixed primitive 120th root, and the exact
class-size weighted sum is 2160.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private abbrev row25Certificate :=
  alternatingSixAmbientRow25ClassMatrixCertificate

/-- The row-25 generator-`b` trace has square two. -/
theorem alternatingSixAmbientRow25Gamma_sq :
    alternatingSixAmbientRow25Gamma ^ 2 = 2 := by
  simp [alternatingSixAmbientRow25Gamma,
    alternatingSixCyclotomicValue]
  linear_combination
    (-(2 : ℂ) + 2 * ζ ^ 4 - 2 * ζ ^ 8 +
        ζ ^ 10 - ζ ^ 14 + ζ ^ 18) *
      alternatingSixComplexCyclotomicRoot_relation

/-- Expansion of the 31-term weighted norm into the one cyclotomic square. -/
theorem alternatingSixAmbientRow25_weightedSelfPairing_collapsed :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientRow25ClassValue i *
            alternatingSixAmbientRow25ClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      600 + 540 * alternatingSixAmbientRow25Gamma ^ 2 + 480 := by
  simp_rw [alternatingSixSchurInverseClassIndex_eq_table]
  simp [Fin.sum_univ_succ,
    alternatingSixAmbientRow25ClassValue,
    alternatingSixAmbientInverseClassIndexTable,
    alternatingSixSchurClassSize]
  ring

/-- Exact class-size weighted self-pairing of row 25. -/
theorem alternatingSixAmbientRow25_weightedSelfPairing :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientRow25ClassValue i *
            alternatingSixAmbientRow25ClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      2160 := by
  rw [alternatingSixAmbientRow25_weightedSelfPairing_collapsed,
    alternatingSixAmbientRow25Gamma_sq]
  norm_num

/-- Complete class-value certificate for the isolated row-25
representation. -/
def alternatingSixAmbientRow25ClassCharacterCertificate :
    AlternatingSixAmbientClassCharacterCertificate
      (FDRep.of row25Certificate.universalCoverRepresentation) where
  value := alternatingSixAmbientRow25ClassValue
  character_representative :=
    alternatingSixAmbientRow25_character_classRepresentative
  weightedSelfPairing :=
    alternatingSixAmbientRow25_weightedSelfPairing

/-- The row-25 class calculation proves its unnormalized character
self-pairing is the order of the universal cover. -/
theorem alternatingSixAmbientRow25_characterSelfPairing :
    characterSelfPairingSum
        (FDRep.of row25Certificate.universalCoverRepresentation) =
      (Nat.card AlternatingSixUniversalCover : ℂ) :=
  alternatingSixAmbientRow25ClassCharacterCertificate.characterSelfPairing

/-- Row 25 as a normalized irreducible character-row certificate. -/
def alternatingSixAmbientRow25CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow25ClassCharacterCertificate
    |>.characterRowCertificate

end InductiveMcKay
end McKayConjecture
