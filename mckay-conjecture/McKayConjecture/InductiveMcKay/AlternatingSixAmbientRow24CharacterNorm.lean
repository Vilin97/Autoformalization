/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientInverseClassTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow24ClassValues

/-!
# The class-value norm certificate for ambient row 24

The 31-term weighted sum collapses to the square of the single cyclotomic
base value `γ`. Its square is reduced exactly using the degree-32
cyclotomic relation for the fixed primitive 120th root.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private abbrev row24Certificate :=
  alternatingSixAmbientRow24ClassMatrixCertificate

/-- The nonintegral-looking generator value has square norm two. -/
theorem alternatingSixAmbientRow24_gamma_sq :
    alternatingSixAmbientRow24Gamma ^ 2 = 2 := by
  simp [alternatingSixAmbientRow24Gamma,
    alternatingSixCyclotomicValue]
  linear_combination
    (-(2 : ℂ) +
          (2 : ℂ) * ζ ^ 4 -
        (2 : ℂ) * ζ ^ 8 +
        ζ ^ 10 -
        ζ ^ 14 +
        ζ ^ 18) *
      alternatingSixComplexCyclotomicRoot_relation

/-- Expansion of the 31-term weighted norm into the one nonzero
cyclotomic base value. -/
theorem alternatingSixAmbientRow24_weightedSelfPairing_collapsed :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientRow24ClassValue i *
            alternatingSixAmbientRow24ClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      600 + 540 * alternatingSixAmbientRow24Gamma ^ 2 + 480 := by
  simp_rw [alternatingSixSchurInverseClassIndex_eq_table]
  simp [Fin.sum_univ_succ,
    alternatingSixAmbientRow24ClassValue,
    alternatingSixAmbientInverseClassIndexTable,
    alternatingSixSchurClassSize]
  ring

/-- Exact class-size weighted self-pairing of row 24. -/
theorem alternatingSixAmbientRow24_weightedSelfPairing :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientRow24ClassValue i *
            alternatingSixAmbientRow24ClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      2160 := by
  rw [alternatingSixAmbientRow24_weightedSelfPairing_collapsed,
    alternatingSixAmbientRow24_gamma_sq]
  norm_num

/-- Complete class-value certificate for the isolated row-24
representation. -/
def alternatingSixAmbientRow24ClassCharacterCertificate :
    AlternatingSixAmbientClassCharacterCertificate
      (FDRep.of row24Certificate.universalCoverRepresentation) where
  value := alternatingSixAmbientRow24ClassValue
  character_representative :=
    alternatingSixAmbientRow24_character_classRepresentative
  weightedSelfPairing :=
    alternatingSixAmbientRow24_weightedSelfPairing

/-- The row-24 class calculation proves its unnormalized character
self-pairing is the order of the universal cover. -/
theorem alternatingSixAmbientRow24_characterSelfPairing :
    characterSelfPairingSum
        (FDRep.of row24Certificate.universalCoverRepresentation) =
      (Nat.card AlternatingSixUniversalCover : ℂ) :=
  alternatingSixAmbientRow24ClassCharacterCertificate.characterSelfPairing

/-- Row 24 as a normalized irreducible character-row certificate. -/
def alternatingSixAmbientRow24CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow24ClassCharacterCertificate
    |>.characterRowCertificate

end InductiveMcKay
end McKayConjecture
