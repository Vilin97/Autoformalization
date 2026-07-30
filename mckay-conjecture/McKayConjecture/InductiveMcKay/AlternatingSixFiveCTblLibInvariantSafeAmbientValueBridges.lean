/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCTblLibInvariantSafeRowIdentification
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientCompletedOrdinaryCharacterTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelveCharacterSeparation

/-!
# Class-value obstructions to the invariant-safe five-local ambient bridges

The invariant-safe five-local position orientation preserves character
degree and the audited central exponent, but those elementary invariants do
not determine the true CTblLib ordering inside the remaining two-row blocks.

The four constructed degree-twelve ATLAS rows have complete exact values on
all thirty-one certified conjugacy-class representatives.  Evaluating the
two proposed ambient bridges at zero-based position `20` and class `15`
shows that both are false:

* for the first generator the proposed equality identifies the distinct
  power-one and power-seven `AB` traces;
* for the second generator the same equality, after the already proved
  inverse-trace reduction, again identifies those two distinct traces.

Thus the `24 × 31` class-value seams exposed by the invariant-safe
orientation are not merely unproved: each ambient seam already fails at one
explicit degree-twelve coordinate.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveInvariantSafeAmbientValueBridgesFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

private theorem alternatingSixAlphaOneConjugacyClassPermutation_symm_fifteen :
    alternatingSixAlphaOneConjugacyClassPermutation.symm (15 : Fin 31) =
      21 := by
  apply alternatingSixAlphaOneConjugacyClassPermutation.injective
  rw [alternatingSixAlphaOneConjugacyClassPermutation.apply_symm_apply]
  rw [alternatingSixAlphaOneConjugacyClassPermutation_eq_vector]
  rfl

private theorem alternatingSixAlphaTwoConjugacyClassPermutation_symm_fifteen :
    alternatingSixAlphaTwoConjugacyClassPermutation.symm (15 : Fin 31) =
      19 := by
  apply alternatingSixAlphaTwoConjugacyClassPermutation.injective
  rw [alternatingSixAlphaTwoConjugacyClassPermutation.apply_symm_apply]
  rw [alternatingSixAlphaTwoConjugacyClassPermutation_eq_vector]
  rfl

private theorem
    alternatingSixCompletedTable_atlasPowerOne_classRepresentative
    (j : Fin 31) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character
          .atlasTwelvePowerOne).values
        (alternatingSixUniversalCoverClassRepresentative j) =
      alternatingSixAmbientAtlas12P1ClassValue j := by
  rw [FiniteCharacterTableCertificate.character_values_apply]
  exact alternatingSixAmbientAtlas12P1_character_classRepresentative j

private theorem
    alternatingSixCompletedTable_atlasPowerTwo_classRepresentative
    (j : Fin 31) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character
          .atlasTwelvePowerTwo).values
        (alternatingSixUniversalCoverClassRepresentative j) =
      alternatingSixAmbientAtlasTwelvePowerTwoClassValue j := by
  rw [FiniteCharacterTableCertificate.character_values_apply]
  exact
    alternatingSixAmbientAtlasTwelvePowerTwo_character_classRepresentative j

private theorem
    alternatingSixCompletedTable_atlasPowerSeven_classRepresentative
    (j : Fin 31) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character
          .atlasTwelvePowerSeven).values
        (alternatingSixUniversalCoverClassRepresentative j) =
      alternatingSixAmbientAtlasTwelvePowerSevenClassValue j := by
  rw [FiniteCharacterTableCertificate.character_values_apply]
  exact
    alternatingSixAmbientAtlasTwelvePowerSeven_character_classRepresentative j

private theorem alternatingSixAmbientAtlasPowerOneAlpha_ne_powerSevenAlpha :
    alternatingSixAmbientAtlas12P1Alpha ≠
      alternatingSixAmbientAtlasTwelvePowerSevenAlpha := by
  have h :=
    alternatingSixAmbientAtlas12Power1_matrixAB_trace_ne_power7_matrixAB_trace
  rw [alternatingSixAmbientAtlas12Power1_matrixAB_trace,
    alternatingSixAmbientAtlas12Power7_matrixAB_trace] at h
  exact h

/-- The exact failed coordinate of the first `24 × 31` class-value seam:
zero-based ambient position `20` and checked class `15`. -/
theorem
    alternatingSixFiveCTblLibInvariantSafe_ambientAlphaOne_classValueCounterexample :
    ¬((alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character
            (alternatingSixFiveCTblLibInvariantSafeRowIdentification
              |>.ambientPositionEquiv
                (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne
                  (20 : Fin 24))).1).values
          (alternatingSixUniversalCoverClassRepresentative (15 : Fin 31)) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
            |>.toFiniteCharacterTableCertificate.character
              (alternatingSixFiveCTblLibInvariantSafeRowIdentification
                |>.ambientPositionEquiv (20 : Fin 24)).1).values
          (alternatingSixUniversalCoverClassRepresentative
            (alternatingSixAlphaOneConjugacyClassPermutation.symm
              (15 : Fin 31)))) := by
  intro hValue
  rw [alternatingSixAlphaOneConjugacyClassPermutation_symm_fifteen] at hValue
  change
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character
          .atlasTwelvePowerSeven).values
        (alternatingSixUniversalCoverClassRepresentative 15) =
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character
            .atlasTwelvePowerTwo).values
        (alternatingSixUniversalCoverClassRepresentative 21)
    at hValue
  rw [alternatingSixCompletedTable_atlasPowerSeven_classRepresentative,
    alternatingSixCompletedTable_atlasPowerTwo_classRepresentative] at hValue
  apply alternatingSixAmbientAtlasPowerOneAlpha_ne_powerSevenAlpha
  simpa [alternatingSixAmbientAtlasTwelvePowerSevenClassValue,
    alternatingSixAmbientAtlasTwelvePowerTwoClassValue,
    alternatingSixAmbientAtlasTwelvePowerTwoBeta,
    alternatingSixAmbientAtlas12P1Alpha] using hValue.symm

/-- Since one exact coordinate fails, the proposed first ambient semantic
bridge is false. -/
theorem
    alternatingSixFiveCTblLibInvariantSafe_not_ambientAlphaOneBridge :
    ¬(alternatingSixFiveCTblLibInvariantSafeRowIdentification
        |>.AmbientCorrectedAlphaOneBridge
          alternatingSixAmbientOrdinaryCharacterTableCertificate) := by
  intro hBridge
  apply
    alternatingSixFiveCTblLibInvariantSafe_ambientAlphaOne_classValueCounterexample
  exact
    (alternatingSixFiveCTblLibInvariantSafeRowIdentification
      |>.ambientAlphaOneBridge_iff_classValues
        alternatingSixAmbientOrdinaryCharacterTableCertificate).mp
      hBridge (20 : Fin 24) (15 : Fin 31)

/-- The exact failed coordinate of the second `24 × 31` class-value seam:
zero-based ambient position `20` and checked class `15`. -/
theorem
    alternatingSixFiveCTblLibInvariantSafe_ambientAlphaTwo_classValueCounterexample :
    ¬((alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character
            (alternatingSixFiveCTblLibInvariantSafeRowIdentification
              |>.ambientPositionEquiv
                (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo
                  (20 : Fin 24))).1).values
          (alternatingSixUniversalCoverClassRepresentative (15 : Fin 31)) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
            |>.toFiniteCharacterTableCertificate.character
              (alternatingSixFiveCTblLibInvariantSafeRowIdentification
                |>.ambientPositionEquiv (20 : Fin 24)).1).values
          (alternatingSixUniversalCoverClassRepresentative
            (alternatingSixAlphaTwoConjugacyClassPermutation.symm
              (15 : Fin 31)))) := by
  intro hValue
  rw [alternatingSixAlphaTwoConjugacyClassPermutation_symm_fifteen] at hValue
  change
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character
          .atlasTwelvePowerOne).values
        (alternatingSixUniversalCoverClassRepresentative 15) =
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character
            .atlasTwelvePowerTwo).values
        (alternatingSixUniversalCoverClassRepresentative 19)
    at hValue
  rw [alternatingSixCompletedTable_atlasPowerOne_classRepresentative,
    alternatingSixCompletedTable_atlasPowerTwo_classRepresentative] at hValue
  apply alternatingSixAmbientAtlasPowerOneAlpha_ne_powerSevenAlpha
  have hReduced :
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 4 *
          alternatingSixAmbientAtlasTwelvePowerTwoAlpha =
        alternatingSixAmbientAtlasTwelvePowerSevenAlpha := by
    rw [
      alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_four_mul_alpha
    ]
    rfl
  simpa [alternatingSixAmbientAtlas12P1ClassValue,
    alternatingSixAmbientAtlasTwelvePowerTwoClassValue, hReduced] using hValue

/-- Since one exact coordinate fails, the proposed second ambient semantic
bridge is false. -/
theorem
    alternatingSixFiveCTblLibInvariantSafe_not_ambientAlphaTwoBridge :
    ¬(alternatingSixFiveCTblLibInvariantSafeRowIdentification
        |>.AmbientCorrectedAlphaTwoBridge
          alternatingSixAmbientOrdinaryCharacterTableCertificate) := by
  intro hBridge
  apply
    alternatingSixFiveCTblLibInvariantSafe_ambientAlphaTwo_classValueCounterexample
  exact
    (alternatingSixFiveCTblLibInvariantSafeRowIdentification
      |>.ambientAlphaTwoBridge_iff_classValues
        alternatingSixAmbientOrdinaryCharacterTableCertificate).mp
      hBridge (20 : Fin 24) (15 : Fin 31)

end InductiveMcKay
end McKayConjecture
