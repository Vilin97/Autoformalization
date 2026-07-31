/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientPPrimeOuterRowActionCompatibility
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCTblLibCorrectedRowIdentification

/-!
# Completed corrected ambient CTblLib bridges at five for `6.A₆`

The corrected five-local ambient position order was previously reduced to
ten unresolved positions for each audited outer generator.  The completed
named-row actions identify the semantic permutations on all ordinary rows.
Transporting those actions through the generic prime-to-`p` compatibility
theorems discharges both residual seams.

These results concern only the ambient character rows.  The corresponding
local row identifications and the projective comparison data remain separate
obligations.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveCorrectedAmbientBridgesFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The corrected five-local ambient order intertwines the first audited
outer generator on all twenty-four prime-to-five rows. -/
theorem alternatingSixFiveCTblLibCorrected_ambientAlphaOneBridge :
    alternatingSixFiveCTblLibCorrectedRowIdentification
      |>.AmbientCorrectedAlphaOneBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate := by
  rw [
    alternatingSixFiveCTblLibCorrected_ambientAlphaOneBridge_iff_tenRemaining
  ]
  intro i hi
  rw [
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq_canonical
  ]
  fin_cases i <;>
    simp_all [
      AlternatingSixFiveCorrectedAlphaOneRemainingAmbientPosition,
      alternatingSixFiveCTblLibCorrectedRowIdentification,
      alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv,
      alternatingSixFiveCTblLibCorrectedAmbientPosition,
      alternatingSixCTblLibFivePPrimeActionData,
      alternatingSixAmbientAlphaOnePPrimeRowAction,
      alternatingSixAmbientAlphaOneOrdinaryRowAction
    ]

/-- The corrected five-local ambient order intertwines the second audited
outer generator on all twenty-four prime-to-five rows. -/
theorem alternatingSixFiveCTblLibCorrected_ambientAlphaTwoBridge :
    alternatingSixFiveCTblLibCorrectedRowIdentification
      |>.AmbientCorrectedAlphaTwoBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate := by
  rw [
    alternatingSixFiveCTblLibCorrected_ambientAlphaTwoBridge_iff_tenRemaining
  ]
  intro i hi
  rw [
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq_canonical
  ]
  fin_cases i <;>
    simp_all [
      AlternatingSixFiveCorrectedAlphaTwoRemainingAmbientPosition,
      alternatingSixFiveCTblLibCorrectedRowIdentification,
      alternatingSixFiveCTblLibCorrectedAmbientPositionEquiv,
      alternatingSixFiveCTblLibCorrectedAmbientPosition,
      alternatingSixCTblLibFivePPrimeActionData,
      alternatingSixAmbientAlphaTwoPPrimeRowAction,
      alternatingSixAmbientAlphaTwoOrdinaryRowAction
    ]

/-- Since both ambient bridges are complete, the full five-local
generator-action package is equivalent to supplying only the two genuine
local generator bridges. -/
theorem
    alternatingSixFiveCTblLibCorrected_generatorActionBridges_iff_localBridges :
    (alternatingSixFiveCTblLibCorrectedRowIdentification
        |>.GeneratorActionBridges
          alternatingSixAmbientOrdinaryCharacterTableCertificate) ↔
      (alternatingSixFiveCTblLibCorrectedRowIdentification
          |>.LocalCorrectedAlphaOneBridge) ∧
        (alternatingSixFiveCTblLibCorrectedRowIdentification
          |>.LocalCorrectedAlphaTwoBridge) := by
  constructor
  · intro h
    exact ⟨h.localAlphaOne, h.localAlphaTwo⟩
  · rintro ⟨hOne, hTwo⟩
    exact {
      ambientAlphaOne :=
        alternatingSixFiveCTblLibCorrected_ambientAlphaOneBridge
      ambientAlphaTwo :=
        alternatingSixFiveCTblLibCorrected_ambientAlphaTwoBridge
      localAlphaOne := hOne
      localAlphaTwo := hTwo
    }

end InductiveMcKay
end McKayConjecture
