/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientPPrimeOuterRowActionCompatibility
import McKayConjecture.InductiveMcKay.AlternatingSixTwoCTblLibCorrectedLocalRowIdentification

/-!
# Corrected two-local CTblLib row identification for `6.A₆`

The invariant-safe ambient order and the corrected local order together give
one coherent proposed identification of the twelve CTblLib positions.  The
completed named-row calculations prove both ambient generator bridges
unconditionally.  On the local side, the existing semantic analysis reduces
the two full bridges to three seed equations apiece.

This file packages that exact boundary: the bundled generator-action bridge
is equivalent to the six local seed equations.  It does not assert those
remaining equations.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixTwoCorrectedRowIdentificationFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The invariant-safe ambient order paired with the corrected semantic local
order at `p = 2`. -/
def alternatingSixTwoCTblLibCorrectedRowIdentification :
    AlternatingSixTwoCTblLibRowIdentification where
  ambientPositionEquiv :=
    alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv
  localPositionEquiv :=
    alternatingSixTwoCTblLibCorrectedLocalPositionEquiv

/-- The corrected two-local ambient order intertwines the first audited outer
generator on all twelve prime-to-two rows. -/
theorem alternatingSixTwoCTblLibCorrected_ambientAlphaOneBridge :
    alternatingSixTwoCTblLibCorrectedRowIdentification
      |>.AmbientCorrectedAlphaOneBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate := by
  intro i
  rw [
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq_canonical
  ]
  apply Subtype.ext
  fin_cases i <;> rfl

/-- The corrected two-local ambient order intertwines the second audited outer
generator on all twelve prime-to-two rows. -/
theorem alternatingSixTwoCTblLibCorrected_ambientAlphaTwoBridge :
    alternatingSixTwoCTblLibCorrectedRowIdentification
      |>.AmbientCorrectedAlphaTwoBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate := by
  intro i
  rw [
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq_canonical
  ]
  apply Subtype.ext
  fin_cases i <;> rfl

/-- The corrected first local generator bridge is exactly its three remaining
semantic seed equations. -/
theorem alternatingSixTwoCTblLibCorrected_localAlphaOneBridge_iff_seeds :
    (alternatingSixTwoCTblLibCorrectedRowIdentification
      |>.LocalCorrectedAlphaOneBridge) ↔
      AlternatingSixTwoCorrectedLocalAlphaOneSeedEquations := by
  simpa [
    alternatingSixTwoCTblLibCorrectedRowIdentification,
    AlternatingSixTwoCTblLibRowIdentification.LocalCorrectedAlphaOneBridge,
    AlternatingSixTwoCTblLibCorrectedLocalAlphaOneBridge
  ] using alternatingSixTwoCTblLibCorrectedLocalAlphaOneBridge_iff_seeds

/-- The corrected second local generator bridge is exactly its three remaining
semantic seed equations. -/
theorem alternatingSixTwoCTblLibCorrected_localAlphaTwoBridge_iff_seeds :
    (alternatingSixTwoCTblLibCorrectedRowIdentification
      |>.LocalCorrectedAlphaTwoBridge) ↔
      AlternatingSixTwoCorrectedLocalAlphaTwoSeedEquations := by
  simpa [
    alternatingSixTwoCTblLibCorrectedRowIdentification,
    AlternatingSixTwoCTblLibRowIdentification.LocalCorrectedAlphaTwoBridge,
    AlternatingSixTwoCTblLibCorrectedLocalAlphaTwoBridge
  ] using alternatingSixTwoCTblLibCorrectedLocalAlphaTwoBridge_iff_seeds

/-- Since the two ambient bridges are complete, the bundled two-local bridge
is equivalent to its two local components. -/
theorem
    alternatingSixTwoCTblLibCorrected_generatorActionBridges_iff_localBridges :
    (alternatingSixTwoCTblLibCorrectedRowIdentification
        |>.GeneratorActionBridges
          alternatingSixAmbientOrdinaryCharacterTableCertificate) ↔
      (AlternatingSixTwoCTblLibCorrectedLocalAlphaOneBridge ∧
        AlternatingSixTwoCTblLibCorrectedLocalAlphaTwoBridge) := by
  constructor
  · intro h
    exact ⟨h.localAlphaOne, h.localAlphaTwo⟩
  · rintro ⟨hOne, hTwo⟩
    exact {
      ambientAlphaOne :=
        alternatingSixTwoCTblLibCorrected_ambientAlphaOneBridge
      ambientAlphaTwo :=
        alternatingSixTwoCTblLibCorrected_ambientAlphaTwoBridge
      localAlphaOne := hOne
      localAlphaTwo := hTwo
    }

/-- The entire corrected two-local generator-action package is equivalent to
the three first-generator and three second-generator local seed equations. -/
theorem
    alternatingSixTwoCTblLibCorrected_generatorActionBridges_iff_sixSeeds :
    (alternatingSixTwoCTblLibCorrectedRowIdentification
        |>.GeneratorActionBridges
          alternatingSixAmbientOrdinaryCharacterTableCertificate) ↔
      (AlternatingSixTwoCorrectedLocalAlphaOneSeedEquations ∧
        AlternatingSixTwoCorrectedLocalAlphaTwoSeedEquations) := by
  rw [
    alternatingSixTwoCTblLibCorrected_generatorActionBridges_iff_localBridges,
    alternatingSixTwoCTblLibCorrectedLocalBridges_iff_sixSeeds
  ]

end InductiveMcKay
end McKayConjecture
