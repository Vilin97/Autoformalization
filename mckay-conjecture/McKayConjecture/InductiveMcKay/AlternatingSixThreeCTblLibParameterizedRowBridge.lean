/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixThreeCTblLibSemanticGeneratorBridge

/-!
# Parameterized semantic CTblLib row identifications for three-local `A₆`

The audited CTblLib data is indexed by `Fin 12`, whereas the project uses
constructed ambient and local character-row types.  Relating those worlds
requires two semantic identifications of CTblLib positions with project
rows.  This file makes those identifications explicit parameters.

Given such parameters, the audited CTblLib candidate transports to an
ambient-to-local row equivalence.  Four further propositions state exactly
that the two audited finite generator actions agree with the corresponding
semantic ambient and local actions.  The audited finite intertwining theorem
then proves conditional equivariance for each generator.

The recorded project enumerations provide one specialization of this
parameterized layer.  Nothing here proves that any supplied equivalence is
the true CTblLib-to-character identification, and no generation statement
for the full Sylow stabilizer is asserted.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixThreeParameterizedRowBridgeFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- Proposed semantic identifications of the twelve CTblLib positions with
the project's ambient and local three-prime row types.

This structure carries identification data; inhabiting it does not assert
that either equivalence agrees with CTblLib semantics. -/
structure AlternatingSixThreeCTblLibRowIdentification where
  /-- Proposed identification of CTblLib ambient positions with project
  ambient rows. -/
  ambientPositionEquiv :
    Fin 12 ≃ AlternatingSixAmbientPPrimeRowIndex 3
  /-- Proposed identification of CTblLib local positions with project local
  rows. -/
  localPositionEquiv :
    Fin 12 ≃ AlternatingSixThreeConcreteNormalizerRow

namespace AlternatingSixThreeCTblLibRowIdentification

variable
  (identification : AlternatingSixThreeCTblLibRowIdentification)

/-- Transport the audited finite candidate through the proposed ambient and
local CT-position identifications. -/
def candidateAmbientLocalRowEquiv :
    AlternatingSixAmbientPPrimeRowIndex 3 ≃
      AlternatingSixThreeConcreteNormalizerRow :=
  identification.ambientPositionEquiv.symm |>.trans
    (alternatingSixCTblLibThreePPrimeActionData.candidate.trans
      identification.localPositionEquiv)

/-- On proposed CT positions, the transported equivalence is exactly the
audited finite candidate. -/
@[simp]
theorem candidateAmbientLocalRowEquiv_ambientPosition
    (i : Fin 12) :
    identification.candidateAmbientLocalRowEquiv
        (identification.ambientPositionEquiv i) =
      identification.localPositionEquiv
        (alternatingSixCTblLibThreePPrimeActionData.candidate i) := by
  simp [candidateAmbientLocalRowEquiv]

/-! ### The four semantic generator-action obligations -/

/-- The corrected first semantic ambient generator agrees with the audited
first ambient permutation under the proposed position identification. -/
def AmbientCorrectedAlphaOneBridge
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Prop :=
  ∀ i : Fin 12,
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
        (alternatingSixUniversalCoverSylow 3)
        (identification.ambientPositionEquiv i) =
      identification.ambientPositionEquiv
        (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne i)

/-- The corrected second semantic ambient generator agrees with the audited
second ambient permutation under the proposed position identification. -/
def AmbientCorrectedAlphaTwoBridge
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Prop :=
  ∀ i : Fin 12,
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
        (alternatingSixUniversalCoverSylow 3)
        (identification.ambientPositionEquiv i) =
      identification.ambientPositionEquiv
        (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaTwo i)

/-- The corrected first semantic local generator agrees with the audited
first local permutation under the proposed position identification. -/
def LocalCorrectedAlphaOneBridge :
    Prop :=
  ∀ i : Fin 12,
    alternatingSixThreeActualNormalizerCorrectedAlphaOneRowPermutation
        (identification.localPositionEquiv i) =
      identification.localPositionEquiv
        (alternatingSixCTblLibThreePPrimeActionData.localAlphaOne i)

/-- The corrected second semantic local generator agrees with the audited
second local permutation under the proposed position identification. -/
def LocalCorrectedAlphaTwoBridge :
    Prop :=
  ∀ i : Fin 12,
    alternatingSixThreeActualNormalizerCorrectedAlphaTwoRowPermutation
        (identification.localPositionEquiv i) =
      identification.localPositionEquiv
        (alternatingSixCTblLibThreePPrimeActionData.localAlphaTwo i)

/-- Bundle the four still-semantic generator-action obligations for a
completed ambient table and a proposed pair of CT-position
identifications. -/
structure GeneratorActionBridges
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Prop where
  ambientAlphaOne :
    identification.AmbientCorrectedAlphaOneBridge T
  ambientAlphaTwo :
    identification.AmbientCorrectedAlphaTwoBridge T
  localAlphaOne :
    identification.LocalCorrectedAlphaOneBridge
  localAlphaTwo :
    identification.LocalCorrectedAlphaTwoBridge

/-! ### Conditional finite-to-semantic transport -/

/-- The audited finite theorem proves that the transported candidate
intertwines the two corrected first-generator semantic actions, conditional
on the corresponding ambient and local bridge obligations. -/
theorem candidate_intertwines_correctedAlphaOne
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hAmbient : identification.AmbientCorrectedAlphaOneBridge T)
    (hLocal : identification.LocalCorrectedAlphaOneBridge)
    (r : AlternatingSixAmbientPPrimeRowIndex 3) :
    identification.candidateAmbientLocalRowEquiv
        (alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
          (alternatingSixUniversalCoverSylow 3) r) =
      alternatingSixThreeActualNormalizerCorrectedAlphaOneRowPermutation
        (identification.candidateAmbientLocalRowEquiv r) := by
  let i : Fin 12 := identification.ambientPositionEquiv.symm r
  have hr : identification.ambientPositionEquiv i = r :=
    identification.ambientPositionEquiv.apply_symm_apply r
  rw [← hr, hAmbient i]
  rw [
    identification.candidateAmbientLocalRowEquiv_ambientPosition,
    identification.candidateAmbientLocalRowEquiv_ambientPosition,
    hLocal
  ]
  exact congrArg identification.localPositionEquiv
    (alternatingSixCTblLibThree_generatorEquivariant.1 i)

/-- The audited finite theorem proves that the transported candidate
intertwines the two corrected second-generator semantic actions,
conditional on the corresponding ambient and local bridge obligations. -/
theorem candidate_intertwines_correctedAlphaTwo
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hAmbient : identification.AmbientCorrectedAlphaTwoBridge T)
    (hLocal : identification.LocalCorrectedAlphaTwoBridge)
    (r : AlternatingSixAmbientPPrimeRowIndex 3) :
    identification.candidateAmbientLocalRowEquiv
        (alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
          (alternatingSixUniversalCoverSylow 3) r) =
      alternatingSixThreeActualNormalizerCorrectedAlphaTwoRowPermutation
        (identification.candidateAmbientLocalRowEquiv r) := by
  let i : Fin 12 := identification.ambientPositionEquiv.symm r
  have hr : identification.ambientPositionEquiv i = r :=
    identification.ambientPositionEquiv.apply_symm_apply r
  rw [← hr, hAmbient i]
  rw [
    identification.candidateAmbientLocalRowEquiv_ambientPosition,
    identification.candidateAmbientLocalRowEquiv_ambientPosition,
    hLocal
  ]
  exact congrArg identification.localPositionEquiv
    (alternatingSixCTblLibThree_generatorEquivariant.2 i)

/-- A bundled set of four bridge obligations yields both conditional
generator-intertwining statements. -/
theorem candidate_intertwines_generators
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : identification.GeneratorActionBridges T) :
    (∀ r : AlternatingSixAmbientPPrimeRowIndex 3,
      identification.candidateAmbientLocalRowEquiv
          (alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
            (alternatingSixUniversalCoverSylow 3) r) =
        alternatingSixThreeActualNormalizerCorrectedAlphaOneRowPermutation
          (identification.candidateAmbientLocalRowEquiv r)) ∧
      ∀ r : AlternatingSixAmbientPPrimeRowIndex 3,
        identification.candidateAmbientLocalRowEquiv
            (alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
              (alternatingSixUniversalCoverSylow 3) r) =
          alternatingSixThreeActualNormalizerCorrectedAlphaTwoRowPermutation
            (identification.candidateAmbientLocalRowEquiv r) :=
  ⟨identification.candidate_intertwines_correctedAlphaOne T
      h.ambientAlphaOne h.localAlphaOne,
    identification.candidate_intertwines_correctedAlphaTwo T
      h.ambientAlphaTwo h.localAlphaTwo⟩

end AlternatingSixThreeCTblLibRowIdentification

/-! ### Specialization to the recorded project enumerations -/

/-- The current project display enumerations, regarded only as one proposed
pair of CT-position identifications. -/
def alternatingSixThreeRecordedCTblLibRowIdentification :
    AlternatingSixThreeCTblLibRowIdentification where
  ambientPositionEquiv :=
    alternatingSixAmbientThreePPrimeRowIndexEquiv
  localPositionEquiv :=
    alternatingSixThreeConcreteNormalizerRowIndexEquiv

/-- With the recorded project enumerations as parameters, the transported
candidate is the previously defined recorded-enumeration candidate. -/
@[simp]
theorem
    alternatingSixThreeRecordedCTblLibRowIdentification_candidateEquiv :
    (alternatingSixThreeRecordedCTblLibRowIdentification
      |>.candidateAmbientLocalRowEquiv) =
      alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv :=
  rfl

/-- The parameterized first ambient bridge specializes to the existing
recorded-enumeration obligation. -/
theorem alternatingSixThreeRecorded_ambientAlphaOneBridge_iff
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    (alternatingSixThreeRecordedCTblLibRowIdentification
      |>.AmbientCorrectedAlphaOneBridge T) ↔
      AlternatingSixThreeAmbientCorrectedAlphaOneCTblLibBridge T :=
  Iff.rfl

/-- The parameterized second ambient bridge specializes to the existing
recorded-enumeration obligation. -/
theorem alternatingSixThreeRecorded_ambientAlphaTwoBridge_iff
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    (alternatingSixThreeRecordedCTblLibRowIdentification
      |>.AmbientCorrectedAlphaTwoBridge T) ↔
      AlternatingSixThreeAmbientCorrectedAlphaTwoCTblLibBridge T :=
  Iff.rfl

/-- The parameterized first local bridge specializes to the existing
recorded-enumeration obligation. -/
theorem alternatingSixThreeRecorded_localAlphaOneBridge_iff :
    (alternatingSixThreeRecordedCTblLibRowIdentification
      |>.LocalCorrectedAlphaOneBridge) ↔
      AlternatingSixThreeLocalCorrectedAlphaOneCTblLibBridge :=
  Iff.rfl

/-- The parameterized second local bridge specializes to the existing
recorded-enumeration obligation. -/
theorem alternatingSixThreeRecorded_localAlphaTwoBridge_iff :
    (alternatingSixThreeRecordedCTblLibRowIdentification
      |>.LocalCorrectedAlphaTwoBridge) ↔
      AlternatingSixThreeLocalCorrectedAlphaTwoCTblLibBridge :=
  Iff.rfl

end InductiveMcKay
end McKayConjecture
