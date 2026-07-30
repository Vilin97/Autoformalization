/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAutomorphismAction
import McKayConjecture.InductiveMcKay.AlternatingSixCTblLibOuterActionData
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCentralBlockRowMatching
import McKayConjecture.InductiveMcKay.AlternatingSixLocalAutomorphismAction

/-!
# Parameterized semantic CTblLib row identifications for five-local `A₆`

The audited CTblLib five-local data uses twenty-four ambient and
twenty-four local display positions.  Identifying those positions with the
project's constructed ambient and proved actual-normalizer row types is
semantic data, not a consequence of the two finite cardinalities.  This
file therefore makes both identifications explicit parameters.

The audited candidate transports through any proposed pair of position
identifications.  Four further propositions say that the two audited
generator permutations agree with the genuine corrected ambient and local
actions.  Assuming the relevant pair, the finite CTblLib audit proves
intertwining for each generator.

The existing central-block row matching is exhibited only as a possible
coordinate specialization obtained by choosing a suitable local position
equivalence.  No claim is made that this engineered choice is the true
CTblLib row identification.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveParameterizedRowBridgeFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-! ### Corrected genuine local generator actions -/

/-- The genuine action on proved actual-normalizer rows of the first outer
automorphism corrected to stabilize the fixed Sylow five-subgroup. -/
def alternatingSixFiveActualNormalizerCorrectedAlphaOneRowPermutation :
    Equiv.Perm AlternatingSixFiveConcreteNormalizerRow :=
  alternatingSixFiveActualNormalizerRowPermutation
    (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
      (alternatingSixUniversalCoverSylow 5))

/-- The genuine action on proved actual-normalizer rows of the second outer
automorphism corrected to stabilize the fixed Sylow five-subgroup. -/
def alternatingSixFiveActualNormalizerCorrectedAlphaTwoRowPermutation :
    Equiv.Perm AlternatingSixFiveConcreteNormalizerRow :=
  alternatingSixFiveActualNormalizerRowPermutation
    (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
      (alternatingSixUniversalCoverSylow 5))

/-! ### Proposed CT-position identifications -/

/-- Proposed semantic identifications of the twenty-four CTblLib positions
with the project's ambient and actual-normalizer five-prime row types.

This structure contains data only.  It does not assert that either
equivalence is the true CTblLib-to-character identification. -/
structure AlternatingSixFiveCTblLibRowIdentification where
  /-- Proposed identification of ambient CT positions with project ambient
  rows. -/
  ambientPositionEquiv :
    Fin 24 ≃ AlternatingSixAmbientPPrimeRowIndex 5
  /-- Proposed identification of local CT positions with project
  actual-normalizer rows. -/
  localPositionEquiv :
    Fin 24 ≃ AlternatingSixFiveConcreteNormalizerRow

namespace AlternatingSixFiveCTblLibRowIdentification

variable
  (identification : AlternatingSixFiveCTblLibRowIdentification)

/-- Transport the audited five-local candidate through the proposed
ambient and local CT-position identifications. -/
def candidateAmbientLocalRowEquiv :
    AlternatingSixAmbientPPrimeRowIndex 5 ≃
      AlternatingSixFiveConcreteNormalizerRow :=
  identification.ambientPositionEquiv.symm |>.trans
    (alternatingSixCTblLibFivePPrimeActionData.candidate.trans
      identification.localPositionEquiv)

/-- On proposed CT positions, the transported equivalence is exactly the
audited finite candidate. -/
@[simp]
theorem candidateAmbientLocalRowEquiv_ambientPosition
    (i : Fin 24) :
    identification.candidateAmbientLocalRowEquiv
        (identification.ambientPositionEquiv i) =
      identification.localPositionEquiv
        (alternatingSixCTblLibFivePPrimeActionData.candidate i) := by
  simp [candidateAmbientLocalRowEquiv]

/-! ### The four semantic generator-action obligations -/

/-- The corrected first semantic ambient generator agrees with the audited
first ambient permutation under the proposed position identification. -/
def AmbientCorrectedAlphaOneBridge
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Prop :=
  ∀ i : Fin 24,
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
        (alternatingSixUniversalCoverSylow 5)
        (identification.ambientPositionEquiv i) =
      identification.ambientPositionEquiv
        (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne i)

/-- The corrected second semantic ambient generator agrees with the
audited second ambient permutation under the proposed position
identification. -/
def AmbientCorrectedAlphaTwoBridge
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Prop :=
  ∀ i : Fin 24,
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
        (alternatingSixUniversalCoverSylow 5)
        (identification.ambientPositionEquiv i) =
      identification.ambientPositionEquiv
        (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i)

/-- The corrected first semantic local generator agrees with the audited
first local permutation under the proposed position identification. -/
def LocalCorrectedAlphaOneBridge :
    Prop :=
  ∀ i : Fin 24,
    alternatingSixFiveActualNormalizerCorrectedAlphaOneRowPermutation
        (identification.localPositionEquiv i) =
      identification.localPositionEquiv
        (alternatingSixCTblLibFivePPrimeActionData.localAlphaOne i)

/-- The corrected second semantic local generator agrees with the audited
second local permutation under the proposed position identification. -/
def LocalCorrectedAlphaTwoBridge :
    Prop :=
  ∀ i : Fin 24,
    alternatingSixFiveActualNormalizerCorrectedAlphaTwoRowPermutation
        (identification.localPositionEquiv i) =
      identification.localPositionEquiv
        (alternatingSixCTblLibFivePPrimeActionData.localAlphaTwo i)

/-- Bundle the four still-semantic generator-action obligations for a
completed ambient table and proposed position identifications. -/
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

/-- The audited finite theorem conditionally proves intertwining of the
corrected first-generator genuine actions. -/
theorem candidate_intertwines_correctedAlphaOne
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hAmbient : identification.AmbientCorrectedAlphaOneBridge T)
    (hLocal : identification.LocalCorrectedAlphaOneBridge)
    (r : AlternatingSixAmbientPPrimeRowIndex 5) :
    identification.candidateAmbientLocalRowEquiv
        (alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
          (alternatingSixUniversalCoverSylow 5) r) =
      alternatingSixFiveActualNormalizerCorrectedAlphaOneRowPermutation
        (identification.candidateAmbientLocalRowEquiv r) := by
  let i : Fin 24 := identification.ambientPositionEquiv.symm r
  have hr : identification.ambientPositionEquiv i = r :=
    identification.ambientPositionEquiv.apply_symm_apply r
  rw [← hr, hAmbient i]
  rw [
    identification.candidateAmbientLocalRowEquiv_ambientPosition,
    identification.candidateAmbientLocalRowEquiv_ambientPosition,
    hLocal
  ]
  exact congrArg identification.localPositionEquiv
    (alternatingSixCTblLibFive_generatorEquivariant.1 i)

/-- The audited finite theorem conditionally proves intertwining of the
corrected second-generator genuine actions. -/
theorem candidate_intertwines_correctedAlphaTwo
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hAmbient : identification.AmbientCorrectedAlphaTwoBridge T)
    (hLocal : identification.LocalCorrectedAlphaTwoBridge)
    (r : AlternatingSixAmbientPPrimeRowIndex 5) :
    identification.candidateAmbientLocalRowEquiv
        (alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
          (alternatingSixUniversalCoverSylow 5) r) =
      alternatingSixFiveActualNormalizerCorrectedAlphaTwoRowPermutation
        (identification.candidateAmbientLocalRowEquiv r) := by
  let i : Fin 24 := identification.ambientPositionEquiv.symm r
  have hr : identification.ambientPositionEquiv i = r :=
    identification.ambientPositionEquiv.apply_symm_apply r
  rw [← hr, hAmbient i]
  rw [
    identification.candidateAmbientLocalRowEquiv_ambientPosition,
    identification.candidateAmbientLocalRowEquiv_ambientPosition,
    hLocal
  ]
  exact congrArg identification.localPositionEquiv
    (alternatingSixCTblLibFive_generatorEquivariant.2 i)

/-- Bundled bridge data yields both conditional generator-intertwining
statements. -/
theorem candidate_intertwines_generators
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : identification.GeneratorActionBridges T) :
    (∀ r : AlternatingSixAmbientPPrimeRowIndex 5,
      identification.candidateAmbientLocalRowEquiv
          (alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
            (alternatingSixUniversalCoverSylow 5) r) =
        alternatingSixFiveActualNormalizerCorrectedAlphaOneRowPermutation
          (identification.candidateAmbientLocalRowEquiv r)) ∧
      ∀ r : AlternatingSixAmbientPPrimeRowIndex 5,
        identification.candidateAmbientLocalRowEquiv
            (alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
              (alternatingSixUniversalCoverSylow 5) r) =
          alternatingSixFiveActualNormalizerCorrectedAlphaTwoRowPermutation
            (identification.candidateAmbientLocalRowEquiv r) :=
  ⟨identification.candidate_intertwines_correctedAlphaOne T
      h.ambientAlphaOne h.localAlphaOne,
    identification.candidate_intertwines_correctedAlphaTwo T
      h.ambientAlphaTwo h.localAlphaTwo⟩

end AlternatingSixFiveCTblLibRowIdentification

/-! ### The central-block matching as a possible specialization -/

/-- Position data engineered so that transporting the audited candidate
recovers the existing central-block row matching.

The local position equivalence is defined for this algebraic purpose.  This
does not assert that either field gives the true CTblLib row order. -/
def alternatingSixFiveCentralBlockCTblLibRowIdentification :
    AlternatingSixFiveCTblLibRowIdentification where
  ambientPositionEquiv :=
    alternatingSixAmbientFivePPrimeRowIndexEquiv
  localPositionEquiv :=
    alternatingSixCTblLibFivePPrimeActionData.candidate.symm.trans
      (alternatingSixAmbientFivePPrimeRowIndexEquiv.trans
        alternatingSixAmbientFivePPrimeCentralBlockRowEquiv)

/-- Under the deliberately engineered position specialization, the
transported audited candidate is the existing central-block row matching. -/
theorem alternatingSixFiveCentralBlockCTblLibRowIdentification_candidate :
    (alternatingSixFiveCentralBlockCTblLibRowIdentification
      |>.candidateAmbientLocalRowEquiv) =
      alternatingSixAmbientFivePPrimeCentralBlockRowEquiv := by
  apply Equiv.ext
  intro r
  simp [
    AlternatingSixFiveCTblLibRowIdentification.candidateAmbientLocalRowEquiv,
    alternatingSixFiveCentralBlockCTblLibRowIdentification
  ]

end InductiveMcKay
end McKayConjecture
