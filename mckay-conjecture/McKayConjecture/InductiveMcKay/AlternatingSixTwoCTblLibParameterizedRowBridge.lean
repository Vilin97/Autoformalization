/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAutomorphismAction
import McKayConjecture.InductiveMcKay.AlternatingSixCTblLibOuterActionData
import McKayConjecture.InductiveMcKay.AlternatingSixLocalAutomorphismAction
import McKayConjecture.InductiveMcKay.AlternatingSixTwoAmbientRowMatching

/-!
# Parameterized semantic CTblLib row identifications for two-local `A₆`

The audited CTblLib two-local data uses twelve ambient and twelve local
display positions.  Identifying those positions with the project's
constructed ambient and actual-normalizer row types is semantic data, not a
consequence of the two finite cardinalities.  This file therefore makes both
identifications explicit parameters.

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

local instance alternatingSixTwoParameterizedRowBridgeFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-! ### Corrected genuine local generator actions -/

/-- The genuine action on proved actual-normalizer rows of the first outer
automorphism corrected to stabilize the fixed Sylow two-subgroup. -/
def alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation :
    Equiv.Perm AlternatingSixTwoConcreteNormalizerRow :=
  alternatingSixTwoActualNormalizerRowPermutation
    (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
      (alternatingSixUniversalCoverSylow 2))

/-- The genuine action on proved actual-normalizer rows of the second outer
automorphism corrected to stabilize the fixed Sylow two-subgroup. -/
def alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation :
    Equiv.Perm AlternatingSixTwoConcreteNormalizerRow :=
  alternatingSixTwoActualNormalizerRowPermutation
    (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
      (alternatingSixUniversalCoverSylow 2))

/-! ### Proposed CT-position identifications -/

/-- Proposed semantic identifications of the twelve CTblLib positions with
the project's ambient and local two-prime row types.

This structure contains data only.  It does not assert that either
equivalence is the true CTblLib-to-character identification. -/
structure AlternatingSixTwoCTblLibRowIdentification where
  /-- Proposed identification of ambient CT positions with project ambient
  rows. -/
  ambientPositionEquiv :
    Fin 12 ≃ AlternatingSixAmbientPPrimeRowIndex 2
  /-- Proposed identification of local CT positions with project
  actual-normalizer rows. -/
  localPositionEquiv :
    Fin 12 ≃ AlternatingSixTwoConcreteNormalizerRow

namespace AlternatingSixTwoCTblLibRowIdentification

variable
  (identification : AlternatingSixTwoCTblLibRowIdentification)

/-- Transport the audited two-local candidate through the proposed ambient
and local CT-position identifications. -/
def candidateAmbientLocalRowEquiv :
    AlternatingSixAmbientPPrimeRowIndex 2 ≃
      AlternatingSixTwoConcreteNormalizerRow :=
  identification.ambientPositionEquiv.symm |>.trans
    (alternatingSixCTblLibTwoPPrimeActionData.candidate.trans
      identification.localPositionEquiv)

/-- On proposed CT positions, the transported equivalence is exactly the
audited finite candidate. -/
@[simp]
theorem candidateAmbientLocalRowEquiv_ambientPosition
    (i : Fin 12) :
    identification.candidateAmbientLocalRowEquiv
        (identification.ambientPositionEquiv i) =
      identification.localPositionEquiv
        (alternatingSixCTblLibTwoPPrimeActionData.candidate i) := by
  simp [candidateAmbientLocalRowEquiv]

/-! ### The four semantic generator-action obligations -/

/-- The corrected first semantic ambient generator agrees with the audited
first ambient permutation under the proposed position identification. -/
def AmbientCorrectedAlphaOneBridge
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Prop :=
  ∀ i : Fin 12,
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
        (alternatingSixUniversalCoverSylow 2)
        (identification.ambientPositionEquiv i) =
      identification.ambientPositionEquiv
        (alternatingSixCTblLibTwoPPrimeActionData.ambientAlphaOne i)

/-- The corrected second semantic ambient generator agrees with the audited
second ambient permutation under the proposed position identification. -/
def AmbientCorrectedAlphaTwoBridge
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Prop :=
  ∀ i : Fin 12,
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
        (alternatingSixUniversalCoverSylow 2)
        (identification.ambientPositionEquiv i) =
      identification.ambientPositionEquiv
        (alternatingSixCTblLibTwoPPrimeActionData.ambientAlphaTwo i)

/-- The corrected first semantic local generator agrees with the audited
first local permutation under the proposed position identification. -/
def LocalCorrectedAlphaOneBridge :
    Prop :=
  ∀ i : Fin 12,
    alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
        (identification.localPositionEquiv i) =
      identification.localPositionEquiv
        (alternatingSixCTblLibTwoPPrimeActionData.localAlphaOne i)

/-- The corrected second semantic local generator agrees with the audited
second local permutation under the proposed position identification. -/
def LocalCorrectedAlphaTwoBridge :
    Prop :=
  ∀ i : Fin 12,
    alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
        (identification.localPositionEquiv i) =
      identification.localPositionEquiv
        (alternatingSixCTblLibTwoPPrimeActionData.localAlphaTwo i)

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
    (r : AlternatingSixAmbientPPrimeRowIndex 2) :
    identification.candidateAmbientLocalRowEquiv
        (alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
          (alternatingSixUniversalCoverSylow 2) r) =
      alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
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
    (alternatingSixCTblLibTwo_generatorEquivariant.1 i)

/-- The audited finite theorem conditionally proves intertwining of the
corrected second-generator genuine actions. -/
theorem candidate_intertwines_correctedAlphaTwo
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hAmbient : identification.AmbientCorrectedAlphaTwoBridge T)
    (hLocal : identification.LocalCorrectedAlphaTwoBridge)
    (r : AlternatingSixAmbientPPrimeRowIndex 2) :
    identification.candidateAmbientLocalRowEquiv
        (alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
          (alternatingSixUniversalCoverSylow 2) r) =
      alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
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
    (alternatingSixCTblLibTwo_generatorEquivariant.2 i)

/-- Bundled bridge data yields both conditional generator-intertwining
statements. -/
theorem candidate_intertwines_generators
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : identification.GeneratorActionBridges T) :
    (∀ r : AlternatingSixAmbientPPrimeRowIndex 2,
      identification.candidateAmbientLocalRowEquiv
          (alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
            (alternatingSixUniversalCoverSylow 2) r) =
        alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
          (identification.candidateAmbientLocalRowEquiv r)) ∧
      ∀ r : AlternatingSixAmbientPPrimeRowIndex 2,
        identification.candidateAmbientLocalRowEquiv
            (alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
              (alternatingSixUniversalCoverSylow 2) r) =
          alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
            (identification.candidateAmbientLocalRowEquiv r) :=
  ⟨identification.candidate_intertwines_correctedAlphaOne T
      h.ambientAlphaOne h.localAlphaOne,
    identification.candidate_intertwines_correctedAlphaTwo T
      h.ambientAlphaTwo h.localAlphaTwo⟩

end AlternatingSixTwoCTblLibRowIdentification

/-! ### The central-block matching as a possible specialization -/

/-- Position data engineered so that transporting the audited candidate
recovers the existing central-block row matching.

The local position equivalence is defined for this algebraic purpose.  This
does not assert that either field gives the true CTblLib row order. -/
def alternatingSixTwoCentralBlockCTblLibRowIdentification :
    AlternatingSixTwoCTblLibRowIdentification where
  ambientPositionEquiv :=
    alternatingSixAmbientTwoPPrimeRowIndexEquiv
  localPositionEquiv :=
    alternatingSixCTblLibTwoPPrimeActionData.candidate.symm.trans
      (alternatingSixAmbientTwoPPrimeRowIndexEquiv.trans
        alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow)

/-- Under the deliberately engineered position specialization, the
transported audited candidate is the existing central-block row matching. -/
theorem alternatingSixTwoCentralBlockCTblLibRowIdentification_candidate :
    (alternatingSixTwoCentralBlockCTblLibRowIdentification
      |>.candidateAmbientLocalRowEquiv) =
      alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow := by
  apply Equiv.ext
  intro r
  simp [
    AlternatingSixTwoCTblLibRowIdentification.candidateAmbientLocalRowEquiv,
    alternatingSixTwoCentralBlockCTblLibRowIdentification
  ]

end InductiveMcKay
end McKayConjecture
