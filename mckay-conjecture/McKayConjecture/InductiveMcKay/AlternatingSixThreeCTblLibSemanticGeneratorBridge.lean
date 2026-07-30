/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAutomorphismAction
import McKayConjecture.InductiveMcKay.AlternatingSixLocalAutomorphismAction
import McKayConjecture.InductiveMcKay.AlternatingSixThreeCTblLibCandidateRowBridge

/-!
# Conditional semantic bridge for the three-local CTblLib candidate

The CTblLib audit proves that its candidate permutation intertwines two
finite generator permutations.  To transfer those two finite equations to
the genuine character actions, one must still identify each audited
generator permutation with the corresponding semantic row permutation.

This file states those four identification obligations exactly: one
ambient and one local obligation for each inner-corrected outer
automorphism.  Assuming the relevant pair, the audited finite calculation
proves equivariance of the candidate for that corrected generator.

No generation statement for the full Sylow automorphism stabilizer is used
or asserted here, so these results do not prove full candidate
equivariance.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixThreeSemanticGeneratorBridgeFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-! ### Corrected semantic local generators -/

/-- The genuine action on the proved local rows of the first outer
automorphism after correcting it to stabilize the chosen Sylow
three-subgroup. -/
def alternatingSixThreeActualNormalizerCorrectedAlphaOneRowPermutation :
    Equiv.Perm AlternatingSixThreeConcreteNormalizerRow :=
  alternatingSixThreeActualNormalizerRowPermutation
    (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
      (alternatingSixUniversalCoverSylow 3))

/-- The genuine action on the proved local rows of the second outer
automorphism after correcting it to stabilize the chosen Sylow
three-subgroup. -/
def alternatingSixThreeActualNormalizerCorrectedAlphaTwoRowPermutation :
    Equiv.Perm AlternatingSixThreeConcreteNormalizerRow :=
  alternatingSixThreeActualNormalizerRowPermutation
    (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
      (alternatingSixUniversalCoverSylow 3))

/-! ### The four semantic-to-CTblLib bridge obligations -/

/-- The exact assertion that the corrected first ambient semantic
generator has the audited CTblLib action in the recorded ambient
`Fin 12` enumeration. -/
def AlternatingSixThreeAmbientCorrectedAlphaOneCTblLibBridge
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Prop :=
  ∀ i : Fin 12,
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
        (alternatingSixUniversalCoverSylow 3)
        (alternatingSixAmbientThreePPrimeRowIndexEquiv i) =
      alternatingSixAmbientThreePPrimeRowIndexEquiv
        (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne i)

/-- The exact assertion that the corrected second ambient semantic
generator has the audited CTblLib action in the recorded ambient
`Fin 12` enumeration. -/
def AlternatingSixThreeAmbientCorrectedAlphaTwoCTblLibBridge
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Prop :=
  ∀ i : Fin 12,
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
        (alternatingSixUniversalCoverSylow 3)
        (alternatingSixAmbientThreePPrimeRowIndexEquiv i) =
      alternatingSixAmbientThreePPrimeRowIndexEquiv
        (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaTwo i)

/-- The exact assertion that the corrected first local semantic generator
has the audited CTblLib action in the recorded local `Fin 12`
enumeration. -/
def AlternatingSixThreeLocalCorrectedAlphaOneCTblLibBridge :
    Prop :=
  ∀ i : Fin 12,
    alternatingSixThreeActualNormalizerCorrectedAlphaOneRowPermutation
        (alternatingSixThreeConcreteNormalizerRowIndexEquiv i) =
      alternatingSixThreeConcreteNormalizerRowIndexEquiv
        (alternatingSixCTblLibThreePPrimeActionData.localAlphaOne i)

/-- The exact assertion that the corrected second local semantic generator
has the audited CTblLib action in the recorded local `Fin 12`
enumeration. -/
def AlternatingSixThreeLocalCorrectedAlphaTwoCTblLibBridge :
    Prop :=
  ∀ i : Fin 12,
    alternatingSixThreeActualNormalizerCorrectedAlphaTwoRowPermutation
        (alternatingSixThreeConcreteNormalizerRowIndexEquiv i) =
      alternatingSixThreeConcreteNormalizerRowIndexEquiv
        (alternatingSixCTblLibThreePPrimeActionData.localAlphaTwo i)

/-! ### Conditional generator equivariance of the audited candidate -/

/-- Once the two semantic bridge obligations for `alpha₁` are supplied,
the audited candidate intertwines the corresponding corrected genuine
ambient and local row permutations. -/
theorem
    alternatingSixThreeCTblLibCandidate_intertwines_correctedAlphaOne
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hAmbient :
      AlternatingSixThreeAmbientCorrectedAlphaOneCTblLibBridge T)
    (hLocal :
      AlternatingSixThreeLocalCorrectedAlphaOneCTblLibBridge)
    (r : AlternatingSixAmbientPPrimeRowIndex 3) :
    alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv
        (alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
          (alternatingSixUniversalCoverSylow 3) r) =
      alternatingSixThreeActualNormalizerCorrectedAlphaOneRowPermutation
        (alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv r) := by
  let i : Fin 12 :=
    alternatingSixAmbientThreePPrimeRowIndexEquiv.symm r
  have hr :
      alternatingSixAmbientThreePPrimeRowIndexEquiv i = r :=
    alternatingSixAmbientThreePPrimeRowIndexEquiv.apply_symm_apply r
  rw [← hr, hAmbient i]
  rw [
    alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv_ordered,
    alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv_ordered,
    hLocal
  ]
  exact congrArg alternatingSixThreeConcreteNormalizerRowIndexEquiv
    (alternatingSixCTblLibThree_generatorEquivariant.1 i)

/-- Once the two semantic bridge obligations for `alpha₂` are supplied,
the audited candidate intertwines the corresponding corrected genuine
ambient and local row permutations. -/
theorem
    alternatingSixThreeCTblLibCandidate_intertwines_correctedAlphaTwo
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hAmbient :
      AlternatingSixThreeAmbientCorrectedAlphaTwoCTblLibBridge T)
    (hLocal :
      AlternatingSixThreeLocalCorrectedAlphaTwoCTblLibBridge)
    (r : AlternatingSixAmbientPPrimeRowIndex 3) :
    alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv
        (alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
          (alternatingSixUniversalCoverSylow 3) r) =
      alternatingSixThreeActualNormalizerCorrectedAlphaTwoRowPermutation
        (alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv r) := by
  let i : Fin 12 :=
    alternatingSixAmbientThreePPrimeRowIndexEquiv.symm r
  have hr :
      alternatingSixAmbientThreePPrimeRowIndexEquiv i = r :=
    alternatingSixAmbientThreePPrimeRowIndexEquiv.apply_symm_apply r
  rw [← hr, hAmbient i]
  rw [
    alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv_ordered,
    alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv_ordered,
    hLocal
  ]
  exact congrArg alternatingSixThreeConcreteNormalizerRowIndexEquiv
    (alternatingSixCTblLibThree_generatorEquivariant.2 i)

end InductiveMcKay
end McKayConjecture
