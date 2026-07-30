/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixThreeCTblLibSemanticGeneratorBridge
import McKayConjecture.InductiveMcKay.NormalizerInnerAutomorphismStabilizer

/-!
# Reduction of three-local CTblLib equivariance to stabilizer generation

The genuine ambient and local row actions are group homomorphisms into
permutation groups.  After transporting the ambient action through the
audited CTblLib candidate, their equalizer is therefore a subgroup of the
Sylow automorphism stabilizer.

The inner image of the Sylow normalizer lies in this equalizer
unconditionally.  The two corrected outer generators lie in it under the
four semantic CTblLib bridge obligations.  Thus an explicit hypothesis that
these three pieces generate the full stabilizer yields full candidate
equivariance.

The generation hypothesis is only defined here; it is not asserted.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixThreeFullEquivarianceReductionFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-! ### The equalizer subgroup of semantic row actions -/

/-- The genuine action of the Sylow automorphism stabilizer on the
arithmetic ambient prime-to-three rows. -/
def alternatingSixThreeAmbientSemanticRowPermutationHom
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3) →*
      Equiv.Perm (AlternatingSixAmbientPPrimeRowIndex 3) where
  toFun a :=
    alternatingSixAmbientPPrimeRowPermutation T 3
      (a : MulAut AlternatingSixUniversalCover)
  map_one' :=
    alternatingSixAmbientPPrimeRowPermutation_one T 3
  map_mul' a b :=
    alternatingSixAmbientPPrimeRowPermutation_mul T 3
      (a : MulAut AlternatingSixUniversalCover)
      (b : MulAut AlternatingSixUniversalCover)

/-- The genuine restricted action of the Sylow automorphism stabilizer on
the proved actual-normalizer prime-to-three rows. -/
def alternatingSixThreeLocalSemanticRowPermutationHom :
    SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3) →*
      Equiv.Perm AlternatingSixThreeConcreteNormalizerRow where
  toFun a :=
    alternatingSixThreeActualNormalizerRowPermutation a
  map_one' :=
    normalizerPPrimeRowPermutation_one
      (alternatingSixUniversalCoverSylow 3)
      AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
  map_mul' a b :=
    normalizerPPrimeRowPermutation_mul
      (alternatingSixUniversalCoverSylow 3)
      AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
      a b

/-- Transport the genuine ambient row action through the audited CTblLib
candidate, producing a permutation action on the local row type. -/
def alternatingSixThreeCTblLibCandidateTransportedAmbientRowPermutationHom
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3) →*
      Equiv.Perm AlternatingSixThreeConcreteNormalizerRow :=
  alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv.permCongrHom.toMonoidHom.comp
    (alternatingSixThreeAmbientSemanticRowPermutationHom T)

/-- The subgroup on which the audited candidate intertwines the two
genuine semantic row actions. -/
def alternatingSixThreeCTblLibCandidateEquivarianceSubgroup
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Subgroup
      (SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3)) :=
  MonoidHom.eqLocus
    (alternatingSixThreeCTblLibCandidateTransportedAmbientRowPermutationHom
      T)
    alternatingSixThreeLocalSemanticRowPermutationHom

/-- Pointwise form of membership in the candidate-equivariance
equalizer. -/
theorem
    alternatingSixThreeCTblLibCandidateEquivarianceSubgroup_mem_iff
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3)) :
    a ∈ alternatingSixThreeCTblLibCandidateEquivarianceSubgroup T ↔
      ∀ r : AlternatingSixAmbientPPrimeRowIndex 3,
        alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv
            (alternatingSixAmbientPPrimeRowPermutation T 3
              (a : MulAut AlternatingSixUniversalCover) r) =
          alternatingSixThreeActualNormalizerRowPermutation a
            (alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv r) := by
  constructor
  · intro ha r
    have hperm :
        alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv.permCongr
            (alternatingSixAmbientPPrimeRowPermutation T 3
              (a : MulAut AlternatingSixUniversalCover)) =
          alternatingSixThreeActualNormalizerRowPermutation a := by
      exact ha
    have hr :=
      Equiv.congr_fun hperm
        (alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv r)
    simpa only [
      Equiv.permCongr_apply,
      Equiv.symm_apply_apply
    ] using hr
  · intro h
    change
      alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv.permCongr
          (alternatingSixAmbientPPrimeRowPermutation T 3
            (a : MulAut AlternatingSixUniversalCover)) =
        alternatingSixThreeActualNormalizerRowPermutation a
    apply Equiv.ext
    intro s
    have hs :=
      h
        (alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv.symm s)
    simpa only [
      Equiv.permCongr_apply,
      Equiv.apply_symm_apply
    ] using hs

/-! ### The explicit missing generation statement -/

/-- The exact group-theoretic hypothesis still needed for the three-local
full-equivariance reduction: the inner normalizer image together with the
two corrected audited outer automorphisms generates the full Sylow
automorphism stabilizer. -/
def AlternatingSixThreeSylowAutStabilizerGenerationHypothesis :
    Prop :=
  (SylowAutStabilizer.normalizerInnerHom
      (alternatingSixUniversalCoverSylow 3)).range ⊔
    Subgroup.closure
      {alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
          (alternatingSixUniversalCoverSylow 3),
        alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
          (alternatingSixUniversalCoverSylow 3)} =
    ⊤

/-! ### Full equivariance, conditional on generation and the four bridges -/

/-- The explicit generation hypothesis and the four semantic CTblLib
generator bridges imply full equivariance of the audited candidate.

This theorem does not prove or assume any stronger classification of the
Sylow automorphism stabilizer than the displayed generation proposition. -/
theorem alternatingSixThreeCTblLibCandidateEquivariant_of_generation
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hGeneration :
      AlternatingSixThreeSylowAutStabilizerGenerationHypothesis)
    (hAmbientAlphaOne :
      AlternatingSixThreeAmbientCorrectedAlphaOneCTblLibBridge T)
    (hAmbientAlphaTwo :
      AlternatingSixThreeAmbientCorrectedAlphaTwoCTblLibBridge T)
    (hLocalAlphaOne :
      AlternatingSixThreeLocalCorrectedAlphaOneCTblLibBridge)
    (hLocalAlphaTwo :
      AlternatingSixThreeLocalCorrectedAlphaTwoCTblLibBridge) :
    AlternatingSixThreeCTblLibCandidateEquivariant T := by
  let P : Sylow 3 AlternatingSixUniversalCover :=
    alternatingSixUniversalCoverSylow 3
  let innerHom :
      SylowNormalizer P →* SylowAutStabilizer P :=
    SylowAutStabilizer.normalizerInnerHom P
  let E :
      Subgroup (SylowAutStabilizer P) :=
    alternatingSixThreeCTblLibCandidateEquivarianceSubgroup T
  have hInner : innerHom.range ≤ E := by
    intro a ha
    rw [
      alternatingSixThreeCTblLibCandidateEquivarianceSubgroup_mem_iff
    ]
    intro r
    exact
      SylowAutStabilizer.rowEquiv_intertwines_mem_normalizerInnerHom_range
        P
        (alternatingSixAmbientPPrimeCharacterEquiv T 3)
        AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
        alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv
        a ha r
  have hAlphaOne :
      alternatingSixUniversalCoverCorrectedAlphaOneStabilizer P ∈ E := by
    rw [
      alternatingSixThreeCTblLibCandidateEquivarianceSubgroup_mem_iff
    ]
    intro r
    exact
      alternatingSixThreeCTblLibCandidate_intertwines_correctedAlphaOne
        T hAmbientAlphaOne hLocalAlphaOne r
  have hAlphaTwo :
      alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer P ∈ E := by
    rw [
      alternatingSixThreeCTblLibCandidateEquivarianceSubgroup_mem_iff
    ]
    intro r
    exact
      alternatingSixThreeCTblLibCandidate_intertwines_correctedAlphaTwo
        T hAmbientAlphaTwo hLocalAlphaTwo r
  have hOuter :
      Subgroup.closure
          {alternatingSixUniversalCoverCorrectedAlphaOneStabilizer P,
            alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer P} ≤
        E := by
    rw [Subgroup.closure_le]
    intro a ha
    rcases ha with (rfl | ha)
    · exact hAlphaOne
    · simpa only [Set.mem_singleton_iff] using ha ▸ hAlphaTwo
  have hGenerated :
      innerHom.range ⊔
          Subgroup.closure
            {alternatingSixUniversalCoverCorrectedAlphaOneStabilizer P,
              alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer P} ≤
        E :=
    sup_le hInner hOuter
  have hTop : (⊤ : Subgroup (SylowAutStabilizer P)) ≤ E := by
    rw [← hGeneration]
    exact hGenerated
  intro a r
  have ha : a ∈ E :=
    hTop (Subgroup.mem_top a)
  exact
    (alternatingSixThreeCTblLibCandidateEquivarianceSubgroup_mem_iff
      T a).mp ha r

end InductiveMcKay
end McKayConjecture
