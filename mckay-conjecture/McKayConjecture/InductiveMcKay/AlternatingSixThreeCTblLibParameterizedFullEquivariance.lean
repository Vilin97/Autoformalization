/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixThreeCTblLibFullEquivarianceReduction
import McKayConjecture.InductiveMcKay.AlternatingSixThreeCTblLibParameterizedRowBridge

/-!
# Conditional full equivariance for parameterized three-local CTblLib rows

A proposed pair of semantic CT-position identifications transports the
audited finite candidate to an equivalence between the project's ambient
and local row types.  The genuine ambient and local Sylow-stabilizer actions
are homomorphisms into permutation groups, so the elements intertwined by
that transported candidate form an equalizer subgroup.

The generic inner-normalizer theorem puts the complete inner normalizer
range in the equalizer.  The four parameterized generator-action bridges
put the two corrected outer generators in it.  Consequently the existing
explicit stabilizer-generation hypothesis implies full equivariance and,
conditionally, a concrete three-local character-table certificate.

None of the CT-position identifications, generator bridges, or generation
hypothesis is asserted in this file.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixThreeParameterizedFullEquivarianceFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace AlternatingSixThreeCTblLibRowIdentification

variable
  (identification : AlternatingSixThreeCTblLibRowIdentification)

/-- Genuine full equivariance of the candidate transported through the
proposed CT-position identifications. -/
def Equivariant
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Prop :=
  ∀ (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3))
    (r : AlternatingSixAmbientPPrimeRowIndex 3),
    identification.candidateAmbientLocalRowEquiv
        (alternatingSixAmbientPPrimeRowPermutation T 3
          (a : MulAut AlternatingSixUniversalCover) r) =
      alternatingSixThreeActualNormalizerRowPermutation a
        (identification.candidateAmbientLocalRowEquiv r)

/-- Transport the genuine ambient row action through the candidate induced
by the proposed CT-position identifications. -/
def transportedAmbientRowPermutationHom
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3) →*
      Equiv.Perm AlternatingSixThreeConcreteNormalizerRow :=
  identification.candidateAmbientLocalRowEquiv.permCongrHom.toMonoidHom.comp
    (alternatingSixThreeAmbientSemanticRowPermutationHom T)

/-- The equalizer subgroup on which the transported candidate intertwines
the two genuine row actions. -/
def equivarianceSubgroup
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Subgroup
      (SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3)) :=
  MonoidHom.eqLocus
    (identification.transportedAmbientRowPermutationHom T)
    alternatingSixThreeLocalSemanticRowPermutationHom

/-- Pointwise form of membership in the parameterized equivariance
equalizer. -/
theorem equivarianceSubgroup_mem_iff
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3)) :
    a ∈ identification.equivarianceSubgroup T ↔
      ∀ r : AlternatingSixAmbientPPrimeRowIndex 3,
        identification.candidateAmbientLocalRowEquiv
            (alternatingSixAmbientPPrimeRowPermutation T 3
              (a : MulAut AlternatingSixUniversalCover) r) =
          alternatingSixThreeActualNormalizerRowPermutation a
            (identification.candidateAmbientLocalRowEquiv r) := by
  constructor
  · intro ha r
    have hperm :
        identification.candidateAmbientLocalRowEquiv.permCongr
            (alternatingSixAmbientPPrimeRowPermutation T 3
              (a : MulAut AlternatingSixUniversalCover)) =
          alternatingSixThreeActualNormalizerRowPermutation a := by
      exact ha
    have hr :=
      Equiv.congr_fun hperm
        (identification.candidateAmbientLocalRowEquiv r)
    simpa only [
      Equiv.permCongr_apply,
      Equiv.symm_apply_apply
    ] using hr
  · intro h
    change
      identification.candidateAmbientLocalRowEquiv.permCongr
          (alternatingSixAmbientPPrimeRowPermutation T 3
            (a : MulAut AlternatingSixUniversalCover)) =
        alternatingSixThreeActualNormalizerRowPermutation a
    apply Equiv.ext
    intro s
    have hs :=
      h (identification.candidateAmbientLocalRowEquiv.symm s)
    simpa only [
      Equiv.permCongr_apply,
      Equiv.apply_symm_apply
    ] using hs

/-- The four parameterized semantic generator bridges and the explicit
stabilizer-generation hypothesis imply genuine full equivariance of the
transported candidate. -/
theorem equivariant_of_generatorActionBridges_of_generation
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hBridges : identification.GeneratorActionBridges T)
    (hGeneration :
      AlternatingSixThreeSylowAutStabilizerGenerationHypothesis) :
    identification.Equivariant T := by
  let P : Sylow 3 AlternatingSixUniversalCover :=
    alternatingSixUniversalCoverSylow 3
  let innerHom :
      SylowNormalizer P →* SylowAutStabilizer P :=
    SylowAutStabilizer.normalizerInnerHom P
  let E :
      Subgroup (SylowAutStabilizer P) :=
    identification.equivarianceSubgroup T
  have hInner : innerHom.range ≤ E := by
    intro a ha
    rw [identification.equivarianceSubgroup_mem_iff]
    intro r
    exact
      SylowAutStabilizer.rowEquiv_intertwines_mem_normalizerInnerHom_range
        P
        (alternatingSixAmbientPPrimeCharacterEquiv T 3)
        AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
        identification.candidateAmbientLocalRowEquiv
        a ha r
  have hAlphaOne :
      alternatingSixUniversalCoverCorrectedAlphaOneStabilizer P ∈ E := by
    rw [identification.equivarianceSubgroup_mem_iff]
    intro r
    exact
      identification.candidate_intertwines_correctedAlphaOne T
        hBridges.ambientAlphaOne hBridges.localAlphaOne r
  have hAlphaTwo :
      alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer P ∈ E := by
    rw [identification.equivarianceSubgroup_mem_iff]
    intro r
    exact
      identification.candidate_intertwines_correctedAlphaTwo T
        hBridges.ambientAlphaTwo hBridges.localAlphaTwo r
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
    (identification.equivarianceSubgroup_mem_iff T a).mp ha r

/-- Package a proof of parameterized genuine full equivariance into the
existing concrete three-local character-table interface. -/
def concreteCharacterTableCertificate
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : identification.Equivariant T) :
    AlternatingSixThreeConcreteCharacterTableCertificate
      (AlternatingSixAmbientPPrimeRowIndex 3) where
  ambientEnumeration :=
    alternatingSixAmbientPPrimeCharacterEquiv T 3
  indexEquiv :=
    identification.candidateAmbientLocalRowEquiv
  indexEquivariance := by
    intro a r
    exact h a r

/-- Construct the conditional concrete character-table certificate directly
from the four generator bridges and the explicit generation hypothesis. -/
def concreteCharacterTableCertificateOfGeneration
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hBridges : identification.GeneratorActionBridges T)
    (hGeneration :
      AlternatingSixThreeSylowAutStabilizerGenerationHypothesis) :
    AlternatingSixThreeConcreteCharacterTableCertificate
      (AlternatingSixAmbientPPrimeRowIndex 3) :=
  identification.concreteCharacterTableCertificate T
    (identification.equivariant_of_generatorActionBridges_of_generation
      T hBridges hGeneration)

@[simp]
theorem concreteCharacterTableCertificate_ambientEnumeration
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : identification.Equivariant T) :
    (identification.concreteCharacterTableCertificate T h
      |>.ambientEnumeration) =
      alternatingSixAmbientPPrimeCharacterEquiv T 3 :=
  rfl

@[simp]
theorem concreteCharacterTableCertificate_indexEquiv
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : identification.Equivariant T) :
    (identification.concreteCharacterTableCertificate T h
      |>.indexEquiv) =
      identification.candidateAmbientLocalRowEquiv :=
  rfl

end AlternatingSixThreeCTblLibRowIdentification

/-- For the recorded project enumerations, parameterized genuine
equivariance is definitionally the previously stated fixed-candidate
predicate. -/
theorem alternatingSixThreeRecorded_equivariant_iff
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    alternatingSixThreeRecordedCTblLibRowIdentification.Equivariant T ↔
      AlternatingSixThreeCTblLibCandidateEquivariant T :=
  Iff.rfl

end InductiveMcKay
end McKayConjecture
