/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCTblLibParameterizedRowBridge
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCentralBlockRowBridgeEquivariance
import McKayConjecture.InductiveMcKay.NormalizerInnerAutomorphismStabilizer

/-!
# Conditional full equivariance for parameterized five-local CTblLib rows

A proposed pair of semantic CT-position identifications transports the
audited finite candidate to an equivalence between the project's ambient
and proved actual-normalizer row types.  The genuine ambient and local
Sylow-stabilizer actions are homomorphisms into permutation groups, so the
elements intertwined by that transported candidate form an equalizer
subgroup.

The generic inner-normalizer theorem puts the complete inner normalizer
range in the equalizer.  The four parameterized generator-action bridges
put the two corrected outer generators in it.  Consequently an explicit
stabilizer-generation hypothesis implies full equivariance and,
conditionally, a concrete five-local character-table certificate.

None of the CT-position identifications, generator bridges, or generation
hypothesis is asserted in this file.  The final central-block comparison is
only an algebraic specialization and does not identify the CTblLib order.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveParameterizedFullEquivarianceFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-! ### Genuine semantic permutation representations -/

/-- The genuine action of the Sylow automorphism stabilizer on the
arithmetic ambient prime-to-five rows. -/
def alternatingSixFiveAmbientSemanticRowPermutationHom
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5) →*
      Equiv.Perm (AlternatingSixAmbientPPrimeRowIndex 5) where
  toFun a :=
    alternatingSixAmbientPPrimeRowPermutation T 5
      (a : MulAut AlternatingSixUniversalCover)
  map_one' :=
    alternatingSixAmbientPPrimeRowPermutation_one T 5
  map_mul' a b :=
    alternatingSixAmbientPPrimeRowPermutation_mul T 5
      (a : MulAut AlternatingSixUniversalCover)
      (b : MulAut AlternatingSixUniversalCover)

/-- The genuine restricted action of the Sylow automorphism stabilizer on
the proved actual-normalizer prime-to-five rows. -/
def alternatingSixFiveLocalSemanticRowPermutationHom :
    SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5) →*
      Equiv.Perm AlternatingSixFiveConcreteNormalizerRow where
  toFun a :=
    alternatingSixFiveActualNormalizerRowPermutation a
  map_one' :=
    normalizerPPrimeRowPermutation_one
      (alternatingSixUniversalCoverSylow 5)
      alternatingSixFiveActualNormalizerPPrimeCharacterEquiv
  map_mul' a b :=
    normalizerPPrimeRowPermutation_mul
      (alternatingSixUniversalCoverSylow 5)
      alternatingSixFiveActualNormalizerPPrimeCharacterEquiv
      a b

/-! ### The explicit missing generation statement -/

/-- The exact group-theoretic hypothesis needed by the five-local
full-equivariance reduction: the inner normalizer image together with the
two corrected outer automorphisms generates the full Sylow automorphism
stabilizer. -/
def AlternatingSixFiveSylowAutStabilizerGenerationHypothesis :
    Prop :=
  (SylowAutStabilizer.normalizerInnerHom
      (alternatingSixUniversalCoverSylow 5)).range ⊔
    Subgroup.closure
      {alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
          (alternatingSixUniversalCoverSylow 5),
        alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
          (alternatingSixUniversalCoverSylow 5)} =
    ⊤

namespace AlternatingSixFiveCTblLibRowIdentification

variable
  (identification : AlternatingSixFiveCTblLibRowIdentification)

/-! ### The equalizer subgroup of semantic row actions -/

/-- Genuine full equivariance of the candidate transported through the
proposed CT-position identifications. -/
def Equivariant
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Prop :=
  ∀ (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5))
    (r : AlternatingSixAmbientPPrimeRowIndex 5),
    identification.candidateAmbientLocalRowEquiv
        (alternatingSixAmbientPPrimeRowPermutation T 5
          (a : MulAut AlternatingSixUniversalCover) r) =
      alternatingSixFiveActualNormalizerRowPermutation a
        (identification.candidateAmbientLocalRowEquiv r)

/-- Transport the genuine ambient row action through the candidate induced
by the proposed CT-position identifications. -/
def transportedAmbientRowPermutationHom
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5) →*
      Equiv.Perm AlternatingSixFiveConcreteNormalizerRow :=
  identification.candidateAmbientLocalRowEquiv.permCongrHom.toMonoidHom.comp
    (alternatingSixFiveAmbientSemanticRowPermutationHom T)

/-- The equalizer subgroup on which the transported candidate intertwines
the two genuine row actions. -/
def equivarianceSubgroup
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Subgroup
      (SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5)) :=
  MonoidHom.eqLocus
    (identification.transportedAmbientRowPermutationHom T)
    alternatingSixFiveLocalSemanticRowPermutationHom

/-- Pointwise form of membership in the parameterized equivariance
equalizer. -/
theorem equivarianceSubgroup_mem_iff
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5)) :
    a ∈ identification.equivarianceSubgroup T ↔
      ∀ r : AlternatingSixAmbientPPrimeRowIndex 5,
        identification.candidateAmbientLocalRowEquiv
            (alternatingSixAmbientPPrimeRowPermutation T 5
              (a : MulAut AlternatingSixUniversalCover) r) =
          alternatingSixFiveActualNormalizerRowPermutation a
            (identification.candidateAmbientLocalRowEquiv r) := by
  constructor
  · intro ha r
    have hperm :
        identification.candidateAmbientLocalRowEquiv.permCongr
            (alternatingSixAmbientPPrimeRowPermutation T 5
              (a : MulAut AlternatingSixUniversalCover)) =
          alternatingSixFiveActualNormalizerRowPermutation a := by
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
          (alternatingSixAmbientPPrimeRowPermutation T 5
            (a : MulAut AlternatingSixUniversalCover)) =
        alternatingSixFiveActualNormalizerRowPermutation a
    apply Equiv.ext
    intro s
    have hs :=
      h (identification.candidateAmbientLocalRowEquiv.symm s)
    simpa only [
      Equiv.permCongr_apply,
      Equiv.apply_symm_apply
    ] using hs

/-! ### Full equivariance and the concrete certificate -/

/-- The four parameterized semantic generator bridges and the explicit
stabilizer-generation hypothesis imply genuine full equivariance of the
transported candidate. -/
theorem equivariant_of_generatorActionBridges_of_generation
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hBridges : identification.GeneratorActionBridges T)
    (hGeneration :
      AlternatingSixFiveSylowAutStabilizerGenerationHypothesis) :
    identification.Equivariant T := by
  let P : Sylow 5 AlternatingSixUniversalCover :=
    alternatingSixUniversalCoverSylow 5
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
        (alternatingSixAmbientPPrimeCharacterEquiv T 5)
        alternatingSixFiveActualNormalizerPPrimeCharacterEquiv
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
existing concrete five-local character-table interface. -/
def concreteCharacterTableCertificate
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : identification.Equivariant T) :
    AlternatingSixFiveConcreteCharacterTableCertificate
      (AlternatingSixAmbientPPrimeRowIndex 5) where
  ambientEnumeration :=
    alternatingSixAmbientPPrimeCharacterEquiv T 5
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
      AlternatingSixFiveSylowAutStabilizerGenerationHypothesis) :
    AlternatingSixFiveConcreteCharacterTableCertificate
      (AlternatingSixAmbientPPrimeRowIndex 5) :=
  identification.concreteCharacterTableCertificate T
    (identification.equivariant_of_generatorActionBridges_of_generation
      T hBridges hGeneration)

@[simp]
theorem concreteCharacterTableCertificate_ambientEnumeration
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : identification.Equivariant T) :
    (identification.concreteCharacterTableCertificate T h
      |>.ambientEnumeration) =
      alternatingSixAmbientPPrimeCharacterEquiv T 5 :=
  rfl

@[simp]
theorem concreteCharacterTableCertificate_indexEquiv
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : identification.Equivariant T) :
    (identification.concreteCharacterTableCertificate T h
      |>.indexEquiv) =
      identification.candidateAmbientLocalRowEquiv :=
  rfl

end AlternatingSixFiveCTblLibRowIdentification

/-! ### The central-block matching as a coordinate specialization -/

/-- Under the deliberately engineered central-block position data,
parameterized genuine equivariance is the existing central-block
equivariance predicate.

This only compares two formulations of the same transported candidate.  It
does not say that the engineered position data records the true CTblLib
order. -/
theorem alternatingSixFiveCentralBlock_equivariant_iff
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    alternatingSixFiveCentralBlockCTblLibRowIdentification.Equivariant T ↔
      AlternatingSixFiveCentralBlockRowMatchingEquivariant T := by
  unfold AlternatingSixFiveCTblLibRowIdentification.Equivariant
  rw [
    alternatingSixFiveCentralBlockCTblLibRowIdentification_candidate
  ]
  rfl

end InductiveMcKay
end McKayConjecture
