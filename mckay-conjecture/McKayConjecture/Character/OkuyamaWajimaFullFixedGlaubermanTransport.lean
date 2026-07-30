/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaFullFixedSourceTransport
import McKayConjecture.Character.OkuyamaWajimaFullFixedTargetTransport
import McKayConjecture.Character.OverAlongTransport

/-!
# Glauberman-character transport in the full-fixed branch

The action-level correspondent of the internal copy of `K` in `U K`
must agree, after all literal fixed-subgroup coordinate changes, with the
ordinary `P`-Glauberman correspondent on `C_K(P)`.

The proof below does not choose a compatible strong realization.  Instead
it transports the defining restriction multiplicity through two commuting
squares and invokes uniqueness in the supplied ordinary Glauberman
correspondence.
-/

noncomputable section

namespace McKayConjecture
namespace OkuyamaWajimaFullFixedGlaubermanTransport

open CliffordCorrespondence

variable {A : Type} [Group A] [Finite A]
variable {p : ℕ} [Fact p.Prime]
variable (P K U : Subgroup A) [K.Normal]

/-- The literal fixed normal subgroup maps back into the internal copy of
`K` in `U K`. -/
def fixedNormalToSourceNormalHom
    (hcentral :
      U ≤ Subgroup.centralizer (P : Set A)) :
    letI :
        MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        P (U ⊔ K)
          (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
            P K U hcentral)
    letI :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
        P K U
    IsaacsGlaubermanRestriction.fixedNormalSubgroup
        (S := P) (G := ↥(U ⊔ K : Subgroup A))
        (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) →*
      OkuyamaWajimaFullFixedCoordinates.sourceNormal K U := by
  letI :
      MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      P (U ⊔ K)
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          P K U hcentral)
  letI :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      P K U
  exact
    (actionFixedPointsInclusion P
      (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U)).comp
      (IsaacsGlaubermanRestriction.fixedNormalSubgroupEquiv
        (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U)
        (OkuyamaWajimaFullFixedCoordinates.sourceNormalAction_compatible
          P K U hcentral)).symm.toMonoidHom

/-- The internal-source and ambient-fixed equivalences commute with their
canonical inclusions. -/
theorem fixedNormalToKernel_square
    (hcentral :
      U ≤ Subgroup.centralizer (P : Set A))
    (hfixedU :
      K ⊓ Subgroup.centralizer (P : Set A) ≤ U) :
    letI :
        MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        P (U ⊔ K)
          (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
            P K U hcentral)
    letI :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
        P K U
    (OkuyamaWajimaFullFixedSourceTransport.sourceNormalEquivKernel
        K U).toMonoidHom.comp
        (fixedNormalToSourceNormalHom P K U hcentral) =
      (coprimeFixedPointsInclusion K P).comp
        (OkuyamaWajimaFullFixedTargetTransport.fixedNormalSubgroupEquivAmbientFixedPoints
          P K U hcentral hfixedU).toMonoidHom := by
  letI :
      MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      P (U ⊔ K)
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          P K U hcentral)
  letI :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      P K U
  ext x
  rfl

/-- The literal fixed-normal correspondent transported to `C_K(P)` is
the correspondent selected by every supplied ordinary Glauberman
correspondence. -/
theorem fixedNormalCorrespondent_transport_eq
    (hcentral :
      U ≤ Subgroup.centralizer (P : Set A))
    (hfixedU :
      K ⊓ Subgroup.centralizer (P : Set A) ≤ U)
    (theta :
      PInvariantPPrimeIrreducibleCharacter K P p)
    (gP : GlaubermanCorrespondence K P p)
    (dN :
      letI :=
        OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
          P K U
      ActionGlaubermanCorrespondence
        P
        (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U)
        p) :
    letI :
        MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        P (U ⊔ K)
          (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
            P K U hcentral)
    letI :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
        P K U
    let thetaN :=
      OkuyamaWajimaFullFixedSourceTransport.internalInvariantSourceCharacter
        P K U theta
    let hsmul :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction_compatible
        P K U hcentral
    let fixedCorr :=
      IsaacsGlaubermanRestriction.fixedNormalCorrespondent
        (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U)
        hsmul dN thetaN
    IrreducibleCharacter.pPrimeComapEquiv p
        (OkuyamaWajimaFullFixedTargetTransport.fixedNormalSubgroupEquivAmbientFixedPoints
          P K U hcentral hfixedU).symm
        fixedCorr =
      gP.characterEquiv theta := by
  letI :
      MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      P (U ⊔ K)
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          P K U hcentral)
  letI :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      P K U
  let N :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal K U
  let hsmul :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction_compatible
      P K U hcentral
  let F :=
    IsaacsGlaubermanRestriction.fixedNormalSubgroup
      (S := P) (G := ↥(U ⊔ K : Subgroup A)) N
  let eN :=
    OkuyamaWajimaFullFixedSourceTransport.sourceNormalEquivKernel
      K U
  let eF :=
    OkuyamaWajimaFullFixedTargetTransport.fixedNormalSubgroupEquivAmbientFixedPoints
      P K U hcentral hfixedU
  let j : F →* N :=
    fixedNormalToSourceNormalHom P K U hcentral
  let thetaN :=
    OkuyamaWajimaFullFixedSourceTransport.internalInvariantSourceCharacter
      P K U theta
  let fixedCorr :=
    IsaacsGlaubermanRestriction.fixedNormalCorrespondent
      N hsmul dN thetaN
  let candidate :
      PPrimeIrreducibleCharacter
        (coprimeFixedPoints K P) p :=
    IrreducibleCharacter.pPrimeComapEquiv p eF.symm
      fixedCorr
  apply gP.eq_correspondent_of_multiplicity_isPPrime
  have hfixedMultiplicity :
      restrictionMultiplicity j fixedCorr.1 thetaN.1.1 =
        restrictionMultiplicity
          (actionFixedPointsInclusion P N)
          (dN.characterEquiv thetaN).1 thetaN.1.1 := by
    let eNF :=
      IsaacsGlaubermanRestriction.fixedNormalSubgroupEquiv
        N hsmul
    have hcomm :
        (MulEquiv.refl N).toMonoidHom.comp j =
          (actionFixedPointsInclusion P N).comp
            eNF.symm.toMonoidHom := by
      rfl
    simpa only [j, fixedCorr,
      IsaacsGlaubermanRestriction.fixedNormalCorrespondent_coe,
      IrreducibleCharacter.comap_refl] using
      (restrictionMultiplicity_comap_equiv
        (MulEquiv.refl N) eNF.symm
        (actionFixedPointsInclusion P N) j hcomm
        (dN.characterEquiv thetaN).1 thetaN.1.1)
  have hjPrime :
      ¬p ∣
        restrictionMultiplicity j fixedCorr.1 thetaN.1.1 := by
    rw [hfixedMultiplicity]
    exact dN.multiplicity_isPPrime thetaN
  have hcomm :
      eN.toMonoidHom.comp j =
        (coprimeFixedPointsInclusion K P).comp
          eF.toMonoidHom :=
    fixedNormalToKernel_square P K U hcentral hfixedU
  have htransport :=
    restrictionMultiplicity_comap_equiv
      eN eF
      (coprimeFixedPointsInclusion K P) j hcomm
      candidate.1 theta.1.1
  have hcandidateBack :
      candidate.1.comap eF = fixedCorr.1 := by
    change
      (fixedCorr.1.comap eF.symm).comap eF =
        fixedCorr.1
    simp
  have hthetaBack :
      theta.1.1.comap eN = thetaN.1.1 := by
    rfl
  rw [hcandidateBack, hthetaBack] at htransport
  rw [← htransport]
  exact hjPrime

end OkuyamaWajimaFullFixedGlaubermanTransport
end McKayConjecture
