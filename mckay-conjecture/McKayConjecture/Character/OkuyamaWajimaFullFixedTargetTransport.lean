/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ExtensionEquivalenceTransport
import McKayConjecture.Character.OkuyamaWajimaFullFixedCoordinates

/-!
# Target-character transport in the full-fixed Okuyama--Wajima branch

If `U` centralizes `P` and contains `C_K(P)`, the literal fixed pair used
by Isaacs 13.29,

`K inside U K ∩ (U K)^P ≤ (U K)^P`,

is canonically isomorphic to the ambient pair

`C_K(P) ≤ U`.

This file records the commuting square and transports exact irreducible
character extensions across it.  It deliberately contains no cyclic or
prime-power ascent: those are separate outer steps.
-/

noncomputable section

namespace McKayConjecture
namespace OkuyamaWajimaFullFixedTargetTransport

variable {A : Type} [Group A] [Finite A]
variable (P K U : Subgroup A) [K.Normal]

/-- The ambient fixed-point kernel `C_K(P)`, named locally so it can be
used uniformly as both a subgroup and its subtype group. -/
abbrev ambientFixedPoints : Subgroup A :=
  K ⊓ Subgroup.centralizer (P : Set A)

/-- The fixed normal subgroup in the literal Isaacs target, transported
all the way to the ambient subgroup `C_K(P)`. -/
def fixedNormalSubgroupEquivAmbientFixedPoints
    (hcentral :
      U ≤ Subgroup.centralizer (P : Set A))
    (hfixedU :
      ambientFixedPoints P K ≤ U) :
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
        (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) ≃*
      ambientFixedPoints P K := by
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
    (OkuyamaWajimaFullFixedCoordinates.fixedNormalSubgroupEquivInternalFixedPoints
      P K U hcentral hfixedU).trans
      (Subgroup.subgroupOfEquivOfLe hfixedU)

/-- The fixed-group and fixed-normal-subgroup equivalences form the exact
commuting square with the ambient inclusion `C_K(P) ≤ U`. -/
theorem fixedPairEquiv_commutes
    (hcentral :
      U ≤ Subgroup.centralizer (P : Set A))
    (hfixedU :
      ambientFixedPoints P K ≤ U) :
    letI :
        MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        P (U ⊔ K)
          (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
            P K U hcentral)
    letI :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
        P K U
    (OkuyamaWajimaFullFixedCoordinates.sourceFixedPointsEquiv
          P K U hcentral hfixedU).toMonoidHom.comp
        (IsaacsGlaubermanRestriction.fixedNormalSubgroup
          (S := P) (G := ↥(U ⊔ K : Subgroup A))
          (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U)).subtype =
      (Subgroup.inclusion hfixedU).comp
        (fixedNormalSubgroupEquivAmbientFixedPoints
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

/-- Exact extensions are unchanged by replacing the literal Isaacs
fixed-point pair with the ambient pair `C_K(P) ≤ U`. -/
theorem isExtensionAlong_fixedPairEquiv_iff
    (hcentral :
      U ≤ Subgroup.centralizer (P : Set A))
    (hfixedU :
      ambientFixedPoints P K ≤ U)
    (phi :
      IrreducibleCharacter (ambientFixedPoints P K))
    (eta : IrreducibleCharacter U) :
    letI :
        MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        P (U ⊔ K)
          (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
            P K U hcentral)
    letI :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
        P K U
    IrreducibleCharacter.IsExtensionAlong
        (IsaacsGlaubermanRestriction.fixedNormalSubgroup
          (S := P) (G := ↥(U ⊔ K : Subgroup A))
          (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U)).subtype
        (phi.comap
          (fixedNormalSubgroupEquivAmbientFixedPoints
            P K U hcentral hfixedU))
        (eta.comap
          (OkuyamaWajimaFullFixedCoordinates.sourceFixedPointsEquiv
            P K U hcentral hfixedU)) ↔
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion hfixedU) phi eta := by
  letI :
      MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      P (U ⊔ K)
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          P K U hcentral)
  letI :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      P K U
  let eG :=
    OkuyamaWajimaFullFixedCoordinates.sourceFixedPointsEquiv
      P K U hcentral hfixedU
  let eN :=
    fixedNormalSubgroupEquivAmbientFixedPoints
      P K U hcentral hfixedU
  let N :=
    IsaacsGlaubermanRestriction.fixedNormalSubgroup
      (S := P) (G := ↥(U ⊔ K : Subgroup A))
      (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U)
  have hcomm :
      eG.toMonoidHom.comp N.subtype =
        (Subgroup.inclusion hfixedU).comp
          eN.toMonoidHom :=
    fixedPairEquiv_commutes P K U hcentral hfixedU
  constructor
  · intro h
    have hcomm' :
        eG.symm.toMonoidHom.comp
            (Subgroup.inclusion hfixedU) =
          N.subtype.comp eN.symm.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      apply eG.injective
      have hx :=
        congrArg
          (fun f : N →* U => f (eN.symm x))
          hcomm
      simpa using hx.symm
    have h' :=
      IrreducibleCharacter.IsExtensionAlong.comap_equiv
        eG.symm eN.symm hcomm' h
    simpa [eG, eN] using h'
  · intro h
    exact
      IrreducibleCharacter.IsExtensionAlong.comap_equiv
        eG eN hcomm h

end OkuyamaWajimaFullFixedTargetTransport
end McKayConjecture
