/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanActionPGroupInduction
import McKayConjecture.Character.GlaubermanActionTransport
import McKayConjecture.Character.GoodElementTwoGeneratorExtension
import McKayConjecture.Character.OkuyamaWajimaFullFixedSourceNormality
import McKayConjecture.Character.OkuyamaWajimaFullFixedGlaubermanTransport
import McKayConjecture.Character.OkuyamaWajimaFullFixedOuterCommutativity
import McKayConjecture.Character.OkuyamaWajimaPrintedInduction

/-!
# Reverse outer assembly in the full-fixed Okuyama--Wajima branch

This file isolates the reverse implication in the full-fixed branch.
The generic maximal-fibre theorem already converts a suitably invariant
extension on `U K` into an extension on the fixed-point group.  The first
part below proves that all of its source-side hypotheses are automatic
after restricting a global extension:

* restriction through an intermediate subgroup remains irreducible;
* the restricted character is fixed by conjugation by `P`; and
* the internal copy of `K` carries exactly the transported original
  character.

The final theorems package the resulting inner reverse step first in
arbitrary `U K` coordinates and then for the subgroup canonically
selected by the Gorenstein theorem.  The character-coordinate
identification on `C_K(P)` is included.  Strong Glauberman equivariance
then supplies an invariant selected extension, after which cyclic ascent
from `U` to the complement and Navarro ascent to `N_G(P)` complete the
reverse implication.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open CliffordCorrespondence
open GroupTheory

namespace CharacterTriple

variable {A : Type} [Group A] [Finite A]

/-- A global extension restricts irreducibly to every intermediate
subgroup containing the distinguished normal subgroup. -/
theorem restrictTo_hasExtension_of_hasExtension
    (T : CharacterTriple A)
    (B : Subgroup A)
    (hNB : T.normalSubgroup ≤ B)
    (hglobal : T.HasExtension) :
    (T.restrictTo B hNB).HasExtension := by
  obtain ⟨chi, hchi⟩ := hglobal
  let TB := T.restrictTo B hNB
  have hchi' :
      IrreducibleCharacter.IsExtensionAlong
        (B.subtype.comp TB.normalSubgroup.subtype)
        TB.character chi := by
    intro x
    change
      chi.values (((x : TB.normalSubgroup) : B) : A) =
        T.character.values (T.normalSubgroupInEquiv B hNB x)
    rw [← T.normalSubgroupInEquiv_apply_coe B hNB x]
    exact hchi (T.normalSubgroupInEquiv B hNB x)
  obtain ⟨eta, heta, _⟩ :=
    IrreducibleCharacter.IsExtensionAlong.exists_intermediate hchi'
  exact ⟨eta, heta⟩

end CharacterTriple

namespace OkuyamaWajimaFullFixedOuterReverse

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)

local instance fullFixedReversePConjugationAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K (P : Subgroup G)

variable
  (theta :
    PInvariantPPrimeIrreducibleCharacter
      K (P : Subgroup G) p)
  (hinvariant :
    ∀ g : G, g • theta.1.1 = theta.1.1)

section SourceCoordinates

variable (U : Subgroup G)

/-- The internal copy of `K` in `U K`, identified with `K` itself. -/
abbrev sourceNormalEquiv :
    OkuyamaWajimaFullFixedCoordinates.sourceNormal K U ≃* K :=
  OkuyamaWajimaFullFixedSourceTransport.sourceNormalEquivKernel K U

/-- The original invariant character, transported to the internal copy
of `K` in `U K`. -/
abbrev sourceNormalCharacter :
    letI :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
        (P : Subgroup G) K U
    ActionInvariantPPrimeIrreducibleCharacter
      P (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) p :=
  OkuyamaWajimaFullFixedSourceTransport.internalInvariantSourceCharacter
    (P : Subgroup G) K U theta

@[simp]
theorem sourceNormalCharacter_coe :
    letI :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
        (P : Subgroup G) K U
    (sourceNormalCharacter K P theta U).1.1 =
      theta.1.1.comap (sourceNormalEquiv K U) := by
  rfl

variable
  (hcentral :
    U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))

/-- In the literal Isaacs fixed-normal coordinate, the action
correspondent is exactly the supplied ordinary `P`-correspondent pulled
back from `C_K(P)`. -/
theorem fixedNormalCorrespondent_eq_phi_comap
    (hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U)
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p) :
    letI : MulDistribMulAction P (U ⊔ K : Subgroup G) :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        (P : Subgroup G) (U ⊔ K)
          (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
            (P : Subgroup G) K U hcentral)
    letI :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
        (P : Subgroup G) K U
    ∀ dNormal :
        ActionGlaubermanCorrespondence P
          (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) p,
      (IsaacsGlaubermanRestriction.fixedNormalCorrespondent
          (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U)
          (OkuyamaWajimaFullFixedCoordinates.sourceNormalAction_compatible
            (P : Subgroup G) K U hcentral)
          dNormal (sourceNormalCharacter K P theta U)).1 =
        (gP.characterEquiv theta).1.comap
          (OkuyamaWajimaFullFixedTargetTransport.fixedNormalSubgroupEquivAmbientFixedPoints
            (P : Subgroup G) K U hcentral hfixedU) := by
  letI : MulDistribMulAction P (U ⊔ K : Subgroup G) :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      (P : Subgroup G) (U ⊔ K)
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          (P : Subgroup G) K U hcentral)
  letI :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      (P : Subgroup G) K U
  intro dNormal
  let N :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal K U
  let eF :=
    OkuyamaWajimaFullFixedTargetTransport.fixedNormalSubgroupEquivAmbientFixedPoints
      (P : Subgroup G) K U hcentral hfixedU
  let fixedCorr :=
    IsaacsGlaubermanRestriction.fixedNormalCorrespondent
      N
      (OkuyamaWajimaFullFixedCoordinates.sourceNormalAction_compatible
        (P : Subgroup G) K U hcentral)
      dNormal (sourceNormalCharacter K P theta U)
  have htransport :=
    OkuyamaWajimaFullFixedGlaubermanTransport.fixedNormalCorrespondent_transport_eq
      (P : Subgroup G) K U hcentral hfixedU theta gP dNormal
  have htransport' :
      fixedCorr.1.comap eF.symm =
        (gP.characterEquiv theta).1 :=
    congrArg Subtype.val htransport
  apply (IrreducibleCharacter.comapEquiv eF.symm).injective
  change
    fixedCorr.1.comap eF.symm =
      ((gP.characterEquiv theta).1.comap eF).comap eF.symm
  rw [htransport']
  simp

/-- The literal fixed-normal correspondent is invariant under the whole
fixed-point group.  After the preceding coordinate equality this is just
normalizer-equivariance of the supplied ordinary Glauberman
correspondence. -/
theorem fixedNormalCorrespondent_invariant
    (hinvariant :
      ∀ g : G, g • theta.1.1 = theta.1.1)
    (hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U)
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p) :
    letI : MulDistribMulAction P (U ⊔ K : Subgroup G) :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        (P : Subgroup G) (U ⊔ K)
          (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
            (P : Subgroup G) K U hcentral)
    letI :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
        (P : Subgroup G) K U
    ∀ (dNormal :
        ActionGlaubermanCorrespondence P
          (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) p)
      (g : FixedPoints.subgroup P (U ⊔ K : Subgroup G)),
      g •
          (IsaacsGlaubermanRestriction.fixedNormalCorrespondent
            (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U)
            (OkuyamaWajimaFullFixedCoordinates.sourceNormalAction_compatible
              (P : Subgroup G) K U hcentral)
            dNormal (sourceNormalCharacter K P theta U)).1 =
        (IsaacsGlaubermanRestriction.fixedNormalCorrespondent
          (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U)
          (OkuyamaWajimaFullFixedCoordinates.sourceNormalAction_compatible
            (P : Subgroup G) K U hcentral)
          dNormal (sourceNormalCharacter K P theta U)).1 := by
  letI : MulDistribMulAction P (U ⊔ K : Subgroup G) :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      (P : Subgroup G) (U ⊔ K)
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          (P : Subgroup G) K U hcentral)
  letI :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      (P : Subgroup G) K U
  intro dNormal g
  rw [fixedNormalCorrespondent_eq_phi_comap
    K P theta U hcentral hfixedU gP dNormal]
  apply IrreducibleCharacter.ext
  funext x
  rw [IrreducibleCharacter.conjBy_values]
  let eG :=
    OkuyamaWajimaFullFixedCoordinates.sourceFixedPointsEquiv
      (P : Subgroup G) K U hcentral hfixedU
  let eF :=
    OkuyamaWajimaFullFixedTargetTransport.fixedNormalSubgroupEquivAmbientFixedPoints
      (P : Subgroup G) K U hcentral hfixedU
  have hphi :=
    okuyamaWajimaFixedPointConjugationAction_invariant
      K (P : Subgroup G) U
      (hcentral.trans
        (Subgroup.centralizer_le_normalizer
          ((P : Subgroup G) : Set G)))
      gP theta hinvariant
      (eG g⁻¹) (eF x)
  change
    (gP.characterEquiv theta).1.values
        (eF ((MulAut.conjNormal g).symm x)) =
      (gP.characterEquiv theta).1.values (eF x)
  calc
    (gP.characterEquiv theta).1.values
          (eF ((MulAut.conjNormal g).symm x)) =
        (gP.characterEquiv theta).1.values
          (okuyamaWajimaFixedPointConjugationAction
            K (P : Subgroup G) U
            (hcentral.trans
              (Subgroup.centralizer_le_normalizer
                ((P : Subgroup G) : Set G)))
            (eG g⁻¹) (eF x)) := by
      apply congrArg (gP.characterEquiv theta).1.values
      apply Subtype.ext
      rfl
    _ = (gP.characterEquiv theta).1.values (eF x) :=
      hphi

/-- A global extension of `theta` restricts to an irreducible extension
on `U K`; because the action is ambient conjugation, that restricted
extension is automatically `P`-invariant. -/
theorem exists_invariant_sourceExtension
    (hsource :
      OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant) :
    letI : MulDistribMulAction P (U ⊔ K : Subgroup G) :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        (P : Subgroup G) (U ⊔ K)
          (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
            (P : Subgroup G) K U hcentral)
    letI : MulDistribMulAction P
        (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
        (P : Subgroup G) K U
    ∃ eta : IrreducibleCharacter (U ⊔ K : Subgroup G),
      IrreducibleCharacter.IsExtension
        (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U)
        (sourceNormalCharacter K P theta U).1.1 eta ∧
      ∀ (s : P) (a : (U ⊔ K : Subgroup G)),
        eta.values (s • a) = eta.values a := by
  letI : MulDistribMulAction P (U ⊔ K : Subgroup G) :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      (P : Subgroup G) (U ⊔ K)
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          (P : Subgroup G) K U hcentral)
  letI : MulDistribMulAction P
      (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      (P : Subgroup G) K U
  obtain ⟨chi, hchi⟩ := hsource
  change
    IrreducibleCharacter.IsExtensionAlong
      K.subtype theta.1.1 chi at hchi
  let N :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal K U
  let A : Subgroup G := U ⊔ K
  let e := sourceNormalEquiv K U
  have hchi' :
      IrreducibleCharacter.IsExtensionAlong
        (A.subtype.comp N.subtype)
        (sourceNormalCharacter K P theta U).1.1 chi := by
    intro n
    change
      chi.values (n : G) =
        theta.1.1.values (e n)
    exact hchi (e n)
  obtain ⟨eta, heta, hetaChi⟩ :=
    IrreducibleCharacter.IsExtensionAlong.exists_intermediate hchi'
  refine ⟨eta, heta, ?_⟩
  intro s a
  rw [← hetaChi (s • a), ← hetaChi a]
  change
    chi.values ((s : G) * (a : G) * (s : G)⁻¹) =
      chi.values (a : G)
  exact
    ClassFunction.conj_apply chi.toClassFunction
      (a : G) (s : G)

/-- If `U K` is ambient normal, the restricted global extension can be
chosen invariant under all ambient conjugations, not merely under the
acting Sylow subgroup.  This is the source of complement invariance in
the final reverse-equivariance argument. -/
theorem exists_ambientInvariant_sourceExtension
    (hsourceNormal : (U ⊔ K : Subgroup G).Normal)
    (hsource :
      OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant) :
    letI : MulDistribMulAction P (U ⊔ K : Subgroup G) :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        (P : Subgroup G) (U ⊔ K)
          (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
            (P : Subgroup G) K U hcentral)
    letI : MulDistribMulAction P
        (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
        (P : Subgroup G) K U
    letI : (U ⊔ K : Subgroup G).Normal := hsourceNormal
    ∃ eta : IrreducibleCharacter (U ⊔ K : Subgroup G),
      IrreducibleCharacter.IsExtension
          (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U)
          (sourceNormalCharacter K P theta U).1.1 eta ∧
        (∀ (s : P) (a : (U ⊔ K : Subgroup G)),
          eta.values (s • a) = eta.values a) ∧
        ∀ (g : G) (a : (U ⊔ K : Subgroup G)),
          eta.values (MulAut.conjNormal g a) =
            eta.values a := by
  letI : MulDistribMulAction P (U ⊔ K : Subgroup G) :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      (P : Subgroup G) (U ⊔ K)
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          (P : Subgroup G) K U hcentral)
  letI : MulDistribMulAction P
      (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      (P : Subgroup G) K U
  letI : (U ⊔ K : Subgroup G).Normal := hsourceNormal
  obtain ⟨chi, hchi⟩ := hsource
  change
    IrreducibleCharacter.IsExtensionAlong
      K.subtype theta.1.1 chi at hchi
  let N :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal K U
  let A : Subgroup G := U ⊔ K
  let e := sourceNormalEquiv K U
  have hchi' :
      IrreducibleCharacter.IsExtensionAlong
        (A.subtype.comp N.subtype)
        (sourceNormalCharacter K P theta U).1.1 chi := by
    intro n
    change
      chi.values (n : G) =
        theta.1.1.values (e n)
    exact hchi (e n)
  obtain ⟨eta, heta, hetaChi⟩ :=
    IrreducibleCharacter.IsExtensionAlong.exists_intermediate hchi'
  refine ⟨eta, heta, ?_, ?_⟩
  · intro s a
    rw [← hetaChi (s • a), ← hetaChi a]
    change
      chi.values ((s : G) * (a : G) * (s : G)⁻¹) =
        chi.values (a : G)
    exact
      ClassFunction.conj_apply chi.toClassFunction
        (a : G) (s : G)
  · intro g a
    rw [← hetaChi (MulAut.conjNormal g a), ← hetaChi a]
    change
      chi.values (g * (a : G) * g⁻¹) =
        chi.values (a : G)
    exact
      ClassFunction.conj_apply chi.toClassFunction
        (a : G) g

/-- All source-side hypotheses of the reverse full-fixed maximal-fibre
theorem are automatic in the `U K` coordinates.  This theorem deliberately
keeps only the target-base invariance visible: it is the character
coordinate statement, not a further source-side condition. -/
theorem exists_fixedTargetExtension
    (hK : IsPPrimeGroup p K)
    (hU : IsPPrimeGroup p U)
    (hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U) :
    letI : MulDistribMulAction P (U ⊔ K : Subgroup G) :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        (P : Subgroup G) (U ⊔ K)
          (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
            (P : Subgroup G) K U hcentral)
    letI : MulDistribMulAction P
        (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
        (P : Subgroup G) K U
    let N :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormal K U
    letI : N.Normal :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormal_normal K U
    ∀ (dSource :
        ActionGlaubermanCorrespondence
          P (U ⊔ K : Subgroup G) p)
      (dNormal :
        ActionGlaubermanCorrespondence P N p),
      IsMulCommutative ((U ⊔ K : Subgroup G) ⧸ N) →
      (∀ g : FixedPoints.subgroup P (U ⊔ K : Subgroup G),
        g •
            (IsaacsGlaubermanRestriction.fixedNormalCorrespondent
              N
              (OkuyamaWajimaFullFixedCoordinates.sourceNormalAction_compatible
                (P : Subgroup G) K U hcentral)
              dNormal
              (sourceNormalCharacter K P theta U)).1 =
          (IsaacsGlaubermanRestriction.fixedNormalCorrespondent
            N
            (OkuyamaWajimaFullFixedCoordinates.sourceNormalAction_compatible
              (P : Subgroup G) K U hcentral)
            dNormal
            (sourceNormalCharacter K P theta U)).1) →
      OkuyamaWajimaProperBranchThetaExtendsToG
          K P theta hinvariant →
        ∃ eta :
            IrreducibleCharacter
              (FixedPoints.subgroup P (U ⊔ K : Subgroup G)),
          IrreducibleCharacter.IsExtension
            (IsaacsGlaubermanRestriction.fixedNormalSubgroup
              (S := P) (G := (U ⊔ K : Subgroup G)) N)
            (IsaacsGlaubermanRestriction.fixedNormalCorrespondent
              N
              (OkuyamaWajimaFullFixedCoordinates.sourceNormalAction_compatible
                (P : Subgroup G) K U hcentral)
              dNormal
              (sourceNormalCharacter K P theta U)).1 eta := by
  letI : MulDistribMulAction P (U ⊔ K : Subgroup G) :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      (P : Subgroup G) (U ⊔ K)
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          (P : Subgroup G) K U hcentral)
  letI : MulDistribMulAction P
      (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      (P : Subgroup G) K U
  let N :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal K U
  letI : N.Normal :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal_normal K U
  dsimp only
  intro dSource dNormal hcomm htargetInvariant hsource
  letI : IsMulCommutative ((U ⊔ K : Subgroup G) ⧸ N) :=
    hcomm
  obtain ⟨sourceExtension, hsourceExtension,
      hsourceExtensionInvariant⟩ :=
    exists_invariant_sourceExtension
      K P theta hinvariant U hcentral hsource
  exact
    IsaacsGlaubermanRestriction.okuyamaWajimaFullFixed_exists_target_extension_of_fixedSourceExtension_automatic
      N
      (OkuyamaWajimaFullFixedCoordinates.sourceNormalAction_compatible
        (P : Subgroup G) K U hcentral)
      dSource dNormal P.isPGroup'
      (OkuyamaWajimaFullFixedCoordinates.sourceGroup_isPPrime
        K U hU hK)
      (sourceNormalCharacter K P theta U)
      sourceExtension hsourceExtension
      hsourceExtensionInvariant
      (OkuyamaWajimaFullFixedOuterCommutativity.source_quotient_action_trivial
        K P U hcentral)
      htargetInvariant
      (OkuyamaWajimaFullFixedCoordinates.sourceNormal_index_eq_fixedNormalSubgroup_index
        (P : Subgroup G) K U P.isPGroup' hK hcentral hfixedU)

/-- The complete inner reverse step in ambient target coordinates.

Starting from a global extension of `theta`, this theorem chooses the two
action Glauberman correspondences, applies the reverse maximal-fibre
theorem on `U K`, identifies its base character with the supplied
ordinary correspondent, and transports the resulting extension from the
literal fixed group to `U`. -/
theorem exists_phiExtensionToSelected
    (hK : IsPPrimeGroup p K)
    (hU : IsPPrimeGroup p U)
    (hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U)
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p) :
    letI : MulDistribMulAction P (U ⊔ K : Subgroup G) :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        (P : Subgroup G) (U ⊔ K)
          (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
            (P : Subgroup G) K U hcentral)
    letI : MulDistribMulAction P
        (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
        (P : Subgroup G) K U
    let N :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormal K U
    letI : N.Normal :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormal_normal K U
    IsMulCommutative ((U ⊔ K : Subgroup G) ⧸ N) →
      OkuyamaWajimaProperBranchThetaExtendsToG
          K P theta hinvariant →
        ∃ eta : IrreducibleCharacter U,
          IrreducibleCharacter.IsExtensionAlong
            (Subgroup.inclusion hfixedU)
            (gP.characterEquiv theta).1 eta := by
  letI : MulDistribMulAction P (U ⊔ K : Subgroup G) :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      (P : Subgroup G) (U ⊔ K)
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          (P : Subgroup G) K U hcentral)
  letI : MulDistribMulAction P
      (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      (P : Subgroup G) K U
  let N :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal K U
  letI : N.Normal :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal_normal K U
  dsimp only
  intro hcomm hsource
  have hSourceGroup :
      IsPPrimeGroup p (U ⊔ K : Subgroup G) :=
    OkuyamaWajimaFullFixedCoordinates.sourceGroup_isPPrime
      K U hU hK
  have hNormalGroup : IsPPrimeGroup p N :=
    hK.of_equiv (sourceNormalEquiv K U).symm
  let dSource :
      ActionGlaubermanCorrespondence
        P (U ⊔ K : Subgroup G) p :=
    Classical.choice
      (actionGlaubermanCorrespondenceOfPGroup
        cyclicStrongActionGlaubermanHypothesis
        P (U ⊔ K : Subgroup G) P.isPGroup' hSourceGroup)
  let dNormal :
      ActionGlaubermanCorrespondence P N p :=
    Classical.choice
      (actionGlaubermanCorrespondenceOfPGroup
        cyclicStrongActionGlaubermanHypothesis
        P N P.isPGroup' hNormalGroup)
  obtain ⟨etaFixed, hetaFixed⟩ :=
    exists_fixedTargetExtension
      K P theta hinvariant U hK hU hcentral hfixedU
      dSource dNormal hcomm
      (fixedNormalCorrespondent_invariant
        K P theta U hcentral hinvariant hfixedU gP dNormal)
      hsource
  let eG :=
    OkuyamaWajimaFullFixedCoordinates.sourceFixedPointsEquiv
      (P : Subgroup G) K U hcentral hfixedU
  let eF :=
    OkuyamaWajimaFullFixedTargetTransport.fixedNormalSubgroupEquivAmbientFixedPoints
      (P : Subgroup G) K U hcentral hfixedU
  let eta : IrreducibleCharacter U :=
    etaFixed.comap eG.symm
  refine ⟨eta, ?_⟩
  apply
    (OkuyamaWajimaFullFixedTargetTransport.isExtensionAlong_fixedPairEquiv_iff
      (P : Subgroup G) K U hcentral hfixedU
      (gP.characterEquiv theta).1 eta).mp
  have hcoordinate :=
    fixedNormalCorrespondent_eq_phi_comap
      K P theta U hcentral hfixedU gP dNormal
  rw [hcoordinate] at hetaFixed
  simpa [eta, eG, eF] using hetaFixed

/-- Ambient commutator containment supplies the remaining commutative
source-quotient hypothesis.  This is the convenient entry point for the
canonical Gorenstein-selected subgroup. -/
theorem exists_phiExtensionToSelected_of_commutator
    (hK : IsPPrimeGroup p K)
    (hKP : (K ⊔ (P : Subgroup G)).Normal)
    (hU : IsPPrimeGroup p U)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U)
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G))
    (hsource :
      OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant) :
    ∃ eta : IrreducibleCharacter U,
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion hfixedU)
        (gP.characterEquiv theta).1 eta := by
  letI : MulDistribMulAction P (U ⊔ K : Subgroup G) :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      (P : Subgroup G) (U ⊔ K)
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          (P : Subgroup G) K U hcentral)
  letI : MulDistribMulAction P
      (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      (P : Subgroup G) K U
  let N :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal K U
  letI : N.Normal :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal_normal K U
  exact
    exists_phiExtensionToSelected
      K P theta hinvariant U hK hU hcentral hfixedU gP
      (OkuyamaWajimaFullFixedOuterCommutativity.source_quotient_isMulCommutative
        K P hK hKP U hUM hcommutativeQuotient)
      hsource

/-! ## Complement-equivariant target extensions -/

/-- Conjugation by `M` on a subgroup `U ◁ M`, expressed on the ambient
subgroup types used by the cyclic-extension API. -/
def targetConjugationAction
    (M U : Subgroup G)
    (hUM : U ≤ M)
    (hUnormal : (U.subgroupOf M).Normal) :
    M →* MulAut U :=
  U.normalizerMonoidHom.comp
    (Subgroup.inclusion (by
      rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hUM]
      exact hUnormal))

@[simp]
theorem targetConjugationAction_apply_coe
    (M U : Subgroup G)
    (hUM : U ≤ M)
    (hUnormal : (U.subgroupOf M).Normal)
    (m : M) (u : U) :
    ((targetConjugationAction M U hUM hUnormal m u : U) : G) =
      (m : G) * (u : G) * (m : G)⁻¹ :=
  rfl

/-- An extension on `U` which is invariant under the whole complement
`M`.  This is the exact input consumed by cyclic target ascent. -/
def HasInvariantTargetExtension
    (M U : Subgroup G)
    (hUM : U ≤ M)
    (hUnormal : (U.subgroupOf M).Normal)
    (hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U)
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p) :
    Prop :=
  ∃ eta : IrreducibleCharacter U,
    IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion hfixedU)
        (gP.characterEquiv theta).1 eta ∧
      ∀ (m : M) (u : U),
        eta.values
            (targetConjugationAction M U hUM hUnormal m u) =
          eta.values u

/-- Equivariant strengthening of the reverse inner step.

The 13.29 fibre equivalence is evaluated at the restriction of the
global source extension.  Ambient normality of `U K` makes that source
character invariant under the complement.  Strong Glauberman
equivariance then makes its target image invariant as well.  The same
maximal-fibre cardinality calculation used above shows that this
particular target image, rather than merely some target character, is
an extension. -/
theorem exists_invariant_phiExtensionToSelected_of_commutator
    (hK : IsPPrimeGroup p K)
    (hKP : (K ⊔ (P : Subgroup G)).Normal)
    (U : Subgroup G)
    (hU : IsPPrimeGroup p U)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hUnormal :
      (U.subgroupOf
        (okuyamaWajimaProperBranchComplement
          K P hK hKP)).Normal)
    (hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U)
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G))
    (hsource :
      OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant) :
    HasInvariantTargetExtension
      K P theta
      (okuyamaWajimaProperBranchComplement K P hK hKP)
      U hUM hUnormal hfixedU gP := by
  let M :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  let A : Subgroup G := U ⊔ K
  letI : MulDistribMulAction P A :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      (P : Subgroup G) A
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          (P : Subgroup G) K U hcentral)
  letI : MulDistribMulAction P
      (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      (P : Subgroup G) K U
  let N :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal K U
  letI : N.Normal :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal_normal K U
  have hA : IsPPrimeGroup p A :=
    OkuyamaWajimaFullFixedCoordinates.sourceGroup_isPPrime
      K U hU hK
  have hN : IsPPrimeGroup p N :=
    hK.of_equiv (sourceNormalEquiv K U).symm
  obtain ⟨dStrong⟩ :=
    strongActionGlaubermanCorrespondenceOfPGroup
      cyclicStrongActionGlaubermanHypothesis
      P A P.isPGroup' hA
  let dSource : ActionGlaubermanCorrespondence P A p :=
    dStrong.toAction
  obtain ⟨dNormal⟩ :=
    actionGlaubermanCorrespondenceOfPGroup
      cyclicStrongActionGlaubermanHypothesis
      P N P.isPGroup' hN
  let hsmul :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction_compatible
      (P : Subgroup G) K U hcentral
  let thetaN :=
    sourceNormalCharacter K P theta U
  let F :=
    IsaacsGlaubermanRestriction.fixedNormalSubgroup
      (S := P) (G := A) N
  let fixedCorr :=
    IsaacsGlaubermanRestriction.fixedNormalCorrespondent
      N hsmul dNormal thetaN
  have hsourceNormal : A.Normal :=
    OkuyamaWajimaFullFixedSourceNormality.source_normal
      K P hK hKP U hUM hUnormal hcentral
  letI : A.Normal := hsourceNormal
  obtain ⟨sourceExtension, hsourceExtension,
      hsourcePInvariant, hsourceAmbientInvariant⟩ :=
    exists_ambientInvariant_sourceExtension
      K P theta hinvariant U hcentral hsourceNormal hsource
  let sourceOver :
      IrreducibleCharactersOverAlong N.subtype thetaN.1.1 :=
    ⟨sourceExtension, hsourceExtension.liesOver⟩
  let sourceInvariant :
      IsaacsGlaubermanRestriction.InvariantCharactersOver N thetaN :=
    ⟨sourceOver, hsourcePInvariant⟩
  let hisaacs :=
    IsaacsGlaubermanRestrictionReduction.isaacsGlaubermanRestrictionInput
      N hsmul dSource dNormal
  let targetOver :=
    IsaacsGlaubermanRestriction.invariantCharactersOverEquiv
      N hsmul dSource dNormal hisaacs
      P.isPGroup' hA thetaN sourceInvariant
  let etaFixed : IrreducibleCharacter (FixedPoints.subgroup P A) :=
    targetOver.1
  have hcomm :
      IsMulCommutative (A ⧸ N) :=
    OkuyamaWajimaFullFixedOuterCommutativity.source_quotient_isMulCommutative
      K P hK hKP U hUM hcommutativeQuotient
  letI : IsMulCommutative (A ⧸ N) := hcomm
  have hsourceCard :
      Nat.card
          (IrreducibleCharactersOverAlong
            N.subtype thetaN.1.1) =
        N.index := by
    calc
      Nat.card
            (IrreducibleCharactersOverAlong
              N.subtype thetaN.1.1) =
          Nat.card (IrreducibleCharacter (A ⧸ N)) :=
        (Nat.card_congr
          (IrreducibleCharacter.gallagherCorrespondence
            hsourceExtension)).symm
      _ = Nat.card (A ⧸ N) :=
        natCard_irreducibleCharacter_eq_card_of_isMulCommutative
          (A ⧸ N)
      _ = N.index := by
        rw [N.index_eq_card]
  have hallSourceInvariant :
      ∀ chi :
          IrreducibleCharactersOverAlong
            N.subtype thetaN.1.1,
        ∀ (s : P) (a : A),
          chi.1.values (s • a) = chi.1.values a := by
    intro chi s a
    exact
      IsaacsGlaubermanRestriction.forall_source_liesOver_values_invariant_of_fixedExtension_of_quotientActionTrivial
        N thetaN sourceExtension hsourceExtension
        hsourcePInvariant
        (OkuyamaWajimaFullFixedOuterCommutativity.source_quotient_action_trivial
          K P U hcentral)
        chi s a
  let sourceInvariantEquiv :
      IsaacsGlaubermanRestriction.InvariantCharactersOver N thetaN ≃
        IrreducibleCharactersOverAlong
          N.subtype thetaN.1.1 :=
    { toFun := fun chi ↦ chi.1
      invFun := fun chi ↦ ⟨chi, hallSourceInvariant chi⟩
      left_inv := fun chi ↦ by
        apply Subtype.ext
        rfl
      right_inv := fun _chi ↦ rfl }
  have hindex :
      N.index = F.index :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal_index_eq_fixedNormalSubgroup_index
      (P : Subgroup G) K U P.isPGroup' hK hcentral hfixedU
  have htargetCard :
      Nat.card
          (IrreducibleCharactersOverAlong
            F.subtype fixedCorr.1) =
        F.index := by
    calc
      Nat.card
            (IrreducibleCharactersOverAlong
              F.subtype fixedCorr.1) =
          Nat.card
            (IsaacsGlaubermanRestriction.InvariantCharactersOver
              N thetaN) :=
        (IsaacsGlaubermanRestriction.natCard_invariantCharactersOver_eq
          N hsmul dSource dNormal hisaacs
          P.isPGroup' hA thetaN).symm
      _ =
          Nat.card
            (IrreducibleCharactersOverAlong
              N.subtype thetaN.1.1) :=
        Nat.card_congr sourceInvariantEquiv
      _ = N.index := hsourceCard
      _ = F.index := hindex
  have hfixedCorrInvariant :
      ∀ g : FixedPoints.subgroup P A,
        g • fixedCorr.1 = fixedCorr.1 :=
    fixedNormalCorrespondent_invariant
      K P theta U hcentral hinvariant hfixedU gP dNormal
  have hetaFixed :
      IrreducibleCharacter.IsExtension
        F fixedCorr.1 etaFixed :=
    isExtension_of_natCard_over_eq_index
      F fixedCorr.1 hfixedCorrInvariant htargetCard targetOver
  let eG :=
    OkuyamaWajimaFullFixedCoordinates.sourceFixedPointsEquiv
      (P : Subgroup G) K U hcentral hfixedU
  let eF :=
    OkuyamaWajimaFullFixedTargetTransport.fixedNormalSubgroupEquivAmbientFixedPoints
      (P : Subgroup G) K U hcentral hfixedU
  let eta : IrreducibleCharacter U :=
    etaFixed.comap eG.symm
  have heta :
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion hfixedU)
        (gP.characterEquiv theta).1 eta := by
    apply
      (OkuyamaWajimaFullFixedTargetTransport.isExtensionAlong_fixedPairEquiv_iff
        (P : Subgroup G) K U hcentral hfixedU
        (gP.characterEquiv theta).1 eta).mp
    have hcoordinate :=
      fixedNormalCorrespondent_eq_phi_comap
        K P theta U hcentral hfixedU gP dNormal
    rw [hcoordinate] at hetaFixed
    simpa [eta, eG, eF] using hetaFixed
  refine ⟨eta, heta, ?_⟩
  intro m u
  have hM :
      M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    okuyamaWajimaAmbientComplement_le_normalizer
      P K hK hKP
  let mNormalizer :
      Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    ⟨m, hM m.property⟩
  let eP : P ≃* P :=
    (P : Subgroup G).normalizerMonoidHom mNormalizer
  let eA : A ≃* A :=
    MulAut.conjNormal (H := A) (m : G)
  have hequivariant :
      ∀ q : P, ∀ a : A,
        eA (q • a) = eP q • eA a := by
    intro q a
    apply Subtype.ext
    change
      (m : G) *
            ((q : G) * (a : G) * (q : G)⁻¹) *
          (m : G)⁻¹ =
        ((m : G) * (q : G) * (m : G)⁻¹) *
            ((m : G) * (a : G) * (m : G)⁻¹) *
          ((m : G) * (q : G) * (m : G)⁻¹)⁻¹
    group
  let sourceActionCharacter :=
    (IsaacsGlaubermanRestriction.invariantCharactersOverEquivInvariantPPrime
      N hA thetaN sourceInvariant).1
  have hsourceTransport :
      actionInvariantPPrimeIrreducibleCharacterEquivOfEquivariant
          (p := p) P P A A eP eA hequivariant
          sourceActionCharacter =
        sourceActionCharacter := by
    apply Subtype.ext
    apply Subtype.ext
    apply IrreducibleCharacter.ext
    funext a
    exact hsourceAmbientInvariant (m : G) a
  let eFixed :=
    actionFixedPointsEquivOfEquivariant
      P P A A eP eA hequivariant
  have hstrongEquivariant :=
    dStrong.characterEquiv_equivariant
      P A eP eA hequivariant sourceActionCharacter
  rw [hsourceTransport] at hstrongEquivariant
  have hstrongFixed :
      (dStrong.characterEquiv sourceActionCharacter).1.comap eFixed =
        (dStrong.characterEquiv sourceActionCharacter).1 := by
    exact
      (congrArg Subtype.val hstrongEquivariant).symm
  have hetaCoordinate :
      etaFixed =
        (dStrong.characterEquiv sourceActionCharacter).1 := by
    exact
      IsaacsGlaubermanRestriction.invariantCharactersOverEquiv_apply_coe
        N hsmul dSource dNormal hisaacs
        P.isPGroup' hA thetaN sourceInvariant
  have hetaFixedInvariant :
      etaFixed.values (eFixed (eG.symm u)) =
        etaFixed.values (eG.symm u) := by
    rw [hetaCoordinate]
    have hvalue :=
      congrArg
        (fun chi : IrreducibleCharacter (FixedPoints.subgroup P A) ↦
          chi.values (eG.symm u))
        hstrongFixed
    simpa using hvalue
  have htargetCoordinate :
      eFixed (eG.symm u) =
        eG.symm
          (targetConjugationAction M U hUM hUnormal m u) := by
    apply Subtype.ext
    rfl
  change
    etaFixed.values
        (eG.symm
          (targetConjugationAction M U hUM hUnormal m u)) =
      etaFixed.values (eG.symm u)
  rw [← htargetCoordinate]
  exact hetaFixedInvariant

/-- The canonical full-fixed reverse inner step.

For the subgroup selected by the Gorenstein cyclic-quotient datum, full
fixedness automatically supplies Burnside centralization.  The canonical
complement supplies `p'`-ness and the containment of `C_K(P)`, while the
ambient commutator hypothesis supplies quotient commutativity.  Hence a
global extension of `theta` restricts, through the reverse
Okuyama--Wajima comparison, to an extension of its Glauberman
correspondent on the selected subgroup. -/
theorem exists_phiExtensionToCanonicalSelected
    (hK : IsPPrimeGroup p K)
    (hKP : (K ⊔ (P : Subgroup G)).Normal)
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G))
    (hsource :
      OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant) :
    let M :=
      okuyamaWajimaProperBranchComplement K P hK hKP
    let hM :
        M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
      okuyamaWajimaAmbientComplement_le_normalizer
        P K hK hKP
    letI : MulDistribMulAction M P :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        M P hM
    let L := okuyamaWajimaActionKernel M P
    ∀ (d : OkuyamaWajimaCyclicQuotientSubgroup M P L)
      (hfull : d.fixedPoints = ⊤),
      let U :=
        OkuyamaWajimaFullFixedCoordinates.ambientSelectedSubgroup
          M P hM d
      let hfixedU :
          K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U :=
        OkuyamaWajimaFullFixedCoordinates.fixedPoints_le_ambientSelectedSubgroup
          M P hM d K
            (fixedPoints_le_okuyamaWajimaAmbientComplement
              P K hK hKP)
            rfl
      ∃ eta : IrreducibleCharacter U,
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion hfixedU)
          (gP.characterEquiv theta).1 eta := by
  let M : Subgroup G :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  let hM :
      M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    okuyamaWajimaAmbientComplement_le_normalizer
      P K hK hKP
  letI : MulDistribMulAction M P :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      M P hM
  let L := okuyamaWajimaActionKernel M P
  dsimp only
  intro d hfull
  let U :=
    OkuyamaWajimaFullFixedCoordinates.ambientSelectedSubgroup
      M P hM d
  have hMPrime : IsPPrimeGroup p M :=
    okuyamaWajimaAmbientComplement_isPPrimeGroup
      K P hK hKP
  have hBurnside :
      OkuyamaWajimaFullFixedCoordinates.FullFixedCoprimeCentralizationInput
        M P hM d P.isPGroup' hMPrime hfull :=
    OkuyamaWajimaFullFixedCoordinates.fullFixedCoprimeCentralizationInput_automatic
      M P hM d P.isPGroup' hMPrime hfull
  have hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G) :=
    OkuyamaWajimaFullFixedCoordinates.ambientSelectedSubgroup_le_centralizer
      M P hM d P.isPGroup' hMPrime hfull hBurnside
  have hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U :=
    OkuyamaWajimaFullFixedCoordinates.fixedPoints_le_ambientSelectedSubgroup
      M P hM d K
        (fixedPoints_le_okuyamaWajimaAmbientComplement
          P K hK hKP)
        rfl
  exact
    exists_phiExtensionToSelected_of_commutator
      K P theta hinvariant U hK hKP
      (OkuyamaWajimaFullFixedCoordinates.ambientSelectedSubgroup_isPPrime
        M P hM d hMPrime)
      (OkuyamaWajimaFullFixedCoordinates.ambientSelectedSubgroup_le_M
        M P hM d)
      hcentral hfixedU gP hcommutativeQuotient hsource

/-! ## Cyclic and Navarro outer ascent -/

/-- Cyclic target ascent from `U` to `M`.

This theorem shows that `HasInvariantTargetExtension` is the exact
intermediate package needed here: normality, cyclicity, and composition
of the two extension maps are all automatic. -/
theorem exists_phiExtensionToComplement_of_invariantTarget
    (M U : Subgroup G)
    (hUM : U ≤ M)
    (hUnormal : (U.subgroupOf M).Normal)
    (hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U)
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (hcyclic : IsCyclic (M ⧸ U.subgroupOf M))
    (hselected :
      HasInvariantTargetExtension
        K P theta M U hUM hUnormal hfixedU gP) :
    ∃ eta : IrreducibleCharacter M,
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion (hfixedU.trans hUM))
        (gP.characterEquiv theta).1 eta := by
  let f : U →* M :=
    Subgroup.inclusion hUM
  have hf : Function.Injective f :=
    Subgroup.inclusion_injective hUM
  have hnormalRange : f.range.Normal := by
    rw [Subgroup.inclusion_range]
    exact hUnormal
  have hcyclicRange : IsCyclic (M ⧸ f.range) := by
    exact
      (QuotientGroup.quotientMulEquivOfEq
        (Subgroup.inclusion_range hUM)).isCyclic.mpr
          hcyclic
  obtain ⟨etaU, hetaU, hetaUInvariant⟩ := hselected
  obtain ⟨etaM, hetaM⟩ :=
    IrreducibleCharacter.exists_extensionAlong_of_injective_cyclic_range
      f hf hnormalRange hcyclicRange
      (targetConjugationAction M U hUM hUnormal)
      (fun m u => by
        apply Subtype.ext
        rfl)
      etaU hetaUInvariant
  have hcomposite :
      f.comp (Subgroup.inclusion hfixedU) =
        Subgroup.inclusion (hfixedU.trans hUM) := by
    ext x
    rfl
  refine ⟨etaM, ?_⟩
  rw [← hcomposite]
  exact hetaM.trans hetaU

/-- Navarro target ascent from the canonical ambient complement to the
full Sylow normalizer.

The existing target-side deletion theorem performs the prime-power
ascent.  The only coordinate calculation here is that `P` together with
the canonical complement generates `N_G(P)`. -/
theorem okuyamaWajimaFullFixedPhi_extendsToPNormalizer_of_complementExtension
    (hK : IsPPrimeGroup p K)
    (hKP : (K ⊔ (P : Subgroup G)).Normal)
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (eta :
      IrreducibleCharacter
        (okuyamaWajimaProperBranchComplement K P hK hKP))
    (heta :
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion
          (fixedPoints_le_okuyamaWajimaAmbientComplement
            P K hK hKP))
        (gP.characterEquiv theta).1 eta) :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
      K P theta hinvariant gP := by
  let M : Subgroup G :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  have hM :
      M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    okuyamaWajimaAmbientComplement_le_normalizer
      P K hK hKP
  have hfixedM :
      coprimeFixedPoints K (P : Subgroup G) ≤ M :=
    fixedPoints_le_okuyamaWajimaAmbientComplement
      P K hK hKP
  have hPM :
      (P : Subgroup G) ⊔ M =
        Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    apply le_antisymm
    · exact sup_le Subgroup.le_normalizer hM
    · rw [←
        fixedPoints_sup_sylow_sup_ambientComplement_eq_normalizer
          P K hK hKP]
      exact sup_le
        (sup_le (hfixedM.trans le_sup_right) le_sup_left)
        le_sup_right
  have hPMExtension :
      ∃ psi :
          IrreducibleCharacter
            ((P : Subgroup G) ⊔ M : Subgroup G),
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion (hfixedM.trans le_sup_right))
          (gP.characterEquiv theta).1 psi :=
    (invariantOkuyamaWajimaTarget_adjoinQ_extension_iff
      (K := K) (Q := (P : Subgroup G)) (W := M)
      P.isPGroup' hK hM hfixedM gP theta hinvariant).mp
        ⟨eta, heta⟩
  apply
    (okuyamaWajimaProperBranchPhi_extendsToPNormalizer_iff
      K P theta hinvariant gP).mpr
  exact
    (IrreducibleCharacter.exists_extensionAlong_inclusion_congr
      (coprimeFixedPoints K (P : Subgroup G))
      ((P : Subgroup G) ⊔ M)
      (Subgroup.normalizer ((P : Subgroup G) : Set G))
      (hfixedM.trans le_sup_right)
      (inf_le_right.trans
        (Subgroup.centralizer_le_normalizer
          ((P : Subgroup G) : Set G)))
      hPM
      (gP.characterEquiv theta).1).mp
        hPMExtension

/-- Once the selected extension is known to be complement-invariant,
the canonical cyclic quotient and Navarro ascent complete the reverse
outer implication. -/
theorem okuyamaWajimaFullFixed_target_of_invariantCanonicalSelected
    (hK : IsPPrimeGroup p K)
    (hKP : (K ⊔ (P : Subgroup G)).Normal)
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p) :
    let M :=
      okuyamaWajimaProperBranchComplement K P hK hKP
    let hM :
        M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
      okuyamaWajimaAmbientComplement_le_normalizer
        P K hK hKP
    letI : MulDistribMulAction M P :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        M P hM
    let L := okuyamaWajimaActionKernel M P
    ∀ (d : OkuyamaWajimaCyclicQuotientSubgroup M P L),
      let U :=
        OkuyamaWajimaFullFixedCoordinates.ambientSelectedSubgroup
          M P hM d
      let hUM :
          U ≤ M :=
        OkuyamaWajimaFullFixedCoordinates.ambientSelectedSubgroup_le_M
          M P hM d
      let hUnormal :
          (U.subgroupOf M).Normal :=
        OkuyamaWajimaFullFixedOuterCoordinates.ambientSelectedSubgroup_normal_in_M
          M P hM d
      let hfixedU :
          K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U :=
        OkuyamaWajimaFullFixedCoordinates.fixedPoints_le_ambientSelectedSubgroup
          M P hM d K
            (fixedPoints_le_okuyamaWajimaAmbientComplement
              P K hK hKP)
            rfl
      HasInvariantTargetExtension
          K P theta M U hUM hUnormal hfixedU gP →
        OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
          K P theta hinvariant gP := by
  let M :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  let hM :
      M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    okuyamaWajimaAmbientComplement_le_normalizer
      P K hK hKP
  letI : MulDistribMulAction M P :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      M P hM
  let L := okuyamaWajimaActionKernel M P
  dsimp only
  intro d hselected
  let U :=
    OkuyamaWajimaFullFixedCoordinates.ambientSelectedSubgroup
      M P hM d
  have hUM : U ≤ M :=
    OkuyamaWajimaFullFixedCoordinates.ambientSelectedSubgroup_le_M
      M P hM d
  have hUnormal : (U.subgroupOf M).Normal :=
    OkuyamaWajimaFullFixedOuterCoordinates.ambientSelectedSubgroup_normal_in_M
      M P hM d
  have hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U :=
    OkuyamaWajimaFullFixedCoordinates.fixedPoints_le_ambientSelectedSubgroup
      M P hM d K
        (fixedPoints_le_okuyamaWajimaAmbientComplement
          P K hK hKP)
        rfl
  have hdenominator :
      U.subgroupOf M = d.U.toSubgroup := by
    simpa only [U,
      OkuyamaWajimaFullFixedOuterCoordinates.selectedSubgroupInM] using
      OkuyamaWajimaFullFixedOuterCoordinates.ambientSelectedSubgroup_subgroupOf_M_eq
        M P hM d
  have hcyclic :
      IsCyclic (M ⧸ U.subgroupOf M) :=
    (QuotientGroup.quotientMulEquivOfEq
      hdenominator).isCyclic.mpr d.quotient_isCyclic
  obtain ⟨etaM, hetaM⟩ :=
    exists_phiExtensionToComplement_of_invariantTarget
      K P theta M U hUM hUnormal hfixedU gP hcyclic hselected
  apply
    okuyamaWajimaFullFixedPhi_extendsToPNormalizer_of_complementExtension
      K P theta hinvariant hK hKP gP etaM
  simpa using hetaM

/-- Complete canonical reverse implication in the full-fixed branch.

Full fixedness supplies Burnside centralization of the canonical selected
subgroup.  The equivariant 13.29 construction then gives an
`M`-invariant extension of the Glauberman correspondent on that subgroup;
the canonical cyclic quotient extends it to `M`, and Navarro target
deletion extends it to `N_G(P)`. -/
theorem okuyamaWajimaFullFixed_target_of_source
    (hK : IsPPrimeGroup p K)
    (hKP : (K ⊔ (P : Subgroup G)).Normal)
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G))
    (hsource :
      OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant) :
    let M :=
      okuyamaWajimaProperBranchComplement K P hK hKP
    let hM :
        M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
      okuyamaWajimaAmbientComplement_le_normalizer
        P K hK hKP
    letI : MulDistribMulAction M P :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        M P hM
    let L := okuyamaWajimaActionKernel M P
    ∀ (d : OkuyamaWajimaCyclicQuotientSubgroup M P L),
      d.fixedPoints = ⊤ →
        OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
          K P theta hinvariant gP := by
  let M :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  let hM :
      M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    okuyamaWajimaAmbientComplement_le_normalizer
      P K hK hKP
  letI : MulDistribMulAction M P :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      M P hM
  let L := okuyamaWajimaActionKernel M P
  dsimp only
  intro d hfull
  let U :=
    OkuyamaWajimaFullFixedCoordinates.ambientSelectedSubgroup
      M P hM d
  have hMPrime : IsPPrimeGroup p M :=
    okuyamaWajimaAmbientComplement_isPPrimeGroup
      K P hK hKP
  have hBurnside :
      OkuyamaWajimaFullFixedCoordinates.FullFixedCoprimeCentralizationInput
        M P hM d P.isPGroup' hMPrime hfull :=
    OkuyamaWajimaFullFixedCoordinates.fullFixedCoprimeCentralizationInput_automatic
      M P hM d P.isPGroup' hMPrime hfull
  have hUM : U ≤ M :=
    OkuyamaWajimaFullFixedCoordinates.ambientSelectedSubgroup_le_M
      M P hM d
  have hUnormal : (U.subgroupOf M).Normal :=
    OkuyamaWajimaFullFixedOuterCoordinates.ambientSelectedSubgroup_normal_in_M
      M P hM d
  have hU : IsPPrimeGroup p U :=
    OkuyamaWajimaFullFixedCoordinates.ambientSelectedSubgroup_isPPrime
      M P hM d hMPrime
  have hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G) :=
    OkuyamaWajimaFullFixedCoordinates.ambientSelectedSubgroup_le_centralizer
      M P hM d P.isPGroup' hMPrime hfull hBurnside
  have hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U :=
    OkuyamaWajimaFullFixedCoordinates.fixedPoints_le_ambientSelectedSubgroup
      M P hM d K
        (fixedPoints_le_okuyamaWajimaAmbientComplement
          P K hK hKP)
        rfl
  have hselected :
      HasInvariantTargetExtension
        K P theta M U hUM hUnormal hfixedU gP :=
    exists_invariant_phiExtensionToSelected_of_commutator
      K P theta hinvariant hK hKP U hU hUM hUnormal
      hcentral hfixedU gP hcommutativeQuotient hsource
  exact
    okuyamaWajimaFullFixed_target_of_invariantCanonicalSelected
      K P theta hinvariant hK hKP gP d hselected

end SourceCoordinates

end OkuyamaWajimaFullFixedOuterReverse

end McKayConjecture
