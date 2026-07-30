/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaFullFixedOuterCommutativity
import McKayConjecture.Character.OkuyamaWajimaFullFixedGlaubermanTransport
import McKayConjecture.Character.OkuyamaWajimaFullFixedSourceNormality
import McKayConjecture.Character.GlaubermanEquivariance
import McKayConjecture.Character.OkuyamaWajimaPrintedInduction

/-!
# Forward outer assembly in the full-fixed Okuyama--Wajima branch

This file isolates and proves the two outer steps in the forward
full-fixed implication.

* An `M K`-invariant extension of `theta` to `U K` extends across
  `U K ◁ M K`, because `(M K) / (U K)` is cyclic.
* An extension to the canonical middle subgroup `M K` ascends to `G`,
  because `[G : M K]` is a power of `p` and Navarro's
  prime-power-index theorem applies.

For any selected `U` satisfying the full-fixed group coordinates, the
character-theoretic chain is automatic.  Restricting a target extension,
transporting the target correspondent, taking the inverse Isaacs 13.29
constituent, and Glauberman normalizer-equivariance produce an `M K`-fixed
source constituent.  Isaacs 13.29 upgrades it to an extension, after which
the cyclic and Navarro ascents finish the forward implication.
-/

noncomputable section

namespace McKayConjecture
namespace OkuyamaWajimaFullFixedOuterForward

open CharacterTriple
open CliffordCorrespondence
open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-! ## Cyclic ascent from `U K` to `M K` -/

section CyclicAscent

variable (K M U : Subgroup G) [K.Normal]
variable
  (hUM : U ≤ M)
  (hUnormal : (U.subgroupOf M).Normal)

/-- Conjugation by `M` on its normal subgroup `U`. -/
def targetConjugationAction :
    M →* MulAut U :=
  U.normalizerMonoidHom.comp
    (Subgroup.inclusion (by
      rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hUM]
      exact hUnormal))

omit [Finite G] in
@[simp]
theorem targetConjugationAction_apply_coe
    (m : M) (u : U) :
    ((targetConjugationAction M U hUM hUnormal m u : U) : G) =
      (m : G) * (u : G) * (m : G)⁻¹ :=
  rfl

/-- Conjugation by the middle group `M K` on its normal source subgroup
`U K`. -/
def middleConjugationAction :
    (M ⊔ K : Subgroup G) →*
      MulAut (U ⊔ K : Subgroup G) :=
  (U ⊔ K : Subgroup G).normalizerMonoidHom.comp
    (Subgroup.inclusion
      (sup_le
        (OkuyamaWajimaFullFixedOuterCoordinates.M_le_normalizer_source
          K M U hUM hUnormal)
        (le_sup_right.trans Subgroup.le_normalizer)))

@[simp]
theorem middleConjugationAction_apply_coe
    (m : (M ⊔ K : Subgroup G))
    (x : (U ⊔ K : Subgroup G)) :
    ((middleConjugationAction K M U hUM hUnormal m x :
        (U ⊔ K : Subgroup G)) : G) =
      (m : G) * (x : G) * (m : G)⁻¹ :=
  rfl

/-- The exact character-theoretic output needed from the inner
full-fixed/Isaacs step: an extension on `U K` which is invariant under
the full middle group `M K`.

The invariance field is deliberately stated for the literal
conjugation action used by the cyclic extension API. -/
def HasInvariantSourceExtension
    (theta : IrreducibleCharacter K) : Prop :=
  ∃ chi : IrreducibleCharacter (U ⊔ K : Subgroup G),
    IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion
          (show K ≤ U ⊔ K from le_sup_right))
        theta chi ∧
      ∀ (m : (M ⊔ K : Subgroup G))
        (x : (U ⊔ K : Subgroup G)),
        chi.values
            (middleConjugationAction
              K M U hUM hUnormal m x) =
          chi.values x

/-- Cyclic quotient ascent: an `M K`-invariant extension on `U K`
extends to `M K`, and the two extension equalities compose to show that
the resulting character extends the original character on `K`. -/
theorem exists_middle_extension_of_hasInvariantSourceExtension
    (theta : IrreducibleCharacter K)
    (hcyclic :
      letI :
          ((U ⊔ K : Subgroup G).subgroupOf
            (M ⊔ K : Subgroup G)).Normal :=
        OkuyamaWajimaFullFixedOuterCoordinates.source_normal_in_middle
          K M U hUM hUnormal
      IsCyclic
        ((M ⊔ K : Subgroup G) ⧸
          (U ⊔ K).subgroupOf (M ⊔ K : Subgroup G)))
    (hsource :
      HasInvariantSourceExtension
        K M U hUM hUnormal theta) :
    ∃ eta : IrreducibleCharacter (M ⊔ K : Subgroup G),
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion
          (show K ≤ M ⊔ K from le_sup_right))
        theta eta := by
  let A : Subgroup G := U ⊔ K
  let H : Subgroup G := M ⊔ K
  have hAH : A ≤ H :=
    OkuyamaWajimaFullFixedOuterCoordinates.source_le_middle
      K M U hUM
  have hnormal :
      (A.subgroupOf H).Normal :=
    OkuyamaWajimaFullFixedOuterCoordinates.source_normal_in_middle
      K M U hUM hUnormal
  letI : (A.subgroupOf H).Normal := hnormal
  let f : A →* H := Subgroup.inclusion hAH
  have hf : Function.Injective f :=
    Subgroup.inclusion_injective hAH
  have hfRange : f.range.Normal := by
    rw [Subgroup.inclusion_range]
    exact hnormal
  have hcyclicRange :
      IsCyclic (H ⧸ f.range) := by
    exact
      (QuotientGroup.quotientMulEquivOfEq
        (Subgroup.inclusion_range hAH)).isCyclic.mpr
          hcyclic
  obtain ⟨chi, hchi, hchiInvariant⟩ := hsource
  obtain ⟨eta, heta⟩ :=
    IrreducibleCharacter.exists_extensionAlong_of_injective_cyclic_range
      f hf hfRange hcyclicRange
      (middleConjugationAction K M U hUM hUnormal)
      (fun m x => by
        apply Subtype.ext
        rfl)
      chi hchiInvariant
  have hKA : K ≤ A := by
    exact le_sup_right
  have hKH : K ≤ H := by
    exact le_sup_right
  have hcomposite :
      f.comp (Subgroup.inclusion hKA) =
        Subgroup.inclusion hKH := by
    ext x
    rfl
  refine ⟨eta, ?_⟩
  rw [← hcomposite]
  exact heta.trans hchi

end CyclicAscent

/-! ## Navarro ascent from `M K` to `G` -/

section NavarroAscent

variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable
  (hK : IsPPrimeGroup p K)
  (hKP : (K ⊔ (P : Subgroup G)).Normal)

local instance fullFixedForwardPConjugationAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K (P : Subgroup G)

variable
  (theta :
    PInvariantPPrimeIrreducibleCharacter
      K (P : Subgroup G) p)
  (hinvariant :
    ∀ g : G, g • theta.1.1 = theta.1.1)

/-- The genuinely residual forward selection statement.

It asks only for a character of `U K` lying over the transported copy of
`theta` which is fixed by conjugation by `M K`.  It does **not** ask that
the selected character already be an extension: the automatic
full-fixed Isaacs 13.29 theorem proves that fact below. -/
def HasMiddleInvariantSourceOver
    (U :
      Subgroup G)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hUnormal :
      (U.subgroupOf
        (okuyamaWajimaProperBranchComplement
          K P hK hKP)).Normal)
    (hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G)) :
    Prop :=
  letI :
      MulDistribMulAction P ↥(U ⊔ K : Subgroup G) :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      (P : Subgroup G) (U ⊔ K)
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          (P : Subgroup G) K U hcentral)
  letI :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      (P : Subgroup G) K U
  let thetaN :=
    OkuyamaWajimaFullFixedSourceTransport.internalInvariantSourceCharacter
      (P : Subgroup G) K U theta
  ∃ chi :
      IrreducibleCharactersOverAlong
        (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U).subtype
        thetaN.1.1,
    ∀
      (m :
        (okuyamaWajimaProperBranchComplement
            K P hK hKP ⊔ K : Subgroup G))
      (x : (U ⊔ K : Subgroup G)),
      chi.1.values
          (middleConjugationAction
            K
            (okuyamaWajimaProperBranchComplement
              K P hK hKP)
            U hUM hUnormal m x) =
        chi.1.values x

/-- Restricting a normalizer extension to `U` gives an extension which
is fixed by conjugation by the whole complement `M`. -/
theorem exists_invariant_targetExtension_of_target
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (U :
      Subgroup G)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hUnormal :
      (U.subgroupOf
        (okuyamaWajimaProperBranchComplement
          K P hK hKP)).Normal)
    (hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U)
    (htarget :
      OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP) :
    ∃ etaU : IrreducibleCharacter U,
      IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion hfixedU)
          (gP.characterEquiv theta).1 etaU ∧
        ∀
          (m :
            okuyamaWajimaProperBranchComplement
              K P hK hKP)
          (u : U),
          etaU.values
              (targetConjugationAction
                (okuyamaWajimaProperBranchComplement
                  K P hK hKP)
                U hUM hUnormal m u) =
            etaU.values u := by
  obtain ⟨etaNormalizer, hetaNormalizer⟩ :=
    (okuyamaWajimaProperBranchPhi_extendsToPNormalizer_iff
      K P theta hinvariant gP).mp htarget
  have hUNormalizer :
      U ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    hUM.trans
      (okuyamaWajimaAmbientComplement_le_normalizer
        P K hK hKP)
  have hfixedNormalizer :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    inf_le_right.trans
      (Subgroup.centralizer_le_normalizer
        ((P : Subgroup G) : Set G))
  have hcomposite :
      (Subgroup.inclusion hUNormalizer).comp
          (Subgroup.inclusion hfixedU) =
        Subgroup.inclusion hfixedNormalizer := by
    ext x
    rfl
  have hetaNormalizer' :
      IrreducibleCharacter.IsExtensionAlong
        ((Subgroup.inclusion hUNormalizer).comp
          (Subgroup.inclusion hfixedU))
        (gP.characterEquiv theta).1 etaNormalizer := by
    rw [hcomposite]
    exact hetaNormalizer
  obtain ⟨etaU, hetaU, hetaNormalizerU⟩ :=
    IrreducibleCharacter.IsExtensionAlong.exists_intermediate
      hetaNormalizer'
  refine ⟨etaU, hetaU, ?_⟩
  intro m u
  rw [← hetaNormalizerU
      (targetConjugationAction
        (okuyamaWajimaProperBranchComplement
          K P hK hKP)
        U hUM hUnormal m u),
    ← hetaNormalizerU u]
  let mN :
      Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    ⟨m,
      (okuyamaWajimaAmbientComplement_le_normalizer
        P K hK hKP) m.property⟩
  let uN :
      Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    Subgroup.inclusion hUNormalizer u
  calc
    etaNormalizer.values
          (Subgroup.inclusion hUNormalizer
            (targetConjugationAction
              (okuyamaWajimaProperBranchComplement
                K P hK hKP)
              U hUM hUnormal m u)) =
        etaNormalizer.values (mN * uN * mN⁻¹) := by
          congr 1
    _ = etaNormalizer.values uN :=
      ClassFunction.conj_apply etaNormalizer.toClassFunction
        uN mN

/-- Restrict a normalizer extension of the ordinary Glauberman
correspondent to `U`, then transport it to the literal fixed-point pair
used by Isaacs 13.29.

The base-character equality is supplied by multiplicity uniqueness in
`fixedNormalCorrespondent_transport_eq`; no compatibility choice between
the ordinary and action-level correspondences is required. -/
theorem exists_fixedTargetExtension_of_target
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (U :
      Subgroup G)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U)
    (dN :
      letI :=
        OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
          (P : Subgroup G) K U
      ActionGlaubermanCorrespondence
        P
        (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U)
        p)
    (htarget :
      OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP) :
    letI :
        MulDistribMulAction P ↥(U ⊔ K : Subgroup G) :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        (P : Subgroup G) (U ⊔ K)
          (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
            (P : Subgroup G) K U hcentral)
    letI :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
        (P : Subgroup G) K U
    let N :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormal K U
    let thetaN :=
      OkuyamaWajimaFullFixedSourceTransport.internalInvariantSourceCharacter
        (P : Subgroup G) K U theta
    ∃ eta :
        IrreducibleCharacter
          (FixedPoints.subgroup P ↥(U ⊔ K : Subgroup G)),
      IrreducibleCharacter.IsExtension
        (IsaacsGlaubermanRestriction.fixedNormalSubgroup
          (S := P) (G := ↥(U ⊔ K : Subgroup G)) N)
        (IsaacsGlaubermanRestriction.fixedNormalCorrespondent
          N
          (OkuyamaWajimaFullFixedCoordinates.sourceNormalAction_compatible
            (P : Subgroup G) K U hcentral)
          dN thetaN).1 eta := by
  letI :
      MulDistribMulAction P ↥(U ⊔ K : Subgroup G) :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      (P : Subgroup G) (U ⊔ K)
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          (P : Subgroup G) K U hcentral)
  letI :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      (P : Subgroup G) K U
  let N :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal K U
  let thetaN :=
    OkuyamaWajimaFullFixedSourceTransport.internalInvariantSourceCharacter
      (P : Subgroup G) K U theta
  let fixedCorr :=
    IsaacsGlaubermanRestriction.fixedNormalCorrespondent
      N
      (OkuyamaWajimaFullFixedCoordinates.sourceNormalAction_compatible
        (P : Subgroup G) K U hcentral)
      dN thetaN
  let eF :=
    OkuyamaWajimaFullFixedTargetTransport.fixedNormalSubgroupEquivAmbientFixedPoints
      (P : Subgroup G) K U hcentral hfixedU
  let eU :=
    OkuyamaWajimaFullFixedCoordinates.sourceFixedPointsEquiv
      (P : Subgroup G) K U hcentral hfixedU
  obtain ⟨etaNormalizer, hetaNormalizer⟩ :=
    (okuyamaWajimaProperBranchPhi_extendsToPNormalizer_iff
      K P theta hinvariant gP).mp htarget
  have hUNormalizer :
      U ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    hUM.trans
      (okuyamaWajimaAmbientComplement_le_normalizer
        P K hK hKP)
  have hfixedNormalizer :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    inf_le_right.trans
      (Subgroup.centralizer_le_normalizer
        ((P : Subgroup G) : Set G))
  have hcomposite :
      (Subgroup.inclusion hUNormalizer).comp
          (Subgroup.inclusion hfixedU) =
        Subgroup.inclusion hfixedNormalizer := by
    ext x
    rfl
  have hetaNormalizer' :
      IrreducibleCharacter.IsExtensionAlong
        ((Subgroup.inclusion hUNormalizer).comp
          (Subgroup.inclusion hfixedU))
        (gP.characterEquiv theta).1 etaNormalizer := by
    rw [hcomposite]
    exact hetaNormalizer
  obtain ⟨etaU, hetaU, _hetaNormalizerU⟩ :=
    IrreducibleCharacter.IsExtensionAlong.exists_intermediate
      hetaNormalizer'
  have htransported :
      IrreducibleCharacter.IsExtensionAlong
        (IsaacsGlaubermanRestriction.fixedNormalSubgroup
          (S := P) (G := ↥(U ⊔ K : Subgroup G)) N).subtype
        ((gP.characterEquiv theta).1.comap eF)
        (etaU.comap eU) :=
    (OkuyamaWajimaFullFixedTargetTransport.isExtensionAlong_fixedPairEquiv_iff
      (P : Subgroup G) K U hcentral hfixedU
      (gP.characterEquiv theta).1 etaU).mpr hetaU
  have hcorrespondent :
      fixedCorr.1.comap eF.symm =
        (gP.characterEquiv theta).1 := by
    exact congrArg Subtype.val
      (OkuyamaWajimaFullFixedGlaubermanTransport.fixedNormalCorrespondent_transport_eq
        (P : Subgroup G) K U hcentral hfixedU theta gP dN)
  have hcorrespondentBack :
      (gP.characterEquiv theta).1.comap eF =
        fixedCorr.1 := by
    rw [← hcorrespondent]
    simp
  refine ⟨etaU.comap eU, ?_⟩
  simpa only [N, thetaN, fixedCorr, hcorrespondentBack] using
    htransported

/-- The automatic full-fixed Isaacs 13.29 theorem upgrades a chosen
middle-invariant source character from merely lying over `theta` to
being an actual extension.

All other hypotheses are group coordinates: the source is a `p'`-group,
the target quotient is commutative, and the two subgroup indices agree.
The normalizer extension is restricted and transported by
`exists_fixedTargetExtension_of_target`. -/
theorem hasInvariantSourceExtension_of_target_of_middleInvariantOver
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (U :
      Subgroup G)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hUnormal :
      (U.subgroupOf
        (okuyamaWajimaProperBranchComplement
          K P hK hKP)).Normal)
    (hU :
      IsPPrimeGroup p U)
    (hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G))
    (htarget :
      OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP)
    (hover :
      HasMiddleInvariantSourceOver
        K P hK hKP theta U hUM hUnormal hcentral) :
    HasInvariantSourceExtension
      K
      (okuyamaWajimaProperBranchComplement
        K P hK hKP)
      U hUM hUnormal theta.1.1 := by
  let A : Subgroup G := U ⊔ K
  let N :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal K U
  letI :
      MulDistribMulAction P A :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      (P : Subgroup G) A
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          (P : Subgroup G) K U hcentral)
  letI : MulDistribMulAction P N :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      (P : Subgroup G) K U
  let thetaN :=
    OkuyamaWajimaFullFixedSourceTransport.internalInvariantSourceCharacter
      (P : Subgroup G) K U theta
  have hA :
      IsPPrimeGroup p A :=
    OkuyamaWajimaFullFixedCoordinates.sourceGroup_isPPrime
      K U hU hK
  obtain ⟨dA⟩ :=
    actionGlaubermanCorrespondenceOfPGroup
      cyclicStrongActionGlaubermanHypothesis
      P A P.isPGroup' hA
  have hN :
      IsPPrimeGroup p N :=
    hA.to_subgroup N
  obtain ⟨dN⟩ :=
    actionGlaubermanCorrespondenceOfPGroup
      cyclicStrongActionGlaubermanHypothesis
      P N P.isPGroup' hN
  obtain ⟨etaTarget, hetaTarget⟩ :=
    exists_fixedTargetExtension_of_target
      K P hK hKP theta hinvariant gP U hUM hcentral hfixedU
      dN htarget
  letI :
      IsMulCommutative
        (FixedPoints.subgroup P A ⧸
          IsaacsGlaubermanRestriction.fixedNormalSubgroup
            (S := P) (G := A) N) :=
    OkuyamaWajimaFullFixedOuterCommutativity.fixed_target_quotient_isMulCommutative
      K P hK hKP U hUM hcentral hfixedU hcommutativeQuotient
  obtain ⟨chi, hchiInvariant⟩ := hover
  have hthetaNInvariant :
      ∀ a : A, a • thetaN.1.1 = thetaN.1.1 := by
    intro a
    apply IrreducibleCharacter.ext
    funext n
    let e :=
      OkuyamaWajimaFullFixedSourceTransport.sourceNormalEquivKernel
        K U
    have hvalue :=
      congrArg
        (fun eta : IrreducibleCharacter K ↦ eta.values (e n))
        (hinvariant (a : G))
    change
      theta.1.1.values
          ((MulAut.conjNormal (H := K) (a : G)).symm (e n)) =
        theta.1.1.values (e n) at hvalue
    exact hvalue
  have hchiExtension :
      IrreducibleCharacter.IsExtension
        N thetaN.1.1 chi.1 :=
    IsaacsGlaubermanRestriction.okuyamaWajimaFullFixed_isExtension_automatic
      N
      (OkuyamaWajimaFullFixedCoordinates.sourceNormalAction_compatible
        (P : Subgroup G) K U hcentral)
      dA dN P.isPGroup' hA thetaN hthetaNInvariant
      etaTarget hetaTarget
      (OkuyamaWajimaFullFixedCoordinates.sourceNormal_index_eq_fixedNormalSubgroup_index
        (P : Subgroup G) K U P.isPGroup' hK hcentral hfixedU)
      chi
  have hchiExternal :
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion
          (show K ≤ U ⊔ K from le_sup_right))
        theta.1.1 chi.1 := by
    apply
      (OkuyamaWajimaFullFixedSourceTransport.isExtensionAlong_sourceNormalEquiv_iff
        K U theta.1.1 chi.1).mp
    simpa only [N, thetaN,
      OkuyamaWajimaFullFixedSourceTransport.internalInvariantSourceCharacter_coe]
      using hchiExtension
  exact ⟨chi.1, hchiExternal, hchiInvariant⟩

/-- The inverse Isaacs 13.29 constituent selected by a restricted target
extension is invariant under the full middle group.

The proof uses one strong action correspondence on `U K`.  Ambient
normality turns it into the ordinary Glauberman correspondence for
`U K ◁ G`.  Normalizer-equivariance of that ordinary correspondence
transfers the `M`-invariance of the restricted target extension to its
inverse source correspondent.  Invariance under `K ≤ U K` is ordinary
class-function invariance. -/
theorem exists_middleInvariantSourceOver_of_target
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (U :
      Subgroup G)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hUnormal :
      (U.subgroupOf
        (okuyamaWajimaProperBranchComplement
          K P hK hKP)).Normal)
    (hU :
      IsPPrimeGroup p U)
    (hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U)
    (htarget :
      OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP) :
    HasMiddleInvariantSourceOver
      K P hK hKP theta U hUM hUnormal hcentral := by
  let A : Subgroup G := U ⊔ K
  let N :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal K U
  letI : A.Normal :=
    OkuyamaWajimaFullFixedSourceNormality.source_normal
      K P hK hKP U hUM hUnormal hcentral
  letI :
      MulDistribMulAction P A :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      (P : Subgroup G) A
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          (P : Subgroup G) K U hcentral)
  letI : MulDistribMulAction P N :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      (P : Subgroup G) K U
  let thetaN :=
    OkuyamaWajimaFullFixedSourceTransport.internalInvariantSourceCharacter
      (P : Subgroup G) K U theta
  have hA :
      IsPPrimeGroup p A :=
    OkuyamaWajimaFullFixedCoordinates.sourceGroup_isPPrime
      K U hU hK
  obtain ⟨dStrong⟩ :=
    strongActionGlaubermanCorrespondenceOfPGroup
      cyclicStrongActionGlaubermanHypothesis
      P A P.isPGroup' hA
  let dA : ActionGlaubermanCorrespondence P A p :=
    dStrong.toAction
  have hN :
      IsPPrimeGroup p N :=
    hA.to_subgroup N
  obtain ⟨dN⟩ :=
    actionGlaubermanCorrespondenceOfPGroup
      cyclicStrongActionGlaubermanHypothesis
      P N P.isPGroup' hN
  obtain ⟨etaU, hetaU, hetaUInvariant⟩ :=
    exists_invariant_targetExtension_of_target
      K P hK hKP theta hinvariant gP U hUM hUnormal
      hfixedU htarget
  let eU :=
    OkuyamaWajimaFullFixedCoordinates.sourceFixedPointsEquiv
      (P : Subgroup G) K U hcentral hfixedU
  let etaTarget : IrreducibleCharacter (FixedPoints.subgroup P A) :=
    etaU.comap eU
  let hsmul :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction_compatible
      (P : Subgroup G) K U hcentral
  let fixedCorr :=
    IsaacsGlaubermanRestriction.fixedNormalCorrespondent
      N hsmul dN thetaN
  let eF :=
    OkuyamaWajimaFullFixedTargetTransport.fixedNormalSubgroupEquivAmbientFixedPoints
      (P : Subgroup G) K U hcentral hfixedU
  have htransported :
      IrreducibleCharacter.IsExtensionAlong
        (IsaacsGlaubermanRestriction.fixedNormalSubgroup
          (S := P) (G := A) N).subtype
        ((gP.characterEquiv theta).1.comap eF)
        etaTarget :=
    (OkuyamaWajimaFullFixedTargetTransport.isExtensionAlong_fixedPairEquiv_iff
      (P : Subgroup G) K U hcentral hfixedU
      (gP.characterEquiv theta).1 etaU).mpr hetaU
  have hcorrespondent :
      fixedCorr.1.comap eF.symm =
        (gP.characterEquiv theta).1 := by
    exact congrArg Subtype.val
      (OkuyamaWajimaFullFixedGlaubermanTransport.fixedNormalCorrespondent_transport_eq
        (P : Subgroup G) K U hcentral hfixedU theta gP dN)
  have hcorrespondentBack :
      (gP.characterEquiv theta).1.comap eF =
        fixedCorr.1 := by
    rw [← hcorrespondent]
    simp
  have hetaTarget :
      IrreducibleCharacter.IsExtension
        (IsaacsGlaubermanRestriction.fixedNormalSubgroup
          (S := P) (G := A) N)
        fixedCorr.1 etaTarget := by
    simpa only [A, N, thetaN, hsmul, fixedCorr,
      etaTarget, hcorrespondentBack] using htransported
  have hetaTargetPPrime :
      etaTarget.IsPPrimeDegree p :=
    (hetaTarget.isPPrimeDegree_iff p).mpr fixedCorr.2
  let etaOver :
      PPrimeIrreducibleCharactersOverAlong
        (IsaacsGlaubermanRestriction.fixedNormalSubgroup
          (S := P) (G := A) N).subtype
        fixedCorr.1 p :=
    ⟨⟨etaTarget, hetaTarget.liesOver⟩, hetaTargetPPrime⟩
  let chiOver :=
    (IsaacsGlaubermanRestriction.invariantPPrimeCharactersOverEquiv
      N hsmul dA dN
      (IsaacsGlaubermanRestrictionReduction.isaacsGlaubermanRestrictionInput
        N hsmul dA dN)
      P.isPGroup' hA thetaN).symm etaOver
  let eC :=
    subgroupConjugationFixedPointsEquiv A (P : Subgroup G)
  let etaOrdinary :
      PPrimeIrreducibleCharacter
        (coprimeFixedPoints A (P : Subgroup G)) p :=
    IrreducibleCharacter.pPrimeComapEquiv p eC.symm
      ⟨etaTarget, hetaTargetPPrime⟩
  let gA : GlaubermanCorrespondence A (P : Subgroup G) p :=
    glaubermanCorrespondenceOfStrongConjugationAction
      A (P : Subgroup G) dStrong
  let chiOrdinary :
      PInvariantPPrimeIrreducibleCharacter
        A (P : Subgroup G) p :=
    gA.characterEquiv.symm etaOrdinary
  have hchiCoordinates :
      chiOrdinary.1.1 = chiOver.1.1.1 := by
    rfl
  have hetaOrdinaryInvariant :
      ∀ m :
          okuyamaWajimaProperBranchComplement
            K P hK hKP,
        fixedPointCharacterConjByNormalizer
            A (P : Subgroup G)
            ⟨m,
              (okuyamaWajimaAmbientComplement_le_normalizer
                P K hK hKP) m.property⟩
            etaOrdinary =
          etaOrdinary := by
    intro m
    apply Subtype.ext
    apply IrreducibleCharacter.ext
    funext z
    change
      etaU.values
          (targetConjugationAction
            (okuyamaWajimaProperBranchComplement K P hK hKP)
            U hUM hUnormal m⁻¹
            (eU (eC.symm z))) =
        etaU.values (eU (eC.symm z))
    exact hetaUInvariant m⁻¹ (eU (eC.symm z))
  have hchiM :
      ∀
        (m :
          okuyamaWajimaProperBranchComplement
            K P hK hKP)
        (x : A),
        chiOver.1.1.1.values
            ⟨(m : G) * (x : G) * (m : G)⁻¹,
              (inferInstance : A.Normal).conj_mem
                (x : G) x.property (m : G)⟩ =
          chiOver.1.1.1.values x := by
    intro m x
    let mInvNormalizer :
        Subgroup.normalizer ((P : Subgroup G) : Set G) :=
      ⟨m⁻¹,
        Subgroup.inv_mem
          (Subgroup.normalizer ((P : Subgroup G) : Set G))
          ((okuyamaWajimaAmbientComplement_le_normalizer
            P K hK hKP) m.property)⟩
    have hequivariant :=
      GlaubermanCorrespondence.characterEquiv_symm_conjByNormalizer
        A (P : Subgroup G) gA mInvNormalizer etaOrdinary
    have hfixed :
        fixedPointCharacterConjByNormalizer
            A (P : Subgroup G) mInvNormalizer etaOrdinary =
          etaOrdinary := by
      convert hetaOrdinaryInvariant m⁻¹ using 1
      apply Subtype.ext
      rfl
    rw [hfixed] at hequivariant
    have hcharacter :=
      congrArg
        (fun rho :
          PInvariantPPrimeIrreducibleCharacter
            A (P : Subgroup G) p ↦ rho.1.1)
        hequivariant.symm
    change
      (mInvNormalizer : G) • chiOrdinary.1.1 =
        chiOrdinary.1.1 at hcharacter
    have hvalue :=
      congrArg
        (fun rho : IrreducibleCharacter A ↦ rho.values x)
        hcharacter
    rw [IrreducibleCharacter.conjBy_values] at hvalue
    rw [hchiCoordinates] at hvalue
    convert hvalue using 1
    apply congrArg chiOver.1.1.1.values
    apply Subtype.ext
    simp only [MulAut.conjNormal_symm_apply,
      mInvNormalizer, inv_inv]
  refine
    ⟨⟨chiOver.1.1.1, chiOver.2⟩, ?_⟩
  intro mk x
  obtain ⟨m, hm, k, hk, hmk⟩ :=
    Subgroup.mem_sup_of_normal_right.mp mk.property
  let mM :
      okuyamaWajimaProperBranchComplement
        K P hK hKP :=
    ⟨m, hm⟩
  let kA : A :=
    ⟨k, (show K ≤ U ⊔ K from le_sup_right) hk⟩
  let y : A :=
    kA * x * kA⁻¹
  calc
    chiOver.1.1.1.values
          (middleConjugationAction
            K
            (okuyamaWajimaProperBranchComplement K P hK hKP)
            U hUM hUnormal mk x) =
        chiOver.1.1.1.values
          ⟨(mM : G) * (y : G) * (mM : G)⁻¹,
            (inferInstance : A.Normal).conj_mem
              (y : G) y.property (mM : G)⟩ := by
          congr 1
          apply Subtype.ext
          change
            (mk : G) * (x : G) * (mk : G)⁻¹ =
              m * (k * (x : G) * k⁻¹) * m⁻¹
          rw [← hmk]
          group
    _ = chiOver.1.1.1.values y :=
      hchiM mM y
    _ = chiOver.1.1.1.values x :=
      ClassFunction.conj_apply
        chiOver.1.1.1.toClassFunction x kA

/-- The exact remaining forward character-selection input after fixing a
selected `U ≤ M`: a normalizer extension must select an `M K`-invariant
member of the source lying-over fibre.

No extension condition occurs here.  It is derived from the automatic
Isaacs 13.29 theorem in
`hasInvariantSourceExtension_of_target_of_middleInvariantOver`. -/
def OkuyamaWajimaFullFixedForwardSelectionInput
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (U :
      Subgroup G)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hUnormal :
      (U.subgroupOf
        (okuyamaWajimaProperBranchComplement
          K P hK hKP)).Normal)
    (hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G)) :
    Prop :=
  OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
      K P theta hinvariant gP →
    HasMiddleInvariantSourceOver
      K P hK hKP theta U hUM hUnormal hcentral

/-- The forward invariant-selection interface is automatic. -/
theorem okuyamaWajimaFullFixedForwardSelectionInput_automatic
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (U :
      Subgroup G)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hUnormal :
      (U.subgroupOf
        (okuyamaWajimaProperBranchComplement
          K P hK hKP)).Normal)
    (hU :
      IsPPrimeGroup p U)
    (hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U) :
    OkuyamaWajimaFullFixedForwardSelectionInput
      K P hK hKP theta hinvariant gP
      U hUM hUnormal hcentral := by
  intro htarget
  exact
    exists_middleInvariantSourceOver_of_target
      K P hK hKP theta hinvariant gP U hUM hUnormal
      hU hcentral hfixedU htarget

/-- The earlier extension-valued interface remains useful as a compact
wrapper around the automatic 13.29 bridge.  New forward assembly should
prefer `OkuyamaWajimaFullFixedForwardSelectionInput`, whose conclusion is
strictly weaker.

It packages exactly the restriction/transport/Isaacs/equivariance step:
an extension of the ordinary target correspondent must produce an
`M K`-invariant source extension on `U K`. -/
def OkuyamaWajimaFullFixedForwardInnerInput
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (U :
      Subgroup G)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hUnormal :
      (U.subgroupOf
        (okuyamaWajimaProperBranchComplement
          K P hK hKP)).Normal) :
    Prop :=
  OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
      K P theta hinvariant gP →
    HasInvariantSourceExtension
      K
      (okuyamaWajimaProperBranchComplement
        K P hK hKP)
      U hUM hUnormal theta.1.1

/-- Navarro's prime-power-index theorem identifies extension to `G`
with extension to the canonical full-fixed middle subgroup `M K`. -/
theorem okuyamaWajimaFullFixedTheta_middle_ascent_iff :
    let H :=
      OkuyamaWajimaFullFixedOuterIndex.okuyamaWajimaFullFixedMiddle
        K P hK hKP
    let T :=
      okuyamaWajimaProperBranchThetaTriple
        K P theta hinvariant
    let hKH : T.normalSubgroup ≤ H := by
      change K ≤ H
      exact le_sup_right
    OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant ↔
      (T.restrictTo H hKH).HasExtension := by
  let H :=
    OkuyamaWajimaFullFixedOuterIndex.okuyamaWajimaFullFixedMiddle
      K P hK hKP
  let T :=
    okuyamaWajimaProperBranchThetaTriple
      K P theta hinvariant
  let hKH : T.normalSubgroup ≤ H := by
    change K ≤ H
    exact le_sup_right
  obtain ⟨n, hn⟩ :=
    OkuyamaWajimaFullFixedOuterIndex.okuyamaWajimaFullFixedMiddle_index_dvd_prime_power
      K P hK hKP
  exact
    T.hasExtension_iff_restrictTo_of_index_dvd_prime_power
      H hKH hK theta.1.2 hn

/-- External extension-along-inclusion form of the forward Navarro
ascent: an extension of `theta` to `M K` extends to `G`. -/
theorem okuyamaWajimaFullFixedTheta_extendsToG_of_middle_extension
    (eta :
      IrreducibleCharacter
        (OkuyamaWajimaFullFixedOuterIndex.okuyamaWajimaFullFixedMiddle
          K P hK hKP))
    (heta :
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion
          (show
            K ≤
              OkuyamaWajimaFullFixedOuterIndex.okuyamaWajimaFullFixedMiddle
                K P hK hKP
            from le_sup_right))
        theta.1.1 eta) :
    OkuyamaWajimaProperBranchThetaExtendsToG
      K P theta hinvariant := by
  let H :=
    OkuyamaWajimaFullFixedOuterIndex.okuyamaWajimaFullFixedMiddle
      K P hK hKP
  let T :=
    okuyamaWajimaProperBranchThetaTriple
      K P theta hinvariant
  let hKH : T.normalSubgroup ≤ H := by
    change K ≤ H
    exact le_sup_right
  have hlocal :
      (T.restrictTo H hKH).HasExtension := by
    apply
      (CharacterTriple.restrictTo_hasExtension_iff_exists_extensionAlong_inclusion
        T H hKH).mpr
    exact ⟨eta, heta⟩
  exact
    (okuyamaWajimaFullFixedTheta_middle_ascent_iff
      K P hK hKP theta hinvariant).mpr hlocal

end NavarroAscent

/-! ## The complete outer chain for an arbitrary selected subgroup -/

section OuterChain

variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable
  (hK : IsPPrimeGroup p K)
  (hKP : (K ⊔ (P : Subgroup G)).Normal)

local instance fullFixedForwardOuterChainPConjugationAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K (P : Subgroup G)

variable
  (theta :
    PInvariantPPrimeIrreducibleCharacter
      K (P : Subgroup G) p)
  (hinvariant :
    ∀ g : G, g • theta.1.1 = theta.1.1)

/-- Once the inner Isaacs step has produced an invariant source
extension on `U K`, the cyclic and Navarro steps compose without any
further character-theoretic input. -/
theorem okuyamaWajimaFullFixedTheta_extendsToG_of_invariantSource
    (U :
      Subgroup G)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hUnormal :
      (U.subgroupOf
        (okuyamaWajimaProperBranchComplement
          K P hK hKP)).Normal)
    (hcyclic :
      let M :=
        okuyamaWajimaProperBranchComplement K P hK hKP
      letI :
          ((U ⊔ K : Subgroup G).subgroupOf
            (M ⊔ K : Subgroup G)).Normal :=
        OkuyamaWajimaFullFixedOuterCoordinates.source_normal_in_middle
          K M U hUM hUnormal
      IsCyclic
        ((M ⊔ K : Subgroup G) ⧸
          (U ⊔ K).subgroupOf (M ⊔ K : Subgroup G)))
    (hsource :
      HasInvariantSourceExtension
        K
        (okuyamaWajimaProperBranchComplement
          K P hK hKP)
        U hUM hUnormal theta.1.1) :
    OkuyamaWajimaProperBranchThetaExtendsToG
      K P theta hinvariant := by
  let M :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  obtain ⟨eta, heta⟩ :=
    exists_middle_extension_of_hasInvariantSourceExtension
      K M U hUM hUnormal theta.1.1 hcyclic hsource
  exact
    okuyamaWajimaFullFixedTheta_extendsToG_of_middle_extension
      K P hK hKP theta hinvariant eta heta

/-- Forward-field constructor from the minimal invariant-selection
interface.  The automatic Isaacs 13.29 theorem supplies the extension
property before the cyclic and Navarro ascents are applied. -/
theorem okuyamaWajimaFullFixed_source_of_target_of_selectionInput
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (U :
      Subgroup G)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hUnormal :
      (U.subgroupOf
        (okuyamaWajimaProperBranchComplement
          K P hK hKP)).Normal)
    (hU :
      IsPPrimeGroup p U)
    (hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G))
    (hcyclic :
      let M :=
        okuyamaWajimaProperBranchComplement K P hK hKP
      letI :
          ((U ⊔ K : Subgroup G).subgroupOf
            (M ⊔ K : Subgroup G)).Normal :=
        OkuyamaWajimaFullFixedOuterCoordinates.source_normal_in_middle
          K M U hUM hUnormal
      IsCyclic
        ((M ⊔ K : Subgroup G) ⧸
          (U ⊔ K).subgroupOf (M ⊔ K : Subgroup G)))
    (selection :
      OkuyamaWajimaFullFixedForwardSelectionInput
        K P hK hKP theta hinvariant gP
        U hUM hUnormal hcentral) :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP →
      OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant := by
  intro htarget
  apply
    okuyamaWajimaFullFixedTheta_extendsToG_of_invariantSource
      K P hK hKP theta hinvariant U hUM hUnormal hcyclic
  exact
    hasInvariantSourceExtension_of_target_of_middleInvariantOver
      K P hK hKP theta hinvariant gP U hUM hUnormal hU
      hcentral hfixedU hcommutativeQuotient htarget
      (selection htarget)

/-- Complete forward implication for any selected subgroup satisfying
the full-fixed group coordinates.

The proof now has no residual character-theoretic input: target
restriction, correspondent transport, inverse-13.29 selection,
normalizer-equivariance, automatic extension, cyclic ascent, and Navarro
ascent are all composed here. -/
theorem okuyamaWajimaFullFixed_source_of_target
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (U :
      Subgroup G)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hUnormal :
      (U.subgroupOf
        (okuyamaWajimaProperBranchComplement
          K P hK hKP)).Normal)
    (hU :
      IsPPrimeGroup p U)
    (hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G))
    (hcyclic :
      let M :=
        okuyamaWajimaProperBranchComplement K P hK hKP
      letI :
          ((U ⊔ K : Subgroup G).subgroupOf
            (M ⊔ K : Subgroup G)).Normal :=
        OkuyamaWajimaFullFixedOuterCoordinates.source_normal_in_middle
          K M U hUM hUnormal
      IsCyclic
        ((M ⊔ K : Subgroup G) ⧸
          (U ⊔ K).subgroupOf (M ⊔ K : Subgroup G))) :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP →
      OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant :=
  okuyamaWajimaFullFixed_source_of_target_of_selectionInput
    K P hK hKP theta hinvariant gP U hUM hUnormal
    hU hcentral hfixedU hcommutativeQuotient hcyclic
    (okuyamaWajimaFullFixedForwardSelectionInput_automatic
      K P hK hKP theta hinvariant gP U hUM hUnormal
      hU hcentral hfixedU)

/-- Canonical Gorenstein-selected specialization of the complete
forward implication.

The subgroup `U` and every group coordinate required by
`okuyamaWajimaFullFixed_source_of_target` are constructed internally
from the datum used by `OkuyamaWajimaPrintedInduction`.  In particular,
the full-fixed hypothesis supplies Burnside centralization
automatically, so the resulting conclusion is literally the
`source_of_target` field of
`OkuyamaWajimaFullFixedOuterAssemblyInput`. -/
theorem okuyamaWajimaFullFixed_source_of_target_canonicalSelected
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G)) :
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
      (_hfull : d.fixedPoints = ⊤),
      OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
          K P theta hinvariant gP →
        OkuyamaWajimaProperBranchThetaExtendsToG
          K P theta hinvariant := by
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
  have hUM : U ≤ M :=
    OkuyamaWajimaFullFixedCoordinates.ambientSelectedSubgroup_le_M
      M P hM d
  have hUnormal : (U.subgroupOf M).Normal :=
    OkuyamaWajimaFullFixedOuterCoordinates.ambientSelectedSubgroup_normal_in_M
      M P hM d
  have hMPrime : IsPPrimeGroup p M :=
    okuyamaWajimaAmbientComplement_isPPrimeGroup
      K P hK hKP
  have hU : IsPPrimeGroup p U :=
    OkuyamaWajimaFullFixedCoordinates.ambientSelectedSubgroup_isPPrime
      M P hM d hMPrime
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
  have hKM : K ⊓ M ≤ U := by
    rw [pPrimeKernel_inf_ambientComplement_eq_fixedPoints
      P K hK hKP]
    exact hfixedU
  have hcyclic :
      letI :
          ((U ⊔ K : Subgroup G).subgroupOf
            (M ⊔ K : Subgroup G)).Normal :=
        OkuyamaWajimaFullFixedOuterCoordinates.source_normal_in_middle
          K M U hUM hUnormal
      IsCyclic
        ((M ⊔ K : Subgroup G) ⧸
          (U ⊔ K).subgroupOf (M ⊔ K : Subgroup G)) :=
    OkuyamaWajimaFullFixedOuterCoordinates.selected_middle_quotient_isCyclic
      K M P hM d hKM
  exact
    okuyamaWajimaFullFixed_source_of_target
      K P hK hKP theta hinvariant gP U hUM hUnormal
      hU hcentral hfixedU hcommutativeQuotient hcyclic

/-- Forward-field constructor from the exact inner
Isaacs/equivariance input and the already-derived selected cyclic
quotient. -/
theorem okuyamaWajimaFullFixed_source_of_target_of_innerInput
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (U :
      Subgroup G)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hUnormal :
      (U.subgroupOf
        (okuyamaWajimaProperBranchComplement
          K P hK hKP)).Normal)
    (hcyclic :
      let M :=
        okuyamaWajimaProperBranchComplement K P hK hKP
      letI :
          ((U ⊔ K : Subgroup G).subgroupOf
            (M ⊔ K : Subgroup G)).Normal :=
        OkuyamaWajimaFullFixedOuterCoordinates.source_normal_in_middle
          K M U hUM hUnormal
      IsCyclic
        ((M ⊔ K : Subgroup G) ⧸
          (U ⊔ K).subgroupOf (M ⊔ K : Subgroup G)))
    (inner :
      OkuyamaWajimaFullFixedForwardInnerInput
        K P hK hKP theta hinvariant gP U hUM hUnormal) :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP →
      OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant := by
  intro htarget
  apply
    okuyamaWajimaFullFixedTheta_extendsToG_of_invariantSource
      K P hK hKP theta hinvariant U hUM hUnormal hcyclic
  exact inner htarget

end OuterChain

end OkuyamaWajimaFullFixedOuterForward
end McKayConjecture
