/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InvariantLinearTwistOver
import McKayConjecture.Character.OkuyamaWajimaProperBranchQuotientInduction
import McKayConjecture.Character.OkuyamaWajimaProperBranchQuotientSourceComparison
import McKayConjecture.Character.PPrimeDeterminantRoot
import McKayConjecture.Character.QuotientDescent
import McKayConjecture.GroupTheory.QuotientEquivalenceTransport

/-!
# The quotient target comparison in the proper Okuyama--Wajima branch

This file identifies the target extension problem in the recursive group
`N_G(Q) / Q` with extension of the original `P`-Glauberman correspondent
to `N_G(P)`.

There are two logically separate ingredients.

* A quotient-normalization lemma says that extension of a `p'`-degree
  character from a subgroup centralized by a normal Sylow subgroup can be
  tested after quotienting by a normal subgroup of that Sylow subgroup.
  In the reverse direction an arbitrary extension is first twisted so that
  the Sylow subgroup acts trivially.
* Exact normalizer and fixed-point equivalences identify the recursive
  quotient character with the original `P`-correspondent.  The character
  identification is the strong two-stage Glauberman transitivity theorem.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open CliffordCorrespondence
open GroupTheory

namespace IrreducibleCharacter

variable {A : Type} [Group A] [Finite A]
variable {p : ℕ} [Fact p.Prime]

/-- The quotient map restricted and corestricted from a subgroup to its
literal quotient image. -/
def subgroupToQuotientImageHom
    (J Q : Subgroup A) [Q.Normal] :
    J →* J.map (QuotientGroup.mk' Q) :=
  ((QuotientGroup.mk' Q).domRestrict J).codRestrict
    (J.map (QuotientGroup.mk' Q))
    (fun j ↦ ⟨j, j.property, rfl⟩)

@[simp]
theorem subgroupToQuotientImageHom_apply_coe
    (J Q : Subgroup A) [Q.Normal]
    (j : J) :
    ((subgroupToQuotientImageHom J Q j :
        J.map (QuotientGroup.mk' Q)) :
      A ⧸ Q) =
        QuotientGroup.mk' Q (j : A) :=
  rfl

/-- A subgroup disjoint from the quotient kernel is canonically
isomorphic to its literal quotient image. -/
def subgroupEquivQuotientImageOfDisjoint
    (J Q : Subgroup A) [Q.Normal]
    (hdisjoint : Disjoint J Q) :
    J ≃* J.map (QuotientGroup.mk' Q) := by
  apply MulEquiv.ofBijective
    (subgroupToQuotientImageHom J Q)
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hquot :
        QuotientGroup.mk' Q
            ((x : A) * (y : A)⁻¹) =
          1 := by
      rw [map_mul, map_inv]
      change
        ((subgroupToQuotientImageHom J Q x :
            J.map (QuotientGroup.mk' Q)) :
          A ⧸ Q) *
          ((subgroupToQuotientImageHom J Q y :
            J.map (QuotientGroup.mk' Q)) :
          A ⧸ Q)⁻¹ =
        1
      rw [hxy]
      simp
    have hQ :
        (x : A) * (y : A)⁻¹ ∈ Q :=
      (QuotientGroup.eq_one_iff
        (N := Q) ((x : A) * (y : A)⁻¹)).mp hquot
    have hJ :
        (x : A) * (y : A)⁻¹ ∈ J :=
      J.mul_mem x.property (J.inv_mem y.property)
    have hone :
        (x : A) * (y : A)⁻¹ = 1 :=
      Subgroup.mem_bot.mp
        (hdisjoint.le_bot ⟨hJ, hQ⟩)
    exact mul_inv_eq_one.mp hone
  · intro z
    obtain ⟨a, ha, haz⟩ := z.property
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    exact haz

@[simp]
theorem subgroupEquivQuotientImageOfDisjoint_apply_coe
    (J Q : Subgroup A) [Q.Normal]
    (hdisjoint : Disjoint J Q)
    (j : J) :
    ((subgroupEquivQuotientImageOfDisjoint
        J Q hdisjoint j :
      J.map (QuotientGroup.mk' Q)) :
      A ⧸ Q) =
        QuotientGroup.mk' Q (j : A) :=
  rfl

/-- Existence of an extension is invariant under an isomorphism of the
ambient/source inclusion square. -/
theorem exists_extensionAlong_equiv_iff
    {A A' B B' : Type}
    [Group A] [Group A'] [Group B] [Group B']
    [Finite A] [Finite A'] [Finite B] [Finite B']
    (f : B →* A) (f' : B' →* A')
    (eA : A' ≃* A) (eB : B' ≃* B)
    (hcomm :
      eA.toMonoidHom.comp f' =
        f.comp eB.toMonoidHom)
    (chi : IrreducibleCharacter B) :
    (∃ eta : IrreducibleCharacter A,
        IsExtensionAlong f chi eta) ↔
      ∃ eta' : IrreducibleCharacter A',
        IsExtensionAlong f' (chi.comap eB) eta' := by
  constructor
  · rintro ⟨eta, heta⟩
    exact
      ⟨eta.comap eA,
        IsExtensionAlong.comap_equiv
          eA eB hcomm heta⟩
  · rintro ⟨eta', heta'⟩
    have hcomm' :
        eA.symm.toMonoidHom.comp f =
          f'.comp eB.symm.toMonoidHom := by
      ext b
      apply eA.injective
      have hpoint :=
        congrArg
          (fun k : B' →* A ↦ k (eB.symm b))
          hcomm
      change
        eA (eA.symm (f b)) =
          eA (f' (eB.symm b))
      rw [eA.apply_symm_apply]
      simpa using hpoint.symm
    refine ⟨eta'.comap eA.symm, ?_⟩
    have hback :=
      IsExtensionAlong.comap_equiv
        eA.symm eB.symm hcomm' heta'
    simpa using hback

/-- The quotient map restricted from a Sylow subgroup to its image after
quotienting by a disjoint normal subgroup. -/
def sylowToQuotientImageHom
    (C : Subgroup A) [C.Normal]
    (S : Sylow p A) :
    (S : Subgroup A) →*
      (S.mapQuotient C : Subgroup (A ⧸ C)) :=
  ((QuotientGroup.mk' C).domRestrict
      (S : Subgroup A)).codRestrict
    (S.mapQuotient C : Subgroup (A ⧸ C))
    (fun x ↦ ⟨x, x.property, rfl⟩)

@[simp]
theorem sylowToQuotientImageHom_apply_coe
    (C : Subgroup A) [C.Normal]
    (S : Sylow p A)
    (x : (S : Subgroup A)) :
    ((sylowToQuotientImageHom C S x :
        (S.mapQuotient C : Subgroup (A ⧸ C))) :
      A ⧸ C) =
        QuotientGroup.mk' C (x : A) :=
  rfl

/-- If `C` is disjoint from `S`, quotienting by `C` identifies `S` with
its literal quotient image. -/
def sylowEquivQuotientImage
    (C : Subgroup A) [C.Normal]
    (S : Sylow p A)
    (hdisjoint : Disjoint C (S : Subgroup A)) :
    (S : Subgroup A) ≃*
      (S.mapQuotient C : Subgroup (A ⧸ C)) := by
  apply MulEquiv.ofBijective
    (sylowToQuotientImageHom C S)
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hquot :
        QuotientGroup.mk' C
            ((x : A) * (y : A)⁻¹) =
          1 := by
      rw [map_mul, map_inv]
      change
        ((sylowToQuotientImageHom C S x :
              (S.mapQuotient C :
                Subgroup (A ⧸ C))) :
            A ⧸ C) *
            ((sylowToQuotientImageHom C S y :
              (S.mapQuotient C :
                Subgroup (A ⧸ C))) :
            A ⧸ C)⁻¹ =
          1
      rw [hxy]
      simp
    have hC : (x : A) * (y : A)⁻¹ ∈ C :=
      (QuotientGroup.eq_one_iff
        (N := C) ((x : A) * (y : A)⁻¹)).mp hquot
    have hS : (x : A) * (y : A)⁻¹ ∈ (S : Subgroup A) :=
      (S : Subgroup A).mul_mem x.property
        ((S : Subgroup A).inv_mem y.property)
    have hone : (x : A) * (y : A)⁻¹ = 1 := by
      exact
        Subgroup.mem_bot.mp
          (hdisjoint.le_bot ⟨hC, hS⟩)
    exact mul_inv_eq_one.mp hone
  · intro y
    obtain ⟨x, hxS, hxy⟩ := y.property
    refine ⟨⟨x, hxS⟩, ?_⟩
    apply Subtype.ext
    exact hxy

@[simp]
theorem sylowEquivQuotientImage_apply_coe
    (C : Subgroup A) [C.Normal]
    (S : Sylow p A)
    (hdisjoint : Disjoint C (S : Subgroup A))
    (x : (S : Subgroup A)) :
    ((sylowEquivQuotientImage C S hdisjoint x :
        (S.mapQuotient C : Subgroup (A ⧸ C))) :
      A ⧸ C) =
        QuotientGroup.mk' C (x : A) :=
  rfl

end IrreducibleCharacter

section NormalizerCoordinates

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable (Q : Subgroup P) [Q.Normal]

/-- The original Sylow normalizer. -/
abbrev properBranchTargetPNormalizer :
    Subgroup G :=
  Subgroup.normalizer ((P : Subgroup G) : Set G)

/-- The original final fixed-point kernel `C_K(P)`. -/
abbrev properBranchTargetFixedKernel :
    Subgroup G :=
  coprimeFixedPoints K (P : Subgroup G)

/-- The Sylow subgroup `P`, regarded inside `N_G(Q)`. -/
abbrev properBranchTargetSylowInQNormalizer :
    Sylow p
      (okuyamaWajimaProperBranchQuotientAmbient P Q) :=
  okuyamaWajimaProperBranchSylowInQNormalizer P Q

/-- The normalizer of the internal copy of `P` in `N_G(Q)`. -/
abbrev properBranchTargetInternalPNormalizer :
    Subgroup
      (okuyamaWajimaProperBranchQuotientAmbient P Q) :=
  Subgroup.normalizer
    ((properBranchTargetSylowInQNormalizer P Q :
      Subgroup
        (okuyamaWajimaProperBranchQuotientAmbient P Q)) :
      Set
        (okuyamaWajimaProperBranchQuotientAmbient P Q))

/-- The copy of `Q` in the internal normalizer of `P`. -/
abbrev properBranchTargetQInInternalPNormalizer :
    Subgroup
      (properBranchTargetInternalPNormalizer P Q) :=
  (okuyamaWajimaProperBranchQuotientKernel P Q).subgroupOf
    (properBranchTargetInternalPNormalizer P Q)

/-- The copy of `Q` in the original normalizer `N_G(P)`. -/
abbrev properBranchTargetQInPNormalizer :
    Subgroup (properBranchTargetPNormalizer P) :=
  (okuyamaWajimaProperBranchQ P Q).subgroupOf
    (properBranchTargetPNormalizer P)

/-- If `N_G(P)` normalizes the selected `Q`, the normalizer computed
internally in `N_G(Q)` is canonically the original `N_G(P)`.

The extra containment is indispensable for an arbitrary normal subgroup
`Q ◁ P`; it is automatic for the subgroup selected in the printed branch
because the chosen complement normalizes `Q`. -/
def properBranchTargetInternalPNormalizerEquiv
    (hPN :
      properBranchTargetPNormalizer P ≤
        okuyamaWajimaProperBranchQuotientAmbient P Q) :
    properBranchTargetInternalPNormalizer P Q ≃*
      properBranchTargetPNormalizer P where
  toFun x :=
    ⟨((x :
        okuyamaWajimaProperBranchQuotientAmbient P Q) : G),
      by
        have hx :
            (x :
              okuyamaWajimaProperBranchQuotientAmbient P Q) ∈
              (properBranchTargetPNormalizer P).subgroupOf
                (okuyamaWajimaProperBranchQuotientAmbient P Q) := by
          have heq :=
            Subgroup.subgroupOf_normalizer_eq
              (okuyamaWajimaProperBranchP_le_QNormalizer P Q)
          have hmem :=
            congrArg
              (fun S :
                Subgroup
                  (okuyamaWajimaProperBranchQuotientAmbient P Q) =>
                ((x :
                  okuyamaWajimaProperBranchQuotientAmbient P Q) ∈ S))
              heq
          exact hmem.mpr x.property
        change
          ((x :
            okuyamaWajimaProperBranchQuotientAmbient P Q) : G) ∈
            properBranchTargetPNormalizer P
        exact hx⟩
  invFun x :=
    ⟨⟨(x : G), hPN x.property⟩,
      by
        change
          (⟨(x : G), hPN x.property⟩ :
            okuyamaWajimaProperBranchQuotientAmbient P Q) ∈
            properBranchTargetInternalPNormalizer P Q
        have heq :=
          Subgroup.subgroupOf_normalizer_eq
            (okuyamaWajimaProperBranchP_le_QNormalizer P Q)
        have hmem :=
          congrArg
            (fun S :
              Subgroup
                (okuyamaWajimaProperBranchQuotientAmbient P Q) =>
              ((⟨(x : G), hPN x.property⟩ :
                okuyamaWajimaProperBranchQuotientAmbient P Q) ∈ S))
            heq
        exact hmem.mp x.property⟩
  left_inv x := by
    rfl
  right_inv x := by
    rfl
  map_mul' x y := by
    rfl

@[simp]
theorem properBranchTargetInternalPNormalizerEquiv_apply_coe
    (hPN :
      properBranchTargetPNormalizer P ≤
        okuyamaWajimaProperBranchQuotientAmbient P Q)
    (x : properBranchTargetInternalPNormalizer P Q) :
    ((properBranchTargetInternalPNormalizerEquiv
        P Q hPN x : properBranchTargetPNormalizer P) : G) =
      (((x :
        properBranchTargetInternalPNormalizer P Q) :
          okuyamaWajimaProperBranchQuotientAmbient P Q) : G) :=
  rfl

/-- The preceding equivalence restricts to the two copies of `Q`. -/
def properBranchTargetQEquiv
    (hPN :
      properBranchTargetPNormalizer P ≤
        okuyamaWajimaProperBranchQuotientAmbient P Q) :
    properBranchTargetQInInternalPNormalizer P Q ≃*
      properBranchTargetQInPNormalizer P Q where
  toFun x :=
    ⟨properBranchTargetInternalPNormalizerEquiv P Q hPN
        (x : properBranchTargetInternalPNormalizer P Q),
      x.property⟩
  invFun x :=
    ⟨(properBranchTargetInternalPNormalizerEquiv
        P Q hPN).symm
        (x : properBranchTargetPNormalizer P),
      x.property⟩
  left_inv x := by
    rfl
  right_inv x := by
    rfl
  map_mul' x y := by
    rfl

@[simp]
theorem properBranchTargetQEquiv_apply_coe
    (hPN :
      properBranchTargetPNormalizer P ≤
        okuyamaWajimaProperBranchQuotientAmbient P Q)
    (x : properBranchTargetQInInternalPNormalizer P Q) :
    ((properBranchTargetQEquiv P Q hPN x :
        properBranchTargetQInPNormalizer P Q) :
      properBranchTargetPNormalizer P) =
        properBranchTargetInternalPNormalizerEquiv P Q hPN x :=
  rfl

omit [Finite G] [Fact p.Prime] [K.Normal] in
/-- The copy of `Q` is normal in `N_G(P)` as soon as `N_G(P)` lies in
`N_G(Q)`. -/
theorem properBranchTargetQInPNormalizer_normal
    (hPN :
      properBranchTargetPNormalizer P ≤
        okuyamaWajimaProperBranchQuotientAmbient P Q) :
    (properBranchTargetQInPNormalizer P Q).Normal := by
  let QA := okuyamaWajimaProperBranchQ P Q
  let NP := properBranchTargetPNormalizer P
  have hQNP : QA ≤ NP := by
    exact
      (okuyamaWajimaProperBranchAmbientQ_le_P
        (P : Subgroup G) Q).trans
        Subgroup.le_normalizer
  exact
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      hQNP).2 hPN

/-- The quotient-normalizer coordinate, transported from the internal
normalizer in `N_G(Q)` to `N_G(P) / Q`.

The normality instance on the right is supplied canonically by
`properBranchTargetQInPNormalizer_normal`. -/
def properBranchTargetNormalizerQuotientEquiv
    (hPN :
      properBranchTargetPNormalizer P ≤
        okuyamaWajimaProperBranchQuotientAmbient P Q)
    [hQnormal :
      (properBranchTargetQInPNormalizer P Q).Normal] :
    Subgroup.normalizer
        (((properBranchTargetSylowInQNormalizer P Q).mapQuotient
          (okuyamaWajimaProperBranchQuotientKernel P Q) :
          Subgroup
            (okuyamaWajimaProperBranchNormalizerQuotient P Q)) :
          Set
            (okuyamaWajimaProperBranchNormalizerQuotient P Q)) ≃*
      (properBranchTargetPNormalizer P ⧸
        properBranchTargetQInPNormalizer P Q) := by
  let PX :=
    properBranchTargetSylowInQNormalizer P Q
  let QX :=
    okuyamaWajimaProperBranchQuotientKernel P Q
  let NX :=
    properBranchTargetInternalPNormalizer P Q
  let QNX :=
    properBranchTargetQInInternalPNormalizer P Q
  let NP :=
    properBranchTargetPNormalizer P
  let QNP :=
    properBranchTargetQInPNormalizer P Q
  let eN : NX ≃* NP :=
    properBranchTargetInternalPNormalizerEquiv P Q hPN
  let eQ : QNX ≃* QNP :=
    properBranchTargetQEquiv P Q hPN
  have hsquare :
      eN.toMonoidHom.comp QNX.subtype =
        QNP.subtype.comp eQ.toMonoidHom := by
    ext x
    rfl
  exact
    (Sylow.quotientNormalizerEquiv PX QX).symm.trans
      (quotientMulEquivOfSubgroupEquiv eN eQ hsquare)

@[simp]
theorem properBranchTargetNormalizerQuotientEquiv_apply_quotient
    (hPN :
      properBranchTargetPNormalizer P ≤
        okuyamaWajimaProperBranchQuotientAmbient P Q)
    [hQnormal :
      (properBranchTargetQInPNormalizer P Q).Normal]
    (x : properBranchTargetInternalPNormalizer P Q) :
    properBranchTargetNormalizerQuotientEquiv P Q hPN
        (Sylow.quotientNormalizerHom
          (properBranchTargetSylowInQNormalizer P Q)
          (okuyamaWajimaProperBranchQuotientKernel P Q) x) =
      QuotientGroup.mk'
        (properBranchTargetQInPNormalizer P Q)
        (properBranchTargetInternalPNormalizerEquiv
          P Q hPN x) := by
  let PX :=
    properBranchTargetSylowInQNormalizer P Q
  let QX :=
    okuyamaWajimaProperBranchQuotientKernel P Q
  let NX :=
    properBranchTargetInternalPNormalizer P Q
  let QNX :=
    properBranchTargetQInInternalPNormalizer P Q
  let NP :=
    properBranchTargetPNormalizer P
  let QNP :=
    properBranchTargetQInPNormalizer P Q
  let eN : NX ≃* NP :=
    properBranchTargetInternalPNormalizerEquiv P Q hPN
  let eQ : QNX ≃* QNP :=
    properBranchTargetQEquiv P Q hPN
  have hsquare :
      eN.toMonoidHom.comp QNX.subtype =
        QNP.subtype.comp eQ.toMonoidHom := by
    ext y
    rfl
  have hfirst :
      (Sylow.quotientNormalizerEquiv PX QX).symm
          (Sylow.quotientNormalizerHom PX QX x) =
        QuotientGroup.mk' QNX x := by
    apply (Sylow.quotientNormalizerEquiv PX QX).injective
    rw [MulEquiv.apply_symm_apply]
    exact Sylow.quotientNormalizerEquiv_mk PX QX x
  rw [properBranchTargetNormalizerQuotientEquiv,
    MulEquiv.trans_apply, hfirst]
  exact
    quotientMulEquivOfSubgroupEquiv_mk
      eN eQ hsquare x

section SelectedNormalizerContainment

variable
  (hK : IsPPrimeGroup p K)
  (hKP : (K ⊔ (P : Subgroup G)).Normal)

local instance properBranchTargetComplementConjugationAction :
    MulDistribMulAction
      (okuyamaWajimaProperBranchComplement K P hK hKP)
      P :=
  normalizingSubgroupConjugationAction
    (P : Subgroup G)
    (okuyamaWajimaProperBranchComplement K P hK hKP)
    (okuyamaWajimaAmbientComplement_le_normalizer
      P K hK hKP)

variable
  {L :
    Subgroup
      (okuyamaWajimaProperBranchComplement K P hK hKP)}

/-- For the subgroup selected by the proper-branch complement action,
the original Sylow normalizer lies in the selected-subgroup normalizer.

This is the canonical source of the containment hypothesis used above:
the Okuyama--Wajima product theorem generates `N_G(P)` from `C_K(P)`,
`P`, and the chosen complement; each of those three factors normalizes
the selected `Q`. -/
theorem properBranchTargetPNormalizer_le_selectedQNormalizer
    (d :
      OkuyamaWajimaCyclicQuotientSubgroup
        (okuyamaWajimaProperBranchComplement K P hK hKP)
        P L) :
    properBranchTargetPNormalizer P ≤
      okuyamaWajimaProperBranchQuotientAmbient
        P d.fixedPointPreimage := by
  let M :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  have hM :
      M ≤
        okuyamaWajimaProperBranchQuotientAmbient
          P d.fixedPointPreimage :=
    properBranchComplement_le_selectedQ_normalizer
      K P hK hKP d
  have hD :
      okuyamaWajimaFixedPoints K (P : Subgroup G) ≤
        okuyamaWajimaProperBranchQuotientAmbient
          P d.fixedPointPreimage :=
    (fixedPoints_le_okuyamaWajimaAmbientComplement
      P K hK hKP).trans hM
  have hP :
      (P : Subgroup G) ≤
        okuyamaWajimaProperBranchQuotientAmbient
          P d.fixedPointPreimage :=
    okuyamaWajimaProperBranchP_le_QNormalizer
      P d.fixedPointPreimage
  change
    Subgroup.normalizer ((P : Subgroup G) : Set G) ≤
      okuyamaWajimaProperBranchQuotientAmbient
        P d.fixedPointPreimage
  rw [←
    fixedPoints_sup_sylow_sup_ambientComplement_eq_normalizer
      P K hK hKP]
  exact sup_le (sup_le hD hP) hM

end SelectedNormalizerContainment

end NormalizerCoordinates

section FixedKernelCoordinates

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable (Q : Subgroup P) [Q.Normal]

local instance properBranchTargetPConjugationAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K (P : Subgroup G)

variable
  (theta :
    PInvariantPPrimeIrreducibleCharacter
      K (P : Subgroup G) p)
  (hinvariant :
    ∀ g : G, g • theta.1.1 = theta.1.1)
  (gQ :
    GlaubermanCorrespondence K
      (okuyamaWajimaProperBranchQ P Q) p)

/-- The fixed-point kernel in the quotient recursive target. -/
abbrev properBranchQuotientTargetFixedKernel
    (hK : IsPPrimeGroup p K) :
    Subgroup
      (okuyamaWajimaProperBranchNormalizerQuotient P Q) :=
  coprimeFixedPoints
    (okuyamaWajimaProperBranchQuotientImageKernel
      K P Q theta hinvariant gQ)
    (okuyamaWajimaProperBranchQuotientSylow P Q :
      Subgroup
        (okuyamaWajimaProperBranchNormalizerQuotient P Q))

/-- Regard `C_K(P)` as a subgroup of the internal source kernel
`C_K(Q) ≤ N_G(Q)`. -/
def properBranchOriginalFixedToSourceKernelHom :
    properBranchTargetFixedKernel K P →*
      okuyamaWajimaProperBranchQuotientSourceKernel
        K P Q theta hinvariant gQ where
  toFun c := by
    have hcQ :
        (c : G) ∈
          Subgroup.centralizer
            (okuyamaWajimaProperBranchQ P Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact
        (Subgroup.mem_centralizer_iff.mp c.property.2
          q
          (okuyamaWajimaProperBranchAmbientQ_le_P
            (P : Subgroup G) Q hq))
    have hcX :
        (c : G) ∈
          okuyamaWajimaProperBranchQuotientAmbient P Q :=
      Subgroup.centralizer_le_normalizer
        (okuyamaWajimaProperBranchQ P Q : Set G) hcQ
    exact
      ⟨⟨(c : G), hcX⟩, ⟨c.property.1, hcQ⟩⟩
  map_one' := by
    rfl
  map_mul' c d := by
    rfl

@[simp]
theorem properBranchOriginalFixedToSourceKernelHom_apply_coe
    (c : properBranchTargetFixedKernel K P) :
    (((properBranchOriginalFixedToSourceKernelHom
        K P Q theta hinvariant gQ c :
      okuyamaWajimaProperBranchQuotientSourceKernel
        K P Q theta hinvariant gQ) :
      okuyamaWajimaProperBranchQuotientAmbient P Q) : G) =
        (c : G) :=
  rfl

/-- The underlying quotient map from `C_K(P)` to the image of
`C_K(Q)` in `N_G(Q) / Q`.  Separating this homomorphism from its
corestriction to the final fixed-point subgroup keeps all group laws
definitionally transparent. -/
def properBranchOriginalFixedToImageKernelHom
    (hK : IsPPrimeGroup p K) :
    properBranchTargetFixedKernel K P →*
      okuyamaWajimaProperBranchQuotientImageKernel
        K P Q theta hinvariant gQ :=
  (okuyamaWajimaProperBranchQuotientSourceKernelEquiv
      K P Q theta hinvariant gQ hK).toMonoidHom.comp
    (properBranchOriginalFixedToSourceKernelHom
      K P Q theta hinvariant gQ)

/-- Map the original fixed-point kernel `C_K(P)` into the fixed-point
kernel of the quotient recursive target. -/
def properBranchOriginalFixedToQuotientFixedHom
    (hK : IsPPrimeGroup p K) :
    properBranchTargetFixedKernel K P →*
      properBranchQuotientTargetFixedKernel
        K P Q theta hinvariant gQ hK where
  toFun c := by
    let X :=
      okuyamaWajimaProperBranchQuotientAmbient P Q
    let JX :=
      okuyamaWajimaProperBranchQuotientSourceKernel
        K P Q theta hinvariant gQ
    let Jbar :=
      okuyamaWajimaProperBranchQuotientImageKernel
        K P Q theta hinvariant gQ
    let Pbar :=
      (okuyamaWajimaProperBranchQuotientSylow P Q :
        Subgroup
          (okuyamaWajimaProperBranchNormalizerQuotient P Q))
    let z : Jbar :=
      properBranchOriginalFixedToImageKernelHom
        K P Q theta hinvariant gQ hK c
    refine
      ⟨(z :
          okuyamaWajimaProperBranchNormalizerQuotient P Q),
        ⟨z.property, ?_⟩⟩
    change
      (z :
        okuyamaWajimaProperBranchNormalizerQuotient P Q) ∈
        Subgroup.centralizer
          (Pbar : Set
            (okuyamaWajimaProperBranchNormalizerQuotient P Q))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨x, hxP, hxy⟩ := hy
    have hxc :
        ((x : X) : G) * (c : G) =
          (c : G) * ((x : X) : G) := by
      exact
        (Subgroup.mem_centralizer_iff.mp c.property.2
          ((x : X) : G) hxP)
    have hz :
        (z :
          okuyamaWajimaProperBranchNormalizerQuotient P Q) =
            okuyamaWajimaProperBranchQuotientMap P Q
              (properBranchOriginalFixedToSourceKernelHom
                K P Q theta hinvariant gQ c) := by
      exact
        okuyamaWajimaProperBranchQuotientSourceKernelEquiv_apply_coe
          K P Q theta hinvariant gQ hK
          (properBranchOriginalFixedToSourceKernelHom
            K P Q theta hinvariant gQ c)
    rw [← hxy, hz, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hxc
  map_one' := by
    apply Subtype.ext
    change
      (((properBranchOriginalFixedToImageKernelHom
          K P Q theta hinvariant gQ hK) 1 :
          okuyamaWajimaProperBranchQuotientImageKernel
            K P Q theta hinvariant gQ) :
        okuyamaWajimaProperBranchNormalizerQuotient P Q) = 1
    exact
      congrArg Subtype.val
        (map_one
          (properBranchOriginalFixedToImageKernelHom
            K P Q theta hinvariant gQ hK))
  map_mul' c d := by
    apply Subtype.ext
    change
      (((properBranchOriginalFixedToImageKernelHom
          K P Q theta hinvariant gQ hK) (c * d) :
          okuyamaWajimaProperBranchQuotientImageKernel
            K P Q theta hinvariant gQ) :
        okuyamaWajimaProperBranchNormalizerQuotient P Q) =
      (((properBranchOriginalFixedToImageKernelHom
          K P Q theta hinvariant gQ hK) c :
          okuyamaWajimaProperBranchQuotientImageKernel
            K P Q theta hinvariant gQ) :
        okuyamaWajimaProperBranchNormalizerQuotient P Q) *
      (((properBranchOriginalFixedToImageKernelHom
          K P Q theta hinvariant gQ hK) d :
          okuyamaWajimaProperBranchQuotientImageKernel
            K P Q theta hinvariant gQ) :
        okuyamaWajimaProperBranchNormalizerQuotient P Q)
    exact
      congrArg Subtype.val
        (map_mul
          (properBranchOriginalFixedToImageKernelHom
            K P Q theta hinvariant gQ hK) c d)

@[simp]
theorem properBranchOriginalFixedToQuotientFixedHom_apply_coe
    (hK : IsPPrimeGroup p K)
    (c : properBranchTargetFixedKernel K P) :
    ((properBranchOriginalFixedToQuotientFixedHom
        K P Q theta hinvariant gQ hK c :
      properBranchQuotientTargetFixedKernel
        K P Q theta hinvariant gQ hK) :
      okuyamaWajimaProperBranchNormalizerQuotient P Q) =
      ((properBranchOriginalFixedToImageKernelHom
          K P Q theta hinvariant gQ hK c :
        okuyamaWajimaProperBranchQuotientImageKernel
          K P Q theta hinvariant gQ) :
        okuyamaWajimaProperBranchNormalizerQuotient P Q) :=
  rfl

/-- Every quotient fixed point has a unique lift in `C_K(P)`.

The key point is that commutation modulo `Q` already gives exact
commutation: the commutator lies both in the `p`-group `P` and in the
normal `p'`-subgroup `K`, hence is trivial. -/
theorem properBranchOriginalFixedToQuotientFixedHom_surjective
    (hK : IsPPrimeGroup p K) :
    Function.Surjective
      (properBranchOriginalFixedToQuotientFixedHom
        K P Q theta hinvariant gQ hK) := by
  intro z
  let X :=
    okuyamaWajimaProperBranchQuotientAmbient P Q
  let Xbar :=
    okuyamaWajimaProperBranchNormalizerQuotient P Q
  let JX :=
    okuyamaWajimaProperBranchQuotientSourceKernel
      K P Q theta hinvariant gQ
  let Jbar :=
    okuyamaWajimaProperBranchQuotientImageKernel
      K P Q theta hinvariant gQ
  let Pbar :=
    (okuyamaWajimaProperBranchQuotientSylow P Q :
      Subgroup Xbar)
  let q :=
    okuyamaWajimaProperBranchQuotientMap P Q
  let eJ :=
    okuyamaWajimaProperBranchQuotientSourceKernelEquiv
      K P Q theta hinvariant gQ hK
  let zJ : Jbar := ⟨(z : Xbar), z.property.1⟩
  let j : JX := eJ.symm zJ
  have hzq :
      (z : Xbar) = q (j : X) := by
    have he := congrArg Subtype.val (eJ.apply_symm_apply zJ)
    rw [
      okuyamaWajimaProperBranchQuotientSourceKernelEquiv_apply_coe
        K P Q theta hinvariant gQ hK j] at he
    exact he.symm
  have hjcentral :
      (((j : JX) : X) : G) ∈
        Subgroup.centralizer ((P : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hyP
    let x : X :=
      ⟨y, okuyamaWajimaProperBranchP_le_QNormalizer P Q hyP⟩
    have hxPbar : q x ∈ Pbar := by
      refine ⟨x, ?_, rfl⟩
      exact hyP
    have hzcomm :
        q x * (z : Xbar) =
          (z : Xbar) * q x :=
      Subgroup.mem_centralizer_iff.mp z.property.2
        (q x) hxPbar
    have hquotmul :
        q (x * (j : X)) =
          q ((j : X) * x) := by
      simpa only [map_mul, hzq] using hzcomm
    let a : X :=
      (x * (j : X)) * ((j : X) * x)⁻¹
    have haquot : q a = 1 := by
      dsimp [a]
      rw [map_mul, map_inv, hquotmul]
      simp
    have haQ :
        ((a : X) : G) ∈
          okuyamaWajimaProperBranchQ P Q :=
      (QuotientGroup.eq_one_iff
        (N := okuyamaWajimaProperBranchQuotientKernel P Q)
        a).mp haquot
    have haP :
        ((a : X) : G) ∈ (P : Subgroup G) :=
      okuyamaWajimaProperBranchAmbientQ_le_P
        (P : Subgroup G) Q haQ
    have haK :
        ((a : X) : G) ∈ K := by
      have hconj :
          ((x : X) : G) * (((j : JX) : X) : G) *
              ((x : X) : G)⁻¹ ∈ K :=
        (inferInstance : K.Normal).conj_mem
          (((j : JX) : X) : G) j.property.1
          ((x : X) : G)
      have hmul :=
        K.mul_mem hconj
          (K.inv_mem j.property.1)
      simpa [a, mul_assoc] using hmul
    have haone :
        ((a : X) : G) = 1 := by
      have hdisjoint :
          Disjoint (P : Subgroup G) K :=
        IsPGroup.disjoint_of_isPPrimeGroup
          P.isPGroup' hK
      exact
        Subgroup.mem_bot.mp
          (hdisjoint.le_bot ⟨haP, haK⟩)
    have hcomm :
        y * (((j : JX) : X) : G) =
          (((j : JX) : X) : G) * y := by
      have :=
        mul_inv_eq_one.mp haone
      simpa [a, x] using this
    exact hcomm
  let c : properBranchTargetFixedKernel K P :=
    ⟨(((j : JX) : X) : G),
      ⟨j.property.1, hjcentral⟩⟩
  refine ⟨c, ?_⟩
  apply Subtype.ext
  change
    (((properBranchOriginalFixedToImageKernelHom
        K P Q theta hinvariant gQ hK) c : Jbar) : Xbar) =
      (z : Xbar)
  have hcJ :
      properBranchOriginalFixedToSourceKernelHom
          K P Q theta hinvariant gQ c =
        j := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [properBranchOriginalFixedToImageKernelHom, MonoidHom.comp_apply,
    hcJ]
  exact congrArg Subtype.val (eJ.apply_symm_apply zJ)

/-- Canonical identification between the quotient recursive target
fixed-point kernel and the original `C_K(P)`. -/
def properBranchTargetFixedKernelEquiv
    (hK : IsPPrimeGroup p K) :
    properBranchTargetFixedKernel K P ≃*
      properBranchQuotientTargetFixedKernel
        K P Q theta hinvariant gQ hK := by
  apply MulEquiv.ofBijective
    (properBranchOriginalFixedToQuotientFixedHom
      K P Q theta hinvariant gQ hK)
  constructor
  · intro c d hcd
    let eJ :=
      okuyamaWajimaProperBranchQuotientSourceKernelEquiv
        K P Q theta hinvariant gQ hK
    have himage :
        properBranchOriginalFixedToImageKernelHom
            K P Q theta hinvariant gQ hK c =
          properBranchOriginalFixedToImageKernelHom
            K P Q theta hinvariant gQ hK d := by
      have hquot :
          ((properBranchOriginalFixedToQuotientFixedHom
              K P Q theta hinvariant gQ hK c :
            properBranchQuotientTargetFixedKernel
              K P Q theta hinvariant gQ hK) :
            okuyamaWajimaProperBranchNormalizerQuotient P Q) =
          ((properBranchOriginalFixedToQuotientFixedHom
              K P Q theta hinvariant gQ hK d :
            properBranchQuotientTargetFixedKernel
              K P Q theta hinvariant gQ hK) :
            okuyamaWajimaProperBranchNormalizerQuotient P Q) :=
        congrArg
          (fun z :
            properBranchQuotientTargetFixedKernel
              K P Q theta hinvariant gQ hK =>
            (z :
              okuyamaWajimaProperBranchNormalizerQuotient P Q))
          hcd
      apply Subtype.ext
      exact hquot
    have hsource :
        properBranchOriginalFixedToSourceKernelHom
            K P Q theta hinvariant gQ c =
          properBranchOriginalFixedToSourceKernelHom
            K P Q theta hinvariant gQ d := by
      exact eJ.injective himage
    apply Subtype.ext
    exact
      congrArg
        (fun x :
          okuyamaWajimaProperBranchQuotientSourceKernel
            K P Q theta hinvariant gQ =>
          (((x :
            okuyamaWajimaProperBranchQuotientSourceKernel
              K P Q theta hinvariant gQ) :
            okuyamaWajimaProperBranchQuotientAmbient P Q) : G))
        hsource
  · exact
      properBranchOriginalFixedToQuotientFixedHom_surjective
        K P Q theta hinvariant gQ hK

@[simp]
theorem properBranchTargetFixedKernelEquiv_apply_coe
    (hK : IsPPrimeGroup p K)
    (c : properBranchTargetFixedKernel K P) :
    ((properBranchTargetFixedKernelEquiv
        K P Q theta hinvariant gQ hK c :
      properBranchQuotientTargetFixedKernel
        K P Q theta hinvariant gQ hK) :
      okuyamaWajimaProperBranchNormalizerQuotient P Q) =
      ((properBranchOriginalFixedToImageKernelHom
          K P Q theta hinvariant gQ hK c :
        okuyamaWajimaProperBranchQuotientImageKernel
          K P Q theta hinvariant gQ) :
        okuyamaWajimaProperBranchNormalizerQuotient P Q) :=
  rfl

end FixedKernelCoordinates

section CharacterTransportCoordinates

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable (Q : Subgroup P) [Q.Normal]

local instance properBranchTargetCharacterPConjugationAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K (P : Subgroup G)

variable
  (theta :
    PInvariantPPrimeIrreducibleCharacter
      K (P : Subgroup G) p)
  (hinvariant :
    ∀ g : G, g • theta.1.1 = theta.1.1)
  (gQ :
    GlaubermanCorrespondence K
      (okuyamaWajimaProperBranchQ P Q) p)

/-- The canonical source coordinate from the abstract first-stage
fixed points `K^Q` to the literal quotient kernel `Jbar`. -/
def properBranchQFixedPointsToQuotientImageKernelEquiv
    (hK : IsPPrimeGroup p K) :
    FixedPoints.subgroup Q K ≃*
      okuyamaWajimaProperBranchQuotientImageKernel
        K P Q theta hinvariant gQ :=
  (okuyamaWajimaProperBranchQFixedPointsEquiv
      K (P : Subgroup G) Q).trans
    ((Subgroup.subgroupOfEquivOfLe
        (okuyamaWajimaProperBranchJ_le_QNormalizer
          K P Q)).symm.trans
      (okuyamaWajimaProperBranchQuotientSourceKernelEquiv
        K P Q theta hinvariant gQ hK))

/-- The canonical target coordinate from iterated fixed points
`(K^Q)^(P/Q)` to the literal quotient fixed-point kernel. -/
def properBranchIteratedFixedPointsToQuotientFixedEquiv
    (hK : IsPPrimeGroup p K) :
    FixedPoints.subgroup (P ⧸ Q)
        (FixedPoints.subgroup Q K) ≃*
      properBranchQuotientTargetFixedKernel
        K P Q theta hinvariant gQ hK :=
  (okuyamaWajimaProperBranchIteratedFixedPointsEquiv
      K (P : Subgroup G) Q).trans
    (properBranchTargetFixedKernelEquiv
      K P Q theta hinvariant gQ hK)

/-- The source and target coordinates form the exact square needed to
transport the second-stage restriction multiplicity. -/
theorem properBranchQuotientFixedPointsInclusion_commutes
    (hK : IsPPrimeGroup p K) :
    (properBranchQFixedPointsToQuotientImageKernelEquiv
        K P Q theta hinvariant gQ hK).toMonoidHom.comp
        (actionFixedPointsInclusion
          (P ⧸ Q) (FixedPoints.subgroup Q K)) =
      (coprimeFixedPointsInclusion
          (okuyamaWajimaProperBranchQuotientImageKernel
            K P Q theta hinvariant gQ)
          (okuyamaWajimaProperBranchQuotientSylow P Q :
            Subgroup
              (okuyamaWajimaProperBranchNormalizerQuotient P Q))).comp
        (properBranchIteratedFixedPointsToQuotientFixedEquiv
          K P Q theta hinvariant gQ hK).toMonoidHom := by
  ext x
  rfl

/-- Pulling the recursive quotient source character back to `K^Q`
recovers the first-stage strong Glauberman correspondent. -/
theorem properBranchQuotientSourceCharacter_comap_eq_QCorrespondent
    (hK : IsPPrimeGroup p K)
    (dQ : StrongActionGlaubermanCorrespondence Q K p) :
    (okuyamaWajimaProperBranchQuotientInvariantSourceCharacter
        K P Q theta hinvariant gQ hK).1.1.comap
        (properBranchQFixedPointsToQuotientImageKernelEquiv
          K P Q theta hinvariant gQ hK) =
      (okuyamaWajimaProperBranchQuotientInvariantCorrespondent
        (P : Subgroup G) K Q dQ
        (pInvariantCharacterEquivActionInvariant
          K (P : Subgroup G) theta)).1.1 := by
  let eQ :=
    okuyamaWajimaProperBranchQFixedPointsEquiv
      K (P : Subgroup G) Q
  let thetaAction :=
    pInvariantCharacterEquivActionInvariant
      K (P : Subgroup G) theta
  let psiAction :=
    okuyamaWajimaProperBranchQCorrespondent
      (P : Subgroup G) K Q dQ thetaAction
  let eJX :
      okuyamaWajimaProperBranchQuotientSourceKernel
          K P Q theta hinvariant gQ ≃*
        okuyamaWajimaProperBranchJ K P Q :=
    Subgroup.subgroupOfEquivOfLe
      (okuyamaWajimaProperBranchJ_le_QNormalizer
        K P Q)
  let eJ :=
    okuyamaWajimaProperBranchQuotientSourceKernelEquiv
      K P Q theta hinvariant gQ hK
  have hpsi :
      (psiAction.1.comap eQ.symm) =
        (okuyamaWajimaProperBranchPsi
          K P Q theta gQ).1 := by
    exact
      congrArg Subtype.val
        (okuyamaWajimaProperBranchAmbientQCorrespondent_eq
          K (P : Subgroup G) Q dQ gQ theta)
  apply IrreducibleCharacter.ext
  funext x
  rw [IrreducibleCharacter.comap_values]
  change
    (((okuyamaWajimaProperBranchPsi
        K P Q theta gQ).1.comap eJX).comap eJ.symm).values
          ((eQ.trans (eJX.symm.trans eJ)) x) =
      psiAction.1.values x
  calc
    (((okuyamaWajimaProperBranchPsi
        K P Q theta gQ).1.comap eJX).comap eJ.symm).values
          ((eQ.trans (eJX.symm.trans eJ)) x) =
        ((okuyamaWajimaProperBranchPsi
          K P Q theta gQ).1.comap eJX).values
          (eJ.symm ((eQ.trans
            (eJX.symm.trans eJ)) x)) := rfl
    _ =
        ((okuyamaWajimaProperBranchPsi
          K P Q theta gQ).1.comap eJX).values
          (eJX.symm (eQ x)) := by
      have htrans :
          (eJX.symm.trans eJ) (eQ x) =
            eJ (eJX.symm (eQ x)) := rfl
      have houter :
          (eQ.trans (eJX.symm.trans eJ)) x =
            (eJX.symm.trans eJ) (eQ x) := rfl
      rw [houter]
      rw [htrans]
      rw [eJ.symm_apply_apply]
    _ =
        (okuyamaWajimaProperBranchPsi
          K P Q theta gQ).1.values
          (eJX (eJX.symm (eQ x))) := rfl
    _ =
        (okuyamaWajimaProperBranchPsi
          K P Q theta gQ).1.values (eQ x) := by
      rw [eJX.apply_symm_apply]
    _ = psiAction.1.values x := by
      have hvalue :=
        congrArg
          (fun chi :
            IrreducibleCharacter
              (coprimeFixedPoints K
                (okuyamaWajimaProperBranchQ P Q)) =>
            chi.values (eQ x))
          hpsi
      simpa [psiAction] using hvalue.symm

variable
  (gBar :
    GlaubermanCorrespondence
      (okuyamaWajimaProperBranchQuotientImageKernel
        K P Q theta hinvariant gQ)
      (okuyamaWajimaProperBranchQuotientSylow P Q :
        Subgroup
          (okuyamaWajimaProperBranchNormalizerQuotient P Q))
      p)

/-- In iterated fixed-point coordinates, the quotient recursive
correspondent is exactly the second-stage strong correspondent. -/
theorem properBranchQuotientCorrespondent_comap_eq_secondStage
    (hK : IsPPrimeGroup p K)
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q K) p) :
    (gBar.characterEquiv
        (okuyamaWajimaProperBranchQuotientInvariantSourceCharacter
          K P Q theta hinvariant gQ hK)).1.comap
        (properBranchIteratedFixedPointsToQuotientFixedEquiv
          K P Q theta hinvariant gQ hK) =
      (dQuot.characterEquiv
        (okuyamaWajimaProperBranchQuotientInvariantCorrespondent
          (P : Subgroup G) K Q dQ
          (pInvariantCharacterEquivActionInvariant
            K (P : Subgroup G) theta))).1 := by
  let Jbar :=
    okuyamaWajimaProperBranchQuotientImageKernel
      K P Q theta hinvariant gQ
  let Pbar :=
    (okuyamaWajimaProperBranchQuotientSylow P Q :
      Subgroup
        (okuyamaWajimaProperBranchNormalizerQuotient P Q))
  let thetaBar :=
    okuyamaWajimaProperBranchQuotientInvariantSourceCharacter
      K P Q theta hinvariant gQ hK
  let eSource :=
    properBranchQFixedPointsToQuotientImageKernelEquiv
      K P Q theta hinvariant gQ hK
  let eTarget :=
    properBranchIteratedFixedPointsToQuotientFixedEquiv
      K P Q theta hinvariant gQ hK
  let etaQ :=
    okuyamaWajimaProperBranchQuotientInvariantCorrespondent
      (P : Subgroup G) K Q dQ
      (pInvariantCharacterEquivActionInvariant
        K (P : Subgroup G) theta)
  let xi :
      IrreducibleCharacter
        (FixedPoints.subgroup (P ⧸ Q)
          (FixedPoints.subgroup Q K)) :=
    (gBar.characterEquiv thetaBar).1.comap eTarget
  have hsource :
      thetaBar.1.1.comap eSource = etaQ.1.1 :=
    properBranchQuotientSourceCharacter_comap_eq_QCorrespondent
      K P Q theta hinvariant gQ hK dQ
  have htransport :
      restrictionMultiplicity
          (actionFixedPointsInclusion
            (P ⧸ Q) (FixedPoints.subgroup Q K))
          xi
          (thetaBar.1.1.comap eSource) =
        restrictionMultiplicity
          (coprimeFixedPointsInclusion Jbar Pbar)
          (gBar.characterEquiv thetaBar).1
          thetaBar.1.1 := by
    exact
      restrictionMultiplicity_comap_equiv
        eSource eTarget
        (coprimeFixedPointsInclusion Jbar Pbar)
        (actionFixedPointsInclusion
          (P ⧸ Q) (FixedPoints.subgroup Q K))
        (properBranchQuotientFixedPointsInclusion_commutes
          K P Q theta hinvariant gQ hK)
        (gBar.characterEquiv thetaBar).1
        thetaBar.1.1
  have hxi :
      ¬p ∣
        restrictionMultiplicity
          (actionFixedPointsInclusion
            (P ⧸ Q) (FixedPoints.subgroup Q K))
          xi etaQ.1.1 := by
    rw [← hsource, htransport]
    exact gBar.multiplicity_isPPrime thetaBar
  exact
    dQuot.eq_correspondent_of_multiplicity_isPPrime
      etaQ xi hxi

variable
  (gP :
    GlaubermanCorrespondence K (P : Subgroup G) p)

/-- Strong two-stage transitivity identifies the quotient recursive
target character, in the exact fixed-kernel coordinate, with the
original `P`-Glauberman correspondent. -/
theorem properBranchQuotientCorrespondent_comap_fixedKernelEquiv_eq_phi
    (hK : IsPPrimeGroup p K)
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q K) p) :
    (gBar.characterEquiv
        (okuyamaWajimaProperBranchQuotientInvariantSourceCharacter
          K P Q theta hinvariant gQ hK)).1.comap
        (properBranchTargetFixedKernelEquiv
          K P Q theta hinvariant gQ hK) =
      (okuyamaWajimaProperBranchPhi
        K P theta gP).1 := by
  let thetaBar :=
    okuyamaWajimaProperBranchQuotientInvariantSourceCharacter
      K P Q theta hinvariant gQ hK
  let phiBar :=
    gBar.characterEquiv thetaBar
  let eFixed :=
    properBranchTargetFixedKernelEquiv
      K P Q theta hinvariant gQ hK
  let eIter :=
    okuyamaWajimaProperBranchIteratedFixedPointsEquiv
      K (P : Subgroup G) Q
  let etaQ :=
    okuyamaWajimaProperBranchQuotientInvariantCorrespondent
      (P : Subgroup G) K Q dQ
      (pInvariantCharacterEquivActionInvariant
        K (P : Subgroup G) theta)
  have hsecond :
      phiBar.1.comap (eIter.trans eFixed) =
        (dQuot.characterEquiv etaQ).1 := by
    exact
      properBranchQuotientCorrespondent_comap_eq_secondStage
        K P Q theta hinvariant gQ gBar hK dQ dQuot
  have hback :=
    congrArg
      (fun chi :
        IrreducibleCharacter
          (FixedPoints.subgroup (P ⧸ Q)
            (FixedPoints.subgroup Q K)) =>
        chi.comap eIter.symm)
      hsecond
  have hfixed :
      phiBar.1.comap eFixed =
        (dQuot.characterEquiv etaQ).1.comap eIter.symm := by
    rw [IrreducibleCharacter.comap_trans] at hback
    have hequiv :
        eIter.symm.trans (eIter.trans eFixed) =
          eFixed := by
      ext x
      simp
    rw [hequiv] at hback
    exact hback
  calc
    phiBar.1.comap eFixed =
        (dQuot.characterEquiv etaQ).1.comap eIter.symm :=
      hfixed
    _ =
        (okuyamaWajimaProperBranchAmbientIteratedCorrespondent
          K (P : Subgroup G) Q dQ dQuot theta).1 := by
      rfl
    _ =
        (okuyamaWajimaProperBranchPhi
          K P theta gP).1 :=
      congrArg Subtype.val
        (okuyamaWajimaProperBranchAmbientIteratedCorrespondent_eq_phi
          K P Q theta gP hK dQ dQuot)

end CharacterTransportCoordinates

section ExtensionCoordinates

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable (Q : Subgroup P) [Q.Normal]

local instance properBranchTargetExtensionPConjugationAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K (P : Subgroup G)

variable
  (theta :
    PInvariantPPrimeIrreducibleCharacter
      K (P : Subgroup G) p)
  (hinvariant :
    ∀ g : G, g • theta.1.1 = theta.1.1)
  (gQ :
    GlaubermanCorrespondence K
      (okuyamaWajimaProperBranchQ P Q) p)

/-- The original fixed-point kernel, regarded inside `N_G(P)`. -/
abbrev properBranchTargetFixedKernelInPNormalizer :
    Subgroup (properBranchTargetPNormalizer P) :=
  (properBranchTargetFixedKernel K P).subgroupOf
    (properBranchTargetPNormalizer P)

omit [Finite G] [Fact p.Prime] [Q.Normal] in
/-- `C_K(P)` lies in the Sylow normalizer. -/
theorem properBranchTargetFixedKernel_le_PNormalizer :
    properBranchTargetFixedKernel K P ≤
      properBranchTargetPNormalizer P :=
  inf_le_right.trans
    (Subgroup.centralizer_le_normalizer
      ((P : Subgroup G) : Set G))

/-- The internal copy of `C_K(P)` in `N_G(P)` is canonically the
ambient fixed-point subgroup. -/
def properBranchTargetFixedKernelInPNormalizerEquiv :
    properBranchTargetFixedKernelInPNormalizer K P ≃*
      properBranchTargetFixedKernel K P :=
  Subgroup.subgroupOfEquivOfLe
    (properBranchTargetFixedKernel_le_PNormalizer K P)

variable
  [hQnormal :
    (properBranchTargetQInPNormalizer P Q).Normal]

/-- The image of `C_K(P)` in `N_G(P) / Q`. -/
abbrev properBranchTargetFixedKernelNormalizerQuotientImage :
    Subgroup
      (properBranchTargetPNormalizer P ⧸
        properBranchTargetQInPNormalizer P Q) :=
  (properBranchTargetFixedKernelInPNormalizer K P).map
    (QuotientGroup.mk'
      (properBranchTargetQInPNormalizer P Q))

/-- The quotient kernel is a `p`-group in `N_G(P)`. -/
theorem properBranchTargetQInPNormalizer_isPGroup :
    IsPGroup p
      (properBranchTargetQInPNormalizer P Q) := by
  exact
    (okuyamaWajimaProperBranchAmbientQ_isPGroup P Q).of_equiv
      (Subgroup.subgroupOfEquivOfLe
        ((okuyamaWajimaProperBranchAmbientQ_le_P
          (P : Subgroup G) Q).trans
          Subgroup.le_normalizer)).symm

/-- The internal fixed-point kernel is a `p'`-group. -/
theorem properBranchTargetFixedKernelInPNormalizer_isPPrime
    (hK : IsPPrimeGroup p K) :
    IsPPrimeGroup p
      (properBranchTargetFixedKernelInPNormalizer K P) := by
  have hC :
      IsPPrimeGroup p
        (properBranchTargetFixedKernel K P) := by
    exact
      (hK.to_subgroup
        ((properBranchTargetFixedKernel K P).subgroupOf K)).of_equiv
        (Subgroup.subgroupOfEquivOfLe
          (show properBranchTargetFixedKernel K P ≤ K
            from inf_le_left))
  exact
    hC.of_equiv
      (properBranchTargetFixedKernelInPNormalizerEquiv
        K P).symm

/-- The two internal subgroups `C_K(P)` and `Q` in `N_G(P)` are
disjoint by coprimality. -/
theorem properBranchTargetFixedKernelInPNormalizer_disjoint_Q
    (hK : IsPPrimeGroup p K) :
    Disjoint
      (properBranchTargetFixedKernelInPNormalizer K P)
      (properBranchTargetQInPNormalizer P Q) :=
  (IsPGroup.disjoint_of_isPPrimeGroup
    (properBranchTargetQInPNormalizer_isPGroup P Q)
    (properBranchTargetFixedKernelInPNormalizer_isPPrime
      K P hK)).symm

/-- Canonical quotient-image coordinate for `C_K(P)`. -/
def properBranchTargetFixedKernelNormalizerQuotientImageEquiv
    (hK : IsPPrimeGroup p K) :
    properBranchTargetFixedKernelInPNormalizer K P ≃*
      properBranchTargetFixedKernelNormalizerQuotientImage
        K P Q :=
  IrreducibleCharacter.subgroupEquivQuotientImageOfDisjoint
    (properBranchTargetFixedKernelInPNormalizer K P)
    (properBranchTargetQInPNormalizer P Q)
    (properBranchTargetFixedKernelInPNormalizer_disjoint_Q
      K P Q hK)

/-- The recursive quotient fixed kernel, transported into the literal
image of `C_K(P)` in `N_G(P) / Q`. -/
def properBranchQuotientFixedToNormalizerImageEquiv
    (hK : IsPPrimeGroup p K) :
    properBranchQuotientTargetFixedKernel
        K P Q theta hinvariant gQ hK ≃*
      properBranchTargetFixedKernelNormalizerQuotientImage
        K P Q :=
  (properBranchTargetFixedKernelEquiv
      K P Q theta hinvariant gQ hK).symm.trans
    ((properBranchTargetFixedKernelInPNormalizerEquiv
      K P).symm.trans
      (properBranchTargetFixedKernelNormalizerQuotientImageEquiv
        K P Q hK))

/-- The quotient-normalizer and fixed-kernel equivalences commute with
the two literal inclusion maps. -/
theorem properBranchTargetQuotientExtension_inclusion_square
    (hK : IsPPrimeGroup p K)
    (hPN :
      properBranchTargetPNormalizer P ≤
        okuyamaWajimaProperBranchQuotientAmbient P Q) :
    (properBranchTargetNormalizerQuotientEquiv
        P Q hPN).toMonoidHom.comp
        (Subgroup.inclusion
          (inf_le_right.trans
            (Subgroup.centralizer_le_normalizer
              ((okuyamaWajimaProperBranchQuotientSylow P Q :
                Subgroup
                  (okuyamaWajimaProperBranchNormalizerQuotient P Q)) :
                Set
                  (okuyamaWajimaProperBranchNormalizerQuotient P Q))))) =
      (properBranchTargetFixedKernelNormalizerQuotientImage
          K P Q).subtype.comp
        (properBranchQuotientFixedToNormalizerImageEquiv
          K P Q theta hinvariant gQ hK).toMonoidHom := by
  let X :=
    okuyamaWajimaProperBranchQuotientAmbient P Q
  let Xbar :=
    okuyamaWajimaProperBranchNormalizerQuotient P Q
  let PX :=
    properBranchTargetSylowInQNormalizer P Q
  let QX :=
    okuyamaWajimaProperBranchQuotientKernel P Q
  let NX :=
    properBranchTargetInternalPNormalizer P Q
  let NP :=
    properBranchTargetPNormalizer P
  let QNP :=
    properBranchTargetQInPNormalizer P Q
  let C :=
    properBranchTargetFixedKernel K P
  let CNP :=
    properBranchTargetFixedKernelInPNormalizer K P
  let Bbar :=
    properBranchTargetFixedKernelNormalizerQuotientImage
      K P Q
  let Dbar :=
    properBranchQuotientTargetFixedKernel
      K P Q theta hinvariant gQ hK
  let eN :=
    properBranchTargetNormalizerQuotientEquiv P Q hPN
  let eInternal :=
    properBranchTargetInternalPNormalizerEquiv P Q hPN
  let eD :=
    properBranchTargetFixedKernelEquiv
      K P Q theta hinvariant gQ hK
  let eC :=
    properBranchTargetFixedKernelInPNormalizerEquiv K P
  let eCQ :=
    properBranchTargetFixedKernelNormalizerQuotientImageEquiv
      K P Q hK
  let eB :=
    properBranchQuotientFixedToNormalizerImageEquiv
      K P Q theta hinvariant gQ hK
  ext d
  let c : C := eD.symm d
  let cNP : CNP := eC.symm c
  let x : NX := eInternal.symm (cNP : NP)
  let z :=
    Sylow.quotientNormalizerHom PX QX x
  have hxsource :
      (x : X) =
        (properBranchOriginalFixedToSourceKernelHom
          K P Q theta hinvariant gQ c :
          okuyamaWajimaProperBranchQuotientSourceKernel
            K P Q theta hinvariant gQ) := by
    apply Subtype.ext
    rfl
  have hd :
      (d : Xbar) =
        okuyamaWajimaProperBranchQuotientMap P Q (x : X) := by
    calc
      (d : Xbar) =
          (eD c : Xbar) :=
        congrArg Subtype.val (eD.apply_symm_apply d).symm
      _ =
          okuyamaWajimaProperBranchQuotientMap P Q
            (properBranchOriginalFixedToSourceKernelHom
              K P Q theta hinvariant gQ c) :=
        properBranchTargetFixedKernelEquiv_apply_coe
          K P Q theta hinvariant gQ hK c
      _ =
          okuyamaWajimaProperBranchQuotientMap P Q
            (x : X) :=
        congrArg
          (okuyamaWajimaProperBranchQuotientMap P Q)
          hxsource.symm
  have hz :
      z =
        Subgroup.inclusion
          (inf_le_right.trans
            (Subgroup.centralizer_le_normalizer
              ((okuyamaWajimaProperBranchQuotientSylow P Q :
                Subgroup Xbar) : Set Xbar))) d := by
    apply Subtype.ext
    exact hd.symm
  have heB :
      ((eB d : Bbar) : NP ⧸ QNP) =
        QuotientGroup.mk' QNP (cNP : NP) := by
    change
      ((eCQ cNP : Bbar) : NP ⧸ QNP) =
        QuotientGroup.mk' QNP (cNP : NP)
    exact
      IrreducibleCharacter.subgroupEquivQuotientImageOfDisjoint_apply_coe
        CNP QNP
        (properBranchTargetFixedKernelInPNormalizer_disjoint_Q
          K P Q hK) cNP
  change
    eN
        (Subgroup.inclusion
          (inf_le_right.trans
            (Subgroup.centralizer_le_normalizer
              ((okuyamaWajimaProperBranchQuotientSylow P Q :
                Subgroup Xbar) : Set Xbar))) d) =
      ((eB d : Bbar) : NP ⧸ QNP)
  rw [← hz,
    properBranchTargetNormalizerQuotientEquiv_apply_quotient]
  rw [heB]
  exact
    congrArg (QuotientGroup.mk' QNP)
      (eInternal.apply_symm_apply (cNP : NP))

omit hQnormal in
/-- The quotient recursive target extension problem is the original
`N_G(P)` extension problem, provided that `N_G(P)` normalizes `Q`.

This is the exact target field needed by the recursive quotient adapter.
The proof factors through the literal image of `C_K(P)` in
`N_G(P) / Q`: first transport along the exact normalizer/fixed-kernel
square, then descend across the commuting `p`-kernel, and finally
transport the internal copy of `C_K(P)` back to the ambient fixed-point
subgroup. -/
theorem
    okuyamaWajimaProperBranchQuotientTargetExtensionCoordinateComparison_of_normalizer_le
    (gP :
      GlaubermanCorrespondence K (P : Subgroup G) p)
    (hK : IsPPrimeGroup p K)
    (hPN :
      properBranchTargetPNormalizer P ≤
        okuyamaWajimaProperBranchQuotientAmbient P Q) :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        (okuyamaWajimaProperBranchQuotientImageKernel
          K P Q theta hinvariant gQ)
        (okuyamaWajimaProperBranchQuotientSylow P Q)
        (okuyamaWajimaProperBranchQuotientInvariantSourceCharacter
          K P Q theta hinvariant gQ hK)
        (okuyamaWajimaProperBranchQuotientSourceCharacter_invariant
          K P Q theta hinvariant gQ hK)
        (okuyamaWajimaProperBranchQuotientGlaubermanCorrespondence
          K P Q theta hinvariant gQ hK) ↔
      OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP := by
  letI :
      (properBranchTargetQInPNormalizer P Q).Normal :=
    properBranchTargetQInPNormalizer_normal P Q hPN
  rw [
    okuyamaWajimaProperBranchPhi_extendsToPNormalizer_iff,
    okuyamaWajimaProperBranchPhi_extendsToPNormalizer_iff]
  let NP := properBranchTargetPNormalizer P
  let QNP := properBranchTargetQInPNormalizer P Q
  let C := properBranchTargetFixedKernel K P
  let CNP := properBranchTargetFixedKernelInPNormalizer K P
  let Bbar :=
    properBranchTargetFixedKernelNormalizerQuotientImage
      K P Q
  let Xbar :=
    okuyamaWajimaProperBranchNormalizerQuotient P Q
  let Jbar :=
    okuyamaWajimaProperBranchQuotientImageKernel
      K P Q theta hinvariant gQ
  let Pbar :=
    okuyamaWajimaProperBranchQuotientSylow P Q
  let Dbar :=
    properBranchQuotientTargetFixedKernel
      K P Q theta hinvariant gQ hK
  let Tbar :=
    Subgroup.normalizer
      ((Pbar : Subgroup Xbar) : Set Xbar)
  let thetaBar :=
    okuyamaWajimaProperBranchQuotientInvariantSourceCharacter
      K P Q theta hinvariant gQ hK
  let gBar :=
    okuyamaWajimaProperBranchQuotientGlaubermanCorrespondence
      K P Q theta hinvariant gQ hK
  let phiBar : PPrimeIrreducibleCharacter Dbar p :=
    gBar.characterEquiv thetaBar
  let phi : PPrimeIrreducibleCharacter C p :=
    okuyamaWajimaProperBranchPhi K P theta gP
  let eN : Tbar ≃* NP ⧸ QNP :=
    properBranchTargetNormalizerQuotientEquiv P Q hPN
  let eD : C ≃* Dbar :=
    properBranchTargetFixedKernelEquiv
      K P Q theta hinvariant gQ hK
  let eC : CNP ≃* C :=
    properBranchTargetFixedKernelInPNormalizerEquiv K P
  let eCQ : CNP ≃* Bbar :=
    properBranchTargetFixedKernelNormalizerQuotientImageEquiv
      K P Q hK
  let eB : Dbar ≃* Bbar :=
    properBranchQuotientFixedToNormalizerImageEquiv
      K P Q theta hinvariant gQ hK
  let dQ : StrongActionGlaubermanCorrespondence Q K p :=
    okuyamaWajimaProperBranchQStrongCorrespondence
      (P : Subgroup G) K Q P.isPGroup' hK
  let dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q K) p :=
    okuyamaWajimaProperBranchQuotientStrongCorrespondence
      (P : Subgroup G) K Q P.isPGroup' hK
  have hcharacter :
      phiBar.1.comap eD = phi.1 := by
    exact
      properBranchQuotientCorrespondent_comap_fixedKernelEquiv_eq_phi
        K P Q theta hinvariant gQ gBar gP hK dQ dQuot
  have hcharacterBack :
      phi.1.comap eD.symm = phiBar.1 := by
    have h :=
      congrArg
        (fun chi : IrreducibleCharacter C =>
          chi.comap eD.symm)
        hcharacter
    rw [IrreducibleCharacter.comap_trans] at h
    have hequiv :
        eD.symm.trans eD = MulEquiv.refl Dbar := by
      ext c
      simp
    rw [hequiv] at h
    simpa using h.symm
  let psi : IrreducibleCharacter CNP :=
    phi.1.comap eC
  let psiBar : IrreducibleCharacter Bbar :=
    psi.comap eCQ.symm
  have hpsiBar :
      psiBar.comap eB = phiBar.1 := by
    calc
      psiBar.comap eB =
          phi.1.comap eD.symm := by
        change
          ((phi.1.comap eC).comap eCQ.symm).comap eB =
            phi.1.comap eD.symm
        rw [IrreducibleCharacter.comap_trans,
          IrreducibleCharacter.comap_trans]
        congr 1
        ext d
        simp [eB, eCQ, eC, eD,
          properBranchQuotientFixedToNormalizerImageEquiv]
      _ = phiBar.1 :=
        hcharacterBack
  have hquotientCoordinate :
      (∃ etaBar : IrreducibleCharacter Tbar,
          IrreducibleCharacter.IsExtensionAlong
            (Subgroup.inclusion
              (inf_le_right.trans
                (Subgroup.centralizer_le_normalizer
                  ((Pbar : Subgroup Xbar) : Set Xbar))))
            phiBar.1 etaBar) ↔
        ∃ etaQuotient : IrreducibleCharacter (NP ⧸ QNP),
          IrreducibleCharacter.IsExtensionAlong
            Bbar.subtype psiBar etaQuotient := by
    have htransport :=
      IrreducibleCharacter.exists_extensionAlong_equiv_iff
        Bbar.subtype
        (Subgroup.inclusion
          (inf_le_right.trans
            (Subgroup.centralizer_le_normalizer
              ((Pbar : Subgroup Xbar) : Set Xbar))))
        eN eB
        (properBranchTargetQuotientExtension_inclusion_square
          K P Q theta hinvariant gQ hK hPN)
        psiBar
    rw [hpsiBar] at htransport
    exact htransport.symm
  have hcentral :
      QNP ≤ Subgroup.centralizer (CNP : Set NP) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    apply Subtype.ext
    have hcomm :
        (((q : NP) : G) * ((c : NP) : G)) =
          (((c : NP) : G) * ((q : NP) : G)) :=
      (Subgroup.mem_centralizer_iff.mp hc.2)
        (((q : NP) : G))
        (okuyamaWajimaProperBranchAmbientQ_le_P
          (P : Subgroup G) Q hq)
    exact hcomm.symm
  have hquotientDescent :
      (∃ etaQuotient : IrreducibleCharacter (NP ⧸ QNP),
          IrreducibleCharacter.IsExtensionAlong
            Bbar.subtype psiBar etaQuotient) ↔
        ∃ etaInternal : IrreducibleCharacter NP,
          IrreducibleCharacter.IsExtensionAlong
            CNP.subtype psi etaInternal := by
    have hcomparison :=
      IrreducibleCharacter.exists_extension_quotient_image_iff
        CNP QNP psi eCQ
        (IrreducibleCharacter.subgroupEquivQuotientImageOfDisjoint_apply_coe
            CNP QNP
            (properBranchTargetFixedKernelInPNormalizer_disjoint_Q
              K P Q hK))
        (properBranchTargetQInPNormalizer_isPGroup P Q)
        (properBranchTargetFixedKernelInPNormalizer_isPPrime
          K P hK)
        (by
          simpa [psi, IrreducibleCharacter.IsPPrimeDegree]
            using phi.2)
        hcentral
    exact hcomparison
  have horiginalCoordinate :
      (∃ etaOriginal : IrreducibleCharacter NP,
          IrreducibleCharacter.IsExtensionAlong
            (Subgroup.inclusion
              (properBranchTargetFixedKernel_le_PNormalizer
                K P))
            phi.1 etaOriginal) ↔
        ∃ etaInternal : IrreducibleCharacter NP,
          IrreducibleCharacter.IsExtensionAlong
            CNP.subtype psi etaInternal := by
    have hsquare :
        (MulEquiv.refl NP).toMonoidHom.comp CNP.subtype =
          (Subgroup.inclusion
            (properBranchTargetFixedKernel_le_PNormalizer
              K P)).comp eC.toMonoidHom := by
      ext c
      rfl
    exact
      IrreducibleCharacter.exists_extensionAlong_equiv_iff
        (Subgroup.inclusion
          (properBranchTargetFixedKernel_le_PNormalizer K P))
        CNP.subtype
        (MulEquiv.refl NP) eC hsquare phi.1
  exact
    hquotientCoordinate.trans
      (hquotientDescent.trans horiginalCoordinate.symm)

end ExtensionCoordinates

section SelectedExtensionCoordinate

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable
  (hK : IsPPrimeGroup p K)
  (hKP : (K ⊔ (P : Subgroup G)).Normal)

local instance selectedTargetPConjugationAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K (P : Subgroup G)

local instance selectedTargetComplementConjugationAction :
    MulDistribMulAction
      (okuyamaWajimaProperBranchComplement K P hK hKP)
      P :=
  normalizingSubgroupConjugationAction
    (P : Subgroup G)
    (okuyamaWajimaProperBranchComplement K P hK hKP)
    (okuyamaWajimaAmbientComplement_le_normalizer
      P K hK hKP)

variable
  {L :
    Subgroup
      (okuyamaWajimaProperBranchComplement K P hK hKP)}
  (d :
    OkuyamaWajimaCyclicQuotientSubgroup
      (okuyamaWajimaProperBranchComplement K P hK hKP)
      P L)
  (theta :
    PInvariantPPrimeIrreducibleCharacter
      K (P : Subgroup G) p)
  (hinvariant :
    ∀ g : G, g • theta.1.1 = theta.1.1)
  (gQ :
    GlaubermanCorrespondence K
      (okuyamaWajimaProperBranchQ
        P d.fixedPointPreimage) p)
  (gP :
    GlaubermanCorrespondence K (P : Subgroup G) p)

/-- Automatic target-coordinate comparison for the subgroup selected by
the proper-branch Gorenstein construction. -/
theorem
    okuyamaWajimaProperBranchSelectedQuotientTargetExtensionCoordinateComparison :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        (okuyamaWajimaProperBranchQuotientImageKernel
          K P d.fixedPointPreimage theta hinvariant gQ)
        (okuyamaWajimaProperBranchQuotientSylow
          P d.fixedPointPreimage)
        (okuyamaWajimaProperBranchQuotientInvariantSourceCharacter
          K P d.fixedPointPreimage theta hinvariant gQ hK)
        (okuyamaWajimaProperBranchQuotientSourceCharacter_invariant
          K P d.fixedPointPreimage theta hinvariant gQ hK)
        (okuyamaWajimaProperBranchQuotientGlaubermanCorrespondence
          K P d.fixedPointPreimage theta hinvariant gQ hK) ↔
      OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP :=
  okuyamaWajimaProperBranchQuotientTargetExtensionCoordinateComparison_of_normalizer_le
    K P d.fixedPointPreimage theta hinvariant gQ gP hK
    (properBranchTargetPNormalizer_le_selectedQNormalizer
      K P hK hKP d)

end SelectedExtensionCoordinate

end McKayConjecture
