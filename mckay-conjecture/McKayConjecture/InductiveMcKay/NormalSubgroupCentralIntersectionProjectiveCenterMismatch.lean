/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveNormalCentralMismatch
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45ProjectiveMismatch

/-!
# The scalar mismatch killed by the Okuyama--Wajima center identity

The normalized Okuyama--Wajima construction preserves normalized values on
the center of `CP`.  This file transports that identity to the internal
copy of `N_{CP}(P)` used by the ambient inertia triples, and then applies the
generic scalar-mismatch theorem.

The result is intentionally only a statement on the image of `Z(CP)`.
Elements of the full matched projective centralizer need not come from that
center.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CharacterTriple.AssociatedProjectiveRepresentation
open CliffordEquivalence
open GroupTheory
open ComplementReduction

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- An ambient-central element of `CP`, represented in the internal copy of
`N_{CP}(P)` inside `N_X(P)`. -/
def productAmbientCenterInternalElement
    (z : Subgroup.center (product S C)) :
    internalProductNormalizer S C := by
  let zProduct : product S C := z.1
  have hzCentralizer :
      (zProduct : X) ∈
        Subgroup.centralizer
          (product S C : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    let yProduct : product S C := ⟨y, hy⟩
    exact
      congrArg Subtype.val
        ((Subgroup.mem_center_iff.mp z.2) yProduct)
  exact
    ⟨⟨(zProduct : X),
        centralizer_product_le_ambientNormalizer
          S C hzCentralizer⟩,
      zProduct.2⟩

@[simp]
theorem productAmbientCenterInternalElement_coe
    (z : Subgroup.center (product S C)) :
    (((productAmbientCenterInternalElement S C z :
          internalProductNormalizer S C) :
        ambientNormalizer S) : X) =
      ((z.1 : product S C) : X) :=
  rfl

/-- The concrete Glauberman--Okuyama--Wajima correspondence preserves
normalized values after its target is transported to the internal
normalizer copy used by Proposition 4.5. -/
theorem complementCharacterEquivOfGlauberman_internal_central_cross
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (z : Subgroup.center (product S C)) :
    theta.1.values z.1 *
        ((internalTheorem44CharacterEquiv
          S C
          (complementCharacterEquivOfGlauberman
            S C hcentral g) theta).1.degree : ℂ) =
      (internalTheorem44CharacterEquiv
        S C
        (complementCharacterEquivOfGlauberman
          S C hcentral g) theta).1.values
          (productAmbientCenterInternalElement S C z) *
        (theta.1.degree : ℂ) := by
  have hcross :=
    (complementCentralScalarLocalCorrespondenceOfGlauberman
      S C hcentral g).correspondence_central_cross
      theta z.1 z.2
      (Subgroup.center_le_normalizer
        (productSylow S C :
          Set (product S C)) z.2)
  let zExternal :
      Subgroup.normalizer
        (productSylow S C :
          Set (product S C)) :=
    ⟨z.1,
      Subgroup.center_le_normalizer
        (productSylow S C :
          Set (product S C)) z.2⟩
  have hzTransport :
      (productNormalizerEquivInternal S C).symm
          (productAmbientCenterInternalElement S C z) =
        zExternal := by
    apply Subtype.ext
    rfl
  have hdegree :
      (internalTheorem44CharacterEquiv
          S C
          (complementCharacterEquivOfGlauberman
            S C hcentral g) theta).1.degree =
        (complementCharacterEquivOfGlauberman
          S C hcentral g theta).1.degree := by
    rfl
  have hvalue :
      (internalTheorem44CharacterEquiv
          S C
          (complementCharacterEquivOfGlauberman
            S C hcentral g) theta).1.values
            (productAmbientCenterInternalElement S C z) =
        (complementCharacterEquivOfGlauberman
          S C hcentral g theta).1.values
          zExternal := by
    change
      ((complementCharacterEquivOfGlauberman
          S C hcentral g theta).1.comap
          (productNormalizerEquivInternal S C).symm).values
            (productAmbientCenterInternalElement S C z) =
        (complementCharacterEquivOfGlauberman
          S C hcentral g theta).1.values zExternal
    rw [IrreducibleCharacter.comap_values, hzTransport]
  rw [hdegree, hvalue]
  exact hcross

/-- A central element of `CP`, viewed in the matched normal-central
subgroup for the canonical embedding of ambient inertia triples. -/
def productAmbientCenterComparisonElement
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (characterEquiv_smul :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      ∀ (h : ambientNormalizer S)
        (theta :
          PPrimeIrreducibleCharacter
            (product S C) q),
        internalTheorem44CharacterEquiv
            S C theorem44Equiv (h • theta) =
          h • internalTheorem44CharacterEquiv
            S C theorem44Equiv theta)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (z : Subgroup.center (product S C)) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    projectiveComparisonNormalCentralSubgroup
      (ofInertia (product S C) theta.1)
      (ofInertia
        (internalProductNormalizer S C)
        (internalTheorem44CharacterEquiv
          S C theorem44Equiv theta).1)
      (MatchedInertiaRestriction.embedding
        (product S C)
        (ambientNormalizer S)
        (internalProductNormalizer S C)
        (internalTheorem44CharacterEquiv
          S C theorem44Equiv)
        characterEquiv_smul theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let phi :=
    internalTheorem44CharacterEquiv
      S C theorem44Equiv theta
  let zInternal :=
    productAmbientCenterInternalElement S C z
  let b :
      IrreducibleCharacter.inertia
        (internalProductNormalizer S C) phi.1 :=
    IrreducibleCharacter.inertiaInclusion
      (internalProductNormalizer S C) phi.1 zInternal
  let e :=
    MatchedInertiaRestriction.embedding
      (product S C)
      (ambientNormalizer S)
      (internalProductNormalizer S C)
      (internalTheorem44CharacterEquiv
        S C theorem44Equiv)
      characterEquiv_smul theta
  have hbcentral :
      e b ∈
        Subgroup.centralizer
          ((ofInertia (product S C) theta.1).normalSubgroup :
            Set
              (IrreducibleCharacter.inertia
                (product S C) theta.1)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    apply Subtype.ext
    change
      (n : X) * ((z.1 : product S C) : X) =
        ((z.1 : product S C) : X) * (n : X)
    let nProduct : product S C :=
      ⟨(n :
          IrreducibleCharacter.inertia
            (product S C) theta.1), hn⟩
    exact
      congrArg Subtype.val
        ((Subgroup.mem_center_iff.mp z.2) nProduct)
  refine ⟨⟨b, hbcentral⟩, ?_⟩
  exact zInternal.property

/-- The canonical homomorphism from `Z(CP)` into the matched
normal-central subgroup of the ambient projective comparison. -/
def productAmbientCenterComparisonHom
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (characterEquiv_smul :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      ∀ (h : ambientNormalizer S)
        (theta :
          PPrimeIrreducibleCharacter
            (product S C) q),
        internalTheorem44CharacterEquiv
            S C theorem44Equiv (h • theta) =
          h • internalTheorem44CharacterEquiv
            S C theorem44Equiv theta)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    Subgroup.center (product S C) →*
      projectiveComparisonNormalCentralSubgroup
        (ofInertia (product S C) theta.1)
        (ofInertia
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C theorem44Equiv theta).1)
        (MatchedInertiaRestriction.embedding
          (product S C)
          (ambientNormalizer S)
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C theorem44Equiv)
          characterEquiv_smul theta) where
  toFun :=
    productAmbientCenterComparisonElement
      S C hgenerate theorem44Equiv
      characterEquiv_smul theta
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' z w := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The same center map, now regarded as taking values in the full
projective-comparison centralizer. -/
def productAmbientCenterProjectiveComparisonHom
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (characterEquiv_smul :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      ∀ (h : ambientNormalizer S)
        (theta :
          PPrimeIrreducibleCharacter
            (product S C) q),
        internalTheorem44CharacterEquiv
            S C theorem44Equiv (h • theta) =
          h • internalTheorem44CharacterEquiv
            S C theorem44Equiv theta)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    Subgroup.center (product S C) →*
      projectiveComparisonCentralizer
        (ofInertia (product S C) theta.1)
        (MatchedInertiaRestriction.embedding
          (product S C)
          (ambientNormalizer S)
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C theorem44Equiv)
          characterEquiv_smul theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    (projectiveComparisonNormalCentralSubgroup
        (ofInertia (product S C) theta.1)
        (ofInertia
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C theorem44Equiv theta).1)
        (MatchedInertiaRestriction.embedding
          (product S C)
          (ambientNormalizer S)
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C theorem44Equiv)
          characterEquiv_smul theta)).subtype.comp
      (productAmbientCenterComparisonHom
        S C hgenerate theorem44Equiv
        characterEquiv_smul theta)

/-- The image of `Z(CP)` is central in the projective-comparison
centralizer.  Hence its range is a normal subgroup and may be quotiented
out without adding any closure operation. -/
theorem productAmbientCenterProjectiveComparisonHom_range_le_center
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (characterEquiv_smul :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      ∀ (h : ambientNormalizer S)
        (theta :
          PPrimeIrreducibleCharacter
            (product S C) q),
        internalTheorem44CharacterEquiv
            S C theorem44Equiv (h • theta) =
          h • internalTheorem44CharacterEquiv
            S C theorem44Equiv theta)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    MonoidHom.range
        (productAmbientCenterProjectiveComparisonHom
          S C hgenerate theorem44Equiv
          characterEquiv_smul theta) ≤
      Subgroup.center
        (projectiveComparisonCentralizer
          (ofInertia (product S C) theta.1)
          (MatchedInertiaRestriction.embedding
            (product S C)
            (ambientNormalizer S)
            (internalProductNormalizer S C)
            (internalTheorem44CharacterEquiv
              S C theorem44Equiv)
            characterEquiv_smul theta)) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let embedding :=
    MatchedInertiaRestriction.embedding
      (product S C)
      (ambientNormalizer S)
      (internalProductNormalizer S C)
      (internalTheorem44CharacterEquiv
        S C theorem44Equiv)
      characterEquiv_smul theta
  let groupData :=
    productAmbientInertiaRestrictionGroupData
      S C hgenerate theorem44Equiv
      characterEquiv_smul theta
  rintro c ⟨z, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro b
  let cNormal :=
    productAmbientCenterComparisonElement
      S C hgenerate theorem44Equiv
      characterEquiv_smul theta z
  change b * cNormal.1 = cNormal.1 * b
  apply Subtype.ext
  apply groupData.embedding_injective
  change
    embedding
          (b :
            IrreducibleCharacter.inertia
              (internalProductNormalizer S C)
              (internalTheorem44CharacterEquiv
                S C theorem44Equiv theta).1) *
        embedding
          (cNormal.1 :
            IrreducibleCharacter.inertia
              (internalProductNormalizer S C)
              (internalTheorem44CharacterEquiv
                S C theorem44Equiv theta).1) =
      embedding
          (cNormal.1 :
            IrreducibleCharacter.inertia
              (internalProductNormalizer S C)
              (internalTheorem44CharacterEquiv
                S C theorem44Equiv theta).1) *
        embedding
          (b :
            IrreducibleCharacter.inertia
              (internalProductNormalizer S C)
              (internalTheorem44CharacterEquiv
                S C theorem44Equiv theta).1)
  have hcNormal :
      embedding (cNormal.1 :
        IrreducibleCharacter.inertia
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C theorem44Equiv theta).1) ∈
        (ofInertia (product S C) theta.1).normalSubgroup :=
    groupData.rightNormal_le_comap_leftNormal cNormal.2
  exact
    ((Subgroup.mem_centralizer_iff.mp b.2)
      (embedding (cNormal.1 :
        IrreducibleCharacter.inertia
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C theorem44Equiv theta).1))
      hcNormal).symm

/-- The center-image subgroup used in the sharp OW residual quotient is
normal in the comparison centralizer. -/
theorem productAmbientCenterProjectiveComparisonHom_range_normal
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (characterEquiv_smul :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      ∀ (h : ambientNormalizer S)
        (theta :
          PPrimeIrreducibleCharacter
            (product S C) q),
        internalTheorem44CharacterEquiv
            S C theorem44Equiv (h • theta) =
          h • internalTheorem44CharacterEquiv
            S C theorem44Equiv theta)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (MonoidHom.range
      (productAmbientCenterProjectiveComparisonHom
        S C hgenerate theorem44Equiv
        characterEquiv_smul theta)).Normal := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let centerRange :=
    MonoidHom.range
      (productAmbientCenterProjectiveComparisonHom
        S C hgenerate theorem44Equiv
        characterEquiv_smul theta)
  have hrangeCenter :
      centerRange ≤
        Subgroup.center
          (projectiveComparisonCentralizer
            (ofInertia (product S C) theta.1)
            (MatchedInertiaRestriction.embedding
              (product S C)
              (ambientNormalizer S)
              (internalProductNormalizer S C)
              (internalTheorem44CharacterEquiv
                S C theorem44Equiv)
              characterEquiv_smul theta)) :=
    productAmbientCenterProjectiveComparisonHom_range_le_center
      S C hgenerate theorem44Equiv
      characterEquiv_smul theta
  exact
    { conj_mem := by
        intro n hn a
        have hcomm :=
          (Subgroup.mem_center_iff.mp
            (hrangeCenter hn)) a
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
        exact hn }

/-- The Okuyama--Wajima normalized-value identity, expressed on the
matched normal-central element of the two ambient inertia triples. -/
theorem productAmbientCenterComparisonElement_normalizedValues
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (characterEquiv_smul :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      ∀ (h : ambientNormalizer S)
        (theta :
          PPrimeIrreducibleCharacter
            (product S C) q),
        internalTheorem44CharacterEquiv
            S C
            (complementCharacterEquivOfGlauberman
              S C hcentral g) (h • theta) =
          h •
            internalTheorem44CharacterEquiv
              S C
              (complementCharacterEquivOfGlauberman
                S C hcentral g) theta)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (z : Subgroup.center (product S C)) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    let theorem44Equiv :=
      complementCharacterEquivOfGlauberman
        S C hcentral g
    let phi :=
      internalTheorem44CharacterEquiv
        S C theorem44Equiv theta
    let groupData :=
      productAmbientInertiaRestrictionGroupData
        S C hgenerate theorem44Equiv
        characterEquiv_smul theta
    let b :=
      productAmbientCenterComparisonElement
        S C hgenerate theorem44Equiv
        characterEquiv_smul theta z
    (ofInertia
        (product S C) theta.1).character.values
          (groupData.comparisonLeftNormalElement b) *
        ((ofInertia
          (internalProductNormalizer S C)
          phi.1).character.degree : ℂ) =
      (ofInertia
        (internalProductNormalizer S C)
        phi.1).character.values
          (groupData.comparisonRightNormalElement b) *
        ((ofInertia
          (product S C) theta.1).character.degree : ℂ) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  change
    theta.1.values z.1 *
        ((internalTheorem44CharacterEquiv
          S C
          (complementCharacterEquivOfGlauberman
            S C hcentral g) theta).1.degree : ℂ) =
      (internalTheorem44CharacterEquiv
        S C
        (complementCharacterEquivOfGlauberman
          S C hcentral g) theta).1.values
          (productAmbientCenterInternalElement S C z) *
        (theta.1.degree : ℂ)
  exact
    complementCharacterEquivOfGlauberman_internal_central_cross
      S C hcentral g theta z

/-- After quotient-factor matching, the scalar mismatch is trivial on every
matched normal-central element coming from `Z(CP)`. -/
theorem postFactorMatchingScalarMismatch_productAmbientCenter_eq_one
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (characterEquiv_smul :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      ∀ (h : ambientNormalizer S)
        (theta :
          PPrimeIrreducibleCharacter
            (product S C) q),
        internalTheorem44CharacterEquiv
            S C
            (complementCharacterEquivOfGlauberman
              S C hcentral g) (h • theta) =
          h •
            internalTheorem44CharacterEquiv
              S C
              (complementCharacterEquivOfGlauberman
                S C hcentral g) theta)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ∀ {V W : Type}
      [AddCommGroup V] [Module ℂ V]
      [Module.Finite ℂ V] [Nontrivial V]
      [AddCommGroup W] [Module ℂ W]
      [Module.Finite ℂ W] [Nontrivial W]
      {P :
        ProjectiveRepresentation ℂ
          (IrreducibleCharacter.inertia
            (product S C) theta.1) V}
      {Q :
        ProjectiveRepresentation ℂ
          (IrreducibleCharacter.inertia
            (internalProductNormalizer S C)
            (internalTheorem44CharacterEquiv
              S C
              (complementCharacterEquivOfGlauberman
                S C hcentral g) theta).1) W}
      (R :
        AssociatedProjectiveRepresentation
          (ofInertia (product S C) theta.1) V P)
      (Rright :
        AssociatedProjectiveRepresentation
          (ofInertia
            (internalProductNormalizer S C)
            (internalTheorem44CharacterEquiv
              S C
              (complementCharacterEquivOfGlauberman
                S C hcentral g) theta).1) W Q)
      (hcoh :
        R.QuotientFactorCohomologyAgreement
          Rright
          (productAmbientInertiaRestrictionGroupData
            S C hgenerate
            (complementCharacterEquivOfGlauberman
              S C hcentral g)
            characterEquiv_smul theta))
      (z : Subgroup.center (product S C)),
    let theorem44Equiv :=
      complementCharacterEquivOfGlauberman
        S C hcentral g
    let groupData :=
      productAmbientInertiaRestrictionGroupData
        S C hgenerate theorem44Equiv
        characterEquiv_smul theta
    let b :=
      productAmbientCenterComparisonElement
        S C hgenerate theorem44Equiv
        characterEquiv_smul theta z
    R.comparisonCentralScalarMismatch
        (R.factorMatchedRightAssociated
          Rright groupData hcoh)
        groupData.projectiveComparisonCentralizer_le_rightCentralizer
        (R.factorMatchedRightAssociated_factor_agreement
          Rright groupData hcoh)
        b.1 =
      1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  intro V W
  intro _ _ _ _ _ _ _ _
  intro P Q R Rright hcoh z
  let theorem44Equiv :=
    complementCharacterEquivOfGlauberman
      S C hcentral g
  let groupData :=
    productAmbientInertiaRestrictionGroupData
      S C hgenerate theorem44Equiv
      characterEquiv_smul theta
  let b :=
    productAmbientCenterComparisonElement
      S C hgenerate theorem44Equiv
      characterEquiv_smul theta z
  apply
    R.comparisonCentralScalarMismatch_apply_eq_one_of_normalizedNormalCentralValue
      (R.factorMatchedRightAssociated
        Rright groupData hcoh)
      groupData
      (R.factorMatchedRightAssociated_factor_agreement
        Rright groupData hcoh)
      b
  exact
    productAmbientCenterComparisonElement_normalizedValues
      S C hcentral hgenerate g
      characterEquiv_smul theta z

/-- The sharp residual scalar obstruction supplied by the actual
Okuyama--Wajima center identity.  Its domain is the comparison centralizer
modulo precisely the range of `Z(CP)`, rather than modulo the whole matched
normal-central subgroup. -/
def postFactorMatchingScalarMismatchProductAmbientCenterQuotient
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (characterEquiv_smul :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      ∀ (h : ambientNormalizer S)
        (theta :
          PPrimeIrreducibleCharacter
            (product S C) q),
        internalTheorem44CharacterEquiv
            S C
            (complementCharacterEquivOfGlauberman
              S C hcentral g) (h • theta) =
          h •
            internalTheorem44CharacterEquiv
              S C
              (complementCharacterEquivOfGlauberman
                S C hcentral g) theta)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ∀ {V W : Type}
      [AddCommGroup V] [Module ℂ V]
      [Module.Finite ℂ V] [Nontrivial V]
      [AddCommGroup W] [Module ℂ W]
      [Module.Finite ℂ W] [Nontrivial W]
      {P :
        ProjectiveRepresentation ℂ
          (IrreducibleCharacter.inertia
            (product S C) theta.1) V}
      {Q :
        ProjectiveRepresentation ℂ
          (IrreducibleCharacter.inertia
            (internalProductNormalizer S C)
            (internalTheorem44CharacterEquiv
              S C
              (complementCharacterEquivOfGlauberman
                S C hcentral g) theta).1) W}
      (R :
        AssociatedProjectiveRepresentation
          (ofInertia (product S C) theta.1) V P)
      (Rright :
        AssociatedProjectiveRepresentation
          (ofInertia
            (internalProductNormalizer S C)
            (internalTheorem44CharacterEquiv
              S C
              (complementCharacterEquivOfGlauberman
                S C hcentral g) theta).1) W Q)
      (hcoh :
        R.QuotientFactorCohomologyAgreement
          Rright
          (productAmbientInertiaRestrictionGroupData
            S C hgenerate
            (complementCharacterEquivOfGlauberman
              S C hcentral g)
            characterEquiv_smul theta)),
    let theorem44Equiv :=
      complementCharacterEquivOfGlauberman
        S C hcentral g
    let centerRange :=
      MonoidHom.range
        (productAmbientCenterProjectiveComparisonHom
          S C hgenerate theorem44Equiv
          characterEquiv_smul theta)
    letI : centerRange.Normal :=
      productAmbientCenterProjectiveComparisonHom_range_normal
        S C hgenerate theorem44Equiv
        characterEquiv_smul theta
    (projectiveComparisonCentralizer
          (ofInertia (product S C) theta.1)
          (MatchedInertiaRestriction.embedding
            (product S C)
            (ambientNormalizer S)
            (internalProductNormalizer S C)
            (internalTheorem44CharacterEquiv
              S C theorem44Equiv)
            characterEquiv_smul theta) ⧸
        centerRange) →*
      ℂˣ := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  intro V W
  intro _ _ _ _ _ _ _ _
  intro P Q R Rright hcoh
  let theorem44Equiv :=
    complementCharacterEquivOfGlauberman
      S C hcentral g
  let groupData :=
    productAmbientInertiaRestrictionGroupData
      S C hgenerate theorem44Equiv
      characterEquiv_smul theta
  let centerRange :=
    MonoidHom.range
      (productAmbientCenterProjectiveComparisonHom
        S C hgenerate theorem44Equiv
        characterEquiv_smul theta)
  letI : centerRange.Normal :=
    productAmbientCenterProjectiveComparisonHom_range_normal
      S C hgenerate theorem44Equiv
      characterEquiv_smul theta
  exact
    QuotientGroup.lift
      centerRange
      (R.comparisonCentralScalarMismatch
        (R.factorMatchedRightAssociated
          Rright groupData hcoh)
        groupData.projectiveComparisonCentralizer_le_rightCentralizer
        (R.factorMatchedRightAssociated_factor_agreement
          Rright groupData hcoh))
      (by
        intro c hc
        obtain ⟨z, rfl⟩ := hc
        apply MonoidHom.mem_ker.mpr
        exact
          postFactorMatchingScalarMismatch_productAmbientCenter_eq_one
            S C hcentral hgenerate g
            characterEquiv_smul theta
            R Rright hcoh z)

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
