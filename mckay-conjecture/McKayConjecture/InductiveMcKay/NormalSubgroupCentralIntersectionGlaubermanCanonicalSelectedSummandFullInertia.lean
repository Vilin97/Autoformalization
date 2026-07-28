/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalFullInertiaHomTransport

/-!
# Full-inertia stability of the canonical Glauberman summand

The scalar-ratio Hom calculation identifies the full kernel action with the
final mismatch action after the direct selected-summand equivalence.  It
follows that the canonically selected Sylow summand is stable under the
whole matched inertia group.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CategoryTheory
open CharacterTriple
open CharacterTriple.AssociatedExistence
open CliffordEquivalence
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

noncomputable local instance productCanonicalSelectedFullInertiaFintype :
    Fintype X :=
  Fintype.ofFinite X

/-- The full projective mismatch action before quotient descent. -/
abbrev ProductAmbientGlaubermanInertiaMismatchProjective
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  ProjectiveMultiplicityMismatch.projective
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta)
    (productAmbientGlaubermanRightAssociated
      S C hcentral hgenerate g theta)
    (productAmbientGlaubermanInertiaRestrictionGroupData
      S C hcentral hgenerate g theta)

/-- Pointwise formula for the restricted kernel multiplicity action in
terms of the named source and target canonical intertwiner operators. -/
theorem productAmbientGlaubermanRestrictedKernelMultiplicityProjective_fullInertia_apply
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta)
    (f :
      ProductAmbientGlaubermanKernelMultiplicitySpace
        S C hcentral g theta)
    (w :
      ProductAmbientGlaubermanFixedPointKernelSpace
        S C hcentral g theta) :
    (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
        S C hcentral hgenerate g theta).operator b f w =
      intertwiner
        (productGlaubermanKernelStabilizerAction
          S C hcentral
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta))
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1.1
        (productGlaubermanKernelCharacter_isInvariant
          S C hcentral
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta))
        (productAmbientGlaubermanRightInertiaToKernelStabilizer
          S C hcentral hgenerate g theta b)
        (f
          ((intertwiner
            (productGlaubermanFixedPointsStabilizerAction
              S C hcentral
              (productAmbientGlaubermanSourceKernelCharacter
                S C hcentral theta))
            (g.characterEquiv
              (productAmbientGlaubermanSourceKernelCharacter
                S C hcentral theta)).1
            (productGlaubermanFixedPointCharacter_isInvariant
              S C hcentral g
              (productAmbientGlaubermanSourceKernelCharacter
                S C hcentral theta))
            (productAmbientGlaubermanRightInertiaToKernelStabilizer
              S C hcentral hgenerate g theta b)).symm w)) := by
  rfl

/-- On a selected vector, the raw normal-Hom transport is exactly the
previously constructed direct equivalence to the mismatch space. -/
theorem productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect_eq_transport
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (z :
      ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta))
    (w :
      ProductAmbientGlaubermanRightNormalCharacterSpace
        S C hcentral hgenerate g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
        S C hcentral hgenerate g theta z w =
      productAmbientGlaubermanNormalHomTransportLinearMap
        S C hcentral hgenerate g theta z.1.toLinearMap w := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  rfl

/-- Linear-map form of the direct-equivalence transport formula. -/
theorem productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect_toLinearMap
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (z :
      ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta)) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
        S C hcentral hgenerate g theta z).toLinearMap =
      productAmbientGlaubermanNormalHomTransportLinearMap
        S C hcentral hgenerate g theta z.1.toLinearMap := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  apply LinearMap.ext
  intro w
  exact
    productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect_eq_transport
      S C hcentral hgenerate g theta z w

/-- The raw associated mismatch Hom action is the pointwise operator of the
bundled projective mismatch representation. -/
theorem productAmbientGlaubermanAssociatedMismatchHomActionLinearMap_apply
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta)
    (f :
      ProductAmbientGlaubermanMultiplicityMismatchSpace
        S C hcentral hgenerate g theta)
    (w :
      ProductAmbientGlaubermanRightNormalCharacterSpace
        S C hcentral hgenerate g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    productAmbientGlaubermanAssociatedMismatchHomActionLinearMap
        S C hcentral hgenerate g theta b f.toLinearMap w =
      (ProductAmbientGlaubermanInertiaMismatchProjective
        S C hcentral hgenerate g theta).operator b f w := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  rfl

/-- Evaluating transported kernel conjugation at the transported point is
the source equivalence applied to the actual restricted kernel action. -/
theorem productAmbientGlaubermanNormalHomTransport_kernelAction_apply
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta)
    (f :
      ProductAmbientGlaubermanKernelMultiplicitySpace
        S C hcentral g theta)
    (w :
      ProductAmbientGlaubermanFixedPointKernelSpace
        S C hcentral g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    productAmbientGlaubermanNormalHomTransportLinearMap
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanKernelHomActionLinearMap
          S C hcentral hgenerate g theta b f.toLinearMap)
        (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
          S C hcentral hgenerate g theta w) =
      productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
        S C hcentral hgenerate g theta
        ((productAmbientGlaubermanRestrictedKernelMultiplicityProjective
          S C hcentral hgenerate g theta).operator b f w) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  rw [
    productAmbientGlaubermanRestrictedKernelMultiplicityProjective_fullInertia_apply]
  change
    productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
        S C hcentral hgenerate g theta
        (intertwiner
          (productGlaubermanKernelStabilizerAction
            S C hcentral
            (productAmbientGlaubermanSourceKernelCharacter
              S C hcentral theta))
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta).1.1
          (productGlaubermanKernelCharacter_isInvariant
            S C hcentral
            (productAmbientGlaubermanSourceKernelCharacter
              S C hcentral theta))
          (productAmbientGlaubermanRightInertiaToKernelStabilizer
            S C hcentral hgenerate g theta b)
          (f
            ((intertwiner
              (productGlaubermanFixedPointsStabilizerAction
                S C hcentral
                (productAmbientGlaubermanSourceKernelCharacter
                  S C hcentral theta))
              (g.characterEquiv
                (productAmbientGlaubermanSourceKernelCharacter
                  S C hcentral theta)).1
              (productGlaubermanFixedPointCharacter_isInvariant
                S C hcentral g
                (productAmbientGlaubermanSourceKernelCharacter
                  S C hcentral theta))
              (productAmbientGlaubermanRightInertiaToKernelStabilizer
                S C hcentral hgenerate g theta b)).symm
              ((productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
                S C hcentral hgenerate g theta).symm
                (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
                  S C hcentral hgenerate g theta w))))) =
      _
  rw [
    (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
      S C hcentral hgenerate g theta).symm_apply_apply]

/-- Pointwise equivariance of the direct selected-summand map, before the
stability conclusion is bundled. -/
theorem productAmbientGlaubermanCanonicalSelectedSummand_fullInertia_pointwise
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta)
    (z :
      ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta))
    (w :
      ProductAmbientGlaubermanFixedPointKernelSpace
        S C hcentral g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
      S C hcentral hgenerate g theta)
        ((productAmbientGlaubermanRestrictedKernelMultiplicityProjective
          S C hcentral hgenerate g theta).operator b z.1 w) =
      (productAmbientGlaubermanFullInertiaScalarRatio
        S C hcentral hgenerate g theta b : ℂ) •
        (ProductAmbientGlaubermanInertiaMismatchProjective
          S C hcentral hgenerate g theta).operator b
          (productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
            S C hcentral hgenerate g theta z)
          (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
            S C hcentral hgenerate g theta w) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  have h :=
    productAmbientGlaubermanNormalHomTransport_inertia_apply
      S C hcentral hgenerate g theta b z.1.toLinearMap
      (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
        S C hcentral hgenerate g theta w)
  rw [productAmbientGlaubermanNormalHomTransport_kernelAction_apply] at h
  rw [←
    productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect_toLinearMap]
    at h
  rw [
    productAmbientGlaubermanAssociatedMismatchHomActionLinearMap_apply] at h
  exact h

/-- Evaluating the direct equivalence at a point transported by the target
equivalence cancels its inverse in the defining Hom conjugation. -/
theorem productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect_transportPoint
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (z :
      ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta))
    (w :
      ProductAmbientGlaubermanFixedPointKernelSpace
        S C hcentral g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
        S C hcentral hgenerate g theta z
        (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
          S C hcentral hgenerate g theta w) =
      productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
        S C hcentral hgenerate g theta (z.1 w) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  rw [
    productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect_eq_transport]
  change
    productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
        S C hcentral hgenerate g theta
        (z.1
          ((productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
            S C hcentral hgenerate g theta).symm
            (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
              S C hcentral hgenerate g theta w))) =
      _
  rw [
    (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
      S C hcentral hgenerate g theta).symm_apply_apply]

/-- The canonically selected Sylow-scalar summand is stable under every
operator of the matched right inertia group. -/
theorem productAmbientGlaubermanCanonicalSelectedSummand_isStable
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
      S C hcentral hgenerate g theta).IsStable
        (ProductAmbientGlaubermanKernelSylowScalarSubspace
          S C hcentral hgenerate g theta
          (productAmbientGlaubermanCanonicalSelectedSylowScalar
            S C hcentral hgenerate g theta)) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  intro b f hf
  let z :
      ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta) :=
    ⟨f, hf⟩
  let E :=
    productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
      S C hcentral hgenerate g theta
  let Q :=
    ProductAmbientGlaubermanInertiaMismatchProjective
      S C hcentral hgenerate g theta
  let r :=
    productAmbientGlaubermanFullInertiaScalarRatio
      S C hcentral hgenerate g theta b
  let yMismatch :
      ProductAmbientGlaubermanMultiplicityMismatchSpace
        S C hcentral hgenerate g theta :=
    (r : ℂ) • Q.operator b (E z)
  let y :
      ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta) :=
    E.symm yMismatch
  have hyE : E y = yMismatch :=
    E.apply_symm_apply yMismatch
  have hfy :
      (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
        S C hcentral hgenerate g theta).operator b f =
        y.1 := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    apply
      (productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
        S C hcentral hgenerate g theta).toLinearEquiv.injective
    have hpoint :=
      productAmbientGlaubermanCanonicalSelectedSummand_fullInertia_pointwise
        S C hcentral hgenerate g theta b z w
    have hyvalue :=
      congrArg
        (fun m :
          ProductAmbientGlaubermanMultiplicityMismatchSpace
            S C hcentral hgenerate g theta ↦
          m
            (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
              S C hcentral hgenerate g theta w))
        hyE
    have hyLeft :
        E y
            (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
              S C hcentral hgenerate g theta w) =
          productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
            S C hcentral hgenerate g theta (y.1 w) :=
      productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect_transportPoint
        S C hcentral hgenerate g theta y w
    have hyRight :
        yMismatch
            (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
              S C hcentral hgenerate g theta w) =
          (r : ℂ) •
            Q.operator b (E z)
              (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
                S C hcentral hgenerate g theta w) := by
      rfl
    have hyFinal :
        productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
            S C hcentral hgenerate g theta (y.1 w) =
          (r : ℂ) •
            Q.operator b (E z)
              (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
                S C hcentral hgenerate g theta w) :=
      hyLeft.symm.trans (hyvalue.trans hyRight)
    exact hpoint.trans hyFinal.symm
  rw [hfy]
  exact y.property

/-- The inherited projective action on the canonical selected summand. -/
def productAmbientGlaubermanCanonicalSelectedSummandInertiaProjective
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    ProjectiveRepresentation ℂ
      (ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta)
      (ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta)) :=
  (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
    S C hcentral hgenerate g theta).restrictStable
      (ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta))
      (productAmbientGlaubermanCanonicalSelectedSummand_isStable
        S C hcentral hgenerate g theta)

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
