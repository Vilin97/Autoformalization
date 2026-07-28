/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalFullInertiaTransport
import McKayConjecture.CharacterTriple.IntertwinerRestrictionScalarComparison

/-!
# Hom-space transport for the full Glauberman inertia action

The source and target Schur scalars combine as their quotient on the
restriction-multiplicity Hom-space.  This file records the calculation on
plain linear maps before restricting it to the canonical selected summand.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CharacterTriple.AssociatedExistence
open CliffordEquivalence
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

noncomputable local instance productCanonicalFullInertiaHomTransportFintype :
    Fintype X :=
  Fintype.ofFinite X

/-- The canonical source-kernel realization space. -/
abbrev ProductAmbientGlaubermanSourceKernelSpace
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :=
  (productAmbientGlaubermanSourceKernelCharacter
    S C hcentral theta).1.1.realization

/-- The final left normal-character realization space. -/
abbrev ProductAmbientGlaubermanLeftNormalCharacterSpace
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  (productAmbientGlaubermanLeftInertiaTriple
    S C hgenerate theta).character.realization

/-- Comparison between the source intertwiner chosen before restricting to
the matched inertia group and the independently chosen restricted
intertwiner. -/
theorem exists_productAmbientGlaubermanSourceIntertwinerRestrictionScalar
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta) :
    ∃ c : ℂˣ,
      ∀ v :
        ProductAmbientGlaubermanSourceKernelSpace
          S C hcentral theta,
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
              S C hcentral hgenerate g theta b) v =
          (c : ℂ) •
            (productAmbientGlaubermanSourceKernelInertiaProjective
              S C hcentral hgenerate g theta).operator b v := by
  simpa only [
    productAmbientGlaubermanSourceKernelInertiaAction,
    productAmbientGlaubermanSourceKernelInertiaProjective_operator] using
    exists_scalar_between_intertwiner_and_restriction
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
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanSourceKernelCharacter_isInvariant_inertia
        S C hcentral hgenerate g theta)
      b

/-- Source scalar contributed only by restricting the acting group. -/
def productAmbientGlaubermanSourceIntertwinerRestrictionScalar
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta) :
    ℂˣ :=
  Classical.choose
    (exists_productAmbientGlaubermanSourceIntertwinerRestrictionScalar
      S C hcentral hgenerate g theta b)

/-- Defining equation for the source restriction scalar. -/
theorem productAmbientGlaubermanSourceIntertwinerRestrictionScalar_apply
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
    (v :
      ProductAmbientGlaubermanSourceKernelSpace
        S C hcentral theta) :
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
          S C hcentral hgenerate g theta b) v =
      (productAmbientGlaubermanSourceIntertwinerRestrictionScalar
        S C hcentral hgenerate g theta b : ℂ) •
        (productAmbientGlaubermanSourceKernelInertiaProjective
          S C hcentral hgenerate g theta).operator b v :=
  Classical.choose_spec
    (exists_productAmbientGlaubermanSourceIntertwinerRestrictionScalar
      S C hcentral hgenerate g theta b) v

/-- Target analogue of the scalar introduced by restricting the acting
group before choosing canonical intertwiners. -/
theorem exists_productAmbientGlaubermanTargetIntertwinerRestrictionScalar
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta) :
    ∃ c : ℂˣ,
      ∀ v :
        ProductAmbientGlaubermanFixedPointKernelSpace
          S C hcentral g theta,
        intertwiner
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
              S C hcentral hgenerate g theta b) v =
          (c : ℂ) •
            (productAmbientGlaubermanFixedPointKernelInertiaProjective
              S C hcentral hgenerate g theta).operator b v := by
  simpa only [
    productAmbientGlaubermanFixedPointKernelInertiaAction,
    productAmbientGlaubermanFixedPointKernelInertiaProjective_operator] using
    exists_scalar_between_intertwiner_and_restriction
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
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanFixedPointCharacter_isInvariant_inertia
        S C hcentral hgenerate g theta)
      b

/-- Target scalar contributed only by restriction of the acting group. -/
def productAmbientGlaubermanTargetIntertwinerRestrictionScalar
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta) :
    ℂˣ :=
  Classical.choose
    (exists_productAmbientGlaubermanTargetIntertwinerRestrictionScalar
      S C hcentral hgenerate g theta b)

/-- Defining equation for the target restriction scalar. -/
theorem productAmbientGlaubermanTargetIntertwinerRestrictionScalar_apply
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
    (v :
      ProductAmbientGlaubermanFixedPointKernelSpace
        S C hcentral g theta) :
    intertwiner
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
          S C hcentral hgenerate g theta b) v =
      (productAmbientGlaubermanTargetIntertwinerRestrictionScalar
        S C hcentral hgenerate g theta b : ℂ) •
        (productAmbientGlaubermanFixedPointKernelInertiaProjective
          S C hcentral hgenerate g theta).operator b v :=
  Classical.choose_spec
    (exists_productAmbientGlaubermanTargetIntertwinerRestrictionScalar
      S C hcentral hgenerate g theta b) v

/-- The complete source comparison scalar for the operator actually used
by the restricted kernel multiplicity action. -/
def productAmbientGlaubermanActualSourceFullInertiaScalar
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta) :
    ℂˣ :=
  productAmbientGlaubermanSourceIntertwinerRestrictionScalar
      S C hcentral hgenerate g theta b *
    productAmbientGlaubermanSourceFullInertiaScalar
      S C hcentral hgenerate g theta b

/-- The complete target comparison scalar for the operator actually used
by the restricted kernel multiplicity action. -/
def productAmbientGlaubermanActualTargetFullInertiaScalar
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta) :
    ℂˣ :=
  productAmbientGlaubermanTargetIntertwinerRestrictionScalar
      S C hcentral hgenerate g theta b *
    productAmbientGlaubermanTargetFullInertiaScalar
      S C hcentral hgenerate g theta b

/-- The scalar induced on a Hom-space is the source comparison scalar
divided by the target comparison scalar. -/
def productAmbientGlaubermanFullInertiaScalarRatio
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta) :
    ℂˣ :=
  productAmbientGlaubermanActualSourceFullInertiaScalar
      S C hcentral hgenerate g theta b *
    (productAmbientGlaubermanActualTargetFullInertiaScalar
      S C hcentral hgenerate g theta b)⁻¹

/-- Complete source comparison for the operator inherited from the original
kernel-stabilizer projective representation. -/
theorem productAmbientGlaubermanActualSourceFullInertiaScalar_apply
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
    (v :
      ProductAmbientGlaubermanSourceKernelSpace
        S C hcentral theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
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
            S C hcentral hgenerate g theta b) v) =
      (productAmbientGlaubermanActualSourceFullInertiaScalar
        S C hcentral hgenerate g theta b : ℂ) •
        (AssociatedGeneralExistence.projectiveRepresentation
          (productAmbientGlaubermanLeftInertiaTriple
            S C hgenerate theta)).operator
          (productAmbientGlaubermanInertiaEmbedding
            S C hcentral hgenerate g theta b)
          (productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
            S C hcentral hgenerate g theta v) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    operator_comparison_of_source_scalar
      (productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
        S C hcentral hgenerate g theta).toLinearEquiv
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
          S C hcentral hgenerate g theta b))
      ((productAmbientGlaubermanSourceKernelInertiaProjective
        S C hcentral hgenerate g theta).operator b)
      ((AssociatedGeneralExistence.projectiveRepresentation
        (productAmbientGlaubermanLeftInertiaTriple
          S C hgenerate theta)).operator
        (productAmbientGlaubermanInertiaEmbedding
          S C hcentral hgenerate g theta b))
      (productAmbientGlaubermanSourceIntertwinerRestrictionScalar
        S C hcentral hgenerate g theta b)
      (productAmbientGlaubermanSourceFullInertiaScalar
        S C hcentral hgenerate g theta b)
      (fun w ↦
        productAmbientGlaubermanSourceIntertwinerRestrictionScalar_apply
          S C hcentral hgenerate g theta b w)
      (fun w ↦ by
        rw [productAmbientGlaubermanSourceKernelInertiaProjective_operator]
        exact
          productAmbientGlaubermanSourceFullInertiaScalar_apply
            S C hcentral hgenerate g theta b w)
      v

/-- Complete target comparison for the operator inherited from the original
kernel-stabilizer projective representation. -/
theorem productAmbientGlaubermanActualTargetFullInertiaScalar_apply
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
    (v :
      ProductAmbientGlaubermanFixedPointKernelSpace
        S C hcentral g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
        S C hcentral hgenerate g theta
        (intertwiner
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
            S C hcentral hgenerate g theta b) v) =
      (productAmbientGlaubermanActualTargetFullInertiaScalar
        S C hcentral hgenerate g theta b : ℂ) •
        (AssociatedGeneralExistence.projectiveRepresentation
          (productAmbientGlaubermanRightInertiaTriple
            S C hcentral hgenerate g theta)).operator b
          (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
            S C hcentral hgenerate g theta v) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    operator_comparison_of_source_scalar
      (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
        S C hcentral hgenerate g theta).toLinearEquiv
      (intertwiner
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
          S C hcentral hgenerate g theta b))
      ((productAmbientGlaubermanFixedPointKernelInertiaProjective
        S C hcentral hgenerate g theta).operator b)
      ((AssociatedGeneralExistence.projectiveRepresentation
        (productAmbientGlaubermanRightInertiaTriple
          S C hcentral hgenerate g theta)).operator b)
      (productAmbientGlaubermanTargetIntertwinerRestrictionScalar
        S C hcentral hgenerate g theta b)
      (productAmbientGlaubermanTargetFullInertiaScalar
        S C hcentral hgenerate g theta b)
      (fun w ↦
        productAmbientGlaubermanTargetIntertwinerRestrictionScalar_apply
          S C hcentral hgenerate g theta b w)
      (fun w ↦
        productAmbientGlaubermanTargetProductFullInertiaScalar_apply
          S C hcentral hgenerate g theta b w)
      v

/-- The canonical inertia conjugation action on an unbundled kernel Hom. -/
def productAmbientGlaubermanKernelHomActionLinearMap
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
      ProductAmbientGlaubermanFixedPointKernelSpace
          S C hcentral g theta →ₗ[ℂ]
        ProductAmbientGlaubermanSourceKernelSpace
          S C hcentral theta) :
    ProductAmbientGlaubermanFixedPointKernelSpace
        S C hcentral g theta →ₗ[ℂ]
      ProductAmbientGlaubermanSourceKernelSpace
        S C hcentral theta :=
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
        S C hcentral hgenerate g theta b)).toLinearMap.comp
    (f.comp
      (intertwiner
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
          S C hcentral hgenerate g theta b)).symm.toLinearMap)

/-- Conjugate a plain kernel Hom by the exact source and target normal
character equivalences. -/
def productAmbientGlaubermanNormalHomTransportLinearMap
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (f :
      ProductAmbientGlaubermanFixedPointKernelSpace
          S C hcentral g theta →ₗ[ℂ]
        ProductAmbientGlaubermanSourceKernelSpace
          S C hcentral theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ProductAmbientGlaubermanRightNormalCharacterSpace
          S C hcentral hgenerate g theta →ₗ[ℂ]
      ProductAmbientGlaubermanLeftNormalCharacterSpace
          S C hgenerate theta :=
  (productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
      S C hcentral hgenerate g theta).toLinearMap.comp
    (f.comp
      (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
        S C hcentral hgenerate g theta).symm.toLinearMap)

/-- The canonical associated-projective conjugation action on an unbundled
normal-character Hom. -/
def productAmbientGlaubermanAssociatedMismatchHomActionLinearMap
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
      ProductAmbientGlaubermanRightNormalCharacterSpace
          S C hcentral hgenerate g theta →ₗ[ℂ]
        ProductAmbientGlaubermanLeftNormalCharacterSpace
          S C hgenerate theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ProductAmbientGlaubermanRightNormalCharacterSpace
          S C hcentral hgenerate g theta →ₗ[ℂ]
      ProductAmbientGlaubermanLeftNormalCharacterSpace
          S C hgenerate theta :=
  ((AssociatedGeneralExistence.projectiveRepresentation
      (productAmbientGlaubermanLeftInertiaTriple
        S C hgenerate theta)).operator
      (productAmbientGlaubermanInertiaEmbedding
        S C hcentral hgenerate g theta b)).toLinearMap.comp
    (f.comp
      ((AssociatedGeneralExistence.projectiveRepresentation
        (productAmbientGlaubermanRightInertiaTriple
          S C hcentral hgenerate g theta)).operator b).symm.toLinearMap)

/-- Transporting full-inertia conjugation from the kernel realizations to
the final normal-character realizations introduces exactly the scalar
ratio `source / target`. -/
theorem productAmbientGlaubermanNormalHomTransport_inertia_apply
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
      ProductAmbientGlaubermanFixedPointKernelSpace
          S C hcentral g theta →ₗ[ℂ]
        ProductAmbientGlaubermanSourceKernelSpace
          S C hcentral theta)
    (w :
      ProductAmbientGlaubermanRightNormalCharacterSpace
        S C hcentral hgenerate g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    productAmbientGlaubermanNormalHomTransportLinearMap
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanKernelHomActionLinearMap
          S C hcentral hgenerate g theta b f) w =
      (productAmbientGlaubermanFullInertiaScalarRatio
        S C hcentral hgenerate g theta b : ℂ) •
        productAmbientGlaubermanAssociatedMismatchHomActionLinearMap
          S C hcentral hgenerate g theta b
          (productAmbientGlaubermanNormalHomTransportLinearMap
            S C hcentral hgenerate g theta f) w := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let ESource :=
    (productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
      S C hcentral hgenerate g theta).toLinearEquiv
  let ETarget :=
    (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
      S C hcentral hgenerate g theta).toLinearEquiv
  let TSource :=
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
  let TTarget :=
    intertwiner
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
        S C hcentral hgenerate g theta b)
  let PSource :=
    (AssociatedGeneralExistence.projectiveRepresentation
      (productAmbientGlaubermanLeftInertiaTriple
        S C hgenerate theta)).operator
      (productAmbientGlaubermanInertiaEmbedding
        S C hcentral hgenerate g theta b)
  let PTarget :=
    (AssociatedGeneralExistence.projectiveRepresentation
      (productAmbientGlaubermanRightInertiaTriple
        S C hcentral hgenerate g theta)).operator b
  have hSource (v :
      ProductAmbientGlaubermanSourceKernelSpace
        S C hcentral theta) :
      ESource (TSource v) =
        (productAmbientGlaubermanActualSourceFullInertiaScalar
          S C hcentral hgenerate g theta b : ℂ) •
          PSource (ESource v) := by
    exact
      productAmbientGlaubermanActualSourceFullInertiaScalar_apply
        S C hcentral hgenerate g theta b v
  have hTarget (v :
      ProductAmbientGlaubermanFixedPointKernelSpace
        S C hcentral g theta) :
      ETarget (TTarget v) =
        (productAmbientGlaubermanActualTargetFullInertiaScalar
          S C hcentral hgenerate g theta b : ℂ) •
          PTarget (ETarget v) := by
    exact
      productAmbientGlaubermanActualTargetFullInertiaScalar_apply
        S C hcentral hgenerate g theta b v
  change
    ESource
        (TSource
          (f (TTarget.symm (ETarget.symm w)))) =
      ((productAmbientGlaubermanActualSourceFullInertiaScalar
          S C hcentral hgenerate g theta b *
        (productAmbientGlaubermanActualTargetFullInertiaScalar
          S C hcentral hgenerate g theta b)⁻¹ : ℂˣ) : ℂ) •
        PSource
          (ESource
            (f (ETarget.symm (PTarget.symm w))))
  exact
    scalar_conjugation_transport
      ESource ETarget TSource TTarget PSource PTarget
      (productAmbientGlaubermanActualSourceFullInertiaScalar
        S C hcentral hgenerate g theta b)
      (productAmbientGlaubermanActualTargetFullInertiaScalar
        S C hcentral hgenerate g theta b)
      hSource hTarget f w

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
