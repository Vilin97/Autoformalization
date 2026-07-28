/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ScalarConjugationTransport
import McKayConjecture.CharacterTriple.RepresentationEquivScalarComparison
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalFullInertiaScalar
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalTargetFullInertiaScalar

/-!
# Full-inertia transport of the canonical Glauberman summand

This file uses the direct source normal-character realization from the
full-inertia scalar comparison.  It gives a pointwise transparent
identification of the selected kernel summand with the final mismatch
space, ready for the source/target scalar-ratio calculation.
-/

noncomputable section

open CategoryTheory

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

noncomputable local instance productCanonicalFullInertiaTransportFintype :
    Fintype X :=
  Fintype.ofFinite X

/-
/-- The exact target product isomorphism intertwines the fixed-point
kernel action with the final right normal-character action. -/
theorem productAmbientGlaubermanFixedPointKernelProductIso_intertwines
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (x : productPPrimeKernelFixedPoints S C hcentral)
    (z :
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1.realization) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (productAmbientGlaubermanFixedPointKernelProductFDRepIsoRightNormalRestriction
        S C hcentral hgenerate g theta).hom
        ((g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1.realization.ρ x z) =
      (productAmbientGlaubermanRightInertiaTriple
          S C hcentral hgenerate g theta).character.realization.ρ
        (productAmbientGlaubermanFixedPointKernelToRightNormalCopy
          S C hcentral hgenerate g theta x)
        ((productAmbientGlaubermanFixedPointKernelProductFDRepIsoRightNormalRestriction
          S C hcentral hgenerate g theta).hom z) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let E :=
    FDRep.representationEquivOfIso
      (productAmbientGlaubermanFixedPointKernelProductFDRepIsoRightNormalRestriction
        S C hcentral hgenerate g theta)
  let a :=
    (productAmbientGlaubermanInternalFixedPointEquiv
      S C hcentral).symm x
  have hE :=
    LinearMap.congr_fun
      (E.isIntertwining' (a, 1)) z
  have hcoordinate :
      productAmbientGlaubermanRightNormalCopyProductEquiv
          S C hcentral hgenerate g theta (a, 1) =
        productAmbientGlaubermanFixedPointKernelToRightNormalCopy
          S C hcentral hgenerate g theta x := by
    simp [a,
      productAmbientGlaubermanFixedPointKernelToRightNormalCopy,
      productAmbientGlaubermanRightNormalCopyFixedPointHom]
  change
    E
        ((g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1.realization.ρ x z) =
      (productAmbientGlaubermanRightInertiaTriple
          S C hcentral hgenerate g theta).character.realization.ρ
        (productAmbientGlaubermanFixedPointKernelToRightNormalCopy
          S C hcentral hgenerate g theta x)
        (E z)
  rw [← hcoordinate]
  rw [←
    (productAmbientGlaubermanInternalFixedPointEquiv
      S C hcentral).apply_symm_apply x]
  change
    E
        ((g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1.realization.ρ
          (productAmbientGlaubermanInternalFixedPointEquiv
            S C hcentral a) z) =
      (productAmbientGlaubermanRightInertiaTriple
          S C hcentral hgenerate g theta).character.realization.ρ
        (productAmbientGlaubermanRightNormalCopyProductEquiv
          S C hcentral hgenerate g theta (a, 1))
        (E z)
  change
    E
        ((ProductAmbientGlaubermanFixedPointKernelProductFDRep
          S C hcentral g theta).ρ (a, 1) z) =
      (productAmbientGlaubermanRightInertiaTriple
          S C hcentral hgenerate g theta).character.realization.ρ
        (productAmbientGlaubermanRightNormalCopyProductEquiv
          S C hcentral hgenerate g theta (a, 1))
        (E z) at hE
  exact
    (congrArg E
      (LinearMap.congr_fun
        (productAmbientGlaubermanFixedPointKernelProductFDRep_inl
          S C hcentral g theta a) z).symm).trans hE

/-- The exact target product equivalence and the canonical target
extension equivalence differ by one nonzero scalar. -/
theorem exists_productAmbientGlaubermanTargetProductEquivComparisonScalar
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ∃ c : ℂˣ,
      ∀ z :
        (g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1.realization,
        (productAmbientGlaubermanFixedPointKernelProductFDRepIsoRightNormalRestriction
            S C hcentral hgenerate g theta).hom z =
          (c : ℂ) •
            productAmbientGlaubermanFixedPointKernelExtensionEquivRightNormalCharacter
              S C hcentral hgenerate g theta z := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let chi :=
    (g.characterEquiv
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta)).1
  let eProduct :=
    FDRep.representationEquivOfIso
      (productAmbientGlaubermanFixedPointKernelProductFDRepIsoRightNormalRestriction
        S C hcentral hgenerate g theta)
  let eExtension :=
    productAmbientGlaubermanFixedPointKernelExtensionEquivRightNormalCharacter
      S C hcentral hgenerate g theta
  let comparison : chi.realization ≃ₗ[ℂ] chi.realization :=
    eProduct.toLinearEquiv.trans eExtension.toLinearEquiv.symm
  have hComparisonApply (y : chi.realization) :
      eExtension (comparison y) = eProduct y := by
    dsimp only [comparison]
    exact eExtension.toLinearEquiv.apply_symm_apply (eProduct y)
  have hComparison :
      ∃ c : ℂˣ, ∀ z : chi.realization,
        comparison z = (c : ℂ) • z := by
    apply
      exists_scalar_of_covariance
        chi
        (1 : MulAut (productPPrimeKernelFixedPoints S C hcentral))
        1 comparison
    · intro x
      rfl
    · intro x
      apply LinearEquiv.toLinearMap_injective
      apply LinearMap.ext
      intro z
      apply eExtension.toLinearEquiv.injective
      have hProduct :=
        productAmbientGlaubermanFixedPointKernelProductIso_intertwines
          S C hcentral hgenerate g theta x z
      have hExtension :=
        LinearMap.congr_fun
          (eExtension.isIntertwining' x)
          (comparison z)
      have hnormal :=
        congrArg
          (fun f :
            productPPrimeKernelFixedPoints S C hcentral →*
              ProductAmbientGlaubermanRightNormalCopy
                S C hcentral hgenerate g theta ↦ f x)
          (productAmbientGlaubermanFixedPointExtensionToInertia_eq
            S C hcentral hgenerate g theta)
      change
        eExtension
            ((g.characterEquiv
              (productAmbientGlaubermanSourceKernelCharacter
                S C hcentral theta)).1.realization.ρ
              x (comparison z)) =
          (productAmbientGlaubermanRightInertiaTriple
            S C hcentral hgenerate g theta).character.realization.ρ
            (extensionToInertiaNormalHom
              (internalProductNormalizer S C)
              (productAmbientGlaubermanFixedPointKernelToRightCharacter
                S C hcentral)
              (productAmbientGlaubermanRightKernelTransportCharacter
                S C hcentral g theta) x)
            (eExtension (comparison z)) at hExtension
      change
        eProduct
            ((g.characterEquiv
              (productAmbientGlaubermanSourceKernelCharacter
                S C hcentral theta)).1.realization.ρ x z) =
          (productAmbientGlaubermanRightInertiaTriple
            S C hcentral hgenerate g theta).character.realization.ρ
            (productAmbientGlaubermanFixedPointKernelToRightNormalCopy
              S C hcentral hgenerate g theta x)
            (eProduct z) at hProduct
      have hMiddle :
          (productAmbientGlaubermanRightInertiaTriple
            S C hcentral hgenerate g theta).character.realization.ρ
              (productAmbientGlaubermanFixedPointKernelToRightNormalCopy
                S C hcentral hgenerate g theta x)
              (eProduct z) =
            (productAmbientGlaubermanRightInertiaTriple
              S C hcentral hgenerate g theta).character.realization.ρ
              (extensionToInertiaNormalHom
                (internalProductNormalizer S C)
                (productAmbientGlaubermanFixedPointKernelToRightCharacter
                  S C hcentral)
                (productAmbientGlaubermanRightKernelTransportCharacter
                  S C hcentral g theta) x)
              (eExtension (comparison z)) := by
        rw [hnormal, hComparisonApply]
      change
        eExtension
            (comparison
              (chi.realization.ρ x z)) =
          eExtension
            (chi.realization.ρ x
              (comparison z))
      rw [hComparisonApply]
      dsimp only [chi]
      exact hProduct.trans (hMiddle.trans hExtension.symm)
  obtain ⟨c, hc⟩ := hComparison
  refine ⟨c, fun z ↦ ?_⟩
  have hz :=
    congrArg (fun y : chi.realization ↦ eExtension y) (hc z)
  rw [hComparisonApply, map_smul] at hz
  change eProduct z = (c : ℂ) • eExtension z
  exact hz

/-- The exact product-model target equivalence satisfies the same
full-inertia scalar comparison as the canonical extension equivalence. -/
theorem productAmbientGlaubermanTargetProductFullInertiaScalar_apply
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
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1.realization) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (productAmbientGlaubermanFixedPointKernelProductFDRepIsoRightNormalRestriction
        S C hcentral hgenerate g theta).hom
        (intertwiner
          (productAmbientGlaubermanFixedPointKernelInertiaAction
            S C hcentral hgenerate g theta)
          (g.characterEquiv
            (productAmbientGlaubermanSourceKernelCharacter
              S C hcentral theta)).1
          (productAmbientGlaubermanFixedPointCharacter_isInvariant_inertia
            S C hcentral hgenerate g theta)
          b z) =
      (productAmbientGlaubermanTargetFullInertiaScalar
        S C hcentral hgenerate g theta b : ℂ) •
        (AssociatedGeneralExistence.projectiveRepresentation
          (productAmbientGlaubermanRightInertiaTriple
            S C hcentral hgenerate g theta)).operator
          b
          ((productAmbientGlaubermanFixedPointKernelProductFDRepIsoRightNormalRestriction
            S C hcentral hgenerate g theta).hom z) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  obtain ⟨c, hc⟩ :=
    exists_productAmbientGlaubermanTargetProductEquivComparisonScalar
      S C hcentral hgenerate g theta
  rw [hc _]
  rw [productAmbientGlaubermanTargetFullInertiaScalar_apply]
  rw [hc z, map_smul]
  simp only [smul_smul]
  ring
-/

/-- The underlying linear equivalence of the exact target product model,
with its large representation terms hidden behind the stable space names. -/
def productAmbientGlaubermanFixedPointKernelProductLinearEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ProductAmbientGlaubermanFixedPointKernelSpace
        S C hcentral g theta ≃ₗ[ℂ]
      ProductAmbientGlaubermanRightNormalCharacterSpace
        S C hcentral hgenerate g theta :=
  (FDRep.representationEquivOfIso
    (productAmbientGlaubermanFixedPointKernelProductFDRepIsoRightNormalRestriction
      S C hcentral hgenerate g theta)).toLinearEquiv

/-- The product coordinates `(a,1)` and the fixed-point inclusion describe
the same element of the final right normal copy. -/
theorem productAmbientGlaubermanRightNormalCopyProductEquiv_inl
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (a :
      internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral)) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    productAmbientGlaubermanRightNormalCopyProductEquiv
        S C hcentral hgenerate g theta (a, 1) =
      productAmbientGlaubermanFixedPointKernelToRightNormalCopy
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanInternalFixedPointEquiv
          S C hcentral a) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  simp [productAmbientGlaubermanFixedPointKernelToRightNormalCopy,
    productAmbientGlaubermanRightNormalCopyFixedPointHom]

/-- Pointwise intertwining for the target product model, phrased using the
stable fixed-point and right-normal representation names. -/
theorem productAmbientGlaubermanFixedPointKernelProductLinearEquiv_intertwines
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (x : productPPrimeKernelFixedPoints S C hcentral)
    (z :
      ProductAmbientGlaubermanFixedPointKernelSpace
        S C hcentral g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    productAmbientGlaubermanFixedPointKernelProductLinearEquiv
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanFixedPointKernelRepresentation
          S C hcentral g theta x z) =
      productAmbientGlaubermanRightNormalFixedPointRepresentation
        S C hcentral hgenerate g theta x
        (productAmbientGlaubermanFixedPointKernelProductLinearEquiv
          S C hcentral hgenerate g theta z) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let E :=
    FDRep.representationEquivOfIso
      (productAmbientGlaubermanFixedPointKernelProductFDRepIsoRightNormalRestriction
        S C hcentral hgenerate g theta)
  let a :=
    (productAmbientGlaubermanInternalFixedPointEquiv
      S C hcentral).symm x
  have hE :
      E
          ((ProductAmbientGlaubermanFixedPointKernelProductFDRep
            S C hcentral g theta).ρ (a, 1) z) =
        (productAmbientGlaubermanRightInertiaTriple
          S C hcentral hgenerate g theta).character.realization.ρ
          (productAmbientGlaubermanRightNormalCopyProductEquiv
            S C hcentral hgenerate g theta (a, 1))
          (E z) :=
    LinearMap.congr_fun (E.isIntertwining' (a, 1)) z
  have hinl :
      (ProductAmbientGlaubermanFixedPointKernelProductFDRep
          S C hcentral g theta).ρ (a, 1) z =
        productAmbientGlaubermanFixedPointKernelRepresentation
          S C hcentral g theta x z := by
    change
      (ProductAmbientGlaubermanFixedPointKernelProductFDRep
          S C hcentral g theta).ρ (a, 1) z =
        (g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1.realization.ρ x z
    rw [LinearMap.congr_fun
      (productAmbientGlaubermanFixedPointKernelProductFDRep_inl
        S C hcentral g theta a) z]
    exact congrArg
      (fun y ↦
        (g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1.realization.ρ y z)
      ((productAmbientGlaubermanInternalFixedPointEquiv
        S C hcentral).apply_symm_apply x)
  change
    E
        (productAmbientGlaubermanFixedPointKernelRepresentation
          S C hcentral g theta x z) =
      (productAmbientGlaubermanRightInertiaTriple
        S C hcentral hgenerate g theta).character.realization.ρ
        (productAmbientGlaubermanFixedPointKernelToRightNormalCopy
          S C hcentral hgenerate g theta x)
        (E z)
  rw [← hinl]
  rw [←
    (productAmbientGlaubermanInternalFixedPointEquiv
      S C hcentral).apply_symm_apply x]
  exact hE.trans
    (congrArg
      (fun y ↦
        (productAmbientGlaubermanRightInertiaTriple
          S C hcentral hgenerate g theta).character.realization.ρ
            y (E z))
      (productAmbientGlaubermanRightNormalCopyProductEquiv_inl
        S C hcentral hgenerate g theta a))

/-- The exact product-model target equivalence, now between the two stable
fixed-point-kernel representations. -/
def productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    Representation.Equiv
      (productAmbientGlaubermanFixedPointKernelRepresentation
        S C hcentral g theta)
      (productAmbientGlaubermanRightNormalFixedPointRepresentation
        S C hcentral hgenerate g theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  apply Representation.Equiv.mk
    (productAmbientGlaubermanFixedPointKernelProductLinearEquiv
      S C hcentral hgenerate g theta)
  intro x
  apply LinearMap.ext
  intro z
  exact
    productAmbientGlaubermanFixedPointKernelProductLinearEquiv_intertwines
      S C hcentral hgenerate g theta x z

/-- The canonical extension equivalence, transported across the equality
between the generic inertia inclusion and the explicit right-normal copy. -/
def productAmbientGlaubermanFixedPointKernelExtensionRepresentationEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    Representation.Equiv
      (productAmbientGlaubermanFixedPointKernelRepresentation
        S C hcentral g theta)
      (productAmbientGlaubermanRightNormalFixedPointRepresentation
        S C hcentral hgenerate g theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let E :=
    productAmbientGlaubermanFixedPointKernelExtensionEquivRightNormalCharacter
      S C hcentral hgenerate g theta
  apply Representation.Equiv.mk E.toLinearEquiv
  intro x
  apply LinearMap.ext
  intro z
  have hE :=
    LinearMap.congr_fun (E.isIntertwining' x) z
  change
    E
        (productAmbientGlaubermanFixedPointKernelRepresentation
          S C hcentral g theta x z) =
      (productAmbientGlaubermanRightNormalFixedPointRepresentation
        S C hcentral hgenerate g theta x)
        (E z)
  change
    E
        ((g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1.realization.ρ x z) =
      (productAmbientGlaubermanRightInertiaTriple
        S C hcentral hgenerate g theta).character.realization.ρ
        (productAmbientGlaubermanFixedPointKernelToRightNormalCopy
          S C hcentral hgenerate g theta x)
        (E z)
  rw [← productAmbientGlaubermanFixedPointExtensionToInertia_eq
    S C hcentral hgenerate g theta]
  exact hE

/-- The exact target product equivalence and the canonical target extension
equivalence differ by one nonzero scalar. -/
theorem exists_productAmbientGlaubermanTargetProductEquivComparisonScalar
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ∃ c : ℂˣ,
      ∀ z :
        ProductAmbientGlaubermanFixedPointKernelSpace
          S C hcentral g theta,
        productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
            S C hcentral hgenerate g theta z =
          (c : ℂ) •
            productAmbientGlaubermanFixedPointKernelExtensionRepresentationEquiv
              S C hcentral hgenerate g theta z := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    exists_scalar_between_representation_equiv
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1
      (productAmbientGlaubermanRightNormalFixedPointRepresentation
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanFixedPointKernelExtensionRepresentationEquiv
        S C hcentral hgenerate g theta)

/-- The exact product-model target equivalence satisfies the same
full-inertia scalar comparison as the canonical extension equivalence. -/
theorem productAmbientGlaubermanTargetProductFullInertiaScalar_apply
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
      ProductAmbientGlaubermanFixedPointKernelSpace
        S C hcentral g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
        S C hcentral hgenerate g theta
        ((productAmbientGlaubermanFixedPointKernelInertiaProjective
          S C hcentral hgenerate g theta).operator b z) =
      (productAmbientGlaubermanTargetFullInertiaScalar
        S C hcentral hgenerate g theta b : ℂ) •
        (AssociatedGeneralExistence.projectiveRepresentation
          (productAmbientGlaubermanRightInertiaTriple
            S C hcentral hgenerate g theta)).operator
          b
          (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
            S C hcentral hgenerate g theta z) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  obtain ⟨c, hc⟩ :=
    exists_productAmbientGlaubermanTargetProductEquivComparisonScalar
      S C hcentral hgenerate g theta
  apply
    operator_comparison_of_constant_equiv
      (productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
        S C hcentral hgenerate g theta).toLinearEquiv
      (productAmbientGlaubermanFixedPointKernelExtensionRepresentationEquiv
        S C hcentral hgenerate g theta).toLinearEquiv
      ((productAmbientGlaubermanFixedPointKernelInertiaProjective
        S C hcentral hgenerate g theta).operator b)
      ((AssociatedGeneralExistence.projectiveRepresentation
        (productAmbientGlaubermanRightInertiaTriple
          S C hcentral hgenerate g theta)).operator b)
      c
      (productAmbientGlaubermanTargetFullInertiaScalar
        S C hcentral hgenerate g theta b)
      hc
      (fun v ↦
        productAmbientGlaubermanTarget_projective_operator_scalar_apply
          S C hcentral hgenerate g theta b v)
      z

/-- Selected-summand/mismatch equivalence using the exact source
normal-character equivalence that occurs in the full-inertia Schur
comparison. -/
def productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta) ≃ₗ[ℂ]
      ProductAmbientGlaubermanMultiplicityMismatchSpace
        S C hcentral hgenerate g theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let e :=
    productAmbientGlaubermanRightNormalCopyProductEquiv
      S C hcentral hgenerate g theta
  let iTarget :=
    productAmbientGlaubermanFixedPointKernelProductFDRepIsoRightNormalRestriction
      S C hcentral hgenerate g theta
  let iSource :=
    productAmbientGlaubermanSourceKernelProductFDRepIsoLeftNormalRestrictionDirect
      S C hcentral hgenerate g theta
  let productHomToPulledNormalHom :=
    fdRepHomCongr iTarget iSource
  let pulledNormalHomToNormalHom :
      (FDRep.res e.toMonoidHom
          (productAmbientGlaubermanRightInertiaTriple
            S C hcentral hgenerate g theta).character.realization ⟶
        FDRep.res e.toMonoidHom
          (FDRep.res
            (ProjectiveMultiplicityMismatch.normalHom
              (productAmbientGlaubermanInertiaRestrictionGroupData
                S C hcentral hgenerate g theta))
            (productAmbientGlaubermanLeftInertiaTriple
              S C hgenerate theta).character.realization)) ≃ₗ[ℂ]
        ((productAmbientGlaubermanRightInertiaTriple
            S C hcentral hgenerate g theta).character.realization ⟶
          FDRep.res
            (ProjectiveMultiplicityMismatch.normalHom
              (productAmbientGlaubermanInertiaRestrictionGroupData
                S C hcentral hgenerate g theta))
            (productAmbientGlaubermanLeftInertiaTriple
              S C hgenerate theta).character.realization) :=
    fdRepHomRestrictMulEquiv e
      (productAmbientGlaubermanRightInertiaTriple
        S C hcentral hgenerate g theta).character.realization
      (FDRep.res
        (ProjectiveMultiplicityMismatch.normalHom
          (productAmbientGlaubermanInertiaRestrictionGroupData
            S C hcentral hgenerate g theta))
        (productAmbientGlaubermanLeftInertiaTriple
          S C hgenerate theta).character.realization)
  let normalHomToMismatch :
      ((productAmbientGlaubermanRightInertiaTriple
          S C hcentral hgenerate g theta).character.realization ⟶
          FDRep.res
            (ProjectiveMultiplicityMismatch.normalHom
              (productAmbientGlaubermanInertiaRestrictionGroupData
                S C hcentral hgenerate g theta))
            (productAmbientGlaubermanLeftInertiaTriple
              S C hgenerate theta).character.realization) ≃ₗ[ℂ]
        ProductAmbientGlaubermanMultiplicityMismatchSpace
          S C hcentral hgenerate g theta :=
    ProjectiveMultiplicityMismatch.fdRepHomEquivSpace
      (productAmbientGlaubermanLeftAssociated
        S C hgenerate theta)
      (productAmbientGlaubermanRightAssociated
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta)
  exact
    (productAmbientGlaubermanCanonicalSelectedSummandEquivFDRepHom
      S C hcentral hgenerate g theta).trans
      (productHomToPulledNormalHom.trans
        (pulledNormalHomToNormalHom.trans
          normalHomToMismatch))

/-- Pointwise formula for the direct selected-summand/mismatch
identification. -/
@[simp]
theorem productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect_apply
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
      (productAmbientGlaubermanRightInertiaTriple
        S C hcentral hgenerate g theta).character.realization) :
    productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
        S C hcentral hgenerate g theta z w =
      (productAmbientGlaubermanSourceKernelProductFDRepIsoLeftNormalRestrictionDirect
        S C hcentral hgenerate g theta).hom
        (z.1
          ((productAmbientGlaubermanFixedPointKernelProductFDRepIsoRightNormalRestriction
            S C hcentral hgenerate g theta).inv w)) :=
  rfl

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
