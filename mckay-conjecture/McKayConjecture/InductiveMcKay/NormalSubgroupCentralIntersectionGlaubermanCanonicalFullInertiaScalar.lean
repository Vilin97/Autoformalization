/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.InertiaExtensionIntertwinerComparison
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalMismatchSpace

/-!
# Full-inertia scalar comparisons for the canonical Glauberman summand

This file extends the two Sylow-operator comparisons to every element of
the matched right inertia group.  The comparison scalars are obtained by
Schur uniqueness from the constructed normal-representation equivalences.
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
open CliffordPartition
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

noncomputable local instance productCanonicalFullInertiaFintype :
    Fintype X :=
  Fintype.ofFinite X

/-- The action of the matched right inertia group on the selected source
`q'`-kernel. -/
def productAmbientGlaubermanSourceKernelInertiaAction
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta →*
      MulAut (productPPrimeKernel S C hcentral) :=
  (productGlaubermanKernelStabilizerAction
    S C hcentral
    (productAmbientGlaubermanSourceKernelCharacter
      S C hcentral theta)).comp
      (productAmbientGlaubermanRightInertiaToKernelStabilizer
        S C hcentral hgenerate g theta)

/-- The selected source-kernel character is invariant under the full
matched right inertia action. -/
theorem productAmbientGlaubermanSourceKernelCharacter_isInvariant_inertia
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    IsInvariant
      (productAmbientGlaubermanSourceKernelInertiaAction
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1 := by
  intro b n
  exact
    productGlaubermanKernelCharacter_isInvariant
      S C hcentral
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta)
      (productAmbientGlaubermanRightInertiaToKernelStabilizer
        S C hcentral hgenerate g theta b) n

/-- The reconstructed source Gallagher character is exactly `theta`, so
it gives an honest extension of the selected source-kernel character. -/
theorem productAmbientGlaubermanTheta_isSourceKernelExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    IrreducibleCharacter.IsExtensionAlong
      (productPPrimeKernel S C hcentral).subtype
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1
      theta.1 := by
  rw [← productAmbientSourceGallagherCharacter_eq
    S C hcentral theta]
  exact
    productAmbientSourceGallagherCharacter_isExtension
      S C hcentral theta

/-- The kernel action and conjugation in the left inertia triple induce
the same automorphism of the source kernel. -/
theorem productAmbientGlaubermanSourceKernel_inertia_conjugates
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
    (n : productPPrimeKernel S C hcentral) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    extensionToInertiaNormalHom
        (product S C)
        (productPPrimeKernel S C hcentral).subtype
        theta.1
        (productAmbientGlaubermanSourceKernelInertiaAction
          S C hcentral hgenerate g theta b n) =
      MulAut.conjNormal
        (productAmbientGlaubermanInertiaEmbedding
          S C hcentral hgenerate g theta b)
        (extensionToInertiaNormalHom
          (product S C)
          (productPPrimeKernel S C hcentral).subtype
          theta.1 n) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  apply
    (inertiaNormalCopyEquiv
      (product S C) theta.1).injective
  apply Subtype.ext
  rfl

/-- The chosen extension-restriction equivalence for the source Gallagher
character, rewritten along its proved equality with `theta`. -/
def productAmbientGlaubermanSourceKernelEquivTheta
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    Representation.Equiv
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1.realization.ρ
      (theta.1.realization.ρ.comp
        (productPPrimeKernel S C hcentral).subtype) :=
  extensionRestrictionEquivOfEq
    (productAmbientGlaubermanSourceKernelCharacter
      S C hcentral theta).1.1
    (productPPrimeKernel S C hcentral).subtype
    (productAmbientSourceGallagherCharacter
      S C hcentral theta)
    (productAmbientSourceGallagherCharacter_isExtension
      S C hcentral theta)
    theta.1
    (productAmbientSourceGallagherCharacter_eq
      S C hcentral theta)

/-- The source extension equivalence intertwines the honest product action
with the restriction of `theta`. -/
theorem productAmbientGlaubermanSourceKernelEquivTheta_product_apply
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (d : ProductAmbientGlaubermanKernelProduct S C hcentral)
    (z :
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1.realization) :
    productAmbientGlaubermanSourceKernelEquivTheta
        S C hcentral theta
        ((ProductAmbientGlaubermanSourceKernelProductFDRep
          S C hcentral theta).ρ d z) =
      theta.1.realization.ρ
        (productAmbientGlaubermanKernelProductToSource
          S C hcentral d)
        (productAmbientGlaubermanSourceKernelEquivTheta
          S C hcentral theta z) := by
  exact
    extensionRestrictionEquivOfEq_transported_apply
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1
      (productPPrimeKernel S C hcentral).subtype
      (productAmbientSourceGallagherCharacter
        S C hcentral theta)
      (productAmbientSourceGallagherCharacter_isExtension
        S C hcentral theta)
      (productAmbientGlaubermanKernelProductToSource
        S C hcentral)
      theta.1
      (productAmbientSourceGallagherCharacter_eq
        S C hcentral theta)
      d z

/-- The exact normal-representation equivalence underlying the source
product isomorphism.  It deliberately uses the same chosen extension
restriction equivalence as the product representation. -/
def productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    Representation.Equiv
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1.realization.ρ
      ((productAmbientGlaubermanLeftInertiaTriple
          S C hgenerate theta).character.realization.ρ.comp
        (extensionToInertiaNormalHom
          (product S C)
          (productPPrimeKernel S C hcentral).subtype
          theta.1)) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let chi :=
    (productAmbientGlaubermanSourceKernelCharacter
      S C hcentral theta).1.1
  let eExtension :=
    productAmbientGlaubermanSourceKernelEquivTheta
      S C hcentral theta
  let eCopy :=
    FDRep.representationEquivOfIso
      (inertiaCopyRealizationIso (product S C) theta.1)
  apply Representation.Equiv.mk
    (eExtension.toLinearEquiv.trans
      eCopy.toLinearEquiv.symm)
  intro n
  apply LinearMap.ext
  intro z
  have hExtension :=
    LinearMap.congr_fun
      (eExtension.isIntertwining' n) z
  have hCopy :=
    LinearMap.congr_fun
      (eCopy.symm.isIntertwining'
        (extensionToInertiaNormalHom
          (product S C)
          (productPPrimeKernel S C hcentral).subtype
          theta.1 n))
      (eExtension z)
  change
    eExtension
        ((productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1.1.realization.ρ n z) =
      theta.1.realization.ρ
        ((productPPrimeKernel S C hcentral).subtype n)
        (eExtension z) at hExtension
  change
    eCopy.symm
        (eExtension
          ((productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta).1.1.realization.ρ n z)) =
      (inertiaCopyCharacter
          (product S C) theta.1).realization.ρ
        (extensionToInertiaNormalHom
          (product S C)
          (productPPrimeKernel S C hcentral).subtype
          theta.1 n)
        (eCopy.symm (eExtension z))
  rw [hExtension]
  change
    eCopy.symm
        (theta.1.realization.ρ
          (inertiaNormalCopyEquiv (product S C) theta.1
            (extensionToInertiaNormalHom
              (product S C)
              (productPPrimeKernel S C hcentral).subtype
              theta.1 n))
          (eExtension z)) =
      (inertiaCopyCharacter
          (product S C) theta.1).realization.ρ
        (extensionToInertiaNormalHom
          (product S C)
          (productPPrimeKernel S C hcentral).subtype
          theta.1 n)
        (eCopy.symm (eExtension z))
      at hCopy
  have hcoordinate :
      inertiaNormalCopyEquiv (product S C) theta.1
          (extensionToInertiaNormalHom
            (product S C)
            (productPPrimeKernel S C hcentral).subtype
            theta.1 n) =
        (productPPrimeKernel S C hcentral).subtype n := by
    change
      inertiaNormalCopyEquiv (product S C) theta.1
          ((inertiaNormalCopyEquiv
            (product S C) theta.1).symm
              ((productPPrimeKernel S C hcentral).subtype n)) =
        (productPPrimeKernel S C hcentral).subtype n
    exact
      (inertiaNormalCopyEquiv
        (product S C) theta.1).apply_symm_apply _
  rw [hcoordinate] at hCopy
  exact hCopy

/-- Direct product-representation isomorphism whose underlying linear
equivalence is the full source-kernel equivalence above. -/
def productAmbientGlaubermanSourceKernelProductFDRepIsoLeftNormalRestrictionDirect
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
    ProductAmbientGlaubermanSourceKernelProductFDRep
        S C hcentral theta ≅
      FDRep.res
        ((ProjectiveMultiplicityMismatch.normalHom
          (productAmbientGlaubermanInertiaRestrictionGroupData
            S C hcentral hgenerate g theta)).comp
          (productAmbientGlaubermanRightNormalCopyProductEquiv
            S C hcentral hgenerate g theta).toMonoidHom)
        (productAmbientGlaubermanLeftInertiaTriple
          S C hgenerate theta).character.realization := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let E :=
    productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
      S C hcentral hgenerate g theta
  refine
    Action.mkIso E.toLinearEquiv.toFGModuleCatIso
      (fun d ↦ ?_)
  apply ConcreteCategory.hom_ext
  intro z
  let eExtension :=
    productAmbientGlaubermanSourceKernelEquivTheta
      S C hcentral theta
  let eCopy :=
    FDRep.representationEquivOfIso
      (inertiaCopyRealizationIso (product S C) theta.1)
  have hCopy :=
    LinearMap.congr_fun
      (eCopy.symm.isIntertwining'
        ((ProjectiveMultiplicityMismatch.normalHom
          (productAmbientGlaubermanInertiaRestrictionGroupData
            S C hcentral hgenerate g theta)).comp
          (productAmbientGlaubermanRightNormalCopyProductEquiv
            S C hcentral hgenerate g theta).toMonoidHom d))
      (eExtension z)
  have hmap :=
    congrArg
      (fun f :
        ProductAmbientGlaubermanKernelProduct S C hcentral →*
          product S C ↦ f d)
      (productAmbientGlauberman_normalHom_productEquiv
        S C hcentral hgenerate g theta)
  change
    E ((ProductAmbientGlaubermanSourceKernelProductFDRep
        S C hcentral theta).ρ d z) =
      (productAmbientGlaubermanLeftInertiaTriple
          S C hgenerate theta).character.realization.ρ
        ((ProjectiveMultiplicityMismatch.normalHom
          (productAmbientGlaubermanInertiaRestrictionGroupData
            S C hcentral hgenerate g theta)).comp
          (productAmbientGlaubermanRightNormalCopyProductEquiv
            S C hcentral hgenerate g theta).toMonoidHom d)
        (E z)
  dsimp only [E,
    productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter]
  change
    eCopy.symm
        (eExtension
          ((ProductAmbientGlaubermanSourceKernelProductFDRep
            S C hcentral theta).ρ d z)) =
      (productAmbientGlaubermanLeftInertiaTriple
          S C hgenerate theta).character.realization.ρ
        ((ProjectiveMultiplicityMismatch.normalHom
          (productAmbientGlaubermanInertiaRestrictionGroupData
            S C hcentral hgenerate g theta)).comp
          (productAmbientGlaubermanRightNormalCopyProductEquiv
            S C hcentral hgenerate g theta).toMonoidHom d)
        (eCopy.symm (eExtension z))
  have hProduct :=
    productAmbientGlaubermanSourceKernelEquivTheta_product_apply
      S C hcentral theta d z
  change
    eExtension
        ((ProductAmbientGlaubermanSourceKernelProductFDRep
          S C hcentral theta).ρ d z) =
      theta.1.realization.ρ
        (productAmbientGlaubermanKernelProductToSource
          S C hcentral d)
        (eExtension z) at hProduct
  rw [hProduct]
  change
    eCopy.symm
        (theta.1.realization.ρ
          (inertiaNormalCopyEquiv (product S C) theta.1
            ((ProjectiveMultiplicityMismatch.normalHom
              (productAmbientGlaubermanInertiaRestrictionGroupData
                S C hcentral hgenerate g theta)).comp
              (productAmbientGlaubermanRightNormalCopyProductEquiv
                S C hcentral hgenerate g theta).toMonoidHom d))
          (eExtension z)) =
      (productAmbientGlaubermanLeftInertiaTriple
          S C hgenerate theta).character.realization.ρ
        ((ProjectiveMultiplicityMismatch.normalHom
          (productAmbientGlaubermanInertiaRestrictionGroupData
            S C hcentral hgenerate g theta)).comp
          (productAmbientGlaubermanRightNormalCopyProductEquiv
            S C hcentral hgenerate g theta).toMonoidHom d)
        (eCopy.symm (eExtension z))
  change
    eCopy.symm
        (theta.1.realization.ρ
          (inertiaNormalCopyEquiv (product S C) theta.1
            ((ProjectiveMultiplicityMismatch.normalHom
              (productAmbientGlaubermanInertiaRestrictionGroupData
                S C hcentral hgenerate g theta)).comp
              (productAmbientGlaubermanRightNormalCopyProductEquiv
                S C hcentral hgenerate g theta).toMonoidHom d))
          (eExtension z)) =
      (inertiaCopyCharacter
          (product S C) theta.1).realization.ρ
        ((ProjectiveMultiplicityMismatch.normalHom
          (productAmbientGlaubermanInertiaRestrictionGroupData
            S C hcentral hgenerate g theta)).comp
          (productAmbientGlaubermanRightNormalCopyProductEquiv
            S C hcentral hgenerate g theta).toMonoidHom d)
        (eCopy.symm (eExtension z))
      at hCopy
  exact hCopy

/-- For every element of the matched right inertia group, the canonical
source-kernel intertwiner becomes the canonical left associated-projective
operator up to a nonzero scalar under the direct normal-character
equivalence.  The scalar is supplied by Schur uniqueness. -/
theorem exists_productAmbientGlaubermanSourceFullInertiaScalar
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
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    ∃ c : ℂˣ,
      ∀ z :
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1.1.realization,
        productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
            S C hcentral hgenerate g theta
            (intertwiner
              (productAmbientGlaubermanSourceKernelInertiaAction
                S C hcentral hgenerate g theta)
              (productAmbientGlaubermanSourceKernelCharacter
                S C hcentral theta).1.1
              (productAmbientGlaubermanSourceKernelCharacter_isInvariant_inertia
                S C hcentral hgenerate g theta)
              b z) =
          (c : ℂ) •
            (AssociatedGeneralExistence.projectiveRepresentation
              (productAmbientGlaubermanLeftInertiaTriple
                S C hgenerate theta)).operator
              (productAmbientGlaubermanInertiaEmbedding
                S C hcentral hgenerate g theta b)
              (productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
                S C hcentral hgenerate g theta z) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    exists_intertwiner_scalar_of_associated_along
      (productAmbientGlaubermanSourceKernelInertiaAction
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1
      (productAmbientGlaubermanSourceKernelCharacter_isInvariant_inertia
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanLeftAssociated
        S C hgenerate theta)
      (extensionToInertiaNormalHom
        (product S C)
        (productPPrimeKernel S C hcentral).subtype
        theta.1)
      (productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInertiaEmbedding
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanSourceKernel_inertia_conjugates
        S C hcentral hgenerate g theta)
      b

/-- The Schur scalar comparing the source-kernel intertwiner and the
left associated-projective operator at a matched inertia element. -/
def productAmbientGlaubermanSourceFullInertiaScalar
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
    (exists_productAmbientGlaubermanSourceFullInertiaScalar
      S C hcentral hgenerate g theta b)

/-- Pointwise source full-inertia scalar comparison. -/
theorem productAmbientGlaubermanSourceFullInertiaScalar_apply
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
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1.realization) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
        S C hcentral hgenerate g theta
        (intertwiner
          (productAmbientGlaubermanSourceKernelInertiaAction
            S C hcentral hgenerate g theta)
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta).1.1
          (productAmbientGlaubermanSourceKernelCharacter_isInvariant_inertia
            S C hcentral hgenerate g theta)
          b z) =
      (productAmbientGlaubermanSourceFullInertiaScalar
        S C hcentral hgenerate g theta b : ℂ) •
        (AssociatedGeneralExistence.projectiveRepresentation
          (productAmbientGlaubermanLeftInertiaTriple
            S C hgenerate theta)).operator
          (productAmbientGlaubermanInertiaEmbedding
            S C hcentral hgenerate g theta b)
          (productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
            S C hcentral hgenerate g theta z) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    Classical.choose_spec
      (exists_productAmbientGlaubermanSourceFullInertiaScalar
        S C hcentral hgenerate g theta b) z

/-- The canonical source-kernel intertwiner projective representation,
restricted from the standard semidirect-product construction to the
matched right inertia group. -/
def productAmbientGlaubermanSourceKernelInertiaProjective
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
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1.realization :=
  (AssociatedExistence.projectiveRepresentation
    (productAmbientGlaubermanSourceKernelInertiaAction
      S C hcentral hgenerate g theta)
    (productAmbientGlaubermanSourceKernelCharacter
      S C hcentral theta).1.1
    (productAmbientGlaubermanSourceKernelCharacter_isInvariant_inertia
      S C hcentral hgenerate g theta)).comap
        (SemidirectProduct.inr :
          ProductAmbientGlaubermanRightInertiaGroup
              S C hcentral hgenerate g theta →*
            (productPPrimeKernel S C hcentral) ⋊[
              productAmbientGlaubermanSourceKernelInertiaAction
                S C hcentral hgenerate g theta]
              ProductAmbientGlaubermanRightInertiaGroup
                S C hcentral hgenerate g theta)

/-- The operators of the restricted semidirect-product construction are
literally the canonical source-kernel intertwiners. -/
@[simp]
theorem productAmbientGlaubermanSourceKernelInertiaProjective_operator
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
    (productAmbientGlaubermanSourceKernelInertiaProjective
        S C hcentral hgenerate g theta).operator b =
      intertwiner
        (productAmbientGlaubermanSourceKernelInertiaAction
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1.1
        (productAmbientGlaubermanSourceKernelCharacter_isInvariant_inertia
          S C hcentral hgenerate g theta)
        b := by
  rw [show
    productAmbientGlaubermanSourceKernelInertiaProjective
        S C hcentral hgenerate g theta =
      (AssociatedExistence.projectiveRepresentation
        (productAmbientGlaubermanSourceKernelInertiaAction
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1.1
        (productAmbientGlaubermanSourceKernelCharacter_isInvariant_inertia
          S C hcentral hgenerate g theta)).comap
            (SemidirectProduct.inr :
              ProductAmbientGlaubermanRightInertiaGroup
                  S C hcentral hgenerate g theta →*
                (productPPrimeKernel S C hcentral) ⋊[
                  productAmbientGlaubermanSourceKernelInertiaAction
                    S C hcentral hgenerate g theta]
                  ProductAmbientGlaubermanRightInertiaGroup
                    S C hcentral hgenerate g theta) from rfl]
  rw [ProjectiveRepresentation.comap_operator,
    AssociatedExistence.projectiveRepresentation_operator]
  change
    realizationAction
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1.1 1 *
      intertwiner
        (productAmbientGlaubermanSourceKernelInertiaAction
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1.1
        (productAmbientGlaubermanSourceKernelCharacter_isInvariant_inertia
          S C hcentral hgenerate g theta)
        b =
      intertwiner
        (productAmbientGlaubermanSourceKernelInertiaAction
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1.1
        (productAmbientGlaubermanSourceKernelCharacter_isInvariant_inertia
          S C hcentral hgenerate g theta)
        b
  rw [map_one, one_mul]

/-- The pulled-back left associated representation is the source-kernel
intertwiner representation rescaled by the inverse Schur cochain. -/
theorem productAmbientGlaubermanLeftAssociated_factorSet_eq_source_gauge
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    ((AssociatedGeneralExistence.projectiveRepresentation
        (productAmbientGlaubermanLeftInertiaTriple
          S C hgenerate theta)).comap
      (productAmbientGlaubermanInertiaEmbedding
        S C hcentral hgenerate g theta)).factorSet =
      (productAmbientGlaubermanSourceKernelInertiaProjective
        S C hcentral hgenerate g theta).factorSet.gauge
        (fun b ↦
          (productAmbientGlaubermanSourceFullInertiaScalar
            S C hcentral hgenerate g theta b)⁻¹) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  apply
    ProjectiveRepresentation.factorSet_eq_gauge_of_rescaled_equiv
      (productAmbientGlaubermanSourceKernelInertiaProjective
        S C hcentral hgenerate g theta)
      ((AssociatedGeneralExistence.projectiveRepresentation
          (productAmbientGlaubermanLeftInertiaTriple
            S C hgenerate theta)).comap
        (productAmbientGlaubermanInertiaEmbedding
          S C hcentral hgenerate g theta))
      (productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
        S C hcentral hgenerate g theta).toLinearEquiv
      (fun b ↦
        (productAmbientGlaubermanSourceFullInertiaScalar
          S C hcentral hgenerate g theta b)⁻¹)
  intro b z
  rw [ProjectiveRepresentation.rescale_operator,
    LinearEquiv.mul_apply, scalarLinearEquiv_apply, map_smul]
  rw [
    productAmbientGlaubermanSourceKernelInertiaProjective_operator,
    ProjectiveRepresentation.comap_operator]
  calc
    (((productAmbientGlaubermanSourceFullInertiaScalar
          S C hcentral hgenerate g theta b)⁻¹ : ℂˣ) : ℂ) •
        (productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
          S C hcentral hgenerate g theta).toLinearEquiv
          (intertwiner
            (productAmbientGlaubermanSourceKernelInertiaAction
              S C hcentral hgenerate g theta)
            (productAmbientGlaubermanSourceKernelCharacter
              S C hcentral theta).1.1
            (productAmbientGlaubermanSourceKernelCharacter_isInvariant_inertia
              S C hcentral hgenerate g theta)
            b z) =
      (((productAmbientGlaubermanSourceFullInertiaScalar
          S C hcentral hgenerate g theta b)⁻¹ : ℂˣ) : ℂ) •
        productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
          S C hcentral hgenerate g theta
          (intertwiner
            (productAmbientGlaubermanSourceKernelInertiaAction
              S C hcentral hgenerate g theta)
            (productAmbientGlaubermanSourceKernelCharacter
              S C hcentral theta).1.1
            (productAmbientGlaubermanSourceKernelCharacter_isInvariant_inertia
              S C hcentral hgenerate g theta)
            b z) := rfl
    _ =
      (((productAmbientGlaubermanSourceFullInertiaScalar
          S C hcentral hgenerate g theta b)⁻¹ : ℂˣ) : ℂ) •
        ((productAmbientGlaubermanSourceFullInertiaScalar
          S C hcentral hgenerate g theta b : ℂ) •
          (AssociatedGeneralExistence.projectiveRepresentation
            (productAmbientGlaubermanLeftInertiaTriple
              S C hgenerate theta)).operator
            (productAmbientGlaubermanInertiaEmbedding
              S C hcentral hgenerate g theta b)
            (productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
              S C hcentral hgenerate g theta z)) := by
      rw [productAmbientGlaubermanSourceFullInertiaScalar_apply]
    _ =
      (AssociatedGeneralExistence.projectiveRepresentation
        (productAmbientGlaubermanLeftInertiaTriple
          S C hgenerate theta)).operator
        (productAmbientGlaubermanInertiaEmbedding
          S C hcentral hgenerate g theta b)
        (productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
          S C hcentral hgenerate g theta z) := by
      simp only [Units.val_inv_eq_inv_val,
        inv_smul_smul₀
          (productAmbientGlaubermanSourceFullInertiaScalar
            S C hcentral hgenerate g theta b).ne_zero]
    _ =
      (AssociatedGeneralExistence.projectiveRepresentation
        (productAmbientGlaubermanLeftInertiaTriple
          S C hgenerate theta)).operator
        (productAmbientGlaubermanInertiaEmbedding
          S C hcentral hgenerate g theta b)
        ((productAmbientGlaubermanSourceKernelEquivLeftNormalCharacter
          S C hcentral hgenerate g theta).toLinearEquiv z) := rfl

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
