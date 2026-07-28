/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.InvariantExtensionIntertwinerComparison
import McKayConjecture.CharacterTriple.ProjectiveConjugationScalarRatio
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalOperatorComparison
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalSylowParameter

/-!
# Canonical Sylow scalar in the kernel Glauberman comparison

This file compares the canonical intertwiners in the kernel Glauberman
Hom-action with honest operators afforded by the two Gallagher extensions.
It fixes the orientation of the resulting scalar ratio and supplies the
selected Sylow parameter from the normalized extension construction.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CharacterTriple.AssociatedExistence
open CliffordPartition
open ComplementReduction
open CentralIntersectionKernelAssembly
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

noncomputable local instance productCanonicalSylowScalarFintype :
    Fintype (product S C) :=
  Fintype.ofFinite (product S C)

/-- The internal Sylow factor included in the source group `CS`. -/
def productAmbientGlaubermanSourceSylowInclusion :
    internalNormalizerSylow (productSylow S C) →*
      product S C :=
  (localNormalizer
      (productSylow S C :
        Subgroup (product S C))).subtype.comp
    (internalNormalizerSylow
      (productSylow S C)).subtype

/-- The same Sylow factor included in the local normalizer. -/
def productAmbientGlaubermanLocalSylowInclusion :
    internalNormalizerSylow (productSylow S C) →*
      localNormalizer
        (productSylow S C :
          Subgroup (product S C)) :=
  (internalNormalizerSylow
    (productSylow S C)).subtype

/-- The internal Sylow factor regarded as a subgroup of the ambient
normalizer through the canonical normalizer-identification. -/
def productAmbientGlaubermanSylowToAmbientNormalizer :
    internalNormalizerSylow (productSylow S C) →*
      ambientNormalizer S :=
  (internalProductNormalizer S C).subtype.comp
    ((productNormalizerEquivInternal S C).toMonoidHom.comp
      (internalNormalizerSylow
        (productSylow S C)).subtype)

/-- The right-normal-copy route and the direct source-normalizer route
give the same ambient element on the internal Sylow factor. -/
theorem productAmbientGlaubermanRightNormalSylowToInertia_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b : internalNormalizerSylow (productSylow S C)) :
    ((productAmbientGlaubermanRightNormalSylowToInertia
        S C hcentral hgenerate g theta b :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta) :
      ambientNormalizer S) =
      productAmbientGlaubermanSylowToAmbientNormalizer S C b := by
  apply Subtype.ext
  simp [productAmbientGlaubermanRightNormalSylowToInertia,
    productAmbientGlaubermanRightNormalCopySylowHom,
    productAmbientGlaubermanRightNormalCopyProductEquiv,
    productAmbientGlaubermanSylowToAmbientNormalizer,
    normalizerProductEquiv,
    pPrimeKernelFixedPointsProductEquiv_apply]

/-- The internal Sylow factor mapped to the stabilizer of the canonical
source-kernel character. -/
def productAmbientGlaubermanSylowToKernelStabilizer
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    internalNormalizerSylow (productSylow S C) →*
      ProductGlaubermanKernelCharacterStabilizer
        S C hcentral
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta) :=
  (productAmbientGlaubermanRightInertiaToKernelStabilizer
    S C hcentral hgenerate g theta).comp
      (productAmbientGlaubermanRightNormalSylowToInertia
        S C hcentral hgenerate g theta)

/-- The source-kernel action restricted to the internal Sylow factor. -/
def productAmbientGlaubermanSourceKernelSylowAction
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    internalNormalizerSylow (productSylow S C) →*
      MulAut (productPPrimeKernel S C hcentral) :=
  (productGlaubermanKernelStabilizerAction
    S C hcentral
    (productAmbientGlaubermanSourceKernelCharacter
      S C hcentral theta)).comp
      (productAmbientGlaubermanSylowToKernelStabilizer
        S C hcentral hgenerate g theta)

/-- Conjugation by the source Sylow inclusion implements the restricted
source-kernel action used by the canonical intertwiners. -/
theorem productAmbientGlaubermanSourceSylowInclusion_conjugates
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b : internalNormalizerSylow (productSylow S C))
    (n : productPPrimeKernel S C hcentral) :
    productAmbientGlaubermanSourceSylowInclusion S C b *
          (productPPrimeKernel S C hcentral).subtype n *
          (productAmbientGlaubermanSourceSylowInclusion S C b)⁻¹ =
      (productPPrimeKernel S C hcentral).subtype
        (productAmbientGlaubermanSourceKernelSylowAction
          S C hcentral hgenerate g theta b n) := by
  apply Subtype.ext
  let k :=
    productAmbientGlaubermanSylowToKernelStabilizer
      S C hcentral hgenerate g theta b
  have hb :=
    productAmbientGlaubermanRightNormalSylowToInertia_coe
      S C hcentral hgenerate g theta b
  have hk :
      (k : ambientNormalizer S) =
        productAmbientGlaubermanSylowToAmbientNormalizer S C b := by
    exact hb
  have hsource :
      (((productAmbientGlaubermanSourceSylowInclusion S C b :
          product S C) : X)) =
        ((k : ambientNormalizer S) : X) := by
    rw [hk]
    rfl
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hsource]
  change
    ((k : ambientNormalizer S) : X) * (n : product S C).1 *
          ((k : ambientNormalizer S) : X)⁻¹ =
      (((productPPrimeKernelConjugationHom
          S C hcentral (k : ambientNormalizer S) n :
            productPPrimeKernel S C hcentral) :
          product S C) : X)
  rw [productPPrimeKernelConjugation_apply_coe,
    productConjugation_apply_coe]

/-- On the source-kernel realization, the honest operator afforded by the
reconstructed Gallagher extension differs from the exact canonical kernel
intertwiner by a nonzero scalar. -/
theorem exists_productAmbientGlaubermanSourceSylowExtensionScalar
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b : internalNormalizerSylow (productSylow S C)) :
    ∃ c : ℂˣ,
      ∀ v :
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1.1.realization,
      transportedExtensionOperator
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta).1.1
          (productPPrimeKernel S C hcentral).subtype
          (productAmbientSourceGallagherCharacter
            S C hcentral theta)
          (productAmbientSourceGallagherCharacter_isExtension
            S C hcentral theta)
          (productAmbientGlaubermanSourceSylowInclusion S C)
          b v =
        (c : ℂ) •
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
            (productAmbientGlaubermanSylowToKernelStabilizer
              S C hcentral hgenerate g theta b) v := by
  apply
    exists_scalar_of_covariance
      (chi :=
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1.1)
      (beta :=
        productAmbientGlaubermanSourceKernelSylowAction
          S C hcentral hgenerate g theta b)
  · exact
      intertwiner_mul_rho
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
        (productAmbientGlaubermanSylowToKernelStabilizer
          S C hcentral hgenerate g theta b)
  · exact
      transportedExtensionOperator_covariance
        (alpha :=
          productAmbientGlaubermanSourceKernelSylowAction
            S C hcentral hgenerate g theta)
        (chi :=
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta).1.1)
        (i := (productPPrimeKernel S C hcentral).subtype)
        (psi :=
          productAmbientSourceGallagherCharacter
            S C hcentral theta)
        (hpsi :=
          productAmbientSourceGallagherCharacter_isExtension
            S C hcentral theta)
        (j := productAmbientGlaubermanSourceSylowInclusion S C)
        (hconj :=
          productAmbientGlaubermanSourceSylowInclusion_conjugates
            S C hcentral hgenerate g theta)
        b

/-- The source comparison cochain: honest Gallagher operator equals this
scalar times the canonical source-kernel intertwiner. -/
def productAmbientGlaubermanSourceSylowExtensionScalar
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    internalNormalizerSylow (productSylow S C) → ℂˣ :=
  fun b ↦
    Classical.choose
      (exists_productAmbientGlaubermanSourceSylowExtensionScalar
        S C hcentral hgenerate g theta b)

/-- Defining operator equation for the source comparison cochain. -/
theorem productAmbientGlaubermanSourceSylowExtensionScalar_spec
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b : internalNormalizerSylow (productSylow S C))
    (v :
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1.realization) :
    transportedExtensionOperator
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1.1
        (productPPrimeKernel S C hcentral).subtype
        (productAmbientSourceGallagherCharacter
          S C hcentral theta)
        (productAmbientSourceGallagherCharacter_isExtension
          S C hcentral theta)
        (productAmbientGlaubermanSourceSylowInclusion S C)
        b v =
      (productAmbientGlaubermanSourceSylowExtensionScalar
        S C hcentral hgenerate g theta b : ℂ) •
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
          (productAmbientGlaubermanSylowToKernelStabilizer
            S C hcentral hgenerate g theta b) v :=
  Classical.choose_spec
    (exists_productAmbientGlaubermanSourceSylowExtensionScalar
      S C hcentral hgenerate g theta b) v

/-- The fixed-point kernel included in the local normalizer using the
canonical internal/external fixed-point relabelling. -/
def productAmbientGlaubermanFixedPointsToLocalNormalizer
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    productPPrimeKernelFixedPoints S C hcentral →*
      localNormalizer
        (productSylow S C :
          Subgroup (product S C)) :=
  (internalKernelNormalizer
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C))).subtype.comp
    (localKernelAmbientFixedPointsEquiv
      S C hcentral).symm.toMonoidHom

/-- The source invariant represented by the active orbit is the canonical
source-kernel character selected directly from the ambient character. -/
theorem productSourceInvariantCharacter_activeOrbitIndex_eq
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    productSourceInvariantCharacter
        S C hcentral
        (productGlaubermanActivationData S C hcentral)
        (activeOrbitIndex
          (productPPrimeKernel S C hcentral) theta) =
      productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta := by
  apply Subtype.ext
  rfl

/-- The normalized local Gallagher character is, after the canonical
fixed-point relabelling, an honest extension of the exact Glauberman
correspondent used in the kernel Hom-space. -/
theorem productAmbientNormalizedLocalGallagherCharacter_isFixedPointExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    IrreducibleCharacter.IsExtensionAlong
      (productAmbientGlaubermanFixedPointsToLocalNormalizer
        S C hcentral)
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1
      (productAmbientNormalizedLocalGallagherCharacter
        S C hcentral g theta) := by
  intro x
  let e :=
    localKernelAmbientFixedPointsEquiv S C hcentral
  let r :=
    activeOrbitIndex
      (productPPrimeKernel S C hcentral) theta
  let a :=
    productGlaubermanActivationData S C hcentral
  have hlocal :=
    productAmbientNormalizedLocalGallagherCharacter_isExtension
      S C hcentral g theta (e.symm x)
  have hout :=
    productGlaubermanTargetPPrimeOut_eq
      S C hcentral g a r
  have hsource :
      productSourceInvariantCharacter
          S C hcentral a r =
        productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta := by
    exact
      productSourceInvariantCharacter_activeOrbitIndex_eq
        S C hcentral theta
  rw [hsource] at hout
  have hvalue :=
    congrArg
      (fun phi :
        PPrimeIrreducibleCharacter
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C))) q ↦
        phi.1.values (e.symm x))
      hout
  change
    (productAmbientNormalizedLocalGallagherCharacter
      S C hcentral g theta).values
        (productAmbientGlaubermanFixedPointsToLocalNormalizer
          S C hcentral x) =
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1.values x
  calc
    _ =
        (((productGlaubermanActiveOrbitEquiv
            S C hcentral g a r).pPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))).1).values
          (e.symm x) := hlocal
    _ =
        (g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1.values x := by
      change
        (((productGlaubermanActiveOrbitEquiv
            S C hcentral g a r).pPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))).1).values
            (e.symm x) =
          ((g.characterEquiv
            (productAmbientGlaubermanSourceKernelCharacter
              S C hcentral theta)).1.comap e).values
            (e.symm x) at hvalue
      rw [IrreducibleCharacter.comap_values,
        e.apply_symm_apply] at hvalue
      exact hvalue

/-- The fixed-point-kernel action restricted to the internal Sylow
factor. -/
def productAmbientGlaubermanFixedPointKernelSylowAction
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    internalNormalizerSylow (productSylow S C) →*
      MulAut (productPPrimeKernelFixedPoints S C hcentral) :=
  (productGlaubermanFixedPointsStabilizerAction
    S C hcentral
    (productAmbientGlaubermanSourceKernelCharacter
      S C hcentral theta)).comp
      (productAmbientGlaubermanSylowToKernelStabilizer
        S C hcentral hgenerate g theta)

/-- Conjugation by the local Sylow inclusion implements the restricted
fixed-point-kernel action used by the canonical target intertwiners. -/
theorem productAmbientGlaubermanLocalSylowInclusion_conjugates
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b : internalNormalizerSylow (productSylow S C))
    (n : productPPrimeKernelFixedPoints S C hcentral) :
    productAmbientGlaubermanLocalSylowInclusion S C b *
          productAmbientGlaubermanFixedPointsToLocalNormalizer
            S C hcentral n *
          (productAmbientGlaubermanLocalSylowInclusion S C b)⁻¹ =
      productAmbientGlaubermanFixedPointsToLocalNormalizer
        S C hcentral
        (productAmbientGlaubermanFixedPointKernelSylowAction
          S C hcentral hgenerate g theta b n) := by
  apply Subtype.ext
  apply Subtype.ext
  let k :=
    productAmbientGlaubermanSylowToKernelStabilizer
      S C hcentral hgenerate g theta b
  have hb :=
    productAmbientGlaubermanRightNormalSylowToInertia_coe
      S C hcentral hgenerate g theta b
  have hk :
      (k : ambientNormalizer S) =
        productAmbientGlaubermanSylowToAmbientNormalizer S C b := by
    exact hb
  have hsylow :
      (((productAmbientGlaubermanLocalSylowInclusion S C b :
          localNormalizer
            (productSylow S C :
              Subgroup (product S C))) :
          product S C) : X) =
        ((k : ambientNormalizer S) : X) := by
    rw [hk]
    rfl
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hinclusion :
      ∀ y : productPPrimeKernelFixedPoints S C hcentral,
        ((productAmbientGlaubermanFixedPointsToLocalNormalizer
          S C hcentral y :
            localNormalizer
              (productSylow S C :
                Subgroup (product S C))) :
          product S C) = y := by
    intro y
    rfl
  simp only [hinclusion]
  rw [hsylow]
  change
    ((k : ambientNormalizer S) : X) * (n : product S C).1 *
          ((k : ambientNormalizer S) : X)⁻¹ =
      (((productPPrimeKernelFixedPointsConjugation
        S C hcentral (k : ambientNormalizer S) n :
          productPPrimeKernelFixedPoints S C hcentral) :
        product S C) : X)
  rw [productPPrimeKernelFixedPointsConjugation_apply_coe,
    productConjugation_apply_coe]

/-- On the fixed-point-kernel realization, the honest operator afforded
by the normalized local Gallagher extension differs from the exact
canonical target intertwiner by a nonzero scalar. -/
theorem exists_productAmbientGlaubermanTargetSylowExtensionScalar
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b : internalNormalizerSylow (productSylow S C)) :
    ∃ c : ℂˣ,
      ∀ w :
        (g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1.realization,
      transportedExtensionOperator
          (g.characterEquiv
            (productAmbientGlaubermanSourceKernelCharacter
              S C hcentral theta)).1
          (productAmbientGlaubermanFixedPointsToLocalNormalizer
            S C hcentral)
          (productAmbientNormalizedLocalGallagherCharacter
            S C hcentral g theta)
          (productAmbientNormalizedLocalGallagherCharacter_isFixedPointExtension
            S C hcentral g theta)
          (productAmbientGlaubermanLocalSylowInclusion S C)
          b w =
        (c : ℂ) •
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
            (productAmbientGlaubermanSylowToKernelStabilizer
              S C hcentral hgenerate g theta b) w := by
  apply
    exists_scalar_of_covariance
      (chi :=
        (g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1)
      (beta :=
        productAmbientGlaubermanFixedPointKernelSylowAction
          S C hcentral hgenerate g theta b)
  · exact
      intertwiner_mul_rho
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
        (productAmbientGlaubermanSylowToKernelStabilizer
          S C hcentral hgenerate g theta b)
  · exact
      transportedExtensionOperator_covariance
        (alpha :=
          productAmbientGlaubermanFixedPointKernelSylowAction
            S C hcentral hgenerate g theta)
        (chi :=
          (g.characterEquiv
            (productAmbientGlaubermanSourceKernelCharacter
              S C hcentral theta)).1)
        (i :=
          productAmbientGlaubermanFixedPointsToLocalNormalizer
            S C hcentral)
        (psi :=
          productAmbientNormalizedLocalGallagherCharacter
            S C hcentral g theta)
        (hpsi :=
          productAmbientNormalizedLocalGallagherCharacter_isFixedPointExtension
            S C hcentral g theta)
        (j := productAmbientGlaubermanLocalSylowInclusion S C)
        (hconj :=
          productAmbientGlaubermanLocalSylowInclusion_conjugates
            S C hcentral hgenerate g theta)
        b

/-- The target comparison cochain: honest normalized-local operator equals
this scalar times the canonical fixed-point-kernel intertwiner. -/
def productAmbientGlaubermanTargetSylowExtensionScalar
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    internalNormalizerSylow (productSylow S C) → ℂˣ :=
  fun b ↦
    Classical.choose
      (exists_productAmbientGlaubermanTargetSylowExtensionScalar
        S C hcentral hgenerate g theta b)

/-- Defining operator equation for the target comparison cochain. -/
theorem productAmbientGlaubermanTargetSylowExtensionScalar_spec
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b : internalNormalizerSylow (productSylow S C))
    (w :
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1.realization) :
    transportedExtensionOperator
        (g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1
        (productAmbientGlaubermanFixedPointsToLocalNormalizer
          S C hcentral)
        (productAmbientNormalizedLocalGallagherCharacter
          S C hcentral g theta)
        (productAmbientNormalizedLocalGallagherCharacter_isFixedPointExtension
          S C hcentral g theta)
        (productAmbientGlaubermanLocalSylowInclusion S C)
        b w =
      (productAmbientGlaubermanTargetSylowExtensionScalar
        S C hcentral hgenerate g theta b : ℂ) •
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
          (productAmbientGlaubermanSylowToKernelStabilizer
            S C hcentral hgenerate g theta b) w :=
  Classical.choose_spec
    (exists_productAmbientGlaubermanTargetSylowExtensionScalar
      S C hcentral hgenerate g theta b) w

/-- The honest internal-Sylow representation afforded by the recovered
source Gallagher extension, transported to the canonical source-kernel
realization. -/
abbrev ProductAmbientGlaubermanSourceKernelSylowFDRep
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    FDRep ℂ (internalNormalizerSylow (productSylow S C)) :=
  transportedExtensionFDRep
    (productAmbientGlaubermanSourceKernelCharacter
      S C hcentral theta).1.1
    (productPPrimeKernel S C hcentral).subtype
    (productAmbientSourceGallagherCharacter
      S C hcentral theta)
    (productAmbientSourceGallagherCharacter_isExtension
      S C hcentral theta)
    (productAmbientGlaubermanSourceSylowInclusion S C)

/-- The honest internal-Sylow representation afforded by the normalized
local Gallagher extension, transported to the canonical fixed-point
kernel realization. -/
abbrev ProductAmbientGlaubermanFixedPointKernelSylowFDRep
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    FDRep ℂ (internalNormalizerSylow (productSylow S C)) :=
  transportedExtensionFDRep
    (g.characterEquiv
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta)).1
    (productAmbientGlaubermanFixedPointsToLocalNormalizer
      S C hcentral)
    (productAmbientNormalizedLocalGallagherCharacter
      S C hcentral g theta)
    (productAmbientNormalizedLocalGallagherCharacter_isFixedPointExtension
      S C hcentral g theta)
    (productAmbientGlaubermanLocalSylowInclusion S C)

/-- Scalar expressing the canonical source-kernel intertwiner in terms of
the honest recovered-source extension operator. -/
def productAmbientGlaubermanSourceCanonicalSylowScalar
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    internalNormalizerSylow (productSylow S C) → ℂˣ :=
  fun b ↦
    (productAmbientGlaubermanSourceSylowExtensionScalar
      S C hcentral hgenerate g theta b)⁻¹

/-- Scalar expressing the canonical fixed-point-kernel intertwiner in
terms of the honest normalized-local extension operator. -/
def productAmbientGlaubermanTargetCanonicalSylowScalar
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    internalNormalizerSylow (productSylow S C) → ℂˣ :=
  fun b ↦
    (productAmbientGlaubermanTargetSylowExtensionScalar
      S C hcentral hgenerate g theta b)⁻¹

/-- The canonical source-kernel intertwiner is the inverse comparison
scalar times the honest recovered-source extension operator. -/
theorem productAmbientGlaubermanSourceCanonicalSylowScalar_spec
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b : internalNormalizerSylow (productSylow S C))
    (v :
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1.realization) :
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
        (productAmbientGlaubermanSylowToKernelStabilizer
          S C hcentral hgenerate g theta b) v =
      (productAmbientGlaubermanSourceCanonicalSylowScalar
        S C hcentral hgenerate g theta b : ℂ) •
        (ProductAmbientGlaubermanSourceKernelSylowFDRep
          S C hcentral theta).ρ b v := by
  rw [show
    (ProductAmbientGlaubermanSourceKernelSylowFDRep
      S C hcentral theta).ρ b v =
        transportedExtensionOperator
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta).1.1
          (productPPrimeKernel S C hcentral).subtype
          (productAmbientSourceGallagherCharacter
            S C hcentral theta)
          (productAmbientSourceGallagherCharacter_isExtension
            S C hcentral theta)
          (productAmbientGlaubermanSourceSylowInclusion S C)
          b v from rfl]
  rw [productAmbientGlaubermanSourceSylowExtensionScalar_spec
    S C hcentral hgenerate g theta b v]
  simp only [productAmbientGlaubermanSourceCanonicalSylowScalar,
    Units.val_inv_eq_inv_val, ← mul_smul]
  rw [inv_mul_cancel₀
    (productAmbientGlaubermanSourceSylowExtensionScalar
      S C hcentral hgenerate g theta b).ne_zero,
    one_smul]

/-- The canonical fixed-point-kernel intertwiner is the inverse comparison
scalar times the honest normalized-local extension operator. -/
theorem productAmbientGlaubermanTargetCanonicalSylowScalar_spec
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b : internalNormalizerSylow (productSylow S C))
    (w :
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1.realization) :
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
        (productAmbientGlaubermanSylowToKernelStabilizer
          S C hcentral hgenerate g theta b) w =
      (productAmbientGlaubermanTargetCanonicalSylowScalar
        S C hcentral hgenerate g theta b : ℂ) •
        (ProductAmbientGlaubermanFixedPointKernelSylowFDRep
          S C hcentral g theta).ρ b w := by
  rw [show
    (ProductAmbientGlaubermanFixedPointKernelSylowFDRep
      S C hcentral g theta).ρ b w =
        transportedExtensionOperator
          (g.characterEquiv
            (productAmbientGlaubermanSourceKernelCharacter
              S C hcentral theta)).1
          (productAmbientGlaubermanFixedPointsToLocalNormalizer
            S C hcentral)
          (productAmbientNormalizedLocalGallagherCharacter
            S C hcentral g theta)
          (productAmbientNormalizedLocalGallagherCharacter_isFixedPointExtension
            S C hcentral g theta)
          (productAmbientGlaubermanLocalSylowInclusion S C)
          b w from rfl]
  rw [productAmbientGlaubermanTargetSylowExtensionScalar_spec
    S C hcentral hgenerate g theta b w]
  simp only [productAmbientGlaubermanTargetCanonicalSylowScalar,
    Units.val_inv_eq_inv_val, ← mul_smul]
  rw [inv_mul_cancel₀
    (productAmbientGlaubermanTargetSylowExtensionScalar
      S C hcentral hgenerate g theta b).ne_zero,
    one_smul]

/-- The selected scalar on the kernel Hom-space.  The first argument of
`conjugationScalarRatio` is the codomain (source-kernel) scalar and the
second is the domain (fixed-point-kernel) scalar. -/
def productAmbientGlaubermanCanonicalSelectedSylowScalar
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    internalNormalizerSylow (productSylow S C) → ℂˣ :=
  ProjectiveRepresentation.conjugationScalarRatio
    (productAmbientGlaubermanSourceCanonicalSylowScalar
      S C hcentral hgenerate g theta)
    (productAmbientGlaubermanTargetCanonicalSylowScalar
      S C hcentral hgenerate g theta)

@[simp]
theorem productAmbientGlaubermanCanonicalSelectedSylowScalar_apply
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b : internalNormalizerSylow (productSylow S C)) :
    productAmbientGlaubermanCanonicalSelectedSylowScalar
        S C hcentral hgenerate g theta b =
      (productAmbientGlaubermanSourceSylowExtensionScalar
        S C hcentral hgenerate g theta b)⁻¹ *
      productAmbientGlaubermanTargetSylowExtensionScalar
        S C hcentral hgenerate g theta b := by
  simp [productAmbientGlaubermanCanonicalSelectedSylowScalar,
    productAmbientGlaubermanSourceCanonicalSylowScalar,
    productAmbientGlaubermanTargetCanonicalSylowScalar,
    ProjectiveRepresentation.conjugationScalarRatio]

/-- On the internal Sylow factor, the canonical kernel Hom-operator is
the selected scalar times the honest `linHom` representation afforded by
the two Gallagher extensions. -/
theorem productAmbientGlaubermanKernelMultiplicityProjective_operator_eq_selected_smul_linHom
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b : internalNormalizerSylow (productSylow S C))
    (f :
      ProductAmbientGlaubermanKernelMultiplicitySpace
        S C hcentral g theta) :
    (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
        S C hcentral hgenerate g theta).operator
          (productAmbientGlaubermanRightNormalSylowToInertia
            S C hcentral hgenerate g theta b) f =
      (productAmbientGlaubermanCanonicalSelectedSylowScalar
        S C hcentral hgenerate g theta b : ℂ) •
        Representation.linHom
          (ProductAmbientGlaubermanFixedPointKernelSylowFDRep
            S C hcentral g theta).ρ
          (ProductAmbientGlaubermanSourceKernelSylowFDRep
            S C hcentral theta).ρ b f := by
  apply LinearMap.ext
  intro w
  change
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
        (productAmbientGlaubermanSylowToKernelStabilizer
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
            (productAmbientGlaubermanSylowToKernelStabilizer
              S C hcentral hgenerate g theta b)).symm w)) =
      (productAmbientGlaubermanCanonicalSelectedSylowScalar
        S C hcentral hgenerate g theta b : ℂ) •
        Representation.linHom
          (ProductAmbientGlaubermanFixedPointKernelSylowFDRep
            S C hcentral g theta).ρ
          (ProductAmbientGlaubermanSourceKernelSylowFDRep
            S C hcentral theta).ρ b f w
  exact
    ProjectiveRepresentation.conjugation_apply_eq_scalarRatio_smul_linHom
      (ProductAmbientGlaubermanFixedPointKernelSylowFDRep
        S C hcentral g theta).ρ
      (ProductAmbientGlaubermanSourceKernelSylowFDRep
        S C hcentral theta).ρ
      (fun d ↦
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
          (productAmbientGlaubermanSylowToKernelStabilizer
            S C hcentral hgenerate g theta d))
      (fun d ↦
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
          (productAmbientGlaubermanSylowToKernelStabilizer
            S C hcentral hgenerate g theta d))
      (productAmbientGlaubermanTargetCanonicalSylowScalar
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanSourceCanonicalSylowScalar
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanTargetCanonicalSylowScalar_spec
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanSourceCanonicalSylowScalar_spec
        S C hcentral hgenerate g theta)
      b f w

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
