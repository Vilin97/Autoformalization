/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.InertiaExtensionIntertwinerComparison
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalMismatchSpace

/-!
# Target-side full-inertia scalar comparison

This file compares the canonical intertwiner of the Glauberman fixed-point
character with the associated operator in the final right inertia triple.
The comparison is valid for every element of the matched inertia group.
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

noncomputable local instance productCanonicalTargetFullInertiaFintype :
    Fintype X :=
  Fintype.ofFinite X

/-- The matched right inertia group acts on the fixed-point kernel through
the stabilizer of the selected source-kernel character. -/
def productAmbientGlaubermanFixedPointKernelInertiaAction
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta →*
      MulAut (productPPrimeKernelFixedPoints S C hcentral) :=
  (productGlaubermanFixedPointsStabilizerAction
    S C hcentral
    (productAmbientGlaubermanSourceKernelCharacter
      S C hcentral theta)).comp
      (productAmbientGlaubermanRightInertiaToKernelStabilizer
        S C hcentral hgenerate g theta)

/-- The Glauberman fixed-point character is invariant under the full
matched right inertia action. -/
theorem productAmbientGlaubermanFixedPointCharacter_isInvariant_inertia
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    IsInvariant
      (productAmbientGlaubermanFixedPointKernelInertiaAction
        S C hcentral hgenerate g theta)
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1 := by
  intro b x
  exact
    productGlaubermanFixedPointCharacter_isInvariant
      S C hcentral g
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta)
      (productAmbientGlaubermanRightInertiaToKernelStabilizer
        S C hcentral hgenerate g theta b) x

/-- Include the ambient fixed-point kernel in the normal copy of the final
right inertia triple. -/
def productAmbientGlaubermanFixedPointKernelToRightNormalCopy
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    productPPrimeKernelFixedPoints S C hcentral →*
      ProductAmbientGlaubermanRightNormalCopy
        S C hcentral hgenerate g theta :=
  (productAmbientGlaubermanRightNormalCopyFixedPointHom
    S C hcentral hgenerate g theta).comp
      (productAmbientGlaubermanInternalFixedPointEquiv
        S C hcentral).symm.toMonoidHom

/-- The same fixed-point inclusion, viewed directly in the ambient
normalizer. -/
def productAmbientGlaubermanFixedPointKernelToAmbientNormalizer
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    productPPrimeKernelFixedPoints S C hcentral →*
      ambientNormalizer S :=
  (internalProductNormalizer S C).subtype.comp
    ((productNormalizerEquivInternal S C).toMonoidHom.comp
      (productAmbientGlaubermanFixedPointsToLocalNormalizer
        S C hcentral))

/-- The normal-copy and direct ambient-normalizer descriptions of a
fixed-point element agree. -/
theorem productAmbientGlaubermanFixedPointKernelToRightNormalCopy_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (x : productPPrimeKernelFixedPoints S C hcentral) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
      (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (((productAmbientGlaubermanFixedPointKernelToRightNormalCopy
          S C hcentral hgenerate g theta x :
        ProductAmbientGlaubermanRightInertiaGroup
          S C hcentral hgenerate g theta) :
      ambientNormalizer S)) =
      productAmbientGlaubermanFixedPointKernelToAmbientNormalizer
        S C hcentral x := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  apply Subtype.ext
  simp [productAmbientGlaubermanFixedPointKernelToRightNormalCopy,
    productAmbientGlaubermanRightNormalCopyFixedPointHom,
    productAmbientGlaubermanRightNormalCopyProductEquiv,
    productAmbientGlaubermanFixedPointKernelToAmbientNormalizer,
    productAmbientGlaubermanInternalFixedPointEquiv,
    normalizerProductEquiv,
    pPrimeKernelFixedPointsProductEquiv_apply]
  rfl

/-- The fixed-point action is the conjugation induced by the final right
inertia triple. -/
theorem productAmbientGlaubermanFixedPointKernel_inertia_conjugates
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
    (x : productPPrimeKernelFixedPoints S C hcentral) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
      (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    productAmbientGlaubermanFixedPointKernelToRightNormalCopy
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanFixedPointKernelInertiaAction
          S C hcentral hgenerate g theta b x) =
      MulAut.conjNormal b
        (productAmbientGlaubermanFixedPointKernelToRightNormalCopy
          S C hcentral hgenerate g theta x) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  apply Subtype.ext
  apply Subtype.ext
  let k :=
    productAmbientGlaubermanRightInertiaToKernelStabilizer
      S C hcentral hgenerate g theta b
  rw [productAmbientGlaubermanFixedPointKernelToRightNormalCopy_coe
    S C hcentral hgenerate g theta]
  change
    productAmbientGlaubermanFixedPointKernelToAmbientNormalizer
        S C hcentral
        (productPPrimeKernelFixedPointsConjugation
          S C hcentral (k : ambientNormalizer S) x) =
      _
  rw [MulAut.conjNormal_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [productAmbientGlaubermanFixedPointKernelToRightNormalCopy_coe
    S C hcentral hgenerate g theta]
  change
    productAmbientGlaubermanFixedPointKernelToAmbientNormalizer
        S C hcentral
        (productPPrimeKernelFixedPointsConjugation
          S C hcentral (k : ambientNormalizer S) x) =
      (b : ambientNormalizer S) *
        productAmbientGlaubermanFixedPointKernelToAmbientNormalizer
          S C hcentral x *
        (b : ambientNormalizer S)⁻¹
  apply Subtype.ext
  change
    ((((productPPrimeKernelFixedPointsConjugation
        S C hcentral (k : ambientNormalizer S) x :
      productPPrimeKernelFixedPoints S C hcentral) :
      product S C) : X)) =
        ((b : ambientNormalizer S) : X) *
          (((x : productPPrimeKernelFixedPoints
            S C hcentral) : product S C) : X) *
          ((b : ambientNormalizer S) : X)⁻¹
  rw [productPPrimeKernelFixedPointsConjugation_apply_coe,
    productConjugation_apply_coe]
  rfl

/-- The chosen realization of the canonical Glauberman fixed-point
character. -/
noncomputable def ProductAmbientGlaubermanFixedPointKernelFDRep
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    FDRep ℂ (productPPrimeKernelFixedPoints S C hcentral) :=
  (g.characterEquiv
    (productAmbientGlaubermanSourceKernelCharacter
      S C hcentral theta)).1.realization

/-- The chosen right normal-character realization restricted to the
fixed-point kernel. -/
noncomputable def ProductAmbientGlaubermanRightNormalFixedPointRestrictionFDRep
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
      (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    FDRep ℂ (productPPrimeKernelFixedPoints S C hcentral) :=
  FDRep.res
    (productAmbientGlaubermanFixedPointKernelToRightNormalCopy
      S C hcentral hgenerate g theta)
    (productAmbientGlaubermanRightInertiaTriple
      S C hcentral hgenerate g theta).character.realization

/-- The fixed-point realization space, named separately so that later
representation types do not repeatedly normalize the full construction. -/
abbrev ProductAmbientGlaubermanFixedPointKernelSpace
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :=
  (g.characterEquiv
    (productAmbientGlaubermanSourceKernelCharacter
      S C hcentral theta)).1.realization

/-- The final right normal-character realization space. -/
abbrev ProductAmbientGlaubermanRightNormalCharacterSpace
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  (productAmbientGlaubermanRightInertiaTriple
    S C hcentral hgenerate g theta).character.realization

/-- The fixed-point character representation, under a short stable name. -/
noncomputable def productAmbientGlaubermanFixedPointKernelRepresentation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    Representation ℂ
      (productPPrimeKernelFixedPoints S C hcentral)
      (ProductAmbientGlaubermanFixedPointKernelSpace
        S C hcentral g theta) :=
  (ProductAmbientGlaubermanFixedPointKernelFDRep
    S C hcentral g theta).ρ

/-- The final right normal-character representation restricted to the
fixed-point kernel, under a short stable name. -/
noncomputable def productAmbientGlaubermanRightNormalFixedPointRepresentation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
      (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    Representation ℂ
      (productPPrimeKernelFixedPoints S C hcentral)
      (ProductAmbientGlaubermanRightNormalCharacterSpace
        S C hcentral hgenerate g theta) :=
  (ProductAmbientGlaubermanRightNormalFixedPointRestrictionFDRep
    S C hcentral hgenerate g theta).ρ

/-- Include the fixed-point kernel in the internal target group supporting
the final right character. -/
def productAmbientGlaubermanFixedPointKernelToRightCharacter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    productPPrimeKernelFixedPoints S C hcentral →*
      internalProductNormalizer S C :=
  (productNormalizerEquivInternal S C).toMonoidHom.comp
    (productAmbientGlaubermanFixedPointsToLocalNormalizer
      S C hcentral)

/-- The final right character is an extension of the canonical
Glauberman fixed-point character along the internal target inclusion. -/
theorem productAmbientGlaubermanRightCharacter_isFixedPointExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    IrreducibleCharacter.IsExtensionAlong
      (productAmbientGlaubermanFixedPointKernelToRightCharacter
        S C hcentral)
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1
      (productAmbientGlaubermanRightKernelTransportCharacter
        S C hcentral g theta) := by
  intro x
  rw [show
    productAmbientGlaubermanRightKernelTransportCharacter
        S C hcentral g theta =
      (productAmbientNormalizedLocalGallagherCharacter
        S C hcentral g theta).comap
          (productNormalizerEquivInternal S C).symm by
    rw [productAmbientNormalizedLocalGallagherCharacter_eq
      S C hcentral g theta]
    rfl]
  rw [IrreducibleCharacter.comap_values]
  change
    (productAmbientNormalizedLocalGallagherCharacter
      S C hcentral g theta).values
        (productAmbientGlaubermanFixedPointsToLocalNormalizer
          S C hcentral x) =
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1.values x
  exact
    productAmbientNormalizedLocalGallagherCharacter_isFixedPointExtension
      S C hcentral g theta x

/-- The generic extension-to-inertia inclusion is the explicit
fixed-point-factor inclusion used by the target product representation. -/
theorem productAmbientGlaubermanFixedPointExtensionToInertia_eq
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI :
      (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    extensionToInertiaNormalHom
        (internalProductNormalizer S C)
        (productAmbientGlaubermanFixedPointKernelToRightCharacter
          S C hcentral)
        (productAmbientGlaubermanRightKernelTransportCharacter
          S C hcentral g theta) =
      productAmbientGlaubermanFixedPointKernelToRightNormalCopy
        S C hcentral hgenerate g theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  apply MonoidHom.ext
  intro x
  let a :=
    (productAmbientGlaubermanInternalFixedPointEquiv
      S C hcentral).symm x
  have hlocal :
      normalizerProductEquiv S C hcentral (a, 1) =
        productAmbientGlaubermanFixedPointsToLocalNormalizer
          S C hcentral x := by
    have h :=
      productAmbientGlaubermanKernelProductToLocalNormalizer_inl
        S C hcentral a
    rw [(productAmbientGlaubermanInternalFixedPointEquiv
      S C hcentral).apply_symm_apply x] at h
    exact h
  change
    (inertiaNormalCopyEquiv
      (internalProductNormalizer S C)
      (productAmbientGlaubermanRightKernelTransportCharacter
        S C hcentral g theta)).symm
        (productNormalizerEquivInternal S C
          (productAmbientGlaubermanFixedPointsToLocalNormalizer
            S C hcentral x)) =
      (inertiaNormalCopyEquiv
        (internalProductNormalizer S C)
        (productAmbientGlaubermanRightKernelTransportCharacter
          S C hcentral g theta)).symm
          (productNormalizerEquivInternal S C
          (normalizerProductEquiv S C hcentral (a, 1)))
  rw [hlocal]

/-- The canonical extension-restriction equivalence for the target
fixed-point character and the final right inertia normal character. -/
def productAmbientGlaubermanFixedPointKernelExtensionEquivRightNormalCharacter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI :
      (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    Representation.Equiv
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1.realization.ρ
      ((ofInertia
          (internalProductNormalizer S C)
          (productAmbientGlaubermanRightKernelTransportCharacter
            S C hcentral g theta)).character.realization.ρ.comp
        (extensionToInertiaNormalHom
          (internalProductNormalizer S C)
          (productAmbientGlaubermanFixedPointKernelToRightCharacter
            S C hcentral)
          (productAmbientGlaubermanRightKernelTransportCharacter
            S C hcentral g theta))) := by
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    extensionRestrictionEquivInertiaCopy
      (internalProductNormalizer S C)
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1
      (productAmbientGlaubermanFixedPointKernelToRightCharacter
        S C hcentral)
      (productAmbientGlaubermanRightKernelTransportCharacter
        S C hcentral g theta)
      (productAmbientGlaubermanRightCharacter_isFixedPointExtension
        S C hcentral g theta)

/-- For every matched right-inertia element, the canonical target
fixed-point intertwiner becomes the canonical right associated-projective
operator up to a constructed nonzero scalar. -/
theorem exists_productAmbientGlaubermanTargetFullInertiaScalar
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
    letI :
      (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ∃ c : ℂˣ,
      ∀ z :
        (g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1.realization,
        productAmbientGlaubermanFixedPointKernelExtensionEquivRightNormalCharacter
            S C hcentral hgenerate g theta
            (intertwiner
              (productAmbientGlaubermanFixedPointKernelInertiaAction
                S C hcentral hgenerate g theta)
              (g.characterEquiv
                (productAmbientGlaubermanSourceKernelCharacter
                  S C hcentral theta)).1
              (productAmbientGlaubermanFixedPointCharacter_isInvariant_inertia
                S C hcentral hgenerate g theta)
              b z) =
          (c : ℂ) •
            (AssociatedGeneralExistence.projectiveRepresentation
              (productAmbientGlaubermanRightInertiaTriple
                S C hcentral hgenerate g theta)).operator
              b
              (productAmbientGlaubermanFixedPointKernelExtensionEquivRightNormalCharacter
                S C hcentral hgenerate g theta z) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  apply
    exists_inertiaExtensionIntertwinerScalar
      (internalProductNormalizer S C)
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1
      (productAmbientGlaubermanFixedPointKernelToRightCharacter
        S C hcentral)
      (productAmbientGlaubermanRightKernelTransportCharacter
        S C hcentral g theta)
      (productAmbientGlaubermanRightCharacter_isFixedPointExtension
        S C hcentral g theta)
      (productAmbientGlaubermanFixedPointKernelInertiaAction
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanFixedPointCharacter_isInvariant_inertia
        S C hcentral hgenerate g theta)
      (fun a ↦ a)
      ?_ b
  intro a x
  rw [productAmbientGlaubermanFixedPointExtensionToInertia_eq
    S C hcentral hgenerate g theta]
  exact
    productAmbientGlaubermanFixedPointKernel_inertia_conjugates
      S C hcentral hgenerate g theta a x

/-- The Schur scalar comparing the target fixed-point intertwiner and the
right associated-projective operator. -/
def productAmbientGlaubermanTargetFullInertiaScalar
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
    (exists_productAmbientGlaubermanTargetFullInertiaScalar
      S C hcentral hgenerate g theta b)

/-- Pointwise target full-inertia scalar comparison. -/
theorem productAmbientGlaubermanTargetFullInertiaScalar_apply
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
    letI :
      (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    productAmbientGlaubermanFixedPointKernelExtensionEquivRightNormalCharacter
        S C hcentral hgenerate g theta
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
          (productAmbientGlaubermanFixedPointKernelExtensionEquivRightNormalCharacter
            S C hcentral hgenerate g theta z) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    Classical.choose_spec
      (exists_productAmbientGlaubermanTargetFullInertiaScalar
        S C hcentral hgenerate g theta b) z

/-- The canonical target fixed-point intertwiner projective
representation, restricted to the matched right inertia group. -/
def productAmbientGlaubermanFixedPointKernelInertiaProjective
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
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1.realization :=
  (AssociatedExistence.projectiveRepresentation
    (productAmbientGlaubermanFixedPointKernelInertiaAction
      S C hcentral hgenerate g theta)
    (g.characterEquiv
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta)).1
    (productAmbientGlaubermanFixedPointCharacter_isInvariant_inertia
      S C hcentral hgenerate g theta)).comap
        (SemidirectProduct.inr :
          ProductAmbientGlaubermanRightInertiaGroup
              S C hcentral hgenerate g theta →*
            (productPPrimeKernelFixedPoints S C hcentral) ⋊[
              productAmbientGlaubermanFixedPointKernelInertiaAction
                S C hcentral hgenerate g theta]
              ProductAmbientGlaubermanRightInertiaGroup
                S C hcentral hgenerate g theta)

/-- The target intertwiner projective operators are literally the
canonical fixed-point intertwiners. -/
@[simp]
theorem productAmbientGlaubermanFixedPointKernelInertiaProjective_operator
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
    (productAmbientGlaubermanFixedPointKernelInertiaProjective
        S C hcentral hgenerate g theta).operator b =
      intertwiner
        (productAmbientGlaubermanFixedPointKernelInertiaAction
          S C hcentral hgenerate g theta)
        (g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1
        (productAmbientGlaubermanFixedPointCharacter_isInvariant_inertia
          S C hcentral hgenerate g theta)
        b := by
  rw [show
    productAmbientGlaubermanFixedPointKernelInertiaProjective
        S C hcentral hgenerate g theta =
      (AssociatedExistence.projectiveRepresentation
        (productAmbientGlaubermanFixedPointKernelInertiaAction
          S C hcentral hgenerate g theta)
        (g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1
        (productAmbientGlaubermanFixedPointCharacter_isInvariant_inertia
          S C hcentral hgenerate g theta)).comap
            (SemidirectProduct.inr :
              ProductAmbientGlaubermanRightInertiaGroup
                  S C hcentral hgenerate g theta →*
                (productPPrimeKernelFixedPoints S C hcentral) ⋊[
                  productAmbientGlaubermanFixedPointKernelInertiaAction
                    S C hcentral hgenerate g theta]
                  ProductAmbientGlaubermanRightInertiaGroup
                    S C hcentral hgenerate g theta) from rfl]
  rw [ProjectiveRepresentation.comap_operator,
    AssociatedExistence.projectiveRepresentation_operator]
  change
    realizationAction
        (g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1 1 *
      intertwiner
        (productAmbientGlaubermanFixedPointKernelInertiaAction
          S C hcentral hgenerate g theta)
        (g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1
        (productAmbientGlaubermanFixedPointCharacter_isInvariant_inertia
          S C hcentral hgenerate g theta)
        b =
      intertwiner
        (productAmbientGlaubermanFixedPointKernelInertiaAction
          S C hcentral hgenerate g theta)
        (g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1
        (productAmbientGlaubermanFixedPointCharacter_isInvariant_inertia
          S C hcentral hgenerate g theta)
        b
  rw [map_one, one_mul]

/-- The target Schur comparison, expressed directly for the named target
fixed-point projective representation. -/
theorem productAmbientGlaubermanTarget_projective_operator_scalar_apply
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta : PPrimeIrreducibleCharacter (product S C) q)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta)
    (z :
      ProductAmbientGlaubermanFixedPointKernelSpace
        S C hcentral g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
      (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (productAmbientGlaubermanFixedPointKernelExtensionEquivRightNormalCharacter
      S C hcentral hgenerate g theta).toLinearEquiv
        ((productAmbientGlaubermanFixedPointKernelInertiaProjective
          S C hcentral hgenerate g theta).operator b z) =
      (productAmbientGlaubermanTargetFullInertiaScalar
        S C hcentral hgenerate g theta b : ℂ) •
        (AssociatedGeneralExistence.projectiveRepresentation
          (productAmbientGlaubermanRightInertiaTriple
            S C hcentral hgenerate g theta)).operator b
          ((productAmbientGlaubermanFixedPointKernelExtensionEquivRightNormalCharacter
            S C hcentral hgenerate g theta).toLinearEquiv z) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  rw [
    productAmbientGlaubermanFixedPointKernelInertiaProjective_operator]
  exact
    productAmbientGlaubermanTargetFullInertiaScalar_apply
      S C hcentral hgenerate g theta b z

/-- The canonical right associated factor set is the target fixed-point
intertwiner factor set gauged by the inverse target Schur cochain. -/
theorem productAmbientGlaubermanRightAssociated_factorSet_eq_target_gauge
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
      (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (AssociatedGeneralExistence.projectiveRepresentation
      (productAmbientGlaubermanRightInertiaTriple
        S C hcentral hgenerate g theta)).factorSet =
      (productAmbientGlaubermanFixedPointKernelInertiaProjective
        S C hcentral hgenerate g theta).factorSet.gauge
        (fun b ↦
          (productAmbientGlaubermanTargetFullInertiaScalar
            S C hcentral hgenerate g theta b)⁻¹) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    ProjectiveRepresentation.factorSet_eq_gauge_inverse_of_scalar_equiv
      (productAmbientGlaubermanFixedPointKernelInertiaProjective
        S C hcentral hgenerate g theta)
      (AssociatedGeneralExistence.projectiveRepresentation
        (productAmbientGlaubermanRightInertiaTriple
          S C hcentral hgenerate g theta))
      (productAmbientGlaubermanFixedPointKernelExtensionEquivRightNormalCharacter
        S C hcentral hgenerate g theta).toLinearEquiv
      (productAmbientGlaubermanTargetFullInertiaScalar
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanTarget_projective_operator_scalar_apply
        S C hcentral hgenerate g theta)

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
