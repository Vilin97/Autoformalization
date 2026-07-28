/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalSylowCochain

/-!
# The canonical selected Glauberman summand

The right normal copy has canonical coordinates
`C_K(P) × P`.  The two Gallagher extensions give honest
representations of this product on the two kernel realizations.  The
canonical selected Sylow summand is identified with the invariant
linear maps for their `linHom` representation, and hence with the
corresponding morphism space by mathlib's
`Representation.linHom.invariantsEquivFDRepHom`.
-/

noncomputable section

open CategoryTheory

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

/-- Fixed-point-times-Sylow coordinates on the local normalizer. -/
abbrev ProductAmbientGlaubermanKernelProduct
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :=
  internalPPrimeKernelFixedPoints
      (productSylow S C)
      (productPPrimeKernel S C hcentral) ×
    internalNormalizerSylow (productSylow S C)

/-- Product coordinates included in the local normalizer. -/
def productAmbientGlaubermanKernelProductToLocalNormalizer
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    ProductAmbientGlaubermanKernelProduct S C hcentral →*
      localNormalizer
        (productSylow S C :
          Subgroup (product S C)) :=
  (normalizerProductEquiv S C hcentral).toMonoidHom

/-- Product coordinates included in the source group. -/
def productAmbientGlaubermanKernelProductToSource
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    ProductAmbientGlaubermanKernelProduct S C hcentral →*
      product S C :=
  (localNormalizer
    (productSylow S C :
      Subgroup (product S C))).subtype.comp
      (productAmbientGlaubermanKernelProductToLocalNormalizer
        S C hcentral)

@[simp]
theorem productAmbientGlaubermanKernelProductToLocalNormalizer_inr
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (b : internalNormalizerSylow (productSylow S C)) :
    productAmbientGlaubermanKernelProductToLocalNormalizer
        S C hcentral (1, b) =
      productAmbientGlaubermanLocalSylowInclusion S C b := by
  apply Subtype.ext
  change
    ((normalizerProductEquiv S C hcentral (1, b) :
        localNormalizer
          (productSylow S C :
            Subgroup (product S C))) :
      product S C) =
      ((b : internalNormalizerSylow (productSylow S C)) :
        product S C)
  rw [show
    normalizerProductEquiv S C hcentral =
      pPrimeKernelFixedPointsProductEquiv
        (productSylow S C)
        (productPPrimeKernel S C hcentral)
        (productPPrimeKernel_isPPrimeGroup S C hcentral)
        (productPPrimeKernel_sup_productSylow_eq_top
          S C hcentral) from rfl]
  rw [pPrimeKernelFixedPointsProductEquiv_apply]
  simp

@[simp]
theorem productAmbientGlaubermanKernelProductToSource_inr
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (b : internalNormalizerSylow (productSylow S C)) :
    productAmbientGlaubermanKernelProductToSource
        S C hcentral (1, b) =
      productAmbientGlaubermanSourceSylowInclusion S C b := by
  change
    (localNormalizer
      (productSylow S C :
        Subgroup (product S C))).subtype
        (productAmbientGlaubermanKernelProductToLocalNormalizer
          S C hcentral (1, b)) =
      (localNormalizer
        (productSylow S C :
          Subgroup (product S C))).subtype
        (productAmbientGlaubermanLocalSylowInclusion S C b)
  rw [productAmbientGlaubermanKernelProductToLocalNormalizer_inr]

/-- Forget the ambient-normalizer packaging of a fixed point and regard
it as an element of the source kernel. -/
def productAmbientGlaubermanInternalFixedPointToSourceKernel
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral) →*
      productPPrimeKernel S C hcentral where
  toFun a :=
    ⟨(a : product S C), a.property.1⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' a d := by
    apply Subtype.ext
    rfl

/-- Relabel an internal fixed point as the ambient fixed-point element
used by the Glauberman correspondent. -/
def productAmbientGlaubermanInternalFixedPointEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    internalPPrimeKernelFixedPoints
          (productSylow S C)
          (productPPrimeKernel S C hcentral) ≃*
      productPPrimeKernelFixedPoints S C hcentral :=
  (localKernelFixedPointsEquiv S C hcentral).symm.trans
    (localKernelAmbientFixedPointsEquiv S C hcentral)

@[simp]
theorem productAmbientGlaubermanKernelProductToLocalNormalizer_inl_internal
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (a :
      internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral)) :
    productAmbientGlaubermanKernelProductToLocalNormalizer
        S C hcentral (a, 1) =
      a.1 := by
  change
    normalizerProductEquiv S C hcentral (a, 1) = a.1
  rw [show
    normalizerProductEquiv S C hcentral =
      pPrimeKernelFixedPointsProductEquiv
        (productSylow S C)
        (productPPrimeKernel S C hcentral)
        (productPPrimeKernel_isPPrimeGroup S C hcentral)
        (productPPrimeKernel_sup_productSylow_eq_top
          S C hcentral) from rfl]
  rw [pPrimeKernelFixedPointsProductEquiv_apply]
  simp

@[simp]
theorem productAmbientGlaubermanKernelProductToSource_inl
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (a :
      internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral)) :
    productAmbientGlaubermanKernelProductToSource
        S C hcentral (a, 1) =
      (productPPrimeKernel S C hcentral).subtype
        (productAmbientGlaubermanInternalFixedPointToSourceKernel
          S C hcentral a) := by
  change
    (localNormalizer
      (productSylow S C :
        Subgroup (product S C))).subtype
        (normalizerProductEquiv S C hcentral (a, 1)) =
      (productPPrimeKernel S C hcentral).subtype
        (productAmbientGlaubermanInternalFixedPointToSourceKernel
          S C hcentral a)
  have ha :=
    productAmbientGlaubermanKernelProductToLocalNormalizer_inl_internal
      S C hcentral a
  change normalizerProductEquiv S C hcentral (a, 1) = a.1 at ha
  rw [ha]
  rfl

@[simp]
theorem productAmbientGlaubermanKernelProductToLocalNormalizer_inl
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (a :
      internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral)) :
    productAmbientGlaubermanKernelProductToLocalNormalizer
        S C hcentral (a, 1) =
      productAmbientGlaubermanFixedPointsToLocalNormalizer
        S C hcentral
        (productAmbientGlaubermanInternalFixedPointEquiv
          S C hcentral a) := by
  change
    normalizerProductEquiv S C hcentral (a, 1) =
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))).subtype
        ((localKernelAmbientFixedPointsEquiv
          S C hcentral).symm
            (productAmbientGlaubermanInternalFixedPointEquiv
              S C hcentral a))
  have ha :=
    productAmbientGlaubermanKernelProductToLocalNormalizer_inl_internal
      S C hcentral a
  change normalizerProductEquiv S C hcentral (a, 1) = a.1 at ha
  rw [ha]
  change
    a.1 =
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))).subtype
        ((localKernelAmbientFixedPointsEquiv
          S C hcentral).symm
            ((localKernelAmbientFixedPointsEquiv
              S C hcentral)
              ((localKernelFixedPointsEquiv
                S C hcentral).symm a)))
  rw [(localKernelAmbientFixedPointsEquiv
    S C hcentral).symm_apply_apply]
  apply Subtype.ext
  rfl

/-- The honest source Gallagher representation on fixed-point-times-Sylow
coordinates, transported to the canonical source-kernel realization. -/
abbrev ProductAmbientGlaubermanSourceKernelProductFDRep
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    FDRep ℂ
      (ProductAmbientGlaubermanKernelProduct S C hcentral) :=
  transportedExtensionFDRep
    (productAmbientGlaubermanSourceKernelCharacter
      S C hcentral theta).1.1
    (productPPrimeKernel S C hcentral).subtype
    (productAmbientSourceGallagherCharacter
      S C hcentral theta)
    (productAmbientSourceGallagherCharacter_isExtension
      S C hcentral theta)
    (productAmbientGlaubermanKernelProductToSource
      S C hcentral)

/-- The honest normalized-local Gallagher representation on
fixed-point-times-Sylow coordinates, transported to the canonical
fixed-point-kernel realization. -/
abbrev ProductAmbientGlaubermanFixedPointKernelProductFDRep
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    FDRep ℂ
      (ProductAmbientGlaubermanKernelProduct S C hcentral) :=
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
    (productAmbientGlaubermanKernelProductToLocalNormalizer
      S C hcentral)

/-- The product source representation restricts on the Sylow factor to
the previously named honest source representation. -/
theorem productAmbientGlaubermanSourceKernelProductFDRep_inr
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b : internalNormalizerSylow (productSylow S C)) :
    (ProductAmbientGlaubermanSourceKernelProductFDRep
        S C hcentral theta).ρ (1, b) =
      (ProductAmbientGlaubermanSourceKernelSylowFDRep
        S C hcentral theta).ρ b := by
  apply LinearMap.ext
  intro v
  change
    transportedExtensionOperator
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1.1
        (productPPrimeKernel S C hcentral).subtype
        (productAmbientSourceGallagherCharacter
          S C hcentral theta)
        (productAmbientSourceGallagherCharacter_isExtension
          S C hcentral theta)
        (productAmbientGlaubermanKernelProductToSource
          S C hcentral)
        (1, b) v =
      transportedExtensionOperator
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1.1
        (productPPrimeKernel S C hcentral).subtype
        (productAmbientSourceGallagherCharacter
          S C hcentral theta)
        (productAmbientSourceGallagherCharacter_isExtension
          S C hcentral theta)
        (productAmbientGlaubermanSourceSylowInclusion S C)
        b v
  rw [transportedExtensionOperator_apply,
    transportedExtensionOperator_apply,
    productAmbientGlaubermanKernelProductToSource_inr]

/-- The product target representation restricts on the Sylow factor to
the previously named honest target representation. -/
theorem productAmbientGlaubermanFixedPointKernelProductFDRep_inr
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b : internalNormalizerSylow (productSylow S C)) :
    (ProductAmbientGlaubermanFixedPointKernelProductFDRep
        S C hcentral g theta).ρ (1, b) =
      (ProductAmbientGlaubermanFixedPointKernelSylowFDRep
        S C hcentral g theta).ρ b := by
  apply LinearMap.ext
  intro w
  change
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
        (productAmbientGlaubermanKernelProductToLocalNormalizer
          S C hcentral)
        (1, b) w =
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
        b w
  rw [transportedExtensionOperator_apply,
    transportedExtensionOperator_apply,
    productAmbientGlaubermanKernelProductToLocalNormalizer_inr]

/-- The internal and ambient descriptions of a fixed point give the same
element of the source kernel. -/
theorem productAmbientGlaubermanInternalFixedPoint_sourceKernel_eq
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (a :
      internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral)) :
    productAmbientGlaubermanInternalFixedPointToSourceKernel
        S C hcentral a =
      coprimeFixedPointsInclusion
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))
        (productAmbientGlaubermanInternalFixedPointEquiv
          S C hcentral a) := by
  apply Subtype.ext
  rfl

/-- On the fixed-point factor, the honest source product
representation is the original source-kernel representation. -/
theorem productAmbientGlaubermanSourceKernelProductFDRep_inl
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (a :
      internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral)) :
    (ProductAmbientGlaubermanSourceKernelProductFDRep
        S C hcentral theta).ρ (a, 1) =
      realizationAction
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1.1
        (productAmbientGlaubermanInternalFixedPointToSourceKernel
          S C hcentral a) := by
  exact congrArg LinearEquiv.toLinearMap
    (transportedExtensionOperator_eq_realizationAction_of_eq
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
      (j :=
        productAmbientGlaubermanKernelProductToSource
          S C hcentral)
      (a, 1)
      (productAmbientGlaubermanInternalFixedPointToSourceKernel
        S C hcentral a)
      (productAmbientGlaubermanKernelProductToSource_inl
        S C hcentral a))

/-- On the fixed-point factor, the honest target product
representation is the original Glauberman fixed-point representation. -/
theorem productAmbientGlaubermanFixedPointKernelProductFDRep_inl
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (a :
      internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral)) :
    (ProductAmbientGlaubermanFixedPointKernelProductFDRep
        S C hcentral g theta).ρ (a, 1) =
      realizationAction
        (g.characterEquiv
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).1
        (productAmbientGlaubermanInternalFixedPointEquiv
          S C hcentral a) := by
  exact congrArg LinearEquiv.toLinearMap
    (transportedExtensionOperator_eq_realizationAction_of_eq
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
      (j :=
        productAmbientGlaubermanKernelProductToLocalNormalizer
          S C hcentral)
      (a, 1)
      (productAmbientGlaubermanInternalFixedPointEquiv
        S C hcentral a)
      (productAmbientGlaubermanKernelProductToLocalNormalizer_inl
        S C hcentral a))

/-- The honest conjugation action on all linear maps between the two
kernel realizations in fixed-point-times-Sylow coordinates. -/
abbrev productAmbientGlaubermanKernelProductLinHomRepresentation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :=
  Representation.linHom
    (ProductAmbientGlaubermanFixedPointKernelProductFDRep
      S C hcentral g theta).ρ
    (ProductAmbientGlaubermanSourceKernelProductFDRep
      S C hcentral theta).ρ

/-- Unbundled fixed-vector criterion for the honest `linHom`
representation. -/
theorem honestLinHom_fixed_iff_comm
    {H V W : Type}
    [Group H]
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (rho : Representation ℂ H V)
    (sigma : Representation ℂ H W)
    (f : V →ₗ[ℂ] W)
    (h : H) :
    Representation.linHom rho sigma h f = f ↔
      f.comp (rho h) = (sigma h).comp f := by
  dsimp [Representation.linHom]
  constructor
  · intro hf
    apply LinearMap.ext
    intro v
    have hv :=
      LinearMap.congr_fun hf (rho h v)
    simpa only [LinearMap.comp_apply,
      Representation.inv_self_apply] using hv.symm
  · intro hf
    apply LinearMap.ext
    intro v
    have hv :=
      LinearMap.congr_fun hf (rho h⁻¹ v)
    simpa only [LinearMap.comp_apply,
      Representation.self_inv_apply] using hv.symm

/-- A kernel intertwiner commutes with the fixed-point factor of the
honest product realizations. -/
theorem productAmbientGlaubermanKernelIntertwiningMap_fixedPoint_comm
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (f :
      ProductAmbientGlaubermanKernelMultiplicitySpace
        S C hcentral g theta)
    (a :
      internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral)) :
    (f : _ →ₗ[ℂ] _).comp
        ((ProductAmbientGlaubermanFixedPointKernelProductFDRep
          S C hcentral g theta).ρ (a, 1)) =
      ((ProductAmbientGlaubermanSourceKernelProductFDRep
        S C hcentral theta).ρ (a, 1)).comp
        (f : _ →ₗ[ℂ] _) := by
  rw [
    productAmbientGlaubermanFixedPointKernelProductFDRep_inl,
    productAmbientGlaubermanSourceKernelProductFDRep_inl,
    productAmbientGlaubermanInternalFixedPoint_sourceKernel_eq]
  exact
    f.isIntertwining'
      (productAmbientGlaubermanInternalFixedPointEquiv
        S C hcentral a)

/-- The defining eigenvalue of the canonical selected summand cancels
the canonical comparison scalar, so its underlying map is fixed by the
honest Sylow `linHom` action. -/
theorem productAmbientGlaubermanCanonicalSelectedSummand_sylow_fixed
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
    (b : internalNormalizerSylow (productSylow S C)) :
    Representation.linHom
        (ProductAmbientGlaubermanFixedPointKernelSylowFDRep
          S C hcentral g theta).ρ
        (ProductAmbientGlaubermanSourceKernelSylowFDRep
          S C hcentral theta).ρ b
        (z.1 : _ →ₗ[ℂ] _) =
      (z.1 : _ →ₗ[ℂ] _) := by
  have hselectedRaw :=
    congrArg
      (fun f :
        ProductAmbientGlaubermanKernelMultiplicitySpace
          S C hcentral g theta ↦ f.toLinearMap)
      (z.2 b)
  have hcanonical :=
    productAmbientGlaubermanKernelMultiplicityProjective_operator_eq_selected_smul_linHom
      S C hcentral hgenerate g theta b z.1
  have hscaled :
      (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta b : ℂ) •
          Representation.linHom
            (ProductAmbientGlaubermanFixedPointKernelSylowFDRep
              S C hcentral g theta).ρ
            (ProductAmbientGlaubermanSourceKernelSylowFDRep
              S C hcentral theta).ρ b
            (z.1 : _ →ₗ[ℂ] _) =
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta b : ℂ) •
          (z.1 : _ →ₗ[ℂ] _) :=
    hcanonical.symm.trans hselectedRaw
  apply
    smul_right_injective
      (_ →ₗ[ℂ] _)
      (productAmbientGlaubermanCanonicalSelectedSylowScalar
        S C hcentral hgenerate g theta b).ne_zero
  exact hscaled

/-- Vectors in the canonical selected summand commute with the Sylow
factor of the honest product realizations. -/
theorem productAmbientGlaubermanCanonicalSelectedSummand_sylow_comm
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
    (b : internalNormalizerSylow (productSylow S C)) :
    (z.1 : _ →ₗ[ℂ] _).comp
        ((ProductAmbientGlaubermanFixedPointKernelProductFDRep
          S C hcentral g theta).ρ (1, b)) =
      ((ProductAmbientGlaubermanSourceKernelProductFDRep
        S C hcentral theta).ρ (1, b)).comp
        (z.1 : _ →ₗ[ℂ] _) := by
  rw [
    productAmbientGlaubermanFixedPointKernelProductFDRep_inr,
    productAmbientGlaubermanSourceKernelProductFDRep_inr]
  exact
    (honestLinHom_fixed_iff_comm
      (ProductAmbientGlaubermanFixedPointKernelSylowFDRep
        S C hcentral g theta).ρ
      (ProductAmbientGlaubermanSourceKernelSylowFDRep
        S C hcentral theta).ρ
      (z.1 : _ →ₗ[ℂ] _) b).1
        (productAmbientGlaubermanCanonicalSelectedSummand_sylow_fixed
          S C hcentral hgenerate g theta z b)

/-- Every vector in the canonically selected Sylow summand is invariant
under the honest fixed-point-times-Sylow `linHom` action. -/
theorem productAmbientGlaubermanCanonicalSelectedSummand_honest_invariant
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
    (d :
      ProductAmbientGlaubermanKernelProduct
        S C hcentral) :
    productAmbientGlaubermanKernelProductLinHomRepresentation
        S C hcentral g theta d
        (z.1 : _ →ₗ[ℂ] _) =
      (z.1 : _ →ₗ[ℂ] _) := by
  let a := d.1
  let b := d.2
  have haComm :=
    productAmbientGlaubermanKernelIntertwiningMap_fixedPoint_comm
      S C hcentral g theta z.1 a
  have hbComm :=
    productAmbientGlaubermanCanonicalSelectedSummand_sylow_comm
      S C hcentral hgenerate g theta z b
  apply
    (honestLinHom_fixed_iff_comm
      (ProductAmbientGlaubermanFixedPointKernelProductFDRep
        S C hcentral g theta).ρ
      (ProductAmbientGlaubermanSourceKernelProductFDRep
        S C hcentral theta).ρ
      (z.1 : _ →ₗ[ℂ] _) d).2
  apply LinearMap.ext
  intro v
  have hd :
      d =
        (a, (1 : internalNormalizerSylow
          (productSylow S C))) * (1, b) := by
    apply Prod.ext <;> simp [a, b]
  rw [hd, map_mul, map_mul]
  change
    z.1
        ((ProductAmbientGlaubermanFixedPointKernelProductFDRep
          S C hcentral g theta).ρ (a, 1)
          ((ProductAmbientGlaubermanFixedPointKernelProductFDRep
            S C hcentral g theta).ρ (1, b) v)) =
      (ProductAmbientGlaubermanSourceKernelProductFDRep
          S C hcentral theta).ρ (a, 1)
        ((ProductAmbientGlaubermanSourceKernelProductFDRep
          S C hcentral theta).ρ (1, b) (z.1 v))
  exact
    (LinearMap.congr_fun haComm
      ((ProductAmbientGlaubermanFixedPointKernelProductFDRep
        S C hcentral g theta).ρ (1, b) v)).trans
      (congrArg
        ((ProductAmbientGlaubermanSourceKernelProductFDRep
          S C hcentral theta).ρ (a, 1))
        (LinearMap.congr_fun hbComm v))

/-- An invariant map for the honest product representations intertwines
the two original kernel representations on the fixed-point subgroup. -/
theorem productAmbientGlaubermanHonestInvariant_fixedPoint_comm
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (z :
      (productAmbientGlaubermanKernelProductLinHomRepresentation
        S C hcentral g theta).invariants)
    (x : productPPrimeKernelFixedPoints S C hcentral) :
    (z.1 :
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1.realization →ₗ[ℂ]
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1.1.realization).comp
        (realizationAction
          (g.characterEquiv
            (productAmbientGlaubermanSourceKernelCharacter
              S C hcentral theta)).1 x).toLinearMap =
      (realizationAction
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1.1
        (coprimeFixedPointsInclusion
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)) x)).toLinearMap.comp
        (z.1 :
          (g.characterEquiv
            (productAmbientGlaubermanSourceKernelCharacter
              S C hcentral theta)).1.realization →ₗ[ℂ]
            (productAmbientGlaubermanSourceKernelCharacter
              S C hcentral theta).1.1.realization) := by
  let a :=
    (productAmbientGlaubermanInternalFixedPointEquiv
      S C hcentral).symm x
  have hz :=
    (honestLinHom_fixed_iff_comm
      (ProductAmbientGlaubermanFixedPointKernelProductFDRep
        S C hcentral g theta).ρ
      (ProductAmbientGlaubermanSourceKernelProductFDRep
        S C hcentral theta).ρ z.1
      ((a, (1 : internalNormalizerSylow
        (productSylow S C))) :
        ProductAmbientGlaubermanKernelProduct
          S C hcentral)).1
      (z.2 (a, 1))
  rw [
    productAmbientGlaubermanFixedPointKernelProductFDRep_inl,
    productAmbientGlaubermanSourceKernelProductFDRep_inl,
    productAmbientGlaubermanInternalFixedPoint_sourceKernel_eq] at hz
  simpa only [a,
    MulEquiv.apply_symm_apply] using hz

/-- Regard an invariant honest product map as the corresponding kernel
Glauberman intertwining map. -/
def productAmbientGlaubermanHonestInvariantToKernelMultiplicitySpace
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (z :
      (productAmbientGlaubermanKernelProductLinHomRepresentation
        S C hcentral g theta).invariants) :
    ProductAmbientGlaubermanKernelMultiplicitySpace
      S C hcentral g theta where
  toLinearMap := z.1
  isIntertwining' :=
    productAmbientGlaubermanHonestInvariant_fixedPoint_comm
      S C hcentral g theta z

/-- An invariant of the honest product `linHom` representation is fixed
by the honest Sylow `linHom` representation after restriction to the
second direct factor. -/
theorem productAmbientGlaubermanHonestInvariant_sylow_fixed
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (z :
      (productAmbientGlaubermanKernelProductLinHomRepresentation
        S C hcentral g theta).invariants)
    (b : internalNormalizerSylow (productSylow S C)) :
    Representation.linHom
        (ProductAmbientGlaubermanFixedPointKernelSylowFDRep
          S C hcentral g theta).ρ
        (ProductAmbientGlaubermanSourceKernelSylowFDRep
          S C hcentral theta).ρ b z.1 =
      z.1 := by
  apply
    (honestLinHom_fixed_iff_comm
      (ProductAmbientGlaubermanFixedPointKernelSylowFDRep
        S C hcentral g theta).ρ
      (ProductAmbientGlaubermanSourceKernelSylowFDRep
        S C hcentral theta).ρ z.1 b).2
  have hcomm :=
    (honestLinHom_fixed_iff_comm
      (ProductAmbientGlaubermanFixedPointKernelProductFDRep
        S C hcentral g theta).ρ
      (ProductAmbientGlaubermanSourceKernelProductFDRep
        S C hcentral theta).ρ z.1
      ((1, b) :
        ProductAmbientGlaubermanKernelProduct
          S C hcentral)).1
      (z.2 (1, b))
  rw [
    productAmbientGlaubermanFixedPointKernelProductFDRep_inr,
    productAmbientGlaubermanSourceKernelProductFDRep_inr] at hcomm
  exact hcomm

/-- The kernel intertwiner recovered from an honest product invariant lies
in the canonically selected Sylow summand. -/
theorem productAmbientGlaubermanHonestInvariant_mem_selectedSummand
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (z :
      (productAmbientGlaubermanKernelProductLinHomRepresentation
        S C hcentral g theta).invariants) :
    productAmbientGlaubermanHonestInvariantToKernelMultiplicitySpace
        S C hcentral g theta z ∈
      ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta) := by
  intro b
  apply Representation.IntertwiningMap.ext
  exact
    (productAmbientGlaubermanKernelMultiplicityProjective_operator_eq_selected_smul_linHom
      S C hcentral hgenerate g theta b
      (productAmbientGlaubermanHonestInvariantToKernelMultiplicitySpace
        S C hcentral g theta z)).trans
      (congrArg
        (fun f ↦
          (productAmbientGlaubermanCanonicalSelectedSylowScalar
            S C hcentral hgenerate g theta b : ℂ) • f)
        (productAmbientGlaubermanHonestInvariant_sylow_fixed
          S C hcentral g theta z b))

/-- The canonical selected Sylow summand is exactly the invariant
subspace of the honest fixed-point-times-Sylow `linHom` representation.
Both directions preserve the underlying linear map literally. -/
def productAmbientGlaubermanCanonicalSelectedSummandEquivHonestInvariants
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
      (productAmbientGlaubermanKernelProductLinHomRepresentation
        S C hcentral g theta).invariants where
  toFun z :=
    ⟨(z.1 : _ →ₗ[ℂ] _),
      by
        intro d
        exact
          productAmbientGlaubermanCanonicalSelectedSummand_honest_invariant
            S C hcentral hgenerate g theta z d⟩
  invFun z :=
    ⟨productAmbientGlaubermanHonestInvariantToKernelMultiplicitySpace
        S C hcentral g theta z,
      productAmbientGlaubermanHonestInvariant_mem_selectedSummand
        S C hcentral hgenerate g theta z⟩
  left_inv z := by
    apply Subtype.ext
    apply Representation.IntertwiningMap.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Categorical form of the canonical selected-summand identification.
The second step is mathlib's canonical equivalence from invariant
`linHom` vectors to morphisms of finite-dimensional representations. -/
def productAmbientGlaubermanCanonicalSelectedSummandEquivFDRepHom
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
      (ProductAmbientGlaubermanFixedPointKernelProductFDRep
          S C hcentral g theta ⟶
        ProductAmbientGlaubermanSourceKernelProductFDRep
          S C hcentral theta) :=
  (productAmbientGlaubermanCanonicalSelectedSummandEquivHonestInvariants
    S C hcentral hgenerate g theta).trans
      (Representation.linHom.invariantsEquivFDRepHom
        (ProductAmbientGlaubermanFixedPointKernelProductFDRep
          S C hcentral g theta)
        (ProductAmbientGlaubermanSourceKernelProductFDRep
          S C hcentral theta))

/-- The categorical selected-summand equivalence preserves the
underlying linear map literally. -/
@[simp]
theorem productAmbientGlaubermanCanonicalSelectedSummandEquivFDRepHom_apply_hom
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
    (productAmbientGlaubermanCanonicalSelectedSummandEquivFDRepHom
        S C hcentral hgenerate g theta z).hom.hom.hom =
      (z.1 : _ →ₗ[ℂ] _) :=
  rfl

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
