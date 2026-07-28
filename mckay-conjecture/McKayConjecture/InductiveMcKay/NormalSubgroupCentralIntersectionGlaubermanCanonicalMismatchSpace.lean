/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalCharacterComparison

/-!
# The canonical Glauberman summand as the final mismatch space

This file transports the honest fixed-point-times-Sylow Hom-space into
the normal-character Hom-space defining the final projective
multiplicity mismatch.
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

noncomputable local instance productCanonicalMismatchAmbientFintype :
    Fintype X :=
  Fintype.ofFinite X

noncomputable local instance productCanonicalMismatchSourceFintype :
    Fintype (product S C) :=
  Fintype.ofFinite (product S C)

noncomputable local instance productCanonicalMismatchTargetFintype :
    Fintype (internalProductNormalizer S C) :=
  Fintype.ofFinite (internalProductNormalizer S C)

/-- In product coordinates, the normal-subgroup map in the matched
inertia restriction is literally the inclusion of the local normalizer
in the source product group. -/
theorem productAmbientGlauberman_normalHom_productEquiv
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
    (inertiaNormalCopyEquiv (product S C) theta.1).toMonoidHom.comp
        ((ProjectiveMultiplicityMismatch.normalHom
          (productAmbientGlaubermanInertiaRestrictionGroupData
            S C hcentral hgenerate g theta)).comp
          (productAmbientGlaubermanRightNormalCopyProductEquiv
            S C hcentral hgenerate g theta).toMonoidHom) =
      productAmbientGlaubermanKernelProductToSource
        S C hcentral := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  apply MonoidHom.ext
  intro d
  apply Subtype.ext
  rfl

/-- Pulling the final right normal character back through the canonical
product coordinates gives exactly the normalized local Gallagher
character pulled back through the local product decomposition. -/
theorem productAmbientGlauberman_rightNormalCharacter_comap_productEquiv
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
    (productAmbientGlaubermanRightInertiaTriple
        S C hcentral hgenerate g theta).character.comap
        (productAmbientGlaubermanRightNormalCopyProductEquiv
          S C hcentral hgenerate g theta) =
      (productAmbientNormalizedLocalGallagherCharacter
        S C hcentral g theta).comap
          (normalizerProductEquiv S C hcentral) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  apply IrreducibleCharacter.ext
  funext d
  rw [productAmbientNormalizedLocalGallagherCharacter_eq
    S C hcentral g theta]
  rfl

/-- The honest target product representation is the chosen realization
of the final right normal character, pulled back to product
coordinates. -/
def productAmbientGlaubermanFixedPointKernelProductFDRepIsoRightNormalCharacter
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
    ProductAmbientGlaubermanFixedPointKernelProductFDRep
        S C hcentral g theta ≅
      ((productAmbientGlaubermanRightInertiaTriple
          S C hcentral hgenerate g theta).character.comap
        (productAmbientGlaubermanRightNormalCopyProductEquiv
          S C hcentral hgenerate g theta)).realization := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  rw [
    productAmbientGlauberman_rightNormalCharacter_comap_productEquiv
      S C hcentral hgenerate g theta]
  exact
    (transportedExtensionFDRepIso
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
        S C hcentral)).trans
      (IrreducibleCharacter.comapRealizationIso
        (normalizerProductEquiv S C hcentral)
        (productAmbientNormalizedLocalGallagherCharacter
          S C hcentral g theta)).symm

/-- Direct form of
`productAmbientGlaubermanFixedPointKernelProductFDRepIsoRightNormalCharacter`:
the target is the literal restriction of the final right normal-character
realization, rather than the separately chosen realization of its comap. -/
def productAmbientGlaubermanFixedPointKernelProductFDRepIsoRightNormalRestriction
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
    ProductAmbientGlaubermanFixedPointKernelProductFDRep
        S C hcentral g theta ≅
      FDRep.res
        (productAmbientGlaubermanRightNormalCopyProductEquiv
          S C hcentral hgenerate g theta).toMonoidHom
        (productAmbientGlaubermanRightInertiaTriple
          S C hcentral hgenerate g theta).character.realization := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    (productAmbientGlaubermanFixedPointKernelProductFDRepIsoRightNormalCharacter
      S C hcentral hgenerate g theta).trans
      (IrreducibleCharacter.comapRealizationIso
        (productAmbientGlaubermanRightNormalCopyProductEquiv
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanRightInertiaTriple
          S C hcentral hgenerate g theta).character)

/-- The honest source product representation is the restriction of the
chosen final left normal-character realization along the matched normal
map, after pulling the right normal copy back to product coordinates. -/
def productAmbientGlaubermanSourceKernelProductFDRepIsoLeftNormalRestriction
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
  let phi :=
    (ProjectiveMultiplicityMismatch.normalHom
      (productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta)).comp
      (productAmbientGlaubermanRightNormalCopyProductEquiv
        S C hcentral hgenerate g theta).toMonoidHom
  let eCopy :=
    inertiaNormalCopyEquiv (product S C) theta.1
  let j :=
    productAmbientGlaubermanKernelProductToSource
      S C hcentral
  let iTransport :
      ProductAmbientGlaubermanSourceKernelProductFDRep
          S C hcentral theta ≅
        FDRep.res j
          (productAmbientSourceGallagherCharacter
            S C hcentral theta).realization :=
    transportedExtensionFDRepIso
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1
      (productPPrimeKernel S C hcentral).subtype
      (productAmbientSourceGallagherCharacter
        S C hcentral theta)
      (productAmbientSourceGallagherCharacter_isExtension
        S C hcentral theta)
      j
  rw [productAmbientSourceGallagherCharacter_eq
    S C hcentral theta] at iTransport
  let iCopy :=
    inertiaCopyRealizationIso
      (product S C) theta.1
  let riCopy :=
    (FDRep.resFunctor phi).mapIso iCopy
  let iComp :=
    (Action.resComp
      (FGModuleCat ℂ) phi eCopy.toMonoidHom).app
        theta.1.realization
  have hmap :
      eCopy.toMonoidHom.comp phi = j := by
    exact
      productAmbientGlauberman_normalHom_productEquiv
        S C hcentral hgenerate g theta
  let iCongr :=
    (Action.resCongr
      (FGModuleCat ℂ) hmap).app theta.1.realization
  exact
    iTransport.trans
      (riCopy.trans (iComp.trans iCongr)).symm

/-- Simultaneous replacement of the source and target of an `FDRep`
morphism by isomorphic objects. -/
def fdRepHomCongr
    {H : Type} [Group H]
    {V V' W W' : FDRep ℂ H}
    (iV : V ≅ V') (iW : W ≅ W') :
    (V ⟶ W) ≃ₗ[ℂ] (V' ⟶ W') where
  toFun f :=
    iV.inv ≫ f ≫ iW.hom
  invFun f :=
    iV.hom ≫ f ≫ iW.inv
  left_inv f := by simp
  right_inv f := by simp
  map_add' f h := by simp
  map_smul' c f := by simp

@[simp]
theorem fdRepHomCongr_apply
    {H : Type} [Group H]
    {V V' W W' : FDRep ℂ H}
    (iV : V ≅ V') (iW : W ≅ W')
    (f : V ⟶ W) :
    fdRepHomCongr iV iW f =
      iV.inv ≫ f ≫ iW.hom :=
  rfl

@[simp]
theorem fdRepHomCongr_symm_apply
    {H : Type} [Group H]
    {V V' W W' : FDRep ℂ H}
    (iV : V ≅ V') (iW : W ≅ W')
    (f : V' ⟶ W') :
    (fdRepHomCongr iV iW).symm f =
      iV.hom ≫ f ≫ iW.inv :=
  rfl

/-- Restricting both representations along a group equivalence does not
change their morphism space.  This categorical form deliberately preserves
the underlying linear map. -/
def fdRepHomRestrictMulEquiv
    {H H' : Type} [Group H] [Group H']
    (e : H' ≃* H)
    (V W : FDRep ℂ H) :
    (FDRep.res e.toMonoidHom V ⟶
        FDRep.res e.toMonoidHom W) ≃ₗ[ℂ]
      (V ⟶ W) :=
  (FDRep.homIntertwiningEquiv
      (FDRep.res e.toMonoidHom V)
      (FDRep.res e.toMonoidHom W)).trans
    ((Representation.intertwiningMapComapEquiv
      e V.ρ W.ρ).symm.trans
        (FDRep.homIntertwiningEquiv V W).symm)

/-- `fdRepHomRestrictMulEquiv` preserves the underlying linear map
literally. -/
@[simp]
theorem fdRepHomRestrictMulEquiv_apply_hom
    {H H' : Type} [Group H] [Group H']
    (e : H' ≃* H)
    (V W : FDRep ℂ H)
    (f :
      FDRep.res e.toMonoidHom V ⟶
        FDRep.res e.toMonoidHom W) :
    (fdRepHomRestrictMulEquiv e V W f).hom.hom.hom =
      f.hom.hom.hom :=
  rfl

/-- The canonically selected kernel summand is linearly equivalent to
the final projective multiplicity mismatch space.  This equivalence is
constructed from the honest product actions and the actual normal
characters; it has no representation-identification premise. -/
def productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpace
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
    productAmbientGlaubermanSourceKernelProductFDRepIsoLeftNormalRestriction
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
identification.  In particular, no arbitrary isomorphism between an
associated restriction and its character realization occurs in this
formula. -/
@[simp]
theorem productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpace_apply
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
    productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpace
        S C hcentral hgenerate g theta z w =
      (productAmbientGlaubermanSourceKernelProductFDRepIsoLeftNormalRestriction
        S C hcentral hgenerate g theta).hom
        (z.1
          ((productAmbientGlaubermanFixedPointKernelProductFDRepIsoRightNormalRestriction
            S C hcentral hgenerate g theta).inv w)) :=
  rfl

/-- Dimension form of the premise-free selected-summand/mismatch-space
identification. -/
theorem productAmbientGlaubermanCanonicalSelectedSummand_finrank_eq_mismatch
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    Module.finrank ℂ
        (ProductAmbientGlaubermanKernelSylowScalarSubspace
          S C hcentral hgenerate g theta
          (productAmbientGlaubermanCanonicalSelectedSylowScalar
            S C hcentral hgenerate g theta)) =
      Module.finrank ℂ
        (ProductAmbientGlaubermanMultiplicityMismatchSpace
          S C hcentral hgenerate g theta) :=
  (productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpace
    S C hcentral hgenerate g theta).finrank_eq

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
