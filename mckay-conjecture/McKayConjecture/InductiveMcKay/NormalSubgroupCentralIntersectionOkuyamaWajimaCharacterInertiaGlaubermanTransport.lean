/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanActionTransport
import McKayConjecture.Character.GlaubermanStrongRealization
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionOkuyamaWajimaCharacterInertiaCount

/-!
# Glauberman transport inside the exact character inertia

This file transports the product Glauberman correspondence from `D = CS`
to the canonical copies of its `q'`-kernel and Sylow subgroup inside the
exact character inertia group `Γ_theta = I_X(theta)`.

The construction goes through the strong action-level correspondence.
Both copying equivalences are identity on the underlying elements of `X`,
so they intertwine the two conjugation actions.  The action transport API
then gives a correspondence on the copied subgroups without identifying
the old and new subgroup types.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CliffordEquivalence
open CliffordCorrespondence
open ComplementReduction
open GroupTheory
open CharacterTriple
open CharacterTriple.AssociatedExistence

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The canonical equivalence from the original product Sylow subgroup
to its copy in the exact character inertia group. -/
def productAmbientGlaubermanLeftOWSylowEquivOriginal
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    (productSylow S C : Subgroup (product S C)) ≃*
      (ProductAmbientGlaubermanLeftOWSylow
        S C hgenerate theta :
        Subgroup
          (ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta)) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    (inertiaSubgroupCopyEquiv
        (product S C) theta.1
        (productSylow S C : Subgroup (product S C))).trans
      (MulEquiv.subgroupCongr
        (productAmbientGlaubermanLeftInertia_productSylowCopy_eq
          S C hgenerate theta))

@[simp]
theorem productAmbientGlaubermanLeftOWSylowEquivOriginal_apply_coe
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (s : (productSylow S C : Subgroup (product S C))) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    ((productAmbientGlaubermanLeftOWSylowEquivOriginal
        S C hgenerate theta s :
      ProductAmbientGlaubermanLeftOWSylow
        S C hgenerate theta) :
      ProductAmbientGlaubermanLeftInertiaGroup
        S C hgenerate theta) =
      inertiaInclusion (product S C) theta.1 s := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  change
    ((inertiaSubgroupCopyEquiv
        (product S C) theta.1
        (productSylow S C : Subgroup (product S C)) s :
      inertiaSubgroupCopy
        (product S C) theta.1
        (productSylow S C : Subgroup (product S C))) :
      ProductAmbientGlaubermanLeftInertiaGroup
        S C hgenerate theta) =
      inertiaInclusion (product S C) theta.1 s
  rw [inertiaSubgroupCopyEquiv_apply_coe]

/-- The canonical equivalence from the original `q'`-kernel to its copy
in the exact character inertia group. -/
def productAmbientGlaubermanLeftOWKernelEquivOriginal
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    productPPrimeKernel S C hcentral ≃*
      ProductAmbientGlaubermanLeftOWKernel
        S C hcentral hgenerate theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    inertiaSubgroupCopyEquiv
      (product S C) theta.1
      (productPPrimeKernel S C hcentral)

@[simp]
theorem productAmbientGlaubermanLeftOWKernelEquivOriginal_apply_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (r : productPPrimeKernel S C hcentral) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    ((productAmbientGlaubermanLeftOWKernelEquivOriginal
        S C hcentral hgenerate theta r :
      ProductAmbientGlaubermanLeftOWKernel
        S C hcentral hgenerate theta) :
      ProductAmbientGlaubermanLeftInertiaGroup
        S C hgenerate theta) =
      inertiaInclusion (product S C) theta.1 r := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    inertiaSubgroupCopyEquiv_apply_coe
      (product S C) theta.1
      (productPPrimeKernel S C hcentral) r

/-- The two copying equivalences intertwine conjugation. -/
theorem productAmbientGlaubermanLeftOWEquivOriginal_smul
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (s : (productSylow S C : Subgroup (product S C)))
    (r : productPPrimeKernel S C hcentral) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
      MulDistribMulAction
        (productSylow S C : Subgroup (product S C))
        (productPPrimeKernel S C hcentral) :=
      subgroupConjugationMulDistribMulAction
        (productPPrimeKernel S C hcentral)
        (productSylow S C : Subgroup (product S C))
    letI :
      MulDistribMulAction
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta))
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta) :=
      subgroupConjugationMulDistribMulAction
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta))
    productAmbientGlaubermanLeftOWKernelEquivOriginal
          S C hcentral hgenerate theta (s • r) =
      productAmbientGlaubermanLeftOWSylowEquivOriginal
          S C hgenerate theta s •
        productAmbientGlaubermanLeftOWKernelEquivOriginal
          S C hcentral hgenerate theta r := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      MulDistribMulAction
        (productSylow S C : Subgroup (product S C))
        (productPPrimeKernel S C hcentral) :=
    subgroupConjugationMulDistribMulAction
      (productPPrimeKernel S C hcentral)
      (productSylow S C : Subgroup (product S C))
  letI :
      MulDistribMulAction
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta))
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta) :=
    subgroupConjugationMulDistribMulAction
      (ProductAmbientGlaubermanLeftOWKernel
        S C hcentral hgenerate theta)
      (ProductAmbientGlaubermanLeftOWSylow
        S C hgenerate theta :
        Subgroup
          (ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta))
  apply Subtype.ext
  calc
    ((productAmbientGlaubermanLeftOWKernelEquivOriginal
        S C hcentral hgenerate theta (s • r) :
      ProductAmbientGlaubermanLeftOWKernel
        S C hcentral hgenerate theta) :
      ProductAmbientGlaubermanLeftInertiaGroup
        S C hgenerate theta) =
        inertiaInclusion (product S C) theta.1
          ((s • r :
            productPPrimeKernel S C hcentral) :
            product S C) :=
      productAmbientGlaubermanLeftOWKernelEquivOriginal_apply_coe
        S C hcentral hgenerate theta (s • r)
    _ =
        inertiaInclusion (product S C) theta.1 s *
          inertiaInclusion (product S C) theta.1 r *
          (inertiaInclusion (product S C) theta.1 s)⁻¹ := by
      simp only [
        subgroupConjugationAction_smul_coe,
        map_mul, map_inv]
    _ =
        (productAmbientGlaubermanLeftOWSylowEquivOriginal
            S C hgenerate theta s :
          ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta) *
          (productAmbientGlaubermanLeftOWKernelEquivOriginal
            S C hcentral hgenerate theta r :
          ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta) *
          (productAmbientGlaubermanLeftOWSylowEquivOriginal
            S C hgenerate theta s :
          ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta)⁻¹ := by
      rw [
        productAmbientGlaubermanLeftOWSylowEquivOriginal_apply_coe,
        productAmbientGlaubermanLeftOWKernelEquivOriginal_apply_coe]
    _ =
        ((productAmbientGlaubermanLeftOWSylowEquivOriginal
            S C hgenerate theta s •
          productAmbientGlaubermanLeftOWKernelEquivOriginal
            S C hcentral hgenerate theta r :
          ProductAmbientGlaubermanLeftOWKernel
            S C hcentral hgenerate theta) :
          ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta) := by
      rfl

/-- The induced equivalence from the original fixed-point kernel to the
fixed-point subgroup of the copied action. -/
def productAmbientGlaubermanLeftOWFixedPointsEquivOriginal
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    coprimeFixedPoints
        (productPPrimeKernel S C hcentral)
        (productSylow S C : Subgroup (product S C)) ≃*
      coprimeFixedPoints
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      MulDistribMulAction
        (productSylow S C : Subgroup (product S C))
        (productPPrimeKernel S C hcentral) :=
    subgroupConjugationMulDistribMulAction
      (productPPrimeKernel S C hcentral)
      (productSylow S C : Subgroup (product S C))
  letI :
      MulDistribMulAction
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta))
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta) :=
    subgroupConjugationMulDistribMulAction
      (ProductAmbientGlaubermanLeftOWKernel
        S C hcentral hgenerate theta)
      (ProductAmbientGlaubermanLeftOWSylow
        S C hgenerate theta :
        Subgroup
          (ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta))
  exact
    (subgroupConjugationFixedPointsEquiv
      (productPPrimeKernel S C hcentral)
      (productSylow S C : Subgroup (product S C))).symm |>.trans
      ((actionFixedPointsEquivOfEquivariant
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta))
        (productSylow S C : Subgroup (product S C))
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (productPPrimeKernel S C hcentral)
        (productAmbientGlaubermanLeftOWSylowEquivOriginal
          S C hgenerate theta)
        (productAmbientGlaubermanLeftOWKernelEquivOriginal
          S C hcentral hgenerate theta)
        (productAmbientGlaubermanLeftOWEquivOriginal_smul
          S C hcentral hgenerate theta)).trans
        (subgroupConjugationFixedPointsEquiv
          (ProductAmbientGlaubermanLeftOWKernel
            S C hcentral hgenerate theta)
          (ProductAmbientGlaubermanLeftOWSylow
            S C hgenerate theta :
            Subgroup
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta))))

@[simp]
theorem
    productAmbientGlaubermanLeftOWFixedPointsEquivOriginal_apply_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (x :
      coprimeFixedPoints
        (productPPrimeKernel S C hcentral)
        (productSylow S C : Subgroup (product S C))) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    ((productAmbientGlaubermanLeftOWFixedPointsEquivOriginal
        S C hcentral hgenerate theta x :
      coprimeFixedPoints
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta))) :
      ProductAmbientGlaubermanLeftInertiaGroup
        S C hgenerate theta) =
      inertiaInclusion (product S C) theta.1 x := by
  rfl

/-- The kernel and fixed-point copying equivalences commute with the two
fixed-point inclusions. -/
theorem
    productAmbientGlaubermanLeftOWFixedPointsEquivOriginal_inclusion_commutes
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    (productAmbientGlaubermanLeftOWKernelEquivOriginal
        S C hcentral hgenerate theta).toMonoidHom.comp
        (coprimeFixedPointsInclusion
          (productPPrimeKernel S C hcentral)
          (productSylow S C : Subgroup (product S C))) =
      (coprimeFixedPointsInclusion
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta))).comp
        (productAmbientGlaubermanLeftOWFixedPointsEquivOriginal
          S C hcentral hgenerate theta).toMonoidHom := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  exact
    productAmbientGlaubermanLeftOWFixedPointsEquivOriginal_apply_coe
      S C hcentral hgenerate theta x

/-- Pulling the copied invariant kernel character back through the kernel
copying equivalence recovers the original invariant kernel character. -/
theorem
    productAmbientGlaubermanLeftInertiaInvariantKernelCharacter_comap_original
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    (productAmbientGlaubermanLeftInertiaInvariantKernelCharacter
        S C hcentral hgenerate theta).1.1.comap
        (productAmbientGlaubermanLeftOWKernelEquivOriginal
          S C hcentral hgenerate theta) =
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  change
    (productAmbientGlaubermanLeftInertiaPPrimeKernelCharacter
        S C hcentral hgenerate theta).1.comap
        (productAmbientGlaubermanLeftOWKernelEquivOriginal
          S C hcentral hgenerate theta) =
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1
  rw [
    productAmbientGlaubermanLeftInertiaPPrimeKernelCharacter_coe]
  simp [productAmbientGlaubermanLeftOWKernelEquivOriginal]

/-- Glauberman correspondents agree after transport through the exact
fixed-point coordinate.  This follows from restriction-multiplicity
transport and hence holds for every correspondence on the copied action,
independently of its construction. -/
theorem
    productAmbientGlaubermanLeftOWCorrespondent_comap_original
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (d :
      GlaubermanCorrespondence
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    ((d.characterEquiv
        (productAmbientGlaubermanLeftInertiaInvariantKernelCharacter
          S C hcentral hgenerate theta)).1.comap
      (productAmbientGlaubermanLeftOWFixedPointsEquivOriginal
        S C hcentral hgenerate theta)) =
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let eK :=
    productAmbientGlaubermanLeftOWKernelEquivOriginal
      S C hcentral hgenerate theta
  let eF :=
    productAmbientGlaubermanLeftOWFixedPointsEquivOriginal
      S C hcentral hgenerate theta
  let source :=
    productAmbientGlaubermanLeftInertiaInvariantKernelCharacter
      S C hcentral hgenerate theta
  let target := d.characterEquiv source
  let targetOld :=
    IrreducibleCharacter.pPrimeComapEquiv q eF target
  have hmult :
      ¬q ∣
        restrictionMultiplicity
          (coprimeFixedPointsInclusion
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))
          targetOld.1
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta).1.1 := by
    have htransport :=
      restrictionMultiplicity_comap_equiv
        eK eF
        (coprimeFixedPointsInclusion
          (ProductAmbientGlaubermanLeftOWKernel
            S C hcentral hgenerate theta)
          (ProductAmbientGlaubermanLeftOWSylow
            S C hgenerate theta :
            Subgroup
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)))
        (coprimeFixedPointsInclusion
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))
        (productAmbientGlaubermanLeftOWFixedPointsEquivOriginal_inclusion_commutes
          S C hcentral hgenerate theta)
        target.1 source.1.1
    change
      ¬q ∣
        restrictionMultiplicity
          (coprimeFixedPointsInclusion
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))
          (target.1.comap eF)
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta).1.1
    rw [←
      productAmbientGlaubermanLeftInertiaInvariantKernelCharacter_comap_original
        S C hcentral hgenerate theta]
    rw [htransport]
    exact d.multiplicity_isPPrime source
  have heq :=
    g.eq_correspondent_of_multiplicity_isPPrime
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta)
      targetOld hmult
  exact congrArg Subtype.val heq

/-- An extension remains an extension after both characters are moved to
the canonical normal copy inside the inertia group of the extension. -/
theorem inertiaCopyCharacter_isExtensionAlong_extensionToInertiaNormalHom
    {G N : Type} [Group G] [Finite G] [Group N] [Finite N]
    (A : Subgroup G) [A.Normal]
    (i : N →* A)
    (chi : IrreducibleCharacter N)
    (psi : IrreducibleCharacter A)
    (hpsi :
      IrreducibleCharacter.IsExtensionAlong i chi psi) :
    IrreducibleCharacter.IsExtensionAlong
      (extensionToInertiaNormalHom A i psi)
      chi
      (inertiaCopyCharacter A psi) := by
  intro n
  change
    psi.values
        (inertiaNormalCopyEquiv A psi
          ((inertiaNormalCopyEquiv A psi).symm (i n))) =
      chi.values n
  rw [(inertiaNormalCopyEquiv A psi).apply_symm_apply]
  exact hpsi n

/-- The right inertia normal-copy character extends the original
Glauberman fixed-point character along the canonical fixed-point-factor
homomorphism. -/
theorem
    productAmbientGlaubermanRightNormalCopyCharacter_isFixedPointExtension
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
    IrreducibleCharacter.IsExtensionAlong
      (productAmbientGlaubermanFixedPointKernelToRightNormalCopy
        S C hcentral hgenerate g theta)
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1
      (inertiaCopyCharacter
        (internalProductNormalizer S C)
        (productAmbientGlaubermanRightKernelTransportCharacter
          S C hcentral g theta)) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  rw [←
    productAmbientGlaubermanFixedPointExtensionToInertia_eq
      S C hcentral hgenerate g theta]
  exact
    inertiaCopyCharacter_isExtensionAlong_extensionToInertiaNormalHom
      (internalProductNormalizer S C)
      (productAmbientGlaubermanFixedPointKernelToRightCharacter
        S C hcentral)
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1
      (productAmbientGlaubermanRightKernelTransportCharacter
        S C hcentral g theta)
      (productAmbientGlaubermanRightCharacter_isFixedPointExtension
        S C hcentral g theta)

/-- The exact equivalence from the internal copied fixed points used by
Okuyama--Wajima back to the original product fixed-point kernel. -/
def productAmbientGlaubermanLeftOWInternalFixedPointsEquivOriginal
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    okuyamaWajimaInternalFixedPoints
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)) ≃*
      productPPrimeKernelFixedPoints S C hcentral :=
  (Subgroup.subgroupOfEquivOfLe
    (show
      coprimeFixedPoints
          (ProductAmbientGlaubermanLeftOWKernel
            S C hcentral hgenerate theta)
          (ProductAmbientGlaubermanLeftOWSylow
            S C hgenerate theta :
            Subgroup
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)) ≤
        Subgroup.normalizer
          ((ProductAmbientGlaubermanLeftOWSylow
            S C hgenerate theta :
            Subgroup
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)) :
            Set
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)) from
      inf_le_right.trans
        (Subgroup.centralizer_le_normalizer
          ((ProductAmbientGlaubermanLeftOWSylow
            S C hgenerate theta :
            Subgroup
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)) :
            Set
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta))))).trans
    (productAmbientGlaubermanLeftOWFixedPointsEquivOriginal
      S C hcentral hgenerate theta).symm

@[simp]
theorem
    productAmbientGlaubermanLeftOWInternalFixedPointsEquivOriginal_apply_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (x :
      okuyamaWajimaInternalFixedPoints
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta))) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    (((productAmbientGlaubermanLeftOWInternalFixedPointsEquivOriginal
          S C hcentral hgenerate theta x :
        productPPrimeKernelFixedPoints S C hcentral) :
      product S C) : X) =
      ((((x :
        Subgroup.normalizer
          ((ProductAmbientGlaubermanLeftOWSylow
            S C hgenerate theta :
            Subgroup
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)) :
            Set
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta))) :
        ProductAmbientGlaubermanLeftInertiaGroup
          S C hgenerate theta) : X)) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let eF :=
    productAmbientGlaubermanLeftOWFixedPointsEquivOriginal
      S C hcentral hgenerate theta
  let eI :=
    Subgroup.subgroupOfEquivOfLe
      (show
        coprimeFixedPoints
            (ProductAmbientGlaubermanLeftOWKernel
              S C hcentral hgenerate theta)
            (ProductAmbientGlaubermanLeftOWSylow
              S C hgenerate theta :
              Subgroup
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta)) ≤
          Subgroup.normalizer
            ((ProductAmbientGlaubermanLeftOWSylow
              S C hgenerate theta :
              Subgroup
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta)) :
              Set
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta)) from
        inf_le_right.trans
          (Subgroup.centralizer_le_normalizer
            ((ProductAmbientGlaubermanLeftOWSylow
              S C hgenerate theta :
              Subgroup
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta)) :
              Set
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta))))
  have hback := eF.apply_symm_apply (eI x)
  have hcoe :=
    congrArg
      (fun z :
        coprimeFixedPoints
          (ProductAmbientGlaubermanLeftOWKernel
            S C hcentral hgenerate theta)
          (ProductAmbientGlaubermanLeftOWSylow
            S C hgenerate theta :
            Subgroup
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)) =>
        ((((z :
          ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta) : X))))
      hback
  rw [
    productAmbientGlaubermanLeftOWFixedPointsEquivOriginal_apply_coe]
    at hcoe
  change
    (((eF.symm (eI x) :
        productPPrimeKernelFixedPoints S C hcentral) :
      product S C) : X) =
      (((x :
          Subgroup.normalizer
            ((ProductAmbientGlaubermanLeftOWSylow
              S C hgenerate theta :
              Subgroup
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta)) :
              Set
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta))) :
        ProductAmbientGlaubermanLeftInertiaGroup
          S C hgenerate theta) : X) at hcoe
  change
    (((eF.symm (eI x) :
      productPPrimeKernelFixedPoints S C hcentral) :
      product S C) : X) =
      (((x :
          Subgroup.normalizer
            ((ProductAmbientGlaubermanLeftOWSylow
              S C hgenerate theta :
              Subgroup
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta)) :
              Set
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta))) :
        ProductAmbientGlaubermanLeftInertiaGroup
          S C hgenerate theta) : X)
  exact hcoe

@[simp]
theorem productAmbientGlaubermanFixedPointKernelToAmbientNormalizer_apply_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (x : productPPrimeKernelFixedPoints S C hcentral) :
    ((productAmbientGlaubermanFixedPointKernelToAmbientNormalizer
        S C hcentral x :
      ambientNormalizer S) : X) =
      ((x : product S C) : X) := by
  rfl

/-- In the exact internal fixed-point coordinate, the copied
correspondent is the pullback of the original correspondent. -/
theorem
    productAmbientGlaubermanLeftOWInternalFixedPointCharacter_eq_comap_original
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (d :
      GlaubermanCorrespondence
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    okuyamaWajimaInternalFixedPointCharacter
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta)
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        d
        (productAmbientGlaubermanLeftInertiaInvariantKernelCharacter
          S C hcentral hgenerate theta) =
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1.comap
        (productAmbientGlaubermanLeftOWInternalFixedPointsEquivOriginal
          S C hcentral hgenerate theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let hfixed :
      coprimeFixedPoints
          (ProductAmbientGlaubermanLeftOWKernel
            S C hcentral hgenerate theta)
          (ProductAmbientGlaubermanLeftOWSylow
            S C hgenerate theta :
            Subgroup
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)) ≤
        Subgroup.normalizer
          ((ProductAmbientGlaubermanLeftOWSylow
            S C hgenerate theta :
            Subgroup
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)) :
            Set
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)) :=
    inf_le_right.trans
      (Subgroup.centralizer_le_normalizer
        ((ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)) :
          Set
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)))
  let eInternal := Subgroup.subgroupOfEquivOfLe hfixed
  apply IrreducibleCharacter.ext
  funext x
  rw [IrreducibleCharacter.comap_values]
  change
    (d.characterEquiv
      (productAmbientGlaubermanLeftInertiaInvariantKernelCharacter
        S C hcentral hgenerate theta)).1.values
        (eInternal x) =
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1.values
        ((productAmbientGlaubermanLeftOWFixedPointsEquivOriginal
          S C hcentral hgenerate theta).symm
          (eInternal x))
  have hcorr :=
    productAmbientGlaubermanLeftOWCorrespondent_comap_original
      S C hcentral hgenerate g theta d
  have hvalue :=
    congrArg
      (fun chi :
        IrreducibleCharacter
          (productPPrimeKernelFixedPoints S C hcentral) =>
        chi.values
          ((productAmbientGlaubermanLeftOWFixedPointsEquivOriginal
            S C hcentral hgenerate theta).symm
            (eInternal x)))
      hcorr
  rw [IrreducibleCharacter.comap_values,
    (productAmbientGlaubermanLeftOWFixedPointsEquivOriginal
      S C hcentral hgenerate theta).apply_symm_apply] at hvalue
  exact hvalue

/-- The canonical right-inertia equivalence sends the original fixed-point
factor in the right normal copy to the internal copied fixed-point element. -/
theorem
    productAmbientGlaubermanRightInertiaEquiv_map_fixedPoint_eq
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (x :
      okuyamaWajimaInternalFixedPoints
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta))) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
      (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    productAmbientGlaubermanRightInertiaEquivLeftSylowNormalizer
        S C hcentral hgenerate g theta
        ((productAmbientGlaubermanFixedPointKernelToRightNormalCopy
          S C hcentral hgenerate g theta
          (productAmbientGlaubermanLeftOWInternalFixedPointsEquivOriginal
            S C hcentral hgenerate theta x) :
          ProductAmbientGlaubermanRightNormalCopy
            S C hcentral hgenerate g theta) :
          ProductAmbientGlaubermanRightInertiaGroup
            S C hcentral hgenerate g theta) =
      (x :
        Subgroup.normalizer
          ((ProductAmbientGlaubermanLeftOWSylow
            S C hgenerate theta :
            Subgroup
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)) :
            Set
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta))) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  apply Subtype.ext
  rw [
    productAmbientGlaubermanRightInertiaEquivLeftSylowNormalizer_apply]
  apply Subtype.ext
  change
    ((((productAmbientGlaubermanFixedPointKernelToRightNormalCopy
          S C hcentral hgenerate g theta
          (productAmbientGlaubermanLeftOWInternalFixedPointsEquivOriginal
            S C hcentral hgenerate theta x) :
        ProductAmbientGlaubermanRightNormalCopy
          S C hcentral hgenerate g theta) :
        ProductAmbientGlaubermanRightInertiaGroup
          S C hcentral hgenerate g theta) :
      ambientNormalizer S) : X) =
      (((x :
          Subgroup.normalizer
            ((ProductAmbientGlaubermanLeftOWSylow
              S C hgenerate theta :
              Subgroup
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta)) :
              Set
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta))) :
        ProductAmbientGlaubermanLeftInertiaGroup
          S C hgenerate theta) : X)
  rw [
    productAmbientGlaubermanFixedPointKernelToRightNormalCopy_coe,
    productAmbientGlaubermanFixedPointKernelToAmbientNormalizer_apply_coe,
    productAmbientGlaubermanLeftOWInternalFixedPointsEquivOriginal_apply_coe]

/-- The canonical target normal-product coordinate commutes with the
fixed-point inclusions. -/
theorem
    productAmbientGlaubermanCanonicalRightOWNormalCoordinate_fixedPoint_commutes
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
    (productAmbientGlaubermanCanonicalRightOWNormalCoordinate
        S C hcentral hgenerate g theta).normalProductEquiv.symm.toMonoidHom.comp
        (Subgroup.inclusion
          (internalFixedPoints_le_internalNormalProduct
            (ProductAmbientGlaubermanLeftOWKernel
              S C hcentral hgenerate theta)
            (ProductAmbientGlaubermanLeftOWSylow
              S C hgenerate theta :
              Subgroup
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta)))) =
      (productAmbientGlaubermanFixedPointKernelToRightNormalCopy
        S C hcentral hgenerate g theta).comp
        (productAmbientGlaubermanLeftOWInternalFixedPointsEquivOriginal
          S C hcentral hgenerate theta).toMonoidHom := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let c :=
    productAmbientGlaubermanCanonicalRightOWNormalCoordinate
      S C hcentral hgenerate g theta
  let e :=
    productAmbientGlaubermanRightInertiaEquivLeftSylowNormalizer
      S C hcentral hgenerate g theta
  let f :=
    productAmbientGlaubermanFixedPointKernelToRightNormalCopy
      S C hcentral hgenerate g theta
  let eF :=
    productAmbientGlaubermanLeftOWInternalFixedPointsEquivOriginal
      S C hcentral hgenerate theta
  apply MonoidHom.ext
  intro x
  apply c.normalProductEquiv.injective
  change
    c.normalProductEquiv
        (c.normalProductEquiv.symm
          (Subgroup.inclusion
            (internalFixedPoints_le_internalNormalProduct
              (ProductAmbientGlaubermanLeftOWKernel
                S C hcentral hgenerate theta)
              (ProductAmbientGlaubermanLeftOWSylow
                S C hgenerate theta :
                Subgroup
                  (ProductAmbientGlaubermanLeftInertiaGroup
                    S C hgenerate theta))) x)) =
      c.normalProductEquiv (f (eF x))
  rw [c.normalProductEquiv.apply_symm_apply]
  apply Subtype.ext
  have hc :=
    congrArg
      (fun k :
        ProductAmbientGlaubermanRightNormalCopy
            S C hcentral hgenerate g theta →*
          Subgroup.normalizer
            ((ProductAmbientGlaubermanLeftOWSylow
              S C hgenerate theta :
              Subgroup
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta)) :
              Set
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta)) =>
        k (f (eF x)))
      c.inclusion_commutes
  change
    e
        ((f (eF x) :
          ProductAmbientGlaubermanRightNormalCopy
            S C hcentral hgenerate g theta) :
          ProductAmbientGlaubermanRightInertiaGroup
            S C hcentral hgenerate g theta) =
      ((c.normalProductEquiv (f (eF x)) :
        ProductAmbientGlaubermanLeftOWTargetNormalProduct
          S C hcentral hgenerate theta) :
        Subgroup.normalizer
          ((ProductAmbientGlaubermanLeftOWSylow
            S C hgenerate theta :
            Subgroup
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)) :
            Set
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta))) at hc
  have hm :=
    productAmbientGlaubermanRightInertiaEquiv_map_fixedPoint_eq
      S C hcentral hgenerate g theta x
  exact hm.symm.trans hc

/-- The canonical transported right normal character extends the copied
Glauberman correspondent in the exact internal fixed-point coordinate. -/
theorem
    productAmbientGlaubermanCanonicalRightOWTargetExtension_isFixedPointExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (d :
      GlaubermanCorrespondence
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)) q) :
    IrreducibleCharacter.IsExtensionAlong
      (Subgroup.inclusion
        (internalFixedPoints_le_internalNormalProduct
          (ProductAmbientGlaubermanLeftOWKernel
            S C hcentral hgenerate theta)
          (ProductAmbientGlaubermanLeftOWSylow
            S C hgenerate theta :
            Subgroup
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta))))
      (okuyamaWajimaInternalFixedPointCharacter
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta)
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        d
        (productAmbientGlaubermanLeftInertiaInvariantKernelCharacter
          S C hcentral hgenerate theta))
      (productAmbientGlaubermanCanonicalRightOWTargetExtension
        S C hcentral hgenerate g theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let c :=
    productAmbientGlaubermanCanonicalRightOWNormalCoordinate
      S C hcentral hgenerate g theta
  let eF :=
    productAmbientGlaubermanLeftOWInternalFixedPointsEquivOriginal
      S C hcentral hgenerate theta
  have htransport :=
    IrreducibleCharacter.IsExtensionAlong.comap_equiv
      c.normalProductEquiv.symm eF
      (productAmbientGlaubermanCanonicalRightOWNormalCoordinate_fixedPoint_commutes
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanRightNormalCopyCharacter_isFixedPointExtension
        S C hcentral hgenerate g theta)
  rw [
    productAmbientGlaubermanLeftOWInternalFixedPointCharacter_eq_comap_original
      S C hcentral hgenerate g theta d]
  exact htransport

/-- Conjugation is transported through every exact right normal-product
coordinate. -/
theorem
    productAmbientGlaubermanRightOWNormalCoordinate_symm_conjugate
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (c :
      ProductAmbientGlaubermanRightOWNormalCoordinate
        S C hcentral hgenerate g theta)
    (a :
      Subgroup.normalizer
        ((ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)) :
          Set
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)))
    (x :
      ProductAmbientGlaubermanLeftOWTargetNormalProduct
        S C hcentral hgenerate theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
      (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    c.normalProductEquiv.symm
        (conjugateNormalElement
          (ProductAmbientGlaubermanLeftOWTargetNormalProduct
            S C hcentral hgenerate theta)
          (internalNormalProduct_normal
            (ProductAmbientGlaubermanLeftOWKernel
              S C hcentral hgenerate theta)
            (ProductAmbientGlaubermanLeftOWSylow
              S C hgenerate theta :
              Subgroup
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta))
            (productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_normal
              S C hcentral hgenerate theta))
          a x) =
      conjugateNormalElement
        (ProductAmbientGlaubermanRightNormalCopy
          S C hcentral hgenerate g theta)
        (inferInstance :
          (ProductAmbientGlaubermanRightNormalCopy
            S C hcentral hgenerate g theta).Normal)
        ((productAmbientGlaubermanRightInertiaEquivLeftSylowNormalizer
          S C hcentral hgenerate g theta).symm a)
        (c.normalProductEquiv.symm x) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let e :=
    productAmbientGlaubermanRightInertiaEquivLeftSylowNormalizer
      S C hcentral hgenerate g theta
  let N :=
    ProductAmbientGlaubermanRightNormalCopy
      S C hcentral hgenerate g theta
  let L :=
    ProductAmbientGlaubermanLeftOWTargetNormalProduct
      S C hcentral hgenerate theta
  let b := e.symm a
  let n := c.normalProductEquiv.symm x
  have hc (z : N) :
      e (z :
        ProductAmbientGlaubermanRightInertiaGroup
          S C hcentral hgenerate g theta) =
        (c.normalProductEquiv z :
          Subgroup.normalizer
            ((ProductAmbientGlaubermanLeftOWSylow
              S C hgenerate theta :
              Subgroup
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta)) :
              Set
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta))) := by
    have hz :=
      congrArg
        (fun k :
          N →*
            Subgroup.normalizer
              ((ProductAmbientGlaubermanLeftOWSylow
                S C hgenerate theta :
                Subgroup
                  (ProductAmbientGlaubermanLeftInertiaGroup
                    S C hgenerate theta)) :
                Set
                  (ProductAmbientGlaubermanLeftInertiaGroup
                    S C hgenerate theta)) =>
          k z)
        c.inclusion_commutes
    exact hz
  apply Subtype.ext
  apply e.injective
  change
    e
        ((c.normalProductEquiv.symm
          (conjugateNormalElement
            L
            (internalNormalProduct_normal
              (ProductAmbientGlaubermanLeftOWKernel
                S C hcentral hgenerate theta)
              (ProductAmbientGlaubermanLeftOWSylow
                S C hgenerate theta :
                Subgroup
                  (ProductAmbientGlaubermanLeftInertiaGroup
                    S C hgenerate theta))
              (productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_normal
                S C hcentral hgenerate theta))
            a x) : N) :
          ProductAmbientGlaubermanRightInertiaGroup
            S C hcentral hgenerate g theta) =
      e
        ((conjugateNormalElement N inferInstance b n : N) :
          ProductAmbientGlaubermanRightInertiaGroup
            S C hcentral hgenerate g theta)
  rw [hc, c.normalProductEquiv.apply_symm_apply]
  change
    (conjugateNormalElement
      L
      (internalNormalProduct_normal
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta))
        (productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_normal
          S C hcentral hgenerate theta))
      a x :
      Subgroup.normalizer
        ((ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)) :
          Set
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta))) =
      e (b * (n :
        ProductAmbientGlaubermanRightInertiaGroup
          S C hcentral hgenerate g theta) * b⁻¹)
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply, hc]
  rw [show c.normalProductEquiv n = x from
    c.normalProductEquiv.apply_symm_apply x]
  rfl

/-- The transported right normal-copy character is invariant under the
whole copied Sylow normalizer, for every exact target coordinate. -/
theorem productAmbientGlaubermanRightOWTargetExtension_isInvariant
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (c :
      ProductAmbientGlaubermanRightOWNormalCoordinate
        S C hcentral hgenerate g theta)
    (a :
      Subgroup.normalizer
        ((ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)) :
          Set
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)))
    (x :
      ProductAmbientGlaubermanLeftOWTargetNormalProduct
        S C hcentral hgenerate theta) :
    (productAmbientGlaubermanRightOWTargetExtension
        S C hcentral hgenerate g theta c).values
        (conjugateNormalElement
          (ProductAmbientGlaubermanLeftOWTargetNormalProduct
            S C hcentral hgenerate theta)
          (internalNormalProduct_normal
            (ProductAmbientGlaubermanLeftOWKernel
              S C hcentral hgenerate theta)
            (ProductAmbientGlaubermanLeftOWSylow
              S C hgenerate theta :
              Subgroup
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta))
            (productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_normal
              S C hcentral hgenerate theta))
          a x) =
      (productAmbientGlaubermanRightOWTargetExtension
        S C hcentral hgenerate g theta c).values x := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let chi :=
    inertiaCopyCharacter
      (internalProductNormalizer S C)
      (productAmbientGlaubermanRightKernelTransportCharacter
        S C hcentral g theta)
  let e :=
    productAmbientGlaubermanRightInertiaEquivLeftSylowNormalizer
      S C hcentral hgenerate g theta
  let b := e.symm a
  let n := c.normalProductEquiv.symm x
  change
    chi.values
        (c.normalProductEquiv.symm
          (conjugateNormalElement
            (ProductAmbientGlaubermanLeftOWTargetNormalProduct
              S C hcentral hgenerate theta)
            (internalNormalProduct_normal
              (ProductAmbientGlaubermanLeftOWKernel
                S C hcentral hgenerate theta)
              (ProductAmbientGlaubermanLeftOWSylow
                S C hgenerate theta :
                Subgroup
                  (ProductAmbientGlaubermanLeftInertiaGroup
                    S C hgenerate theta))
              (productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_normal
                S C hcentral hgenerate theta))
            a x)) =
      chi.values n
  rw [
    productAmbientGlaubermanRightOWNormalCoordinate_symm_conjugate
      S C hcentral hgenerate g theta c a x]
  have hfix :=
    inertiaCopyCharacter_invariant
      (internalProductNormalizer S C)
      (productAmbientGlaubermanRightKernelTransportCharacter
        S C hcentral g theta)
      b⁻¹
  have hvalue :=
    congrArg
      (fun eta :
        IrreducibleCharacter
          (ProductAmbientGlaubermanRightNormalCopy
            S C hcentral hgenerate g theta) =>
        eta.values n)
      hfix
  rw [IrreducibleCharacter.conjBy_values] at hvalue
  convert hvalue using 1
  apply congrArg chi.values
  apply Subtype.ext
  simp [conjugateNormalElement, b, e, n]

/-- The canonical transported target extension is invariant under the
whole copied Sylow normalizer. -/
theorem productAmbientGlaubermanCanonicalRightOWTargetExtension_isInvariant
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (a :
      Subgroup.normalizer
        ((ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)) :
          Set
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)))
    (x :
      ProductAmbientGlaubermanLeftOWTargetNormalProduct
        S C hcentral hgenerate theta) :
    (productAmbientGlaubermanCanonicalRightOWTargetExtension
        S C hcentral hgenerate g theta).values
        (conjugateNormalElement
          (ProductAmbientGlaubermanLeftOWTargetNormalProduct
            S C hcentral hgenerate theta)
          (internalNormalProduct_normal
            (ProductAmbientGlaubermanLeftOWKernel
              S C hcentral hgenerate theta)
            (ProductAmbientGlaubermanLeftOWSylow
              S C hgenerate theta :
              Subgroup
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta))
            (productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_normal
              S C hcentral hgenerate theta))
          a x) =
      (productAmbientGlaubermanCanonicalRightOWTargetExtension
        S C hcentral hgenerate g theta).values x :=
  productAmbientGlaubermanRightOWTargetExtension_isInvariant
    S C hcentral hgenerate g theta
    (productAmbientGlaubermanCanonicalRightOWNormalCoordinate
      S C hcentral hgenerate g theta) a x

/-- A chosen strong realization of the original product Glauberman
correspondence. -/
def productAmbientGlaubermanOriginalStrongRealization
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral) :
    letI :
      MulDistribMulAction
        (productSylow S C : Subgroup (product S C))
        (productPPrimeKernel S C hcentral) :=
      subgroupConjugationMulDistribMulAction
        (productPPrimeKernel S C hcentral)
        (productSylow S C : Subgroup (product S C))
    StrongActionGlaubermanCorrespondence
      (productSylow S C : Subgroup (product S C))
      (productPPrimeKernel S C hcentral) q :=
  Classical.choose
    (GlaubermanCorrespondence.exists_strongActionRealization
      (productPPrimeKernel S C hcentral)
      (productSylow S C : Subgroup (product S C))
      (productSylow S C).isPGroup'
      (productPPrimeKernel_isPPrimeGroup S C hcentral)
      g)

/-- The chosen strong action correspondence realizes the supplied
ordinary product Glauberman correspondence. -/
theorem productAmbientGlaubermanOriginalStrongRealization_realizes
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral) :
    letI :
      MulDistribMulAction
        (productSylow S C : Subgroup (product S C))
        (productPPrimeKernel S C hcentral) :=
      subgroupConjugationMulDistribMulAction
        (productPPrimeKernel S C hcentral)
        (productSylow S C : Subgroup (product S C))
    glaubermanCorrespondenceOfStrongConjugationAction
        (productPPrimeKernel S C hcentral)
        (productSylow S C : Subgroup (product S C))
        (productAmbientGlaubermanOriginalStrongRealization
          S C hcentral g) =
      g :=
  Classical.choose_spec
    (GlaubermanCorrespondence.exists_strongActionRealization
      (productPPrimeKernel S C hcentral)
      (productSylow S C : Subgroup (product S C))
      (productSylow S C).isPGroup'
      (productPPrimeKernel_isPPrimeGroup S C hcentral)
      g)

/-- Transport the chosen strong realization to the copied kernel action
inside the exact character inertia group. -/
def productAmbientGlaubermanLeftOWStrongCorrespondence
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
      MulDistribMulAction
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta))
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta) :=
      subgroupConjugationMulDistribMulAction
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta))
    StrongActionGlaubermanCorrespondence
      (ProductAmbientGlaubermanLeftOWSylow
        S C hgenerate theta :
        Subgroup
          (ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta))
      (ProductAmbientGlaubermanLeftOWKernel
        S C hcentral hgenerate theta) q := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      MulDistribMulAction
        (productSylow S C : Subgroup (product S C))
        (productPPrimeKernel S C hcentral) :=
    subgroupConjugationMulDistribMulAction
      (productPPrimeKernel S C hcentral)
      (productSylow S C : Subgroup (product S C))
  letI :
      MulDistribMulAction
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta))
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta) :=
    subgroupConjugationMulDistribMulAction
      (ProductAmbientGlaubermanLeftOWKernel
        S C hcentral hgenerate theta)
      (ProductAmbientGlaubermanLeftOWSylow
        S C hgenerate theta :
        Subgroup
          (ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta))
  exact
    StrongActionGlaubermanCorrespondence.transport
      (ProductAmbientGlaubermanLeftOWSylow
        S C hgenerate theta :
        Subgroup
          (ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta))
      (productSylow S C : Subgroup (product S C))
      (ProductAmbientGlaubermanLeftOWKernel
        S C hcentral hgenerate theta)
      (productPPrimeKernel S C hcentral)
      (productAmbientGlaubermanLeftOWSylowEquivOriginal
        S C hgenerate theta)
      (productAmbientGlaubermanLeftOWKernelEquivOriginal
        S C hcentral hgenerate theta)
      (productAmbientGlaubermanLeftOWEquivOriginal_smul
        S C hcentral hgenerate theta)
      (productAmbientGlaubermanOriginalStrongRealization
        S C hcentral g)

/-- The ordinary Glauberman correspondence on the copied kernel action. -/
def productAmbientGlaubermanLeftOWCorrespondence
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    GlaubermanCorrespondence
      (ProductAmbientGlaubermanLeftOWKernel
        S C hcentral hgenerate theta)
      (ProductAmbientGlaubermanLeftOWSylow
        S C hgenerate theta :
        Subgroup
          (ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta)) q := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      MulDistribMulAction
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta))
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta) :=
    subgroupConjugationMulDistribMulAction
      (ProductAmbientGlaubermanLeftOWKernel
        S C hcentral hgenerate theta)
      (ProductAmbientGlaubermanLeftOWSylow
        S C hgenerate theta :
        Subgroup
          (ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta))
  exact
    glaubermanCorrespondenceOfStrongConjugationAction
      (ProductAmbientGlaubermanLeftOWKernel
        S C hcentral hgenerate theta)
      (ProductAmbientGlaubermanLeftOWSylow
        S C hgenerate theta :
        Subgroup
          (ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta))
      (productAmbientGlaubermanLeftOWStrongCorrespondence
        S C hcentral hgenerate g theta)

/-- The canonical right target extension supplies the complete target
input for every Glauberman correspondence on the copied action. -/
theorem productAmbientGlaubermanCanonicalRightOWTargetExtensionInput
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (d :
      GlaubermanCorrespondence
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)) q) :
    ProductAmbientGlaubermanCanonicalRightOWTargetExtensionInput
      S C hcentral hgenerate g theta d where
  isExtension :=
    productAmbientGlaubermanCanonicalRightOWTargetExtension_isFixedPointExtension
      S C hcentral hgenerate g theta d
  isInvariant :=
    productAmbientGlaubermanCanonicalRightOWTargetExtension_isInvariant
      S C hcentral hgenerate g theta

/-- The fully constructed target input for the explicitly transported
copied Glauberman correspondence. -/
theorem productAmbientGlaubermanLeftOWCorrespondenceTargetExtensionInput
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    ProductAmbientGlaubermanCanonicalRightOWTargetExtensionInput
      S C hcentral hgenerate g theta
      (productAmbientGlaubermanLeftOWCorrespondence
        S C hcentral hgenerate g theta) :=
  productAmbientGlaubermanCanonicalRightOWTargetExtensionInput
    S C hcentral hgenerate g theta
    (productAmbientGlaubermanLeftOWCorrespondence
      S C hcentral hgenerate g theta)

/-- Once the semantic ordinary Okuyama--Wajima input is available, no
additional target-extension hypothesis is needed for the exact
right-inertia count. -/
theorem
    productAmbientGlaubermanLeftOW_natCard_eq_rightInertia_of_uniformInput
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (d :
      GlaubermanCorrespondence
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)) q)
    (how :
      OkuyamaWajimaComplementUniformOrdinaryInput
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta)
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (productAmbientGlaubermanLeftInertiaPPrimeKernel_isPPrimeGroup
          S C hcentral hgenerate theta)
        (productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_normal
          S C hcentral hgenerate theta)
        d
        (productAmbientGlaubermanLeftInertiaInvariantKernelCharacter
          S C hcentral hgenerate theta)) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
      (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    Nat.card
        (IrreducibleCharactersOverAlong
          (inertiaNormalCopy (product S C) theta.1).subtype
          (productAmbientGlaubermanLeftInertiaTheta
            S C hgenerate theta).1) =
      Nat.card
        (IrreducibleCharactersOverAlong
          (ProductAmbientGlaubermanRightNormalCopy
            S C hcentral hgenerate g theta).subtype
          (inertiaCopyCharacter
            (internalProductNormalizer S C)
            (productAmbientGlaubermanRightKernelTransportCharacter
              S C hcentral g theta))) :=
  productAmbientGlaubermanLeftOW_natCard_eq_rightInertia_canonical
    S C hcentral hgenerate g theta d how
    (productAmbientGlaubermanCanonicalRightOWTargetExtensionInput
      S C hcentral hgenerate g theta d)

/-- Exact right-inertia count using the explicitly transported copied
Glauberman correspondence; the uniform ordinary OW theorem is the only
remaining input. -/
theorem
    productAmbientGlaubermanLeftOW_natCard_eq_rightInertia_transported
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (how :
      OkuyamaWajimaComplementUniformOrdinaryInput
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta)
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (productAmbientGlaubermanLeftInertiaPPrimeKernel_isPPrimeGroup
          S C hcentral hgenerate theta)
        (productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_normal
          S C hcentral hgenerate theta)
        (productAmbientGlaubermanLeftOWCorrespondence
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanLeftInertiaInvariantKernelCharacter
          S C hcentral hgenerate theta)) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
      (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    Nat.card
        (IrreducibleCharactersOverAlong
          (inertiaNormalCopy (product S C) theta.1).subtype
          (productAmbientGlaubermanLeftInertiaTheta
            S C hgenerate theta).1) =
      Nat.card
        (IrreducibleCharactersOverAlong
          (ProductAmbientGlaubermanRightNormalCopy
            S C hcentral hgenerate g theta).subtype
          (inertiaCopyCharacter
            (internalProductNormalizer S C)
            (productAmbientGlaubermanRightKernelTransportCharacter
              S C hcentral g theta))) :=
  productAmbientGlaubermanLeftOW_natCard_eq_rightInertia_of_uniformInput
    S C hcentral hgenerate g theta
    (productAmbientGlaubermanLeftOWCorrespondence
      S C hcentral hgenerate g theta) how

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
