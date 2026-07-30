/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaParameterCoordinates
import McKayConjecture.Character.OkuyamaWajimaSourceRouteAutomatic
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalTargetFullInertiaScalar
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionOkuyamaWajimaCharacterInertiaCharacters

/-!
# The ordinary Okuyama--Wajima count inside the exact character inertia

Fix a prime-to-`q` character `theta` of `D = CS` and work in its exact
ambient inertia group

`Γ_theta = I_X(theta)`.

The preceding two adapters supplied the copied canonical `q'`-kernel
`K_theta`, the restricted Sylow subgroup `S_theta`, their normal product,
and the invariant copied kernel character.  This file specializes the
ordinary Okuyama--Wajima cardinality theorem to those data.

The source normal-product extension is canonical: it is the transported
copy of `theta`, and its full `Γ_theta`-invariance is proved here.  On the
target side, the existing matched right inertia group is canonically
equivalent to `N_{Γ_theta}(S_theta)`.  The only group-coordinate datum
retained explicitly is an equivalence between the right inertia normal
copy and the internal Okuyama--Wajima target normal product, together with
the commuting inclusion square.  Pulling the right normal-copy character
through that equivalence defines the target extension; no literal equality
of subtype groups is assumed.

The final theorem therefore retains only:

* an ordinary Glauberman correspondence for the copied kernel action;
* the printed (or semantic uniform) ordinary Okuyama--Wajima input;
* the genuine target extension and normalizer-invariance statements; and
* the exact target normal-subgroup coordinate square.

No source and target Gallagher parameters are identified.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CliffordEquivalence
open CliffordCorrespondence
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The copied canonical `q'`-kernel inside `Γ_theta`. -/
abbrev ProductAmbientGlaubermanLeftOWKernel
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :=
  productAmbientGlaubermanLeftInertiaPPrimeKernel
    S C hcentral hgenerate theta

/-- The restricted Sylow subgroup inside `Γ_theta`. -/
abbrev ProductAmbientGlaubermanLeftOWSylow
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :=
  productAmbientGlaubermanLeftInertiaSylow
    S C hgenerate theta

/-- The source normal product `K_theta S_theta` inside `Γ_theta`. -/
abbrev ProductAmbientGlaubermanLeftOWSourceNormalProduct
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    Subgroup
      (ProductAmbientGlaubermanLeftInertiaGroup
        S C hgenerate theta) :=
  ProductAmbientGlaubermanLeftOWKernel
      S C hcentral hgenerate theta ⊔
    (ProductAmbientGlaubermanLeftOWSylow
      S C hgenerate theta :
      Subgroup
        (ProductAmbientGlaubermanLeftInertiaGroup
          S C hgenerate theta))

/-- The internal target normal product inside
`N_{Γ_theta}(S_theta)`. -/
abbrev ProductAmbientGlaubermanLeftOWTargetNormalProduct
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :=
  okuyamaWajimaInternalNormalProduct
    (ProductAmbientGlaubermanLeftOWKernel
      S C hcentral hgenerate theta)
    (ProductAmbientGlaubermanLeftOWSylow
      S C hgenerate theta :
      Subgroup
        (ProductAmbientGlaubermanLeftInertiaGroup
          S C hgenerate theta))

/-- The source normal product is canonically the normal copy of `D = CS`
inside `Γ_theta`. -/
def productAmbientGlaubermanLeftOWSourceNormalProductEquivNormalCopy
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    ProductAmbientGlaubermanLeftOWSourceNormalProduct
        S C hcentral hgenerate theta ≃*
      inertiaNormalCopy (product S C) theta.1 :=
  MulEquiv.subgroupCongr
    (productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_eq_normalCopy
      S C hcentral hgenerate theta)

@[simp]
theorem productAmbientGlaubermanLeftOWSourceNormalProductEquivNormalCopy_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (x :
      ProductAmbientGlaubermanLeftOWSourceNormalProduct
        S C hcentral hgenerate theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    ((productAmbientGlaubermanLeftOWSourceNormalProductEquivNormalCopy
        S C hcentral hgenerate theta x :
      inertiaNormalCopy (product S C) theta.1) :
      ProductAmbientGlaubermanLeftInertiaGroup
        S C hgenerate theta) =
      x :=
  rfl

/-- The copied `theta`, expressed on the literal source normal product used
by the ordinary Okuyama--Wajima API. -/
def productAmbientGlaubermanLeftOWSourceExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    IrreducibleCharacter
      (ProductAmbientGlaubermanLeftOWSourceNormalProduct
        S C hcentral hgenerate theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    (productAmbientGlaubermanLeftInertiaTheta
      S C hgenerate theta).1.comap
      (productAmbientGlaubermanLeftOWSourceNormalProductEquivNormalCopy
        S C hcentral hgenerate theta)

/-- The source normal-product character extends the copied kernel
character. -/
theorem productAmbientGlaubermanLeftOWSourceExtension_isKernelExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    IrreducibleCharacter.IsExtensionAlong
      (Subgroup.inclusion le_sup_left)
      (productAmbientGlaubermanLeftInertiaPPrimeKernelCharacter
        S C hcentral hgenerate theta).1
      (productAmbientGlaubermanLeftOWSourceExtension
        S C hcentral hgenerate theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let K :=
    ProductAmbientGlaubermanLeftOWKernel
      S C hcentral hgenerate theta
  let L :=
    ProductAmbientGlaubermanLeftOWSourceNormalProduct
      S C hcentral hgenerate theta
  let Dcopy := inertiaNormalCopy (product S C) theta.1
  let eL : L ≃* Dcopy :=
    productAmbientGlaubermanLeftOWSourceNormalProductEquivNormalCopy
      S C hcentral hgenerate theta
  let eK : K ≃* K := MulEquiv.refl K
  have hcomm :
      eL.toMonoidHom.comp
          (Subgroup.inclusion
            (show K ≤ L from le_sup_left)) =
        (Subgroup.inclusion
          (productAmbientGlaubermanLeftInertiaPPrimeKernel_le_normalCopy
            S C hcentral hgenerate theta)).comp
          eK.toMonoidHom := by
    apply MonoidHom.ext
    intro k
    apply Subtype.ext
    rfl
  exact
    IrreducibleCharacter.IsExtensionAlong.comap_equiv
      eL eK hcomm
      (productAmbientGlaubermanLeftInertiaTheta_isKernelExtension
        S C hcentral hgenerate theta)

/-- The source normal-product extension is invariant under all of
`Γ_theta`. -/
theorem productAmbientGlaubermanLeftOWSourceExtension_isInvariant
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (a :
      ProductAmbientGlaubermanLeftInertiaGroup
        S C hgenerate theta)
    (x :
      ProductAmbientGlaubermanLeftOWSourceNormalProduct
        S C hcentral hgenerate theta) :
    (productAmbientGlaubermanLeftOWSourceExtension
        S C hcentral hgenerate theta).values
        (conjugateNormalElement
          (ProductAmbientGlaubermanLeftOWSourceNormalProduct
            S C hcentral hgenerate theta)
          (productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_normal
            S C hcentral hgenerate theta)
          a x) =
      (productAmbientGlaubermanLeftOWSourceExtension
        S C hcentral hgenerate theta).values x := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let e :=
    productAmbientGlaubermanLeftOWSourceNormalProductEquivNormalCopy
      S C hcentral hgenerate theta
  have hfix :=
    productAmbientGlaubermanLeftInertiaTheta_isInvariant
      S C hgenerate theta a⁻¹
  have hvalue :=
    congrArg
      (fun chi :
        IrreducibleCharacter
          (inertiaNormalCopy (product S C) theta.1) =>
        chi.values (e x))
      hfix
  rw [IrreducibleCharacter.conjBy_values] at hvalue
  change
    (productAmbientGlaubermanLeftInertiaTheta
        S C hgenerate theta).1.values
        (e
          (conjugateNormalElement
            (ProductAmbientGlaubermanLeftOWSourceNormalProduct
              S C hcentral hgenerate theta)
            (productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_normal
              S C hcentral hgenerate theta)
            a x)) =
      (productAmbientGlaubermanLeftInertiaTheta
        S C hgenerate theta).1.values (e x)
  convert hvalue using 1
  apply congrArg
    (productAmbientGlaubermanLeftInertiaTheta
      S C hgenerate theta).1.values
  apply Subtype.ext
  simp only [MulAut.conjNormal_symm_apply,
    inv_inv]
  rfl

/-- Relabel the source normal-product fibre back to the canonical normal
copy of `D` in `Γ_theta`. -/
def productAmbientGlaubermanLeftOWSourceFibreEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    IrreducibleCharactersOverAlong
        (inertiaNormalCopy (product S C) theta.1).subtype
        (productAmbientGlaubermanLeftInertiaTheta
          S C hgenerate theta).1 ≃
      IrreducibleCharactersOverAlong
        (ProductAmbientGlaubermanLeftOWSourceNormalProduct
          S C hcentral hgenerate theta).subtype
        (productAmbientGlaubermanLeftOWSourceExtension
          S C hcentral hgenerate theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let eL :=
    productAmbientGlaubermanLeftOWSourceNormalProductEquivNormalCopy
      S C hcentral hgenerate theta
  have hcomm :
      (MulEquiv.refl
          (ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta)).toMonoidHom.comp
          (ProductAmbientGlaubermanLeftOWSourceNormalProduct
            S C hcentral hgenerate theta).subtype =
        (inertiaNormalCopy
          (product S C) theta.1).subtype.comp
          eL.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    rfl
  exact
    CliffordCorrespondence.irreducibleCharactersOverAlongComapEquiv
      (MulEquiv.refl
        (ProductAmbientGlaubermanLeftInertiaGroup
          S C hgenerate theta))
      eL
      (inertiaNormalCopy (product S C) theta.1).subtype
      (ProductAmbientGlaubermanLeftOWSourceNormalProduct
        S C hcentral hgenerate theta).subtype
      hcomm
      (productAmbientGlaubermanLeftInertiaTheta
        S C hgenerate theta).1

/-- The exact target normal-subgroup coordinate seam.  The ambient
equivalence is fixed canonically; only its restriction to the two normal
products is recorded here. -/
structure ProductAmbientGlaubermanRightOWNormalCoordinate
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) where
  /-- Relabel the right inertia normal copy as the OW target normal
  product. -/
  normalProductEquiv :
    ProductAmbientGlaubermanRightNormalCopy
        S C hcentral hgenerate g theta ≃*
      ProductAmbientGlaubermanLeftOWTargetNormalProduct
        S C hcentral hgenerate theta
  /-- The relabelling commutes with the two subgroup inclusions and the
  canonical right-inertia equivalence. -/
  inclusion_commutes :
    (productAmbientGlaubermanRightInertiaEquivLeftSylowNormalizer
        S C hcentral hgenerate g theta).toMonoidHom.comp
        (ProductAmbientGlaubermanRightNormalCopy
          S C hcentral hgenerate g theta).subtype =
      (ProductAmbientGlaubermanLeftOWTargetNormalProduct
        S C hcentral hgenerate theta).subtype.comp
        normalProductEquiv.toMonoidHom

/-- Under the canonical right-inertia equivalence, the right normal copy
maps exactly onto the internal OW target normal product. -/
theorem
    productAmbientGlaubermanRightInertiaEquiv_map_normalCopy_eq_OWTarget
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
    (ProductAmbientGlaubermanRightNormalCopy
        S C hcentral hgenerate g theta).map
        (productAmbientGlaubermanRightInertiaEquivLeftSylowNormalizer
          S C hcentral hgenerate g theta).toMonoidHom =
      ProductAmbientGlaubermanLeftOWTargetNormalProduct
        S C hcentral hgenerate theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let e :=
    productAmbientGlaubermanRightInertiaEquivLeftSylowNormalizer
      S C hcentral hgenerate g theta
  let K :=
    ProductAmbientGlaubermanLeftOWKernel
      S C hcentral hgenerate theta
  let Q : Subgroup
      (ProductAmbientGlaubermanLeftInertiaGroup
        S C hgenerate theta) :=
    ProductAmbientGlaubermanLeftOWSylow
      S C hgenerate theta
  let L :=
    ProductAmbientGlaubermanLeftOWTargetNormalProduct
      S C hcentral hgenerate theta
  ext x
  constructor
  · rintro ⟨b, hb, hbx⟩
    have hbD :
        (((b :
          ProductAmbientGlaubermanRightInertiaGroup
            S C hcentral hgenerate g theta) :
          ambientNormalizer S) : X) ∈
          product S C := by
      exact hb
    have hebD :
        (((e b :
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
            S C hgenerate theta) : X) ∈
          product S C := by
      exact hbD
    have hxD :
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
            S C hgenerate theta) : X) ∈
          product S C := by
      rw [← hbx]
      exact hebD
    change
      (x :
        ProductAmbientGlaubermanLeftInertiaGroup
          S C hgenerate theta) ∈
        K ⊔ Q
    rw [
      productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_eq_normalCopy
        S C hcentral hgenerate theta]
    exact hxD
  · intro hx
    let b :
        ProductAmbientGlaubermanRightInertiaGroup
          S C hcentral hgenerate g theta :=
      e.symm x
    have hxD :
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
            S C hgenerate theta) : X) ∈
          product S C := by
      change
        (x :
          ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta) ∈
          inertiaNormalCopy (product S C) theta.1
      rw [←
        productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_eq_normalCopy
          S C hcentral hgenerate theta]
      exact hx
    have hbD :
        (((b :
          ProductAmbientGlaubermanRightInertiaGroup
            S C hcentral hgenerate g theta) :
          ambientNormalizer S) : X) ∈
          product S C := by
      have heq := e.apply_symm_apply x
      have heqX :=
        congrArg
          (fun y :
            Subgroup.normalizer
              ((ProductAmbientGlaubermanLeftOWSylow
                S C hgenerate theta :
                Subgroup
                  (ProductAmbientGlaubermanLeftInertiaGroup
                    S C hgenerate theta)) :
                Set
                  (ProductAmbientGlaubermanLeftInertiaGroup
                    S C hgenerate theta)) =>
            (((y :
              ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta) : X)))
          heq
      rw [← heqX] at hxD
      exact hxD
    refine ⟨b, ?_, e.apply_symm_apply x⟩
    exact hbD

/-- The canonical restriction of the right-inertia equivalence supplies
the exact target normal-subgroup coordinate square. -/
def productAmbientGlaubermanCanonicalRightOWNormalCoordinate
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    ProductAmbientGlaubermanRightOWNormalCoordinate
      S C hcentral hgenerate g theta := by
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
  let eN :
      N ≃* N.map e.toMonoidHom :=
    N.equivMapOfInjective e.toMonoidHom e.injective
  let hmap :=
    productAmbientGlaubermanRightInertiaEquiv_map_normalCopy_eq_OWTarget
      S C hcentral hgenerate g theta
  refine
    { normalProductEquiv :=
        eN.trans (MulEquiv.subgroupCongr hmap)
      inclusion_commutes := ?_ }
  apply MonoidHom.ext
  intro n
  apply Subtype.ext
  rfl

/-- Transport the existing right inertia normal character to the internal
OW target normal product. -/
def productAmbientGlaubermanRightOWTargetExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (c :
      ProductAmbientGlaubermanRightOWNormalCoordinate
        S C hcentral hgenerate g theta) :
    IrreducibleCharacter
      (ProductAmbientGlaubermanLeftOWTargetNormalProduct
        S C hcentral hgenerate theta) := by
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    (inertiaCopyCharacter
      (internalProductNormalizer S C)
      (productAmbientGlaubermanRightKernelTransportCharacter
        S C hcentral g theta)).comap
      c.normalProductEquiv.symm

/-- The target extension in the canonical normal-product coordinate. -/
def productAmbientGlaubermanCanonicalRightOWTargetExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    IrreducibleCharacter
      (ProductAmbientGlaubermanLeftOWTargetNormalProduct
        S C hcentral hgenerate theta) :=
  productAmbientGlaubermanRightOWTargetExtension
    S C hcentral hgenerate g theta
    (productAmbientGlaubermanCanonicalRightOWNormalCoordinate
      S C hcentral hgenerate g theta)

/-- The genuinely character-theoretic target input left after all group
coordinates have been made canonical. -/
structure ProductAmbientGlaubermanCanonicalRightOWTargetExtensionInput
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
              S C hgenerate theta)) q) where
  /-- The transported right normal character extends the Glauberman
  correspondent for the copied kernel action. -/
  isExtension :
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
        S C hcentral hgenerate g theta)
  /-- The transported right normal character is invariant under the whole
  Sylow normalizer in `Γ_theta`. -/
  isInvariant :
    ∀ (a :
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
          S C hcentral hgenerate theta),
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
          S C hcentral hgenerate g theta).values x

/-- Relabel the internal OW target fibre as the existing matched
right-inertia fibre. -/
def productAmbientGlaubermanRightOWTargetFibreEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (c :
      ProductAmbientGlaubermanRightOWNormalCoordinate
        S C hcentral hgenerate g theta) :
    letI :
      (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
    IrreducibleCharactersOverAlong
        (ProductAmbientGlaubermanLeftOWTargetNormalProduct
          S C hcentral hgenerate theta).subtype
        (productAmbientGlaubermanRightOWTargetExtension
          S C hcentral hgenerate g theta c) ≃
      IrreducibleCharactersOverAlong
        (ProductAmbientGlaubermanRightNormalCopy
          S C hcentral hgenerate g theta).subtype
        (inertiaCopyCharacter
          (internalProductNormalizer S C)
          (productAmbientGlaubermanRightKernelTransportCharacter
            S C hcentral g theta)) := by
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let chi :=
    inertiaCopyCharacter
      (internalProductNormalizer S C)
      (productAmbientGlaubermanRightKernelTransportCharacter
        S C hcentral g theta)
  have hchar :
      (chi.comap c.normalProductEquiv.symm).comap
          c.normalProductEquiv =
        chi := by
    apply IrreducibleCharacter.ext
    funext x
    change
      chi.values
          (c.normalProductEquiv.symm
            (c.normalProductEquiv x)) =
        chi.values x
    rw [c.normalProductEquiv.symm_apply_apply]
  let E :=
    CliffordCorrespondence.irreducibleCharactersOverAlongComapEquiv
      (productAmbientGlaubermanRightInertiaEquivLeftSylowNormalizer
        S C hcentral hgenerate g theta)
      c.normalProductEquiv
      (ProductAmbientGlaubermanLeftOWTargetNormalProduct
        S C hcentral hgenerate theta).subtype
      (ProductAmbientGlaubermanRightNormalCopy
        S C hcentral hgenerate g theta).subtype
      c.inclusion_commutes
      (productAmbientGlaubermanRightOWTargetExtension
        S C hcentral hgenerate g theta c)
  change
    IrreducibleCharactersOverAlong
        (ProductAmbientGlaubermanLeftOWTargetNormalProduct
          S C hcentral hgenerate theta).subtype
        (chi.comap c.normalProductEquiv.symm) ≃
      IrreducibleCharactersOverAlong
        (ProductAmbientGlaubermanRightNormalCopy
          S C hcentral hgenerate g theta).subtype
        ((chi.comap c.normalProductEquiv.symm).comap
          c.normalProductEquiv) at E
  rw [hchar] at E
  change
    IrreducibleCharactersOverAlong
        (ProductAmbientGlaubermanLeftOWTargetNormalProduct
          S C hcentral hgenerate theta).subtype
        (chi.comap c.normalProductEquiv.symm) ≃
      IrreducibleCharactersOverAlong
        (ProductAmbientGlaubermanRightNormalCopy
          S C hcentral hgenerate g theta).subtype
        chi
  exact E

/-- Conditional ordinary count inside `Γ_theta`, with the source written in
the canonical normal-copy coordinate and the target still in the internal
Sylow-normalizer coordinate. -/
theorem productAmbientGlaubermanLeftOW_natCard_source_eq_internalTarget
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
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
          S C hcentral hgenerate theta))
    (beta :
      IrreducibleCharacter
        (ProductAmbientGlaubermanLeftOWTargetNormalProduct
          S C hcentral hgenerate theta))
    (hbetaExtension :
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
        beta)
    (hbetaInvariant :
      ∀ (a :
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
            S C hcentral hgenerate theta),
        beta.values
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
          beta.values x) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    Nat.card
        (IrreducibleCharactersOverAlong
          (inertiaNormalCopy (product S C) theta.1).subtype
          (productAmbientGlaubermanLeftInertiaTheta
            S C hgenerate theta).1) =
      Nat.card
        (IrreducibleCharactersOverAlong
          (ProductAmbientGlaubermanLeftOWTargetNormalProduct
            S C hcentral hgenerate theta).subtype
          beta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  calc
    Nat.card
        (IrreducibleCharactersOverAlong
          (inertiaNormalCopy (product S C) theta.1).subtype
          (productAmbientGlaubermanLeftInertiaTheta
            S C hgenerate theta).1) =
      Nat.card
        (IrreducibleCharactersOverAlong
          (ProductAmbientGlaubermanLeftOWSourceNormalProduct
            S C hcentral hgenerate theta).subtype
          (productAmbientGlaubermanLeftOWSourceExtension
            S C hcentral hgenerate theta)) :=
      Nat.card_congr
        (productAmbientGlaubermanLeftOWSourceFibreEquiv
          S C hcentral hgenerate theta)
    _ = Nat.card
        (IrreducibleCharactersOverAlong
          (ProductAmbientGlaubermanLeftOWTargetNormalProduct
            S C hcentral hgenerate theta).subtype
          beta) :=
      okuyamaWajima_natCard_over_eq_of_invariantExtensions
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
          S C hcentral hgenerate theta)
        (productAmbientGlaubermanLeftInertiaInvariantKernelCharacter_ambient
          S C hcentral hgenerate theta)
        how
        (productAmbientGlaubermanLeftOWSourceExtension
          S C hcentral hgenerate theta)
        beta
        (productAmbientGlaubermanLeftOWSourceExtension_isKernelExtension
          S C hcentral hgenerate theta)
        (productAmbientGlaubermanLeftOWSourceExtension_isInvariant
          S C hcentral hgenerate theta)
        hbetaExtension
        hbetaInvariant

/-- The exact per-character ordinary count, transported all the way to the
existing matched right-inertia normal-copy fibre. -/
theorem productAmbientGlaubermanLeftOW_natCard_eq_rightInertia
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
          S C hcentral hgenerate theta))
    (c :
      ProductAmbientGlaubermanRightOWNormalCoordinate
        S C hcentral hgenerate g theta)
    (hbetaExtension :
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
        (productAmbientGlaubermanRightOWTargetExtension
          S C hcentral hgenerate g theta c))
    (hbetaInvariant :
      ∀ (a :
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
            S C hcentral hgenerate theta),
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
            S C hcentral hgenerate g theta c).values x) :
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
              S C hcentral g theta))) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  calc
    Nat.card
        (IrreducibleCharactersOverAlong
          (inertiaNormalCopy (product S C) theta.1).subtype
          (productAmbientGlaubermanLeftInertiaTheta
            S C hgenerate theta).1) =
      Nat.card
        (IrreducibleCharactersOverAlong
          (ProductAmbientGlaubermanLeftOWTargetNormalProduct
            S C hcentral hgenerate theta).subtype
          (productAmbientGlaubermanRightOWTargetExtension
            S C hcentral hgenerate g theta c)) :=
      productAmbientGlaubermanLeftOW_natCard_source_eq_internalTarget
        S C hcentral hgenerate theta d how
        (productAmbientGlaubermanRightOWTargetExtension
          S C hcentral hgenerate g theta c)
        hbetaExtension hbetaInvariant
    _ = Nat.card
        (IrreducibleCharactersOverAlong
          (ProductAmbientGlaubermanRightNormalCopy
            S C hcentral hgenerate g theta).subtype
          (inertiaCopyCharacter
            (internalProductNormalizer S C)
            (productAmbientGlaubermanRightKernelTransportCharacter
              S C hcentral g theta))) :=
      Nat.card_congr
        (productAmbientGlaubermanRightOWTargetFibreEquiv
          S C hcentral hgenerate g theta c)

/-- Strongest canonical-coordinate form of the conditional per-character
ordinary count.  All group-coordinate data and the source extension have
been discharged; `targetInput` is precisely the remaining invariant target
extension assertion. -/
theorem
    productAmbientGlaubermanLeftOW_natCard_eq_rightInertia_canonical
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
          S C hcentral hgenerate theta))
    (targetInput :
      ProductAmbientGlaubermanCanonicalRightOWTargetExtensionInput
        S C hcentral hgenerate g theta d) :
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
              S C hcentral g theta))) := by
  exact
    productAmbientGlaubermanLeftOW_natCard_eq_rightInertia
      S C hcentral hgenerate g theta d how
      (productAmbientGlaubermanCanonicalRightOWNormalCoordinate
        S C hcentral hgenerate g theta)
      targetInput.isExtension targetInput.isInvariant

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
