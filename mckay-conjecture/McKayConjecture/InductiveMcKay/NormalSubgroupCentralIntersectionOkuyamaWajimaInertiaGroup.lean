/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InertiaCharacteristicCopy
import McKayConjecture.InductiveMcKay.InvariantCharacterInertiaNormalProduct
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanKernelCharacterStabilizer

/-!
# The kernel-character inertia group in the central-intersection reduction

Let `S` be Sylow in `X`, put `D = C S`, and let `R = O_{q'}(D)` be the
canonical complement constructed in the central-intersection reduction.
The canonical `S`-invariant character of `R` is transported to the ambient
copy of `R` in `X`.  Its full ambient inertia group is denoted below by
`productOkuyamaWajimaInertia`; mathematically this is the auxiliary group
`Δ_r = I_X(r)`.

This is deliberately different from both the inertia group of the original
character of `D` and the stabilizer of that original character inside
`N_X(S)`.

The file verifies the corresponding normal-product and Frattini facts in
`Δ_r`: the ambient copy of `S` is Sylow in `Δ_r`, the product of the
copied kernel and that Sylow subgroup is normal, and the kernel together
with the Sylow normalizer generates `Δ_r`.

For the per-character cardinality boundary, the operative OW ambient group
is the smaller extension-character inertia `Γ_θ = I_X(θ) ≤ Δ_r`, because
`θ` need not be `Δ_r`-invariant.  A later adapter copies the kernel into
`Γ_θ`; the two inertia groups must not be conflated.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace ComplementReduction

open CliffordEquivalence
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The canonical `q'`-kernel of `CS`, mapped to its literal ambient copy
inside `X`. -/
abbrev productAmbientPPrimeKernel
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    Subgroup X :=
  (productPPrimeKernel S C hcentral).map
    (product S C).subtype

/-- The identity-on-elements equivalence between the internal kernel of
`CS` and its ambient copy in `X`. -/
def productPPrimeKernelAmbientEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    productPPrimeKernel S C hcentral ≃*
      productAmbientPPrimeKernel S C hcentral :=
  (productPPrimeKernel S C hcentral).equivMapOfInjective
    (product S C).subtype
    (product S C).subtype_injective

@[simp]
theorem productPPrimeKernelAmbientEquiv_apply_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (x : productPPrimeKernel S C hcentral) :
    ((productPPrimeKernelAmbientEquiv S C hcentral x :
        productAmbientPPrimeKernel S C hcentral) : X) =
      ((x : product S C) : X) :=
  rfl

/-- Mapping the kernel--Sylow decomposition of `CS` into `X` recovers
the literal ambient subgroup `CS`. -/
theorem productAmbientPPrimeKernel_sup_sylow_eq_product
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    productAmbientPPrimeKernel S C hcentral ⊔
        (S : Subgroup X) =
      product S C := by
  have hmap :=
    congrArg
      (fun H : Subgroup (product S C) =>
        H.map (product S C).subtype)
      (productPPrimeKernel_sup_productSylow_eq_top
        S C hcentral)
  rw [Subgroup.map_sup,
    map_productSylow_subtype,
    ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at hmap
  exact hmap

/-- The ambient copy of the canonical kernel is normal in `X`: the kernel
is characteristic in the normal subgroup `CS`. -/
theorem productAmbientPPrimeKernel_normal
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤) :
    (productAmbientPPrimeKernel S C hcentral).Normal := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  change
    ((productPPrimeKernel S C hcentral).map
      (product S C).subtype).Normal
  infer_instance

/-- The canonical invariant kernel character, transported from its internal
copy in `CS` to the literal ambient copy in `X`. -/
def productAmbientGlaubermanKernelCharacterInX
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    PPrimeIrreducibleCharacter
      (productAmbientPPrimeKernel S C hcentral) q :=
  IrreducibleCharacter.pPrimeComapEquiv q
    (productPPrimeKernelAmbientEquiv S C hcentral).symm
    (productAmbientGlaubermanSourceKernelCharacter
      S C hcentral theta).1

@[simp]
theorem productAmbientGlaubermanKernelCharacterInX_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    (productAmbientGlaubermanKernelCharacterInX
      S C hcentral theta).1 =
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1.comap
        (productPPrimeKernelAmbientEquiv
          S C hcentral).symm :=
  rfl

/-- The ambient Sylow subgroup fixes the transported canonical kernel
character.  This is the key distinction between the full inertia group
defined below and a stabilizer taken only inside `N_X(S)`. -/
theorem sylow_le_inertia_productAmbientGlaubermanKernelCharacterInX
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (productAmbientPPrimeKernel S C hcentral).Normal :=
      productAmbientPPrimeKernel_normal
        S C hcentral hgenerate
    (S : Subgroup X) ≤
      IrreducibleCharacter.inertia
        (productAmbientPPrimeKernel S C hcentral)
        (productAmbientGlaubermanKernelCharacterInX
          S C hcentral theta).1 := by
  let K := productAmbientPPrimeKernel S C hcentral
  letI : K.Normal :=
    productAmbientPPrimeKernel_normal
      S C hcentral hgenerate
  let R := productPPrimeKernel S C hcentral
  let e : R ≃* K :=
    productPPrimeKernelAmbientEquiv S C hcentral
  let vartheta :=
    productAmbientGlaubermanSourceKernelCharacter
      S C hcentral theta
  intro s hs
  rw [IrreducibleCharacter.mem_inertia_iff]
  apply IrreducibleCharacter.ext
  funext k
  rw [IrreducibleCharacter.conjBy_values]
  change
    vartheta.1.1.values
        (e.symm ((MulAut.conjNormal s).symm k)) =
      vartheta.1.1.values (e.symm k)
  let sD : product S C :=
    ⟨s,
      (show
        (S : Subgroup X) ≤ product S C from
        le_sup_right) hs⟩
  have hsD :
      sD ∈
        (productSylow S C :
          Subgroup (product S C)) := by
    exact hs
  have hfix :
      IrreducibleCharacter.conjBy R sD vartheta.1.1 =
        vartheta.1.1 :=
    (IrreducibleCharacter.mem_inertia_iff
      R vartheta.1.1 sD).mp
      (vartheta.2 hsD)
  have hvalue :=
    congrArg
      (fun psi : IrreducibleCharacter R =>
        psi.values (e.symm k))
      hfix
  rw [IrreducibleCharacter.conjBy_values] at hvalue
  have hconj :
      e.symm ((MulAut.conjNormal s).symm k) =
        (MulAut.conjNormal sD).symm (e.symm k) := by
    apply e.injective
    apply Subtype.ext
    simp only [MulAut.conjNormal_symm_apply,
      e, K, R,
      productPPrimeKernelAmbientEquiv_apply_coe,
      MulEquiv.apply_symm_apply]
    have hk :
        (((e.symm k : R) : product S C) : X) =
          (k : X) := by
      calc
        (((e.symm k : R) : product S C) : X) =
            ((e (e.symm k) : K) : X) := rfl
        _ = (k : X) :=
          congrArg
            (fun z : K => (z : X))
            (e.apply_symm_apply k)
    change
      s⁻¹ * (k : X) * s =
        (sD : X)⁻¹ *
          (((e.symm k : R) : product S C) : X) *
          (sD : X)
    rw [hk]
  rw [hconj]
  exact hvalue

/-- The transported character together with its ambient `S`-invariance,
packaged in the form consumed by the generic inertia-normal-product API. -/
def productAmbientGlaubermanInvariantKernelCharacterInX
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (productAmbientPPrimeKernel S C hcentral).Normal :=
      productAmbientPPrimeKernel_normal
        S C hcentral hgenerate
    PInvariantPPrimeIrreducibleCharacter
      (productAmbientPPrimeKernel S C hcentral)
      (S : Subgroup X) q :=
  ⟨productAmbientGlaubermanKernelCharacterInX
      S C hcentral theta,
    sylow_le_inertia_productAmbientGlaubermanKernelCharacterInX
      S C hcentral hgenerate theta⟩

/-- The full inertia group in `X` of the transported canonical kernel
character.  In particular, this is not an inertia group formed in `CS` or
in `N_X(S)`. -/
abbrev productOkuyamaWajimaInertia
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    Subgroup X :=
  letI : (productAmbientPPrimeKernel S C hcentral).Normal :=
    productAmbientPPrimeKernel_normal
      S C hcentral hgenerate
  IrreducibleCharacter.inertia
    (productAmbientPPrimeKernel S C hcentral)
    (productAmbientGlaubermanKernelCharacterInX
      S C hcentral theta).1

/-- The ambient Sylow subgroup restricted to the full kernel-character
inertia group. -/
def productOkuyamaWajimaInertiaSylow
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    Sylow q
      (productOkuyamaWajimaInertia
        S C hcentral hgenerate theta) := by
  let K := productAmbientPPrimeKernel S C hcentral
  letI : K.Normal :=
    productAmbientPPrimeKernel_normal
      S C hcentral hgenerate
  exact
    invariantCharacterInertiaSylow K S
      (productAmbientGlaubermanInvariantKernelCharacterInX
        S C hcentral hgenerate theta)

@[simp]
theorem coe_productOkuyamaWajimaInertiaSylow
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    (productOkuyamaWajimaInertiaSylow
        S C hcentral hgenerate theta :
      Subgroup
        (productOkuyamaWajimaInertia
          S C hcentral hgenerate theta)) =
      (S : Subgroup X).subgroupOf
        (productOkuyamaWajimaInertia
          S C hcentral hgenerate theta) :=
  rfl

/-- The ambient kernel itself has order prime to `q`. -/
theorem productAmbientPPrimeKernel_isPPrimeGroup
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    IsPPrimeGroup q
      (productAmbientPPrimeKernel S C hcentral) :=
  (productPPrimeKernel_isPPrimeGroup
    S C hcentral).of_equiv
      (productPPrimeKernelAmbientEquiv
        S C hcentral)

/-- The canonical copy of the ambient kernel in its character inertia group
still has order prime to `q`. -/
theorem productOkuyamaWajimaInertiaKernel_isPPrimeGroup
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (productAmbientPPrimeKernel S C hcentral).Normal :=
      productAmbientPPrimeKernel_normal
        S C hcentral hgenerate
    IsPPrimeGroup q
      (inertiaNormalCopy
        (productAmbientPPrimeKernel S C hcentral)
        (productAmbientGlaubermanKernelCharacterInX
          S C hcentral theta).1) := by
  let K := productAmbientPPrimeKernel S C hcentral
  letI : K.Normal :=
    productAmbientPPrimeKernel_normal
      S C hcentral hgenerate
  let vartheta :=
    (productAmbientGlaubermanKernelCharacterInX
      S C hcentral theta).1
  have htop :
      IsPPrimeGroup q (⊤ : Subgroup K) :=
    (productAmbientPPrimeKernel_isPPrimeGroup
      S C hcentral).to_subgroup ⊤
  have hcopy :=
    inertiaSubgroupCopy_isPPrimeGroup
      K vartheta (⊤ : Subgroup K) htop
  rw [inertiaSubgroupCopy_top] at hcopy
  exact hcopy

/-- The kernel and the restricted Sylow subgroup generate the internal
copy of their ambient product inside the full inertia group. -/
theorem productOkuyamaWajimaInertia_normalProduct_eq
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (productAmbientPPrimeKernel S C hcentral).Normal :=
      productAmbientPPrimeKernel_normal
        S C hcentral hgenerate
    inertiaNormalCopy
          (productAmbientPPrimeKernel S C hcentral)
          (productAmbientGlaubermanKernelCharacterInX
            S C hcentral theta).1 ⊔
        (productOkuyamaWajimaInertiaSylow
          S C hcentral hgenerate theta :
          Subgroup
            (productOkuyamaWajimaInertia
              S C hcentral hgenerate theta)) =
      (product S C).subgroupOf
        (productOkuyamaWajimaInertia
          S C hcentral hgenerate theta) := by
  let K := productAmbientPPrimeKernel S C hcentral
  letI : K.Normal :=
    productAmbientPPrimeKernel_normal
      S C hcentral hgenerate
  let vartheta :=
    productAmbientGlaubermanInvariantKernelCharacterInX
      S C hcentral hgenerate theta
  rw [show product S C =
      K ⊔ (S : Subgroup X) from
    (productAmbientPPrimeKernel_sup_sylow_eq_product
      S C hcentral).symm]
  exact
    invariantCharacterInertia_normalProduct_eq
      K S vartheta

/-- The kernel--Sylow product is normal in the full kernel-character
inertia group. -/
theorem productOkuyamaWajimaInertia_normalProduct_normal
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (productAmbientPPrimeKernel S C hcentral).Normal :=
      productAmbientPPrimeKernel_normal
        S C hcentral hgenerate
    (inertiaNormalCopy
          (productAmbientPPrimeKernel S C hcentral)
          (productAmbientGlaubermanKernelCharacterInX
            S C hcentral theta).1 ⊔
        (productOkuyamaWajimaInertiaSylow
          S C hcentral hgenerate theta :
          Subgroup
            (productOkuyamaWajimaInertia
              S C hcentral hgenerate theta))).Normal := by
  let K := productAmbientPPrimeKernel S C hcentral
  letI : K.Normal :=
    productAmbientPPrimeKernel_normal
      S C hcentral hgenerate
  let vartheta :=
    productAmbientGlaubermanInvariantKernelCharacterInX
      S C hcentral hgenerate theta
  apply
    invariantCharacterInertia_normalProduct_normal
      K S vartheta
  rw [productAmbientPPrimeKernel_sup_sylow_eq_product
    S C hcentral]
  exact product_normal S C hgenerate

/-- Equivalent ambient-product form of
`productOkuyamaWajimaInertia_normalProduct_normal`. -/
theorem productOkuyamaWajimaInertia_product_normal
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    ((product S C).subgroupOf
      (productOkuyamaWajimaInertia
        S C hcentral hgenerate theta)).Normal := by
  rw [← productOkuyamaWajimaInertia_normalProduct_eq
    S C hcentral hgenerate theta]
  exact
    productOkuyamaWajimaInertia_normalProduct_normal
      S C hcentral hgenerate theta

/-- Frattini generation in the exact orientation required by the printed
Okuyama--Wajima theorem. -/
theorem productOkuyamaWajimaInertia_sup_normalizer_eq_top
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (productAmbientPPrimeKernel S C hcentral).Normal :=
      productAmbientPPrimeKernel_normal
        S C hcentral hgenerate
    inertiaNormalCopy
          (productAmbientPPrimeKernel S C hcentral)
          (productAmbientGlaubermanKernelCharacterInX
            S C hcentral theta).1 ⊔
        Subgroup.normalizer
          ((productOkuyamaWajimaInertiaSylow
            S C hcentral hgenerate theta :
            Subgroup
              (productOkuyamaWajimaInertia
                S C hcentral hgenerate theta)) :
            Set
              (productOkuyamaWajimaInertia
                S C hcentral hgenerate theta)) =
      ⊤ := by
  let K := productAmbientPPrimeKernel S C hcentral
  letI : K.Normal :=
    productAmbientPPrimeKernel_normal
      S C hcentral hgenerate
  let vartheta :=
    productAmbientGlaubermanInvariantKernelCharacterInX
      S C hcentral hgenerate theta
  apply
    invariantCharacterInertia_sup_normalizer_eq_top
      K S vartheta
  rw [productAmbientPPrimeKernel_sup_sylow_eq_product
    S C hcentral]
  exact product_normal S C hgenerate

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
