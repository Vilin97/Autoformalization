/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.InvariantSubgroupAutomorphism
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionComplement

/-!
# Ambient-normalizer transport on the canonical `CP` source

Conjugation by `N_X(S)` preserves `CP = C ⊔ S`.  The canonical normal
`q′`-complement constructed inside `CP` is in fact the `q′`-core of `CP`,
so it is characteristic and is preserved by the induced automorphism.

This file constructs the resulting automorphisms of `CP`, its kernel, its
Sylow subgroup, and its quotient.  The inclusion and quotient-class formulas
are stated explicitly for later character-transport calculations.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace ComplementReduction

open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

omit [Finite X] [Fact q.Prime] in
/-- Every element normalizing `S` also normalizes `CP`. -/
theorem ambientNormalizer_le_normalizer_product :
    ambientNormalizer S ≤
      Subgroup.normalizer (product S C : Set X) := by
  have h :=
    Subgroup.normalizer_le_normalizer_sup_normal
      (G := X) (H := (S : Subgroup X)) (K := C)
  rw [sup_comm (S : Subgroup X) C] at h
  exact h

/-- The inclusion `N_X(S) → N_X(CP)`. -/
def ambientNormalizerToProductNormalizer :
    ambientNormalizer S →*
      Subgroup.normalizer (product S C : Set X) where
  toFun h :=
    ⟨h.1,
      ambientNormalizer_le_normalizer_product
        S C h.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Conjugation by `N_X(S)`, restricted to an automorphism of `CP`. -/
def productConjugationHom :
    ambientNormalizer S →*
      MulAut (product S C) :=
  (product S C).normalizerMonoidHom.comp
    (ambientNormalizerToProductNormalizer S C)

omit [Finite X] [Fact q.Prime] in
@[simp]
theorem productConjugation_apply_coe
    (h : ambientNormalizer S)
    (x : product S C) :
    ((productConjugationHom S C h x :
        product S C) : X) =
      (h : X) * (x : X) * (h : X)⁻¹ :=
  rfl

omit [Finite X] [Fact q.Prime] in
@[simp]
theorem productConjugation_symm_apply_coe
    (h : ambientNormalizer S)
    (x : product S C) :
    (((productConjugationHom S C h).symm x :
        product S C) : X) =
      (h : X)⁻¹ * (x : X) * (h : X) :=
  by
    have heq :
        (productConjugationHom S C h).symm =
          productConjugationHom S C h⁻¹ :=
      (map_inv (productConjugationHom S C) h).symm
    rw [heq, productConjugation_apply_coe]
    simp

omit [Finite X] [Fact q.Prime] in
/-- The restricted Sylow subgroup is invariant under the source
conjugation automorphism. -/
theorem productSylow_map_productConjugation
    (h : ambientNormalizer S) :
    (productSylow S C :
        Subgroup (product S C)).map
          (productConjugationHom S C h).toMonoidHom =
      (productSylow S C :
        Subgroup (product S C)) := by
  ext x
  rw [Subgroup.mem_map_equiv]
  change
    ((((productConjugationHom S C h).symm x :
        product S C) : X) ∈ S) ↔
      (x : X) ∈ S
  rw [productConjugation_symm_apply_coe]
  exact
    (Subgroup.mem_normalizer_iff''.mp
      h.2 (x : X)).symm

/-- The canonical complement inside `CP` is its full `q′`-core. -/
theorem productPPrimeKernel_eq_pPrimeCore
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    productPPrimeKernel S C hcentral =
      pPrimeCore q (product S C) := by
  let R :=
    productPPrimeKernel S C hcentral
  let P : Subgroup (product S C) :=
    productSylow S C
  have hRle :
      R ≤ pPrimeCore q (product S C) :=
    le_pPrimeCore
      (productPPrimeKernel_isPPrimeGroup
        S C hcentral)
      inferInstance
  apply le_antisymm hRle
  intro x hx
  have hxSup : x ∈ R ⊔ P := by
    rw [show R ⊔ P = ⊤ from
      productPPrimeKernel_sup_productSylow_eq_top
        S C hcentral]
    exact Subgroup.mem_top x
  obtain ⟨r, hr, s, hs, hrs⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hxSup
  have hrCore :
      r ∈ pPrimeCore q (product S C) :=
    hRle hr
  have hsCore :
      s ∈ pPrimeCore q (product S C) := by
    have hsEq : s = r⁻¹ * x := by
      rw [← hrs]
      group
    rw [hsEq]
    exact mul_mem (inv_mem hrCore) hx
  have hsOne : s = 1 :=
    Subgroup.disjoint_def.mp
      (IsPGroup.disjoint_of_isPPrimeGroup
        (productSylow S C).isPGroup'
        (pPrimeCore_isPPrimeGroup
          (p := q) (G := product S C)))
      hs hsCore
  rw [hsOne, mul_one] at hrs
  rw [← hrs]
  exact hr

/-- The canonical `q′`-kernel is characteristic in `CP`. -/
instance productPPrimeKernel_characteristic
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    (productPPrimeKernel S C hcentral).Characteristic := by
  rw [productPPrimeKernel_eq_pPrimeCore
    S C hcentral]
  infer_instance

/-- Source conjugation maps the canonical `q′`-kernel to itself. -/
theorem productPPrimeKernel_map_productConjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productPPrimeKernel S C hcentral).map
        (productConjugationHom S C h).toMonoidHom =
      productPPrimeKernel S C hcentral :=
  Subgroup.characteristic_iff_map_eq.mp
    (inferInstance :
      (productPPrimeKernel
        S C hcentral).Characteristic)
    (productConjugationHom S C h)

/-- The ambient-normalizer action on the characteristic `q′`-kernel. -/
def productPPrimeKernelConjugationHom
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    ambientNormalizer S →*
      MulAut (productPPrimeKernel S C hcentral) :=
  (MulAut.characteristic
      (productPPrimeKernel S C hcentral)).comp
    (productConjugationHom S C)

@[simp]
theorem productPPrimeKernelConjugation_apply_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (x : productPPrimeKernel S C hcentral) :
    ((productPPrimeKernelConjugationHom
        S C hcentral h x :
          productPPrimeKernel S C hcentral) :
        product S C) =
      productConjugationHom S C h x :=
  rfl

/-- Kernel conjugation commutes with the inclusion into `CP`. -/
theorem productPPrimeKernelConjugation_subtype_commutes
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productConjugationHom S C h).toMonoidHom.comp
        (productPPrimeKernel S C hcentral).subtype =
      (productPPrimeKernel S C hcentral).subtype.comp
        (productPPrimeKernelConjugationHom
          S C hcentral h).toMonoidHom := by
  ext x
  rfl

/-- The induced automorphism of the source quotient `CP/O_{q′}(CP)`. -/
def productPPrimeKernelQuotientConjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    MulAut
      ((product S C) ⧸
        productPPrimeKernel S C hcentral) :=
  quotientMulEquivOfSubgroupEquiv
    (productConjugationHom S C h)
    (productPPrimeKernelConjugationHom
      S C hcentral h)
    (productPPrimeKernelConjugation_subtype_commutes
      S C hcentral h)

@[simp]
theorem productPPrimeKernelQuotientConjugation_mk
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (x : product S C) :
    productPPrimeKernelQuotientConjugation
        S C hcentral h
        (QuotientGroup.mk'
          (productPPrimeKernel S C hcentral) x) =
      QuotientGroup.mk'
        (productPPrimeKernel S C hcentral)
        (productConjugationHom S C h x) :=
  quotientMulEquivOfSubgroupEquiv_mk
    (productConjugationHom S C h)
    (productPPrimeKernelConjugationHom
      S C hcentral h)
    (productPPrimeKernelConjugation_subtype_commutes
      S C hcentral h)
    x

/-- The induced automorphism of the restricted Sylow subgroup. -/
def productSylowConjugation
    (h : ambientNormalizer S) :
    MulAut
      (productSylow S C :
        Subgroup (product S C)) :=
  invariantSubgroupAutomorphism
    (productConjugationHom S C h)
    (productSylow S C :
      Subgroup (product S C))
    (productSylow_map_productConjugation
      S C h)

omit [Finite X] [Fact q.Prime] in
@[simp]
theorem productSylowConjugation_apply_coe
    (h : ambientNormalizer S)
    (x :
      (productSylow S C :
        Subgroup (product S C))) :
    ((productSylowConjugation S C h x :
        (productSylow S C :
          Subgroup (product S C))) :
      product S C) =
      productConjugationHom S C h x :=
  rfl

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
