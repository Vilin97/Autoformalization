/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizerSourceTransport

/-!
# Ambient-normalizer transport on the local `CP` groups

The automorphism of `CP` induced by an element of `N_X(S)` preserves the
restricted Sylow subgroup.  It therefore preserves its normalizer, the
fixed-point subgroup of the canonical `q′`-kernel, and the internal local
kernel.  This file constructs all of those restricted automorphisms and the
automorphism of the local quotient.

The final commuting formulas identify every restricted map with the same
ambient conjugation.  They are the group-theoretic squares needed for
Glauberman and Gallagher covariance; no character-extension choices enter.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace ComplementReduction

open GroupTheory
open CentralIntersectionKernelAssembly

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The ambient fixed-point subgroup of the canonical kernel is invariant
under source conjugation. -/
theorem productPPrimeKernelFixedPoints_map_productConjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productPPrimeKernelFixedPoints
        S C hcentral).map
        (productConjugationHom S C h).toMonoidHom =
      productPPrimeKernelFixedPoints
        S C hcentral :=
  map_inf_centralizer_eq_of_map_eq
    (productConjugationHom S C h)
    (productPPrimeKernel S C hcentral)
    (productSylow S C :
      Subgroup (product S C))
    (productPPrimeKernel_map_productConjugation
      S C hcentral h)
    (productSylow_map_productConjugation
      S C h)

/-- Conjugation restricted to the ambient fixed-point group `C_R(S)`. -/
def productPPrimeKernelFixedPointsConjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    MulAut
      (productPPrimeKernelFixedPoints
        S C hcentral) :=
  invariantSubgroupAutomorphism
    (productConjugationHom S C h)
    (productPPrimeKernelFixedPoints
      S C hcentral)
    (productPPrimeKernelFixedPoints_map_productConjugation
      S C hcentral h)

@[simp]
theorem productPPrimeKernelFixedPointsConjugation_apply_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (x :
      productPPrimeKernelFixedPoints
        S C hcentral) :
    ((productPPrimeKernelFixedPointsConjugation
        S C hcentral h x :
          productPPrimeKernelFixedPoints
            S C hcentral) :
      product S C) =
      productConjugationHom S C h x :=
  rfl

/-- Fixed-point conjugation commutes with its inclusion into `CP`. -/
theorem productPPrimeKernelFixedPointsConjugation_subtype_commutes
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productConjugationHom S C h).toMonoidHom.comp
        (productPPrimeKernelFixedPoints
          S C hcentral).subtype =
      (productPPrimeKernelFixedPoints
          S C hcentral).subtype.comp
        (productPPrimeKernelFixedPointsConjugation
          S C hcentral h).toMonoidHom :=
  invariantSubgroupAutomorphism_subtype_commutes
    (productConjugationHom S C h)
    (productPPrimeKernelFixedPoints
      S C hcentral)
    (productPPrimeKernelFixedPoints_map_productConjugation
      S C hcentral h)

omit [Finite X] [Fact q.Prime] in
/-- Source conjugation maps the local Sylow normalizer to itself. -/
theorem productLocalNormalizer_map_productConjugation
    (h : ambientNormalizer S) :
    (Subgroup.normalizer
        (productSylow S C :
          Set (product S C))).map
        (productConjugationHom S C h).toMonoidHom =
      Subgroup.normalizer
        (productSylow S C :
          Set (product S C)) :=
  map_equiv_normalizer_eq_of_map_eq
    (productConjugationHom S C h)
    (productSylow S C :
      Subgroup (product S C))
    (productSylow_map_productConjugation
      S C h)

/-- Conjugation restricted to the local group `N_{CP}(S)`. -/
def productLocalNormalizerConjugation
    (h : ambientNormalizer S) :
    MulAut
      (localNormalizer
        (productSylow S C :
          Subgroup (product S C))) :=
  invariantSubgroupAutomorphism
    (productConjugationHom S C h)
    (Subgroup.normalizer
      (productSylow S C :
        Set (product S C)))
    (productLocalNormalizer_map_productConjugation
      S C h)

omit [Finite X] [Fact q.Prime] in
@[simp]
theorem productLocalNormalizerConjugation_apply_coe
    (h : ambientNormalizer S)
    (x :
      localNormalizer
        (productSylow S C :
          Subgroup (product S C))) :
    ((productLocalNormalizerConjugation S C h x :
        localNormalizer
          (productSylow S C :
            Subgroup (product S C))) :
      product S C) =
      productConjugationHom S C h x :=
  rfl

omit [Finite X] [Fact q.Prime] in
@[simp]
theorem productLocalNormalizerConjugation_symm_apply_coe
    (h : ambientNormalizer S)
    (x :
      localNormalizer
        (productSylow S C :
          Subgroup (product S C))) :
    (((productLocalNormalizerConjugation
        S C h).symm x :
          localNormalizer
            (productSylow S C :
              Subgroup (product S C))) :
      product S C) =
      (productConjugationHom S C h).symm x :=
  invariantSubgroupAutomorphism_symm_apply_coe
    (productConjugationHom S C h)
    (Subgroup.normalizer
      (productSylow S C :
        Set (product S C)))
    (productLocalNormalizer_map_productConjugation
      S C h)
    x

omit [Finite X] [Fact q.Prime] in
/-- Local-normalizer conjugation commutes with its inclusion into `CP`. -/
theorem productLocalNormalizerConjugation_subtype_commutes
    (h : ambientNormalizer S) :
    (productConjugationHom S C h).toMonoidHom.comp
        (localNormalizer
          (productSylow S C :
            Subgroup (product S C))).subtype =
      (localNormalizer
          (productSylow S C :
            Subgroup (product S C))).subtype.comp
        (productLocalNormalizerConjugation
          S C h).toMonoidHom :=
  invariantSubgroupAutomorphism_subtype_commutes
    (productConjugationHom S C h)
    (Subgroup.normalizer
      (productSylow S C :
        Set (product S C)))
    (productLocalNormalizer_map_productConjugation
      S C h)

/-- The internal local kernel `R ∩ N_{CP}(S)` is invariant under local
conjugation. -/
theorem productLocalKernel_map_productLocalNormalizerConjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))).map
        (productLocalNormalizerConjugation
          S C h).toMonoidHom =
      internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) := by
  let R :=
    productPPrimeKernel S C hcentral
  let P : Subgroup (product S C) :=
    productSylow S C
  let H :=
    localNormalizer P
  let e :=
    productConjugationHom S C h
  let eH :=
    productLocalNormalizerConjugation S C h
  have hR :
      R.map e.toMonoidHom = R :=
    productPPrimeKernel_map_productConjugation
      S C hcentral h
  ext x
  rw [Subgroup.mem_map_equiv]
  change
    (((eH.symm x : H) : product S C) ∈ R) ↔
      ((x : H) : product S C) ∈ R
  rw [show
    ((eH.symm x : H) : product S C) =
      e.symm ((x : H) : product S C) from
        productLocalNormalizerConjugation_symm_apply_coe
          S C h x]
  have hmem :
      ((x : H) : product S C) ∈
          R.map e.toMonoidHom ↔
        e.symm ((x : H) : product S C) ∈ R :=
    Subgroup.mem_map_equiv
  rw [hR] at hmem
  exact hmem.symm

/-- Conjugation restricted to the internal local kernel. -/
def productLocalKernelConjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    MulAut
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))) :=
  invariantSubgroupAutomorphism
    (productLocalNormalizerConjugation S C h)
    (internalKernelNormalizer
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C)))
    (productLocalKernel_map_productLocalNormalizerConjugation
      S C hcentral h)

@[simp]
theorem productLocalKernelConjugation_apply_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (x :
      internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))) :
    ((productLocalKernelConjugation
        S C hcentral h x :
          internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C))) :
      localNormalizer
        (productSylow S C :
          Subgroup (product S C))) =
      productLocalNormalizerConjugation S C h x :=
  rfl

/-- Local-kernel conjugation commutes with its inclusion in the local
normalizer. -/
theorem productLocalKernelConjugation_subtype_commutes
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productLocalNormalizerConjugation
        S C h).toMonoidHom.comp
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))).subtype =
      (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))).subtype.comp
        (productLocalKernelConjugation
          S C hcentral h).toMonoidHom :=
  invariantSubgroupAutomorphism_subtype_commutes
    (productLocalNormalizerConjugation S C h)
    (internalKernelNormalizer
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C)))
    (productLocalKernel_map_productLocalNormalizerConjugation
      S C hcentral h)

/-- The induced automorphism of the local quotient
`N_{CP}(S)/C_R(S)`. -/
def productLocalKernelQuotientConjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    MulAut
      (localNormalizer
          (productSylow S C :
            Subgroup (product S C)) ⧸
        internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) :=
  quotientMulEquivOfSubgroupEquiv
    (productLocalNormalizerConjugation S C h)
    (productLocalKernelConjugation
      S C hcentral h)
    (productLocalKernelConjugation_subtype_commutes
      S C hcentral h)

@[simp]
theorem productLocalKernelQuotientConjugation_mk
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (x :
      localNormalizer
        (productSylow S C :
          Subgroup (product S C))) :
    productLocalKernelQuotientConjugation
        S C hcentral h
        (QuotientGroup.mk'
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))
          x) =
      QuotientGroup.mk'
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))
        (productLocalNormalizerConjugation
          S C h x) :=
  quotientMulEquivOfSubgroupEquiv_mk
    (productLocalNormalizerConjugation S C h)
    (productLocalKernelConjugation
      S C hcentral h)
    (productLocalKernelConjugation_subtype_commutes
      S C hcentral h)
    x

/-- The canonical identification of the internal local kernel with the
ambient fixed-point subgroup intertwines the two conjugation maps. -/
theorem localKernelAmbientFixedPointsEquiv_conjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (x :
      internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))) :
    localKernelAmbientFixedPointsEquiv
        S C hcentral
        (productLocalKernelConjugation
          S C hcentral h x) =
      productPPrimeKernelFixedPointsConjugation
        S C hcentral h
        (localKernelAmbientFixedPointsEquiv
          S C hcentral x) := by
  apply Subtype.ext
  rfl

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
