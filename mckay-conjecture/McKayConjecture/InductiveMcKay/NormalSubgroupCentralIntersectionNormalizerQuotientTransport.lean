/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizedExtension
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizerLocalTransport

/-!
# Ambient-normalizer transport on the source and local quotients

The canonical identification

`N_{CP}(S) / C_R(S) ≃ CP / R`

sends the class of a local element to the class of the same element in
`CP`.  Consequently it intertwines the quotient automorphisms induced by
every element of `N_X(S)`.  Precomposition therefore transports
multiplicative linear characters equivariantly.
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

/-- The canonical local-to-source quotient equivalence is induced by the
literal inclusion of the local normalizer into `CP`. -/
@[simp]
theorem productLocalSourceQuotientEquiv_mk
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (x :
      localNormalizer
        (productSylow S C :
          Subgroup (product S C))) :
    productLocalSourceQuotientEquiv S C hcentral
        (QuotientGroup.mk'
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))
          x) =
      QuotientGroup.mk'
        (productPPrimeKernel S C hcentral)
        (x : product S C) := by
  let K :=
    productPPrimeKernel S C hcentral
  let P : Subgroup (product S C) :=
    productSylow S C
  let H :=
    localNormalizer P
  let KN : Subgroup H :=
    internalKernelNormalizer K P
  let PN : Subgroup H :=
    internalPNormalizer P
  let s : P :=
    productSylowCoordinate S C hcentral (x : product S C)
  let sH : PN :=
    ⟨⟨s, Subgroup.le_normalizer s.2⟩, s.2⟩
  have hsourceClass :
      QuotientGroup.mk' K (x : product S C) =
        QuotientGroup.mk' K (s : product S C) := by
    rw [← productKernelCoordinate_mul_productSylowCoordinate
      S C hcentral (x : product S C)]
    rw [map_mul]
    change
      QuotientGroup.mk' K
          (productKernelCoordinate S C hcentral
            (x : product S C) : product S C) *
          QuotientGroup.mk' K (s : product S C) =
        QuotientGroup.mk' K (s : product S C)
    have hkernelClass :
        QuotientGroup.mk' K
            (productKernelCoordinate S C hcentral
              (x : product S C) : product S C) =
          1 :=
      (QuotientGroup.eq_one_iff _).mpr
        (productKernelCoordinate S C hcentral
          (x : product S C)).2
    rw [hkernelClass, one_mul]
  have hlocalClass :
      QuotientGroup.mk' KN x =
        QuotientGroup.mk' KN (sH : H) := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hkambient :
        (x : product S C) * (s : product S C)⁻¹ ∈ K := by
      have hdecomp :=
        productKernelCoordinate_mul_productSylowCoordinate
          S C hcentral (x : product S C)
      have heq :
          (x : product S C) * (s : product S C)⁻¹ =
            (productKernelCoordinate S C hcentral
              (x : product S C) : product S C) := by
        calc
          (x : product S C) * (s : product S C)⁻¹ =
              ((productKernelCoordinate S C hcentral
                  (x : product S C) : product S C) *
                (s : product S C)) *
                (s : product S C)⁻¹ := by
            rw [hdecomp]
          _ =
              (productKernelCoordinate S C hcentral
                (x : product S C) : product S C) := by
            group
      rw [heq]
      exact
        (productKernelCoordinate S C hcentral
          (x : product S C)).2
    rw [show KN = K.subgroupOf H from rfl,
      Subgroup.mem_subgroupOf]
    have hcoediv :
        (((x / (sH : H) : H) : product S C)) =
          (x : product S C) *
            (s : product S C)⁻¹ := by
      change
        (x : product S C) / (s : product S C) =
          (x : product S C) * (s : product S C)⁻¹
      exact div_eq_mul_inv _ _
    rw [hcoediv]
    exact hkambient
  rw [hlocalClass, hsourceClass]
  change
    ((productLocalQuotientSylowEquiv S C hcentral).trans
      (productSourceQuotientSylowEquiv S C hcentral).symm)
        (QuotientGroup.mk' KN (sH : H)) =
      QuotientGroup.mk' K (s : product S C)
  have hlocal :
      productLocalQuotientSylowEquiv S C hcentral
          (QuotientGroup.mk' KN (sH : H)) =
        s := by
    let hPN : IsPGroup q PN :=
      (productSylow S C).isPGroup'.of_equiv
        (Subgroup.subgroupOfEquivOfLe
          (show P ≤ localNormalizer P from
            Subgroup.le_normalizer)).symm
    let hdisjoint : Disjoint PN KN :=
      GroupTheory.IsPGroup.disjoint_of_isPPrimeGroup
        hPN (productLocalKernel_isPPrimeGroup
          S C hcentral)
    let hsup : KN ⊔ PN = ⊤ :=
      internalKernelNormalizer_sup_internalP_eq_top
        K P
        (productPPrimeKernel_sup_productSylow_eq_top
          S C hcentral)
    have hfirst :
        GroupTheory.normalComplementQuotientEquiv
            KN PN hdisjoint hsup
            (QuotientGroup.mk' KN (sH : H)) =
          sH :=
      (GroupTheory.normalComplementQuotientEquiv
        KN PN hdisjoint hsup).apply_symm_apply sH
    change
      ((GroupTheory.normalComplementQuotientEquiv
          KN PN hdisjoint hsup).trans
        (Subgroup.subgroupOfEquivOfLe
          (show P ≤ localNormalizer P from
            Subgroup.le_normalizer)))
          (QuotientGroup.mk' KN (sH : H)) =
        s
    rw [MulEquiv.trans_apply, hfirst]
    rfl
  rw [MulEquiv.trans_apply, hlocal]
  rfl

/-- Elementwise naturality of the local-to-source quotient equivalence
under ambient-normalizer conjugation. -/
theorem productLocalSourceQuotientEquiv_conjugation_apply
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (x :
      localNormalizer
          (productSylow S C :
            Subgroup (product S C)) ⧸
        internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) :
    productLocalSourceQuotientEquiv S C hcentral
        (productLocalKernelQuotientConjugation
          S C hcentral h x) =
      productPPrimeKernelQuotientConjugation
        S C hcentral h
        (productLocalSourceQuotientEquiv
          S C hcentral x) := by
  refine Quotient.inductionOn' x ?_
  intro y
  change
    productLocalSourceQuotientEquiv S C hcentral
        (productLocalKernelQuotientConjugation
          S C hcentral h
          (QuotientGroup.mk'
            (internalKernelNormalizer
              (productPPrimeKernel S C hcentral)
              (productSylow S C :
                Subgroup (product S C)))
            y)) =
      productPPrimeKernelQuotientConjugation
        S C hcentral h
        (productLocalSourceQuotientEquiv
          S C hcentral
          (QuotientGroup.mk'
            (internalKernelNormalizer
              (productPPrimeKernel S C hcentral)
              (productSylow S C :
                Subgroup (product S C)))
            y))
  rw [productLocalKernelQuotientConjugation_mk,
    productLocalSourceQuotientEquiv_mk,
    productLocalSourceQuotientEquiv_mk,
    productPPrimeKernelQuotientConjugation_mk]
  congr 1

/-- Equivalence-level naturality of the local-to-source quotient
identification under ambient-normalizer conjugation. -/
theorem productLocalSourceQuotientEquiv_conjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productLocalKernelQuotientConjugation
        S C hcentral h).trans
        (productLocalSourceQuotientEquiv
          S C hcentral) =
      (productLocalSourceQuotientEquiv
        S C hcentral).trans
        (productPPrimeKernelQuotientConjugation
          S C hcentral h) := by
  ext x
  exact
    productLocalSourceQuotientEquiv_conjugation_apply
      S C hcentral h x

/-- Transport of multiplicative quotient characters commutes with
precomposition by the induced quotient conjugations. -/
theorem productLinearQuotientEquiv_comp_conjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (lam :
      ((product S C) ⧸
        productPPrimeKernel S C hcentral) →* ℂˣ) :
    productLinearQuotientEquiv S C hcentral
        (lam.comp
          (productPPrimeKernelQuotientConjugation
            S C hcentral h).toMonoidHom) =
      (productLinearQuotientEquiv
        S C hcentral lam).comp
          (productLocalKernelQuotientConjugation
            S C hcentral h).toMonoidHom := by
  apply DFunLike.ext _ _
  intro x
  change
    lam
        (productPPrimeKernelQuotientConjugation
          S C hcentral h
          (productLocalSourceQuotientEquiv
            S C hcentral x)) =
      lam
        (productLocalSourceQuotientEquiv
          S C hcentral
          (productLocalKernelQuotientConjugation
            S C hcentral h x))
  exact congrArg lam
    (productLocalSourceQuotientEquiv_conjugation_apply
      S C hcentral h x).symm

/-- Elementwise inverse naturality of the local-to-source quotient
equivalence. -/
theorem productLocalSourceQuotientEquiv_conjugation_symm_apply
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (x :
      localNormalizer
          (productSylow S C :
            Subgroup (product S C)) ⧸
        internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) :
    productLocalSourceQuotientEquiv S C hcentral
        ((productLocalKernelQuotientConjugation
          S C hcentral h).symm x) =
      (productPPrimeKernelQuotientConjugation
        S C hcentral h).symm
        (productLocalSourceQuotientEquiv
          S C hcentral x) := by
  apply
    (productPPrimeKernelQuotientConjugation
      S C hcentral h).injective
  rw [(productPPrimeKernelQuotientConjugation
      S C hcentral h).apply_symm_apply]
  rw [← productLocalSourceQuotientEquiv_conjugation_apply
    S C hcentral h]
  rw [(productLocalKernelQuotientConjugation
      S C hcentral h).apply_symm_apply]

/-- Inverse-conjugation form of quotient-character covariance, matching
the contragredient convention for automorphism actions on characters. -/
theorem productLinearQuotientEquiv_comp_conjugation_symm
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (lam :
      ((product S C) ⧸
        productPPrimeKernel S C hcentral) →* ℂˣ) :
    productLinearQuotientEquiv S C hcentral
        (lam.comp
          (productPPrimeKernelQuotientConjugation
            S C hcentral h).symm.toMonoidHom) =
      (productLinearQuotientEquiv
        S C hcentral lam).comp
          (productLocalKernelQuotientConjugation
            S C hcentral h).symm.toMonoidHom := by
  apply DFunLike.ext _ _
  intro x
  change
    lam
        ((productPPrimeKernelQuotientConjugation
          S C hcentral h).symm
          (productLocalSourceQuotientEquiv
            S C hcentral x)) =
      lam
        (productLocalSourceQuotientEquiv
          S C hcentral
          ((productLocalKernelQuotientConjugation
            S C hcentral h).symm x))
  exact congrArg lam
    (productLocalSourceQuotientEquiv_conjugation_symm_apply
      S C hcentral h x).symm

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
