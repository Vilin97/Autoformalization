/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizedExtension

/-!
# The normalized Gallagher fibre correspondence

The determinant-normalized local extension constructed in
`NormalSubgroupCentralIntersectionNormalizedExtension` is used as the
local base point for Gallagher correspondence.  Transporting the same
linear quotient parameter on the source and local sides then preserves
normalized values on ambient-central elements throughout the entire
inertia fibre.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace ComplementReduction

open CliffordCorrespondence
open CliffordPartition
open CentralIntersectionKernelAssembly
open NormalPPrimeKernelGlauberman

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

noncomputable local instance productNormalizedFibreFintype :
    Fintype (product S C) :=
  Fintype.ofFinite (product S C)

noncomputable local instance productNormalizedFibreLocalFintype :
    Fintype
      (localNormalizer
        (productSylow S C :
          Subgroup (product S C))) :=
  Fintype.ofFinite _

/-- The common quotient identification sends the local and source
classes of an ambient-central element to one another. -/
theorem productLocalSourceQuotientEquiv_mk_central
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (z : product S C)
    (hz : z ∈ Subgroup.center (product S C)) :
    productLocalSourceQuotientEquiv S C hcentral
        (QuotientGroup.mk'
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))
          ⟨z,
            Subgroup.center_le_normalizer
              (productSylow S C :
                Set (product S C)) hz⟩) =
      QuotientGroup.mk'
        (productPPrimeKernel S C hcentral) z := by
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
    productSylowCoordinate S C hcentral z
  let sH : PN :=
    ⟨⟨s, Subgroup.le_normalizer s.2⟩, s.2⟩
  have hsourceClass :
      QuotientGroup.mk' K z =
        QuotientGroup.mk' K (s : product S C) := by
    rw [← productKernelCoordinate_mul_productSylowCoordinate
      S C hcentral z]
    rw [map_mul]
    change
      QuotientGroup.mk' K
          (productKernelCoordinate S C hcentral z :
            product S C) *
          QuotientGroup.mk' K (s : product S C) =
        QuotientGroup.mk' K (s : product S C)
    have hkernelClass :
        QuotientGroup.mk' K
            (productKernelCoordinate S C hcentral z :
              product S C) =
          1 :=
      (QuotientGroup.eq_one_iff _).mpr
        (productKernelCoordinate S C hcentral z).2
    rw [hkernelClass, one_mul]
  have hlocalClass :
      QuotientGroup.mk' KN
          ⟨z,
            Subgroup.center_le_normalizer
              (P : Set (product S C)) hz⟩ =
        QuotientGroup.mk' KN (sH : H) := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hkambient :
        z * (s : product S C)⁻¹ ∈ K := by
      have hdecomp :=
        productKernelCoordinate_mul_productSylowCoordinate
          S C hcentral z
      have heq :
          z * (s : product S C)⁻¹ =
            (productKernelCoordinate
              S C hcentral z : product S C) := by
        calc
          z * (s : product S C)⁻¹ =
              ((productKernelCoordinate
                  S C hcentral z : product S C) *
                (s : product S C)) *
                (s : product S C)⁻¹ :=
            congrArg
              (fun t : product S C ↦
                t * (s : product S C)⁻¹)
              hdecomp.symm
          _ =
              (productKernelCoordinate
                S C hcentral z : product S C) := by
            group
      rw [heq]
      exact
        (productKernelCoordinate S C hcentral z).2
    rw [show KN = K.subgroupOf H from rfl,
      Subgroup.mem_subgroupOf]
    have hcoediv :
        (((⟨z,
              Subgroup.center_le_normalizer
                (P : Set (product S C)) hz⟩ : H) /
            (sH : H) : H) : product S C) =
          z * (s : product S C)⁻¹ := by
      simp [sH, div_eq_mul_inv]
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
        hPN (productLocalKernel_isPPrimeGroup S C hcentral)
    let hsup : KN ⊔ PN = ⊤ :=
      internalKernelNormalizer_sup_internalP_eq_top
        K P
        (productPPrimeKernel_sup_productSylow_eq_top
          S C hcentral)
    have hfirst :
        GroupTheory.normalComplementQuotientEquiv
            KN PN hdisjoint hsup
            (QuotientGroup.mk' KN (sH : H)) =
          sH := by
      exact
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

/-- Gallagher coordinates on the local ambient fibre, based at the
determinant-normalized extension. -/
def productNormalizedLocalAmbientGallagherEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    ((localNormalizer
          (productSylow S C :
            Subgroup (product S C)) ⧸
        internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) →* ℂˣ) ≃
      PPrimeIrreducibleCharactersOverAlong
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))).subtype
        (((productGlaubermanActiveOrbitEquiv
            S C hcentral g a r).pPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))).1) q :=
  IrreducibleCharacter.gallagherLinearCorrespondenceOfPGroupQuotient
    (internalKernelNormalizer
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C)))
    (localNormalizer_quotient_internalKernel_isPGroup
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C))
      (productPPrimeKernelCentralIntersectionSetup
        S C hcentral).pSubgroup
      (productPPrimeKernelCentralIntersectionSetup
        S C hcentral).generate)
    (productNormalizedLocalExtension_isExtension
      S C hcentral g a r)
    ((productGlaubermanActiveOrbitEquiv
      S C hcentral g a r).pPrimeOut
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))).2

/-- Evaluation of the source Gallagher character in multiplicative-linear
coordinates. -/
theorem productSourceAmbientGallagherEquiv_values
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (lam :
      ((product S C) ⧸
        productPPrimeKernel S C hcentral) →* ℂˣ)
    (z : product S C) :
    ((productSourceAmbientGallagherEquiv
        S C hcentral r lam).1.1.values z) =
      (productSourcePPrimeExtension
        S C hcentral r).1.values z *
        (lam
          (QuotientGroup.mk'
            (productPPrimeKernel S C hcentral) z) : ℂ) := by
  change
    (IrreducibleCharacter.gallagherTensorCharacter
        (productSourcePPrimeExtension_isExtension
          S C hcentral r)
        (IrreducibleCharacter.linear lam)).values z =
      _
  rw [IrreducibleCharacter.gallagherTensorCharacter_values,
    IrreducibleCharacter.linear_values]

/-- Every source Gallagher twist has the same degree as its base
extension because the quotient parameter is linear. -/
theorem productSourceAmbientGallagherEquiv_degree
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (lam :
      ((product S C) ⧸
        productPPrimeKernel S C hcentral) →* ℂˣ) :
    ((productSourceAmbientGallagherEquiv
        S C hcentral r lam).1.1.degree) =
      (productSourcePPrimeExtension
        S C hcentral r).1.degree := by
  change
    (IrreducibleCharacter.gallagherTensorCharacter
        (productSourcePPrimeExtension_isExtension
          S C hcentral r)
        (IrreducibleCharacter.linear lam)).degree =
      _
  rw [IrreducibleCharacter.gallagherTensorCharacter_degree,
    IrreducibleCharacter.linear_degree, mul_one]

/-- Evaluation of the normalized local Gallagher character in
multiplicative-linear coordinates. -/
theorem productNormalizedLocalAmbientGallagherEquiv_values
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (mu :
      (localNormalizer
          (productSylow S C :
            Subgroup (product S C)) ⧸
        internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) →* ℂˣ)
    (h :
      localNormalizer
        (productSylow S C :
          Subgroup (product S C))) :
    ((productNormalizedLocalAmbientGallagherEquiv
        S C hcentral g a r mu).1.1.values h) =
      (productNormalizedLocalExtension
        S C hcentral g a r).1.values h *
        (mu
          (QuotientGroup.mk'
            (internalKernelNormalizer
              (productPPrimeKernel S C hcentral)
              (productSylow S C :
                Subgroup (product S C))) h) : ℂ) := by
  change
    (IrreducibleCharacter.gallagherTensorCharacter
        (productNormalizedLocalExtension_isExtension
          S C hcentral g a r)
        (IrreducibleCharacter.linear mu)).values h =
      _
  rw [IrreducibleCharacter.gallagherTensorCharacter_values,
    IrreducibleCharacter.linear_values]

/-- Every normalized local Gallagher twist has the degree of its base
extension. -/
theorem productNormalizedLocalAmbientGallagherEquiv_degree
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (mu :
      (localNormalizer
          (productSylow S C :
            Subgroup (product S C)) ⧸
        internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) →* ℂˣ) :
    ((productNormalizedLocalAmbientGallagherEquiv
        S C hcentral g a r mu).1.1.degree) =
      (productNormalizedLocalExtension
        S C hcentral g a r).1.degree := by
  change
    (IrreducibleCharacter.gallagherTensorCharacter
        (productNormalizedLocalExtension_isExtension
          S C hcentral g a r)
        (IrreducibleCharacter.linear mu)).degree =
      _
  rw [IrreducibleCharacter.gallagherTensorCharacter_degree,
    IrreducibleCharacter.linear_degree, mul_one]

/-- Gallagher twisting by the transported quotient-linear character
preserves the normalized central-value identity. -/
theorem productNormalizedAmbientGallagher_central_cross
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (lam :
      ((product S C) ⧸
        productPPrimeKernel S C hcentral) →* ℂˣ)
    (z : product S C)
    (hz : z ∈ Subgroup.center (product S C)) :
    ((productSourceAmbientGallagherEquiv
        S C hcentral r lam).1.1.values z) *
        (((productNormalizedLocalAmbientGallagherEquiv
          S C hcentral g a r
          (productLinearQuotientEquiv
            S C hcentral lam)).1.1.degree : ℂ)) =
      ((productNormalizedLocalAmbientGallagherEquiv
        S C hcentral g a r
        (productLinearQuotientEquiv
          S C hcentral lam)).1.1.values
          ⟨z,
            Subgroup.center_le_normalizer
              (productSylow S C :
                Set (product S C)) hz⟩) *
        (((productSourceAmbientGallagherEquiv
          S C hcentral r lam).1.1.degree : ℂ)) := by
  let zH :
      localNormalizer
        (productSylow S C :
          Subgroup (product S C)) :=
    ⟨z,
      Subgroup.center_le_normalizer
        (productSylow S C :
          Set (product S C)) hz⟩
  let mu :=
    productLinearQuotientEquiv
      S C hcentral lam
  have hparameter :
      (mu
          (QuotientGroup.mk'
            (internalKernelNormalizer
              (productPPrimeKernel S C hcentral)
              (productSylow S C :
                Subgroup (product S C))) zH) : ℂ) =
        (lam
          (QuotientGroup.mk'
            (productPPrimeKernel S C hcentral) z) : ℂ) := by
    change
      (lam
          (productLocalSourceQuotientEquiv
            S C hcentral
            (QuotientGroup.mk'
              (internalKernelNormalizer
                (productPPrimeKernel S C hcentral)
                (productSylow S C :
                  Subgroup (product S C))) zH)) : ℂ) =
        _
    rw [productLocalSourceQuotientEquiv_mk_central
      S C hcentral z hz]
  have hbase :=
    productNormalizedExtensions_central_cross
      S C hcentral g a r z hz
  change
    ((productSourceAmbientGallagherEquiv
        S C hcentral r lam).1.1.values z) *
        (((productNormalizedLocalAmbientGallagherEquiv
          S C hcentral g a r mu).1.1.degree : ℂ)) =
      ((productNormalizedLocalAmbientGallagherEquiv
        S C hcentral g a r mu).1.1.values zH) *
        (((productSourceAmbientGallagherEquiv
          S C hcentral r lam).1.1.degree : ℂ))
  rw [productSourceAmbientGallagherEquiv_values,
    productNormalizedLocalAmbientGallagherEquiv_values,
    productSourceAmbientGallagherEquiv_degree,
    productNormalizedLocalAmbientGallagherEquiv_degree,
    hparameter]
  calc
    ((productSourcePPrimeExtension
        S C hcentral r).1.values z *
          (lam
            (QuotientGroup.mk'
              (productPPrimeKernel S C hcentral) z) : ℂ)) *
        ((productNormalizedLocalExtension
          S C hcentral g a r).1.degree : ℂ) =
      ((productSourcePPrimeExtension
        S C hcentral r).1.values z *
        ((productNormalizedLocalExtension
          S C hcentral g a r).1.degree : ℂ)) *
          (lam
            (QuotientGroup.mk'
              (productPPrimeKernel S C hcentral) z) : ℂ) := by
      ring
    _ =
      ((productNormalizedLocalExtension
        S C hcentral g a r).1.values zH *
        ((productSourcePPrimeExtension
          S C hcentral r).1.degree : ℂ)) *
          (lam
            (QuotientGroup.mk'
              (productPPrimeKernel S C hcentral) z) : ℂ) := by
      rw [hbase]
    _ =
      ((productNormalizedLocalExtension
        S C hcentral g a r).1.values zH *
          (lam
            (QuotientGroup.mk'
              (productPPrimeKernel S C hcentral) z) : ℂ)) *
        ((productSourcePPrimeExtension
          S C hcentral r).1.degree : ℂ) := by
      ring

/-- The normalized Okuyama--Wajima inertia-fibre equivalence. -/
def productNormalizedOkuyamaWajimaInertiaFibreEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    PPrimeIrreducibleCharactersOverInertia
        (productPPrimeKernel S C hcentral)
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral)).1 q ≃
      PPrimeIrreducibleCharactersOverInertia
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))
        (((productGlaubermanActiveOrbitEquiv
            S C hcentral g a r).pPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))).1) q :=
  (pPrimeIrreducibleCharactersOverInertiaEquivAmbient
      (productPPrimeKernel S C hcentral)
      (r.pPrimeOut
        (productPPrimeKernel S C hcentral)).1
      ((productPPrimeKernelCentralIntersectionSetup
        S C hcentral).activeKernel_inertia_eq_top
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))
          (r.pPrimeOut
            (productPPrimeKernel S C hcentral))
          (activePPrimeOut
            (productPPrimeKernel S C hcentral) r).2)
      q).trans <|
    (productSourceAmbientGallagherEquiv
      S C hcentral r).symm |>.trans <|
    (productLinearQuotientEquiv
      S C hcentral) |>.trans <|
    (productNormalizedLocalAmbientGallagherEquiv
      S C hcentral g a r) |>.trans <|
    (pPrimeIrreducibleCharactersOverInertiaEquivAmbient
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)))
      (((productGlaubermanActiveOrbitEquiv
          S C hcentral g a r).pPrimeOut
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))).1)
      ((productPPrimeKernelCentralIntersectionSetup
        S C hcentral).activeLocalKernel_inertia_eq_top
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))
          ((productGlaubermanActiveOrbitEquiv
            S C hcentral g a r).pPrimeOut
              (internalKernelNormalizer
                (productPPrimeKernel S C hcentral)
                (productSylow S C :
                  Subgroup (product S C))))
          (activePPrimeOut
            (internalKernelNormalizer
              (productPPrimeKernel S C hcentral)
              (productSylow S C :
                Subgroup (product S C)))
            (productGlaubermanActiveOrbitEquiv
              S C hcentral g a r)).2)
      q).symm

/-- The normalized Gallagher construction proves the central
Okuyama--Wajima identity on every inertia fibre. -/
theorem productNormalizedOkuyamaWajimaInertiaFibreEquiv_central_cross
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (rho :
      PPrimeIrreducibleCharactersOverInertia
        (productPPrimeKernel S C hcentral)
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral)).1 q)
    (z : product S C)
    (hz : z ∈ Subgroup.center (product S C)) :
    rho.1.1.values
        ((productPPrimeKernelCentralIntersectionSetup
          S C hcentral).kernelInertiaElement
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C))
            r z) *
        (((productNormalizedOkuyamaWajimaInertiaFibreEquiv
          S C hcentral g a r rho).1.1.degree : ℂ)) =
      (productNormalizedOkuyamaWajimaInertiaFibreEquiv
        S C hcentral g a r rho).1.1.values
          ((productPPrimeKernelCentralIntersectionSetup
            S C hcentral).localKernelInertiaElement
              (productPPrimeKernel S C hcentral)
              (productSylow S C :
                Subgroup (product S C))
              (productGlaubermanActiveOrbitEquiv
                S C hcentral g a r)
              ⟨z,
                Subgroup.center_le_normalizer
                  (productSylow S C :
                    Set (product S C)) hz⟩) *
        (rho.1.1.degree : ℂ) := by
  let K :=
    productPPrimeKernel S C hcentral
  let P : Subgroup (product S C) :=
    productSylow S C
  let H :=
    localNormalizer P
  let KN : Subgroup H :=
    internalKernelNormalizer K P
  let theta :=
    (r.pPrimeOut K).1
  let rLocal :=
    productGlaubermanActiveOrbitEquiv
      S C hcentral g a r
  let phi :=
    (rLocal.pPrimeOut KN).1
  let hSourceInertia :
      IrreducibleCharacter.inertia K theta = ⊤ :=
    (productPPrimeKernelCentralIntersectionSetup
      S C hcentral).activeKernel_inertia_eq_top
        K P (r.pPrimeOut K)
        (activePPrimeOut K r).2
  let hTargetInertia :
      IrreducibleCharacter.inertia KN phi = ⊤ :=
    (productPPrimeKernelCentralIntersectionSetup
      S C hcentral).activeLocalKernel_inertia_eq_top
        K P (rLocal.pPrimeOut KN)
        (activePPrimeOut KN rLocal).2
  let sourceTopEquiv :=
    pPrimeIrreducibleCharactersOverInertiaEquivAmbient
      K theta hSourceInertia q
  let targetTopEquiv :=
    pPrimeIrreducibleCharactersOverInertiaEquivAmbient
      KN phi hTargetInertia q
  let sourceAmbient :=
    sourceTopEquiv rho
  let lam :=
    (productSourceAmbientGallagherEquiv
      S C hcentral r).symm sourceAmbient
  let localAmbient :=
    productNormalizedLocalAmbientGallagherEquiv
      S C hcentral g a r
      (productLinearQuotientEquiv
        S C hcentral lam)
  let zH : H :=
    ⟨z,
      Subgroup.center_le_normalizer
        (P : Set (product S C)) hz⟩
  let zSource :=
    (productPPrimeKernelCentralIntersectionSetup
      S C hcentral).kernelInertiaElement K P r z
  let zTarget :=
    (productPPrimeKernelCentralIntersectionSetup
      S C hcentral).localKernelInertiaElement
        K P rLocal zH
  have hsourceCoordinate :
      productSourceAmbientGallagherEquiv
          S C hcentral r lam =
        sourceAmbient :=
    (productSourceAmbientGallagherEquiv
      S C hcentral r).apply_symm_apply sourceAmbient
  have hambient :=
    productNormalizedAmbientGallagher_central_cross
      S C hcentral g a r lam z hz
  rw [hsourceCoordinate] at hambient
  have htargetCoordinate :
      productNormalizedOkuyamaWajimaInertiaFibreEquiv
          S C hcentral g a r rho =
        targetTopEquiv.symm localAmbient := by
    rfl
  rw [htargetCoordinate]
  change
    rho.1.1.values zSource *
        ((targetTopEquiv.symm localAmbient).1.1.degree : ℂ) =
      (targetTopEquiv.symm localAmbient).1.1.values zTarget *
        (rho.1.1.degree : ℂ)
  rw [
    pPrimeIrreducibleCharactersOverInertiaEquivAmbient_symm_degree
      KN phi hTargetInertia q localAmbient,
    pPrimeIrreducibleCharactersOverInertiaEquivAmbient_symm_values
      KN phi hTargetInertia q localAmbient zTarget,
    ← pPrimeIrreducibleCharactersOverInertiaEquivAmbient_values
      K theta hSourceInertia q rho zSource,
    ← pPrimeIrreducibleCharactersOverInertiaEquivAmbient_degree
      K theta hSourceInertia q rho]
  exact hambient

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
