/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InertiaTopFibre
import McKayConjecture.Character.LinearCharacterTransport
import McKayConjecture.CharacterTriple.NormalHallPPrimeExtension
import McKayConjecture.GroupTheory.NormalComplementQuotient
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlauberman
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionDirectProductActivation

/-!
# Gallagher construction of the central-intersection inertia-fibre equivalence

For the canonical normal `p'`-kernel `R ◁ RP`, both the source group and
the local Sylow normalizer are split extensions by the same Sylow group.
Every active kernel character has full inertia and extends by the normal
Hall extension theorem.  Gallagher correspondence therefore parametrizes
both prime-to-`p` fibres by multiplicative linear characters of isomorphic
quotients.  This constructs the numerical part of the Okuyama--Wajima
fibre comparison without taking it as an input.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace ComplementReduction

open CliffordCorrespondence
open CliffordPartition
open CentralIntersectionKernelAssembly

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

noncomputable local instance productFibreEquivalenceFintype :
    Fintype (product S C) :=
  Fintype.ofFinite (product S C)

noncomputable local instance productFibreEquivalenceLocalFintype :
    Fintype
      (localNormalizer
        (productSylow S C :
          Subgroup (product S C))) :=
  Fintype.ofFinite _

/-- The local kernel `C_R(P)` is again a `q'`-group. -/
theorem productLocalKernel_isPPrimeGroup
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    GroupTheory.IsPPrimeGroup q
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))) := by
  let K :=
    productPPrimeKernel S C hcentral
  let P : Subgroup (product S C) :=
    productSylow S C
  let F : Subgroup (product S C) :=
    K ⊓ Subgroup.centralizer (P : Set (product S C))
  have hFle : F ≤ K :=
    inf_le_left
  have hfinternal :
      GroupTheory.IsPPrimeGroup q (F.subgroupOf K) :=
    (productPPrimeKernel_isPPrimeGroup
      S C hcentral).to_subgroup (F.subgroupOf K)
  have hfixed :
      GroupTheory.IsPPrimeGroup q F :=
    hfinternal.of_equiv
      (Subgroup.subgroupOfEquivOfLe hFle)
  exact
    hfixed.of_equiv
      (localKernelAmbientFixedPointsEquiv
        S C hcentral).symm

/-- The source quotient `RP/R` is canonically the chosen Sylow subgroup. -/
def productSourceQuotientSylowEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    ((product S C) ⧸
        productPPrimeKernel S C hcentral) ≃*
      (productSylow S C :
        Subgroup (product S C)) := by
  apply GroupTheory.normalComplementQuotientEquiv
  · apply disjoint_iff_inf_le.mpr
    rw [inf_comm,
      productPPrimeKernel_inf_productSylow_eq_bot
        S C hcentral]
  · exact
      productPPrimeKernel_sup_productSylow_eq_top
        S C hcentral

/-- The local quotient `N_{RP}(P)/C_R(P)` is canonically the same Sylow
subgroup. -/
def productLocalQuotientSylowEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    (localNormalizer
        (productSylow S C :
          Subgroup (product S C)) ⧸
      internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))) ≃*
      (productSylow S C :
        Subgroup (product S C)) := by
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
  have hPN :
      IsPGroup q PN :=
    (productSylow S C).isPGroup'.of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (show P ≤ localNormalizer P from
          Subgroup.le_normalizer)).symm
  have hdisjoint : Disjoint PN KN :=
    GroupTheory.IsPGroup.disjoint_of_isPPrimeGroup hPN
      (productLocalKernel_isPPrimeGroup
        S C hcentral)
  exact
    (GroupTheory.normalComplementQuotientEquiv
      KN PN hdisjoint
      (internalKernelNormalizer_sup_internalP_eq_top
        K P
        (productPPrimeKernel_sup_productSylow_eq_top
          S C hcentral))).trans
      (Subgroup.subgroupOfEquivOfLe
        (show P ≤ localNormalizer P from
          Subgroup.le_normalizer))

/-- The source and local quotient groups are canonically isomorphic by
identifying both with the chosen Sylow subgroup. -/
def productLocalSourceQuotientEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    (localNormalizer
        (productSylow S C :
          Subgroup (product S C)) ⧸
      internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))) ≃*
      ((product S C) ⧸
        productPPrimeKernel S C hcentral) :=
  (productLocalQuotientSylowEquiv
    S C hcentral).trans
      (productSourceQuotientSylowEquiv
        S C hcentral).symm

/-- Transport multiplicative linear characters from the source quotient
to the local quotient. -/
def productLinearQuotientEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    (((product S C) ⧸
        productPPrimeKernel S C hcentral) →* ℂˣ) ≃
      ((localNormalizer
          (productSylow S C :
            Subgroup (product S C)) ⧸
        internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) →* ℂˣ) :=
  monoidHomPrecompMulEquiv
    (productLocalSourceQuotientEquiv
      S C hcentral)

/-- A selected prime-to-`q` source extension of an active kernel
representative. -/
def productSourcePPrimeExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    PPrimeIrreducibleCharacter (product S C) q :=
  Classical.choose
    (CharacterTriple.exists_pPrime_extension_of_normalHall_inertiaTop
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
      (productPPrimeKernel_isPPrimeGroup
        S C hcentral)
      (productPPrimeKernelCentralIntersectionSetup
        S C hcentral).quotientPGroup
      (r.pPrimeOut
        (productPPrimeKernel S C hcentral)).2)

/-- The selected source character extends the active kernel
representative. -/
theorem productSourcePPrimeExtension_isExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    IrreducibleCharacter.IsExtensionAlong
      (productPPrimeKernel S C hcentral).subtype
      (r.pPrimeOut
        (productPPrimeKernel S C hcentral)).1
      (productSourcePPrimeExtension
        S C hcentral r).1 :=
  Classical.choose_spec
    (CharacterTriple.exists_pPrime_extension_of_normalHall_inertiaTop
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
      (productPPrimeKernel_isPPrimeGroup
        S C hcentral)
      (productPPrimeKernelCentralIntersectionSetup
        S C hcentral).quotientPGroup
      (r.pPrimeOut
        (productPPrimeKernel S C hcentral)).2)

/-- Gallagher coordinates on the source ambient fibre. -/
def productSourceAmbientGallagherEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    (((product S C) ⧸
        productPPrimeKernel S C hcentral) →* ℂˣ) ≃
      PPrimeIrreducibleCharactersOverAlong
        (productPPrimeKernel S C hcentral).subtype
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral)).1 q :=
  IrreducibleCharacter.gallagherLinearCorrespondenceOfPGroupQuotient
    (productPPrimeKernel S C hcentral)
    (productPPrimeKernelCentralIntersectionSetup
      S C hcentral).quotientPGroup
    (productSourcePPrimeExtension_isExtension
      S C hcentral r)
    (r.pPrimeOut
      (productPPrimeKernel S C hcentral)).2

/-- A selected prime-to-`q` local extension of the matched active local
kernel representative. -/
def productLocalPPrimeExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    PPrimeIrreducibleCharacter
      (localNormalizer
        (productSylow S C :
          Subgroup (product S C))) q :=
  Classical.choose
    (CharacterTriple.exists_pPrime_extension_of_normalHall_inertiaTop
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
      (productLocalKernel_isPPrimeGroup
        S C hcentral)
      (localNormalizer_quotient_internalKernel_isPGroup
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))
        (productPPrimeKernelCentralIntersectionSetup
          S C hcentral).pSubgroup
        (productPPrimeKernelCentralIntersectionSetup
          S C hcentral).generate)
      ((productGlaubermanActiveOrbitEquiv
        S C hcentral g a r).pPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))).2)

/-- The selected local character extends the matched active local-kernel
representative. -/
theorem productLocalPPrimeExtension_isExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    IrreducibleCharacter.IsExtensionAlong
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))).subtype
      (((productGlaubermanActiveOrbitEquiv
          S C hcentral g a r).pPrimeOut
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))).1)
      (productLocalPPrimeExtension
        S C hcentral g a r).1 :=
  Classical.choose_spec
    (CharacterTriple.exists_pPrime_extension_of_normalHall_inertiaTop
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
      (productLocalKernel_isPPrimeGroup
        S C hcentral)
      (localNormalizer_quotient_internalKernel_isPGroup
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))
        (productPPrimeKernelCentralIntersectionSetup
          S C hcentral).pSubgroup
        (productPPrimeKernelCentralIntersectionSetup
          S C hcentral).generate)
      ((productGlaubermanActiveOrbitEquiv
        S C hcentral g a r).pPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))).2)

/-- Gallagher coordinates on the matched local ambient fibre. -/
def productLocalAmbientGallagherEquiv
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
    (productLocalPPrimeExtension_isExtension
      S C hcentral g a r)
    ((productGlaubermanActiveOrbitEquiv
      S C hcentral g a r).pPrimeOut
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))).2

/-- The numerical Okuyama--Wajima inertia-fibre equivalence is a theorem:
transport full inertia to the two ambient fibres, use Gallagher
coordinates, and identify the two quotient groups through the common
Sylow complement. -/
def productOkuyamaWajimaInertiaFibreEquiv
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
    (productLocalAmbientGallagherEquiv
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

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
