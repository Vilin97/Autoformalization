/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalSelectedSummand

/-!
# Character comparison for the canonical Glauberman summand

This file identifies the two honest Gallagher characters used to describe
the selected kernel summand with the source and target normal characters in
the final matched inertia comparison.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CliffordPartition
open CliffordCorrespondence
open ComplementReduction
open CentralIntersectionKernelAssembly
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

noncomputable local instance productCanonicalCharacterComparisonSourceFintype :
    Fintype (product S C) :=
  Fintype.ofFinite (product S C)

noncomputable local instance productCanonicalCharacterComparisonTargetFintype :
    Fintype
      (localNormalizer
        (productSylow S C :
          Subgroup (product S C))) :=
  Fintype.ofFinite _

/-- The normalized local Gallagher character recovered from the source
coordinate is exactly the local character produced by the assembled
Okuyama--Wajima correspondence. -/
theorem productAmbientNormalizedLocalGallagherCharacter_eq
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    productAmbientNormalizedLocalGallagherCharacter
        S C hcentral g theta =
      (complementCharacterEquivOfGlauberman
        S C hcentral g theta).1 := by
  let K := productPPrimeKernel S C hcentral
  let P : Subgroup (product S C) :=
    productSylow S C
  let M :=
    internalKernelNormalizer K P
  let a :=
    productGlaubermanActivationData S C hcentral
  let r := activeOrbitIndex K theta
  let block :=
    productAmbientSourceOrbitBlockCoordinate
      S C hcentral theta
  let rho :=
    productAmbientSourceInertiaCoordinate
      S C hcentral theta
  let t :=
    productGlaubermanActiveOrbitEquiv
      S C hcentral g a r
  let sigma :=
    productNormalizedOkuyamaWajimaInertiaFibreEquiv
      S C hcentral g a r rho
  let normalized :=
    productNormalizedActivePPrimeOrbitwiseCorrespondence
      S C hcentral g a
  let targetBlock :=
    normalized.blockEquiv r block
  let eTarget :=
    CliffordEquivalence.cliffordPPrimeCorrespondence
      M (t.pPrimeOut M).1
      (Fact.out : q.Prime)
      (activeOrbit_inertia_index_isPPrime M t)
  let hTargetInertia :
      IrreducibleCharacter.inertia
          M (t.pPrimeOut M).1 = ⊤ :=
    (productPPrimeKernelCentralIntersectionSetup
      S C hcentral).activeLocalKernel_inertia_eq_top
        K P (t.pPrimeOut M)
        (activePPrimeOut M t).2
  have hGallagher :=
    congrArg
      (fun z ↦ z.1.1)
      (productNormalizedOkuyamaWajimaInertiaFibreEquiv_ambient_apply
        S C hcentral g a r rho)
  have htop :=
    CliffordCorrespondence.cliffordPPrimeCorrespondence_eq_inertiaTopAmbient
      M (t.pPrimeOut M).1 hTargetInertia q
      (Fact.out : q.Prime)
      (activeOrbit_inertia_index_isPPrime M t)
      sigma
  have hblock :
      targetBlock.1.1 = (eTarget sigma).1.1 := by
    simpa only [targetBlock, eTarget, sigma, rho, block,
      productAmbientSourceInertiaCoordinate,
      normalized, M, P, K, t, r, a] using
      (productNormalizedActivePPrimeOrbitwiseCorrespondence_block_character
        S C hcentral g a r block)
  have hassemble :
      (normalized.assemble theta).1 =
        targetBlock.1.1 := by
    change
      ((pPrimeActiveOrbitBlockSigmaEquiv M q).symm
        ⟨normalized.activeOrbitEquiv r, targetBlock⟩).1 =
          targetBlock.1.1
    exact
      congrArg (fun z ↦ z.1)
        (pPrimeActiveOrbitBlockSigmaEquiv_symm_mk
          (N := M) (p := q)
          (normalized.activeOrbitEquiv r) targetBlock)
  have hnamed :
      (complementCharacterEquivOfGlauberman
          S C hcentral g theta).1 =
        (normalized.assemble theta).1 := by
    rfl
  exact
    hGallagher.symm.trans
      (htop.symm.trans
        (hblock.symm.trans
          (hassemble.symm.trans hnamed.symm)))

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
