/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordInductionCentralScalar
import McKayConjecture.InductiveMcKay.AdaptedCliffordFibreCoordinates
import McKayConjecture.InductiveMcKay.CentralIntersectionKernelAssembly

/-!
# The numerical Corollary 5.14 interface

For the numerical McKay reduction, a complete central character-triple
isomorphism is stronger than necessary.  Clifford assembly needs only:

* a matching of active kernel orbits;
* an equivalence of the corresponding prime-to-`p` inertia fibres; and
* preservation of normalized values at the canonical copies of ambient
  central elements in those two inertia groups.

`ActiveKernelCentralFibreData` records precisely that output.  It is the
narrow ordinary-character interface that an Okuyama--Wajima or Glauberman
argument must construct.  The rest of this file assembles it into an ambient
equivalence and proves the global central cross identity.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace CentralIntersectionKernelAssembly

open CliffordCorrespondence
open CliffordEquivalence
open CliffordPartition

variable {L : Type} [Group L] [Finite L]
variable {p : ℕ} [Fact p.Prime]
variable (K P : Subgroup L) [K.Normal]

noncomputable local instance centralIntersectionKernelNumericalFintypeL :
    Fintype L :=
  Fintype.ofFinite L

noncomputable local instance centralIntersectionKernelNumericalFintypeH :
    Fintype (localNormalizer P) :=
  Fintype.ofFinite (localNormalizer P)

/-- The canonical copy of an ambient element in the full inertia group of
an active kernel representative. -/
def CentralIntersectionSetup.kernelInertiaElement
    (s : CentralIntersectionSetup (p := p) K P)
    (a : ActiveOrbit K p)
    (z : L) :
    IrreducibleCharacter.inertia
      K (a.pPrimeOut K).1 :=
  ⟨z, by
    rw [s.activeKernel_inertia_eq_top
      K P (a.pPrimeOut K)
      (activePPrimeOut K a).2]
    exact Subgroup.mem_top z⟩

@[simp]
theorem CentralIntersectionSetup.kernelInertiaElement_coe
    (s : CentralIntersectionSetup (p := p) K P)
    (a : ActiveOrbit K p)
    (z : L) :
    (s.kernelInertiaElement K P a z : L) = z :=
  rfl

/-- The canonical copy of an element of the local normalizer in the full
inertia group of an active local-kernel representative. -/
def CentralIntersectionSetup.localKernelInertiaElement
    (s : CentralIntersectionSetup (p := p) K P)
    (a :
      ActiveOrbit (internalKernelNormalizer K P) p)
    (h : localNormalizer P) :
    IrreducibleCharacter.inertia
      (internalKernelNormalizer K P)
      (a.pPrimeOut
        (internalKernelNormalizer K P)).1 :=
  ⟨h, by
    rw [s.activeLocalKernel_inertia_eq_top
      K P
      (a.pPrimeOut
        (internalKernelNormalizer K P))
      (activePPrimeOut
        (internalKernelNormalizer K P) a).2]
    exact Subgroup.mem_top h⟩

@[simp]
theorem CentralIntersectionSetup.localKernelInertiaElement_coe
    (s : CentralIntersectionSetup (p := p) K P)
    (a :
      ActiveOrbit (internalKernelNormalizer K P) p)
    (h : localNormalizer P) :
    (s.localKernelInertiaElement K P a h :
      localNormalizer P) = h :=
  rfl

/-- The exact numerical output required from the active-kernel
Okuyama--Wajima/Glauberman correspondence. -/
structure ActiveKernelCentralFibreData
    (s : CentralIntersectionSetup (p := p) K P) where
  /-- Matching of the active kernel-character orbits. -/
  activeOrbitEquiv :
    ActiveOrbit K p ≃
      ActiveOrbit (internalKernelNormalizer K P) p
  /-- Matching of the prime-to-`p` inertia fibres at the quotient-chosen
  representatives. -/
  inertiaFibreEquiv :
    ∀ a : ActiveOrbit K p,
      PPrimeIrreducibleCharactersOverInertia
          K (a.pPrimeOut K).1 p ≃
        PPrimeIrreducibleCharactersOverInertia
          (internalKernelNormalizer K P)
          ((activeOrbitEquiv a).pPrimeOut
            (internalKernelNormalizer K P)).1 p
  /-- The fibre correspondence preserves normalized values at every
  ambient-central element. -/
  inertia_central_cross :
    ∀ (a : ActiveOrbit K p)
      (ρ :
        PPrimeIrreducibleCharactersOverInertia
          K (a.pPrimeOut K).1 p)
      (z : L)
      (hzcentral : z ∈ Subgroup.center L),
      ρ.1.1.values
          (s.kernelInertiaElement K P a z) *
          (((inertiaFibreEquiv a ρ).1.1.degree : ℂ)) =
        (inertiaFibreEquiv a ρ).1.1.values
            (s.localKernelInertiaElement K P
              (activeOrbitEquiv a)
              ⟨z,
                Subgroup.center_le_normalizer
                  (P : Set L) hzcentral⟩) *
          (ρ.1.1.degree : ℂ)

namespace ActiveKernelCentralFibreData

/-- Forget the central-value identity and retain the exact adapted
Clifford-fibre assembly data. -/
def toAdaptedCliffordFibreAssemblyData
    (d : ActiveKernelCentralFibreData (p := p) K P s) :
    AdaptedCliffordFibreAssemblyData
      K (internalKernelNormalizer K P) p where
  activeOrbitEquiv := d.activeOrbitEquiv
  sourceRepresentative := fun a => a.pPrimeOut K
  sourceRepresentative_orbit := fun a =>
    Quotient.out_eq' a.1
  sourceInertiaIndex_isPPrime := fun a =>
    activeOrbit_inertia_index_isPPrime K a
  targetRepresentative := fun a =>
    (d.activeOrbitEquiv a).pPrimeOut
      (internalKernelNormalizer K P)
  targetRepresentative_orbit := fun a =>
    Quotient.out_eq' (d.activeOrbitEquiv a).1
  targetInertiaIndex_isPPrime := fun a =>
    activeOrbit_inertia_index_isPPrime
      (internalKernelNormalizer K P)
      (d.activeOrbitEquiv a)
  inertiaFibreEquiv := d.inertiaFibreEquiv

/-- The ambient prime-to-`p` correspondence assembled from the exact
numerical fibre data. -/
def assembledPPrimeEquiv
    (d : ActiveKernelCentralFibreData (p := p) K P s) :
    PPrimeIrreducibleCharacter L p ≃
      PPrimeIrreducibleCharacter
        (localNormalizer P) p :=
  d.toAdaptedCliffordFibreAssemblyData.assembledPPrimeEquiv

/-- The narrow numerical fibre interface preserves normalized values after
global Clifford assembly. -/
theorem assembledPPrimeEquiv_central_cross
    (d : ActiveKernelCentralFibreData (p := p) K P s)
    (χ : PPrimeIrreducibleCharacter L p)
    (z : L)
    (hzcentral : z ∈ Subgroup.center L) :
    χ.1.values z *
        ((assembledPPrimeEquiv K P d χ).1.degree : ℂ) =
      (assembledPPrimeEquiv K P d χ).1.values
          ⟨z,
            Subgroup.center_le_normalizer
              (P : Set L) hzcentral⟩ *
        (χ.1.degree : ℂ) := by
  let a := d.toAdaptedCliffordFibreAssemblyData
  let q := activeOrbitIndex K χ
  let r := d.activeOrbitEquiv q
  let θ := q.pPrimeOut K
  let φ := r.pPrimeOut (internalKernelNormalizer K P)
  let ρ := a.sourceInertiaCharacter χ
  let σ := a.targetInertiaCharacter χ
  let zH : localNormalizer P :=
    ⟨z, Subgroup.center_le_normalizer
      (P : Set L) hzcentral⟩
  let zSource :=
    s.kernelInertiaElement K P q z
  let zTarget :=
    s.localKernelInertiaElement K P r zH
  have hzHcentral :
      zH ∈ Subgroup.center (localNormalizer P) := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hzcentral (h : L)
  have hfibre :
      ρ.1.1.values zSource * (σ.1.1.degree : ℂ) =
        σ.1.1.values zTarget * (ρ.1.1.degree : ℂ) :=
    d.inertia_central_cross q ρ z hzcentral
  have hsource :=
    inducedIrreducibleCharacter_central_cross
      K θ.1 ρ.1.1
      (inertiaInduction_simple K θ.1 ρ.1.1 ρ.1.2)
      zSource hzcentral
  have htarget :=
    inducedIrreducibleCharacter_central_cross
      (internalKernelNormalizer K P) φ.1 σ.1.1
      (inertiaInduction_simple
        (internalKernelNormalizer K P) φ.1
        σ.1.1 σ.1.2)
      zTarget hzHcentral
  have hsourceInduced :
      (inducedIrreducibleCharacter
        K θ.1 ρ.1.1
        (inertiaInduction_simple
          K θ.1 ρ.1.1 ρ.1.2)) =
        χ.1 :=
    a.induce_sourceInertiaCharacter χ
  have htargetInduced :
      (inducedIrreducibleCharacter
        (internalKernelNormalizer K P) φ.1 σ.1.1
        (inertiaInduction_simple
          (internalKernelNormalizer K P) φ.1
          σ.1.1 σ.1.2)) =
        (assembledPPrimeEquiv K P d χ).1 :=
    a.induce_targetInertiaCharacter χ
  rw [hsourceInduced] at hsource
  rw [htargetInduced] at htarget
  have hsource' :
      χ.1.values z * (ρ.1.1.degree : ℂ) =
        ρ.1.1.values zSource * (χ.1.degree : ℂ) := by
    simpa [zSource] using hsource
  have htarget' :
      (assembledPPrimeEquiv K P d χ).1.values zH *
          (σ.1.1.degree : ℂ) =
        σ.1.1.values zTarget *
          ((assembledPPrimeEquiv K P d χ).1.degree : ℂ) := by
    simpa [zTarget] using htarget
  apply mul_right_cancel₀
    (mul_ne_zero
      (Nat.cast_ne_zero.mpr ρ.1.1.degree_ne_zero)
      (Nat.cast_ne_zero.mpr σ.1.1.degree_ne_zero))
  calc
    (χ.1.values z *
          ((assembledPPrimeEquiv K P d χ).1.degree : ℂ)) *
        ((ρ.1.1.degree : ℂ) * (σ.1.1.degree : ℂ)) =
      (χ.1.values z * (ρ.1.1.degree : ℂ)) *
        ((assembledPPrimeEquiv K P d χ).1.degree : ℂ) *
          (σ.1.1.degree : ℂ) := by ring
    _ =
      (ρ.1.1.values zSource * (χ.1.degree : ℂ)) *
        ((assembledPPrimeEquiv K P d χ).1.degree : ℂ) *
          (σ.1.1.degree : ℂ) := by rw [hsource']
    _ =
      (ρ.1.1.values zSource * (σ.1.1.degree : ℂ)) *
        ((assembledPPrimeEquiv K P d χ).1.degree : ℂ) *
          (χ.1.degree : ℂ) := by ring
    _ =
      (σ.1.1.values zTarget * (ρ.1.1.degree : ℂ)) *
        ((assembledPPrimeEquiv K P d χ).1.degree : ℂ) *
          (χ.1.degree : ℂ) := by rw [hfibre]
    _ =
      ((assembledPPrimeEquiv K P d χ).1.values zH *
          (σ.1.1.degree : ℂ)) *
        (ρ.1.1.degree : ℂ) * (χ.1.degree : ℂ) := by
      rw [htarget']
      ring
    _ =
      ((assembledPPrimeEquiv K P d χ).1.values zH *
          (χ.1.degree : ℂ)) *
        ((ρ.1.1.degree : ℂ) * (σ.1.1.degree : ℂ)) := by
      ring

end ActiveKernelCentralFibreData
end CentralIntersectionKernelAssembly
end InductiveMcKay
end McKayConjecture
