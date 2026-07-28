/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordInductionCentralScalar
import McKayConjecture.CharacterTriple.CentralCharacterScalar
import McKayConjecture.InductiveMcKay.CentralIntersectionKernelNumerical

/-!
# Central scalars in the central-intersection kernel assembly

The central character-triple witness compares normalized values inside the
matched inertia groups.  Clifford induction preserves the normalized value
of an ambient-central element.  Combining these two facts proves that the
active-kernel assembly preserves normalized values on the center.

The only element-level input beyond the complete central witnesses is that
their abstract embeddings are the canonical inclusions.  This coherence is
recorded explicitly by `ActiveKernelDGNData.embedding_coe`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace CentralIntersectionKernelAssembly

open CharacterTriple
open CliffordCorrespondence
open CliffordEquivalence
open CliffordPartition

variable {L : Type} [Group L] [Finite L]
variable {p : ℕ} [Fact p.Prime]
variable (K P : Subgroup L) [K.Normal]

noncomputable local instance centralIntersectionKernelScalarFintypeL :
    Fintype L :=
  Fintype.ofFinite L

noncomputable local instance centralIntersectionKernelScalarFintypeH :
    Fintype (localNormalizer P) :=
  Fintype.ofFinite (localNormalizer P)

/-- Complete central witnesses with the canonical-embedding coherence
produce exactly the narrower numerical Corollary 5.14 interface. -/
def ActiveKernelDGNData.toActiveKernelCentralFibreData
    (s : CentralIntersectionSetup (p := p) K P)
    (d : ActiveKernelDGNData (p := p) K P) :
    ActiveKernelCentralFibreData (p := p) K P s where
  activeOrbitEquiv := d.activeOrbitEquiv
  inertiaFibreEquiv := fun a => by
    let C := d.centralWitness a
    letI := C.leftAddCommGroup
    letI := C.leftModule
    letI := C.leftModuleFinite
    letI := C.leftNontrivial
    letI := C.rightAddCommGroup
    letI := C.rightModule
    letI := C.rightModuleFinite
    letI := C.rightNontrivial
    exact
      C.witness.pPrimeInertiaEquiv
        K (a.pPrimeOut K).1
        (internalKernelNormalizer K P)
        ((d.activeOrbitEquiv a).pPrimeOut
          (internalKernelNormalizer K P)).1
        (Fact.out : p.Prime)
        (a.pPrimeOut K).2
        ((d.activeOrbitEquiv a).pPrimeOut
          (internalKernelNormalizer K P)).2
  inertia_central_cross := by
    intro a ρ z hzcentral
    let C := d.centralWitness a
    let zSource :=
      s.kernelInertiaElement K P a z
    let zTarget :=
      s.localKernelInertiaElement K P
        (d.activeOrbitEquiv a)
        ⟨z,
          Subgroup.center_le_normalizer
            (P : Set L) hzcentral⟩
    letI := C.leftAddCommGroup
    letI := C.leftModule
    letI := C.leftModuleFinite
    letI := C.leftNontrivial
    letI := C.rightAddCommGroup
    letI := C.rightModule
    letI := C.rightModuleFinite
    letI := C.rightNontrivial
    have hembedding :
        C.witness.embedding zTarget = zSource := by
      apply Subtype.ext
      exact d.embedding_coe a zTarget
    have hzSourceCenter :
        zSource ∈
          Subgroup.center
            (IrreducibleCharacter.inertia
              K (a.pPrimeOut K).1) := by
      rw [Subgroup.mem_center_iff]
      intro h
      apply Subtype.ext
      exact
        Subgroup.mem_center_iff.mp
          hzcentral (h : L)
    have hzcentralizer :
        C.witness.embedding zTarget ∈
          Subgroup.centralizer
            ((ofInertia
              K (a.pPrimeOut K).1).normalSubgroup :
              Set (IrreducibleCharacter.inertia
                K (a.pPrimeOut K).1)) := by
      rw [hembedding]
      exact
        Subgroup.center_le_centralizer
          ((ofInertia
            K (a.pPrimeOut K).1).normalSubgroup :
            Set (IrreducibleCharacter.inertia
              K (a.pPrimeOut K).1))
          hzSourceCenter
    let ρTriple :=
      pPrimeIrreducibleCharactersOverInertiaEquivTriple
        K (a.pPrimeOut K).1 p ρ
    have hρTriple :
        ρTriple.1.1 = ρ.1.1 :=
      rfl
    have htarget :
        ((C.witness.pPrimeInertiaEquiv
          K (a.pPrimeOut K).1
          (internalKernelNormalizer K P)
          ((d.activeOrbitEquiv a).pPrimeOut
            (internalKernelNormalizer K P)).1
          (Fact.out : p.Prime)
          (a.pPrimeOut K).2
          ((d.activeOrbitEquiv a).pPrimeOut
            (internalKernelNormalizer K P)).2
          ρ).1.1) =
          (C.witness.rightCharacterMap ρTriple.1).1 :=
      rfl
    have h :=
      C.witness.rightCharacterMap_matchedCentral_cross
        ρTriple.1 zTarget hzcentralizer
    rw [hembedding] at h
    rw [hρTriple] at h
    rw [← htarget] at h
    simpa [zSource, zTarget, C] using h

/-- The correspondence assembled from faithful active-kernel DGN data
preserves normalized values at every central element. -/
theorem pPrimeEquivOfCentralIntersectionActiveKernelDGNData_central_cross
    (s : CentralIntersectionSetup (p := p) K P)
    (d : ActiveKernelDGNData (p := p) K P)
    (χ : PPrimeIrreducibleCharacter L p)
    (z : L)
    (hzcentral : z ∈ Subgroup.center L) :
    χ.1.values z *
        ((pPrimeEquivOfCentralIntersectionActiveKernelDGNData
          K P s d χ).1.degree : ℂ) =
      (pPrimeEquivOfCentralIntersectionActiveKernelDGNData
        K P s d χ).1.values
          ⟨z, Subgroup.center_le_normalizer (P : Set L) hzcentral⟩ *
        (χ.1.degree : ℂ) := by
  let q := activeOrbitIndex K χ
  let r := d.activeOrbitEquiv q
  let θ := q.pPrimeOut K
  let φ := r.pPrimeOut (internalKernelNormalizer K P)
  let C := d.centralWitness q
  let a :=
    AdaptedCliffordFibreAssemblyData.ofCentralTriple
      d.toAdaptedCentralTripleCliffordAssemblyData
  let ρ := a.sourceInertiaCharacter χ
  let σ := a.targetInertiaCharacter χ
  let zH : localNormalizer P :=
    ⟨z, Subgroup.center_le_normalizer (P : Set L) hzcentral⟩
  have hθactive : IsActivePPrimeCharacter K θ :=
    (activePPrimeOut K q).2
  have hφactive :
      IsActivePPrimeCharacter
        (internalKernelNormalizer K P) φ :=
    (activePPrimeOut
      (internalKernelNormalizer K P) r).2
  have hsourceInertia :
      IrreducibleCharacter.inertia K θ.1 = ⊤ :=
    s.activeKernel_inertia_eq_top K P θ hθactive
  have htargetInertia :
      IrreducibleCharacter.inertia
          (internalKernelNormalizer K P) φ.1 =
        ⊤ :=
    s.activeLocalKernel_inertia_eq_top K P φ hφactive
  let zSource : IrreducibleCharacter.inertia K θ.1 :=
    ⟨z, by rw [hsourceInertia]; exact Subgroup.mem_top z⟩
  let zTarget :
      IrreducibleCharacter.inertia
        (internalKernelNormalizer K P) φ.1 :=
    ⟨zH, by rw [htargetInertia]; exact Subgroup.mem_top zH⟩
  have hzHcentral : zH ∈ Subgroup.center (localNormalizer P) := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hzcentral (h : L)
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  have hembedding :
      C.witness.embedding zTarget = zSource := by
    apply Subtype.ext
    exact d.embedding_coe q zTarget
  have hzSourceCenter :
      zSource ∈
        Subgroup.center
          (IrreducibleCharacter.inertia K θ.1) := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hzcentral (h : L)
  have hzcentralizer :
      C.witness.embedding zTarget ∈
        Subgroup.centralizer
          ((ofInertia K θ.1).normalSubgroup :
            Set (IrreducibleCharacter.inertia K θ.1)) := by
    rw [hembedding]
    exact
      Subgroup.center_le_centralizer
        ((ofInertia K θ.1).normalSubgroup :
          Set (IrreducibleCharacter.inertia K θ.1))
        hzSourceCenter
  let ρTriple :=
    pPrimeIrreducibleCharactersOverInertiaEquivTriple
      K θ.1 p ρ
  have hρTriple :
      ρTriple.1.1 = ρ.1.1 :=
    rfl
  have hσ :
      σ.1.1 =
        (C.witness.rightCharacterMap ρTriple.1).1 :=
    rfl
  have hfibre :
      ρ.1.1.values zSource * (σ.1.1.degree : ℂ) =
        σ.1.1.values zTarget * (ρ.1.1.degree : ℂ) := by
    have h :=
      C.witness.rightCharacterMap_matchedCentral_cross
        ρTriple.1 zTarget hzcentralizer
    rw [hembedding] at h
    simpa [hρTriple, hσ] using h
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
        χ.1 := by
    exact a.induce_sourceInertiaCharacter χ
  have htargetInduced :
      (inducedIrreducibleCharacter
        (internalKernelNormalizer K P) φ.1 σ.1.1
        (inertiaInduction_simple
          (internalKernelNormalizer K P) φ.1
          σ.1.1 σ.1.2)) =
        (a.assembledPPrimeEquiv χ).1 := by
    exact a.induce_targetInertiaCharacter χ
  rw [hsourceInduced] at hsource
  rw [htargetInduced] at htarget
  have hassembled :
      a.assembledPPrimeEquiv =
        pPrimeEquivOfCentralIntersectionActiveKernelDGNData
          K P s d := by
    exact
      AdaptedCliffordFibreAssemblyData.assembledPPrimeEquiv_ofCentralTriple
        d.toAdaptedCentralTripleCliffordAssemblyData
  rw [hassembled] at htarget
  apply mul_right_cancel₀
    (mul_ne_zero
      (Nat.cast_ne_zero.mpr ρ.1.1.degree_ne_zero)
      (Nat.cast_ne_zero.mpr σ.1.1.degree_ne_zero))
  calc
    (χ.1.values z *
          ((pPrimeEquivOfCentralIntersectionActiveKernelDGNData
            K P s d χ).1.degree : ℂ)) *
        ((ρ.1.1.degree : ℂ) * (σ.1.1.degree : ℂ)) =
      (χ.1.values z * (ρ.1.1.degree : ℂ)) *
        ((pPrimeEquivOfCentralIntersectionActiveKernelDGNData
          K P s d χ).1.degree : ℂ) *
          (σ.1.1.degree : ℂ) := by ring
    _ =
      (ρ.1.1.values zSource * (χ.1.degree : ℂ)) *
        ((pPrimeEquivOfCentralIntersectionActiveKernelDGNData
          K P s d χ).1.degree : ℂ) *
          (σ.1.1.degree : ℂ) := by rw [hsource]
    _ =
      (ρ.1.1.values zSource * (σ.1.1.degree : ℂ)) *
        ((pPrimeEquivOfCentralIntersectionActiveKernelDGNData
          K P s d χ).1.degree : ℂ) *
          (χ.1.degree : ℂ) := by ring
    _ =
      (σ.1.1.values zTarget * (ρ.1.1.degree : ℂ)) *
        ((pPrimeEquivOfCentralIntersectionActiveKernelDGNData
          K P s d χ).1.degree : ℂ) *
          (χ.1.degree : ℂ) := by rw [hfibre]
    _ =
      ((pPrimeEquivOfCentralIntersectionActiveKernelDGNData
          K P s d χ).1.values zH *
          (σ.1.1.degree : ℂ)) *
        (ρ.1.1.degree : ℂ) * (χ.1.degree : ℂ) := by
      rw [htarget]
      ring
    _ =
      ((pPrimeEquivOfCentralIntersectionActiveKernelDGNData
          K P s d χ).1.values zH * (χ.1.degree : ℂ)) *
        ((ρ.1.1.degree : ℂ) * (σ.1.1.degree : ℂ)) := by ring

end CentralIntersectionKernelAssembly
end InductiveMcKay
end McKayConjecture
