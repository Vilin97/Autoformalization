/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordInductionCentralScalar
import McKayConjecture.InductiveMcKay.AdaptedCliffordFibreCoordinates
import McKayConjecture.InductiveMcKay.MatchedCentralFibreCliffordAssembly
import McKayConjecture.InductiveMcKay.MatchedCentralTripleCentralScalarAssembly

/-!
# Central scalars in matched numerical fibre assembly

For matched normal-subgroup characters, suppose the chosen inertia-fibre
equivalence preserves normalized values at the canonical copies of every
ambient-central element lying in the target subgroup.  Clifford induction
then lifts this exact identity to the ambient character correspondence.

This is the numerical fibre-level counterpart of
`MatchedCentralTripleCliffordAssemblyData.assembledPPrimeEquiv_central_cross`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CliffordCorrespondence
open CliffordEquivalence
open CliffordPartition

variable {G : Type} [Group G] [Finite G]
variable (N H : Subgroup G) [N.Normal]
variable (M : Subgroup H) [M.Normal]

noncomputable local instance matchedCentralFibreScalarFintypeG :
    Fintype G :=
  Fintype.ofFinite G

noncomputable local instance matchedCentralFibreScalarFintypeH :
    Fintype H :=
  Fintype.ofFinite H

namespace MatchedCentralFibreCliffordAssemblyData

variable {N H M}
variable {p : ℕ} [Fact p.Prime]

/-- The canonical copy of an ambient-central element in a source inertia
group. -/
def sourceInertiaElement
    (_d : MatchedCentralFibreCliffordAssemblyData N H M p)
    (θ : PPrimeIrreducibleCharacter N p)
    (z : G) (hzcentral : z ∈ Subgroup.center G) :
    IrreducibleCharacter.inertia N θ.1 :=
  ⟨z,
    IrreducibleCharacter.mem_inertia_of_mem_center
      N θ.1 z hzcentral⟩

@[simp]
theorem sourceInertiaElement_coe
    (d : MatchedCentralFibreCliffordAssemblyData N H M p)
    (θ : PPrimeIrreducibleCharacter N p)
    (z : G) (hzcentral : z ∈ Subgroup.center G) :
    (d.sourceInertiaElement θ z hzcentral : G) = z :=
  rfl

/-- The canonical copy of the same element in the matched target inertia
group. -/
def targetInertiaElement
    (d : MatchedCentralFibreCliffordAssemblyData N H M p)
    (θ : PPrimeIrreducibleCharacter N p)
    (z : G) (hzcentral : z ∈ Subgroup.center G)
    (hzH : z ∈ H) :
    IrreducibleCharacter.inertia M
      (d.characterEquiv θ).1 :=
  let zH : H := ⟨z, hzH⟩
  ⟨zH,
    MatchedInertiaRestriction.mem_target_inertia_of_mem_source_inertia
      N H M d.characterEquiv d.characterEquiv_smul
        θ zH (d.sourceInertiaElement θ z hzcentral).property⟩

@[simp]
theorem targetInertiaElement_coe
    (d : MatchedCentralFibreCliffordAssemblyData N H M p)
    (θ : PPrimeIrreducibleCharacter N p)
    (z : G) (hzcentral : z ∈ Subgroup.center G)
    (hzH : z ∈ H) :
    (d.targetInertiaElement θ z hzcentral hzH :
      H) = ⟨z, hzH⟩ :=
  rfl

/-- Exact central-value coherence required of the matched inertia-fibre
equivalences. -/
def PreservesCentralScalars
    (d : MatchedCentralFibreCliffordAssemblyData N H M p) : Prop :=
  ∀ (θ : PPrimeIrreducibleCharacter N p)
    (ρ :
      PPrimeIrreducibleCharactersOverInertia
        N θ.1 p)
    (z : G)
    (hzcentral : z ∈ Subgroup.center G)
    (hzH : z ∈ H),
    ρ.1.1.values
        (d.sourceInertiaElement θ z hzcentral) *
        (((d.inertiaFibreEquiv θ ρ).1.1.degree : ℂ)) =
      (d.inertiaFibreEquiv θ ρ).1.1.values
          (d.targetInertiaElement θ z hzcentral hzH) *
        (ρ.1.1.degree : ℂ)

/-- Central scalar preservation passes through the matched Clifford
assembly. -/
theorem assembledPPrimeEquiv_central_cross
    (d : MatchedCentralFibreCliffordAssemblyData N H M p)
    (hscalar : d.PreservesCentralScalars)
    (χ : PPrimeIrreducibleCharacter G p)
    (z : G)
    (hzcentral : z ∈ Subgroup.center G)
    (hzH : z ∈ H) :
    χ.1.values z *
        ((d.assembledPPrimeEquiv χ).1.degree : ℂ) =
      (d.assembledPPrimeEquiv χ).1.values
          ⟨z, hzH⟩ *
        (χ.1.degree : ℂ) := by
  let a := d.toAdaptedCliffordFibreAssemblyData
  let q := activeOrbitIndex N χ
  let θ := q.pPrimeOut N
  let φ := d.characterEquiv θ
  let ρ := a.sourceInertiaCharacter χ
  let σ := a.targetInertiaCharacter χ
  let zH : H := ⟨z, hzH⟩
  let zSource :=
    d.sourceInertiaElement θ z hzcentral
  let zTarget :=
    d.targetInertiaElement θ z hzcentral hzH
  have hzHcentral :
      zH ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hzcentral (h : G)
  have hfibre :
      ρ.1.1.values zSource * (σ.1.1.degree : ℂ) =
        σ.1.1.values zTarget * (ρ.1.1.degree : ℂ) := by
    exact hscalar θ ρ z hzcentral hzH
  have hsource :=
    inducedIrreducibleCharacter_central_cross
      N θ.1 ρ.1.1
      (inertiaInduction_simple N θ.1 ρ.1.1 ρ.1.2)
      zSource hzcentral
  have htarget :=
    inducedIrreducibleCharacter_central_cross
      M φ.1 σ.1.1
      (inertiaInduction_simple
        M φ.1 σ.1.1 σ.1.2)
      zTarget hzHcentral
  have hsourceInduced :
      (inducedIrreducibleCharacter
        N θ.1 ρ.1.1
        (inertiaInduction_simple
          N θ.1 ρ.1.1 ρ.1.2)) =
        χ.1 :=
    a.induce_sourceInertiaCharacter χ
  have htargetInduced :
      (inducedIrreducibleCharacter
        M φ.1 σ.1.1
        (inertiaInduction_simple
          M φ.1 σ.1.1 σ.1.2)) =
        (d.assembledPPrimeEquiv χ).1 :=
    a.induce_targetInertiaCharacter χ
  rw [hsourceInduced] at hsource
  rw [htargetInduced] at htarget
  have hsource' :
      χ.1.values z * (ρ.1.1.degree : ℂ) =
        ρ.1.1.values zSource * (χ.1.degree : ℂ) := by
    simpa [zSource] using hsource
  have htarget' :
      (d.assembledPPrimeEquiv χ).1.values zH *
          (σ.1.1.degree : ℂ) =
        σ.1.1.values zTarget *
          ((d.assembledPPrimeEquiv χ).1.degree : ℂ) := by
    simpa [zTarget] using htarget
  apply mul_right_cancel₀
    (mul_ne_zero
      (Nat.cast_ne_zero.mpr ρ.1.1.degree_ne_zero)
      (Nat.cast_ne_zero.mpr σ.1.1.degree_ne_zero))
  calc
    (χ.1.values z *
          ((d.assembledPPrimeEquiv χ).1.degree : ℂ)) *
        ((ρ.1.1.degree : ℂ) * (σ.1.1.degree : ℂ)) =
      (χ.1.values z * (ρ.1.1.degree : ℂ)) *
        ((d.assembledPPrimeEquiv χ).1.degree : ℂ) *
          (σ.1.1.degree : ℂ) := by ring
    _ =
      (ρ.1.1.values zSource * (χ.1.degree : ℂ)) *
        ((d.assembledPPrimeEquiv χ).1.degree : ℂ) *
          (σ.1.1.degree : ℂ) := by rw [hsource']
    _ =
      (ρ.1.1.values zSource * (σ.1.1.degree : ℂ)) *
        ((d.assembledPPrimeEquiv χ).1.degree : ℂ) *
          (χ.1.degree : ℂ) := by ring
    _ =
      (σ.1.1.values zTarget * (ρ.1.1.degree : ℂ)) *
        ((d.assembledPPrimeEquiv χ).1.degree : ℂ) *
          (χ.1.degree : ℂ) := by rw [hfibre]
    _ =
      ((d.assembledPPrimeEquiv χ).1.values zH *
          (σ.1.1.degree : ℂ)) *
        (ρ.1.1.degree : ℂ) * (χ.1.degree : ℂ) := by
      rw [htarget']
      ring
    _ =
      ((d.assembledPPrimeEquiv χ).1.values zH *
          (χ.1.degree : ℂ)) *
        ((ρ.1.1.degree : ℂ) * (σ.1.1.degree : ℂ)) := by
      ring

end MatchedCentralFibreCliffordAssemblyData
end InductiveMcKay
end McKayConjecture
