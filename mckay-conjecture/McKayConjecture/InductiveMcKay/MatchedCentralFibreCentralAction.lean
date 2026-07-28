/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralActionIntertwiner
import McKayConjecture.InductiveMcKay.MatchedCentralFibreCentralScalarAssembly

/-!
# Central-action intertwiners in matched Clifford fibres

For each pair of matched inertia-fibre characters and each ambient-central
element in the target subgroup, a nonzero map intertwining the two
realization operators forces equality of their central scalars.  This
representation-level condition therefore discharges the element-level
central-value condition used by matched Clifford assembly.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]
variable (N H : Subgroup G) [N.Normal]
variable (M : Subgroup H) [M.Normal]

namespace MatchedCentralFibreCliffordAssemblyData

variable {N H M}
variable {p : ℕ} [Fact p.Prime]

/-- The canonical ambient-central source element is central in its source
inertia group. -/
theorem sourceInertiaElement_mem_center
    (d : MatchedCentralFibreCliffordAssemblyData N H M p)
    (θ : PPrimeIrreducibleCharacter N p)
    (z : G) (hzcentral : z ∈ Subgroup.center G) :
    d.sourceInertiaElement θ z hzcentral ∈
      Subgroup.center
        (IrreducibleCharacter.inertia N θ.1) := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  exact
    Subgroup.mem_center_iff.mp hzcentral (x : G)

/-- The canonical ambient-central target element is central in its target
inertia group. -/
theorem targetInertiaElement_mem_center
    (d : MatchedCentralFibreCliffordAssemblyData N H M p)
    (θ : PPrimeIrreducibleCharacter N p)
    (z : G) (hzcentral : z ∈ Subgroup.center G)
    (hzH : z ∈ H) :
    d.targetInertiaElement θ z hzcentral hzH ∈
      Subgroup.center
        (IrreducibleCharacter.inertia M
          (d.characterEquiv θ).1) := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact
    Subgroup.mem_center_iff.mp hzcentral (x : G)

/-- Representation-level coherence for matched central fibre actions.

The map need only intertwine the two operators attached to the specified
central element.  Nonzeroness then forces their Schur scalars to agree. -/
def HasCentralActionIntertwiners
    (d : MatchedCentralFibreCliffordAssemblyData N H M p) : Prop :=
  ∀ (θ : PPrimeIrreducibleCharacter N p)
    (ρ :
      PPrimeIrreducibleCharactersOverInertia
        N θ.1 p)
    (z : G)
    (hzcentral : z ∈ Subgroup.center G)
    (hzH : z ∈ H),
    Nonempty
      (IrreducibleCharacter.CentralActionIntertwiner
        ρ.1.1
        (d.inertiaFibreEquiv θ ρ).1.1
        (d.sourceInertiaElement θ z hzcentral)
        (d.targetInertiaElement θ z hzcentral hzH))

/-- Central-action intertwiners imply the exact central-scalar condition
consumed by the numerical Clifford assembly. -/
theorem preservesCentralScalars_of_hasCentralActionIntertwiners
    (d : MatchedCentralFibreCliffordAssemblyData N H M p)
    (h : d.HasCentralActionIntertwiners) :
    d.PreservesCentralScalars := by
  intro θ ρ z hzcentral hzH
  obtain ⟨I⟩ := h θ ρ z hzcentral hzH
  exact
    I.central_cross
      (d.sourceInertiaElement_mem_center
        θ z hzcentral)
      (d.targetInertiaElement_mem_center
        θ z hzcentral hzH)

/-- Conversely, scalar preservation constructs the required nonzero
central-action intertwiners.  This uses a rank-one map between the two
realization spaces after Schur's lemma identifies the central scalars. -/
theorem hasCentralActionIntertwiners_of_preservesCentralScalars
    (d : MatchedCentralFibreCliffordAssemblyData N H M p)
    (h : d.PreservesCentralScalars) :
    d.HasCentralActionIntertwiners := by
  intro θ ρ z hzcentral hzH
  exact
    ⟨IrreducibleCharacter.CentralActionIntertwiner.of_central_cross
      (d.sourceInertiaElement_mem_center
        θ z hzcentral)
      (d.targetInertiaElement_mem_center
        θ z hzcentral hzH)
      (h θ ρ z hzcentral hzH)⟩

/-- The operator and scalar formulations of matched central-fibre
coherence are equivalent. -/
theorem hasCentralActionIntertwiners_iff_preservesCentralScalars
    (d : MatchedCentralFibreCliffordAssemblyData N H M p) :
    d.HasCentralActionIntertwiners ↔
      d.PreservesCentralScalars :=
  ⟨d.preservesCentralScalars_of_hasCentralActionIntertwiners,
    d.hasCentralActionIntertwiners_of_preservesCentralScalars⟩

/-- The representation-level coherence directly yields central-scalar
preservation for the assembled ambient correspondence. -/
theorem assembledPPrimeEquiv_central_cross_of_hasCentralActionIntertwiners
    (d : MatchedCentralFibreCliffordAssemblyData N H M p)
    (h : d.HasCentralActionIntertwiners)
    (χ : PPrimeIrreducibleCharacter G p)
    (z : G)
    (hzcentral : z ∈ Subgroup.center G)
    (hzH : z ∈ H) :
    χ.1.values z *
        ((d.assembledPPrimeEquiv χ).1.degree : ℂ) =
      (d.assembledPPrimeEquiv χ).1.values
          ⟨z, hzH⟩ *
        (χ.1.degree : ℂ) :=
  d.assembledPPrimeEquiv_central_cross
    (d.preservesCentralScalars_of_hasCentralActionIntertwiners h)
    χ z hzcentral hzH

end MatchedCentralFibreCliffordAssemblyData
end InductiveMcKay
end McKayConjecture
