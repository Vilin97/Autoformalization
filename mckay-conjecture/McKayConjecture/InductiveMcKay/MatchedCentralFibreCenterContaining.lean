/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalarConstituent
import McKayConjecture.InductiveMcKay.MatchedCentralFibreCentralScalarAssembly

/-!
# Matched Clifford fibres over center-containing normal subgroups

Suppose the source and target normal subgroups in a matched Clifford
assembly contain the relevant copies of every ambient-central element.  An
arbitrary equivalence of inertia fibres then preserves central scalars as
soon as the matched normal-subgroup characters do.  Indeed, every character
in either inertia fibre lies over its normal-subgroup character, so the
three normalized central values agree by transitivity.

This elementary observation removes the otherwise genuine ambiguity coming
from central factors outside the two normal subgroups.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]
variable (N H : Subgroup G) [N.Normal]
variable (M : Subgroup H) [M.Normal]
variable {p : ℕ} [Fact p.Prime]

namespace MatchedCentralFibreCliffordAssemblyData

variable {N H M}

omit [Finite G] [Fact p.Prime] in
/-- If both matched normal subgroups contain every relevant
ambient-central element, then central-scalar preservation of their
character correspondence automatically passes through any chosen
equivalences of the inertia fibres. -/
theorem preservesCentralScalars_of_center_containing
    (d : MatchedCentralFibreCliffordAssemblyData N H M p)
    (hcenterN :
      ∀ (z : G), z ∈ Subgroup.center G → z ∈ N)
    (hcenterM :
      ∀ (z : G) (_hzcentral : z ∈ Subgroup.center G)
        (hzH : z ∈ H),
        (⟨z, hzH⟩ : H) ∈ M)
    (hcharacter :
      ∀ (θ : PPrimeIrreducibleCharacter N p)
        (z : G) (hzcentral : z ∈ Subgroup.center G)
        (hzH : z ∈ H),
        θ.1.values ⟨z, hcenterN z hzcentral⟩ *
            (((d.characterEquiv θ).1.degree : ℂ)) =
          (d.characterEquiv θ).1.values
              ⟨⟨z, hzH⟩,
                hcenterM z hzcentral hzH⟩ *
            (θ.1.degree : ℂ)) :
    d.PreservesCentralScalars := by
  intro θ ρ z hzcentral hzH
  let φ := d.characterEquiv θ
  let σ := d.inertiaFibreEquiv θ ρ
  let zN : N :=
    ⟨z, hcenterN z hzcentral⟩
  let zM : M :=
    ⟨⟨z, hzH⟩,
      hcenterM z hzcentral hzH⟩
  have hzNcenter :
      zN ∈ Subgroup.center N := by
    rw [Subgroup.mem_center_iff]
    intro n
    apply Subtype.ext
    exact
      Subgroup.mem_center_iff.mp hzcentral
        (n : G)
  have hzMcenter :
      zM ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    apply Subtype.ext
    exact
      Subgroup.mem_center_iff.mp hzcentral
        ((m : M) : G)
  have hzSourceCenter :
      inertiaInclusion N θ.1 zN ∈
        Subgroup.center
          (IrreducibleCharacter.inertia N θ.1) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact
      Subgroup.mem_center_iff.mp hzcentral
        (x : G)
  have hzTargetCenter :
      inertiaInclusion M φ.1 zM ∈
        Subgroup.center
          (IrreducibleCharacter.inertia M φ.1) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact
      Subgroup.mem_center_iff.mp hzcentral
        ((x :
          IrreducibleCharacter.inertia M φ.1) : G)
  have hsource :=
    central_cross_of_liesOverAlong
      (inertiaInclusion N θ.1)
      θ.1 ρ.1.1 ρ.1.2
      zN hzNcenter hzSourceCenter
  have htarget :=
    central_cross_of_liesOverAlong
      (inertiaInclusion M φ.1)
      φ.1 σ.1.1 σ.1.2
      zM hzMcenter hzTargetCenter
  have hsourceElement :
      inertiaInclusion N θ.1 zN =
        d.sourceInertiaElement θ z hzcentral := by
    apply Subtype.ext
    rfl
  have htargetElement :
      inertiaInclusion M φ.1 zM =
        d.targetInertiaElement θ z hzcentral hzH := by
    apply Subtype.ext
    rfl
  rw [hsourceElement] at hsource
  rw [htargetElement] at htarget
  have hsource' :
      ρ.1.1.values
            (d.sourceInertiaElement θ z hzcentral) *
          (θ.1.degree : ℂ) =
        θ.1.values zN *
          (ρ.1.1.degree : ℂ) := by
    exact hsource
  have htarget' :
      σ.1.1.values
            (d.targetInertiaElement θ z hzcentral hzH) *
          (φ.1.degree : ℂ) =
        φ.1.values zM *
          (σ.1.1.degree : ℂ) := by
    exact htarget
  have hnormal :
      θ.1.values zN * (φ.1.degree : ℂ) =
        φ.1.values zM * (θ.1.degree : ℂ) := by
    simpa [zN, zM, φ] using
      hcharacter θ z hzcentral hzH
  apply mul_right_cancel₀
    (mul_ne_zero
      (Nat.cast_ne_zero.mpr θ.1.degree_ne_zero)
      (Nat.cast_ne_zero.mpr φ.1.degree_ne_zero))
  calc
    (ρ.1.1.values
          (d.sourceInertiaElement θ z hzcentral) *
        (σ.1.1.degree : ℂ)) *
          ((θ.1.degree : ℂ) * (φ.1.degree : ℂ)) =
      (ρ.1.1.values
          (d.sourceInertiaElement θ z hzcentral) *
        (θ.1.degree : ℂ)) *
          ((σ.1.1.degree : ℂ) * (φ.1.degree : ℂ)) := by
      ring
    _ =
      (θ.1.values zN * (ρ.1.1.degree : ℂ)) *
          ((σ.1.1.degree : ℂ) * (φ.1.degree : ℂ)) := by
      rw [hsource']
    _ =
      (θ.1.values zN * (φ.1.degree : ℂ)) *
          ((ρ.1.1.degree : ℂ) * (σ.1.1.degree : ℂ)) := by
      ring
    _ =
      (φ.1.values zM * (θ.1.degree : ℂ)) *
          ((ρ.1.1.degree : ℂ) * (σ.1.1.degree : ℂ)) := by
      rw [hnormal]
    _ =
      (φ.1.values zM * (σ.1.1.degree : ℂ)) *
          ((ρ.1.1.degree : ℂ) * (θ.1.degree : ℂ)) := by
      ring
    _ =
      (σ.1.1.values
          (d.targetInertiaElement θ z hzcentral hzH) *
        (φ.1.degree : ℂ)) *
          ((ρ.1.1.degree : ℂ) * (θ.1.degree : ℂ)) := by
      rw [htarget']
    _ =
      (σ.1.1.values
          (d.targetInertiaElement θ z hzcentral hzH) *
        (ρ.1.1.degree : ℂ)) *
          ((θ.1.degree : ℂ) * (φ.1.degree : ℂ)) := by
      ring

end MatchedCentralFibreCliffordAssemblyData
end InductiveMcKay
end McKayConjecture
