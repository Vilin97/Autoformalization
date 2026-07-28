/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import McKayConjecture.Character.CyclicExtensionConstruction
import McKayConjecture.Character.Extension

/-!
# Maximal extendibility from cyclic inertia quotients

The cyclic extension theorem applies character by character to an inertia
group.  Thus, if every quotient `I_G(χ) / N` is cyclic, the normal subgroup
`N` is maximally extendible in `G`.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G : Type u} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal]

/-- The canonical identification between `N`, as a group in its own right,
and its copy inside an inertia group. -/
abbrev subgroupOfInertiaEquiv (χ : IrreducibleCharacter N) :
    N.subgroupOf (inertia N χ) ≃* N :=
  Subgroup.subgroupOfEquivOfLe (subgroup_le_inertia N χ)

/-- Regard a character of `N` as a character of the canonical copy of `N`
inside its inertia group. -/
def onSubgroupOfInertia (χ : IrreducibleCharacter N) :
    IrreducibleCharacter (N.subgroupOf (inertia N χ)) :=
  χ.comap (subgroupOfInertiaEquiv N χ)

omit [Finite G] in
@[simp]
theorem onSubgroupOfInertia_values
    (χ : IrreducibleCharacter N)
    (n : N.subgroupOf (inertia N χ)) :
    (onSubgroupOfInertia N χ).values n =
      χ.values (subgroupOfInertiaEquiv N χ n) :=
  rfl

omit [Finite G] in
/-- Every element of the inertia group fixes the transported character on
the canonical copy of `N`. -/
theorem onSubgroupOfInertia_invariant
    (χ : IrreducibleCharacter N) (g : inertia N χ) :
    IsInvariantUnder (N.subgroupOf (inertia N χ))
      (onSubgroupOfInertia N χ) g := by
  intro n
  have hg_inv : ((g : G)⁻¹) ∈ inertia N χ :=
    (inertia N χ).inv_mem g.property
  have hfix :
      conjBy N ((g : G)⁻¹) χ = χ :=
    (mem_inertia_iff N χ ((g : G)⁻¹)).mp hg_inv
  have hvalue := congrArg
    (fun θ : IrreducibleCharacter N ↦
      θ.values (subgroupOfInertiaEquiv N χ n)) hfix
  rw [conjBy_values] at hvalue
  change
    χ.values
        (subgroupOfInertiaEquiv N χ
          (RepresentationTheory.ClassFunction.conjByMulEquiv g n)) =
      χ.values (subgroupOfInertiaEquiv N χ n)
  have heq :
      subgroupOfInertiaEquiv N χ
          (RepresentationTheory.ClassFunction.conjByMulEquiv g n) =
        (MulAut.conjNormal ((g : G)⁻¹)).symm
          (subgroupOfInertiaEquiv N χ n) := by
    apply Subtype.ext
    have hc :=
      RepresentationTheory.ClassFunction.conjByMulEquiv_apply
        (K := inertia N χ)
        (H := N.subgroupOf (inertia N χ)) g n
    have hcG := congrArg
      (fun z : inertia N χ ↦ (z : G)) hc
    simp only [MulAut.conjNormal_symm_apply, inv_inv]
    dsimp only [subgroupOfInertiaEquiv,
      Subgroup.subgroupOfEquivOfLe]
    exact hcG
  rw [heq]
  exact hvalue

/-- Cyclicity of every inertia quotient, expressed without introducing a
global typeclass instance depending on a character. -/
def HasCyclicInertiaQuotients : Prop :=
  ∀ χ : IrreducibleCharacter N, IsCyclic (inertiaQuotient N χ)

/-- If every inertia quotient is cyclic, every irreducible character of `N`
extends to its inertia group. -/
theorem maximallyExtendible_of_cyclicInertiaQuotients
    (hcyclic : HasCyclicInertiaQuotients N) :
    IsMaximallyExtendible N := by
  intro χ
  let I : Subgroup G := inertia N χ
  let H : Subgroup I := N.subgroupOf I
  letI : H.Normal := inferInstance
  letI : IsCyclic (I ⧸ H) := hcyclic χ
  obtain ⟨q, hq⟩ :=
    isCyclic_iff_exists_zpowers_eq_top.mp
      (inferInstance : IsCyclic (I ⧸ H))
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H q
  let θ : IrreducibleCharacter H := onSubgroupOfInertia N χ
  obtain ⟨ψ, hψ⟩ :=
    exists_extension_of_cyclic_quotient H θ hq
      (onSubgroupOfInertia_invariant N χ g)
  refine ⟨ψ, ?_⟩
  intro n
  let nH : H :=
    (subgroupOfInertiaEquiv N χ).symm n
  have hn := hψ nH
  have helem :
      H.subtype nH = inertiaInclusion N χ n := by
    apply Subtype.ext
    rfl
  rw [← helem]
  calc
    ψ.values (H.subtype nH) = θ.values nH := hn
    _ = χ.values n := by
      change χ.values (subgroupOfInertiaEquiv N χ nH) =
        χ.values n
      rw [show subgroupOfInertiaEquiv N χ nH = n by
        exact (subgroupOfInertiaEquiv N χ).apply_symm_apply n]

/-- The corresponding extension map obtained by classical choice. -/
def extensionMapOfCyclicInertiaQuotients
    (hcyclic : HasCyclicInertiaQuotients N) :
    ExtensionMap N :=
  ExtensionMap.ofMaximallyExtendible
    (maximallyExtendible_of_cyclicInertiaQuotients N hcyclic)

end IrreducibleCharacter
end McKayConjecture
