/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PermutationModuleOrbitDecomposition

/-!
# Equivariant maps for the orbit decomposition

The internal orbit decomposition of a permutation module is
equivariant.  This file bundles its inclusions and canonical
components as intertwining maps and proves that their composites
resolve the identity.
-/

noncomputable section

namespace Representation
namespace PermutationModuleBasis

variable {k P V ι : Type}
variable [Field k] [Group P]
variable [AddCommGroup V] [Module k V]
variable [DistribMulAction P V] [SMulCommClass P k V]
variable [MulAction P ι] [Finite ι]

variable (B : PermutationModuleBasis
  (k := k) (P := P) (V := V) (ι := ι))

local notation "ρ" => B.representation
local notation "Ω" => MulAction.orbitRel.Quotient P ι

noncomputable local instance orbitIntertwiningQuotientFintype :
    Fintype Ω :=
  Fintype.ofFinite Ω

noncomputable local instance orbitIntertwiningQuotientDecidableEq :
    DecidableEq Ω :=
  Classical.decEq Ω

omit [SMulCommClass P k V] [Finite ι] in
/-- A basis vector belongs to the orbit submodule indexed by its
orbit. -/
theorem basis_mem_orbitSubmodule
    (ω : Ω) (i : ι) (hi : i ∈ ω.orbit) :
    B.basis i ∈ B.orbitSubmodule ω := by
  rw [B.orbitSubmodule_eq_span_image]
  exact Submodule.subset_span ⟨i, hi, rfl⟩

/-- The inclusion of an orbit factor into the full permutation
module, bundled as an intertwining map. -/
def orbitInclusionIntertwiningMap (ω : Ω) :
    IntertwiningMap
      (B.orbitSubrepresentation ω).toRepresentation ρ where
  toLinearMap := (B.orbitSubmodule ω).subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    rfl

/-- The canonical component onto an orbit factor, bundled as an
intertwining map. -/
def orbitComponentIntertwiningMap (ω : Ω) :
    IntertwiningMap ρ
      (B.orbitSubrepresentation ω).toRepresentation where
  toLinearMap := B.orbitComponent ω
  isIntertwining' g := by
    apply B.basis.ext
    intro i
    change
      B.orbitComponent ω (ρ g (B.basis i)) =
        (B.orbitSubrepresentation ω).toRepresentation g
          (B.orbitComponent ω (B.basis i))
    let τ : Ω := Quotient.mk'' i
    have hiτ : i ∈ τ.orbit :=
      (MulAction.orbitRel.Quotient.mem_orbit).mpr rfl
    have hbi : B.basis i ∈ B.orbitSubmodule τ :=
      B.basis_mem_orbitSubmodule τ i hiτ
    have hgbi :
        ρ g (B.basis i) ∈ B.orbitSubmodule τ :=
      (B.orbitSubrepresentation τ).apply_mem_toSubmodule g hbi
    by_cases hτω : τ = ω
    · subst ω
      rw [B.orbitComponent_of_mem hgbi,
        B.orbitComponent_of_mem hbi]
      apply Subtype.ext
      rfl
    · rw [B.orbitComponent_of_mem_ne hτω hgbi,
        B.orbitComponent_of_mem_ne hτω hbi]
      exact (map_zero
        ((B.orbitSubrepresentation ω).toRepresentation g)).symm

omit [Finite ι] in
@[simp]
theorem orbitInclusionIntertwiningMap_apply
    (ω : Ω) (v : B.orbitSubmodule ω) :
    B.orbitInclusionIntertwiningMap ω v = (v : V) :=
  rfl

omit [Finite ι] in
@[simp]
theorem orbitComponentIntertwiningMap_apply
    (ω : Ω) (v : V) :
    B.orbitComponentIntertwiningMap ω v =
      B.orbitComponent ω v :=
  rfl

/-- The sum of orbit inclusion followed by orbit projection is the
identity of the permutation representation. -/
theorem sum_orbitInclusion_comp_orbitComponent :
    (∑ ω : Ω,
      (B.orbitInclusionIntertwiningMap ω).comp
        (B.orbitComponentIntertwiningMap ω)) =
      IntertwiningMap.id ρ := by
  apply IntertwiningMap.ext
  simp only [IntertwiningMap.toLinearMap_sum]
  apply B.basis.ext
  intro i
  simp only [LinearMap.sum_apply,
    IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
    IntertwiningMap.toLinearMap_id, LinearMap.id_apply]
  let τ : Ω := Quotient.mk'' i
  have hiτ : i ∈ τ.orbit :=
    (MulAction.orbitRel.Quotient.mem_orbit).mpr rfl
  have hbi : B.basis i ∈ B.orbitSubmodule τ :=
    B.basis_mem_orbitSubmodule τ i hiτ
  rw [Finset.sum_eq_single τ]
  · exact congrArg Subtype.val
      (B.orbitComponent_of_mem hbi)
  · intro ω _ hωτ
    exact congrArg Subtype.val
      (B.orbitComponent_of_mem_ne hωτ.symm hbi)
  · simp

end PermutationModuleBasis
end Representation
