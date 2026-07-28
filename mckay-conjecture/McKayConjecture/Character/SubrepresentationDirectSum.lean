/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.Projection
import Mathlib.RepresentationTheory.Intertwining

/-!
# Equivariant complementary subrepresentations

Complementary subrepresentations give equivariant inclusion and
projection maps, and their product representation is equivalent to
the ambient representation.
-/

noncomputable section

namespace Representation
namespace Subrepresentation

variable {k G V : Type}
variable [Field k] [Group G]
variable [AddCommGroup V] [Module k V]
variable {ρ : Representation k G V}

/-- The inclusion of a subrepresentation into its ambient
representation. -/
def inclusionIntertwiningMap (U : Subrepresentation ρ) :
    IntertwiningMap U.toRepresentation ρ where
  toLinearMap := U.toSubmodule.subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    rfl

/-- Projection onto a subrepresentation along an invariant
complement is equivariant. -/
def projectionIntertwiningMap
    (U W : Subrepresentation ρ)
    (hUW : IsCompl U.toSubmodule W.toSubmodule) :
    IntertwiningMap ρ U.toRepresentation where
  toLinearMap :=
    U.toSubmodule.projectionOnto W.toSubmodule hUW
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change
      ((U.toSubmodule.projectionOnto W.toSubmodule hUW)
          (ρ g x) : V) =
        ρ g
          ((U.toSubmodule.projectionOnto W.toSubmodule hUW x : U) :
            V)
    let y : U :=
      U.toSubmodule.projectionOnto W.toSubmodule hUW x
    let z : W :=
      ⟨x - (y : V),
        U.toSubmodule.sub_projection_mem hUW x⟩
    have hxy : x = (y : V) + (z : V) := by
      simp only [z, y, add_sub_cancel]
    rw [hxy, map_add, map_add]
    have hgy : ρ g (y : V) ∈ U.toSubmodule :=
      U.apply_mem_toSubmodule g y.property
    have hgz : ρ g (z : V) ∈ W.toSubmodule :=
      W.apply_mem_toSubmodule g z.property
    rw [Submodule.projectionOnto_apply_of_mem_left hUW hgy,
      Submodule.projectionOnto_apply_of_mem_right hUW hgz]
    simp

@[simp]
theorem projection_comp_inclusion
    (U W : Subrepresentation ρ)
    (hUW : IsCompl U.toSubmodule W.toSubmodule) :
    (projectionIntertwiningMap U W hUW).comp
        (inclusionIntertwiningMap U) =
      IntertwiningMap.id U.toRepresentation := by
  apply IntertwiningMap.ext
  exact Submodule.projectionOnto_comp_subtype hUW

/-- Complementary subrepresentations identify the ambient
representation with their product representation. -/
def prodEquivOfIsCompl
    (U W : Subrepresentation ρ)
    (hUW : IsCompl U.toSubmodule W.toSubmodule) :
    (U.toRepresentation.prod W.toRepresentation).Equiv ρ :=
  Representation.Equiv.mk
    (U.toSubmodule.prodEquivOfIsCompl W.toSubmodule hUW)
    (by
      intro g
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply]
      change
        ρ g (x.1 : V) + ρ g (x.2 : V) =
          ρ g ((x.1 : V) + (x.2 : V))
      exact (map_add (ρ g) (x.1 : V) (x.2 : V)).symm)

end Subrepresentation
end Representation
