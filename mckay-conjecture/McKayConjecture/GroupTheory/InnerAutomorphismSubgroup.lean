/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# The subgroup of inner automorphisms

This file names the range of the conjugation homomorphism and records its
normality in the full automorphism group.  The normality theorem is the
small group-theoretic input needed to pass from global automorphism
generation to generation of a Sylow stabilizer.
-/

namespace McKayConjecture
namespace GroupTheory

universe u

variable (G : Type u) [Group G]

/-- The subgroup of `MulAut G` consisting of inner automorphisms. -/
def innerAutomorphismSubgroup :
    Subgroup (MulAut G) :=
  (MulAut.conj : G →* MulAut G).range

/-- Inner automorphisms form a normal subgroup of the full automorphism
group. -/
instance innerAutomorphismSubgroup_normal :
    (innerAutomorphismSubgroup G).Normal where
  conj_mem a ha α := by
    obtain ⟨g, rfl⟩ := ha
    refine ⟨α g, ?_⟩
    apply MulEquiv.ext
    intro x
    simp [MulAut.conj_apply]

@[simp]
theorem mem_innerAutomorphismSubgroup_iff
    (a : MulAut G) :
    a ∈ innerAutomorphismSubgroup G ↔
      ∃ g : G, MulAut.conj g = a :=
  Iff.rfl

end GroupTheory
end McKayConjecture
