/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Proper images under a surjective homomorphism

A proper subgroup need not have proper image under a quotient map.
The exact extra condition is that it contain the kernel.  This small
lemma is used when local subgroups of components are multiplied onto a
central product: the multiplication kernel is central and hence lies in
the product of the local subgroups.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} {H : Type v}
variable [Group G] [Group H]

/-- A proper subgroup containing the kernel of a surjective homomorphism
has proper image. -/
theorem map_lt_top_of_surjective_of_ker_le_of_lt_top
    (f : G →* H)
    (_hf : Function.Surjective f)
    (M : Subgroup G)
    (hker : f.ker ≤ M)
    (hM : M < ⊤) :
    M.map f < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  apply hM.ne
  have hcomap :=
    congrArg (Subgroup.comap f) htop
  rw [Subgroup.comap_map_eq_self hker,
    Subgroup.comap_top] at hcomap
  exact hcomap

/-- Equivalence form: for a surjective homomorphism and a subgroup
containing its kernel, properness is reflected by the image. -/
theorem map_lt_top_iff_of_surjective_of_ker_le
    (f : G →* H)
    (hf : Function.Surjective f)
    (M : Subgroup G)
    (hker : f.ker ≤ M) :
    M.map f < ⊤ ↔ M < ⊤ := by
  constructor
  · intro hmap
    rw [lt_top_iff_ne_top]
    intro htop
    apply hmap.ne
    rw [htop, Subgroup.map_top_of_surjective f hf]
  · exact
      map_lt_top_of_surjective_of_ker_le_of_lt_top
        f hf M hker

end GroupTheory
end McKayConjecture
