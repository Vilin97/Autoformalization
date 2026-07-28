/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Subgroup.Center
import McKayConjecture.GroupTheory.SurjectiveImageProper

/-!
# Local subgroups in a central-product quotient

Suppose a product of groups maps surjectively onto a central product and
the multiplication kernel is central.  Coordinate subgroups containing
the coordinate centers therefore contain the kernel.  If one coordinate
subgroup is proper, their product is proper, and so is its image in the
central product.

This is the group-theoretic properness mechanism used when local
subgroups of quasisimple components are assembled inside the layer.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace GroupTheory

variable {ι : Type u}
variable {G : ι → Type v} [∀ i, Group (G i)]

/-- The coordinatewise product of a family of subgroups. -/
def piLocalSubgroup
    (M : ∀ i, Subgroup (G i)) :
    Subgroup (∀ i, G i) :=
  Subgroup.pi Set.univ M

@[simp]
theorem mem_piLocalSubgroup
    (M : ∀ i, Subgroup (G i))
    (x : ∀ i, G i) :
    x ∈ piLocalSubgroup M ↔
      ∀ i, x i ∈ M i := by
  simp [piLocalSubgroup, Subgroup.mem_pi]

/-- If every coordinate subgroup contains the coordinate center, their
product contains the center of the whole direct product. -/
theorem center_pi_le_piLocalSubgroup
    (M : ∀ i, Subgroup (G i))
    (hcenter :
      ∀ i, Subgroup.center (G i) ≤ M i) :
    Subgroup.center (∀ i, G i) ≤
      piLocalSubgroup M := by
  rw [Subgroup.center_pi]
  intro x hx
  rw [mem_piLocalSubgroup]
  intro i
  exact hcenter i (hx i (Set.mem_univ i))

/-- A coordinatewise product is proper as soon as one coordinate
subgroup is proper. -/
theorem piLocalSubgroup_lt_top_of_exists_lt_top
    (M : ∀ i, Subgroup (G i))
    (hproper : ∃ i, M i < ⊤) :
    piLocalSubgroup M < ⊤ := by
  classical
  obtain ⟨i, hi⟩ := hproper
  rw [lt_top_iff_ne_top]
  intro htop
  apply hi.ne
  rw [Subgroup.eq_top_iff']
  intro x
  have hx :
      Pi.mulSingle i x ∈
        piLocalSubgroup M := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [mem_piLocalSubgroup] at hx
  simpa using hx i

variable {H : Type w} [Group H]

/-- The image of coordinate local subgroups in a central quotient is
proper when they contain the coordinate centers and at least one of
them is proper. -/
theorem map_piLocalSubgroup_lt_top_of_centralKernel
    (f : (∀ i, G i) →* H)
    (hf : Function.Surjective f)
    (hker :
      f.ker ≤
        Subgroup.center (∀ i, G i))
    (M : ∀ i, Subgroup (G i))
    (hcenter :
      ∀ i, Subgroup.center (G i) ≤ M i)
    (hproper : ∃ i, M i < ⊤) :
    (piLocalSubgroup M).map f < ⊤ := by
  apply
    map_lt_top_of_surjective_of_ker_le_of_lt_top
      f hf (piLocalSubgroup M)
  · exact
      hker.trans
        (center_pi_le_piLocalSubgroup M hcenter)
  · exact
      piLocalSubgroup_lt_top_of_exists_lt_top
        M hproper

end GroupTheory
end McKayConjecture
