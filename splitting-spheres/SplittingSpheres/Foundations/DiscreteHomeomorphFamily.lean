/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Families of homeomorphisms over a discrete base

A pointwise family `e d : X ≃ₜ Y` need not vary continuously with `d` over an arbitrary base.
When the base is discrete, it assembles canonically into a homeomorphism `D × X ≃ₜ D × Y`
which fixes the first coordinate.  This is useful for independently reparametrizing finitely or
discretely labelled attaching maps.
-/

@[expose] public section

open Function Set Topology

noncomputable section

namespace SplittingSpheres

variable {D X Y : Type*}
variable [TopologicalSpace D] [DiscreteTopology D]
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Assemble a label-dependent family of homeomorphisms over a discrete base. -/
def discreteFamilyHomeomorph (e : D → X ≃ₜ Y) :
    D × X ≃ₜ D × Y where
  toFun p := (p.1, e p.1 p.2)
  invFun p := (p.1, (e p.1).symm p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro p
    have hfixed : Continuous (fun q : D × X ↦ (q.1, e p.1 q.2)) :=
      continuous_fst.prodMk ((e p.1).continuous.comp continuous_snd)
    apply hfixed.continuousAt.congr_of_eventuallyEq
    filter_upwards [
      ((isOpen_discrete ({p.1} : Set D)).preimage continuous_fst).mem_nhds
        (by simp)] with q hq
    change q.1 ∈ ({p.1} : Set D) at hq
    simp only [mem_singleton_iff] at hq
    rw [hq]
  continuous_invFun := by
    rw [continuous_iff_continuousAt]
    intro p
    have hfixed : Continuous (fun q : D × Y ↦ (q.1, (e p.1).symm q.2)) :=
      continuous_fst.prodMk ((e p.1).symm.continuous.comp continuous_snd)
    apply hfixed.continuousAt.congr_of_eventuallyEq
    filter_upwards [
      ((isOpen_discrete ({p.1} : Set D)).preimage continuous_fst).mem_nhds
        (by simp)] with q hq
    change q.1 ∈ ({p.1} : Set D) at hq
    simp only [mem_singleton_iff] at hq
    rw [hq]

/-- The assembled family fixes the label and applies the corresponding homeomorphism. -/
@[simp]
theorem discreteFamilyHomeomorph_apply
    (e : D → X ≃ₜ Y) (p : D × X) :
    discreteFamilyHomeomorph e p = (p.1, e p.1 p.2) :=
  rfl

/-- The inverse assembled family fixes the label and applies the corresponding inverse. -/
@[simp]
theorem discreteFamilyHomeomorph_symm_apply
    (e : D → X ≃ₜ Y) (p : D × Y) :
    (discreteFamilyHomeomorph e).symm p =
      (p.1, (e p.1).symm p.2) :=
  rfl

end SplittingSpheres

end
