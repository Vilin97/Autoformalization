/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Compactly supported smooth cutoffs

A smooth map on a finite-dimensional real normed space can be multiplied by a smooth cutoff so
that it is unchanged on a prescribed compact set and vanishes outside a prescribed open
neighborhood.  The resulting map has compact support.  This packages the support-control step
used after extending data from an embedded trace.
-/

@[expose] public section

open Function Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace SplittingSpheres

/-- Cut a smooth map off outside an open neighborhood without changing it on a compact subset. -/
theorem exists_contDiff_compactSupport_eqOn_of_isCompact_subset_isOpen
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f)
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ g : E → F,
      ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
        EqOn g f K ∧ (∀ x, f x = 0 → g x = 0) ∧ ∀ x ∉ U, g x = 0 := by
  obtain ⟨L, hLcompact, hLclosed, hKLint, hLU⟩ :=
    exists_compact_closed_between hK hU hKU
  obtain ⟨χ, hχone, hχzero, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (I := 𝓘(ℝ, E)) (n := (⊤ : ℕ∞)) hK.isClosed hKLint
  let g : E → F := fun x ↦ χ x • f x
  have hχdiff : ContDiff ℝ ∞ (χ : E → ℝ) := χ.contMDiff.contDiff
  have hχsupport : Function.support (χ : E → ℝ) ⊆ L := by
    intro x hx
    by_contra hxL
    exact hx (hχzero x hxL)
  have hχtsupport : tsupport (χ : E → ℝ) ⊆ L :=
    closure_minimal hχsupport hLclosed
  have hχcompact : HasCompactSupport (χ : E → ℝ) := by
    exact IsCompact.of_isClosed_subset hLcompact isClosed_closure hχtsupport
  refine ⟨g, hχdiff.smul hf, hχcompact.smul_right, ?_, ?_, ?_, ?_⟩
  · change tsupport (fun x ↦ χ x • f x) ⊆ U
    exact (tsupport_smul_subset_left (χ : E → ℝ) f).trans <|
      hχtsupport.trans hLU
  · intro x hx
    change χ x • f x = f x
    rw [hχone.self_of_nhdsSet x hx, one_smul]
  · intro x hx
    change χ x • f x = 0
    rw [hx, smul_zero]
  · intro x hxU
    change χ x • f x = 0
    rw [hχzero x (fun hxL ↦ hxU (hLU hxL)), zero_smul]

end SplittingSpheres
