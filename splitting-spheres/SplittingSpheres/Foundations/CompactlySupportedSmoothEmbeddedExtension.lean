/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.CompactlySupportedSmoothCutoff
public import SplittingSpheres.Foundations.SmoothEmbeddedExtension

/-!
# Compactly supported extension from a closed embedded submanifold

Combine smooth extension from a closed embedded manifold with a compactly supported cutoff.  It is
enough that every point where the prescribed map is nonzero lands in one compact subset of the
chosen open support region.  The resulting global smooth extension agrees everywhere on the
embedded source, has compact support, and has topological support contained in that open region.
-/

@[expose] public section

open Function Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace SplittingSpheres

universe uM uD uA uF

variable
    {D : Type uD} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace D M]

/-- Extend smooth data from a closed embedded manifold, with compact support inside a prescribed
open set, when all its nonzero values occur over one compact subset. -/
theorem exists_contDiff_compactSupport_extension_of_isClosed_range_isSmoothEmbedding
    [FiniteDimensional ℝ D] [FiniteDimensional ℝ A]
    [T2Space M] [IsManifold (modelWithCornersSelf ℝ D) ∞ M]
    {e : M → A} {v : M → F}
    (he : Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ D) (modelWithCornersSelf ℝ A) ∞ e)
    (herange : IsClosed (Set.range e))
    (hv : ContMDiff (modelWithCornersSelf ℝ D) (modelWithCornersSelf ℝ F) ∞ v)
    {K U : Set A} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hactive : ∀ x, v x ≠ 0 → e x ∈ K) :
    ∃ V : A → F,
      ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧ tsupport V ⊆ U ∧
        ∀ x, V (e x) = v x := by
  obtain ⟨W, hWdiff, hW⟩ :=
    exists_contDiff_extension_of_isClosed_range_isSmoothEmbedding
      he herange hv
  obtain ⟨V, hVdiff, hVcompact, hVsupp, hVK, hVzero, _⟩ :=
    exists_contDiff_compactSupport_eqOn_of_isCompact_subset_isOpen
      W hWdiff hK hU hKU
  refine ⟨V, hVdiff, hVcompact, hVsupp, fun x ↦ ?_⟩
  by_cases hx : v x = 0
  · rw [hx]
    exact hVzero (e x) ((hW x).trans hx)
  · exact (hVK (hactive x hx)).trans (hW x)

end SplittingSpheres
