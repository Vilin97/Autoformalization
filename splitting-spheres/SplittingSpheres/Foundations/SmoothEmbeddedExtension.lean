/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# Smooth extension from a closed embedded submanifold

A smooth map from a closed embedded manifold into a real normed space extends to a globally smooth
map on the ambient finite-dimensional normed space.  The source is modeled on a full normed vector
space, rather than a model with corners.  A fixed complement is chosen internally from the
immersion contained in the smooth-embedding hypothesis.

The proof constructs a local retraction in the normal-form charts of the immersion.  Closedness of
the embedded range excludes all remote branches of the image from that chart neighborhood.  The
local extensions are then glued by `exists_contMDiffMap_forall_mem_convex_of_local`, using a
singleton constraint on the embedded range and no constraint away from it.  Consequently the
resulting global map agrees exactly with the prescribed map, not merely near or up to homotopy.

No compactness of the source is required.  This theorem does not assert compact support of the
extension; a cutoff can be applied separately when the closed embedded range lies in the interior
of a compact support set.
-/

@[expose] public section

open Function Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace SplittingSpheres

universe uM uD uA uC uF

variable
    {D : Type uD} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {C : Type uC} [NormedAddCommGroup C] [NormedSpace ℝ C]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace D M]

private theorem immersion_normal_fst_eq
    {e : M → A} {x z : M}
    (h : Manifold.IsImmersionAtOfComplement C
      (modelWithCornersSelf ℝ D) (modelWithCornersSelf ℝ A) ∞ e x)
    (hz : z ∈ h.domChart.source) :
    (h.equiv.symm (h.codChart (e z))).1 = h.domChart z := by
  have ha : (h.domChart.extend (modelWithCornersSelf ℝ D)) z ∈
      (h.domChart.extend (modelWithCornersSelf ℝ D)).target :=
    (h.domChart.extend (modelWithCornersSelf ℝ D)).map_source (by simpa using hz)
  have hw := h.writtenInCharts ha
  simp only [Function.comp_apply] at hw
  rw [(h.domChart.extend (modelWithCornersSelf ℝ D)).left_inv (by simpa using hz)] at hw
  have hw' := congrArg h.equiv.symm hw
  simpa using congrArg Prod.fst hw'

private theorem immersion_local_retraction_eq
    {e : M → A} {x z : M}
    (h : Manifold.IsImmersionAtOfComplement C
      (modelWithCornersSelf ℝ D) (modelWithCornersSelf ℝ A) ∞ e x)
    (hz : z ∈ h.domChart.source) :
    h.domChart.symm ((h.equiv.symm (h.codChart (e z))).1) = z := by
  rw [immersion_normal_fst_eq h hz, h.domChart.left_inv hz]

/-- Let `e : M → A` be a closed-range smooth embedding of a boundaryless manifold into a
finite-dimensional real normed space.  Then every smooth `v : M → F` has a globally smooth
extension `V : A → F` satisfying `V (e x) = v x` at every point of `M`.

The fixed complement used to write the local normal retractions is chosen internally from the
immersion contained in `IsSmoothEmbedding`. -/
theorem exists_contDiff_extension_of_isClosed_range_isSmoothEmbedding
    [FiniteDimensional ℝ D] [FiniteDimensional ℝ A]
    [T2Space M] [IsManifold (modelWithCornersSelf ℝ D) ∞ M]
    {e : M → A} {v : M → F}
    (he : Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ D) (modelWithCornersSelf ℝ A) ∞ e)
    (herange : IsClosed (Set.range e))
    (hv : ContMDiff (modelWithCornersSelf ℝ D) (modelWithCornersSelf ℝ F) ∞ v) :
    ∃ V : A → F, ContDiff ℝ ∞ V ∧ ∀ x, V (e x) = v x := by
  classical
  let t : A → Set F := fun y ↦
    if hy : y ∈ Set.range e then {v (Classical.choose hy)} else Set.univ
  have ht : ∀ y, Convex ℝ (t y) := by
    intro y
    by_cases hy : y ∈ Set.range e
    · rw [show t y = {v (Classical.choose hy)} by simp only [t, dite_eq_left hy]]
      exact convex_singleton (𝕜 := ℝ) (v (Classical.choose hy))
    · rw [show t y = Set.univ by simp only [t, dite_eq_right hy]]
      exact convex_univ
  have heclosed : Topology.IsClosedEmbedding e := ⟨he.isEmbedding, herange⟩
  have hlocal : ∀ y₀ : A, ∃ U ∈ nhds y₀, ∃ g : A → F,
      ContMDiffOn (modelWithCornersSelf ℝ A) (modelWithCornersSelf ℝ F) ∞ g U ∧
        ∀ y ∈ U, g y ∈ t y := by
    intro y₀
    by_cases hy₀ : y₀ ∈ Set.range e
    · obtain ⟨x, rfl⟩ := hy₀
      let h := he.isImmersion.isImmersionOfComplement_complement x
      let q : A → D := fun y ↦ (h.equiv.symm (h.codChart y)).1
      let bad : Set A := e '' (h.domChart.source)ᶜ
      let U : Set A := h.codChart.source ∩ (q ⁻¹' h.domChart.target ∩ badᶜ)
      let g : A → F := fun y ↦ v (h.domChart.symm (q y))
      have hbad_closed : IsClosed bad := by
        exact heclosed.isClosedMap _ h.domChart.open_source.isClosed_compl
      have hex_not_bad : e x ∉ bad := by
        rintro ⟨z, hz, hezx⟩
        have hzx : z = x := he.isEmbedding.injective hezx
        exact hz (hzx ▸ h.mem_domChart_source)
      have hq_cont : ContinuousAt q (e x) := by
        have hc : ContinuousAt h.codChart (e x) :=
          (contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
            h.mem_codChart_source).continuousAt
        dsimp only [q]
        fun_prop
      have hq_mem : q (e x) ∈ h.domChart.target := by
        dsimp only [q]
        rw [immersion_normal_fst_eq h h.mem_domChart_source]
        exact h.domChart.map_source h.mem_domChart_source
      have hU : U ∈ nhds (e x) := by
        refine inter_mem (h.codChart.open_source.mem_nhds h.mem_codChart_source)
          (inter_mem ?_ ?_)
        · exact hq_cont.preimage_mem_nhds (h.domChart.open_target.mem_nhds hq_mem)
        · exact hbad_closed.isOpen_compl.mem_nhds hex_not_bad
      refine ⟨U, hU, g, ?_, ?_⟩
      · have hc : ContMDiffOn (modelWithCornersSelf ℝ A)
            (modelWithCornersSelf ℝ A) ∞ h.codChart U :=
          (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mono fun y hy ↦ hy.1
        have hlin : ContMDiff (modelWithCornersSelf ℝ A)
            (modelWithCornersSelf ℝ D) ∞ (fun a ↦ (h.equiv.symm a).1) := by
          rw [contMDiff_iff_contDiff]
          fun_prop
        have hq : ContMDiffOn (modelWithCornersSelf ℝ A)
            (modelWithCornersSelf ℝ D) ∞ q U := by
          exact (hlin.contMDiffOn (s := Set.univ)).comp hc (fun _ _ ↦ Set.mem_univ _)
        have hr : ContMDiffOn (modelWithCornersSelf ℝ D)
            (modelWithCornersSelf ℝ D) ∞ h.domChart.symm h.domChart.target :=
          contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
        have hret : ContMDiffOn (modelWithCornersSelf ℝ A)
            (modelWithCornersSelf ℝ D) ∞ (h.domChart.symm ∘ q) U :=
          hr.comp hq fun y hy ↦ hy.2.1
        exact (hv.contMDiffOn (s := Set.univ)).comp hret (fun _ _ ↦ Set.mem_univ _)
      · intro y hy
        by_cases hyrange : y ∈ Set.range e
        · let z := Classical.choose hyrange
          have hz : e z = y := Classical.choose_spec hyrange
          have hzsource : z ∈ h.domChart.source := by
            by_contra hznot
            exact hy.2.2 ⟨z, hznot, hz⟩
          have hret : h.domChart.symm (q y) = z := by
            rw [← hz]
            exact immersion_local_retraction_eq h hzsource
          simp only [t, dite_eq_left hyrange, Set.mem_singleton_iff]
          simp only [g, hret, z]
        · rw [show t y = Set.univ by simp only [t, dite_eq_right hyrange]]
          exact Set.mem_univ _
    · refine ⟨(Set.range e)ᶜ, herange.isOpen_compl.mem_nhds hy₀, fun _ ↦ 0, ?_, ?_⟩
      · exact contMDiffOn_const
      · intro y hy
        have hyrange : y ∉ Set.range e := hy
        rw [show t y = Set.univ by simp only [t, dite_eq_right hyrange]]
        exact Set.mem_univ _
  obtain ⟨V, hV⟩ :=
    exists_contMDiffMap_forall_mem_convex_of_local (modelWithCornersSelf ℝ A) ht hlocal
  refine ⟨V, ?_, fun x ↦ ?_⟩
  · rw [← contMDiff_iff_contDiff]
    exact V.contMDiff
  · have hrange : e x ∈ Set.range e := ⟨x, rfl⟩
    have hchoose : Classical.choose hrange = x := by
      apply he.isEmbedding.injective
      exact Classical.choose_spec hrange
    have := hV (e x)
    rw [show t (e x) = {v (Classical.choose hrange)} by
      simp only [t, dite_eq_left hrange], Set.mem_singleton_iff] at this
    exact this.trans (congrArg v hchoose)

end SplittingSpheres
