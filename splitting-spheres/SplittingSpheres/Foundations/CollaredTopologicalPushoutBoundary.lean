/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.CollaredTopologicalPushoutManifold
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Boundaries of collared topological pushouts

This file identifies the manifold boundary of the explicit smooth atlas on a collared topological
pushout.  Its seam chart and its two off-seam chart families are local diffeomorphisms for that
atlas.  Consequently, when the seam model has empty boundary, the pushout boundary consists
exactly of the boundary points of the two pieces that do not lie in their attaching ranges.

The final theorem packages the same conclusion for the literal signed seam map used by the
automatic compatibility criterion.  All results concern the generated atlas itself; no smooth
structure is transported across a merely topological equivalence.
-/

@[expose] public section

noncomputable section

open Function Set Topology TopologicalSpace IsManifold
open scoped ContDiff Manifold

universe u

namespace SplittingSpheres

variable {A X Y N H E 𝕜 : Type u}
variable [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalSpace N] [TopologicalSpace H]
variable [Nonempty H] [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [ChartedSpace H X] [ChartedSpace H Y] [ChartedSpace H N]
variable (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
variable (f : C(A, X)) (g : C(A, Y))

private def partialDiffeomorphOfAtlas
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I n M) :
    PartialDiffeomorph I I M H n where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he

/-- The seam map is a local diffeomorphism for the generated topological-pushout atlas. -/
theorem isLocalDiffeomorph_topologicalPushoutSeamMap
    [IsManifold I n N]
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    (hcover : ∀ a, ∃ q, seam q = topologicalPushoutInl f g (f a))
    (hcompat : ∀ i j : TopologicalPushoutAtlasIndex f g N,
      (topologicalPushoutAtlasChart (H := H)
        f g hf hg seam hseam i).symm.trans
          (topologicalPushoutAtlasChart (H := H)
            f g hf hg seam hseam j) ∈
        contDiffGroupoid n I) :
    letI := topologicalPushoutChartedSpace (H := H)
      f g hf hg seam hseam hcover
    IsLocalDiffeomorph I I n seam := by
  let _ := topologicalPushoutChartedSpace (H := H)
    f g hf hg seam hseam hcover
  let _ : IsManifold I n (TopologicalPushout f g) :=
    isManifold_topologicalPushoutChartedSpace f g I n
      hf hg seam hseam hcover hcompat
  intro q
  let sourceChart : PartialDiffeomorph I I N H n :=
    partialDiffeomorphOfAtlas I n (chartAt H q)
      (chart_mem_maximalAtlas q)
  let targetOpenChart :=
    topologicalPushoutSeamChart (H := H) f g seam hseam q
  have htargetAtlas : targetOpenChart ∈
      atlas H (TopologicalPushout f g) := by
    exact ⟨TopologicalPushoutAtlasIndex.seam q, rfl⟩
  have htargetMax : targetOpenChart ∈
      IsManifold.maximalAtlas I n (TopologicalPushout f g) :=
    StructureGroupoid.subset_maximalAtlas
      (contDiffGroupoid n I) htargetAtlas
  let targetChart : PartialDiffeomorph I I
      (TopologicalPushout f g) H n :=
    partialDiffeomorphOfAtlas I n targetOpenChart htargetMax
  let phi := sourceChart.trans targetChart.symm
  refine ⟨phi, ?_, ?_⟩
  · change q ∈ sourceChart.source ∩ sourceChart ⁻¹' targetChart.symm.source
    refine ⟨mem_chart_source H q, ?_⟩
    change (chartAt H q) q ∈ targetOpenChart.target
    simp [targetOpenChart, topologicalPushoutSeamChart]
  · intro r hr
    change seam r = targetChart.symm (sourceChart r)
    change seam r = targetOpenChart.symm ((chartAt H q) r)
    rw [show targetOpenChart =
      (chartAt H q).lift_openEmbedding hseam by rfl]
    simp only [OpenPartialHomeomorph.lift_openEmbedding_symm,
      comp_apply]
    rw [(chartAt H q).left_inv hr.1]

/-- The left off-seam coprojection is a local diffeomorphism for the generated
topological-pushout atlas. -/
theorem isLocalDiffeomorph_topologicalPushoutInlOffSeamMap'
    [IsManifold I n X]
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    (hcover : ∀ a, ∃ q, seam q = topologicalPushoutInl f g (f a))
    (hcompat : ∀ i j : TopologicalPushoutAtlasIndex f g N,
      (topologicalPushoutAtlasChart (H := H)
        f g hf hg seam hseam i).symm.trans
          (topologicalPushoutAtlasChart (H := H)
            f g hf hg seam hseam j) ∈
        contDiffGroupoid n I) :
    letI := topologicalPushoutChartedSpace (H := H)
      f g hf hg seam hseam hcover
    IsLocalDiffeomorph I I n
      (topologicalPushoutInlOffSeamMap' f g hf) := by
  let _ := topologicalPushoutChartedSpace (H := H)
    f g hf hg seam hseam hcover
  let _ : IsManifold I n (TopologicalPushout f g) :=
    isManifold_topologicalPushoutChartedSpace f g I n
      hf hg seam hseam hcover hcompat
  intro x
  let U := topologicalPushoutInlOffSeamOpens f hf
  let x' : TopologicalPushoutInlOffSeamDomain f := ⟨x.1, x.2⟩
  let sourceOpenChart : OpenPartialHomeomorph U H :=
    (chartAt H x.1).subtypeRestr ⟨x⟩
  have hsourceMax : sourceOpenChart ∈
      IsManifold.maximalAtlas I n U :=
    StructureGroupoid.subtypeRestr_mem_maximalAtlas
      (G := contDiffGroupoid n I)
      (chart_mem_atlas H x.1) ⟨x⟩
  let sourceChart : PartialDiffeomorph I I U H n :=
    partialDiffeomorphOfAtlas I n sourceOpenChart hsourceMax
  let targetOpenChart :=
    topologicalPushoutInlOffSeamChart (H := H) f g hf hg x'
  have htargetAtlas : targetOpenChart ∈
      atlas H (TopologicalPushout f g) := by
    exact ⟨TopologicalPushoutAtlasIndex.inl x', rfl⟩
  have htargetMax : targetOpenChart ∈
      IsManifold.maximalAtlas I n (TopologicalPushout f g) :=
    StructureGroupoid.subset_maximalAtlas
      (contDiffGroupoid n I) htargetAtlas
  let targetChart : PartialDiffeomorph I I
      (TopologicalPushout f g) H n :=
    partialDiffeomorphOfAtlas I n targetOpenChart htargetMax
  let phi := sourceChart.trans targetChart.symm
  refine ⟨phi, ?_, ?_⟩
  · change x ∈ sourceChart.source ∩ sourceChart ⁻¹' targetChart.symm.source
    have hxsource : x ∈ sourceOpenChart.source := by
      simp [sourceOpenChart]
    refine ⟨hxsource, ?_⟩
    change sourceOpenChart x ∈ targetOpenChart.target
    exact sourceOpenChart.map_source hxsource
  · intro y hy
    change topologicalPushoutInlOffSeamMap' f g hf y =
      targetChart.symm (sourceChart y)
    change topologicalPushoutInlOffSeamMap' f g hf y =
      targetOpenChart.symm (sourceOpenChart y)
    rw [show targetOpenChart = sourceOpenChart.lift_openEmbedding
      (isOpenEmbedding_topologicalPushoutInlOffSeamMap' f g hf hg) by rfl]
    simp only [OpenPartialHomeomorph.lift_openEmbedding_symm, comp_apply]
    rw [sourceOpenChart.left_inv hy.1]

/-- The right off-seam coprojection is a local diffeomorphism for the generated
topological-pushout atlas. -/
theorem isLocalDiffeomorph_topologicalPushoutInrOffSeamMap'
    [IsManifold I n Y]
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    (hcover : ∀ a, ∃ q, seam q = topologicalPushoutInl f g (f a))
    (hcompat : ∀ i j : TopologicalPushoutAtlasIndex f g N,
      (topologicalPushoutAtlasChart (H := H)
        f g hf hg seam hseam i).symm.trans
          (topologicalPushoutAtlasChart (H := H)
            f g hf hg seam hseam j) ∈
        contDiffGroupoid n I) :
    letI := topologicalPushoutChartedSpace (H := H)
      f g hf hg seam hseam hcover
    IsLocalDiffeomorph I I n
      (topologicalPushoutInrOffSeamMap' f g hg) := by
  let _ := topologicalPushoutChartedSpace (H := H)
    f g hf hg seam hseam hcover
  let _ : IsManifold I n (TopologicalPushout f g) :=
    isManifold_topologicalPushoutChartedSpace f g I n
      hf hg seam hseam hcover hcompat
  intro y
  let V := topologicalPushoutInrOffSeamOpens g hg
  let y' : TopologicalPushoutInrOffSeamDomain g := ⟨y.1, y.2⟩
  let sourceOpenChart : OpenPartialHomeomorph V H :=
    (chartAt H y.1).subtypeRestr ⟨y⟩
  have hsourceMax : sourceOpenChart ∈
      IsManifold.maximalAtlas I n V :=
    StructureGroupoid.subtypeRestr_mem_maximalAtlas
      (G := contDiffGroupoid n I)
      (chart_mem_atlas H y.1) ⟨y⟩
  let sourceChart : PartialDiffeomorph I I V H n :=
    partialDiffeomorphOfAtlas I n sourceOpenChart hsourceMax
  let targetOpenChart :=
    topologicalPushoutInrOffSeamChart (H := H) f g hf hg y'
  have htargetAtlas : targetOpenChart ∈
      atlas H (TopologicalPushout f g) := by
    exact ⟨TopologicalPushoutAtlasIndex.inr y', rfl⟩
  have htargetMax : targetOpenChart ∈
      IsManifold.maximalAtlas I n (TopologicalPushout f g) :=
    StructureGroupoid.subset_maximalAtlas
      (contDiffGroupoid n I) htargetAtlas
  let targetChart : PartialDiffeomorph I I
      (TopologicalPushout f g) H n :=
    partialDiffeomorphOfAtlas I n targetOpenChart htargetMax
  let phi := sourceChart.trans targetChart.symm
  refine ⟨phi, ?_, ?_⟩
  · change y ∈ sourceChart.source ∩ sourceChart ⁻¹' targetChart.symm.source
    have hysource : y ∈ sourceOpenChart.source := by
      simp [sourceOpenChart]
    refine ⟨hysource, ?_⟩
    change sourceOpenChart y ∈ targetOpenChart.target
    exact sourceOpenChart.map_source hysource
  · intro z hz
    change topologicalPushoutInrOffSeamMap' f g hg z =
      targetChart.symm (sourceChart z)
    change topologicalPushoutInrOffSeamMap' f g hg z =
      targetOpenChart.symm (sourceOpenChart z)
    rw [show targetOpenChart = sourceOpenChart.lift_openEmbedding
      (isOpenEmbedding_topologicalPushoutInrOffSeamMap' f g hf hg) by rfl]
    simp only [OpenPartialHomeomorph.lift_openEmbedding_symm, comp_apply]
    rw [sourceOpenChart.left_inv hz.1]

/-- For the generated atlas on a collared pushout with boundaryless seam, the boundary is exactly
the union of the two old boundaries away from their attaching ranges. -/
theorem boundary_topologicalPushoutChartedSpace
    [IsManifold I n X] [IsManifold I n Y] [IsManifold I n N]
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    (hcover : ∀ a, ∃ q, seam q = topologicalPushoutInl f g (f a))
    (hcompat : ∀ i j : TopologicalPushoutAtlasIndex f g N,
      (topologicalPushoutAtlasChart (H := H)
        f g hf hg seam hseam i).symm.trans
          (topologicalPushoutAtlasChart (H := H)
            f g hf hg seam hseam j) ∈
        contDiffGroupoid n I)
    (hn : n ≠ 0)
    (hNboundary : I.boundary N = ∅) :
    letI := topologicalPushoutChartedSpace (H := H)
      f g hf hg seam hseam hcover
    I.boundary (TopologicalPushout f g) =
      topologicalPushoutInl f g '' (I.boundary X \ range f) ∪
        topologicalPushoutInr f g '' (I.boundary Y \ range g) := by
  let _ := topologicalPushoutChartedSpace (H := H)
    f g hf hg seam hseam hcover
  let _ : IsManifold I n (TopologicalPushout f g) :=
    isManifold_topologicalPushoutChartedSpace f g I n
      hf hg seam hseam hcover hcompat
  have hseamLocal : IsLocalDiffeomorph I I n seam :=
    isLocalDiffeomorph_topologicalPushoutSeamMap I n f g
      hf hg seam hseam hcover hcompat
  have hinlLocal : IsLocalDiffeomorph I I n
      (topologicalPushoutInlOffSeamMap' f g hf) :=
    isLocalDiffeomorph_topologicalPushoutInlOffSeamMap' I n f g
      hf hg seam hseam hcover hcompat
  have hinrLocal : IsLocalDiffeomorph I I n
      (topologicalPushoutInrOffSeamMap' f g hg) :=
    isLocalDiffeomorph_topologicalPushoutInrOffSeamMap' I n f g
      hf hg seam hseam hcover hcompat
  ext z
  constructor
  · intro hz
    rcases topologicalPushout_jointly_surjective f g z with
      ⟨x, rfl⟩ | ⟨y, rfl⟩
    · by_cases hx : x ∈ range f
      · obtain ⟨a, rfl⟩ := hx
        obtain ⟨q, hq⟩ := hcover a
        have hqBoundary : q ∈ I.boundary N :=
          ((hseamLocal q).isBoundaryPoint_iff hn).mpr (by rwa [hq])
        rw [hNboundary] at hqBoundary
        exact hqBoundary.elim
      · let U := topologicalPushoutInlOffSeamOpens f hf
        let x' : U := ⟨x, hx⟩
        have hxBoundary : x' ∈ I.boundary U :=
          ((hinlLocal x').isBoundaryPoint_iff hn).mpr hz
        have hxAmbient : x ∈ I.boundary X := by
          change x' ∈ I.boundary U at hxBoundary
          rwa [I.boundary_open] at hxBoundary
        exact Or.inl ⟨x, ⟨hxAmbient, hx⟩, rfl⟩
    · by_cases hy : y ∈ range g
      · obtain ⟨a, rfl⟩ := hy
        obtain ⟨q, hq⟩ := hcover a
        have hqImage : seam q =
            topologicalPushoutInr f g (g a) :=
          hq.trans (topologicalPushout_condition f g a)
        have hqBoundary : q ∈ I.boundary N :=
          ((hseamLocal q).isBoundaryPoint_iff hn).mpr (by rwa [hqImage])
        rw [hNboundary] at hqBoundary
        exact hqBoundary.elim
      · let V := topologicalPushoutInrOffSeamOpens g hg
        let y' : V := ⟨y, hy⟩
        have hyBoundary : y' ∈ I.boundary V :=
          ((hinrLocal y').isBoundaryPoint_iff hn).mpr hz
        have hyAmbient : y ∈ I.boundary Y := by
          change y' ∈ I.boundary V at hyBoundary
          rwa [I.boundary_open] at hyBoundary
        exact Or.inr ⟨y, ⟨hyAmbient, hy⟩, rfl⟩
  · rintro (⟨x, ⟨hxBoundary, hx⟩, rfl⟩ |
      ⟨y, ⟨hyBoundary, hy⟩, rfl⟩)
    · let U := topologicalPushoutInlOffSeamOpens f hf
      let x' : U := ⟨x, hx⟩
      apply ((hinlLocal x').isBoundaryPoint_iff hn).mp
      change x' ∈ I.boundary U
      rw [I.boundary_open]
      exact hxBoundary
    · let V := topologicalPushoutInrOffSeamOpens g hg
      let y' : V := ⟨y, hy⟩
      apply ((hinrLocal y').isBoundaryPoint_iff hn).mp
      change y' ∈ I.boundary V
      rw [I.boundary_open]
      exact hyBoundary

/-- A convenience form of `boundary_topologicalPushoutChartedSpace` when manifoldness of the
generated atlas is already available. -/
theorem boundary_topologicalPushoutChartedSpace_of_isManifold
    [IsManifold I n X] [IsManifold I n Y] [IsManifold I n N]
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    (hcover : ∀ a, ∃ q, seam q = topologicalPushoutInl f g (f a))
    (hpushout :
      letI := topologicalPushoutChartedSpace (H := H)
        f g hf hg seam hseam hcover
      IsManifold I n (TopologicalPushout f g))
    (hn : n ≠ 0)
    (hNboundary : I.boundary N = ∅) :
    letI := topologicalPushoutChartedSpace (H := H)
      f g hf hg seam hseam hcover
    I.boundary (TopologicalPushout f g) =
      topologicalPushoutInl f g '' (I.boundary X \ range f) ∪
        topologicalPushoutInr f g '' (I.boundary Y \ range g) := by
  apply boundary_topologicalPushoutChartedSpace I n f g hf hg
    seam hseam hcover
  · let _ := topologicalPushoutChartedSpace (H := H)
      f g hf hg seam hseam hcover
    let hM : IsManifold I n (TopologicalPushout f g) := hpushout
    intro i j
    exact hM.compatible ⟨i, rfl⟩ ⟨j, rfl⟩
  · exact hn
  · exact hNboundary

/-- Boundary formula for the generated atlas when its seam is the literal signed seam map and
the two branch maps are local diffeomorphisms on their canonical overlap sources. -/
theorem boundary_topologicalPushoutChartedSpace_of_signed_localDiffeomorphOn
    [IsManifold I n X] [IsManifold I n Y] [IsManifold I n N]
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (tau : N → ℝ) (left : N → X) (right : N → Y)
    (hseam : IsOpenEmbedding
      (topologicalPushoutSeamMap f g tau left right))
    (hcover : ∀ a, ∃ q,
      topologicalPushoutSeamMap f g tau left right q =
        topologicalPushoutInl f g (f a))
    [Nonempty N]
    [Nonempty ↑(topologicalPushoutInlOffSeamOpens f hf)]
    [Nonempty ↑(topologicalPushoutInrOffSeamOpens g hg)]
    (hzero : ∀ p, tau p = 0 →
      ∃ a, f a = left p ∧ g a = right p)
    (hleftBoundary : ∀ p, left p ∈ range f → tau p = 0)
    (hrightBoundary : ∀ p, right p ∈ range g → tau p = 0)
    (hleftLocal : IsLocalDiffeomorphOn I I n left
      (topologicalPushoutSeamInlOffSeamOverlap f g hf hg
        (topologicalPushoutSeamMap f g tau left right) hseam).source)
    (hrightLocal : IsLocalDiffeomorphOn I I n right
      (topologicalPushoutSeamInrOffSeamOverlap f g hf hg
        (topologicalPushoutSeamMap f g tau left right) hseam).source)
    (hn : n ≠ 0)
    (hNboundary : I.boundary N = ∅) :
    letI := topologicalPushoutChartedSpace (H := H) f g hf hg
      (topologicalPushoutSeamMap f g tau left right) hseam hcover
    I.boundary (TopologicalPushout f g) =
      topologicalPushoutInl f g '' (I.boundary X \ range f) ∪
        topologicalPushoutInr f g '' (I.boundary Y \ range g) := by
  apply boundary_topologicalPushoutChartedSpace I n f g hf hg
    (topologicalPushoutSeamMap f g tau left right) hseam hcover
  · exact topologicalPushoutSeamMap_atlasChart_compatible_of_localDiffeomorphOn
      f g I n hf hg tau left right hseam hzero
        hleftBoundary hrightBoundary hleftLocal hrightLocal
  · exact hn
  · exact hNboundary

end SplittingSpheres
