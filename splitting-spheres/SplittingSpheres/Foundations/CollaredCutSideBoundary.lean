/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.CollaredCutSideManifold
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Boundaries of collared cut sides

This file identifies the model boundary of the direct smooth atlas on a collared cut side.  The
native off-boundary charts and the half-collar charts are local diffeomorphisms into the cut side.
Consequently, when the half-collar pulls back the union of the old ambient boundary and the new
cutting seam to precisely the model boundary of its source, the boundary of the cut side is
exactly the preimage of that union.

The theorem is deliberately stated for the explicit direct cut-side atlas and its concrete
compatibility proof.  It does not transport an atlas or infer a collar boundary formula from
point-set topology alone.
-/

@[expose] public section

noncomputable section


open Function Set Topology TopologicalSpace IsManifold
open scoped ContDiff Manifold

universe u

namespace SplittingSpheres

variable {M P H E : Type*}
variable [TopologicalSpace M] [TopologicalSpace P] [TopologicalSpace H]
variable [Nonempty H] [NormedAddCommGroup E] [NormedSpace Real E]
variable [ChartedSpace H M] [ChartedSpace H P]
variable (I : ModelWithCorners Real E H) (n : ℕ∞ω)
variable [IsManifold I n M] [IsManifold I n P]

private def partialDiffeomorphOfAtlas
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I n X]
    (e : OpenPartialHomeomorph X H)
    (he : e ∈ IsManifold.maximalAtlas I n X) :
    PartialDiffeomorph I I X H n where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he

omit [IsManifold I n M] in
/-- The half-collar inclusion is a local diffeomorphism into the direct cut-side atlas. -/
theorem isLocalDiffeomorph_collaredCutSideHalfCollarMap
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    (hcover : ∀ z : CollaredCutSide C,
      z.1 ∈ collaredCutSideOffBoundary C B ∨ z.1 ∈ range c)
    (hcompat : ∀ i j : CollaredCutSideAtlasIndex C B P,
      (collaredCutSideAtlasChart (H := H)
        C B hopen c hc hcollar i).symm.trans
          (collaredCutSideAtlasChart (H := H)
            C B hopen c hc hcollar j) ∈
        contDiffGroupoid n I) :
    letI := collaredCutSideChartedSpace (H := H)
      C B hopen c hc hcollar hcover
    IsLocalDiffeomorph I I n
      (collaredCutSideHalfCollarMap C c hc) := by
  let _ := collaredCutSideChartedSpace (H := H)
    C B hopen c hc hcollar hcover
  let _ : IsManifold I n (CollaredCutSide C) :=
    isManifold_collaredCutSideChartedSpace I n
      C B hopen c hc hcollar hcover hcompat
  intro p
  let sourceChart : PartialDiffeomorph I I P H n :=
    partialDiffeomorphOfAtlas I n (chartAt H p)
      (chart_mem_maximalAtlas p)
  let targetOpenChart :=
    collaredCutSideCollarChart (H := H) C c hc hcollar p
  have htargetAtlas : targetOpenChart ∈ atlas H (CollaredCutSide C) := by
    exact ⟨CollaredCutSideAtlasIndex.collar p, rfl⟩
  have htargetMax : targetOpenChart ∈
      IsManifold.maximalAtlas I n (CollaredCutSide C) :=
    StructureGroupoid.subset_maximalAtlas (contDiffGroupoid n I) htargetAtlas
  let targetChart : PartialDiffeomorph I I (CollaredCutSide C) H n :=
    partialDiffeomorphOfAtlas I n targetOpenChart htargetMax
  let phi := sourceChart.trans targetChart.symm
  refine ⟨phi, ?_, ?_⟩
  · change p ∈ sourceChart.source ∩ sourceChart ⁻¹' targetChart.symm.source
    refine ⟨mem_chart_source H p, ?_⟩
    change (chartAt H p) p ∈ targetOpenChart.target
    simp [targetOpenChart, collaredCutSideCollarChart]
  · intro q hq
    change collaredCutSideHalfCollarMap C c hc q =
      targetChart.symm (sourceChart q)
    change collaredCutSideHalfCollarMap C c hc q =
      targetOpenChart.symm ((chartAt H p) q)
    rw [show targetOpenChart =
      (chartAt H p).lift_openEmbedding hcollar by rfl]
    simp only [OpenPartialHomeomorph.lift_openEmbedding_symm,
      comp_apply]
    rw [(chartAt H p).left_inv hq.1]

omit [IsManifold I n P] in
/-- The native off-boundary inclusion is a local diffeomorphism into the direct cut-side atlas. -/
theorem isLocalDiffeomorph_collaredCutSideOffBoundaryMap
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    (hcover : ∀ z : CollaredCutSide C,
      z.1 ∈ collaredCutSideOffBoundary C B ∨ z.1 ∈ range c)
    (hcompat : ∀ i j : CollaredCutSideAtlasIndex C B P,
      (collaredCutSideAtlasChart (H := H)
        C B hopen c hc hcollar i).symm.trans
          (collaredCutSideAtlasChart (H := H)
            C B hopen c hc hcollar j) ∈
        contDiffGroupoid n I) :
    letI := collaredCutSideChartedSpace (H := H)
      C B hopen c hc hcollar hcover
    IsLocalDiffeomorph I I n
      (collaredCutSideOffBoundaryOpensMap C B hopen) := by
  let _ := collaredCutSideChartedSpace (H := H)
    C B hopen c hc hcollar hcover
  let _ : IsManifold I n (CollaredCutSide C) :=
    isManifold_collaredCutSideChartedSpace I n
      C B hopen c hc hcollar hcover hcompat
  intro x
  let U := collaredCutSideOffBoundaryOpens C B hopen
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
    collaredCutSideNativeChart (H := H) C B hopen x
  have htargetAtlas : targetOpenChart ∈ atlas H (CollaredCutSide C) := by
    exact ⟨CollaredCutSideAtlasIndex.native x, rfl⟩
  have htargetMax : targetOpenChart ∈
      IsManifold.maximalAtlas I n (CollaredCutSide C) :=
    StructureGroupoid.subset_maximalAtlas (contDiffGroupoid n I) htargetAtlas
  let targetChart : PartialDiffeomorph I I (CollaredCutSide C) H n :=
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
    change collaredCutSideOffBoundaryOpensMap C B hopen y =
      targetChart.symm (sourceChart y)
    change collaredCutSideOffBoundaryOpensMap C B hopen y =
      targetOpenChart.symm (sourceOpenChart y)
    rw [show targetOpenChart = sourceOpenChart.lift_openEmbedding
      (isOpenEmbedding_collaredCutSideOffBoundaryOpensMap C B hopen) by rfl]
    simp only [OpenPartialHomeomorph.lift_openEmbedding_symm, comp_apply]
    rw [sourceOpenChart.left_inv hy.1]

/--
The model boundary of the direct cut-side atlas is the old ambient model boundary together with
the new cutting seam.  The exact pullback equality is the sole boundary compatibility required
of the half-collar.
-/
theorem boundary_collaredCutSideChartedSpace
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    (hcover : ∀ z : CollaredCutSide C,
      z.1 ∈ collaredCutSideOffBoundary C B ∨ z.1 ∈ range c)
    (hcompat : ∀ i j : CollaredCutSideAtlasIndex C B P,
      (collaredCutSideAtlasChart (H := H)
        C B hopen c hc hcollar i).symm.trans
          (collaredCutSideAtlasChart (H := H)
            C B hopen c hc hcollar j) ∈
        contDiffGroupoid n I)
    (hn : n ≠ 0)
    (hboundary : c ⁻¹' (I.boundary M ∪ B) = I.boundary P) :
    letI := collaredCutSideChartedSpace (H := H)
      C B hopen c hc hcollar hcover
    I.boundary (CollaredCutSide C) =
      (Subtype.val : CollaredCutSide C → M) ⁻¹'
        (I.boundary M ∪ B) := by
  let _ := collaredCutSideChartedSpace (H := H)
    C B hopen c hc hcollar hcover
  let _ : IsManifold I n (CollaredCutSide C) :=
    isManifold_collaredCutSideChartedSpace I n
      C B hopen c hc hcollar hcover hcompat
  have hcollarLocal : IsLocalDiffeomorph I I n
      (collaredCutSideHalfCollarMap C c hc) :=
    isLocalDiffeomorph_collaredCutSideHalfCollarMap I n
      C B hopen c hc hcollar hcover hcompat
  have hnativeLocal : IsLocalDiffeomorph I I n
      (collaredCutSideOffBoundaryOpensMap C B hopen) :=
    isLocalDiffeomorph_collaredCutSideOffBoundaryMap I n
      C B hopen c hc hcollar hcover hcompat
  ext z
  change I.IsBoundaryPoint z ↔ z.1 ∈ I.boundary M ∪ B
  rcases hcover z with hzNative | hzCollar
  · let U := collaredCutSideOffBoundaryOpens C B hopen
    let x : U := ⟨z.1, hzNative⟩
    have hxEq : collaredCutSideOffBoundaryOpensMap C B hopen x = z :=
      Subtype.ext rfl
    rw [← hxEq]
    have hiff := (hnativeLocal x).isBoundaryPoint_iff hn
    constructor
    · intro hzBoundary
      have hxBoundary : I.IsBoundaryPoint x := hiff.mpr hzBoundary
      have hxAmbient : x.1 ∈ I.boundary M := by
        change x ∈ I.boundary U at hxBoundary
        rwa [I.boundary_open] at hxBoundary
      exact Or.inl hxAmbient
    · intro hx
      rcases hx with hxAmbient | hxB
      · apply hiff.mp
        change x ∈ I.boundary U
        rw [I.boundary_open]
        exact hxAmbient
      · exact False.elim (x.2.2 hxB)
  · obtain ⟨p, hp⟩ := hzCollar
    have hpEq : collaredCutSideHalfCollarMap C c hc p = z :=
      Subtype.ext hp
    rw [← hpEq]
    have hiff := (hcollarLocal p).isBoundaryPoint_iff hn
    have hpBoundary : p ∈ I.boundary P ↔ c p ∈ I.boundary M ∪ B := by
      have hpSet := Set.ext_iff.mp hboundary p
      exact hpSet.symm
    exact hiff.symm.trans hpBoundary

/--
Application-facing boundary identification from local diffeomorphism on the exact native/collar
overlap.  This is the same direct atlas used by
`isManifold_collaredCutSideChartedSpace_of_localDiffeomorphOn`.
-/
theorem boundary_collaredCutSideChartedSpace_of_localDiffeomorphOn
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    (hcover : ∀ z : CollaredCutSide C,
      z.1 ∈ collaredCutSideOffBoundary C B ∨ z.1 ∈ range c)
    (hlocal : IsLocalDiffeomorphOn I I n c
      (c ⁻¹' collaredCutSideOffBoundary C B))
    (hn : n ≠ 0)
    (hboundary : c ⁻¹' (I.boundary M ∪ B) = I.boundary P) :
    letI := collaredCutSideChartedSpace (H := H)
      C B hopen c hc hcollar hcover
    I.boundary (CollaredCutSide C) =
      (Subtype.val : CollaredCutSide C → M) ⁻¹'
        (I.boundary M ∪ B) :=
  boundary_collaredCutSideChartedSpace I n
    C B hopen c hc hcollar hcover
      (collaredCutSideAtlasChart_compatible_of_localDiffeomorphOn I n
        C B hopen c hc hcollar hlocal)
      hn hboundary

end SplittingSpheres
