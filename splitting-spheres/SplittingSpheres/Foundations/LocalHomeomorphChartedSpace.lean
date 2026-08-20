/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Pulling a charted-space atlas back through a local homeomorphism

A covering projection is a local homeomorphism.  This file records the first, purely charted-space
part of the standard construction which gives the covering space the smooth structure lifted from
its base.  Around `x`, the chosen chart is the local sheet map to the base followed by the chosen
base chart at `p x`.

The construction in this file does not yet assert compatibility of the lifted atlas with a smooth
structure groupoid; that is the separate manifold step.
-/

@[expose] public section

noncomputable section

open Set ChartedSpace IsManifold TopologicalSpace
open scoped ContDiff Manifold

namespace SplittingSpheres

universe uE uX uH

variable {E : Type uE} {X : Type uX} {H : Type uH}
variable [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace H]
variable [ChartedSpace H X]

namespace IsLocalHomeomorph

/-- The chart on the source of a local homeomorphism obtained from its chosen local sheet and the
preferred chart on the target. -/
def pullbackChart {p : E → X} (hp : IsLocalHomeomorph p) (x : E) :
    OpenPartialHomeomorph E H :=
  (hp.localInverseAt x).symm.trans (chartAt H (p x))

/-- The basepoint lies in the source of its lifted chart. -/
@[simp]
theorem mem_pullbackChart_source {p : E → X} (hp : IsLocalHomeomorph p) (x : E) :
    x ∈ (pullbackChart (H := H) hp x).source := by
  refine ⟨hp.self_mem_localInverseAt_target, ?_⟩
  rw [show (hp.localInverseAt x).symm.symm.symm =
    (hp.localInverseAt x).symm by simp]
  rw [hp.localInverseAt_symm]
  change p x ∈ (chartAt H (p x)).source
  exact mem_chart_source H (p x)

/-- The lifted chart is pointwise the target chart after the local-homeomorphism map on its
source. -/
theorem pullbackChart_apply {p : E → X} (hp : IsLocalHomeomorph p) (x : E)
    {y : E} (_hy : y ∈ (pullbackChart (H := H) hp x).source) :
    pullbackChart (H := H) hp x y = chartAt H (p x) (p y) := by
  change chartAt H (p x) ((hp.localInverseAt x).symm y) = _
  rw [hp.localInverseAt_symm]

/-- Pull the preferred target atlas back through a local homeomorphism. -/
@[instance_reducible]
def pullbackChartedSpace {p : E → X} (hp : IsLocalHomeomorph p) : ChartedSpace H E where
  atlas := range (pullbackChart (H := H) hp)
  chartAt := pullbackChart (H := H) hp
  mem_chart_source := mem_pullbackChart_source (H := H) hp
  chart_mem_atlas x := ⟨x, rfl⟩

/-- With the pulled-back atlas selected explicitly, the preferred chart is the displayed lifted
chart. -/
@[simp]
theorem pullbackChartedSpace_chartAt {p : E → X} (hp : IsLocalHomeomorph p) (x : E) :
    @chartAt H _ E _ (pullbackChartedSpace hp) x = pullbackChart (H := H) hp x :=
  rfl

/-- Every member of the pulled-back atlas is one of the displayed lifted charts. -/
theorem mem_pullbackChartedSpace_atlas_iff {p : E → X} (hp : IsLocalHomeomorph p)
    (e : OpenPartialHomeomorph E H) :
    e ∈ @atlas H _ E _ (pullbackChartedSpace hp) ↔
      ∃ x, e = pullbackChart (H := H) hp x := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

end IsLocalHomeomorph

section Manifold

universe uK

variable {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable (I : ModelWithCorners 𝕜 V H) (n : ℕ∞ω)

/-- The pulled-back atlas of a local homeomorphism is a manifold atlas whenever the target atlas
is one. -/
theorem IsLocalHomeomorph.isManifold_pullbackChartedSpace
    {p : E → X} (hp : IsLocalHomeomorph p) [IsManifold I n X] :
    letI := SplittingSpheres.IsLocalHomeomorph.pullbackChartedSpace (H := H) hp
    IsManifold I n E := by
  let _ := SplittingSpheres.IsLocalHomeomorph.pullbackChartedSpace (H := H) hp
  apply isManifold_of_contDiffOn I n E
  intro e e' he he'
  rw [SplittingSpheres.IsLocalHomeomorph.mem_pullbackChartedSpace_atlas_iff hp e] at he
  rw [SplittingSpheres.IsLocalHomeomorph.mem_pullbackChartedSpace_atlas_iff hp e'] at he'
  obtain ⟨x, rfl⟩ := he
  obtain ⟨y, rfl⟩ := he'
  have hbase := (contDiffGroupoid n I).compatible
    (chart_mem_atlas H (p x)) (chart_mem_atlas H (p y))
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hbase
  apply hbase.1.congr_mono
  · intro z hz
    simp [IsLocalHomeomorph.pullbackChart] at hz ⊢
    rw [hp.apply_localInverseAt_of_mem hz.1.1.2]
  · intro z hz
    simp [IsLocalHomeomorph.pullbackChart] at hz ⊢
    refine ⟨⟨hz.1.1.1, ?_⟩, hz.2⟩
    have h := hz.1.2.2
    rw [hp.apply_localInverseAt_of_mem hz.1.1.2] at h
    exact h

/-- Turn an atlas member into the corresponding partial diffeomorphism. -/
private def partialDiffeomorphOfMemMaximalAtlas
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
    (e : OpenPartialHomeomorph M H) (he : e ∈ maximalAtlas I n M) :
    PartialDiffeomorph I I M H n where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he

/-- With the pulled-back atlas and its induced manifold structure selected, a local homeomorphism
is a local diffeomorphism. -/
theorem IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
    {p : E → X} (hp : IsLocalHomeomorph p) [IsManifold I n X] :
    letI := SplittingSpheres.IsLocalHomeomorph.pullbackChartedSpace (H := H) hp
    letI : IsManifold I n E :=
      SplittingSpheres.IsLocalHomeomorph.isManifold_pullbackChartedSpace I n hp
    IsLocalDiffeomorph I I n p := by
  let _ := SplittingSpheres.IsLocalHomeomorph.pullbackChartedSpace (H := H) hp
  let _ : IsManifold I n E :=
    SplittingSpheres.IsLocalHomeomorph.isManifold_pullbackChartedSpace I n hp
  intro x
  let sourceChart : PartialDiffeomorph I I E H n :=
    partialDiffeomorphOfMemMaximalAtlas I n (chartAt H x) (chart_mem_maximalAtlas x)
  let targetChart : PartialDiffeomorph I I X H n :=
    partialDiffeomorphOfMemMaximalAtlas I n (chartAt H (p x))
      (chart_mem_maximalAtlas (p x))
  let Φ : PartialDiffeomorph I I E X n := sourceChart.trans targetChart.symm
  have hΦx : x ∈ Φ.source := by
    simp [Φ, sourceChart, targetChart, partialDiffeomorphOfMemMaximalAtlas,
      IsLocalHomeomorph.pullbackChart]
  have hΦ : EqOn p Φ Φ.source := by
    intro y hy
    simp [Φ, sourceChart, targetChart, partialDiffeomorphOfMemMaximalAtlas] at hy ⊢
    rw [IsLocalHomeomorph.pullbackChart_apply hp x hy.1]
    have htriple : (hp.localInverseAt x).symm.symm.symm y = p y := by
      simpa only [OpenPartialHomeomorph.symm_symm] using
        congrFun (hp.localInverseAt_symm x) y
    have hpy : p y ∈ (chartAt H (p x)).source := by
      rw [← htriple]
      exact hy.1.2
    exact ((chartAt H (p x)).left_inv hpy).symm
  let Ψ : PartialDiffeomorph I I E X n :=
    { toPartialEquiv :=
        { toFun := p
          invFun := Φ.toPartialEquiv.invFun
          source := Φ.source
          target := Φ.target
          map_source' := fun _ hx ↦ hΦ hx ▸ Φ.toPartialEquiv.map_source' hx
          map_target' := Φ.toPartialEquiv.map_target'
          left_inv' := fun _ hx ↦ hΦ hx ▸ Φ.toPartialEquiv.left_inv' hx
          right_inv' := fun _ hy ↦
            hΦ (Φ.toPartialEquiv.map_target' hy) ▸ Φ.toPartialEquiv.right_inv' hy }
      open_source := Φ.open_source
      open_target := Φ.open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.congr hΦ
      contMDiffOn_invFun := Φ.contMDiffOn_invFun }
  exact PartialDiffeomorph.isLocalDiffeomorphAt I I n Ψ hΦx

end Manifold

end SplittingSpheres
