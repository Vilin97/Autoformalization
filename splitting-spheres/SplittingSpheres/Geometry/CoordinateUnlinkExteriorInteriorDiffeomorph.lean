/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.CoordinateUnlinkExteriorSmoothAtlas
public import SplittingSpheres.Geometry.UnlinkComplementExteriorHomeomorph

/-!
# The intrinsic smooth interior of the coordinate unlink exterior

The strict part of the literal radius-`1 / 8` coordinate exterior is the complement of the two
closed radius-`1 / 8` tubes as a point set. This file proves that the evident equivalence is a
genuine diffeomorphism from the atlas constructed on the closed exterior to the inherited open
subtype atlas on the four-sphere.

The proof does not transport an atlas. It restricts each actual ambient exterior chart to the
strict interior, proves that restriction belongs to the inherited maximal atlas, and computes the
forward and inverse coordinate expressions as opposite translations by the chart shift.
-/

@[expose] public section

open Function Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

private theorem ambientChartOnInterior_mem_maximalAtlas
    (x : CoordinateUnlinkExteriorEighthInterior) :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    coordinateUnlinkExteriorEighthAmbientChartOnInterior x ∈
      IsManifold.maximalAtlas coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighthInterior := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let G := contDiffGroupoid ∞ coordinateUnlinkExteriorModel
  let e := coordinateUnlinkExteriorEighthAmbientChart x
  let e₀ := coordinateUnlinkExteriorEighthAmbientChartOnInterior x
  have he : e ∈ atlas CoordinateUnlinkExteriorModelSpace
      CoordinateUnlinkExteriorEighth := by
    exact Or.inl ⟨x, rfl⟩
  have hrestr :
      e.subtypeRestr (s := coordinateUnlinkExteriorEighthInteriorOpens) ⟨x⟩ ∈
        G.maximalAtlas CoordinateUnlinkExteriorEighthInterior :=
    G.subtypeRestr_mem_maximalAtlas he (s :=
      coordinateUnlinkExteriorEighthInteriorOpens) ⟨x⟩
  apply G.mem_maximalAtlas_of_eqOnSource (e :=
    e.subtypeRestr (s := coordinateUnlinkExteriorEighthInteriorOpens) ⟨x⟩) ?_ hrestr
  apply (e₀.eqOnSource_iff _).mpr
  constructor
  · ext q
    simp only [e, e₀, coordinateUnlinkExteriorEighthAmbientChart,
      OpenPartialHomeomorph.subtypeRestr_source,
      OpenPartialHomeomorph.lift_openEmbedding_source, mem_preimage, mem_image]
    constructor
    · intro hq
      exact ⟨q, hq, rfl⟩
    · rintro ⟨y, hy, hqy⟩
      have hyq : y = q := by
        apply Subtype.ext
        exact hqy
      simpa only [hyq] using hy
  · intro q hq
    change e₀ q = e q.1
    dsimp only [e, coordinateUnlinkExteriorEighthAmbientChart]
    exact (OpenPartialHomeomorph.lift_openEmbedding_apply _ _).symm

private theorem ambientChartOnInterior_model_apply
    (x q : CoordinateUnlinkExteriorEighthInterior)
    (hq : q ∈ (coordinateUnlinkExteriorEighthAmbientChartOnInterior x).source) :
    coordinateUnlinkExteriorModel
        (coordinateUnlinkExteriorEighthAmbientChartOnInterior x q) =
      chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1 q.1.1 +
        (coordinateUnlinkExteriorModelInteriorBasePoint -
          chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1 x.1.1) := by
  let c := chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1
  let s := coordinateUnlinkExteriorModelInteriorBasePoint - c x.1.1
  let _ : Nonempty CoordinateUnlinkExteriorEighthInterior := ⟨x⟩
  let j : OpenPartialHomeomorph CoordinateUnlinkExteriorEighthInterior
      (Sphere 4) :=
    isOpenEmbedding_coordinateUnlinkExteriorEighthInteriorToSphere
      |>.toOpenPartialHomeomorph
        coordinateUnlinkExteriorEighthInteriorToSphere
  let t := (Homeomorph.addRight s).toOpenPartialHomeomorph
  let D := coordinateUnlinkExteriorModelInteriorOpenPartialHomeomorph
  let b := (j.trans c).trans t
  change coordinateUnlinkExteriorModel ((b.trans D) q) = c (j q) + s
  change q ∈ (b.trans D).source at hq
  rw [OpenPartialHomeomorph.trans_source] at hq
  have hDsource : b q ∈ D.source := hq.2
  have hvec : t (c (j q)) ∈ range coordinateUnlinkExteriorModel := by
    apply interior_subset
    change t (c (j q)) ∈ D.source
    exact hDsource
  simp only [OpenPartialHomeomorph.trans_apply]
  change coordinateUnlinkExteriorModel
      (coordinateUnlinkExteriorModel.symm (t (c (j q)))) = c (j q) + s
  rw [coordinateUnlinkExteriorModel.right_inv hvec]
  rfl

private theorem mem_ambientChartOnInterior_source
    (x : CoordinateUnlinkExteriorEighthInterior) :
    x ∈ (coordinateUnlinkExteriorEighthAmbientChartOnInterior x).source := by
  have hx := mem_coordinateUnlinkExteriorEighthAmbientChart_source x
  rw [coordinateUnlinkExteriorEighthAmbientChart,
    OpenPartialHomeomorph.lift_openEmbedding_source] at hx
  rcases hx with ⟨y, hy, hyx⟩
  have hyx' : y = x := by
    apply Subtype.ext
    exact hyx
  simpa only [hyx'] using hy

private def interiorToClosedTubeExterior
    (q : CoordinateUnlinkExteriorEighthInterior) :
    StandardUnlinkClosedTubeExterior :=
  ⟨q.1.1, q.2⟩

private def closedTubeExteriorToInterior
    (q : StandardUnlinkClosedTubeExterior) :
    CoordinateUnlinkExteriorEighthInterior :=
  ⟨⟨q.1, standardUnlinkClosedTubeExterior_subset_coordinateUnlinkExterior q.2⟩, q.2⟩

private theorem continuous_closedTubeExteriorToInterior :
    Continuous closedTubeExteriorToInterior :=
  ((continuous_subtype_val : Continuous
    (Subtype.val : StandardUnlinkClosedTubeExterior → Sphere 4)).subtype_mk _).subtype_mk _

private theorem contMDiff_interiorToSphere :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    ContMDiff coordinateUnlinkExteriorModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      coordinateUnlinkExteriorEighthInteriorToSphere := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  intro x
  let e := coordinateUnlinkExteriorEighthAmbientChartOnInterior x
  let c := chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1
  let s := coordinateUnlinkExteriorModelInteriorBasePoint - c x.1.1
  have he : e ∈ IsManifold.maximalAtlas
      coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighthInterior :=
    ambientChartOnInterior_mem_maximalAtlas x
  have hc : c ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (Sphere 4) :=
    (contDiffGroupoid ∞
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
        |>.subset_maximalAtlas (chart_mem_atlas _ _)
  have hx : x ∈ e.source := mem_ambientChartOnInterior_source x
  have hcx : coordinateUnlinkExteriorEighthInteriorToSphere x ∈ c.source :=
    ChartedSpace.mem_chart_source x.1.1
  apply (contMDiffAt_iff_of_mem_maximalAtlas he hc hx hcx).2
  constructor
  · exact isOpenEmbedding_coordinateUnlinkExteriorEighthInteriorToSphere.continuous.continuousAt
  · have hsmooth : ContDiffWithinAt ℝ ∞ (fun z ↦ z - s)
        (range coordinateUnlinkExteriorModel) (e.extend coordinateUnlinkExteriorModel x) :=
      (contDiff_id.sub contDiff_const).contDiffWithinAt
    have hwritten (z : EuclideanSpace ℝ (Fin 4))
        (hz : z ∈ (e.extend coordinateUnlinkExteriorModel).target) :
        (c.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∘
          coordinateUnlinkExteriorEighthInteriorToSphere ∘
          (e.extend coordinateUnlinkExteriorModel).symm) z = z - s := by
      let q := (e.extend coordinateUnlinkExteriorModel).symm z
      have hqsource : q ∈ e.source := by
        rw [← OpenPartialHomeomorph.extend_source
          (I := coordinateUnlinkExteriorModel) e]
        exact (e.extend coordinateUnlinkExteriorModel).map_target hz
      have hqcoord := ambientChartOnInterior_model_apply x q hqsource
      have hright := (e.extend coordinateUnlinkExteriorModel).right_inv hz
      change c q.1.1 = z - s
      rw [← hright]
      change c q.1.1 = coordinateUnlinkExteriorModel (e q) - s
      rw [hqcoord]
      change c q.1.1 = c q.1.1 + s - s
      abel
    apply hsmooth.congr_of_eventuallyEq
    · filter_upwards [
        (e.extend_target_eventuallyEq (I := coordinateUnlinkExteriorModel) hx).filter_mono
          inf_le_left,
        self_mem_nhdsWithin] with z hzEq hzRange
      exact hwritten z (hzEq.mpr hzRange)
    · exact hwritten _ ((e.extend coordinateUnlinkExteriorModel).map_source (by
        rwa [OpenPartialHomeomorph.extend_source
          (I := coordinateUnlinkExteriorModel)]))

private theorem contMDiff_closedTubeExteriorToInterior :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      coordinateUnlinkExteriorModel ∞ closedTubeExteriorToInterior := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  intro q
  let x := closedTubeExteriorToInterior q
  let c := chartAt (EuclideanSpace ℝ (Fin 4)) q.1
  let d := c.subtypeRestr (s := standardUnlinkClosedTubeExteriorOpens) ⟨q⟩
  let e := coordinateUnlinkExteriorEighthAmbientChartOnInterior x
  let s := coordinateUnlinkExteriorModelInteriorBasePoint - c q.1
  have hd : d ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      StandardUnlinkClosedTubeExterior := by
    exact (contDiffGroupoid ∞
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
        |>.subtypeRestr_mem_maximalAtlas (chart_mem_atlas _ _)
          (s := standardUnlinkClosedTubeExteriorOpens) ⟨q⟩
  have he : e ∈ IsManifold.maximalAtlas coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighthInterior :=
    ambientChartOnInterior_mem_maximalAtlas x
  have hqsource : q ∈ d.source := by
    change q ∈
      (c.subtypeRestr (s := standardUnlinkClosedTubeExteriorOpens) ⟨q⟩).source
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact ChartedSpace.mem_chart_source
      (H := EuclideanSpace ℝ (Fin 4)) q.1
  have hxsource : x ∈ e.source := mem_ambientChartOnInterior_source x
  apply (contMDiffAt_iff_of_mem_maximalAtlas hd he hqsource hxsource).2
  constructor
  · exact continuous_closedTubeExteriorToInterior.continuousAt
  · have hsmooth : ContDiffWithinAt ℝ ∞ (fun z ↦ z + s)
        (range (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
        (d.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) q) :=
      (contDiff_id.add contDiff_const).contDiffWithinAt
    have hwritten (z : EuclideanSpace ℝ (Fin 4))
        (hzd : z ∈
          (d.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))).target)
        (hze : closedTubeExteriorToInterior
            ((d.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))).symm z) ∈
          e.source) :
        (e.extend coordinateUnlinkExteriorModel ∘
          closedTubeExteriorToInterior ∘
          (d.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))).symm) z =
            z + s := by
      let y :=
        (d.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))).symm z
      have hycoord := ambientChartOnInterior_model_apply x
        (closedTubeExteriorToInterior y) hze
      have hright :=
        (d.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))).right_inv hzd
      change coordinateUnlinkExteriorModel
        (e (closedTubeExteriorToInterior y)) = z + s
      rw [hycoord]
      change c y.1 + s = z + s
      rw [← hright]
      rfl
    have hcenter :
        closedTubeExteriorToInterior
            ((d.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))).symm
              (d.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) q)) = x := by
      rw [(d.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))).left_inv
        (by rwa [OpenPartialHomeomorph.extend_source
          (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))])]
    have hlocal :
        (closedTubeExteriorToInterior ∘
          (d.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))).symm) ⁻¹'
            e.source ∈
          𝓝 (d.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) q) := by
      apply (continuous_closedTubeExteriorToInterior.continuousAt.comp
        (d.continuousAt_extend_symm (I :=
          modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) hqsource)).preimage_mem_nhds
      change e.source ∈ 𝓝 (closedTubeExteriorToInterior
        ((d.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))).symm
          (d.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) q)))
      rw [hcenter]
      exact e.open_source.mem_nhds hxsource
    apply hsmooth.congr_of_eventuallyEq
    · filter_upwards [
        (d.extend_target_eventuallyEq
          (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) hqsource).filter_mono
            inf_le_left,
        mem_nhdsWithin_of_mem_nhds hlocal,
        self_mem_nhdsWithin] with z hzd hze hzRange
      exact hwritten z (hzd.mpr hzRange) hze
    · apply hwritten
      · exact (d.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))).map_source
          (by rwa [OpenPartialHomeomorph.extend_source
            (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))])
      · rw [hcenter]
        exact hxsource

/-- The strict coordinate exterior with its inherited exterior atlas is intrinsically
diffeomorphic to the open complement of the two closed radius-`1 / 8` tubes in `S⁴`. -/
def coordinateUnlinkExteriorEighthInteriorSphereDiffeomorph :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    CoordinateUnlinkExteriorEighthInterior
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, 𝓡 4⟯
        StandardUnlinkClosedTubeExterior := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  refine {
    toFun := fun q ↦ ⟨q.1.1, q.2⟩
    invFun := fun q ↦
      ⟨⟨q.1, standardUnlinkClosedTubeExterior_subset_coordinateUnlinkExterior q.2⟩, q.2⟩
    left_inv := by
      intro q
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv := by
      intro q
      apply Subtype.ext
      rfl
    contMDiff_toFun := by
      change ContMDiff coordinateUnlinkExteriorModel (𝓡 4) ∞
        interiorToClosedTubeExterior
      apply (ContMDiff.subtypeVal_comp_iff
        standardUnlinkClosedTubeExteriorOpens interiorToClosedTubeExterior).mp
      apply contMDiff_interiorToSphere.congr
      intro q
      rfl
    contMDiff_invFun := by
      change ContMDiff (𝓡 4) coordinateUnlinkExteriorModel ∞
        closedTubeExteriorToInterior
      exact contMDiff_closedTubeExteriorToInterior
  }

/-- The intrinsic interior diffeomorphism is literally ambient inclusion in the forward
direction. -/
@[simp]
theorem coordinateUnlinkExteriorEighthInteriorSphereDiffeomorph_apply_coe
    (q : CoordinateUnlinkExteriorEighthInterior) :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    (coordinateUnlinkExteriorEighthInteriorSphereDiffeomorph q : Sphere 4) = q.1.1 := by
  rfl

/-- The inverse intrinsic interior diffeomorphism preserves the underlying ambient sphere
point. -/
@[simp]
theorem coordinateUnlinkExteriorEighthInteriorSphereDiffeomorph_symm_apply_coe
    (q : StandardUnlinkClosedTubeExterior) :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    (coordinateUnlinkExteriorEighthInteriorSphereDiffeomorph.symm q).1.1 = q.1 := by
  rfl

end SplittingSpheres
