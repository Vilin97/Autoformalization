module

public import SplittingSpheres.Geometry.CoordinateUnlinkExteriorCommonModelFourBall
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The four-sphere in the common coordinate-exterior model

This file gives the standard four-sphere a direct smooth atlas in the common coordinate-unlink
exterior model. Each natural sphere chart is translated to the distinguished interior point and
then recharted through the common model's interior partial homeomorphism. The topology is
unchanged, and literal identity diffeomorphisms compare the direct atlas with the standard sphere
atlas.

The singleton common-model atlas on ambient Euclidean four-space is also compared explicitly
with its standard atlas. No cut side, cap, gluing, or handlebody statement is asserted here.
-/

@[expose] public section

open Function Metric Set Topology TopologicalSpace IsManifold
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

private theorem coordinateUnlinkExteriorCommonModelInteriorBallRadius_pos :
    0 < coordinateUnlinkExteriorModelInteriorBallRadius :=
  (Classical.choose_spec exists_coordinateUnlinkExteriorModelInteriorBall).1

private theorem coordinateUnlinkExteriorCommonModelInteriorBall_subset :
    ball coordinateUnlinkExteriorModelInteriorBasePoint
        coordinateUnlinkExteriorModelInteriorBallRadius ⊆
      interior (range coordinateUnlinkExteriorModel) :=
  (Classical.choose_spec exists_coordinateUnlinkExteriorModelInteriorBall).2

private theorem contMDiff_coordinateUnlinkExteriorEuclideanAmbientChart_standard :
    ContMDiff (𝓡 4) coordinateUnlinkExteriorModel ∞
      coordinateUnlinkExteriorEuclideanAmbientChart := by
  have hball : ContMDiff (𝓡 4) (𝓡 4) ∞
      (OpenPartialHomeomorph.univBall
        coordinateUnlinkExteriorModelInteriorBasePoint
        coordinateUnlinkExteriorModelInteriorBallRadius) :=
    OpenPartialHomeomorph.contDiff_univBall.contMDiff
  have hsymm := coordinateUnlinkExteriorModel.contMDiffOn_symm.comp_contMDiff
    hball (fun x ↦ ?_)
  · exact hsymm.congr fun _ ↦ rfl
  · apply interior_subset
    apply coordinateUnlinkExteriorCommonModelInteriorBall_subset
    rw [← OpenPartialHomeomorph.univBall_target
      coordinateUnlinkExteriorModelInteriorBasePoint
      coordinateUnlinkExteriorCommonModelInteriorBallRadius_pos]
    exact (OpenPartialHomeomorph.univBall
      coordinateUnlinkExteriorModelInteriorBasePoint
      coordinateUnlinkExteriorModelInteriorBallRadius).map_source (by simp)

private theorem coordinateUnlinkExteriorEuclideanAmbientChart_coordinate
    (x : EuclideanSpace ℝ (Fin 4)) :
    coordinateUnlinkExteriorModel
        (coordinateUnlinkExteriorEuclideanAmbientChart x) =
      OpenPartialHomeomorph.univBall
        coordinateUnlinkExteriorModelInteriorBasePoint
        coordinateUnlinkExteriorModelInteriorBallRadius x := by
  change coordinateUnlinkExteriorModel
      (coordinateUnlinkExteriorModel.symm
        (OpenPartialHomeomorph.univBall
          coordinateUnlinkExteriorModelInteriorBasePoint
          coordinateUnlinkExteriorModelInteriorBallRadius x)) = _
  apply coordinateUnlinkExteriorModel.right_inv
  apply interior_subset
  apply coordinateUnlinkExteriorCommonModelInteriorBall_subset
  rw [← OpenPartialHomeomorph.univBall_target
    coordinateUnlinkExteriorModelInteriorBasePoint
    coordinateUnlinkExteriorCommonModelInteriorBallRadius_pos]
  exact (OpenPartialHomeomorph.univBall
    coordinateUnlinkExteriorModelInteriorBasePoint
    coordinateUnlinkExteriorModelInteriorBallRadius).map_source (by simp)

/-- The Euclidean identity is smooth from the standard atlas to the singleton common atlas. -/
theorem contMDiff_standardToCoordinateUnlinkExteriorCommonModelEuclideanIdentity :
    letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
    ContMDiff (𝓡 4) coordinateUnlinkExteriorModel ∞
      (id : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)) := by
  let _ := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
  apply ContMDiff.of_comp_isOpenEmbedding
    isOpenEmbedding_coordinateUnlinkExteriorEuclideanAmbientChart
  exact contMDiff_coordinateUnlinkExteriorEuclideanAmbientChart_standard.congr
    fun _ ↦ rfl

/-- The Euclidean identity is smooth from the singleton common atlas to the standard atlas. -/
theorem contMDiff_coordinateUnlinkExteriorCommonModelToStandardEuclideanIdentity :
    letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
    ContMDiff coordinateUnlinkExteriorModel (𝓡 4) ∞
      (id : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)) := by
  let _ := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
  have hchart : ContMDiff coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      coordinateUnlinkExteriorEuclideanAmbientChart :=
    contMDiff_isOpenEmbedding
      isOpenEmbedding_coordinateUnlinkExteriorEuclideanAmbientChart
  have hcoordinate : ContMDiff coordinateUnlinkExteriorModel (𝓡 4) ∞
      (coordinateUnlinkExteriorModel ∘
        coordinateUnlinkExteriorEuclideanAmbientChart) :=
    coordinateUnlinkExteriorModel.contMDiff.comp hchart
  have hinverse : ContMDiffOn (𝓡 4) (𝓡 4) ∞
      (OpenPartialHomeomorph.univBall
        coordinateUnlinkExteriorModelInteriorBasePoint
        coordinateUnlinkExteriorModelInteriorBallRadius).symm
      (ball coordinateUnlinkExteriorModelInteriorBasePoint
        coordinateUnlinkExteriorModelInteriorBallRadius) :=
    OpenPartialHomeomorph.contDiffOn_univBall_symm.contMDiffOn
  have hcomp := hinverse.comp_contMDiff hcoordinate (fun x ↦ ?_)
  · exact hcomp.congr fun x ↦ by
      simp only [id_eq, comp_apply]
      rw [coordinateUnlinkExteriorEuclideanAmbientChart_coordinate]
      exact ((OpenPartialHomeomorph.univBall
        coordinateUnlinkExteriorModelInteriorBasePoint
        coordinateUnlinkExteriorModelInteriorBallRadius).left_inv (by simp)).symm
  · simp only [comp_apply]
    rw [coordinateUnlinkExteriorEuclideanAmbientChart_coordinate]
    rw [← OpenPartialHomeomorph.univBall_target
      coordinateUnlinkExteriorModelInteriorBasePoint
      coordinateUnlinkExteriorCommonModelInteriorBallRadius_pos]
    exact (OpenPartialHomeomorph.univBall
      coordinateUnlinkExteriorModelInteriorBasePoint
      coordinateUnlinkExteriorModelInteriorBallRadius).map_source (by simp)

/-- The literal identity from standard Euclidean four-space to its singleton common-model atlas. -/
def standardToCoordinateUnlinkExteriorCommonModelEuclideanIdentityDiffeomorph :
    letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
    EuclideanSpace ℝ (Fin 4) ≃ₘ^∞⟮𝓡 4,
      coordinateUnlinkExteriorModel⟯ EuclideanSpace ℝ (Fin 4) := by
  let _ := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
  exact
    { toEquiv := Equiv.refl _
      contMDiff_toFun :=
        contMDiff_standardToCoordinateUnlinkExteriorCommonModelEuclideanIdentity
      contMDiff_invFun :=
        contMDiff_coordinateUnlinkExteriorCommonModelToStandardEuclideanIdentity }

/-- The reverse literal identity from the singleton common-model Euclidean atlas. -/
def coordinateUnlinkExteriorCommonModelToStandardEuclideanIdentityDiffeomorph :
    letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
    EuclideanSpace ℝ (Fin 4) ≃ₘ^∞⟮coordinateUnlinkExteriorModel,
      𝓡 4⟯ EuclideanSpace ℝ (Fin 4) := by
  let _ := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
  exact standardToCoordinateUnlinkExteriorCommonModelEuclideanIdentityDiffeomorph.symm


/-! ## A direct common-model rechart of the ambient four-sphere -/

/-- Rechart a natural four-sphere chart by a translation into the interior of the common
half-space model. -/
def coordinateUnlinkExteriorCommonModelSphereChart (x : Sphere 4) :
    OpenPartialHomeomorph (Sphere 4) CoordinateUnlinkExteriorModelSpace :=
  let cx := chartAt (EuclideanSpace ℝ (Fin 4)) x
  let sx := coordinateUnlinkExteriorModelInteriorBasePoint - cx x
  ((cx.trans (Homeomorph.addRight sx).toOpenPartialHomeomorph).trans
    coordinateUnlinkExteriorModelInteriorOpenPartialHomeomorph)

/-- The centre of every directly recharted sphere chart lies in its source. -/
@[simp]
theorem mem_coordinateUnlinkExteriorCommonModelSphereChart_source (x : Sphere 4) :
    x ∈ (coordinateUnlinkExteriorCommonModelSphereChart x).source := by
  simp only [coordinateUnlinkExteriorCommonModelSphereChart,
    OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ,
    mem_inter_iff, mem_preimage]
  refine ⟨ChartedSpace.mem_chart_source x, ?_⟩
  change chartAt (EuclideanSpace ℝ (Fin 4)) x x +
      (coordinateUnlinkExteriorModelInteriorBasePoint -
        chartAt (EuclideanSpace ℝ (Fin 4)) x x) ∈
    interior (range coordinateUnlinkExteriorModel)
  convert coordinateUnlinkExteriorModelInteriorBasePoint_mem using 1
  all_goals abel

/-- The natural sphere atlas, directly recharted into the common half-space-model carrier. -/
@[instance_reducible]
noncomputable def coordinateUnlinkExteriorCommonModelSphereChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace (Sphere 4) where
  atlas := range coordinateUnlinkExteriorCommonModelSphereChart
  chartAt := coordinateUnlinkExteriorCommonModelSphereChart
  mem_chart_source := mem_coordinateUnlinkExteriorCommonModelSphereChart_source
  chart_mem_atlas x := ⟨x, rfl⟩

private theorem coordinateUnlinkExteriorCommonModelSphereTransition_forward
    (x y : Sphere 4) :
    ContDiffOn ℝ ∞
      (coordinateUnlinkExteriorModel ∘
        (coordinateUnlinkExteriorCommonModelSphereChart x).symm.trans
          (coordinateUnlinkExteriorCommonModelSphereChart y) ∘
        coordinateUnlinkExteriorModel.symm)
      (coordinateUnlinkExteriorModel.symm ⁻¹'
          ((coordinateUnlinkExteriorCommonModelSphereChart x).symm.trans
            (coordinateUnlinkExteriorCommonModelSphereChart y)).source ∩
        range coordinateUnlinkExteriorModel) := by
  let cx := chartAt (EuclideanSpace ℝ (Fin 4)) x
  let cy := chartAt (EuclideanSpace ℝ (Fin 4)) y
  have hbase := (contDiffGroupoid ∞
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))).compatible
      (chart_mem_atlas (EuclideanSpace ℝ (Fin 4)) x)
      (chart_mem_atlas (EuclideanSpace ℝ (Fin 4)) y)
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hbase
  have hg : ContDiffOn ℝ ∞ ((cy : Sphere 4 →
        EuclideanSpace ℝ (Fin 4)) ∘ cx.symm)
      (cx.symm.trans cy).source := by
    simpa only [contDiffPregroupoid, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, id_comp, comp_id,
      OpenPartialHomeomorph.coe_trans, cx, cy, preimage_id, range_id,
      inter_univ] using hbase.1
  let sx := coordinateUnlinkExteriorModelInteriorBasePoint - cx x
  let sy := coordinateUnlinkExteriorModelInteriorBasePoint - cy y
  let tx := (Homeomorph.addRight sx).toOpenPartialHomeomorph
  let ty := (Homeomorph.addRight sy).toOpenPartialHomeomorph
  let D := coordinateUnlinkExteriorModelInteriorOpenPartialHomeomorph
  let bx := cx.trans tx
  let bY := cy.trans ty
  have hsubset :
      coordinateUnlinkExteriorModel.symm ⁻¹'
          ((coordinateUnlinkExteriorCommonModelSphereChart x).symm.trans
            (coordinateUnlinkExteriorCommonModelSphereChart y)).source ∩
          range coordinateUnlinkExteriorModel ⊆
        (fun z ↦ z - sx) ⁻¹' (cx.symm.trans cy).source := by
    intro z hz
    rcases hz.2 with ⟨w, rfl⟩
    have hz' : w ∈ ((bx.trans D).symm.trans (bY.trans D)).source := by
      have hz0 := hz.1
      change coordinateUnlinkExteriorModel.symm
          (coordinateUnlinkExteriorModel w) ∈
        ((coordinateUnlinkExteriorCommonModelSphereChart x).symm.trans
          (coordinateUnlinkExteriorCommonModelSphereChart y)).source at hz0
      rw [coordinateUnlinkExteriorModel.left_inv] at hz0
      change w ∈ ((bx.trans D).symm.trans (bY.trans D)).source at hz0
      exact hz0
    rw [OpenPartialHomeomorph.trans_source] at hz'
    have hwtarget := hz'.1
    rw [OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.trans_target] at hwtarget
    have hbx := hwtarget.2
    rw [OpenPartialHomeomorph.trans_target] at hbx
    have hcxTarget := hbx.2
    have hpby := hz'.2
    rw [OpenPartialHomeomorph.trans_source] at hpby
    have hpcy := hpby.1
    rw [OpenPartialHomeomorph.trans_source] at hpcy
    have hcySource := hpcy.1
    have htx : tx.symm (coordinateUnlinkExteriorModel w) =
        coordinateUnlinkExteriorModel w - sx := by
      rw [eq_sub_iff_add_eq]
      exact (Homeomorph.addRight sx).apply_symm_apply
        (coordinateUnlinkExteriorModel w)
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · change tx.symm (coordinateUnlinkExteriorModel w) ∈ cx.target at hcxTarget
      rwa [htx] at hcxTarget
    · change cx.symm (tx.symm (coordinateUnlinkExteriorModel w)) ∈
        cy.source at hcySource
      rwa [htx] at hcySource
  have hshift : ContDiff ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin 4) ↦ z - sx) :=
    contDiff_id.sub contDiff_const
  have hcomp : ContDiffOn ℝ ∞
      (fun z ↦ cy (cx.symm (z - sx)))
      ((fun z ↦ z - sx) ⁻¹' (cx.symm.trans cy).source) := by
    refine (hg.comp hshift.contDiffOn (mapsTo_preimage _ _)).congr ?_
    intro z _
    rfl
  have hfull : ContDiffOn ℝ ∞
      (fun z ↦ cy (cx.symm (z - sx)) + sy)
      ((fun z ↦ z - sx) ⁻¹' (cx.symm.trans cy).source) :=
    hcomp.add contDiff_const.contDiffOn
  refine (hfull.mono hsubset).congr ?_
  intro z hz
  rcases hz.2 with ⟨w, rfl⟩
  have hz0 := hz.1
  change coordinateUnlinkExteriorModel.symm
      (coordinateUnlinkExteriorModel w) ∈
    ((coordinateUnlinkExteriorCommonModelSphereChart x).symm.trans
      (coordinateUnlinkExteriorCommonModelSphereChart y)).source at hz0
  rw [coordinateUnlinkExteriorModel.left_inv] at hz0
  have hz' : w ∈ ((bx.trans D).symm.trans (bY.trans D)).source := by
    change w ∈
      ((coordinateUnlinkExteriorCommonModelSphereChart x).symm.trans
        (coordinateUnlinkExteriorCommonModelSphereChart y)).source
    exact hz0
  rw [OpenPartialHomeomorph.trans_source] at hz'
  have hwtarget := hz'.1
  rw [OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.trans_target] at hwtarget
  have hbx := hwtarget.2
  rw [OpenPartialHomeomorph.trans_target] at hbx
  have hcxTarget := hbx.1
  have hpby := hz'.2
  rw [OpenPartialHomeomorph.trans_source] at hpby
  have hDsource := hpby.2
  have htx : tx.symm (coordinateUnlinkExteriorModel w) =
      coordinateUnlinkExteriorModel w - sx := by
    rw [eq_sub_iff_add_eq]
    exact (Homeomorph.addRight sx).apply_symm_apply
      (coordinateUnlinkExteriorModel w)
  have hvecRange :
      ty (cy ((bx.trans D).symm w)) ∈
        range coordinateUnlinkExteriorModel := by
    apply interior_subset
    change (bY ((bx.trans D).symm w)) ∈ D.source at hDsource
    exact hDsource
  simp only [comp_apply, OpenPartialHomeomorph.trans_apply]
  rw [coordinateUnlinkExteriorModel.left_inv]
  change coordinateUnlinkExteriorModel
      (D (ty (cy ((bx.trans D).symm w)))) =
    cy (cx.symm (coordinateUnlinkExteriorModel w - sx)) + sy
  change coordinateUnlinkExteriorModel
      (coordinateUnlinkExteriorModel.symm
        (ty (cy ((bx.trans D).symm w)))) = _
  rw [coordinateUnlinkExteriorModel.right_inv hvecRange]
  change ty (cy (cx.symm (tx.symm
    (coordinateUnlinkExteriorModel w)))) = _
  rw [htx]
  rfl

private theorem coordinateUnlinkExteriorCommonModelSphereTransition
    (x y : Sphere 4) :
    (coordinateUnlinkExteriorCommonModelSphereChart x).symm.trans
        (coordinateUnlinkExteriorCommonModelSphereChart y) ∈
      contDiffGroupoid ∞ coordinateUnlinkExteriorModel := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · exact coordinateUnlinkExteriorCommonModelSphereTransition_forward x y
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
    exact coordinateUnlinkExteriorCommonModelSphereTransition_forward y x

/-- The direct common-model rechart makes the four-sphere a boundaryless smooth manifold. -/
theorem isManifold_coordinateUnlinkExteriorCommonModelSphere :
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  refine { compatible := ?_ }
  rintro e e' ⟨x, rfl⟩ ⟨y, rfl⟩
  exact coordinateUnlinkExteriorCommonModelSphereTransition x y

private theorem coordinateUnlinkExteriorCommonModelSphereChart_model_apply
    (x q : Sphere 4)
    (hq : q ∈ (coordinateUnlinkExteriorCommonModelSphereChart x).source) :
    coordinateUnlinkExteriorModel
        (coordinateUnlinkExteriorCommonModelSphereChart x q) =
      chartAt (EuclideanSpace ℝ (Fin 4)) x q +
        (coordinateUnlinkExteriorModelInteriorBasePoint -
          chartAt (EuclideanSpace ℝ (Fin 4)) x x) := by
  let c := chartAt (EuclideanSpace ℝ (Fin 4)) x
  let s := coordinateUnlinkExteriorModelInteriorBasePoint - c x
  let t := (Homeomorph.addRight s).toOpenPartialHomeomorph
  let D := coordinateUnlinkExteriorModelInteriorOpenPartialHomeomorph
  let b := c.trans t
  change coordinateUnlinkExteriorModel ((b.trans D) q) = c q + s
  change q ∈ (b.trans D).source at hq
  rw [OpenPartialHomeomorph.trans_source] at hq
  have hDsource : b q ∈ D.source := hq.2
  have hvec : t (c q) ∈ range coordinateUnlinkExteriorModel := by
    apply interior_subset
    change t (c q) ∈ D.source
    exact hDsource
  simp only [OpenPartialHomeomorph.trans_apply]
  change coordinateUnlinkExteriorModel
      (coordinateUnlinkExteriorModel.symm (t (c q))) = c q + s
  rw [coordinateUnlinkExteriorModel.right_inv hvec]
  rfl

/-- The sphere identity is smooth from the direct common atlas to the standard atlas. -/
theorem contMDiff_coordinateUnlinkExteriorCommonModelToStandardSphereIdentity :
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    ContMDiff coordinateUnlinkExteriorModel (modelWithCornersSelf ℝ
      (EuclideanSpace ℝ (Fin 4))) ∞ (id : Sphere 4 → Sphere 4) := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  intro x
  let e := coordinateUnlinkExteriorCommonModelSphereChart x
  let c := chartAt (EuclideanSpace ℝ (Fin 4)) x
  let s := coordinateUnlinkExteriorModelInteriorBasePoint - c x
  have he : e ∈ IsManifold.maximalAtlas coordinateUnlinkExteriorModel ∞
      (Sphere 4) :=
    (contDiffGroupoid ∞ coordinateUnlinkExteriorModel).subset_maximalAtlas
      ⟨x, rfl⟩
  have hc : c ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (Sphere 4) :=
    (contDiffGroupoid ∞
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
        |>.subset_maximalAtlas (chart_mem_atlas _ _)
  have hex : x ∈ e.source := mem_coordinateUnlinkExteriorCommonModelSphereChart_source x
  have hcx : x ∈ c.source := ChartedSpace.mem_chart_source x
  apply (contMDiffAt_iff_of_mem_maximalAtlas he hc hex hcx).2
  constructor
  · exact continuous_id.continuousAt
  · have hsmooth : ContDiffWithinAt ℝ ∞ (fun z ↦ z - s)
        (range coordinateUnlinkExteriorModel)
        (e.extend coordinateUnlinkExteriorModel x) :=
      (contDiff_id.sub contDiff_const).contDiffWithinAt
    have hwritten (z : EuclideanSpace ℝ (Fin 4))
        (hz : z ∈ (e.extend coordinateUnlinkExteriorModel).target) :
        (c.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∘
          id ∘ (e.extend coordinateUnlinkExteriorModel).symm) z = z - s := by
      let q := (e.extend coordinateUnlinkExteriorModel).symm z
      have hqsource : q ∈ e.source := by
        rw [← OpenPartialHomeomorph.extend_source
          (I := coordinateUnlinkExteriorModel) e]
        exact (e.extend coordinateUnlinkExteriorModel).map_target hz
      have hqcoord := coordinateUnlinkExteriorCommonModelSphereChart_model_apply x q hqsource
      have hright := (e.extend coordinateUnlinkExteriorModel).right_inv hz
      change c q = z - s
      rw [← hright]
      change c q = coordinateUnlinkExteriorModel (e q) - s
      rw [hqcoord]
      dsimp only [s, c]
      abel
    apply hsmooth.congr_of_eventuallyEq
    · filter_upwards [
        (e.extend_target_eventuallyEq (I := coordinateUnlinkExteriorModel) hex).filter_mono
          inf_le_left,
        self_mem_nhdsWithin] with z hzEq hzRange
      exact hwritten z (hzEq.mpr hzRange)
    · exact hwritten _ ((e.extend coordinateUnlinkExteriorModel).map_source (by
        rwa [OpenPartialHomeomorph.extend_source
          (I := coordinateUnlinkExteriorModel)]))

/-- The sphere identity is smooth from the standard atlas to the direct common atlas. -/
theorem contMDiff_standardToCoordinateUnlinkExteriorCommonModelSphereIdentity :
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      coordinateUnlinkExteriorModel ∞ (id : Sphere 4 → Sphere 4) := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  intro x
  let c := chartAt (EuclideanSpace ℝ (Fin 4)) x
  let e := coordinateUnlinkExteriorCommonModelSphereChart x
  let s := coordinateUnlinkExteriorModelInteriorBasePoint - c x
  have hc : c ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (Sphere 4) :=
    (contDiffGroupoid ∞
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
        |>.subset_maximalAtlas (chart_mem_atlas _ _)
  have he : e ∈ IsManifold.maximalAtlas coordinateUnlinkExteriorModel ∞
      (Sphere 4) :=
    (contDiffGroupoid ∞ coordinateUnlinkExteriorModel).subset_maximalAtlas
      ⟨x, rfl⟩
  have hcx : x ∈ c.source := ChartedSpace.mem_chart_source x
  have hex : x ∈ e.source := mem_coordinateUnlinkExteriorCommonModelSphereChart_source x
  apply (contMDiffAt_iff_of_mem_maximalAtlas hc he hcx hex).2
  constructor
  · exact continuous_id.continuousAt
  · have hsmooth : ContDiffWithinAt ℝ ∞ (fun z ↦ z + s)
        (range (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
        (c.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) x) :=
      (contDiff_id.add contDiff_const).contDiffWithinAt
    have hwritten (z : EuclideanSpace ℝ (Fin 4))
        (hzc : z ∈
          (c.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))).target)
        (hze : (id ((c.extend
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))).symm z)) ∈
          e.source) :
        (e.extend coordinateUnlinkExteriorModel ∘ id ∘
          (c.extend (modelWithCornersSelf ℝ
            (EuclideanSpace ℝ (Fin 4)))).symm) z = z + s := by
      let y := (c.extend
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))).symm z
      have hycoord := coordinateUnlinkExteriorCommonModelSphereChart_model_apply x y hze
      have hright := (c.extend
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))).right_inv hzc
      change coordinateUnlinkExteriorModel (e y) = z + s
      rw [hycoord]
      change c y + s = z + s
      have hcy : c y = z := by
        simpa only [OpenPartialHomeomorph.extend_coe,
          modelWithCornersSelf_coe, id_comp] using hright
      rw [hcy]
    have hcenter :
        id ((c.extend (modelWithCornersSelf ℝ
            (EuclideanSpace ℝ (Fin 4)))).symm
          (c.extend (modelWithCornersSelf ℝ
            (EuclideanSpace ℝ (Fin 4))) x)) = x := by
      rw [(c.extend (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin 4)))).left_inv (by
          rwa [OpenPartialHomeomorph.extend_source
            (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))])]
      rfl
    have hlocal :
        (id ∘ (c.extend (modelWithCornersSelf ℝ
          (EuclideanSpace ℝ (Fin 4)))).symm) ⁻¹' e.source ∈
          nhds (c.extend (modelWithCornersSelf ℝ
            (EuclideanSpace ℝ (Fin 4))) x) := by
      apply (continuous_id.continuousAt.comp
        (c.continuousAt_extend_symm (I := modelWithCornersSelf ℝ
          (EuclideanSpace ℝ (Fin 4))) hcx)).preimage_mem_nhds
      change e.source ∈ nhds (id ((c.extend (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin 4)))).symm
          (c.extend (modelWithCornersSelf ℝ
            (EuclideanSpace ℝ (Fin 4))) x)))
      rw [hcenter]
      exact e.open_source.mem_nhds hex
    apply hsmooth.congr_of_eventuallyEq
    · filter_upwards [
        (c.extend_target_eventuallyEq
          (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) hcx).filter_mono
            inf_le_left,
        mem_nhdsWithin_of_mem_nhds hlocal,
        self_mem_nhdsWithin] with z hzc hze hzRange
      exact hwritten z (hzc.mpr hzRange) hze
    · apply hwritten
      · exact (c.extend
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))).map_source
            (by rwa [OpenPartialHomeomorph.extend_source
              (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))])
      · rw [hcenter]
        exact hex

/-- The literal identity compares the direct common-model sphere atlas with its natural atlas. -/
def coordinateUnlinkExteriorCommonModelToStandardSphereIdentityDiffeomorph :
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    Sphere 4 ≃ₘ^∞⟮coordinateUnlinkExteriorModel,
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))⟯ Sphere 4 := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  exact
    { toEquiv := Equiv.refl _
      contMDiff_toFun := contMDiff_coordinateUnlinkExteriorCommonModelToStandardSphereIdentity
      contMDiff_invFun := contMDiff_standardToCoordinateUnlinkExteriorCommonModelSphereIdentity }

/-- The reverse literal identity from the standard sphere atlas to the direct common-model atlas. -/
def standardToCoordinateUnlinkExteriorCommonModelSphereIdentityDiffeomorph :
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    Sphere 4 ≃ₘ^∞⟮𝓡 4, coordinateUnlinkExteriorModel⟯ Sphere 4 := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  exact coordinateUnlinkExteriorCommonModelToStandardSphereIdentityDiffeomorph.symm

/-- The standard-to-common Euclidean identity is pointwise the identity. -/
@[simp]
theorem standardToCoordinateUnlinkExteriorCommonModelEuclideanIdentityDiffeomorph_apply
    (x : EuclideanSpace ℝ (Fin 4)) :
    letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
    standardToCoordinateUnlinkExteriorCommonModelEuclideanIdentityDiffeomorph x = x := by
  rfl

/-- The common-to-standard Euclidean identity is pointwise the identity. -/
@[simp]
theorem coordinateUnlinkExteriorCommonModelToStandardEuclideanIdentityDiffeomorph_apply
    (x : EuclideanSpace ℝ (Fin 4)) :
    letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
    coordinateUnlinkExteriorCommonModelToStandardEuclideanIdentityDiffeomorph x = x := by
  rfl

/-- The common-to-standard sphere identity is pointwise the identity. -/
@[simp]
theorem coordinateUnlinkExteriorCommonModelToStandardSphereIdentityDiffeomorph_apply
    (x : Sphere 4) :
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    coordinateUnlinkExteriorCommonModelToStandardSphereIdentityDiffeomorph x = x := by
  rfl

/-- The standard-to-common sphere identity is pointwise the identity. -/
@[simp]
theorem standardToCoordinateUnlinkExteriorCommonModelSphereIdentityDiffeomorph_apply
    (x : Sphere 4) :
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    standardToCoordinateUnlinkExteriorCommonModelSphereIdentityDiffeomorph x = x := by
  rfl

/-- The direct common-model atlas on the four-sphere has empty model boundary. -/
theorem coordinateUnlinkExteriorCommonModelSphere_boundary :
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    coordinateUnlinkExteriorModel.boundary (Sphere 4) = ∅ := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  have h :=
    coordinateUnlinkExteriorCommonModelToStandardSphereIdentityDiffeomorph.preimage_boundary
      (by simp)
  simpa only [ModelWithCorners.Boundaryless.boundary_eq_empty,
    preimage_empty] using h.symm

end SplittingSpheres
