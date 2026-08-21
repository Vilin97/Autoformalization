/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.CoordinateUnlinkBoundaryCollarDiffeomorph
public import SplittingSpheres.Foundations.CollaredCutSideBoundary
import Mathlib.Analysis.InnerProductSpace.Calculus
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The Euclidean four-ball in the common coordinate-exterior model

This file gives the literal closed Euclidean four-ball a direct smooth atlas in the common
coordinate-unlink exterior model.  It first puts an explicit singleton atlas on ambient Euclidean
four-space by mapping it smoothly into a small open ball in the interior of the common model.
The four-ball is then the direct collared cut side of that ambient space, with native charts on
the open unit ball and the explicitly recharted radial collar along the unit sphere.

Thus the topology is the literal closed-ball subtype topology and the boundary charts are the
actual radial collar charts.  No smooth structure is transported through an unrelated ball
homeomorphism.  The resulting model boundary is proved to equal the boundary of the existing
convex-range four-ball model.  The construction is also pulled back componentwise to a discrete
`ZMod m` family.

No attaching, capping, pushout, or handlebody statement is asserted here.
-/

@[expose] public section

open Function Metric Set Topology TopologicalSpace IsManifold
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-- A small Euclidean ball around the distinguished common-model interior point lies wholly in
the common-model interior. -/
theorem exists_coordinateUnlinkExteriorModelInteriorBall :
    ∃ r > 0,
      ball coordinateUnlinkExteriorModelInteriorBasePoint r ⊆
        interior (range coordinateUnlinkExteriorModel) := by
  exact (Metric.isOpen_iff.mp isOpen_interior
    coordinateUnlinkExteriorModelInteriorBasePoint
    coordinateUnlinkExteriorModelInteriorBasePoint_mem)

/-- A fixed positive radius for an ambient singleton chart in the common exterior model. -/
def coordinateUnlinkExteriorModelInteriorBallRadius : ℝ :=
  Classical.choose exists_coordinateUnlinkExteriorModelInteriorBall

private theorem coordinateUnlinkExteriorModelInteriorBallRadius_pos :
    0 < coordinateUnlinkExteriorModelInteriorBallRadius :=
  (Classical.choose_spec exists_coordinateUnlinkExteriorModelInteriorBall).1

private theorem coordinateUnlinkExteriorModelInteriorBall_subset :
    ball coordinateUnlinkExteriorModelInteriorBasePoint
        coordinateUnlinkExteriorModelInteriorBallRadius ⊆
      interior (range coordinateUnlinkExteriorModel) :=
  (Classical.choose_spec exists_coordinateUnlinkExteriorModelInteriorBall).2

/-- The singleton ambient chart from Euclidean four-space into the common exterior model. -/
def coordinateUnlinkExteriorEuclideanAmbientChart :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 4))
      CoordinateUnlinkExteriorModelSpace :=
  (OpenPartialHomeomorph.univBall
      coordinateUnlinkExteriorModelInteriorBasePoint
      coordinateUnlinkExteriorModelInteriorBallRadius).trans
    coordinateUnlinkExteriorModelInteriorOpenPartialHomeomorph

private theorem coordinateUnlinkExteriorEuclideanAmbientChart_source :
    coordinateUnlinkExteriorEuclideanAmbientChart.source = univ := by
  ext x
  simp only [coordinateUnlinkExteriorEuclideanAmbientChart,
    OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.univBall_source, mem_inter_iff, mem_univ, true_and,
    mem_preimage]
  constructor
  · intro _
    trivial
  · intro _
    change (OpenPartialHomeomorph.univBall
        coordinateUnlinkExteriorModelInteriorBasePoint
        coordinateUnlinkExteriorModelInteriorBallRadius) x ∈
      interior (range coordinateUnlinkExteriorModel)
    apply coordinateUnlinkExteriorModelInteriorBall_subset
    rw [← OpenPartialHomeomorph.univBall_target
      coordinateUnlinkExteriorModelInteriorBasePoint
      coordinateUnlinkExteriorModelInteriorBallRadius_pos]
    have hxsource : x ∈ (OpenPartialHomeomorph.univBall
        coordinateUnlinkExteriorModelInteriorBasePoint
        coordinateUnlinkExteriorModelInteriorBallRadius).source := by
      simp
    exact (OpenPartialHomeomorph.univBall
      coordinateUnlinkExteriorModelInteriorBasePoint
      coordinateUnlinkExteriorModelInteriorBallRadius).map_source hxsource

/-- The singleton ambient chart is an open embedding. -/
theorem isOpenEmbedding_coordinateUnlinkExteriorEuclideanAmbientChart :
    IsOpenEmbedding coordinateUnlinkExteriorEuclideanAmbientChart :=
  coordinateUnlinkExteriorEuclideanAmbientChart.isOpenEmbedding
    coordinateUnlinkExteriorEuclideanAmbientChart_source

/-- The singleton ambient atlas on Euclidean four-space in the common exterior model. -/
@[instance_reducible]
def coordinateUnlinkExteriorEuclideanAmbientChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (EuclideanSpace ℝ (Fin 4)) :=
  isOpenEmbedding_coordinateUnlinkExteriorEuclideanAmbientChart.singletonChartedSpace

private theorem isManifold_coordinateUnlinkExteriorEuclideanAmbient :
    letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
    IsManifold coordinateUnlinkExteriorModel ∞
      (EuclideanSpace ℝ (Fin 4)) :=
  isOpenEmbedding_coordinateUnlinkExteriorEuclideanAmbientChart.isManifold_singleton

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
    apply coordinateUnlinkExteriorModelInteriorBall_subset
    rw [← OpenPartialHomeomorph.univBall_target
      coordinateUnlinkExteriorModelInteriorBasePoint
      coordinateUnlinkExteriorModelInteriorBallRadius_pos]
    have hxsource : x ∈ (OpenPartialHomeomorph.univBall
        coordinateUnlinkExteriorModelInteriorBasePoint
        coordinateUnlinkExteriorModelInteriorBallRadius).source := by
      simp
    exact (OpenPartialHomeomorph.univBall
      coordinateUnlinkExteriorModelInteriorBasePoint
      coordinateUnlinkExteriorModelInteriorBallRadius).map_source hxsource

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
  apply coordinateUnlinkExteriorModelInteriorBall_subset
  rw [← OpenPartialHomeomorph.univBall_target
    coordinateUnlinkExteriorModelInteriorBasePoint
    coordinateUnlinkExteriorModelInteriorBallRadius_pos]
  have hxsource : x ∈ (OpenPartialHomeomorph.univBall
      coordinateUnlinkExteriorModelInteriorBasePoint
      coordinateUnlinkExteriorModelInteriorBallRadius).source := by
    simp
  exact (OpenPartialHomeomorph.univBall
    coordinateUnlinkExteriorModelInteriorBasePoint
    coordinateUnlinkExteriorModelInteriorBallRadius).map_source hxsource

private theorem contMDiff_coordinateUnlinkExteriorEuclideanAmbientIdentity_forward :
    letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
    ContMDiff (𝓡 4) coordinateUnlinkExteriorModel ∞
      (id : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)) := by
  let _ := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
  apply ContMDiff.of_comp_isOpenEmbedding
    isOpenEmbedding_coordinateUnlinkExteriorEuclideanAmbientChart
  exact contMDiff_coordinateUnlinkExteriorEuclideanAmbientChart_standard.congr
    fun _ ↦ rfl

private theorem contMDiff_coordinateUnlinkExteriorEuclideanAmbientIdentity_reverse :
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
      apply ((OpenPartialHomeomorph.univBall
        coordinateUnlinkExteriorModelInteriorBasePoint
        coordinateUnlinkExteriorModelInteriorBallRadius).left_inv (by simp)).symm
  · simp only [comp_apply]
    rw [coordinateUnlinkExteriorEuclideanAmbientChart_coordinate]
    rw [← OpenPartialHomeomorph.univBall_target
      coordinateUnlinkExteriorModelInteriorBasePoint
      coordinateUnlinkExteriorModelInteriorBallRadius_pos]
    apply (OpenPartialHomeomorph.univBall
      coordinateUnlinkExteriorModelInteriorBasePoint
      coordinateUnlinkExteriorModelInteriorBallRadius).map_source
    simp

private def coordinateUnlinkExteriorEuclideanAmbientIdentityDiffeomorph :
    letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
    EuclideanSpace ℝ (Fin 4) ≃ₘ^∞⟮(𝓡 4),
      coordinateUnlinkExteriorModel⟯ EuclideanSpace ℝ (Fin 4) := by
  let _ := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
  exact
    { toEquiv := Equiv.refl _
      contMDiff_toFun :=
        contMDiff_coordinateUnlinkExteriorEuclideanAmbientIdentity_forward
      contMDiff_invFun :=
        contMDiff_coordinateUnlinkExteriorEuclideanAmbientIdentity_reverse }

@[simp]
private theorem coordinateUnlinkExteriorEuclideanAmbientIdentityDiffeomorph_apply
    (x : EuclideanSpace ℝ (Fin 4)) :
    letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
    coordinateUnlinkExteriorEuclideanAmbientIdentityDiffeomorph x = x := by
  rfl

private def euclideanFourBallInteriorOpens : Opens EuclideanFourBall :=
  ⟨Subtype.val ⁻¹' ball (0 : EuclideanSpace ℝ (Fin 4)) 1,
    isOpen_ball.preimage continuous_subtype_val⟩

private def euclideanFourBallAmbientInteriorOpens :
    Opens (EuclideanSpace ℝ (Fin 4)) :=
  ⟨ball (0 : EuclideanSpace ℝ (Fin 4)) 1, isOpen_ball⟩

private def euclideanFourBallInteriorEquivAmbient :
    euclideanFourBallInteriorOpens ≃
      euclideanFourBallAmbientInteriorOpens where
  toFun x := ⟨x.1.1, x.2⟩
  invFun y := ⟨⟨y.1, ball_subset_closedBall y.2⟩, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def euclideanFourBallInteriorHomeomorphAmbient :
    euclideanFourBallInteriorOpens ≃ₜ
      euclideanFourBallAmbientInteriorOpens where
  toEquiv := euclideanFourBallInteriorEquivAmbient
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

private theorem contMDiff_euclideanFourBallInteriorHomeomorphAmbient :
    ContMDiff euclideanFourBallModel (modelWithCornersSelf ℝ
      (EuclideanSpace ℝ (Fin 4))) ∞
      euclideanFourBallInteriorHomeomorphAmbient := by
  rw [← ContMDiff.subtypeVal_comp_iff
    euclideanFourBallAmbientInteriorOpens]
  exact contMDiff_closedUnitBall_inclusion
    (EuclideanSpace ℝ (Fin 4)) |>.comp contMDiff_subtype_val

private theorem contMDiff_euclideanFourBallInteriorHomeomorphAmbient_symm :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      euclideanFourBallModel ∞
      euclideanFourBallInteriorHomeomorphAmbient.symm := by
  rw [← ContMDiff.subtypeVal_comp_iff euclideanFourBallInteriorOpens]
  apply contMDiff_euclideanClosedBall_of_contMDiff_val
  exact contMDiff_subtype_val.congr fun _ ↦ rfl

private def euclideanFourBallInteriorDiffeomorphAmbient :
    euclideanFourBallInteriorOpens ≃ₘ^∞⟮euclideanFourBallModel,
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))⟯
      euclideanFourBallAmbientInteriorOpens where
  toEquiv := euclideanFourBallInteriorEquivAmbient
  contMDiff_toFun := contMDiff_euclideanFourBallInteriorHomeomorphAmbient
  contMDiff_invFun :=
    contMDiff_euclideanFourBallInteriorHomeomorphAmbient_symm

private theorem isLocalDiffeomorphAt_euclideanFourBall_inclusion_of_mem_interior
    (x : EuclideanFourBall)
    (hx : (x.1 : EuclideanSpace ℝ (Fin 4)) ∈
      ball (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    IsLocalDiffeomorphAt euclideanFourBallModel (modelWithCornersSelf ℝ
      (EuclideanSpace ℝ (Fin 4))) ∞
      (Subtype.val : EuclideanFourBall → EuclideanSpace ℝ (Fin 4)) x := by
  let u : euclideanFourBallInteriorOpens := ⟨x, hx⟩
  let hU := isLocalDiffeomorph_opensSubtypeVal euclideanFourBallModel
    euclideanFourBallInteriorOpens u
  let pU := hU.localInverse
  let e := euclideanFourBallInteriorDiffeomorphAmbient
  let v : euclideanFourBallAmbientInteriorOpens := e u
  let hV := isLocalDiffeomorph_opensSubtypeVal
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    euclideanFourBallAmbientInteriorOpens v
  let pV := Classical.choose hV
  let phi := (pU.trans e.toPartialDiffeomorph).trans pV
  have hpUx : pU x = u := by
    exact hU.localInverse_left_inv hU.localInverse_mem_target
  have hpVv : v ∈ pV.source := hV.choose_spec.1
  refine ⟨phi, ?_, ?_⟩
  · change x ∈ (pU.trans e.toPartialDiffeomorph).source ∩
      (pU.trans e.toPartialDiffeomorph) ⁻¹' pV.source
    constructor
    · change x ∈ pU.source ∩ pU ⁻¹' e.toPartialDiffeomorph.source
      refine ⟨hU.localInverse_mem_source, ?_⟩
      exact mem_univ _
    · change e (pU x) ∈ pV.source
      rw [hpUx]
      exact hpVv
  · intro y hy
    have hypU : y ∈ pU.source := hy.1.1
    have hypV : e (pU y) ∈ pV.source := by
      exact hy.2
    have hpVeq : pV (e (pU y)) =
        (e (pU y) : EuclideanSpace ℝ (Fin 4)) := by
      exact (hV.choose_spec.2 hypV).symm
    change (y : EuclideanSpace ℝ (Fin 4)) = pV (e (pU y))
    rw [hpVeq]
    change (y : EuclideanSpace ℝ (Fin 4)) = ((pU y : EuclideanFourBall) :
      EuclideanSpace ℝ (Fin 4))
    exact congrArg Subtype.val (hU.localInverse_right_inv hypU).symm

/-- The radial four-ball collar, regarded as an ambient Euclidean-space map. -/
def euclideanFourBallSmoothCollarAmbient
    (p : EuclideanFourBallCollarDomain) : EuclideanSpace ℝ (Fin 4) :=
  (euclideanFourBallSmoothCollar p : EuclideanSpace ℝ (Fin 4))

private theorem isLocalDiffeomorphOn_euclideanFourBallSmoothCollarAmbient :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
    IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      euclideanFourBallSmoothCollarAmbient
      (euclideanFourBallSmoothCollarAmbient ⁻¹'
        ball (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  let _ := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (EuclideanSpace ℝ (Fin 4)) :=
    isManifold_coordinateUnlinkExteriorEuclideanAmbient
  rintro ⟨p, hp⟩
  have hOne :=
    isLocalDiffeomorph_coordinateUnlinkExteriorRechartedFourBallCollarIdentity p
  have hTwo := isLocalDiffeomorph_euclideanFourBallSmoothCollar p
  have hThree :=
    isLocalDiffeomorphAt_euclideanFourBall_inclusion_of_mem_interior
      (euclideanFourBallSmoothCollar p) hp
  have hFour :=
    coordinateUnlinkExteriorEuclideanAmbientIdentityDiffeomorph.isLocalDiffeomorph
      (euclideanFourBallSmoothCollarAmbient p)
  have hTwelve := hOne.comp euclideanFourBallModel EuclideanFourBall hTwo
  have h123 := hTwelve.comp
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (EuclideanSpace ℝ (Fin 4)) hThree
  have h1234 := h123.comp coordinateUnlinkExteriorModel
    (EuclideanSpace ℝ (Fin 4)) hFour
  change IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
    coordinateUnlinkExteriorModel ∞
      (fun x : EuclideanFourBallCollarDomain ↦
        (euclideanFourBallSmoothCollar x : EuclideanSpace ℝ (Fin 4))) p
  simpa only [Function.comp_def, id_eq,
    coordinateUnlinkExteriorRechartedFourBallCollarIdentityDiffeomorph_apply,
    coordinateUnlinkExteriorEuclideanAmbientIdentityDiffeomorph_apply,
    euclideanFourBallSmoothCollarAmbient] using h1234

/-- The ambient carrier of the literal Euclidean four-ball cut side. -/
abbrev euclideanFourBallAmbientCarrier :
    Set (EuclideanSpace ℝ (Fin 4)) :=
  closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- The ambient cutting seam of the literal Euclidean four-ball. -/
abbrev euclideanFourBallAmbientBoundary :
    Set (EuclideanSpace ℝ (Fin 4)) :=
  sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- The part of the closed unit ball away from its cutting seam is open. -/
theorem isOpen_euclideanFourBallAmbientOffBoundary :
    IsOpen (collaredCutSideOffBoundary euclideanFourBallAmbientCarrier
      euclideanFourBallAmbientBoundary) := by
  rw [collaredCutSideOffBoundary, closedBall_sdiff_sphere]
  exact isOpen_ball

/-- The radial collar lands in the closed unit ball. -/
theorem range_euclideanFourBallSmoothCollarAmbient_subset :
    range euclideanFourBallSmoothCollarAmbient ⊆
      euclideanFourBallAmbientCarrier := by
  rintro x ⟨p, rfl⟩
  exact (euclideanFourBallSmoothCollar p).2

/-- The radial half-collar is an open embedding into the literal cut side. -/
theorem isOpenEmbedding_collaredCutSide_euclideanFourBallSmoothCollarAmbient :
    IsOpenEmbedding
      (collaredCutSideHalfCollarMap euclideanFourBallAmbientCarrier
        euclideanFourBallSmoothCollarAmbient
        range_euclideanFourBallSmoothCollarAmbient_subset) := by
  have h := isOpenEmbedding_euclideanFourBallSmoothCollar
  convert h using 1
  funext p
  apply Subtype.ext
  rfl

/-- The open unit ball and the radial half-collar cover the literal cut side. -/
theorem euclideanFourBallAmbient_cover
    (z : CollaredCutSide euclideanFourBallAmbientCarrier) :
    z.1 ∈ collaredCutSideOffBoundary euclideanFourBallAmbientCarrier
        euclideanFourBallAmbientBoundary ∨
      z.1 ∈ range euclideanFourBallSmoothCollarAmbient := by
  by_cases hz : z.1 ∈ euclideanFourBallAmbientBoundary
  · right
    let s : Sphere 3 := ⟨z.1, hz⟩
    refine ⟨(s, euclideanFourBallCollarZero), ?_⟩
    exact euclideanFourBallSmoothCollar_zero_coe s
  · left
    exact ⟨z.2, hz⟩

private theorem isLocalDiffeomorphOn_euclideanFourBallSmoothCollarAmbient_offBoundary :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
    IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      euclideanFourBallSmoothCollarAmbient
      (euclideanFourBallSmoothCollarAmbient ⁻¹'
        collaredCutSideOffBoundary euclideanFourBallAmbientCarrier
          euclideanFourBallAmbientBoundary) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
  simpa only [collaredCutSideOffBoundary, closedBall_sdiff_sphere] using
    isLocalDiffeomorphOn_euclideanFourBallSmoothCollarAmbient

/-- The direct smooth atlas on the literal Euclidean four-ball in common exterior coordinates. -/
@[instance_reducible]
def coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace EuclideanFourBall := by
  let _ := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  exact collaredCutSideChartedSpace
    euclideanFourBallAmbientCarrier euclideanFourBallAmbientBoundary
    isOpen_euclideanFourBallAmbientOffBoundary
    euclideanFourBallSmoothCollarAmbient
    range_euclideanFourBallSmoothCollarAmbient_subset
    isOpenEmbedding_collaredCutSide_euclideanFourBallSmoothCollarAmbient
    euclideanFourBallAmbient_cover

/-- The direct common-model atlas makes the literal Euclidean four-ball a smooth manifold. -/
theorem isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBall :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
    IsManifold coordinateUnlinkExteriorModel ∞ EuclideanFourBall := by
  let _ := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (EuclideanSpace ℝ (Fin 4)) :=
    isManifold_coordinateUnlinkExteriorEuclideanAmbient
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  exact isManifold_collaredCutSideChartedSpace_of_localDiffeomorphOn
    coordinateUnlinkExteriorModel ∞
    euclideanFourBallAmbientCarrier euclideanFourBallAmbientBoundary
    isOpen_euclideanFourBallAmbientOffBoundary
    euclideanFourBallSmoothCollarAmbient
    range_euclideanFourBallSmoothCollarAmbient_subset
    isOpenEmbedding_collaredCutSide_euclideanFourBallSmoothCollarAmbient
    euclideanFourBallAmbient_cover
    isLocalDiffeomorphOn_euclideanFourBallSmoothCollarAmbient_offBoundary

private theorem coordinateUnlinkExteriorEuclideanAmbient_boundary :
    letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
    coordinateUnlinkExteriorModel.boundary
      (EuclideanSpace ℝ (Fin 4)) = ∅ := by
  let _ := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (EuclideanSpace ℝ (Fin 4)) :=
    isManifold_coordinateUnlinkExteriorEuclideanAmbient
  have h :=
    coordinateUnlinkExteriorEuclideanAmbientIdentityDiffeomorph.preimage_boundary
      (by simp)
  have happ :
      (⇑coordinateUnlinkExteriorEuclideanAmbientIdentityDiffeomorph :
        EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)) = id := by
    funext x
    exact coordinateUnlinkExteriorEuclideanAmbientIdentityDiffeomorph_apply x
  rw [happ, preimage_id] at h
  simpa only [ModelWithCorners.Boundaryless.boundary_eq_empty] using h

private theorem preimage_euclideanFourBallSmoothCollarAmbient_boundary_union :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
    euclideanFourBallSmoothCollarAmbient ⁻¹'
        (coordinateUnlinkExteriorModel.boundary
            (EuclideanSpace ℝ (Fin 4)) ∪
          euclideanFourBallAmbientBoundary) =
      coordinateUnlinkExteriorModel.boundary
        EuclideanFourBallCollarDomain := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  let _ := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (EuclideanSpace ℝ (Fin 4)) :=
    isManifold_coordinateUnlinkExteriorEuclideanAmbient
  rw [coordinateUnlinkExteriorEuclideanAmbient_boundary, empty_union]
  rw [coordinateUnlinkExteriorRechartedFourBallCollar_boundary]
  change (fun x : EuclideanFourBallCollarDomain ↦
      (euclideanFourBallSmoothCollar x : EuclideanSpace ℝ (Fin 4))) ⁻¹'
        sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 =
      euclideanFourBallCollarModel.boundary
        EuclideanFourBallCollarDomain
  simpa only [euclideanFourBallSmoothCollarAmbient,
    closedUnitBallModel_boundary, preimage_preimage] using
      preimage_euclideanFourBallSmoothCollar_boundary

/-- The direct common-model atlas has exactly the established Euclidean four-ball boundary. -/
theorem coordinateUnlinkExteriorCommonModelEuclideanFourBall_boundary :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
    coordinateUnlinkExteriorModel.boundary EuclideanFourBall =
      euclideanFourBallModel.boundary EuclideanFourBall := by
  let _ := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (EuclideanSpace ℝ (Fin 4)) :=
    isManifold_coordinateUnlinkExteriorEuclideanAmbient
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ EuclideanFourBall :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBall
  have h := boundary_collaredCutSideChartedSpace_of_localDiffeomorphOn
    coordinateUnlinkExteriorModel ∞
    euclideanFourBallAmbientCarrier euclideanFourBallAmbientBoundary
    isOpen_euclideanFourBallAmbientOffBoundary
    euclideanFourBallSmoothCollarAmbient
    range_euclideanFourBallSmoothCollarAmbient_subset
    isOpenEmbedding_collaredCutSide_euclideanFourBallSmoothCollarAmbient
    euclideanFourBallAmbient_cover
    isLocalDiffeomorphOn_euclideanFourBallSmoothCollarAmbient_offBoundary
    (by simp)
    preimage_euclideanFourBallSmoothCollarAmbient_boundary_union
  rw [coordinateUnlinkExteriorEuclideanAmbient_boundary, empty_union] at h
  simpa only [closedUnitBallModel_boundary] using h

/-- The radial boundary collar into the direct common-model Euclidean four-ball. -/
def coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar
    (p : EuclideanFourBallCollarDomain) : EuclideanFourBall :=
  collaredCutSideHalfCollarMap euclideanFourBallAmbientCarrier
    euclideanFourBallSmoothCollarAmbient
    range_euclideanFourBallSmoothCollarAmbient_subset p

/-- The common-model boundary collar is literally the established radial collar. -/
@[simp]
theorem coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar_apply
    (p : EuclideanFourBallCollarDomain) :
    coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar p =
      euclideanFourBallSmoothCollar p := by
  apply Subtype.ext
  rfl

/-- The radial boundary collar is a local diffeomorphism for the direct common-model atlas. -/
theorem isLocalDiffeomorph_coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar := by
  let _ := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (EuclideanSpace ℝ (Fin 4)) :=
    isManifold_coordinateUnlinkExteriorEuclideanAmbient
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ EuclideanFourBall :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBall
  have hcompat :=
    collaredCutSideAtlasChart_compatible_of_localDiffeomorphOn
      coordinateUnlinkExteriorModel ∞
      euclideanFourBallAmbientCarrier euclideanFourBallAmbientBoundary
      isOpen_euclideanFourBallAmbientOffBoundary
      euclideanFourBallSmoothCollarAmbient
      range_euclideanFourBallSmoothCollarAmbient_subset
      isOpenEmbedding_collaredCutSide_euclideanFourBallSmoothCollarAmbient
      isLocalDiffeomorphOn_euclideanFourBallSmoothCollarAmbient_offBoundary
  exact isLocalDiffeomorph_collaredCutSideHalfCollarMap
    coordinateUnlinkExteriorModel ∞
    euclideanFourBallAmbientCarrier euclideanFourBallAmbientBoundary
    isOpen_euclideanFourBallAmbientOffBoundary
    euclideanFourBallSmoothCollarAmbient
    range_euclideanFourBallSmoothCollarAmbient_subset
    isOpenEmbedding_collaredCutSide_euclideanFourBallSmoothCollarAmbient
    euclideanFourBallAmbient_cover hcompat

/-- The radial boundary collar is smooth for the direct common-model atlas. -/
theorem contMDiff_coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
    ContMDiff coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
      coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
  exact
    isLocalDiffeomorph_coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar.contMDiff

/-- The componentwise direct common-model atlas on a discrete family of Euclidean four-balls. -/
@[instance_reducible]
def coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace
    (m : ℕ) :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m × EuclideanFourBall) :=
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
  discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) EuclideanFourBall

/-- A discrete family of direct common-model Euclidean four-balls is a smooth manifold. -/
theorem isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBallFamily
    (m : ℕ) :
    letI :=
      coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
    IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBall) := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ EuclideanFourBall :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBall
  exact isManifold_discreteProductChartedSpace
    coordinateUnlinkExteriorModel ∞ (ZMod m) EuclideanFourBall

/-- The boundary of the discrete family is the inverse image of the Euclidean four-ball boundary. -/
theorem coordinateUnlinkExteriorCommonModelEuclideanFourBallFamily_boundary
    (m : ℕ) :
    letI :=
      coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
    coordinateUnlinkExteriorModel.boundary (ZMod m × EuclideanFourBall) =
      Prod.snd ⁻¹' euclideanFourBallModel.boundary EuclideanFourBall := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ EuclideanFourBall :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBall
  let _ :=
    coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBall) :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBallFamily m
  have hlocal : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × EuclideanFourBall → EuclideanFourBall) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd (D := ZMod m)
        (P := EuclideanFourBall))
  have hboundary := hlocal.preimage_boundary (by simp)
  calc
    coordinateUnlinkExteriorModel.boundary (ZMod m × EuclideanFourBall) =
        Prod.snd ⁻¹' coordinateUnlinkExteriorModel.boundary
          EuclideanFourBall := hboundary.symm
    _ = Prod.snd ⁻¹' euclideanFourBallModel.boundary
          EuclideanFourBall := by
      rw [coordinateUnlinkExteriorCommonModelEuclideanFourBall_boundary]

end SplittingSpheres

end
