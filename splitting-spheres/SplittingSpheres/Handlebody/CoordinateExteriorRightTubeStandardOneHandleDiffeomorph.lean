/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorRightTubeStandardSmoothStructure
import all SplittingSpheres.Handlebody.CoordinateExteriorRightTubeOneHandleDiffeomorph

/-!
# The standard right-tube exterior as a smooth one-handle

This file recognizes the closed right-tube exterior with its literal standard-collar atlas as
`OneHandlePiece`. It then lifts that recognition to the cyclic power pullback and composes with
the existing smooth trivialization of the one-handle power pullback.
-/

public section

open Function Metric Set Topology TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

private theorem standardRightTubeAtlas_compatible
    (i j : CollaredCutSideAtlasIndex
      coordinateExteriorRightTubeClosedCarrier
      coordinateExteriorRightTubeBoundary
      CoordinateExteriorRightTubeClosedCollarDomain) :
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    letI := coordinateExteriorRightTubeStandardChartedSpace
    (collaredCutSideAtlasChart
        coordinateExteriorRightTubeClosedCarrier
        coordinateExteriorRightTubeBoundary
        isOpen_coordinateExteriorRightTubeClosed_offBoundary
        coordinateExteriorRightTubeStandardCollarAmbient
        range_coordinateExteriorRightTubeStandardCollarAmbient_subset
        isOpenEmbedding_coordinateExteriorRightTubeStandardBoundaryCollar i).symm.trans
      (collaredCutSideAtlasChart
        coordinateExteriorRightTubeClosedCarrier
        coordinateExteriorRightTubeBoundary
        isOpen_coordinateExteriorRightTubeClosed_offBoundary
        coordinateExteriorRightTubeStandardCollarAmbient
        range_coordinateExteriorRightTubeStandardCollarAmbient_subset
        isOpenEmbedding_coordinateExteriorRightTubeStandardBoundaryCollar j) ∈
      contDiffGroupoid ∞ coordinateUnlinkExteriorModel := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  apply (contDiffGroupoid ∞ coordinateUnlinkExteriorModel).compatible
  · exact ⟨i, rfl⟩
  · exact ⟨j, rfl⟩

private theorem isLocalDiffeomorph_coordinateExteriorRightTubeStandardOffMap :
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (collaredCutSideOffBoundaryOpensMap
        coordinateExteriorRightTubeClosedCarrier
        coordinateExteriorRightTubeBoundary
        isOpen_coordinateExteriorRightTubeClosed_offBoundary) := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  exact isLocalDiffeomorph_collaredCutSideOffBoundaryMap
    coordinateUnlinkExteriorModel ∞
    coordinateExteriorRightTubeClosedCarrier
    coordinateExteriorRightTubeBoundary
    isOpen_coordinateExteriorRightTubeClosed_offBoundary
    coordinateExteriorRightTubeStandardCollarAmbient
    range_coordinateExteriorRightTubeStandardCollarAmbient_subset
    isOpenEmbedding_coordinateExteriorRightTubeStandardBoundaryCollar
    coordinateExteriorRightTubeClosed_offBoundary_or_standardCollar
    standardRightTubeAtlas_compatible

private theorem isLocalDiffeomorph_coordinateExteriorRightTubeStandardBoundaryCollar :
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      coordinateExteriorRightTubeStandardBoundaryCollar := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  exact isLocalDiffeomorph_collaredCutSideHalfCollarMap
    coordinateUnlinkExteriorModel ∞
    coordinateExteriorRightTubeClosedCarrier
    coordinateExteriorRightTubeBoundary
    isOpen_coordinateExteriorRightTubeClosed_offBoundary
    coordinateExteriorRightTubeStandardCollarAmbient
    range_coordinateExteriorRightTubeStandardCollarAmbient_subset
    isOpenEmbedding_coordinateExteriorRightTubeStandardBoundaryCollar
    coordinateExteriorRightTubeClosed_offBoundary_or_standardCollar
    standardRightTubeAtlas_compatible

private theorem isLocalDiffeomorph_coordinateExteriorRightTubeOneHandleHomeomorph_standard :
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel oneHandlePieceModel ∞
      coordinateExteriorRightTubeOneHandleHomeomorph := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let U := collaredCutSideOffBoundaryOpens
    coordinateExteriorRightTubeClosedCarrier
    coordinateExteriorRightTubeBoundary
    isOpen_coordinateExteriorRightTubeClosed_offBoundary
  let cOne : U → CoordinateExteriorRightTubeClosed :=
    collaredCutSideOffBoundaryOpensMap
      coordinateExteriorRightTubeClosedCarrier
      coordinateExteriorRightTubeBoundary
      isOpen_coordinateExteriorRightTubeClosed_offBoundary
  let cTwo : CoordinateExteriorRightTubeClosedCollarDomain →
      CoordinateExteriorRightTubeClosed :=
    coordinateExteriorRightTubeStandardBoundaryCollar
  have hcOne : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ cOne :=
    isLocalDiffeomorph_coordinateExteriorRightTubeStandardOffMap
  have hcTwo : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ cTwo :=
    isLocalDiffeomorph_coordinateExteriorRightTubeStandardBoundaryCollar
  have hFcOne : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      oneHandlePieceModel ∞
      (coordinateExteriorRightTubeOneHandleHomeomorph ∘ cOne) := by
    let _ := RightTubeClosedFinalProbe.rightTubeClosedOneHandleChartedSpace
    let UCustom := collaredCutSideOffBoundaryOpens
      RightTubeRadialScout.rightTubeClosedCarrier
      RightTubeRadialScout.rightTubeClosedBoundary
      RightTubeRadialScout.isOpen_collaredCutSideOffBoundary_rightTubeClosed
    have hU : UCustom = U := by
      apply Opens.ext
      rfl
    let cOneCustom : UCustom → RightTubeRadialScout.RightTubeClosed :=
      collaredCutSideOffBoundaryOpensMap
        RightTubeRadialScout.rightTubeClosedCarrier
        RightTubeRadialScout.rightTubeClosedBoundary
        RightTubeRadialScout.isOpen_collaredCutSideOffBoundary_rightTubeClosed
    have hcOneCustom : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞ cOneCustom :=
      RightTubeClosedFinalProbe.isLocalDiffeomorph_rightTubeClosedOffMap
    subst UCustom
    rw [show coordinateExteriorRightTubeOneHandleHomeomorph ∘ cOne =
        RightTubeRadialScout.rightTubeClosedOneHandleHomeomorph ∘ cOneCustom by
      funext x
      rfl]
    intro x
    exact (hcOneCustom x).comp oneHandlePieceModel OneHandlePiece
      (RightTubeClosedFinalProbe.isLocalDiffeomorph_rightTubeClosedOneHandleHomeomorph
        (cOneCustom x))
  have hFcTwo : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      oneHandlePieceModel ∞
      (coordinateExteriorRightTubeOneHandleHomeomorph ∘ cTwo) := by
    rw [show coordinateExteriorRightTubeOneHandleHomeomorph ∘ cTwo =
        coordinateExteriorRightTubeOneHandleStandardCollarMap by
      funext p
      apply congrArg coordinateExteriorRightTubeOneHandleHomeomorph
      apply Subtype.ext
      rfl]
    exact isLocalDiffeomorph_coordinateExteriorRightTubeOneHandleStandardCollarMap
  apply isLocalDiffeomorph_of_three_localDiffeomorph_parametrizations
    coordinateUnlinkExteriorModel oneHandlePieceModel
    coordinateExteriorRightTubeOneHandleHomeomorph cOne cTwo cTwo
    hcOne hcTwo hcTwo hFcOne hFcTwo hFcTwo
  intro z
  rcases coordinateExteriorRightTubeClosed_offBoundary_or_standardCollar z with hz | hz
  · exact Or.inl ⟨⟨z.1, hz⟩, Subtype.ext rfl⟩
  · rcases hz with ⟨p, hp⟩
    exact Or.inr (Or.inl ⟨p, Subtype.ext hp⟩)

/-- The closed right-tube exterior with its standard-collar atlas is the natural one-handle. -/
noncomputable def coordinateExteriorRightTubeOneHandleStandardDiffeomorph :
    letI := coordinateExteriorRightTubeStandardChartedSpace
    CoordinateExteriorRightTubeClosed
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, oneHandlePieceModel⟯
        OneHandlePiece := by
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  exact diffeomorphOfHomeomorphIsLocalDiffeomorph
    coordinateUnlinkExteriorModel oneHandlePieceModel
    coordinateExteriorRightTubeOneHandleHomeomorph
    isLocalDiffeomorph_coordinateExteriorRightTubeOneHandleHomeomorph_standard

@[simp] theorem coordinateExteriorRightTubeOneHandleStandardDiffeomorph_apply
    (q : CoordinateExteriorRightTubeClosed) :
    letI := coordinateExteriorRightTubeStandardChartedSpace
    coordinateExteriorRightTubeOneHandleStandardDiffeomorph q =
      coordinateExteriorRightTubeOneHandleHomeomorph q := by
  rfl

@[simp] theorem coordinateExteriorRightTubeOneHandleStandardDiffeomorph_toHomeomorph :
    letI := coordinateExteriorRightTubeStandardChartedSpace
    coordinateExteriorRightTubeOneHandleStandardDiffeomorph.toHomeomorph =
      coordinateExteriorRightTubeOneHandleHomeomorph := by
  rfl

/-- Lift the standard-atlas right-tube diffeomorphism to the cyclic power pullbacks. -/
noncomputable def coordinateExteriorRightTubePowerPullbackStandardDiffeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateExteriorRightTubePowerPullback m) :=
      isManifold_coordinateExteriorRightTubePowerPullbackStandard m
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    letI : IsManifold oneHandlePieceModel ∞
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
    CoordinateExteriorRightTubePowerPullback m
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, oneHandlePieceModel⟯
        CoordinateUnlinkExteriorOneHandlePowerPullback m := by
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullbackStandard m
  let _ : ChartedSpace OneHandleModelSpace
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
  let _ : IsManifold oneHandlePieceModel ∞
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
  exact diffeomorphOfHomeomorphOverDiffeomorph
    coordinateUnlinkExteriorModel oneHandlePieceModel
    (coordinateExteriorRightTubePowerPullbackProj m)
    (coordinateUnlinkExteriorOneHandlePowerPullbackProj m)
    (isLocalDiffeomorph_coordinateExteriorRightTubePowerPullbackProj_standard m)
    (isLocalDiffeomorph_coordinateUnlinkExteriorOneHandlePowerPullbackProj m)
    coordinateExteriorRightTubeOneHandleStandardDiffeomorph
    (coordinateExteriorRightTubePowerPullbackHomeomorph m)
    (fun z ↦ by
      rw [coordinateExteriorRightTubePowerPullbackHomeomorph_proj]
      rw [coordinateExteriorRightTubeOneHandleDiffeomorph_apply]
      exact
        (coordinateExteriorRightTubeOneHandleStandardDiffeomorph_apply
          (coordinateExteriorRightTubePowerPullbackProj m z)).symm)

@[simp] theorem coordinateExteriorRightTubePowerPullbackStandardDiffeomorph_apply
    (m : ℕ) [NeZero m]
    (z : CoordinateExteriorRightTubePowerPullback m) :
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateExteriorRightTubePowerPullback m) :=
      isManifold_coordinateExteriorRightTubePowerPullbackStandard m
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    letI : IsManifold oneHandlePieceModel ∞
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
    coordinateExteriorRightTubePowerPullbackStandardDiffeomorph m z =
      coordinateExteriorRightTubePowerPullbackHomeomorph m z := by
  rfl

@[simp] theorem coordinateExteriorRightTubePowerPullbackStandardDiffeomorph_toHomeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateExteriorRightTubePowerPullback m) :=
      isManifold_coordinateExteriorRightTubePowerPullbackStandard m
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    letI : IsManifold oneHandlePieceModel ∞
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
    (coordinateExteriorRightTubePowerPullbackStandardDiffeomorph m).toHomeomorph =
      coordinateExteriorRightTubePowerPullbackHomeomorph m := by
  rfl

theorem coordinateExteriorRightTubePowerPullbackStandardDiffeomorph_proj
    (m : ℕ) [NeZero m]
    (z : CoordinateExteriorRightTubePowerPullback m) :
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateExteriorRightTubePowerPullback m) :=
      isManifold_coordinateExteriorRightTubePowerPullbackStandard m
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    letI : IsManifold oneHandlePieceModel ∞
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
    coordinateUnlinkExteriorOneHandlePowerPullbackProj m
        (coordinateExteriorRightTubePowerPullbackStandardDiffeomorph m z) =
      coordinateExteriorRightTubeOneHandleStandardDiffeomorph
        (coordinateExteriorRightTubePowerPullbackProj m z) := by
  rfl

/-- Trivialize the standard-atlas right-tube power pullback as the natural one-handle. -/
noncomputable def coordinateExteriorRightTubePowerPullbackStandardOneHandleDiffeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateExteriorRightTubePowerPullback m) :=
      isManifold_coordinateExteriorRightTubePowerPullbackStandard m
    CoordinateExteriorRightTubePowerPullback m
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, oneHandlePieceModel⟯
        OneHandlePiece := by
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullbackStandard m
  let _ : ChartedSpace OneHandleModelSpace
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
  let _ : IsManifold oneHandlePieceModel ∞
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
  exact (coordinateExteriorRightTubePowerPullbackStandardDiffeomorph m).trans
    (coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph m).symm

@[simp] theorem coordinateExteriorRightTubePowerPullbackStandardOneHandleDiffeomorph_apply
    (m : ℕ) [NeZero m]
    (z : CoordinateExteriorRightTubePowerPullback m) :
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateExteriorRightTubePowerPullback m) :=
      isManifold_coordinateExteriorRightTubePowerPullbackStandard m
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    letI : IsManifold oneHandlePieceModel ∞
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
    coordinateExteriorRightTubePowerPullbackStandardOneHandleDiffeomorph m z =
      (coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph m).symm
        (coordinateExteriorRightTubePowerPullbackHomeomorph m z) := by
  rfl

@[simp] theorem
    coordinateExteriorRightTubePowerPullbackStandardOneHandleDiffeomorph_toHomeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateExteriorRightTubePowerPullback m) :=
      isManifold_coordinateExteriorRightTubePowerPullbackStandard m
    (coordinateExteriorRightTubePowerPullbackStandardOneHandleDiffeomorph m).toHomeomorph =
      (coordinateExteriorRightTubePowerPullbackHomeomorph m).trans
        (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m).symm := by
  rfl

theorem coordinateExteriorRightTubePowerPullbackStandardOneHandleDiffeomorph_proj
    (m : ℕ) [NeZero m]
    (z : CoordinateExteriorRightTubePowerPullback m) :
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateExteriorRightTubePowerPullback m) :=
      isManifold_coordinateExteriorRightTubePowerPullbackStandard m
    coordinateUnlinkExteriorOneHandleBasePowerMap m
        (coordinateExteriorRightTubePowerPullbackStandardOneHandleDiffeomorph m z) =
      coordinateExteriorRightTubeOneHandleStandardDiffeomorph
        (coordinateExteriorRightTubePowerPullbackProj m z) := by
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullbackStandard m
  let _ : ChartedSpace OneHandleModelSpace
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
  let _ : IsManifold oneHandlePieceModel ∞
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
  rw [coordinateExteriorRightTubePowerPullbackStandardOneHandleDiffeomorph_apply]
  rw [← coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph_proj]
  rw [Diffeomorph.apply_symm_apply]
  exact coordinateExteriorRightTubePowerPullbackStandardDiffeomorph_proj m z

end SplittingSpheres
