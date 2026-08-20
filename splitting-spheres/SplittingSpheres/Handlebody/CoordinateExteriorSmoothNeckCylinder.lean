/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothLocalDiffeomorphLift
public import SplittingSpheres.Geometry.ClosedBallMaps
public import SplittingSpheres.Geometry.UnlinkCyclicCover
public import SplittingSpheres.Handlebody.AlignedSphereHandleSmoothness
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarSmoothNeckArc

/-!
# The smooth neck cylinder in the coordinate-unlink cover

The vertical planar neck segment determines a disk coordinate in the aligned cap face.  Crossing
that coordinate with the unchanged `S²` factor gives a jointly smooth cylinder in the strict
coordinate-unlink complement.  The explicit smooth complex root from
`CoordinateExteriorPlanarSmoothNeckArc` then gives one smooth lift for every fixed deck label.

The lift is proved smooth in the explicit atlas pulled back along the covering projection.  No
smooth structure or smoothness assertion is made for the planar flower, partial-spin, or pushout
models, and no endpoint capping or gluing assertion is made here.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped ContDiff Manifold

namespace SplittingSpheres

/-- The product model on the closed neck interval times the two-sphere. -/
abbrev coordinateUnlinkExteriorSmoothNeckCylinderModel :=
  (modelWithCornersEuclideanHalfSpace 1).prod (𝓡 2)

/-! ## The cap-disk coordinate -/

/-- The ambient aligned cap-disk coordinate determined by the vertical neck segment. -/
def coordinateUnlinkExteriorSmoothNeckDiskRaw
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) : SphereHandleFirst :=
  sphereHandleRadius⁻¹ •
    complexToUnlinkNormalPlane
      (coordinateUnlinkExteriorPlanarNeckBaseArc t + (1 / 2 : ℂ))

@[simp]
theorem sphereHandleRadius_smul_coordinateUnlinkExteriorSmoothNeckDiskRaw
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    sphereHandleRadius • coordinateUnlinkExteriorSmoothNeckDiskRaw t =
      complexToUnlinkNormalPlane
        (coordinateUnlinkExteriorPlanarNeckBaseArc t + (1 / 2 : ℂ)) := by
  rw [coordinateUnlinkExteriorSmoothNeckDiskRaw, smul_smul,
    mul_inv_cancel₀ sphereHandleRadius_ne_zero, one_smul]

/-- The ambient disk coordinate stays in the closed unit disk. -/
theorem norm_coordinateUnlinkExteriorSmoothNeckDiskRaw_le_one
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    ‖coordinateUnlinkExteriorSmoothNeckDiskRaw t‖ ≤ 1 := by
  rw [coordinateUnlinkExteriorSmoothNeckDiskRaw, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr sphereHandleRadius_pos), norm_complexToUnlinkNormalPlane]
  exact (inv_mul_le_one₀ sphereHandleRadius_pos).2
    (norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_half_le t)

/-- The neck disk coordinate, bundled in the literal closed Euclidean two-ball. -/
def coordinateUnlinkExteriorSmoothNeckDisk
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) : EuclideanClosedBall 2 :=
  ⟨coordinateUnlinkExteriorSmoothNeckDiskRaw t,
    mem_closedBall_zero_iff.mpr
      (norm_coordinateUnlinkExteriorSmoothNeckDiskRaw_le_one t)⟩

@[simp]
theorem coordinateUnlinkExteriorSmoothNeckDisk_val
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorSmoothNeckDisk t : SphereHandleFirst) =
      sphereHandleRadius⁻¹ •
        complexToUnlinkNormalPlane
          (coordinateUnlinkExteriorPlanarNeckBaseArc t + (1 / 2 : ℂ)) :=
  rfl

/-- The ambient disk coordinate is smooth from the closed-interval model. -/
theorem contMDiff_coordinateUnlinkExteriorSmoothNeckDiskRaw :
    ContMDiff (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf ℝ SphereHandleFirst) ∞
      coordinateUnlinkExteriorSmoothNeckDiskRaw := by
  have hcoordinate : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ SphereHandleFirst) ∞
      (fun z : ℂ ↦ sphereHandleRadius⁻¹ •
        complexToUnlinkNormalPlane (z + (1 / 2 : ℂ))) := by
    apply contMDiff_iff_contDiff.mpr
    rw [contDiff_piLp]
    intro j
    fin_cases j
    · simpa [complexToUnlinkNormalPlane, Complex.reCLM_apply] using
        (contDiff_const.mul (Complex.reCLM.contDiff.add contDiff_const))
    · simpa [complexToUnlinkNormalPlane, Complex.imCLM_apply] using
        (contDiff_const.mul Complex.imCLM.contDiff)
  exact (hcoordinate.comp
    contMDiff_coordinateUnlinkExteriorPlanarNeckBaseArc).congr fun _ ↦ rfl

/-- The bundled closed-ball coordinate is smooth for the actual convex closed-ball model. -/
theorem contMDiff_coordinateUnlinkExteriorSmoothNeckDisk :
    ContMDiff (modelWithCornersEuclideanHalfSpace 1)
      (euclideanClosedBallModel 2) ∞
      coordinateUnlinkExteriorSmoothNeckDisk := by
  apply contMDiff_euclideanClosedBall_of_contMDiff_val
  exact contMDiff_coordinateUnlinkExteriorSmoothNeckDiskRaw.congr fun _ ↦ rfl

/-- Distance from the right deleted-disk center is the norm of the neck character, after
rescaling by the seam radius. -/
theorem sphereHandleRadius_mul_dist_smoothNeckDiskRaw_center_one
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    sphereHandleRadius *
        dist (coordinateUnlinkExteriorSmoothNeckDiskRaw t)
          (unlinkCapCoordinateCenter 1) =
      ‖coordinateUnlinkExteriorPlanarNeckBaseArc t‖ := by
  have hdist := dist_sphereHandleRadius_smul_unlinkCapCoordinateCenter
    (1 : Fin 2) (coordinateUnlinkExteriorSmoothNeckDiskRaw t)
  rw [sphereHandleRadius_smul_coordinateUnlinkExteriorSmoothNeckDiskRaw,
    dist_eq_norm] at hdist
  have hvec :
      complexToUnlinkNormalPlane
          (coordinateUnlinkExteriorPlanarNeckBaseArc t + (1 / 2 : ℂ)) -
        standardUnlinkNormalCenter 1 =
      complexToUnlinkNormalPlane
        (coordinateUnlinkExteriorPlanarNeckBaseArc t) := by
    ext j
    fin_cases j <;>
      simp [complexToUnlinkNormalPlane, standardUnlinkNormalCenter,
        standardUnlinkHeight]
  rw [hvec, norm_complexToUnlinkNormalPlane] at hdist
  exact hdist.symm

/-- Distance from the left deleted-disk center is the norm of the translated neck character,
after rescaling by the seam radius. -/
theorem sphereHandleRadius_mul_dist_smoothNeckDiskRaw_center_zero
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    sphereHandleRadius *
        dist (coordinateUnlinkExteriorSmoothNeckDiskRaw t)
          (unlinkCapCoordinateCenter 0) =
      ‖coordinateUnlinkExteriorPlanarNeckBaseArc t + 1‖ := by
  have hdist := dist_sphereHandleRadius_smul_unlinkCapCoordinateCenter
    (0 : Fin 2) (coordinateUnlinkExteriorSmoothNeckDiskRaw t)
  rw [sphereHandleRadius_smul_coordinateUnlinkExteriorSmoothNeckDiskRaw,
    dist_eq_norm] at hdist
  have hvec :
      complexToUnlinkNormalPlane
          (coordinateUnlinkExteriorPlanarNeckBaseArc t + (1 / 2 : ℂ)) -
        standardUnlinkNormalCenter 0 =
      complexToUnlinkNormalPlane
        (coordinateUnlinkExteriorPlanarNeckBaseArc t + 1) := by
    ext j
    fin_cases j
    · simp [complexToUnlinkNormalPlane, standardUnlinkNormalCenter,
        standardUnlinkHeight]
      ring
    · simp [complexToUnlinkNormalPlane, standardUnlinkNormalCenter,
        standardUnlinkHeight]
  rw [hvec, norm_complexToUnlinkNormalPlane] at hdist
  exact hdist.symm

/-- The neck disk avoids both radius-`1/8` deleted disks. -/
theorem coordinateUnlinkExteriorSmoothNeckDisk_mem_puncturedNormalDiskSet
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorSmoothNeckDisk t ∈
      unlinkPuncturedNormalDiskSet (1 / 8 : ℝ) := by
  change (1 / 8 : ℝ) / sphereHandleRadius ≤
        dist (coordinateUnlinkExteriorSmoothNeckDiskRaw t)
          (unlinkCapCoordinateCenter 0) ∧
      (1 / 8 : ℝ) / sphereHandleRadius ≤
        dist (coordinateUnlinkExteriorSmoothNeckDiskRaw t)
          (unlinkCapCoordinateCenter 1)
  constructor
  · apply le_of_mul_le_mul_left _ sphereHandleRadius_pos
    rw [sphereHandleRadius_mul_oneEighth_div_sphereHandleRadius,
      sphereHandleRadius_mul_dist_smoothNeckDiskRaw_center_zero]
    exact le_trans (by norm_num)
      (norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_one_ge_half t)
  · apply le_of_mul_le_mul_left _ sphereHandleRadius_pos
    rw [sphereHandleRadius_mul_oneEighth_div_sphereHandleRadius,
      sphereHandleRadius_mul_dist_smoothNeckDiskRaw_center_one]
    exact le_trans (by norm_num)
      (norm_coordinateUnlinkExteriorPlanarNeckBaseArc_ge_half t)

/-! ## The smooth base cylinder -/

/-- The label-independent cap coordinate of the neck cylinder, bundled in the exact punctured
cap. -/
def coordinateUnlinkExteriorSmoothNeckPuncturedCap
    (x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2) :
    UnlinkPuncturedCap (1 / 8 : ℝ) :=
  ⟨(coordinateUnlinkExteriorSmoothNeckDisk x.1, x.2), by
    rw [mem_unlinkPuncturedCapSet_iff]
    exact coordinateUnlinkExteriorSmoothNeckDisk_mem_puncturedNormalDiskSet x.1⟩

@[simp]
theorem coordinateUnlinkExteriorSmoothNeckPuncturedCap_disk
    (x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2) :
    (coordinateUnlinkExteriorSmoothNeckPuncturedCap x).1.1 =
      coordinateUnlinkExteriorSmoothNeckDisk x.1 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorSmoothNeckPuncturedCap_sphere
    (x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2) :
    (coordinateUnlinkExteriorSmoothNeckPuncturedCap x).1.2 = x.2 :=
  rfl

/-- The neck cylinder as an honest map into the strict coordinate-unlink complement. -/
def coordinateUnlinkExteriorSmoothNeckCylinderBase
    (x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2) :
    StandardUnlinkComplement :=
  coordinateUnlinkExteriorToComplement (r := (1 / 8 : ℝ)) (by norm_num)
    (unlinkAlignedPuncturedCapExteriorMap (1 / 8 : ℝ)
      (coordinateUnlinkExteriorSmoothNeckPuncturedCap x))

@[simp]
theorem coordinateUnlinkExteriorSmoothNeckCylinderBase_coe
    (x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2) :
    (coordinateUnlinkExteriorSmoothNeckCylinderBase x : Sphere 4) =
      unlinkAlignedCapSphereMap
        (coordinateUnlinkExteriorSmoothNeckDisk x.1, x.2) := by
  rw [coordinateUnlinkExteriorSmoothNeckCylinderBase,
    coordinateUnlinkExteriorToComplement_coe,
    unlinkAlignedPuncturedCapExteriorMap_coe]
  rfl

/-- Exact normal coordinate of the smooth base cylinder. -/
@[simp]
theorem standardUnlinkNormalProjection_smoothNeckCylinderBase
    (x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2) :
    standardUnlinkNormalProjection
        (coordinateUnlinkExteriorSmoothNeckCylinderBase x).1 =
      complexToUnlinkNormalPlane
        (coordinateUnlinkExteriorPlanarNeckBaseArc x.1 + (1 / 2 : ℂ)) := by
  rw [coordinateUnlinkExteriorSmoothNeckCylinderBase_coe,
    standardUnlinkNormalProjection_unlinkAlignedCapSphereMap,
    coordinateUnlinkExteriorSmoothNeckDisk_val,
    smul_smul, mul_inv_cancel₀ sphereHandleRadius_ne_zero, one_smul]

/-- The right-normal character of the cylinder is exactly the vertical base arc. -/
@[simp]
theorem standardUnlinkRightDisplacementComplex_smoothNeckCylinderBase
    (x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2) :
    standardUnlinkRightDisplacementComplex
        (coordinateUnlinkExteriorSmoothNeckCylinderBase x).1 =
      coordinateUnlinkExteriorPlanarNeckBaseArc x.1 := by
  rw [standardUnlinkRightDisplacementComplex,
    standardUnlinkNormalProjection_smoothNeckCylinderBase]
  have hvec :
      complexToUnlinkNormalPlane
          (coordinateUnlinkExteriorPlanarNeckBaseArc x.1 + (1 / 2 : ℂ)) -
        standardUnlinkNormalCenter 1 =
      complexToUnlinkNormalPlane
        (coordinateUnlinkExteriorPlanarNeckBaseArc x.1) := by
    ext j
    fin_cases j <;>
      simp [complexToUnlinkNormalPlane, standardUnlinkNormalCenter,
        standardUnlinkHeight]
  rw [hvec, unlinkNormalPlaneToComplex_complexToUnlinkNormalPlane]

/-- The cap-piece coordinates underlying the neck cylinder are jointly smooth. -/
theorem contMDiff_coordinateUnlinkExteriorSmoothNeckCapPiece :
    ContMDiff coordinateUnlinkExteriorSmoothNeckCylinderModel capPieceModel ∞
      (fun x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2 ↦
        (coordinateUnlinkExteriorSmoothNeckDisk x.1, x.2)) :=
  (contMDiff_coordinateUnlinkExteriorSmoothNeckDisk.comp contMDiff_fst).prodMk
    contMDiff_snd

/-- The label-independent cylinder is jointly smooth in the strict unlink complement. -/
theorem contMDiff_coordinateUnlinkExteriorSmoothNeckCylinderBase :
    ContMDiff coordinateUnlinkExteriorSmoothNeckCylinderModel (𝓡 4) ∞
      coordinateUnlinkExteriorSmoothNeckCylinderBase := by
  rw [← ContMDiff.subtypeVal_comp_iff standardUnlinkComplementOpens]
  exact (contMDiff_unlinkAlignedCapSphereMap.comp
    contMDiff_coordinateUnlinkExteriorSmoothNeckCapPiece).congr
      coordinateUnlinkExteriorSmoothNeckCylinderBase_coe

/-- The label-independent base cylinder is continuous. -/
theorem continuous_coordinateUnlinkExteriorSmoothNeckCylinderBase :
    Continuous coordinateUnlinkExteriorSmoothNeckCylinderBase :=
  contMDiff_coordinateUnlinkExteriorSmoothNeckCylinderBase.continuous

/-! ## Explicit smooth lifts -/

/-- The nonzero complex coordinate of the fixed-label lift. -/
def coordinateUnlinkExteriorSmoothNeckCylinderPowerCoordinate
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2) :
    {z : ℂ // z ≠ 0} :=
  ⟨coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate m a x.1,
    mul_ne_zero
      (Units.ne_zero
        (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).1)
      (coordinateUnlinkExteriorPlanarSmoothNeckArcComplex_ne_zero m x.1)⟩

@[simp]
theorem coordinateUnlinkExteriorSmoothNeckCylinderPowerCoordinate_coe
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2) :
    (coordinateUnlinkExteriorSmoothNeckCylinderPowerCoordinate m a x : ℂ) =
      coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate m a x.1 :=
  rfl

/-- The fixed-label direct lift into the strict-complement power pullback. -/
def coordinateUnlinkExteriorSmoothNeckCylinderLift
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2) :
    StandardUnlinkPowerPullback m :=
  ⟨(coordinateUnlinkExteriorSmoothNeckCylinderBase x,
      coordinateUnlinkExteriorSmoothNeckCylinderPowerCoordinate m a x), by
    apply Subtype.ext
    change standardUnlinkRightDisplacementComplex
        (coordinateUnlinkExteriorSmoothNeckCylinderBase x).1 =
      coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate m a x.1 ^ m
    rw [standardUnlinkRightDisplacementComplex_smoothNeckCylinderBase,
      coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate_pow]⟩

/-- Projection of the direct lift is the smooth base cylinder. -/
@[simp]
theorem coordinateUnlinkExteriorSmoothNeckCylinderLift_proj
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2) :
    standardUnlinkPowerPullbackProj m
        (coordinateUnlinkExteriorSmoothNeckCylinderLift m a x) =
      coordinateUnlinkExteriorSmoothNeckCylinderBase x :=
  rfl

/-- The second pullback coordinate is the explicit fixed-label smooth root. -/
@[simp]
theorem coordinateUnlinkExteriorSmoothNeckCylinderLift_powerCoordinate
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2) :
    (coordinateUnlinkExteriorSmoothNeckCylinderLift m a x).1.2.1 =
      coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate m a x.1 :=
  rfl

/-- The power coordinate recovers both the base arc and the right-normal character. -/
@[simp]
theorem coordinateUnlinkExteriorSmoothNeckCylinderLift_power
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2) :
    (coordinateUnlinkExteriorSmoothNeckCylinderLift m a x).1.2.1 ^ m =
      coordinateUnlinkExteriorPlanarNeckBaseArc x.1 :=
  coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate_pow m a x.1

/-- The fixed-label power coordinate is jointly continuous; it is constant in the sphere
factor. -/
theorem continuous_coordinateUnlinkExteriorSmoothNeckCylinderPowerCoordinate
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Continuous (coordinateUnlinkExteriorSmoothNeckCylinderPowerCoordinate m a) := by
  apply Continuous.subtype_mk
  exact
    (contMDiff_coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate m a).continuous.comp
      continuous_fst

/-- The explicit fixed-label direct lift is jointly continuous. -/
theorem continuous_coordinateUnlinkExteriorSmoothNeckCylinderLift
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Continuous (coordinateUnlinkExteriorSmoothNeckCylinderLift m a) := by
  apply Continuous.subtype_mk
  exact continuous_coordinateUnlinkExteriorSmoothNeckCylinderBase.prodMk
    (continuous_coordinateUnlinkExteriorSmoothNeckCylinderPowerCoordinate m a)

/-- In the explicit atlas pulled back from the strict complement, every fixed-label direct lift
is jointly smooth. -/
theorem contMDiff_coordinateUnlinkExteriorSmoothNeckCylinderLift
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    ContMDiff coordinateUnlinkExteriorSmoothNeckCylinderModel (𝓡 4) ∞
      (coordinateUnlinkExteriorSmoothNeckCylinderLift m a) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  apply contMDiff_of_comp_isLocalDiffeomorph
    coordinateUnlinkExteriorSmoothNeckCylinderModel (𝓡 4) (𝓡 4)
    (smoothCover_standardUnlinkPowerPullbackProj m).isLocalDiffeomorph
    (continuous_coordinateUnlinkExteriorSmoothNeckCylinderLift m a)
  exact contMDiff_coordinateUnlinkExteriorSmoothNeckCylinderBase.congr fun _ ↦ rfl

end SplittingSpheres
