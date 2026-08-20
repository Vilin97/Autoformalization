/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckSphere
public import SplittingSpheres.Handlebody.CoordinateExteriorSmoothNeckCylinder
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarSmoothNeckArcComparison
public import SplittingSpheres.Geometry.UnlinkEquatorPowerLift

/-!
# Comparing the planar neck spheres with the coordinate equator

This file transports the topological neck spheres from the planar-flower partial-spin model
through the literal closed exterior power pullback and into the strict unlink power pullback.
It computes both boundary faces, identifies the shifted side with the smooth neck-cylinder lift,
and proves that the projected sphere has exactly the range of the coordinate equator.  Inverting
the equatorial embedding on this range gives a continuous surjective source reparametrization.
Covering-space uniqueness then identifies the full transported lift, at the explicitly shifted
label, with the corresponding smooth equatorial lift after reparametrization.  Injectivity of
the original embedded neck sphere upgrades that reparametrization to a homeomorphism.

No separation or ambient-isotopy claim is made here.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-- Transport from the planar-flower partial spin through the original partial-spin model to
the literal radius-`1/8` closed-exterior power pullback. -/
def coordinateUnlinkExteriorPlanarNeckTransportHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m ≃ₜ
      CoordinateUnlinkExteriorEighthPowerPullback m :=
  (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph m).symm.trans
    (coordinateUnlinkExteriorPartialSphereSpinHomeomorph m)

/-- The planar base of every selected translated neck arc is the explicit smooth neck disk. -/
theorem coordinateUnlinkExteriorPlanarFlowerBase_neckArcTranslate
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarFlowerBase m
        (coordinateUnlinkExteriorPlanarNeckArcTranslate m a t) =
      coordinateUnlinkExteriorSmoothNeckDisk t := by
  apply Subtype.ext
  rw [coordinateUnlinkExteriorPlanarFlowerBase_val,
    coordinateUnlinkExteriorSmoothNeckDisk_val,
    coordinateUnlinkExteriorPlanarNeckArcTranslate_pow]

/-- Inverse flower-coordinate transport on the planar face of the partial spin. -/
theorem coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph_symm_planar
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarFlower m) (s : Sphere 2) :
    (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph m).symm
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarFlowerOuter m) (z, s)) =
      partialSphereSpinInr
        (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m)
        ((coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m).symm z,
          s) := by
  apply (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph m).injective
  rw [(coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph m).apply_symm_apply,
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph_planar,
    (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph
      m).apply_symm_apply]

/-- Inverse flower-coordinate transport is the identity on the one-handle face. -/
theorem coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph_symm_oneHandle
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph m).symm
        (partialSphereSpinInl
          (coordinateUnlinkExteriorPlanarFlowerOuter m) x) =
      partialSphereSpinInl
        (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m) x := by
  apply (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph m).injective
  rw [(coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph m).apply_symm_apply,
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph_oneHandle]

private theorem coordinateUnlinkExteriorPlanarNeckTransport_side_cap_base
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    coordinateUnlinkExteriorPuncturedCapPowerPullbackProj m
        ((coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m).symm
          ((coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m).symm
            (coordinateUnlinkExteriorPlanarNeckArcTranslate m a t), s)) =
      coordinateUnlinkExteriorSmoothNeckPuncturedCap (t, s) := by
  apply coordinateUnlinkExteriorPuncturedCapProductHomeomorph.injective
  rw [coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph_symm_proj]
  apply Prod.ext
  · apply Subtype.ext
    simpa only [coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj_apply,
      coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph_symm_base,
      coordinateUnlinkExteriorPuncturedCapProductHomeomorph_fst_val,
      coordinateUnlinkExteriorSmoothNeckPuncturedCap_disk] using
        coordinateUnlinkExteriorPlanarFlowerBase_neckArcTranslate m a t
  · rfl

/-- The transported side projects to its literal punctured-cap representative in the closed
radius-`1/8` exterior. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_side_proj_closed
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    coordinateUnlinkExteriorEighthPowerPullbackProj m
        (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (partialSphereSpinInr
            (coordinateUnlinkExteriorPlanarFlowerOuter m)
            (coordinateUnlinkExteriorPlanarNeckArcTranslate m a t, s))) =
      unlinkAlignedPuncturedCapExteriorMap (1 / 8 : ℝ)
        (coordinateUnlinkExteriorSmoothNeckPuncturedCap (t, s)) := by
  rw [coordinateUnlinkExteriorPlanarNeckTransportHomeomorph, Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph_symm_planar,
    coordinateUnlinkExteriorPartialSphereSpinHomeomorph_proj,
    coordinateUnlinkExteriorPartialSphereSpinPushoutHomeomorph_inr,
    coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout_proj,
    coordinateUnlinkExteriorPlanarNeckTransport_side_cap_base]
  exact coordinateUnlinkExteriorPushoutHomeomorph_inr (by norm_num)
    oneEighth_lt_sphereHandleRadius_sub_half _

/-- After inclusion into the strict complement, the transported side projects exactly to the
smooth neck-cylinder base. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_side_proj
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    standardUnlinkPowerPullbackProj m
        (coordinateUnlinkExteriorEighthPowerPullbackToComplement m
          (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (partialSphereSpinInr
              (coordinateUnlinkExteriorPlanarFlowerOuter m)
              (coordinateUnlinkExteriorPlanarNeckArcTranslate m a t, s)))) =
      coordinateUnlinkExteriorSmoothNeckCylinderBase (t, s) := by
  rw [standardUnlinkPowerPullbackProj_apply,
    coordinateUnlinkExteriorEighthPowerPullbackToComplement_base,
    coordinateUnlinkExteriorSmoothNeckCylinderBase]
  change coordinateUnlinkExteriorToComplement (by norm_num)
      (coordinateUnlinkExteriorEighthPowerPullbackProj m
        (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (partialSphereSpinInr
            (coordinateUnlinkExteriorPlanarFlowerOuter m)
            (coordinateUnlinkExteriorPlanarNeckArcTranslate m a t, s)))) = _
  rw [coordinateUnlinkExteriorPlanarNeckTransport_side_proj_closed]

/-- Closed-pullback transport preserves the selected neck arc's power coordinate on the side
face. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_side_powerCoordinate
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
      (partialSphereSpinInr
        (coordinateUnlinkExteriorPlanarFlowerOuter m)
        (coordinateUnlinkExteriorPlanarNeckArcTranslate m a t, s))).1.2.1 =
      (coordinateUnlinkExteriorPlanarNeckArcTranslate m a t).1.1 := by
  rw [coordinateUnlinkExteriorPlanarNeckTransportHomeomorph, Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph_symm_planar]
  unfold coordinateUnlinkExteriorPartialSphereSpinHomeomorph
  rw [Homeomorph.trans_apply,
    coordinateUnlinkExteriorPartialSphereSpinPushoutHomeomorph_inr]
  rfl

/-- With the explicit smooth label shift, strict transport of the complete side face is exactly
the smooth neck-cylinder lift. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_side_eq_smoothNeckCylinderLift
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    coordinateUnlinkExteriorEighthPowerPullbackToComplement m
        (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (partialSphereSpinInr
            (coordinateUnlinkExteriorPlanarFlowerOuter m)
            (coordinateUnlinkExteriorPlanarNeckArcTranslate m
              (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) t, s))) =
      coordinateUnlinkExteriorSmoothNeckCylinderLift m a (t, s) := by
  apply Subtype.ext
  apply Prod.ext
  · exact coordinateUnlinkExteriorPlanarNeckTransport_side_proj m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) t s
  · apply Subtype.ext
    rw [coordinateUnlinkExteriorEighthPowerPullbackToComplement_powerCoordinate,
      coordinateUnlinkExteriorPlanarNeckTransport_side_powerCoordinate,
      coordinateUnlinkExteriorSmoothNeckCylinderLift_powerCoordinate]
    exact congrArg (fun z : CoordinateUnlinkExteriorPlanarFlower m ↦ z.1.1)
      (coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate_eq_selectedTranslate_add
        m a t).symm

/-- Every point of the smooth neck-cylinder base lies in the literal coordinate equator. -/
theorem coordinateUnlinkExteriorSmoothNeckCylinderBase_mem_coordinateEquator
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    (coordinateUnlinkExteriorSmoothNeckCylinderBase (t, s) : Sphere 4) ∈
      coordinateEquator := by
  change (unlinkAlignedCapSphereMap
    (coordinateUnlinkExteriorSmoothNeckDisk t, s)).1 3 = 0
  rw [← unlinkAlignedSplitEquiv_apply_fst_zero,
    unlinkAlignedSplitEquiv_capSphereMap]
  change sphereHandleRadius *
      (coordinateUnlinkExteriorSmoothNeckDisk t).1 0 = 0
  rw [coordinateUnlinkExteriorSmoothNeckDisk_val]
  simp [complexToUnlinkNormalPlane,
    coordinateUnlinkExteriorPlanarNeckBaseArc_re]
  norm_num

/-- The transported end face projects to the one-handle face in the closed exterior. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_end_proj_closed
    (m : ℕ) [NeZero m] (a : ZMod m)
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (v : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorEighthPowerPullbackProj m
        (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (partialSphereSpinInl
            (coordinateUnlinkExteriorPlanarFlowerOuter m)
            (coordinateUnlinkExteriorPlanarNeckOuterParameter m a e, v))) =
      unlinkAlignedOneHandleExteriorMap
        oneEighth_lt_sphereHandleRadius_sub_half
        (coordinateUnlinkExteriorOneHandleBasePowerMap m
          (coordinateUnlinkExteriorPlanarNeckOuterParameter m a e, v)) := by
  rw [coordinateUnlinkExteriorPlanarNeckTransportHomeomorph, Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph_symm_oneHandle,
    coordinateUnlinkExteriorPartialSphereSpinHomeomorph_proj,
    coordinateUnlinkExteriorPartialSphereSpinPushoutHomeomorph_inl,
    coordinateUnlinkExteriorOneHandlePowerPullbackToPushout_proj,
    coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph_proj]
  exact coordinateUnlinkExteriorPushoutHomeomorph_inl (by norm_num)
    oneEighth_lt_sphereHandleRadius_sub_half _

/-- After strict-complement inclusion, the transported end face has the displayed one-handle
base coordinate. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_end_proj
    (m : ℕ) [NeZero m] (a : ZMod m)
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (v : EuclideanClosedBall 3) :
    standardUnlinkPowerPullbackProj m
        (coordinateUnlinkExteriorEighthPowerPullbackToComplement m
          (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (partialSphereSpinInl
              (coordinateUnlinkExteriorPlanarFlowerOuter m)
              (coordinateUnlinkExteriorPlanarNeckOuterParameter m a e, v)))) =
      coordinateUnlinkExteriorToComplement (by norm_num)
        (unlinkAlignedOneHandleExteriorMap
          oneEighth_lt_sphereHandleRadius_sub_half
          (coordinateUnlinkExteriorOneHandleBasePowerMap m
            (coordinateUnlinkExteriorPlanarNeckOuterParameter m a e, v))) := by
  rw [standardUnlinkPowerPullbackProj_apply,
    coordinateUnlinkExteriorEighthPowerPullbackToComplement_base]
  change coordinateUnlinkExteriorToComplement (by norm_num)
      (coordinateUnlinkExteriorEighthPowerPullbackProj m
        (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (partialSphereSpinInl
            (coordinateUnlinkExteriorPlanarFlowerOuter m)
            (coordinateUnlinkExteriorPlanarNeckOuterParameter m a e, v)))) = _
  rw [coordinateUnlinkExteriorPlanarNeckTransport_end_proj_closed]

/-- The powered outer-circle parameter of a neck endpoint is the smooth vertical disk point at
the corresponding interval endpoint. -/
theorem coordinateUnlinkExteriorPlanarNeckOuterParameter_powerDisk
    (m : ℕ) [NeZero m] (a : ZMod m)
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    (coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary
        (unlinkUnitCirclePow m
          (coordinateUnlinkExteriorPlanarNeckOuterParameter m a e))).1 =
      coordinateUnlinkExteriorSmoothNeckDisk
        (productFourEndUnitInterval e) := by
  let u := coordinateUnlinkExteriorPlanarNeckOuterParameter m a e
  calc
    (coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary
        (unlinkUnitCirclePow m u)).1 =
        (coordinateUnlinkExteriorPlanarOuterLift m u).1.1.1 :=
      congrArg Subtype.val
        (coordinateUnlinkExteriorPlanarOuterLift_proj m u).symm
    _ = (coordinateUnlinkExteriorPlanarFlowerBase m
          (coordinateUnlinkExteriorPlanarFlowerOuter m u)).1 := by
      exact congrArg Subtype.val
        (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph_base
          m (coordinateUnlinkExteriorPlanarOuterLift m u)).symm
    _ = (coordinateUnlinkExteriorPlanarFlowerBase m
          (coordinateUnlinkExteriorPlanarNeckArcTranslate m a
            (productFourEndUnitInterval e))).1 := by
      rw [coordinateUnlinkExteriorPlanarFlowerOuter_neckOuterParameter]
    _ = coordinateUnlinkExteriorSmoothNeckDisk
          (productFourEndUnitInterval e) :=
      coordinateUnlinkExteriorPlanarFlowerBase_neckArcTranslate m a _

/-- The smooth neck disk has zero first coordinate. -/
@[simp]
theorem coordinateUnlinkExteriorSmoothNeckDisk_apply_zero
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorSmoothNeckDisk t).1 0 = 0 := by
  rw [coordinateUnlinkExteriorSmoothNeckDisk_val]
  simp [complexToUnlinkNormalPlane,
    coordinateUnlinkExteriorPlanarNeckBaseArc_re]
  norm_num

/-- The second smooth neck-disk coordinate is the affine interval coordinate. -/
@[simp]
theorem coordinateUnlinkExteriorSmoothNeckDisk_apply_one
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorSmoothNeckDisk t).1 1 = 2 * (t : ℝ) - 1 := by
  rw [coordinateUnlinkExteriorSmoothNeckDisk_val,
    coordinateUnlinkExteriorPlanarNeckBaseArc_add_half]
  simp [complexToUnlinkNormalPlane, sphereHandleRadius_ne_zero]

private theorem exists_smoothNeckDisk_eq_of_apply_zero
    (d : EuclideanClosedBall 2) (hd : d.1 0 = 0) :
    ∃ t : CoordinateUnlinkExteriorPlanarNeckInterval,
      coordinateUnlinkExteriorSmoothNeckDisk t = d := by
  have hnorm : ‖d.1‖ ≤ 1 := mem_closedBall_zero_iff.mp d.2
  have hsq : ‖d.1‖ ^ 2 = d.1 0 ^ 2 + d.1 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
  have habs : |d.1 1| ≤ 1 := by
    nlinarith [sq_nonneg (d.1 0), sq_abs (d.1 1), norm_nonneg d.1]
  have hbds : -1 ≤ d.1 1 ∧ d.1 1 ≤ 1 := abs_le.mp habs
  let t : CoordinateUnlinkExteriorPlanarNeckInterval :=
    ⟨(d.1 1 + 1) / 2, by constructor <;> linarith⟩
  refine ⟨t, ?_⟩
  apply Subtype.ext
  ext j
  fin_cases j
  · change (coordinateUnlinkExteriorSmoothNeckDisk t).1 0 = d.1 0
    rw [coordinateUnlinkExteriorSmoothNeckDisk_apply_zero, hd]
  · change (coordinateUnlinkExteriorSmoothNeckDisk t).1 1 = d.1 1
    rw [coordinateUnlinkExteriorSmoothNeckDisk_apply_one]
    dsimp [t]
    ring

/-- The powered one-handle circle at a neck endpoint has zero first coordinate. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckOuterParameter_powCircle_apply_zero
    (m : ℕ) [NeZero m] (a : ZMod m)
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    (unlinkUnitCirclePow m
      (coordinateUnlinkExteriorPlanarNeckOuterParameter m a e)).1 0 = 0 := by
  have h := congrArg
    (fun d : EuclideanClosedBall 2 ↦ d.1 0)
    (coordinateUnlinkExteriorPlanarNeckOuterParameter_powerDisk m a e)
  simpa only [coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary_val,
    coordinateUnlinkExteriorSmoothNeckDisk_apply_zero] using h

/-- The powered one-handle circle at a neck endpoint has second coordinate equal to the source
`S⁰` coordinate. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckOuterParameter_powCircle_apply_one
    (m : ℕ) [NeZero m] (a : ZMod m)
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    (unlinkUnitCirclePow m
      (coordinateUnlinkExteriorPlanarNeckOuterParameter m a e)).1 1 = e.1 0 := by
  have h := congrArg
    (fun d : EuclideanClosedBall 2 ↦ d.1 1)
    (coordinateUnlinkExteriorPlanarNeckOuterParameter_powerDisk m a e)
  rw [coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary_val,
    coordinateUnlinkExteriorSmoothNeckDisk_apply_one,
    productFourEndUnitInterval_coe] at h
  linarith

private theorem exists_neckOuterParameter_powCircle_eq_of_apply_zero
    (m : ℕ) [NeZero m] (a : ZMod m)
    (u : Sphere 1) (hu : u.1 0 = 0) :
    ∃ e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1,
      unlinkUnitCirclePow m
        (coordinateUnlinkExteriorPlanarNeckOuterParameter m a e) = u := by
  have hunorm : ‖u.1‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  have huabs : |u.1 1| = 1 := by
    have hsq : ‖u.1‖ ^ 2 = u.1 0 ^ 2 + u.1 1 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_succ]
    nlinarith [abs_nonneg (u.1 1), sq_abs (u.1 1)]
  let ev : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 ![u.1 1]
  let e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := ⟨ev, by
    rw [mem_sphere_zero_iff_norm, norm_euclideanSpace_fin_one]
    simpa [ev] using huabs⟩
  refine ⟨e, ?_⟩
  apply Subtype.ext
  ext j
  fin_cases j
  · exact
      (coordinateUnlinkExteriorPlanarNeckOuterParameter_powCircle_apply_zero m a e).trans
        hu.symm
  · simp [e, ev]

/-- Every transported one-handle end base lies in the literal coordinate equator. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_end_base_mem_coordinateEquator
    (m : ℕ) [NeZero m] (a : ZMod m)
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (v : EuclideanClosedBall 3) :
    (coordinateUnlinkExteriorToComplement (by norm_num)
      (unlinkAlignedOneHandleExteriorMap
        oneEighth_lt_sphereHandleRadius_sub_half
        (coordinateUnlinkExteriorOneHandleBasePowerMap m
          (coordinateUnlinkExteriorPlanarNeckOuterParameter m a e, v))) : Sphere 4) ∈
      coordinateEquator := by
  change (unlinkAlignedOneHandleSphereMap
    (coordinateUnlinkExteriorOneHandleBasePowerMap m
      (coordinateUnlinkExteriorPlanarNeckOuterParameter m a e, v))).1 3 = 0
  rw [← unlinkAlignedSplitEquiv_apply_fst_zero,
    unlinkAlignedSplitEquiv_oneHandleSphereMap]
  change sphereHandleScale ‖v.1‖ *
      (unlinkUnitCirclePow m
        (coordinateUnlinkExteriorPlanarNeckOuterParameter m a e)).1 0 = 0
  rw [coordinateUnlinkExteriorPlanarNeckOuterParameter_powCircle_apply_zero, mul_zero]

/-- Every projected point of the transported boundary-pushout neck lies in the coordinate
equator. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_boundary_proj_mem_coordinateEquator
    (m : ℕ) [NeZero m] (a : ZMod m)
    (q : ProductFourBoundaryPushout) :
    (standardUnlinkPowerPullbackProj m
      (coordinateUnlinkExteriorEighthPowerPullbackToComplement m
        (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (coordinateUnlinkExteriorPlanarNeckBoundaryMap m a q))) : Sphere 4) ∈
      coordinateEquator := by
  rcases topologicalPushout_jointly_surjective
      productFourCornerToSide productFourCornerToEnd q with
    ⟨x, rfl⟩ | ⟨y, rfl⟩
  · rw [coordinateUnlinkExteriorPlanarNeckBoundaryMap_inl,
      coordinateUnlinkExteriorPlanarNeckSideMap_apply,
      coordinateUnlinkExteriorPlanarNeckTransport_side_proj]
    exact coordinateUnlinkExteriorSmoothNeckCylinderBase_mem_coordinateEquator _ _
  · rw [coordinateUnlinkExteriorPlanarNeckBoundaryMap_inr,
      coordinateUnlinkExteriorPlanarNeckEndMap_apply,
      coordinateUnlinkExteriorPlanarNeckTransport_end_proj]
    exact coordinateUnlinkExteriorPlanarNeckTransport_end_base_mem_coordinateEquator m a y.1 y.2

/-- Every projected point of the transported literal neck sphere lies in the coordinate
equator. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_sphere_proj_mem_coordinateEquator
    (m : ℕ) [NeZero m] (a : ZMod m) (s : Sphere 3) :
    (standardUnlinkPowerPullbackProj m
      (coordinateUnlinkExteriorEighthPowerPullbackToComplement m
        (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (coordinateUnlinkExteriorPlanarNeckSphereMap m a s))) : Sphere 4) ∈
      coordinateEquator := by
  exact coordinateUnlinkExteriorPlanarNeckTransport_boundary_proj_mem_coordinateEquator m a
    (productFourBoundaryPushoutHomeomorphSphere.symm s)

/-- The base projection of a labelled neck sphere after closed-exterior transport and inclusion
into the strict unlink power pullback. -/
def coordinateUnlinkExteriorPlanarTransportedNeckSphereBase
    (m : ℕ) [NeZero m] (a : ZMod m) (s : Sphere 3) :
    StandardUnlinkComplement :=
  standardUnlinkPowerPullbackProj m
    (coordinateUnlinkExteriorEighthPowerPullbackToComplement m
      (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
        (coordinateUnlinkExteriorPlanarNeckSphereMap m a s)))

private theorem exists_neckBoundary_proj_eq_of_mem_coordinateEquator
    (m : ℕ) [NeZero m] (a : ZMod m)
    (q : StandardUnlinkComplement) (hq : q.1 ∈ coordinateEquator) :
    ∃ r : ProductFourBoundaryPushout,
      standardUnlinkPowerPullbackProj m
        (coordinateUnlinkExteriorEighthPowerPullbackToComplement m
          (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (coordinateUnlinkExteriorPlanarNeckBoundaryMap m a r))) = q := by
  rcases exists_unlinkAlignedOneHandleSphereMap_or_capSphereMap q.1 with
    ⟨x, hx⟩ | ⟨y, hy⟩
  · have hxzero : x.1.1 0 = 0 := by
      have hqthree : q.1.1 3 = 0 := hq
      rw [← hx, ← unlinkAlignedSplitEquiv_apply_fst_zero,
        unlinkAlignedSplitEquiv_oneHandleSphereMap] at hqthree
      change sphereHandleScale ‖x.2.1‖ * x.1.1 0 = 0 at hqthree
      exact (mul_eq_zero.mp hqthree).resolve_left
        (sphereHandleScale_pos (norm_nonneg _)
          (mem_closedBall_zero_iff.mp x.2.2)).ne'
    obtain ⟨e, he⟩ :=
      exists_neckOuterParameter_powCircle_eq_of_apply_zero m a x.1 hxzero
    refine ⟨topologicalPushoutInr productFourCornerToSide productFourCornerToEnd
      (e, x.2), ?_⟩
    rw [coordinateUnlinkExteriorPlanarNeckBoundaryMap_inr,
      coordinateUnlinkExteriorPlanarNeckEndMap_apply,
      coordinateUnlinkExteriorPlanarNeckTransport_end_proj]
    have hpiece : coordinateUnlinkExteriorOneHandleBasePowerMap m
        (coordinateUnlinkExteriorPlanarNeckOuterParameter m a e, x.2) = x := by
      apply Prod.ext
      · exact he
      · rfl
    apply Subtype.ext
    rw [coordinateUnlinkExteriorToComplement_coe,
      unlinkAlignedOneHandleExteriorMap_coe, hpiece, hx]
  · have hyzero : y.1.1 0 = 0 := by
      have hqthree : q.1.1 3 = 0 := hq
      rw [← hy, ← unlinkAlignedSplitEquiv_apply_fst_zero,
        unlinkAlignedSplitEquiv_capSphereMap] at hqthree
      change sphereHandleRadius * y.1.1 0 = 0 at hqthree
      exact (mul_eq_zero.mp hqthree).resolve_left sphereHandleRadius_ne_zero
    obtain ⟨t, ht⟩ := exists_smoothNeckDisk_eq_of_apply_zero y.1 hyzero
    refine ⟨topologicalPushoutInl productFourCornerToSide productFourCornerToEnd
      ((euclideanClosedBallOneHomeomorphUnitInterval).symm t, y.2), ?_⟩
    rw [coordinateUnlinkExteriorPlanarNeckBoundaryMap_inl,
      coordinateUnlinkExteriorPlanarNeckSideMap_apply,
      (euclideanClosedBallOneHomeomorphUnitInterval).apply_symm_apply,
      coordinateUnlinkExteriorPlanarNeckTransport_side_proj]
    apply Subtype.ext
    rw [coordinateUnlinkExteriorSmoothNeckCylinderBase_coe, ht, hy]

/-- For every label, the transported neck-sphere base has exactly the range of the coordinate
equator in the strict unlink complement. -/
theorem range_coordinateUnlinkExteriorPlanarTransportedNeckSphereBase
    (m : ℕ) [NeZero m] (a : ZMod m) :
    range (coordinateUnlinkExteriorPlanarTransportedNeckSphereBase m a) =
      range equatorUnlinkComplementMap := by
  ext q
  constructor
  · rintro ⟨s, rfl⟩
    have hsphere :=
      coordinateUnlinkExteriorPlanarNeckTransport_sphere_proj_mem_coordinateEquator m a s
    rw [← range_equatorSphereMap] at hsphere
    obtain ⟨x, hx⟩ := hsphere
    exact ⟨x, Subtype.ext hx⟩
  · rintro ⟨x, rfl⟩
    have hequator : (equatorUnlinkComplementMap x).1 ∈ coordinateEquator := by
      rw [← range_equatorSphereMap]
      exact ⟨x, equatorUnlinkComplementMap_coe x⟩
    obtain ⟨r, hr⟩ :=
      exists_neckBoundary_proj_eq_of_mem_coordinateEquator m a
        (equatorUnlinkComplementMap x) hequator
    refine ⟨productFourBoundaryPushoutHomeomorphSphere r, ?_⟩
    change standardUnlinkPowerPullbackProj m
        (coordinateUnlinkExteriorEighthPowerPullbackToComplement m
          (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (coordinateUnlinkExteriorPlanarNeckBoundaryMap m a
              (productFourBoundaryPushoutHomeomorphSphere.symm
                (productFourBoundaryPushoutHomeomorphSphere r))))) = _
    rw [productFourBoundaryPushoutHomeomorphSphere.symm_apply_apply]
    exact hr

/-! ## Source reparametrization and uniqueness of the lifted sphere -/

/-- The old labelled neck sphere, transported all the way into the strict-complement power
pullback. -/
def coordinateUnlinkExteriorPlanarTransportedNeckSphereMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    C(Sphere 3, StandardUnlinkPowerPullback m) where
  toFun s :=
    coordinateUnlinkExteriorEighthPowerPullbackToComplement m
      (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
        (coordinateUnlinkExteriorPlanarNeckSphereMap m a s))
  continuous_toFun :=
    (continuous_coordinateUnlinkExteriorEighthPowerPullbackToComplement m).comp
      ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).continuous.comp
        (coordinateUnlinkExteriorPlanarNeckSphereMap m a).continuous)

@[simp]
theorem coordinateUnlinkExteriorPlanarTransportedNeckSphereMap_apply
    (m : ℕ) [NeZero m] (a : ZMod m) (s : Sphere 3) :
    coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m a s =
      coordinateUnlinkExteriorEighthPowerPullbackToComplement m
        (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (coordinateUnlinkExteriorPlanarNeckSphereMap m a s)) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarTransportedNeckSphereMap_proj
    (m : ℕ) [NeZero m] (a : ZMod m) (s : Sphere 3) :
    standardUnlinkPowerPullbackProj m
        (coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m a s) =
      coordinateUnlinkExteriorPlanarTransportedNeckSphereBase m a s :=
  rfl

theorem injective_coordinateUnlinkExteriorPlanarTransportedNeckSphereMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Injective
      (coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m a) :=
  (coordinateUnlinkExteriorEighthPowerPullbackToComplement_injective m).comp
    ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).injective.comp
      (injective_coordinateUnlinkExteriorPlanarNeckSphereMap m a))

theorem continuous_coordinateUnlinkExteriorPlanarTransportedNeckSphereBase
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Continuous
      (coordinateUnlinkExteriorPlanarTransportedNeckSphereBase m a) :=
  (isCoveringMap_standardUnlinkPowerPullbackProj m).continuous.comp
    (coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m a).continuous

/-- The unique equatorial source point over each projected old-neck point.  Exact equality of
the two projected ranges makes this map surjective; injectivity is proved below from the lifted
comparison. -/
def coordinateUnlinkExteriorPlanarNeckEquatorReparam
    (m : ℕ) [NeZero m] (a : ZMod m) : C(Sphere 3, Sphere 3) where
  toFun x :=
    isSmoothEmbedding_equatorUnlinkComplementMap.isEmbedding.toHomeomorph.symm
      ⟨coordinateUnlinkExteriorPlanarTransportedNeckSphereBase m a x, by
        rw [← range_coordinateUnlinkExteriorPlanarTransportedNeckSphereBase m a]
        exact mem_range_self x⟩
  continuous_toFun :=
    isSmoothEmbedding_equatorUnlinkComplementMap.isEmbedding.toHomeomorph.symm.continuous.comp
      ((continuous_coordinateUnlinkExteriorPlanarTransportedNeckSphereBase m a).subtype_mk _)

theorem equatorUnlinkComplementMap_neckEquatorReparam
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    equatorUnlinkComplementMap
        (coordinateUnlinkExteriorPlanarNeckEquatorReparam m a x) =
      coordinateUnlinkExteriorPlanarTransportedNeckSphereBase m a x := by
  let E := isSmoothEmbedding_equatorUnlinkComplementMap.isEmbedding.toHomeomorph
  let y : range equatorUnlinkComplementMap :=
    ⟨coordinateUnlinkExteriorPlanarTransportedNeckSphereBase m a x, by
      rw [← range_coordinateUnlinkExteriorPlanarTransportedNeckSphereBase m a]
      exact mem_range_self x⟩
  exact congrArg Subtype.val (E.apply_symm_apply y)

theorem surjective_coordinateUnlinkExteriorPlanarNeckEquatorReparam
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Surjective (coordinateUnlinkExteriorPlanarNeckEquatorReparam m a) := by
  intro x
  have hx : equatorUnlinkComplementMap x ∈
      range (coordinateUnlinkExteriorPlanarTransportedNeckSphereBase m a) := by
    rw [range_coordinateUnlinkExteriorPlanarTransportedNeckSphereBase m a]
    exact mem_range_self x
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, isSmoothEmbedding_equatorUnlinkComplementMap.isEmbedding.injective ?_⟩
  rw [equatorUnlinkComplementMap_neckEquatorReparam]
  exact hy

/-- Equality of base points identifies the logarithmic root used on the equator with the same
logarithmic root used on the smooth neck arc. -/
theorem equatorUnlinkPowerRoot_eq_smoothNeckArcComplex_of_base_eq
    (m : ℕ) [NeZero m] (x : Sphere 3)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2)
    (hbase : equatorUnlinkComplementMap x =
      coordinateUnlinkExteriorSmoothNeckCylinderBase (t, s)) :
    equatorUnlinkPowerRoot m x =
      coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m t := by
  have hcharacter := congrArg
    (fun q : StandardUnlinkComplement ↦
      standardUnlinkRightDisplacementComplex q.1) hbase
  rw [standardUnlinkRightDisplacementComplex_smoothNeckCylinderBase] at hcharacter
  have hequator :
      standardUnlinkRightDisplacementComplex
          (equatorUnlinkComplementMap x).1 =
        equatorUnlinkCharacter x :=
    standardUnlinkRightNormalMap_equatorUnlinkComplementMap x
  have hcharacter' : equatorUnlinkCharacter x =
      coordinateUnlinkExteriorPlanarNeckBaseArc t :=
    hequator.symm.trans hcharacter
  unfold equatorUnlinkPowerRoot
    coordinateUnlinkExteriorPlanarSmoothNeckArcComplex
    coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot
  rw [hcharacter']

/-- Equality of base points identifies the equally labelled equatorial and neck-cylinder
lifts. -/
theorem equatorUnlinkPowerLift_eq_smoothNeckCylinderLift_of_base_eq
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2)
    (hbase : equatorUnlinkComplementMap x =
      coordinateUnlinkExteriorSmoothNeckCylinderBase (t, s)) :
    equatorUnlinkPowerLift m a x =
      coordinateUnlinkExteriorSmoothNeckCylinderLift m a (t, s) := by
  apply Subtype.ext
  apply Prod.ext
  · exact hbase
  · apply Subtype.ext
    change equatorUnlinkPowerRootTranslate m a x =
      coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate m a t
    unfold equatorUnlinkPowerRootTranslate
      coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate
    rw [equatorUnlinkPowerRoot_eq_smoothNeckArcComplex_of_base_eq
      m x t s hbase]

private def neckEquatorComparisonBoundaryBasepoint :
    ProductFourBoundaryPushout :=
  topologicalPushoutInl productFourCornerToSide productFourCornerToEnd
    ((euclideanClosedBallOneHomeomorphUnitInterval).symm 0,
      coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint)

private def neckEquatorComparisonSphereBasepoint : Sphere 3 :=
  productFourBoundaryPushoutHomeomorphSphere
    neckEquatorComparisonBoundaryBasepoint

private theorem transportedNeckSphereMap_basepoint
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m
        (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)
        neckEquatorComparisonSphereBasepoint =
      coordinateUnlinkExteriorSmoothNeckCylinderLift m a
        (0, coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint) := by
  rw [coordinateUnlinkExteriorPlanarTransportedNeckSphereMap_apply]
  change coordinateUnlinkExteriorEighthPowerPullbackToComplement m
      (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
        (coordinateUnlinkExteriorPlanarNeckBoundaryMap m
          (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)
          (productFourBoundaryPushoutHomeomorphSphere.symm
            neckEquatorComparisonSphereBasepoint))) = _
  rw [neckEquatorComparisonSphereBasepoint,
    productFourBoundaryPushoutHomeomorphSphere.symm_apply_apply,
    neckEquatorComparisonBoundaryBasepoint,
    coordinateUnlinkExteriorPlanarNeckBoundaryMap_inl,
    coordinateUnlinkExteriorPlanarNeckSideMap_apply,
    (euclideanClosedBallOneHomeomorphUnitInterval).apply_symm_apply]
  exact
    coordinateUnlinkExteriorPlanarNeckTransport_side_eq_smoothNeckCylinderLift
      m a 0 coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint

private theorem transportedNeckSphereMap_basepoint_eq_equatorLift_reparam
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m
        (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)
        neckEquatorComparisonSphereBasepoint =
      equatorUnlinkPowerLift m a
        (coordinateUnlinkExteriorPlanarNeckEquatorReparam m
          (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)
          neckEquatorComparisonSphereBasepoint) := by
  have hbase :
      equatorUnlinkComplementMap
          (coordinateUnlinkExteriorPlanarNeckEquatorReparam m
            (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)
            neckEquatorComparisonSphereBasepoint) =
        coordinateUnlinkExteriorSmoothNeckCylinderBase
          (0, coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint) := by
    rw [equatorUnlinkComplementMap_neckEquatorReparam]
    change standardUnlinkPowerPullbackProj m
        (coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m
          (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)
          neckEquatorComparisonSphereBasepoint) = _
    rw [transportedNeckSphereMap_basepoint,
      coordinateUnlinkExteriorSmoothNeckCylinderLift_proj]
  exact (transportedNeckSphereMap_basepoint m a).trans
    (equatorUnlinkPowerLift_eq_smoothNeckCylinderLift_of_base_eq
      m a _ 0 coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint hbase).symm

/-- Covering-space uniqueness identifies the transported old sphere at selected label
`a + smoothNeckShift` with the explicit equatorial lift at label `a`, after the displayed
continuous source reparametrization. -/
theorem transportedNeckSphereMap_eq_equatorPowerLift_comp_reparam
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) :
        Sphere 3 → StandardUnlinkPowerPullback m) =
      equatorUnlinkPowerLift m a ∘
        coordinateUnlinkExteriorPlanarNeckEquatorReparam m
          (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 4)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin, Nat.one_lt_cast]
    omega
  let _ : PreconnectedSpace (Sphere 3) :=
    Subtype.preconnectedSpace
      (isPreconnected_sphere hrank (0 : EuclideanSpace ℝ (Fin 4)) 1)
  have hcomp : standardUnlinkPowerPullbackProj m ∘
        (coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m
          (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) :
            Sphere 3 → StandardUnlinkPowerPullback m) =
      standardUnlinkPowerPullbackProj m ∘
        (equatorUnlinkPowerLift m a ∘
          coordinateUnlinkExteriorPlanarNeckEquatorReparam m
            (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)) := by
    funext x
    change standardUnlinkPowerPullbackProj m
        (coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m
          (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) x) =
      standardUnlinkPowerPullbackProj m
        (equatorUnlinkPowerLift m a
          (coordinateUnlinkExteriorPlanarNeckEquatorReparam m
            (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) x))
    rw [coordinateUnlinkExteriorPlanarTransportedNeckSphereMap_proj,
      equatorUnlinkPowerLift_proj,
      equatorUnlinkComplementMap_neckEquatorReparam]
  exact (isCoveringMap_standardUnlinkPowerPullbackProj m).eq_of_comp_eq
    (coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)).continuous
    ((continuous_equatorUnlinkPowerLift m a).comp
      (coordinateUnlinkExteriorPlanarNeckEquatorReparam m
        (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)).continuous)
    hcomp neckEquatorComparisonSphereBasepoint
      (transportedNeckSphereMap_basepoint_eq_equatorLift_reparam m a)

theorem injective_neckEquatorReparam_add_shift
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Injective (coordinateUnlinkExteriorPlanarNeckEquatorReparam m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)) := by
  intro x y hxy
  apply injective_coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m
    (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)
  have h := congrArg (equatorUnlinkPowerLift m a) hxy
  exact (congrFun
    (transportedNeckSphereMap_eq_equatorPowerLift_comp_reparam m a) x).trans
      (h.trans (congrFun
        (transportedNeckSphereMap_eq_equatorPowerLift_comp_reparam m a) y).symm)

theorem injective_coordinateUnlinkExteriorPlanarNeckEquatorReparam
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Injective (coordinateUnlinkExteriorPlanarNeckEquatorReparam m a) := by
  simpa only [sub_add_cancel] using
    injective_neckEquatorReparam_add_shift m
      (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m)

/-- The source reparametrization as an honest homeomorphism of the literal `Sphere 3`. -/
def coordinateUnlinkExteriorPlanarNeckEquatorHomeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) : Sphere 3 ≃ₜ Sphere 3 :=
  IsHomeomorph.homeomorph _ <|
    (isHomeomorph_iff_continuous_bijective).2
      ⟨(coordinateUnlinkExteriorPlanarNeckEquatorReparam m a).continuous,
        injective_coordinateUnlinkExteriorPlanarNeckEquatorReparam m a,
        surjective_coordinateUnlinkExteriorPlanarNeckEquatorReparam m a⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckEquatorHomeomorph_apply
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    coordinateUnlinkExteriorPlanarNeckEquatorHomeomorph m a x =
      coordinateUnlinkExteriorPlanarNeckEquatorReparam m a x :=
  rfl

/-- Exact range comparison in the requested label convention: the old selected label
`a + smoothNeckShift` and the explicit equatorial label `a` give the same lifted sphere. -/
theorem range_transportedNeckSphereMap_eq_equatorPowerLift
    (m : ℕ) [NeZero m] (a : ZMod m) :
    range (coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)) =
      range (equatorUnlinkPowerLift m a) := by
  rw [transportedNeckSphereMap_eq_equatorPowerLift_comp_reparam]
  exact
    (surjective_coordinateUnlinkExteriorPlanarNeckEquatorReparam m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)).range_comp _

/-- Equivalent range comparison indexed by the old selected label itself. -/
theorem range_transportedNeckSphereMap_eq_equatorPowerLift_sub_shift
    (m : ℕ) [NeZero m] (a : ZMod m) :
    range (coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m a) =
      range (equatorUnlinkPowerLift m
        (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m)) := by
  convert range_transportedNeckSphereMap_eq_equatorPowerLift m
    (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) using 1
  rw [sub_add_cancel]

end SplittingSpheres

end
