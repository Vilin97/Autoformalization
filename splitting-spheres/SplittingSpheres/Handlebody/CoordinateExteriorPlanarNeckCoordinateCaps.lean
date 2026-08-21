/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckCoordinateEquator
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckFullCoverExactComponents

/-!
# Coordinate-cap orientation of the full planar neck

The two global off-seam sides of the strict planar neck are identified with the inverse images
of the negative and positive coordinate hemispheres in the standard unlink power cover.  The
orientation is fixed by an explicit normalized left-annulus point.  On the right, deterministic
paths in the strict right column preserve avoidance of the entire labelled attaching family and
connect every point to the normalized open right annulus.

This file makes no assertion about the raw compact collar orientation, compact cut carriers,
normalized-annulus smoothness, or rounded capping recognition.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open Set.Notation
open scoped unitInterval

namespace SplittingSpheres

private def capOrientationHalfTime : Set.Icc (0 : ℝ) 1 :=
  ⟨1 / 2, by norm_num, by norm_num⟩

private def capOrientationCirclePoint : Sphere 1 :=
  unlinkMeridianCirclePoint 0

private def capOrientationSpherePoint : Sphere 2 :=
  coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint

private def capOrientationLeftFlowerPoint
    (m : ℕ) [NeZero m] (a : ZMod m) :
    CoordinateUnlinkExteriorPlanarFlower m :=
  coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint m a
    capOrientationCirclePoint capOrientationHalfTime

private def capOrientationLeftClosedPoint
    (m : ℕ) [NeZero m] (a : ZMod m) :
    CoordinateUnlinkExteriorEighthPowerPullback m :=
  coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
    (partialSphereSpinInr (coordinateUnlinkExteriorPlanarFlowerOuter m)
      (capOrientationLeftFlowerPoint m a, capOrientationSpherePoint))

private theorem capOrientationLeftClosedPoint_mem_strict
    (m : ℕ) [NeZero m] (a : ZMod m) :
    capOrientationLeftClosedPoint m a ∈
      coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m := by
  exact coordinateUnlinkExteriorPlanarNeckTransport_normalizedLeft_mem_strict_of_pos
    m a capOrientationCirclePoint capOrientationHalfTime capOrientationSpherePoint
      (by norm_num [capOrientationHalfTime])

private theorem capOrientationLeftFlowerPoint_pow
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (capOrientationLeftFlowerPoint m a).1.1 ^ m = (-11 / 16 : ℂ) := by
  rw [capOrientationLeftFlowerPoint,
    coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint_pow,
    coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_apply_coe]
  unfold directionalRadialAnnulusRadius capOrientationHalfTime
    capOrientationCirclePoint coordinateUnlinkExteriorPlanarLeftOuterRadius
    coordinateUnlinkExteriorPlanarLeftOuterRadiusScalar
  rw [unlinkUnitCircleHomeomorph_coe]
  simp only [unlinkUnitCircleComplex_circlePoint]
  norm_num
  rw [ite_eq_right (not_le.mpr planarNeckAngularThreshold_lt_one)]
  norm_num

private theorem capOrientationLeftClosedPoint_not_mem_closedTubes_quarter
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (capOrientationLeftClosedPoint m a).1.1.1 ∉
      standardUnlinkClosedTubes (1 / 4 : ℝ) := by
  simp only [standardUnlinkClosedTubes, standardUnlinkClosedTube,
    mem_union, mem_preimage, mem_closedBall, dist_eq_norm, not_or, not_le]
  constructor
  · rw [capOrientationLeftClosedPoint,
      coordinateUnlinkExteriorPlanarNeckTransport_planar_leftTubeDistance
      m (capOrientationLeftFlowerPoint m a) capOrientationSpherePoint,
      capOrientationLeftFlowerPoint_pow]
    norm_num [Complex.norm_def]
  · rw [capOrientationLeftClosedPoint,
      coordinateUnlinkExteriorPlanarNeckTransport_planar_rightTubeDistance
      m (capOrientationLeftFlowerPoint m a) capOrientationSpherePoint,
      capOrientationLeftFlowerPoint_pow]
    norm_num [Complex.norm_def]

private def capOrientationLeftStrictPoint
    (m : ℕ) [NeZero m] (a : ZMod m) :
    CoordinateUnlinkExteriorEighthPowerPullbackStrict m :=
  ⟨capOrientationLeftClosedPoint m a,
    capOrientationLeftClosedPoint_mem_strict m a⟩

private def capOrientationLeftFullCoverPoint
    (m : ℕ) [NeZero m] (a : ZMod m) :
    StandardUnlinkPowerPullback m :=
  (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).symm
    (capOrientationLeftStrictPoint m a)

private theorem capOrientationLeftFullCoverPoint_proj_coe
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (standardUnlinkPowerPullbackProj m
        (capOrientationLeftFullCoverPoint m a) : Sphere 4) =
      (capOrientationLeftClosedPoint m a).1.1.1 := by
  change (standardUnlinkPowerPullbackProj m
      ((standardUnlinkPowerPullbackExteriorHomeomorph m).symm
        ((standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictHomeomorph m).symm
          (capOrientationLeftStrictPoint m a))) : Sphere 4) = _
  rw [standardUnlinkPowerPullbackExteriorHomeomorph_symm_proj]
  apply
    standardUnlinkComplementExteriorHomeomorph_symm_eq_self_of_not_mem_closedTubes_quarter
  change (capOrientationLeftClosedPoint m a).1.1.1 ∉
    standardUnlinkClosedTubes (1 / 4 : ℝ)
  exact capOrientationLeftClosedPoint_not_mem_closedTubes_quarter m a

private theorem capOrientation_planar_proj_closed_formula
    (m : ℕ) [NeZero m] (z : CoordinateUnlinkExteriorPlanarFlower m)
    (s : Sphere 2) :
    coordinateUnlinkExteriorEighthPowerPullbackProj m
        (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (partialSphereSpinInr
            (coordinateUnlinkExteriorPlanarFlowerOuter m) (z, s))) =
      unlinkAlignedPuncturedCapExteriorMap (1 / 8 : ℝ)
        (coordinateUnlinkExteriorPuncturedCapProductHomeomorph.symm
          (coordinateUnlinkExteriorPlanarFlowerBase m z, s)) := by
  rw [coordinateUnlinkExteriorPlanarNeckTransportHomeomorph, Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph_symm_planar,
    coordinateUnlinkExteriorPartialSphereSpinHomeomorph_proj,
    coordinateUnlinkExteriorPartialSphereSpinPushoutHomeomorph_inr,
    coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout_proj]
  apply coordinateUnlinkExteriorPushoutHomeomorph_inr (by norm_num)
    oneEighth_lt_sphereHandleRadius_sub_half

private theorem capOrientationLeftClosedPoint_coord_three
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (capOrientationLeftClosedPoint m a).1.1.1.1 3 = -3 / 16 := by
  change (coordinateUnlinkExteriorEighthPowerPullbackProj m
      (capOrientationLeftClosedPoint m a) : Sphere 4).1 3 = _
  rw [capOrientationLeftClosedPoint, capOrientation_planar_proj_closed_formula]
  change (unlinkAlignedCapSphereMap
    (coordinateUnlinkExteriorPuncturedCapProductHomeomorph.symm
      (coordinateUnlinkExteriorPlanarFlowerBase m
        (capOrientationLeftFlowerPoint m a), capOrientationSpherePoint)).1).1 3 = _
  rw [← unlinkAlignedSplitEquiv_apply_fst_zero,
    unlinkAlignedSplitEquiv_capSphereMap]
  change sphereHandleRadius *
      (coordinateUnlinkExteriorPuncturedCapProductHomeomorph.symm
        (coordinateUnlinkExteriorPlanarFlowerBase m
          (capOrientationLeftFlowerPoint m a), capOrientationSpherePoint)).1.1.1 0 = _
  rw [coordinateUnlinkExteriorPuncturedCapProductHomeomorph_symm_fst_val]
  change (sphereHandleRadius •
      coordinateUnlinkExteriorPlanarFlowerBaseRaw m
        (capOrientationLeftFlowerPoint m a).1) 0 = _
  rw [sphereHandleRadius_smul_coordinateUnlinkExteriorPlanarFlowerBaseRaw,
    capOrientationLeftFlowerPoint_pow]
  norm_num [complexToUnlinkNormalPlane]

private theorem capOrientationLeftFullCoverPoint_mem_cap_zero
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (standardUnlinkPowerPullbackProj m
      (capOrientationLeftFullCoverPoint m a) : Sphere 4) ∈
        coordinateOpenCap 0 := by
  rw [mem_coordinateOpenCap_zero,
    capOrientationLeftFullCoverPoint_proj_coe,
    capOrientationLeftClosedPoint_coord_three]
  norm_num

private theorem coordinateUnlinkExteriorPlanarFullCoverToNeckStar_capOrientationLeft
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFullCoverToNeckStar m
        (capOrientationLeftFullCoverPoint m a) =
      coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m a
        capOrientationCirclePoint capOrientationHalfTime capOrientationSpherePoint := by
  rw [capOrientationLeftFullCoverPoint]
  change coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
      ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm
        ((coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m
          ((coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).symm
            (capOrientationLeftStrictPoint m a))).1)) = _
  rw [(coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).apply_symm_apply]
  change coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
      ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm
        (capOrientationLeftClosedPoint m a)) = _
  rw [capOrientationLeftClosedPoint,
    (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm_apply_apply]
  rfl

private theorem capOrientationLeftFullCoverPoint_mem_selected
    (m : ℕ) [NeZero m] (a : ZMod m) :
    capOrientationLeftFullCoverPoint m
        (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) ∈
      coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a := by
  change coordinateUnlinkExteriorPlanarFullCoverToNeckStar m
      (capOrientationLeftFullCoverPoint m
        (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)) ∈
      coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m
        (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)
  rw [coordinateUnlinkExteriorPlanarFullCoverToNeckStar_capOrientationLeft]
  exact coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_mem_leaf
    m (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)
      capOrientationCirclePoint capOrientationHalfTime capOrientationSpherePoint
      (by norm_num [capOrientationHalfTime])

/-- The global strict left side is the union of the selected labelled left sides. -/
theorem coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam_eq_iUnion_equatorLeftSide
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam m =
      ⋃ a : ZMod m, coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a := by
  rw [coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam]
  change coordinateUnlinkExteriorPlanarFullCoverToNeckStar m ⁻¹'
      coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam m =
    ⋃ a : ZMod m, coordinateUnlinkExteriorPlanarFullCoverToNeckStar m ⁻¹'
      coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m
        (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)
  rw [← preimage_iUnion]
  congr 1
  ext z
  simp only [coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam,
    coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam,
    topologicalPushoutInlOffSeam, topologicalPushoutInlFiberOffSeam,
    mem_image, mem_compl_iff, mem_range, Set.mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨coordinateUnlinkExteriorPlanarNeckStarLeftLabel m x -
        coordinateUnlinkExteriorPlanarSmoothNeckShift m, x,
      ⟨by simp, hx⟩, rfl⟩
  · rintro ⟨a, x, ⟨_hlabel, hx⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

private def capOrientationBaseProj
    (m : ℕ) (z : StandardUnlinkPowerPullback m) : Sphere 4 :=
  standardUnlinkPowerPullbackProj m z

private theorem continuous_capOrientationBaseProj
    (m : ℕ) [NeZero m] :
    Continuous (capOrientationBaseProj m) :=
  continuous_subtype_val.comp
    (isCoveringMap_standardUnlinkPowerPullbackProj m).continuous

private theorem isOpen_coordinateOpenCap_zero :
    IsOpen (coordinateOpenCap 0) := by
  rw [show coordinateOpenCap 0 =
      (fun x : Sphere 4 ↦ x.1 3) ⁻¹' Set.Iio 0 by
    ext x
    simp]
  exact isOpen_Iio.preimage (by fun_prop)

private theorem isOpen_coordinateOpenCap_one :
    IsOpen (coordinateOpenCap 1) := by
  rw [show coordinateOpenCap 1 =
      (fun x : Sphere 4 ↦ x.1 3) ⁻¹' Set.Ioi 0 by
    ext x
    simp]
  exact isOpen_Ioi.preimage (by fun_prop)

private theorem disjoint_coordinateOpenCaps :
    Disjoint (coordinateOpenCap 0) (coordinateOpenCap 1) := by
  rw [Set.disjoint_left]
  intro x hx0 hx1
  rw [mem_coordinateOpenCap_zero] at hx0
  rw [mem_coordinateOpenCap_one] at hx1
  linarith

private theorem selectedLeft_subset_cap_union
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a ⊆
      capOrientationBaseProj m ⁻¹'
        (coordinateOpenCap 0 ∪ coordinateOpenCap 1) := by
  intro z hz
  have hzGlobalLeft :
      z ∈ coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam m := by
    rw [coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam_eq_iUnion_equatorLeftSide]
    exact mem_iUnion.mpr ⟨a, hz⟩
  have hzNotSeam :
      z ∉ coordinateUnlinkExteriorPlanarFullCoverGlobalSeam m := by
    have hzCompl : z ∈
        (coordinateUnlinkExteriorPlanarFullCoverGlobalSeam m)ᶜ := by
      rw [← union_coordinateUnlinkExteriorPlanarFullCoverGlobalOffSeam]
      exact Or.inl hzGlobalLeft
    exact hzCompl
  have hbaseNotEquator :
      capOrientationBaseProj m z ∉ coordinateEquator := by
    intro hbase
    apply hzNotSeam
    rw [coordinateUnlinkExteriorPlanarFullCoverGlobalSeam_eq_preimage_coordinateEquator]
    exact hbase
  change capOrientationBaseProj m z ∈
    coordinateOpenCap 0 ∪ coordinateOpenCap 1
  rw [← compl_coordinateEquator_eq_union_openCaps]
  exact hbaseNotEquator

private theorem selectedLeft_subset_cap_zero
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a ⊆
      capOrientationBaseProj m ⁻¹' coordinateOpenCap 0 := by
  have hsplit := IsPreconnected.subset_or_subset
    (isOpen_coordinateOpenCap_zero.preimage
      (continuous_capOrientationBaseProj m))
    (isOpen_coordinateOpenCap_one.preimage
      (continuous_capOrientationBaseProj m))
    (disjoint_coordinateOpenCaps.preimage (capOrientationBaseProj m))
    (selectedLeft_subset_cap_union m a)
    (isPreconnected_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a)
  rcases hsplit with hzero | hone
  · exact hzero
  · exfalso
    have hselected := capOrientationLeftFullCoverPoint_mem_selected m a
    have hzero := capOrientationLeftFullCoverPoint_mem_cap_zero m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)
    have hone' := hone hselected
    exact (disjoint_coordinateOpenCaps.le_bot ⟨hzero, hone'⟩)

private theorem globalLeft_subset_cap_zero
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam m ⊆
      capOrientationBaseProj m ⁻¹' coordinateOpenCap 0 := by
  rw [coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam_eq_iUnion_equatorLeftSide]
  exact iUnion_subset fun a ↦ selectedLeft_subset_cap_zero m a

private theorem cap_one_subset_globalRight
    (m : ℕ) [NeZero m] :
    capOrientationBaseProj m ⁻¹' coordinateOpenCap 1 ⊆
      coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam m := by
  intro z hzCapOne
  have hzNotSeam :
      z ∉ coordinateUnlinkExteriorPlanarFullCoverGlobalSeam m := by
    rw [coordinateUnlinkExteriorPlanarFullCoverGlobalSeam_eq_preimage_coordinateEquator]
    exact coordinateOpenCap_subset_compl_coordinateEquator 1 hzCapOne
  have hzSides :
      z ∈ coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam m ∪
        coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam m := by
    rw [union_coordinateUnlinkExteriorPlanarFullCoverGlobalOffSeam]
    exact hzNotSeam
  rcases hzSides with hzLeft | hzRight
  · have hzCapZero := globalLeft_subset_cap_zero m hzLeft
    exact (disjoint_coordinateOpenCaps.le_bot ⟨hzCapZero, hzCapOne⟩).elim
  · exact hzRight

private abbrev capOrientationStarStrictGlobalRight
    (m : ℕ) [NeZero m] : Set (CoordinateUnlinkExteriorPlanarNeckStar m) :=
  coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
    coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m

private theorem capOrientation_inr_mem_globalRight_iff
    (m : ℕ) [NeZero m]
    (y : CoordinateUnlinkExteriorPlanarNeckRightComplement m) :
    topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m) y ∈
        coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m ↔
      y ∉ range (coordinateUnlinkExteriorPlanarNeckStarToRight m) := by
  let f := coordinateUnlinkExteriorPlanarNeckStarToLeft m
  let g := coordinateUnlinkExteriorPlanarNeckStarToRight m
  change topologicalPushoutInr f g y ∈
      topologicalPushoutInrOffSeam f g ↔ y ∉ range g
  constructor
  · rintro ⟨y', hy', hEq⟩
    have hyy : y' = y :=
      topologicalPushoutInr_injective f g
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m).injective
        hEq
    simpa [hyy] using hy'
  · intro hy
    exact ⟨y, hy, rfl⟩

private theorem capOrientation_rightGridPoint_mem_globalRight_iff
    (m : ℕ) [NeZero m]
    (q : (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalRight) :
    coordinateUnlinkExteriorPlanarNeckStarRightGridPoint m q ∈
        coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m ↔
      coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m q ∉
        range (coordinateUnlinkExteriorPlanarNeckStarToRight m) :=
  capOrientation_inr_mem_globalRight_iff m _

private theorem capOrientation_rightTopPoint_mem_globalRight_iff
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridRightOuter m)
    (b c : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarNeckStarRightTopPoint m x b ∈
        coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m ↔
      coordinateUnlinkExteriorPlanarNeckStarRightTopPoint m x c ∈
        coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m := by
  simp only [coordinateUnlinkExteriorPlanarNeckStarRightTopPoint]
  rw [capOrientation_rightGridPoint_mem_globalRight_iff,
    capOrientation_rightGridPoint_mem_globalRight_iff]
  constructor
  · intro hb hc
    apply hb
    obtain ⟨⟨a, s⟩, has⟩ := hc
    have hc' :
        coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m
          (topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight
            (x, c)) ∈
          range (fun s : Sphere 3 ↦
            coordinateUnlinkExteriorPlanarNeckStarToRight m (a, s)) :=
      ⟨s, has⟩
    rw [coordinateUnlinkExteriorPlanarNeckStarRightTopPoint_mem_attachingRange_iff]
      at hc'
    have hb' :
        coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m
          (topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight
            (x, b)) ∈
          range (fun s : Sphere 3 ↦
            coordinateUnlinkExteriorPlanarNeckStarToRight m (a, s)) := by
      rw [coordinateUnlinkExteriorPlanarNeckStarRightTopPoint_mem_attachingRange_iff]
      exact hc'
    obtain ⟨s', hs'⟩ := hb'
    exact ⟨(a, s'), hs'⟩
  · intro hc hb
    apply hc
    obtain ⟨⟨a, s⟩, has⟩ := hb
    have hb' :
        coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m
          (topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight
            (x, b)) ∈
          range (fun s : Sphere 3 ↦
            coordinateUnlinkExteriorPlanarNeckStarToRight m (a, s)) :=
      ⟨s, has⟩
    rw [coordinateUnlinkExteriorPlanarNeckStarRightTopPoint_mem_attachingRange_iff]
      at hb'
    have hc' :
        coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m
          (topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight
            (x, c)) ∈
          range (fun s : Sphere 3 ↦
            coordinateUnlinkExteriorPlanarNeckStarToRight m (a, s)) := by
      rw [coordinateUnlinkExteriorPlanarNeckStarRightTopPoint_mem_attachingRange_iff]
      exact hb'
    obtain ⟨s', hs'⟩ := hc'
    exact ⟨(a, s'), hs'⟩

private theorem capOrientation_rightBottomPoint_mem_globalRight_of_lt_one
    (m : ℕ) [NeZero m] (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) (ht : (t : ℝ) < 1) :
    coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint m u t s ∈
      coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m := by
  rw [coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint_eq_normalized,
    coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint_eq_grid]
  apply (capOrientation_inr_mem_globalRight_iff m _).mpr
  exact coordinateUnlinkExteriorPlanarNeckGrid_bottomRight_complement_not_mem_range
    m u t s ht

private theorem capOrientation_rightInteriorCarrier_subset
    (m : ℕ) [NeZero m] :
    range (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m) ⊆
      capOrientationStarStrictGlobalRight m := by
  rintro _ ⟨⟨u, t, s⟩, rfl⟩
  constructor
  · rw [coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier]
    exact (coordinateUnlinkExteriorPlanarNeckStar_normalizedRight_mem_strictCore_iff
      m u (coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed t) s).mpr t.2.1
  · change coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint m u
      (coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed t) s ∈ _
    rw [← coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint_eq_normalized]
    exact capOrientation_rightBottomPoint_mem_globalRight_of_lt_one m u
      (coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed t) s t.2.2

private def capOrientationRightHalfTime : Set.Icc (0 : ℝ) 1 :=
  ⟨1 / 2, by norm_num, by norm_num⟩

private def capOrientationRightOpenHalfTime : Set.Ioo (0 : ℝ) 1 :=
  ⟨1 / 2, by norm_num, by norm_num⟩

private def capOrientationRightTimeDescent
    (t : Set.Icc (0 : ℝ) 1) (r : I) : Set.Icc (0 : ℝ) 1 :=
  ⟨(1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) * (1 / 2), by
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr r.2.2) t.2.1)
        (mul_nonneg r.2.1 (by norm_num)),
    by
      have hfirst : (1 - (r : ℝ)) * (t : ℝ) ≤ 1 - (r : ℝ) :=
        by simpa using (mul_le_mul_of_nonneg_left t.2.2
          (sub_nonneg.mpr r.2.2))
      have hsecond : (r : ℝ) * (1 / 2) ≤ (r : ℝ) :=
        mul_le_of_le_one_right r.2.1 (by norm_num)
      linarith⟩

private theorem continuous_capOrientationRightTimeDescent
    (t : Set.Icc (0 : ℝ) 1) :
    Continuous (capOrientationRightTimeDescent t) := by
  apply Continuous.subtype_mk
  fun_prop

@[simp] private theorem capOrientationRightTimeDescent_zero
    (t : Set.Icc (0 : ℝ) 1) :
    capOrientationRightTimeDescent t 0 = t := by
  apply Subtype.ext
  simp [capOrientationRightTimeDescent]

@[simp] private theorem capOrientationRightTimeDescent_one
    (t : Set.Icc (0 : ℝ) 1) :
    capOrientationRightTimeDescent t 1 = capOrientationRightHalfTime := by
  apply Subtype.ext
  norm_num [capOrientationRightTimeDescent, capOrientationRightHalfTime]

private theorem capOrientationRightTimeDescent_pos
    (t : Set.Icc (0 : ℝ) 1) (ht : 0 < (t : ℝ)) (r : I) :
    0 < (capOrientationRightTimeDescent t r : ℝ) := by
  change 0 < (1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) * (1 / 2)
  have hfirst : 0 ≤ (1 - (r : ℝ)) * (t : ℝ) :=
    mul_nonneg (sub_nonneg.mpr r.2.2) ht.le
  by_cases hr : (r : ℝ) = 0
  · rw [hr]
    simpa using ht
  · have hrpos : 0 < (r : ℝ) := lt_of_le_of_ne r.2.1 (Ne.symm hr)
    exact add_pos_of_nonneg_of_pos hfirst (mul_pos hrpos (by norm_num))

private theorem capOrientationRightTimeDescent_lt_one_of_ne_zero
    (t : Set.Icc (0 : ℝ) 1) (r : I) (hr : r ≠ 0) :
    (capOrientationRightTimeDescent t r : ℝ) < 1 := by
  change (1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) * (1 / 2) < 1
  have hrval : (r : ℝ) ≠ 0 := fun h ↦ hr (Subtype.ext h)
  have hrpos : 0 < (r : ℝ) := lt_of_le_of_ne r.2.1 (Ne.symm hrval)
  have hfirst : (1 - (r : ℝ)) * (t : ℝ) ≤ 1 - (r : ℝ) :=
    by simpa using (mul_le_mul_of_nonneg_left t.2.2
      (sub_nonneg.mpr r.2.2))
  nlinarith

private def capOrientationRightTimePath
    (t : Set.Icc (0 : ℝ) 1) : Path t capOrientationRightHalfTime where
  toFun := capOrientationRightTimeDescent t
  continuous_toFun := continuous_capOrientationRightTimeDescent t
  source' := capOrientationRightTimeDescent_zero t
  target' := capOrientationRightTimeDescent_one t

private def capOrientationRightClosedAnnulusCurve
    (m : ℕ) [NeZero m] (u : Sphere 1) (s : Sphere 2) :
    C(Set.Icc (0 : ℝ) 1, CoordinateUnlinkExteriorPlanarNeckStar m) where
  toFun t := coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint m u t s
  continuous_toFun := by
    have hx : Continuous (fun t : Set.Icc (0 : ℝ) 1 ↦ ((u, t), s)) :=
      (continuous_const.prodMk continuous_id).prodMk continuous_const
    have hp :=
      (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight).continuous.comp hx
    have hh :=
      (coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m).continuous.comp hp
    exact
      (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)).continuous.comp hh

private theorem capOrientation_rightBottomPoint_joinedIn_carrier
    (m : ℕ) [NeZero m] (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) (ht : 0 < (t : ℝ))
    (hy : coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint m u t s ∈
      capOrientationStarStrictGlobalRight m) :
    ∃ z ∈ range (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m),
      JoinedIn (capOrientationStarStrictGlobalRight m)
        (coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint m u t s) z := by
  let P := capOrientationRightTimePath t
  let C := capOrientationRightClosedAnnulusCurve m u s
  have htime : JoinedIn (range (P : I → Set.Icc (0 : ℝ) 1)) t
      capOrientationRightHalfTime := ⟨P, fun r ↦ ⟨r, rfl⟩⟩
  have hmapped := htime.map C.continuous
  have hsubset : C '' range (P : I → Set.Icc (0 : ℝ) 1) ⊆
      capOrientationStarStrictGlobalRight m := by
    rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
    constructor
    · apply (coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint_mem_strictCore_iff
        m u (capOrientationRightTimeDescent t r) s).mpr
      exact capOrientationRightTimeDescent_pos t ht r
    · by_cases hr : r = 0
      · subst r
        change C (capOrientationRightTimeDescent t 0) ∈
          coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m
        rw [capOrientationRightTimeDescent_zero]
        change coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint m u t s ∈
          coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m
        exact hy.2
      · exact capOrientation_rightBottomPoint_mem_globalRight_of_lt_one m u
          (capOrientationRightTimeDescent t r) s
          (capOrientationRightTimeDescent_lt_one_of_ne_zero t r hr)
  have hjoined := hmapped.mono hsubset
  refine ⟨C capOrientationRightHalfTime, ?_, hjoined⟩
  refine ⟨(u, (capOrientationRightOpenHalfTime, s)), ?_⟩
  change coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint m u
      (coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed
        capOrientationRightOpenHalfTime) s =
    coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint m u
      capOrientationRightHalfTime s
  rw [coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint_eq_normalized]
  congr 1

private def capOrientationRightTopBallCurve
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridRightOuter m) :
    C(EuclideanClosedBall 3, CoordinateUnlinkExteriorPlanarNeckStar m) where
  toFun b := coordinateUnlinkExteriorPlanarNeckStarRightTopPoint m x b
  continuous_toFun := by
    have hx : Continuous (fun b : EuclideanClosedBall 3 ↦ (x, b)) :=
      continuous_const.prodMk continuous_id
    have hp :=
      (topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight).continuous.comp hx
    have hh :=
      (coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m).continuous.comp hp
    exact
      (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)).continuous.comp hh

private theorem capOrientation_rightTopPoint_joinedIn_carrier
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridRightOuter m)
    (b : EuclideanClosedBall 3) (s : Sphere 2)
    (hy : coordinateUnlinkExteriorPlanarNeckStarRightTopPoint m x b ∈
      capOrientationStarStrictGlobalRight m) :
    ∃ z ∈ range (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m),
      JoinedIn (capOrientationStarStrictGlobalRight m)
        (coordinateUnlinkExteriorPlanarNeckStarRightTopPoint m x b) z := by
  let C := capOrientationRightTopBallCurve m x
  have hball : JoinedIn (univ : Set (EuclideanClosedBall 3)) b
      (coordinateUnlinkExteriorPlanarNeckGridSphereToBall s) :=
    (isPathConnected_euclideanClosedBall 3).joinedIn _ (mem_univ _) _ (mem_univ _)
  have hmapped := hball.map C.continuous
  have hsubset : C '' (univ : Set (EuclideanClosedBall 3)) ⊆
      capOrientationStarStrictGlobalRight m := by
    rintro _ ⟨c, _hc, rfl⟩
    constructor
    · exact coordinateUnlinkExteriorPlanarNeckStarRightTopPoint_mem_strictCore m x c
    · exact (capOrientation_rightTopPoint_mem_globalRight_iff m x b c).mp hy.2
  have htoBoundary := hmapped.mono hsubset
  change JoinedIn (capOrientationStarStrictGlobalRight m)
      (coordinateUnlinkExteriorPlanarNeckStarRightTopPoint m x b)
      (coordinateUnlinkExteriorPlanarNeckStarRightTopPoint m x
        (coordinateUnlinkExteriorPlanarNeckGridSphereToBall s)) at htoBoundary
  rw [coordinateUnlinkExteriorPlanarNeckStarRightTopPoint_sphere_eq_bottom_one]
    at htoBoundary
  obtain ⟨z, hz, hfromBoundary⟩ :=
    capOrientation_rightBottomPoint_joinedIn_carrier m
      (coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m x) 1 s
      (by norm_num) htoBoundary.target_mem
  exact ⟨z, hz, htoBoundary.trans hfromBoundary⟩

private theorem capOrientation_rightGridPoint_joinedIn_carrier
    (m : ℕ) [NeZero m]
    (q : (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalRight)
    (hq : coordinateUnlinkExteriorPlanarNeckStarRightGridPoint m q ∈
      capOrientationStarStrictGlobalRight m) :
    ∃ z ∈ range (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m),
      JoinedIn (capOrientationStarStrictGlobalRight m)
        (coordinateUnlinkExteriorPlanarNeckStarRightGridPoint m q) z := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  rcases topologicalPushout_jointly_surjective
      D.rightToTopRight D.rightToBottomRight q with
    ⟨x, hx⟩ | ⟨x, hx⟩
  · rw [← hx] at hq ⊢
    obtain ⟨s, _hs⟩ := isPathConnected_sphereTwo.nonempty
    exact capOrientation_rightTopPoint_joinedIn_carrier m x.1 x.2 s hq
  · rw [← hx] at hq ⊢
    have ht : 0 < (x.1.2 : ℝ) :=
      (coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint_mem_strictCore_iff
        m x.1.1 x.1.2 x.2).mp hq.1
    exact capOrientation_rightBottomPoint_joinedIn_carrier
      m x.1.1 x.1.2 x.2 ht hq

private theorem capOrientation_rightCoprojection_joinedIn_carrier
    (m : ℕ) [NeZero m]
    (y : CoordinateUnlinkExteriorPlanarNeckRightComplement m)
    (hy : topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m) y ∈
      capOrientationStarStrictGlobalRight m) :
    ∃ z ∈ range (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m),
      JoinedIn (capOrientationStarStrictGlobalRight m)
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
          (coordinateUnlinkExteriorPlanarNeckStarToRight m) y) z := by
  let H := coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m
  let q := H.symm y
  have hpoint : coordinateUnlinkExteriorPlanarNeckStarRightGridPoint m q =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m) y := by
    change topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m) (H q) = _
    rw [H.apply_symm_apply]
  have hq : coordinateUnlinkExteriorPlanarNeckStarRightGridPoint m q ∈
      capOrientationStarStrictGlobalRight m := by
    rw [hpoint]
    exact hy
  obtain ⟨z, hz, hj⟩ := capOrientation_rightGridPoint_joinedIn_carrier m q hq
  exact ⟨z, hz, hpoint ▸ hj⟩

private theorem isPathConnected_capOrientationStarStrictGlobalRight
    (m : ℕ) [NeZero m] :
    IsPathConnected (capOrientationStarStrictGlobalRight m) := by
  obtain ⟨x, hx⟩ :=
    (isPathConnected_range_coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier
      m).nonempty
  rcases hx with ⟨u, rfl⟩
  refine ⟨coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m u,
    capOrientation_rightInteriorCarrier_subset m ⟨u, rfl⟩, ?_⟩
  intro y hy
  change y ∈ coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
    topologicalPushoutInrOffSeam
      (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
      (coordinateUnlinkExteriorPlanarNeckStarToRight m) at hy
  rcases hy.2 with ⟨r, hr, hry⟩
  have hyr : topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m) r ∈
      capOrientationStarStrictGlobalRight m := by
    rw [hry]
    exact hy
  obtain ⟨z, hz, hyz⟩ :=
    capOrientation_rightCoprojection_joinedIn_carrier m r hyr
  have huz :=
    (isPathConnected_range_coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier
      m).joinedIn _ ⟨u, rfl⟩ _ hz |>.mono
        (capOrientation_rightInteriorCarrier_subset m)
  rw [hry] at hyz
  exact huz.trans hyz.symm

/-- The global strict right side in the full unlink power cover is path connected. -/
theorem isPathConnected_coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam
    (m : ℕ) [NeZero m] :
    IsPathConnected
      (coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam m) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  let E := coordinateUnlinkExteriorPlanarFullCoverPreimageHomeomorphRangeInter m
    (coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m)
  have htarget : IsPathConnected
      (range (coordinateUnlinkExteriorPlanarFullCoverToNeckStar m) ∩
        coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m) := by
    rw [range_coordinateUnlinkExteriorPlanarFullCoverToNeckStar]
    exact isPathConnected_capOrientationStarStrictGlobalRight m
  let _ : PathConnectedSpace
      (↑(range (coordinateUnlinkExteriorPlanarFullCoverToNeckStar m) ∩
        coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m)) :=
    isPathConnected_iff_pathConnectedSpace.mp htarget
  exact E.symm.surjective.pathConnectedSpace E.symm.continuous

/-- The global strict right side in the full unlink power cover is preconnected. -/
theorem isPreconnected_coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam
    (m : ℕ) [NeZero m] :
    IsPreconnected
      (coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam m) :=
  (isPathConnected_coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam
    m).isConnected.isPreconnected

private theorem globalRight_subset_cap_union
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam m ⊆
      capOrientationBaseProj m ⁻¹'
        (coordinateOpenCap 0 ∪ coordinateOpenCap 1) := by
  intro z hzRight
  have hzNotSeam :
      z ∉ coordinateUnlinkExteriorPlanarFullCoverGlobalSeam m := by
    have hzCompl : z ∈
        (coordinateUnlinkExteriorPlanarFullCoverGlobalSeam m)ᶜ := by
      rw [← union_coordinateUnlinkExteriorPlanarFullCoverGlobalOffSeam]
      exact Or.inr hzRight
    exact hzCompl
  have hbaseNotEquator : capOrientationBaseProj m z ∉ coordinateEquator := by
    intro hbase
    apply hzNotSeam
    rw [coordinateUnlinkExteriorPlanarFullCoverGlobalSeam_eq_preimage_coordinateEquator]
    exact hbase
  change capOrientationBaseProj m z ∈
    coordinateOpenCap 0 ∪ coordinateOpenCap 1
  rw [← compl_coordinateEquator_eq_union_openCaps]
  exact hbaseNotEquator

private theorem globalRight_subset_cap_one
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam m ⊆
      capOrientationBaseProj m ⁻¹' coordinateOpenCap 1 := by
  have hsplit := IsPreconnected.subset_or_subset
    (isOpen_coordinateOpenCap_zero.preimage
      (continuous_capOrientationBaseProj m))
    (isOpen_coordinateOpenCap_one.preimage
      (continuous_capOrientationBaseProj m))
    (disjoint_coordinateOpenCaps.preimage (capOrientationBaseProj m))
    (globalRight_subset_cap_union m)
    (isPreconnected_coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam m)
  rcases hsplit with hzero | hone
  · exfalso
    let x : Sphere 3 := ⟨Classical.choose
        (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin 4))
          (x := 0) (r := 1) |>.2 (by norm_num)),
      Classical.choose_spec
        (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin 4))
          (x := 0) (r := 1) |>.2 (by norm_num))⟩
    let t : EquatorCollarInterval :=
      ⟨1 / 4, by constructor <;> norm_num⟩
    let z := equatorUnlinkPowerCollarLift m 0 (x, t)
    have hzCapOne : capOrientationBaseProj m z ∈ coordinateOpenCap 1 := by
      rw [mem_coordinateOpenCap_one]
      change 0 < (equatorCollarSphereMap (x, t)).1 3
      rw [equatorCollarSphereMap_coord_three]
      norm_num [t]
    have hzRight := cap_one_subset_globalRight m hzCapOne
    have hzCapZero := hzero hzRight
    exact (disjoint_coordinateOpenCaps.le_bot ⟨hzCapZero, hzCapOne⟩).elim
  · exact hone

/-- The global strict right side is exactly the inverse image of the positive coordinate cap. -/
theorem coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam_eq_preimage_coordinateOpenCap_one
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam m =
      (fun z : StandardUnlinkPowerPullback m ↦
        (standardUnlinkPowerPullbackProj m z : Sphere 4)) ⁻¹'
          coordinateOpenCap 1 := by
  apply Subset.antisymm
  · exact globalRight_subset_cap_one m
  · exact cap_one_subset_globalRight m

private theorem cap_zero_subset_globalLeft
    (m : ℕ) [NeZero m] :
    capOrientationBaseProj m ⁻¹' coordinateOpenCap 0 ⊆
      coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam m := by
  intro z hzCapZero
  have hzNotSeam :
      z ∉ coordinateUnlinkExteriorPlanarFullCoverGlobalSeam m := by
    rw [coordinateUnlinkExteriorPlanarFullCoverGlobalSeam_eq_preimage_coordinateEquator]
    exact coordinateOpenCap_subset_compl_coordinateEquator 0 hzCapZero
  have hzSides :
      z ∈ coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam m ∪
        coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam m := by
    rw [union_coordinateUnlinkExteriorPlanarFullCoverGlobalOffSeam]
    exact hzNotSeam
  rcases hzSides with hzLeft | hzRight
  · exact hzLeft
  · have hzCapOne := globalRight_subset_cap_one m hzRight
    exact (disjoint_coordinateOpenCaps.le_bot ⟨hzCapZero, hzCapOne⟩).elim

/-- The global strict left side is exactly the inverse image of the negative coordinate cap. -/
theorem coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam_eq_preimage_coordinateOpenCap_zero
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam m =
      (fun z : StandardUnlinkPowerPullback m ↦
        (standardUnlinkPowerPullbackProj m z : Sphere 4)) ⁻¹'
          coordinateOpenCap 0 := by
  apply Subset.antisymm
  · exact globalLeft_subset_cap_zero m
  · exact cap_zero_subset_globalLeft m

end SplittingSpheres

end
