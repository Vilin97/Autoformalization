/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkComplementExteriorPowerHomeomorph
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckEquatorComparison
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckStarFiberSeparation

/-!
# Separation by a coordinate equator in the full unlink power cover

This file transports the labelled fiber separation of the literal planar neck star through
the strict part of the compact coordinate exterior and the corrected full-cover exterior
homeomorphism.  The star label corresponding to the explicit equator lift labelled `a` is
`a + coordinateUnlinkExteriorPlanarSmoothNeckShift m`.

The two displayed sides are open, disjoint, and cover the complement of the selected equator
lift.  Explicit normalized-annulus points at time `1 / 2` show that both sides survive the
restriction from the compact exterior to its strict core.  Consequently the complement is not
preconnected.  No connectedness assertion for either side, component count, manifold
recognition, or smoothness assertion for the star model is made.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open Set.Notation
open scoped unitInterval

namespace SplittingSpheres

/-! ## Transport from the full cover to the neck star -/

/-- The corrected full-cover homeomorphism onto the strict open core of the compact pullback. -/
def coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph
    (m : ℕ) [NeZero m] :
    StandardUnlinkPowerPullback m ≃ₜ
      CoordinateUnlinkExteriorEighthPowerPullbackStrict m :=
  (standardUnlinkPowerPullbackExteriorHomeomorph m).trans
    (standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictHomeomorph m)

/-- Forget the strict-core proof and transport through the flower model to the literal star. -/
def coordinateUnlinkExteriorPlanarFullCoverToNeckStar
    (m : ℕ) [NeZero m] :
    C(StandardUnlinkPowerPullback m,
      CoordinateUnlinkExteriorPlanarNeckStar m) where
  toFun z :=
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
      ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm
        (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m z).1)
  continuous_toFun :=
    (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m).continuous.comp
      ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm.continuous.comp
        (continuous_subtype_val.comp
          (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).continuous))

private def coordinateUnlinkExteriorPlanarClosedNeckSphereMap
    (m : ℕ) [NeZero m] (a : ZMod m) (s : Sphere 3) :
    CoordinateUnlinkExteriorEighthPowerPullback m :=
  coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
    (coordinateUnlinkExteriorPlanarNeckSphereMap m a s)

private theorem coordinateUnlinkExteriorPlanarFullCoverStrict_coe
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m z).1 =
      standardUnlinkPowerPullbackToCoordinateExteriorStrict m z :=
  rfl

private theorem injective_coordinateUnlinkExteriorPlanarFullCoverStrict_coe
    (m : ℕ) [NeZero m] :
    Injective (standardUnlinkPowerPullbackToCoordinateExteriorStrict m) :=
  injective_standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior m |>.comp
    (standardUnlinkPowerPullbackExteriorHomeomorph m).injective

private theorem coordinateUnlinkExteriorEighthPowerPullbackToComplement_fullCoverStrict_equator
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    coordinateUnlinkExteriorEighthPowerPullbackToComplement m
        (standardUnlinkPowerPullbackToCoordinateExteriorStrict m
          (equatorUnlinkPowerLift m a x)) =
      equatorUnlinkPowerLift m a x := by
  rw [standardUnlinkPowerPullbackToCoordinateExteriorStrict_equatorUnlinkPowerLift]
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    exact equatorUnlinkClosedTubeExteriorPowerLift_powerCoordinate m a x

private theorem range_coordinateUnlinkExteriorPlanarClosedNeckSphereMap_eq_image_equator
    (m : ℕ) [NeZero m] (a : ZMod m) :
    range (coordinateUnlinkExteriorPlanarClosedNeckSphereMap m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)) =
      standardUnlinkPowerPullbackToCoordinateExteriorStrict m ''
        range (equatorUnlinkPowerLift m a) := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    have hs : coordinateUnlinkExteriorEighthPowerPullbackToComplement m
          (coordinateUnlinkExteriorPlanarClosedNeckSphereMap m
            (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) s) ∈
        range (equatorUnlinkPowerLift m a) := by
      rw [← range_transportedNeckSphereMap_eq_equatorPowerLift m a]
      exact ⟨s, rfl⟩
    obtain ⟨x, hx⟩ := hs
    refine ⟨equatorUnlinkPowerLift m a x, ⟨x, rfl⟩, ?_⟩
    apply coordinateUnlinkExteriorEighthPowerPullbackToComplement_injective m
    rw [coordinateUnlinkExteriorEighthPowerPullbackToComplement_fullCoverStrict_equator]
    exact hx
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    have hx : equatorUnlinkPowerLift m a x ∈
        range (coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m
          (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)) := by
      rw [range_transportedNeckSphereMap_eq_equatorPowerLift m a]
      exact ⟨x, rfl⟩
    obtain ⟨s, hs⟩ := hx
    refine ⟨s, ?_⟩
    apply coordinateUnlinkExteriorEighthPowerPullbackToComplement_injective m
    rw [coordinateUnlinkExteriorEighthPowerPullbackToComplement_fullCoverStrict_equator]
    exact hs

/-! ## The selected seam and its two sides -/

/-- The side corresponding to the selected labelled left leaf of the strict neck star. -/
def coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Set (StandardUnlinkPowerPullback m) :=
  coordinateUnlinkExteriorPlanarFullCoverToNeckStar m ⁻¹'
    coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)

/-- The remainder side of the complement of the selected lifted equator. -/
def coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Set (StandardUnlinkPowerPullback m) :=
  coordinateUnlinkExteriorPlanarFullCoverToNeckStar m ⁻¹'
    coordinateUnlinkExteriorPlanarNeckStarFiberRest m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)

private theorem preimage_coordinateUnlinkExteriorPlanarNeckStarFiberSeam_fullCover
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFullCoverToNeckStar m ⁻¹'
        coordinateUnlinkExteriorPlanarNeckStarFiberSeam m
          (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) =
      range (equatorUnlinkPowerLift m a) := by
  ext z
  constructor
  · rintro ⟨s, hs⟩
    have hclosed : coordinateUnlinkExteriorPlanarClosedNeckSphereMap m
          (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) s =
        standardUnlinkPowerPullbackToCoordinateExteriorStrict m z := by
      have hsource : coordinateUnlinkExteriorPlanarNeckSphereMap m
            (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) s =
          (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm
            (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m z).1 := by
        apply
          (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m).injective
        calc
          coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
                (coordinateUnlinkExteriorPlanarNeckSphereMap m
                  (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) s) =
              topologicalPushoutInl
                (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
                (coordinateUnlinkExteriorPlanarNeckStarToRight m)
                (coordinateUnlinkExteriorPlanarNeckStarToLeft m
                  (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m, s)) :=
            coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar_neckSphereFamily
              m (_ , s)
          _ = coordinateUnlinkExteriorPlanarFullCoverToNeckStar m z := hs
          _ = coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
                ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm
                  (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m z).1) := rfl
      rw [coordinateUnlinkExteriorPlanarClosedNeckSphereMap,
        ← coordinateUnlinkExteriorPlanarFullCoverStrict_coe, hsource,
        (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).apply_symm_apply]
    have hrange : standardUnlinkPowerPullbackToCoordinateExteriorStrict m z ∈
        range (coordinateUnlinkExteriorPlanarClosedNeckSphereMap m
          (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)) :=
      ⟨s, hclosed⟩
    rw [range_coordinateUnlinkExteriorPlanarClosedNeckSphereMap_eq_image_equator] at hrange
    obtain ⟨y, hy, hzy⟩ := hrange
    obtain ⟨x, rfl⟩ := hy
    refine ⟨x, ?_⟩
    exact injective_coordinateUnlinkExteriorPlanarFullCoverStrict_coe m hzy
  · rintro ⟨x, rfl⟩
    have hrange : standardUnlinkPowerPullbackToCoordinateExteriorStrict m
          (equatorUnlinkPowerLift m a x) ∈
        range (coordinateUnlinkExteriorPlanarClosedNeckSphereMap m
          (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)) := by
      rw [range_coordinateUnlinkExteriorPlanarClosedNeckSphereMap_eq_image_equator]
      exact ⟨equatorUnlinkPowerLift m a x, ⟨x, rfl⟩, rfl⟩
    obtain ⟨s, hs⟩ := hrange
    refine ⟨s, ?_⟩
    have hs' : coordinateUnlinkExteriorPlanarClosedNeckSphereMap m
          (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) s =
        (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m
          (equatorUnlinkPowerLift m a x)).1 := by
      rw [coordinateUnlinkExteriorPlanarFullCoverStrict_coe]
      exact hs
    change (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
          (coordinateUnlinkExteriorPlanarNeckStarToRight m)
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m
            (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m, s))) =
      coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
        ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm
          (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m
            (equatorUnlinkPowerLift m a x)).1)
    rw [← hs', coordinateUnlinkExteriorPlanarClosedNeckSphereMap,
      (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm_apply_apply]
    exact (
      coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar_neckSphereFamily
        m (_, s)).symm

theorem isOpen_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsOpen (coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a) :=
  (isOpen_coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)).preimage
    (coordinateUnlinkExteriorPlanarFullCoverToNeckStar m).continuous

theorem isOpen_coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsOpen (coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a) :=
  (isOpen_coordinateUnlinkExteriorPlanarNeckStarFiberRest m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)).preimage
    (coordinateUnlinkExteriorPlanarFullCoverToNeckStar m).continuous

theorem disjoint_coordinateUnlinkExteriorPlanarFullCoverEquatorSides
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Disjoint (coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a)
      (coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a) :=
  (disjoint_coordinateUnlinkExteriorPlanarNeckStarFiberSides m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)).preimage
    (coordinateUnlinkExteriorPlanarFullCoverToNeckStar m)

theorem union_coordinateUnlinkExteriorPlanarFullCoverEquatorSides
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a ∪
        coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a =
      (range (equatorUnlinkPowerLift m a))ᶜ := by
  rw [coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide,
    coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide,
    ← preimage_union,
    union_coordinateUnlinkExteriorPlanarNeckStarFiberSides,
    preimage_compl,
    preimage_coordinateUnlinkExteriorPlanarNeckStarFiberSeam_fullCover]

/-! ## Strict planar points -/

private theorem coordinateUnlinkExteriorPlanarNeckTransport_planar_proj_closed
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

private theorem coordinateUnlinkExteriorPlanarNeckTransport_planar_norm_sub_center
    (m : ℕ) [NeZero m] (z : CoordinateUnlinkExteriorPlanarFlower m)
    (s : Sphere 2) (i : Fin 2) :
    ‖standardUnlinkNormalProjection
          ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (partialSphereSpinInr
              (coordinateUnlinkExteriorPlanarFlowerOuter m) (z, s))).1.1.1) -
        standardUnlinkNormalCenter i‖ =
      if i = 0 then ‖z.1.1 ^ m + 1‖ else ‖z.1.1 ^ m‖ := by
  change ‖standardUnlinkNormalProjection
        ((coordinateUnlinkExteriorEighthPowerPullbackProj m
          (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (partialSphereSpinInr
              (coordinateUnlinkExteriorPlanarFlowerOuter m) (z, s)))).1) -
      standardUnlinkNormalCenter i‖ = _
  rw [coordinateUnlinkExteriorPlanarNeckTransport_planar_proj_closed]
  change ‖standardUnlinkNormalProjection
      (unlinkAlignedCapSphereMap
        (coordinateUnlinkExteriorPuncturedCapProductHomeomorph.symm
          (coordinateUnlinkExteriorPlanarFlowerBase m z, s)).1) -
      standardUnlinkNormalCenter i‖ = _
  rw [standardUnlinkNormalProjection_unlinkAlignedCapSphereMap,
    ← sphereHandleRadius_smul_unlinkCapCoordinateCenter i,
    ← dist_eq_norm, dist_smul₀, Real.norm_eq_abs,
    abs_of_pos sphereHandleRadius_pos,
    coordinateUnlinkExteriorPuncturedCapProductHomeomorph_symm_fst_val]
  fin_cases i
  · simp only [Fin.zero_eta, ↓reduceIte]
    exact dist_planarFlowerBaseRaw_center_zero m z.1
  · simp only [Fin.mk_one, one_ne_zero, ↓reduceIte]
    exact dist_planarFlowerBaseRaw_center_one m z.1

private theorem coordinateUnlinkExteriorPlanarNeckTransport_planar_mem_strict
    (m : ℕ) [NeZero m] (z : CoordinateUnlinkExteriorPlanarFlower m)
    (s : Sphere 2)
    (hzero : (1 / 8 : ℝ) < ‖z.1.1 ^ m‖)
    (hone : (1 / 8 : ℝ) < ‖z.1.1 ^ m + 1‖) :
    (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarFlowerOuter m) (z, s))).1.1.1 ∈
      standardUnlinkClosedTubeExteriorOpens := by
  rw [mem_standardUnlinkClosedTubeExteriorOpens]
  intro i
  rw [coordinateUnlinkExteriorPlanarNeckTransport_planar_norm_sub_center]
  split_ifs with hi
  · exact hone
  · exact hzero

private def coordinateUnlinkExteriorPlanarInteriorHalfTime : Set.Icc (0 : ℝ) 1 :=
  ⟨1 / 2, by norm_num, by norm_num⟩

private def coordinateUnlinkExteriorPlanarFullCoverSeparationCirclePoint : Sphere 1 :=
  unlinkMeridianCirclePoint 0

private def coordinateUnlinkExteriorPlanarFullCoverSeparationSpherePoint : Sphere 2 :=
  coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint

private def coordinateUnlinkExteriorPlanarLeftInteriorFlowerPoint
    (m : ℕ) [NeZero m] (a : ZMod m) :
    CoordinateUnlinkExteriorPlanarFlower m :=
  coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion m
    (coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m
      (a, (coordinateUnlinkExteriorPlanarFullCoverSeparationCirclePoint,
        coordinateUnlinkExteriorPlanarInteriorHalfTime)))

private def coordinateUnlinkExteriorPlanarRightInteriorFlowerPoint
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarFlower m :=
  coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion m
    (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m
      (coordinateUnlinkExteriorPlanarFullCoverSeparationCirclePoint,
        coordinateUnlinkExteriorPlanarInteriorHalfTime))

private theorem coordinateUnlinkExteriorPlanarLeftInteriorFlowerPoint_pow
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (coordinateUnlinkExteriorPlanarLeftInteriorFlowerPoint m a).1.1 ^ m =
      (coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph
        (coordinateUnlinkExteriorPlanarFullCoverSeparationCirclePoint,
          coordinateUnlinkExteriorPlanarInteriorHalfTime) : ℂ) := by
  rw [coordinateUnlinkExteriorPlanarLeftInteriorFlowerPoint,
    coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion_apply,
    coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph_apply,
    coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization_apply,
    coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap_coe,
    coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw_pow]

private theorem coordinateUnlinkExteriorPlanarLeftInteriorFlowerPoint_pow_add_one_strict
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (1 / 8 : ℝ) <
      ‖(coordinateUnlinkExteriorPlanarLeftInteriorFlowerPoint m a).1.1 ^ m + 1‖ := by
  rw [coordinateUnlinkExteriorPlanarLeftInteriorFlowerPoint_pow,
    norm_coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_add_one]
  unfold directionalRadialAnnulusRadius
    coordinateUnlinkExteriorPlanarInteriorHalfTime
  have hgap := oneEighth_lt_coordinateUnlinkExteriorPlanarLeftOuterRadius
    (unlinkUnitCircleHomeomorph
      coordinateUnlinkExteriorPlanarFullCoverSeparationCirclePoint)
  norm_num at *
  linarith

private theorem coordinateUnlinkExteriorPlanarLeftInteriorFlowerPoint_pow_strict
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (1 / 8 : ℝ) <
      ‖(coordinateUnlinkExteriorPlanarLeftInteriorFlowerPoint m a).1.1 ^ m‖ := by
  rw [coordinateUnlinkExteriorPlanarLeftInteriorFlowerPoint_pow]
  let w := coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph
    (coordinateUnlinkExteriorPlanarFullCoverSeparationCirclePoint,
      coordinateUnlinkExteriorPlanarInteriorHalfTime)
  have hw := (mem_coordinateUnlinkExteriorPlanarBaseLeftHalfSet_iff w.1).mp w.2
  calc
    (1 / 8 : ℝ) < 1 / 2 := by norm_num
    _ ≤ |w.1.re| := by
      rw [abs_of_nonpos (by linarith [hw.2.2.2])]
      linarith [hw.2.2.2]
    _ ≤ ‖w.1‖ := Complex.abs_re_le_norm w.1

private theorem coordinateUnlinkExteriorPlanarRightInteriorFlowerPoint_pow_strict
    (m : ℕ) [NeZero m] :
    (1 / 8 : ℝ) <
      ‖(coordinateUnlinkExteriorPlanarRightInteriorFlowerPoint m).1.1 ^ m‖ := by
  rw [norm_pow, coordinateUnlinkExteriorPlanarRightInteriorFlowerPoint,
    coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion_apply,
    norm_coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_apply,
    ← coordinateUnlinkExteriorPlanarRightInnerRadius_pow m]
  apply pow_lt_pow_left₀
  · unfold directionalRadialAnnulusRadius
      coordinateUnlinkExteriorPlanarInteriorHalfTime
    have hgap := coordinateUnlinkExteriorPlanarRightInner_lt_outer m
      (unlinkUnitCircleHomeomorph
        coordinateUnlinkExteriorPlanarFullCoverSeparationCirclePoint)
    norm_num at *
    linarith
  · exact (coordinateUnlinkExteriorPlanarRightInnerRadius_pos m).le
  · exact NeZero.ne m

private theorem coordinateUnlinkExteriorPlanarRightInteriorFlowerPoint_pow_add_one_strict
    (m : ℕ) [NeZero m] :
    (1 / 8 : ℝ) <
      ‖(coordinateUnlinkExteriorPlanarRightInteriorFlowerPoint m).1.1 ^ m + 1‖ := by
  let w := coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m
    (coordinateUnlinkExteriorPlanarFullCoverSeparationCirclePoint,
      coordinateUnlinkExteriorPlanarInteriorHalfTime)
  have hw : (-1 / 2 : ℝ) ≤ (w.1.1.1 ^ m).re := w.2
  change (1 / 8 : ℝ) < ‖w.1.1.1 ^ m + 1‖
  calc
    (1 / 8 : ℝ) < 1 / 2 := by norm_num
    _ ≤ |(w.1.1.1 ^ m + 1).re| := by
      rw [Complex.add_re, Complex.one_re, abs_of_nonneg (by linarith)]
      linarith
    _ ≤ ‖w.1.1.1 ^ m + 1‖ := Complex.abs_re_le_norm _

private def coordinateUnlinkExteriorPlanarLeftInteriorFlowerSpinPoint
    (m : ℕ) [NeZero m] (a : ZMod m) :
    CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m :=
  partialSphereSpinInr (coordinateUnlinkExteriorPlanarFlowerOuter m)
    (coordinateUnlinkExteriorPlanarLeftInteriorFlowerPoint m a,
      coordinateUnlinkExteriorPlanarFullCoverSeparationSpherePoint)

private def coordinateUnlinkExteriorPlanarRightInteriorFlowerSpinPoint
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m :=
  partialSphereSpinInr (coordinateUnlinkExteriorPlanarFlowerOuter m)
    (coordinateUnlinkExteriorPlanarRightInteriorFlowerPoint m,
      coordinateUnlinkExteriorPlanarFullCoverSeparationSpherePoint)

private def coordinateUnlinkExteriorPlanarLeftInteriorClosedPoint
    (m : ℕ) [NeZero m] (a : ZMod m) :
    CoordinateUnlinkExteriorEighthPowerPullback m :=
  coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
    (coordinateUnlinkExteriorPlanarLeftInteriorFlowerSpinPoint m a)

private def coordinateUnlinkExteriorPlanarRightInteriorClosedPoint
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorEighthPowerPullback m :=
  coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
    (coordinateUnlinkExteriorPlanarRightInteriorFlowerSpinPoint m)

private theorem coordinateUnlinkExteriorPlanarLeftInteriorClosedPoint_mem_strict
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarLeftInteriorClosedPoint m a ∈
      coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m := by
  exact coordinateUnlinkExteriorPlanarNeckTransport_planar_mem_strict m
    (coordinateUnlinkExteriorPlanarLeftInteriorFlowerPoint m a)
    coordinateUnlinkExteriorPlanarFullCoverSeparationSpherePoint
    (coordinateUnlinkExteriorPlanarLeftInteriorFlowerPoint_pow_strict m a)
    (coordinateUnlinkExteriorPlanarLeftInteriorFlowerPoint_pow_add_one_strict m a)

private theorem coordinateUnlinkExteriorPlanarRightInteriorClosedPoint_mem_strict
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarRightInteriorClosedPoint m ∈
      coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m := by
  exact coordinateUnlinkExteriorPlanarNeckTransport_planar_mem_strict m
    (coordinateUnlinkExteriorPlanarRightInteriorFlowerPoint m)
    coordinateUnlinkExteriorPlanarFullCoverSeparationSpherePoint
    (coordinateUnlinkExteriorPlanarRightInteriorFlowerPoint_pow_strict m)
    (coordinateUnlinkExteriorPlanarRightInteriorFlowerPoint_pow_add_one_strict m)

private def coordinateUnlinkExteriorPlanarLeftInteriorStrictPoint
    (m : ℕ) [NeZero m] (a : ZMod m) :
    CoordinateUnlinkExteriorEighthPowerPullbackStrict m :=
  ⟨coordinateUnlinkExteriorPlanarLeftInteriorClosedPoint m a,
    coordinateUnlinkExteriorPlanarLeftInteriorClosedPoint_mem_strict m a⟩

private def coordinateUnlinkExteriorPlanarRightInteriorStrictPoint
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorEighthPowerPullbackStrict m :=
  ⟨coordinateUnlinkExteriorPlanarRightInteriorClosedPoint m,
    coordinateUnlinkExteriorPlanarRightInteriorClosedPoint_mem_strict m⟩

private def coordinateUnlinkExteriorPlanarLeftInteriorFullCoverPoint
    (m : ℕ) [NeZero m] (a : ZMod m) :
    StandardUnlinkPowerPullback m :=
  (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).symm
    (coordinateUnlinkExteriorPlanarLeftInteriorStrictPoint m a)

private def coordinateUnlinkExteriorPlanarRightInteriorFullCoverPoint
    (m : ℕ) [NeZero m] :
    StandardUnlinkPowerPullback m :=
  (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).symm
    (coordinateUnlinkExteriorPlanarRightInteriorStrictPoint m)

private theorem coordinateUnlinkExteriorPlanarFullCoverToNeckStar_leftInterior
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFullCoverToNeckStar m
        (coordinateUnlinkExteriorPlanarLeftInteriorFullCoverPoint m a) =
      coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
        (coordinateUnlinkExteriorPlanarLeftInteriorFlowerSpinPoint m a) := by
  rw [coordinateUnlinkExteriorPlanarLeftInteriorFullCoverPoint]
  change coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
      ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm
        ((coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m
          ((coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).symm
            (coordinateUnlinkExteriorPlanarLeftInteriorStrictPoint m a))).1)) = _
  rw [
    (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).apply_symm_apply]
  change coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
      ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm
        (coordinateUnlinkExteriorPlanarLeftInteriorClosedPoint m a)) = _
  rw [coordinateUnlinkExteriorPlanarLeftInteriorClosedPoint,
    (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm_apply_apply]

private theorem coordinateUnlinkExteriorPlanarFullCoverToNeckStar_rightInterior
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarFullCoverToNeckStar m
        (coordinateUnlinkExteriorPlanarRightInteriorFullCoverPoint m) =
      coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
        (coordinateUnlinkExteriorPlanarRightInteriorFlowerSpinPoint m) := by
  rw [coordinateUnlinkExteriorPlanarRightInteriorFullCoverPoint]
  change coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
      ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm
        ((coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m
          ((coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).symm
            (coordinateUnlinkExteriorPlanarRightInteriorStrictPoint m))).1)) = _
  rw [
    (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).apply_symm_apply]
  change coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
      ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm
        (coordinateUnlinkExteriorPlanarRightInteriorClosedPoint m)) = _
  rw [coordinateUnlinkExteriorPlanarRightInteriorClosedPoint,
    (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm_apply_apply]

private def coordinateUnlinkExteriorPlanarLeftInteriorGridPoint
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalLeft :=
  topologicalPushoutInr
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
    ((a, (coordinateUnlinkExteriorPlanarFullCoverSeparationCirclePoint,
      coordinateUnlinkExteriorPlanarInteriorHalfTime)),
        coordinateUnlinkExteriorPlanarFullCoverSeparationSpherePoint)

private def coordinateUnlinkExteriorPlanarRightInteriorGridPoint
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalRight :=
  topologicalPushoutInr
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight
    ((coordinateUnlinkExteriorPlanarFullCoverSeparationCirclePoint,
      coordinateUnlinkExteriorPlanarInteriorHalfTime),
        coordinateUnlinkExteriorPlanarFullCoverSeparationSpherePoint)

private def coordinateUnlinkExteriorPlanarLeftInteriorStarComplementPoint
    (m : ℕ) [NeZero m] (a : ZMod m) :
    CoordinateUnlinkExteriorPlanarNeckLeftComplement m :=
  coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
    (coordinateUnlinkExteriorPlanarLeftInteriorGridPoint m a)

private def coordinateUnlinkExteriorPlanarRightInteriorStarComplementPoint
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNeckRightComplement m :=
  coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m
    (coordinateUnlinkExteriorPlanarRightInteriorGridPoint m)

private theorem coordinateUnlinkExteriorPlanarFlowerToStar_leftInterior
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
        (coordinateUnlinkExteriorPlanarLeftInteriorFlowerSpinPoint m a) =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)
        (coordinateUnlinkExteriorPlanarLeftInteriorStarComplementPoint m a) := by
  rw [coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar,
    Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarLeftInteriorFlowerSpinPoint,
    coordinateUnlinkExteriorPlanarLeftInteriorFlowerPoint,
    coordinateUnlinkExteriorPlanarNeckGridRegrouping_bottomLeft_apply]
  unfold TopologicalPushoutGridDiagram.columnFirstBottomLeft
  rw [ContinuousMap.comp_apply,
    coordinateUnlinkExteriorPlanarNeckGridColumnFirstHomeomorphStar_inl]
  rfl

private theorem coordinateUnlinkExteriorPlanarFlowerToStar_rightInterior
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
        (coordinateUnlinkExteriorPlanarRightInteriorFlowerSpinPoint m) =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)
        (coordinateUnlinkExteriorPlanarRightInteriorStarComplementPoint m) := by
  rw [coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar,
    Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarRightInteriorFlowerSpinPoint,
    coordinateUnlinkExteriorPlanarRightInteriorFlowerPoint,
    coordinateUnlinkExteriorPlanarNeckGridRegrouping_bottomRight_apply]
  unfold TopologicalPushoutGridDiagram.columnFirstBottomRight
  rw [ContinuousMap.comp_apply,
    coordinateUnlinkExteriorPlanarNeckGridColumnFirstHomeomorphStar_inr]
  rfl

private theorem injective_coordinateUnlinkExteriorPlanarNeckGridLeftToTopLeft
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft := by
  intro x y hxy
  apply Prod.ext
  · exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridHL m ↦ z.1) hxy
  · apply Subtype.ext
    exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridHL m ↦ z.2.1) hxy

private theorem coordinateUnlinkExteriorPlanarLeftInteriorGridPoint_not_range
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarLeftInteriorGridPoint m a ∉
      range (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  rintro ⟨q, hq⟩
  rcases topologicalPushout_jointly_surjective D.centerToTop D.centerToBottom q with
    ⟨e, rfl⟩ | ⟨x, rfl⟩
  · rw [TopologicalPushoutGridDiagram.verticalCenterToLeft_inl] at hq
    obtain ⟨b, _hbTop, hbBottom⟩ :=
      (topologicalPushoutInl_eq_inr_iff D.leftToTopLeft D.leftToBottomLeft
        (injective_coordinateUnlinkExteriorPlanarNeckGridLeftToTopLeft m)
        (D.topToTopLeft e)
        ((a, (coordinateUnlinkExteriorPlanarFullCoverSeparationCirclePoint,
          coordinateUnlinkExteriorPlanarInteriorHalfTime)),
            coordinateUnlinkExteriorPlanarFullCoverSeparationSpherePoint)).mp hq
    have htime := congrArg
      (fun z : CoordinateUnlinkExteriorPlanarNeckGridFL m ↦ z.1.2.2) hbBottom
    rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_leftToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridLeftToBottomLeft_apply] at htime
    have htimeVal := congrArg Subtype.val htime
    norm_num [coordinateUnlinkExteriorPlanarInteriorHalfTime] at htimeVal
  · rw [TopologicalPushoutGridDiagram.verticalCenterToLeft_inr] at hq
    have hbottom := topologicalPushoutInr_injective
      D.leftToTopLeft D.leftToBottomLeft
      (injective_coordinateUnlinkExteriorPlanarNeckGridLeftToTopLeft m) hq
    have htime := congrArg
      (fun z : CoordinateUnlinkExteriorPlanarNeckGridFL m ↦ z.1.2.2) hbottom
    rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_bottomToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridBottomToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNormalizedLeftSeam_time] at htime
    have htimeVal := congrArg Subtype.val htime
    norm_num [coordinateUnlinkExteriorPlanarInteriorHalfTime] at htimeVal

private theorem injective_coordinateUnlinkExteriorPlanarNeckGridRightToTopRight
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight := by
  intro x y hxy
  apply Prod.ext
  · exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridHR m ↦ z.1) hxy
  · apply Subtype.ext
    exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridHR m ↦ z.2.1) hxy

private theorem coordinateUnlinkExteriorPlanarRightInteriorGridPoint_not_range
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarRightInteriorGridPoint m ∉
      range (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  rintro ⟨q, hq⟩
  rcases topologicalPushout_jointly_surjective D.centerToTop D.centerToBottom q with
    ⟨e, rfl⟩ | ⟨x, rfl⟩
  · rw [TopologicalPushoutGridDiagram.verticalCenterToRight_inl] at hq
    obtain ⟨b, _hbTop, hbBottom⟩ :=
      (topologicalPushoutInl_eq_inr_iff D.rightToTopRight D.rightToBottomRight
        (injective_coordinateUnlinkExteriorPlanarNeckGridRightToTopRight m)
        (D.topToTopRight e)
        ((coordinateUnlinkExteriorPlanarFullCoverSeparationCirclePoint,
          coordinateUnlinkExteriorPlanarInteriorHalfTime),
            coordinateUnlinkExteriorPlanarFullCoverSeparationSpherePoint)).mp hq
    have htime := congrArg
      (fun z : CoordinateUnlinkExteriorPlanarNeckGridFR ↦ z.1.2) hbBottom
    rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_rightToBottomRight_apply,
      coordinateUnlinkExteriorPlanarNeckGridRightToBottomRight_apply] at htime
    have htimeVal := congrArg Subtype.val htime
    norm_num [coordinateUnlinkExteriorPlanarInteriorHalfTime] at htimeVal
  · rw [TopologicalPushoutGridDiagram.verticalCenterToRight_inr] at hq
    have hbottom := topologicalPushoutInr_injective
      D.rightToTopRight D.rightToBottomRight
      (injective_coordinateUnlinkExteriorPlanarNeckGridRightToTopRight m) hq
    have htime := congrArg
      (fun z : CoordinateUnlinkExteriorPlanarNeckGridFR ↦ z.1.2) hbottom
    rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_bottomToBottomRight_apply,
      coordinateUnlinkExteriorPlanarNeckGridBottomToBottomRight_apply,
      coordinateUnlinkExteriorPlanarNormalizedRightSeam_time] at htime
    have htimeVal := congrArg Subtype.val htime
    norm_num [coordinateUnlinkExteriorPlanarInteriorHalfTime] at htimeVal

private theorem coordinateUnlinkExteriorPlanarLeftInteriorStarComplementPoint_not_range
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarLeftInteriorStarComplementPoint m a ∉
      range (coordinateUnlinkExteriorPlanarNeckStarToLeft m) := by
  rintro ⟨x, hx⟩
  apply coordinateUnlinkExteriorPlanarLeftInteriorGridPoint_not_range m a
  refine ⟨(coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm x, ?_⟩
  apply (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m).injective
  exact hx

private theorem coordinateUnlinkExteriorPlanarRightInteriorStarComplementPoint_not_range
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarRightInteriorStarComplementPoint m ∉
      range (coordinateUnlinkExteriorPlanarNeckStarToRight m) := by
  rintro ⟨x, hx⟩
  apply coordinateUnlinkExteriorPlanarRightInteriorGridPoint_not_range m
  refine ⟨(coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm x, ?_⟩
  apply (coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m).injective
  exact hx

private theorem coordinateUnlinkExteriorPlanarLeftInteriorStarComplementPoint_label
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarNeckStarLeftLabel m
        (coordinateUnlinkExteriorPlanarLeftInteriorStarComplementPoint m a) = a := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  let x : CoordinateUnlinkExteriorPlanarNeckGridFL m :=
    ((a, (coordinateUnlinkExteriorPlanarFullCoverSeparationCirclePoint,
      coordinateUnlinkExteriorPlanarInteriorHalfTime)),
        coordinateUnlinkExteriorPlanarFullCoverSeparationSpherePoint)
  have hsymm :
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal m).symm
          (topologicalPushoutInr D.leftToTopLeft D.leftToBottomLeft x) =
        topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram m).leftToTopLeft
          (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram m).leftToBottomLeft
          x := by
    apply
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal m).injective
    rw [(coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal
      m).apply_symm_apply]
    exact (simLeftVerticalLeftOriginal_inr m x).symm
  rw [coordinateUnlinkExteriorPlanarNeckStarLeftLabel_apply,
    coordinateUnlinkExteriorPlanarLeftInteriorStarComplementPoint,
    coordinateUnlinkExteriorPlanarLeftInteriorGridPoint,
    coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement,
    Homeomorph.trans_apply, hsymm,
    coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphComplementOneHandles_apply_coe]
  change
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle m
      ((coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
        m).columnFirstBottomLeft x)).1 = a
  rw [coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle_bottomLeft]

/-- The selected full-cover left side remains nonempty after restriction to the strict core.
The displayed witness has normalized annulus time `1 / 2`. -/
theorem coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide_nonempty
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a).Nonempty := by
  let oldLabel := a + coordinateUnlinkExteriorPlanarSmoothNeckShift m
  refine ⟨coordinateUnlinkExteriorPlanarLeftInteriorFullCoverPoint m oldLabel, ?_⟩
  change coordinateUnlinkExteriorPlanarFullCoverToNeckStar m
      (coordinateUnlinkExteriorPlanarLeftInteriorFullCoverPoint m oldLabel) ∈
    coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m oldLabel
  rw [coordinateUnlinkExteriorPlanarFullCoverToNeckStar_leftInterior,
    coordinateUnlinkExteriorPlanarFlowerToStar_leftInterior]
  exact ⟨coordinateUnlinkExteriorPlanarLeftInteriorStarComplementPoint m oldLabel,
    ⟨coordinateUnlinkExteriorPlanarLeftInteriorStarComplementPoint_label m oldLabel,
      coordinateUnlinkExteriorPlanarLeftInteriorStarComplementPoint_not_range
        m oldLabel⟩, rfl⟩

/-- The remainder side also survives strict-core restriction; its witness is the right
normalized annulus point at time `1 / 2`. -/
theorem coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide_nonempty
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a).Nonempty := by
  let oldLabel := a + coordinateUnlinkExteriorPlanarSmoothNeckShift m
  let f := coordinateUnlinkExteriorPlanarNeckStarToLeft m
  let g := coordinateUnlinkExteriorPlanarNeckStarToRight m
  let y := coordinateUnlinkExteriorPlanarRightInteriorStarComplementPoint m
  refine ⟨coordinateUnlinkExteriorPlanarRightInteriorFullCoverPoint m, ?_⟩
  change coordinateUnlinkExteriorPlanarFullCoverToNeckStar m
      (coordinateUnlinkExteriorPlanarRightInteriorFullCoverPoint m) ∈
    coordinateUnlinkExteriorPlanarNeckStarFiberRest m oldLabel
  rw [coordinateUnlinkExteriorPlanarFullCoverToNeckStar_rightInterior,
    coordinateUnlinkExteriorPlanarFlowerToStar_rightInterior]
  change topologicalPushoutInr f g y ∈
    topologicalPushoutFiberRest f g
      (coordinateUnlinkExteriorPlanarNeckStarLeftLabel m) oldLabel
  refine ⟨?_, ?_⟩
  · rintro ⟨s, hs⟩
    obtain ⟨z, hzf, hzg⟩ :=
      (topologicalPushoutInl_eq_inr_iff f g
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m).injective
        (f (oldLabel, s)) y).mp hs
    have hz : z = (oldLabel, s) :=
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m).injective hzf
    exact coordinateUnlinkExteriorPlanarRightInteriorStarComplementPoint_not_range m
      ⟨z, hz ▸ hzg⟩
  · rintro ⟨x, hx, hxp⟩
    obtain ⟨z, hzf, _hzg⟩ :=
      (topologicalPushoutInl_eq_inr_iff f g
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m).injective
        x y).mp hxp
    exact hx.2 ⟨z, hzf⟩

/-! ## Clopen restriction and failure of preconnectedness -/

/-- The selected left side is clopen in the complement of the selected equator lift. -/
theorem isClopen_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide_restrict
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsClopen (((range (equatorUnlinkPowerLift m a))ᶜ) ↓∩
      coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a) := by
  let E := (range (equatorUnlinkPowerLift m a))ᶜ
  let L := coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a
  let R := coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a
  have hopenL : IsOpen (E ↓∩ L) :=
    (isOpen_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a).preimage
      continuous_subtype_val
  have hopenR : IsOpen (E ↓∩ R) :=
    (isOpen_coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a).preimage
      continuous_subtype_val
  refine ⟨?_, hopenL⟩
  rw [← isOpen_compl_iff]
  convert hopenR using 1
  ext x
  change (x.1 ∉ L) ↔ x.1 ∈ R
  have hxUnion : x.1 ∈ L ∨ x.1 ∈ R := by
    have hx : x.1 ∈
        coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a ∪
          coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a := by
      rw [union_coordinateUnlinkExteriorPlanarFullCoverEquatorSides]
      exact x.2
    simpa [L, R] using hx
  constructor
  · exact fun hx ↦ hxUnion.resolve_left hx
  · intro hxR hxL
    exact Set.disjoint_left.1
      (disjoint_coordinateUnlinkExteriorPlanarFullCoverEquatorSides m a) hxL hxR

/-- Removing one selected coordinate-equator lift genuinely disconnects the actual full
`StandardUnlinkPowerPullback`.  This does not assert that either displayed side is connected. -/
theorem not_preconnectedSpace_coordinateUnlinkExteriorPlanarFullCoverEquatorComplement
    (m : ℕ) [NeZero m] (a : ZMod m) :
    ¬ PreconnectedSpace (↑(range (equatorUnlinkPowerLift m a))ᶜ) := by
  intro hpre
  let _ : PreconnectedSpace (↑(range (equatorUnlinkPowerLift m a))ᶜ) := hpre
  let leftRestricted :=
    (((range (equatorUnlinkPowerLift m a))ᶜ) ↓∩
      coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a)
  have hleftClopen : IsClopen leftRestricted :=
    isClopen_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide_restrict m a
  rcases isClopen_iff.mp hleftClopen with hleftEmpty | hleftUniv
  · obtain ⟨x, hx⟩ :=
      coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide_nonempty m a
    have hxComplement : x ∈ (range (equatorUnlinkPowerLift m a))ᶜ := by
      rw [← union_coordinateUnlinkExteriorPlanarFullCoverEquatorSides]
      exact Or.inl hx
    let xs : ↑(range (equatorUnlinkPowerLift m a))ᶜ := ⟨x, hxComplement⟩
    have hxs : xs ∈ leftRestricted := hx
    rw [hleftEmpty] at hxs
    exact hxs
  · obtain ⟨y, hy⟩ :=
      coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide_nonempty m a
    have hyComplement : y ∈ (range (equatorUnlinkPowerLift m a))ᶜ := by
      rw [← union_coordinateUnlinkExteriorPlanarFullCoverEquatorSides]
      exact Or.inr hy
    let ys : ↑(range (equatorUnlinkPowerLift m a))ᶜ := ⟨y, hyComplement⟩
    have hys : ys ∈ leftRestricted := hleftUniv.symm ▸ mem_univ ys
    exact Set.disjoint_left.1
      (disjoint_coordinateUnlinkExteriorPlanarFullCoverEquatorSides m a) hys hy

end SplittingSpheres

end
