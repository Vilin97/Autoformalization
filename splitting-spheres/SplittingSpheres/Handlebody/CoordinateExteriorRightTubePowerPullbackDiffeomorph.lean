/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorRightTubeOneHandleDiffeomorph
public import SplittingSpheres.Handlebody.CoordinateExteriorOneHandlePowerPullbackDiffeomorph

/-!
# Right-tube power-pullback diffeomorphism

This file pulls the nonzero-complex power cover back over the direct closed right-tube
exterior. A positive radial gauge compares this pullback with the established one-handle
power pullback, yielding a genuine diffeomorphism and hence a direct one-handle recognition.
No compact-neck inclusion or capping construction is introduced here.
-/

@[expose] public section

open Function Metric Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

local instance :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      CoordinateExteriorRightTubeClosed :=
  coordinateExteriorRightTubeClosedChartedSpace

local instance :
    IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
  isManifold_coordinateExteriorRightTubeClosed

/-- The right character after identifying the closed right-tube exterior with the one-handle
piece and applying the aligned sphere map. -/
def coordinateExteriorRightTubeTargetCharacter
    (q : CoordinateExteriorRightTubeClosed) : ℂ :=
  standardUnlinkRightDisplacementComplex
    (unlinkAlignedOneHandleSphereMap
      (coordinateExteriorRightTubeOneHandleDiffeomorph q))

/-- The right-normal character on the closed right-tube exterior. -/
def coordinateExteriorRightTubeRightNormalMap
    (q : CoordinateExteriorRightTubeClosed) : {z : ℂ // z ≠ 0} :=
  ⟨standardUnlinkRightDisplacementComplex q.1, by
    intro hz
    have hnorm :
        ‖standardUnlinkNormalProjection q.1 -
            standardUnlinkNormalCenter 1‖ = 0 := by
      rw [← norm_unlinkNormalPlaneToComplex]
      exact norm_eq_zero.mpr hz
    have hmem : q.1 ∈ standardUnlinkOpenTube 1 (1 / 8 : ℝ) := by
      change ‖standardUnlinkNormalProjection q.1 -
          standardUnlinkNormalCenter 1‖ < 1 / 8
      rw [hnorm]
      norm_num
    have hcarrier := q.2
    change q.1 ∈ coordinateExteriorRightTubeClosedCarrier at hcarrier
    rw [coordinateExteriorRightTubeClosedCarrier_eq_compl_openTube] at hcarrier
    exact hcarrier hmem⟩

/-- Coercing the right normal map recovers the standard right displacement character. -/
@[simp]
theorem coordinateExteriorRightTubeRightNormalMap_coe
    (q : CoordinateExteriorRightTubeClosed) :
    (coordinateExteriorRightTubeRightNormalMap q : ℂ) =
      standardUnlinkRightDisplacementComplex q.1 :=
  rfl

/-- The right normal map on the direct closed right-tube exterior is continuous. -/
theorem continuous_coordinateExteriorRightTubeRightNormalMap :
    Continuous coordinateExteriorRightTubeRightNormalMap :=
  (continuous_standardUnlinkRightDisplacementComplex.comp
    continuous_subtype_val).subtype_mk _

/-- The degree-`m` power pullback over the closed right-tube exterior. -/
abbrev CoordinateExteriorRightTubePowerPullback (m : ℕ) :=
  TopologicalCoverPullback (nonzeroComplexPow m)
    coordinateExteriorRightTubeRightNormalMap

/-- Projection from the right-tube power pullback. -/
def coordinateExteriorRightTubePowerPullbackProj (m : ℕ) :
    CoordinateExteriorRightTubePowerPullback m →
      CoordinateExteriorRightTubeClosed :=
  topologicalCoverPullbackProj (nonzeroComplexPow m)
    coordinateExteriorRightTubeRightNormalMap

/-- The pullback projection is the base component of a pullback point. -/
@[simp]
theorem coordinateExteriorRightTubePowerPullbackProj_apply
    (m : ℕ) (z : CoordinateExteriorRightTubePowerPullback m) :
    coordinateExteriorRightTubePowerPullbackProj m z = z.1.1 :=
  rfl

/-- For nonzero degree, the right-tube power-pullback projection is a covering map. -/
theorem isCoveringMap_coordinateExteriorRightTubePowerPullbackProj
    (m : ℕ) [NeZero m] :
    IsCoveringMap (coordinateExteriorRightTubePowerPullbackProj m) :=
  SplittingSpheres.IsCoveringMap.pullback
    (isCoveringMap_nonzeroComplexPow m)
    continuous_coordinateExteriorRightTubeRightNormalMap

/-- The atlas pulled back from the direct closed right-tube atlas. -/
abbrev coordinateExteriorRightTubePowerPullbackChartedSpace
    (m : ℕ) [NeZero m] :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateExteriorRightTubePowerPullback m) :=
  SplittingSpheres.IsCoveringMap.pullbackChartedSpace
    (isCoveringMap_coordinateExteriorRightTubePowerPullbackProj m)

/-- The pulled-back atlas makes the right-tube power pullback a smooth manifold with boundary. -/
theorem isManifold_coordinateExteriorRightTubePowerPullback
    (m : ℕ) [NeZero m] :
    letI := coordinateExteriorRightTubePowerPullbackChartedSpace m
    IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) := by
  let _ := coordinateExteriorRightTubePowerPullbackChartedSpace m
  exact SplittingSpheres.IsCoveringMap.isManifold_pullbackChartedSpace
    coordinateUnlinkExteriorModel ∞
      (isCoveringMap_coordinateExteriorRightTubePowerPullbackProj m)

/-- The right-tube power-pullback projection is a local diffeomorphism for the direct atlas. -/
theorem isLocalDiffeomorph_coordinateExteriorRightTubePowerPullbackProj
    (m : ℕ) [NeZero m] :
    letI := coordinateExteriorRightTubePowerPullbackChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateExteriorRightTubePowerPullback m) :=
      isManifold_coordinateExteriorRightTubePowerPullback m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
        (coordinateExteriorRightTubePowerPullbackProj m) := by
  let _ := coordinateExteriorRightTubePowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullback m
  exact SplittingSpheres.IsCoveringMap.isLocalDiffeomorph_pullbackChartedSpace
    coordinateUnlinkExteriorModel ∞
      (isCoveringMap_coordinateExteriorRightTubePowerPullbackProj m)

/-- The pullback boundary is exactly the projection preimage of the right-tube boundary. -/
theorem coordinateExteriorRightTubePowerPullback_boundary
    (m : ℕ) [NeZero m] :
    letI := coordinateExteriorRightTubePowerPullbackChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateExteriorRightTubePowerPullback m) :=
      isManifold_coordinateExteriorRightTubePowerPullback m
    coordinateUnlinkExteriorModel.boundary
        (CoordinateExteriorRightTubePowerPullback m) =
      coordinateExteriorRightTubePowerPullbackProj m ⁻¹'
        ((Subtype.val : CoordinateExteriorRightTubeClosed → Sphere 4) ⁻¹'
          coordinateExteriorRightTubeBoundary) := by
  let _ := coordinateExteriorRightTubePowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullback m
  rw [← coordinateExteriorRightTubeClosed_boundary]
  exact
    ((isLocalDiffeomorph_coordinateExteriorRightTubePowerPullbackProj m)
      |>.preimage_boundary (by simp)).symm

/-- The positive real ratio between the one-handle and right-tube characters. -/
def coordinateExteriorRightTubeCharacterScale
    (q : CoordinateExteriorRightTubeClosed) : ℝ :=
  ((coordinateExteriorRightTubeTargetCharacter q) /
    standardUnlinkRightDisplacementComplex q.1).re

/-- The right-tube character comparison scale is positive. -/
theorem coordinateExteriorRightTubeCharacterScale_pos
    (q : CoordinateExteriorRightTubeClosed) :
    0 < coordinateExteriorRightTubeCharacterScale q := by
  obtain ⟨c, hc, hchar⟩ :=
    coordinateExteriorRightTubeOneHandleDiffeomorph_character_positiveScalar q
  have hratio :
      coordinateExteriorRightTubeTargetCharacter q /
          standardUnlinkRightDisplacementComplex q.1 = (c : ℂ) := by
    rw [coordinateExteriorRightTubeTargetCharacter, hchar]
    exact mul_div_cancel_right₀ (c : ℂ)
      (coordinateExteriorRightTubeRightNormalMap q).2
  rw [coordinateExteriorRightTubeCharacterScale, hratio]
  simpa using hc

/-- The target character is the positive comparison scale times the source character. -/
theorem coordinateExteriorRightTubeTargetCharacter_eq_scale_mul
    (q : CoordinateExteriorRightTubeClosed) :
    coordinateExteriorRightTubeTargetCharacter q =
      (coordinateExteriorRightTubeCharacterScale q : ℂ) *
        standardUnlinkRightDisplacementComplex q.1 := by
  obtain ⟨c, _hc, hchar⟩ :=
    coordinateExteriorRightTubeOneHandleDiffeomorph_character_positiveScalar q
  have hratio :
      coordinateExteriorRightTubeTargetCharacter q /
          standardUnlinkRightDisplacementComplex q.1 = (c : ℂ) := by
    rw [coordinateExteriorRightTubeTargetCharacter, hchar]
    exact mul_div_cancel_right₀ (c : ℂ)
      (coordinateExteriorRightTubeRightNormalMap q).2
  have hscale : coordinateExteriorRightTubeCharacterScale q = c := by
    rw [coordinateExteriorRightTubeCharacterScale, hratio]
    rfl
  rw [hscale]
  exact hchar

/-- The positive right-tube character comparison scale is continuous. -/
theorem continuous_coordinateExteriorRightTubeCharacterScale :
    Continuous coordinateExteriorRightTubeCharacterScale := by
  have hsource : Continuous
      (fun q : CoordinateExteriorRightTubeClosed ↦
        standardUnlinkRightDisplacementComplex q.1) :=
    continuous_standardUnlinkRightDisplacementComplex.comp
      (continuous_subtype_val)
  have htarget : Continuous coordinateExteriorRightTubeTargetCharacter :=
    continuous_standardUnlinkRightDisplacementComplex.comp
      (unlinkAlignedOneHandleSphereMap.continuous.comp
        coordinateExteriorRightTubeOneHandleDiffeomorph.continuous)
  exact Complex.continuous_re.comp
    (htarget.div hsource fun q ↦
      (coordinateExteriorRightTubeRightNormalMap q).2)

/-- The positive `m`-th root of the right-tube character comparison scale. -/
@[nolint unusedArguments]
def coordinateExteriorRightTubeCharacterRootScale (m : ℕ) [NeZero m]
    (q : CoordinateExteriorRightTubeClosed) : ℝ :=
  Real.exp (Real.log (coordinateExteriorRightTubeCharacterScale q) / (m : ℝ))

/-- The right-tube character root scale is positive. -/
theorem coordinateExteriorRightTubeCharacterRootScale_pos
    (m : ℕ) [NeZero m] (q : CoordinateExteriorRightTubeClosed) :
    0 < coordinateExteriorRightTubeCharacterRootScale m q :=
  Real.exp_pos _

/-- The right-tube character root scale is continuous. -/
theorem continuous_coordinateExteriorRightTubeCharacterRootScale
    (m : ℕ) [NeZero m] :
    Continuous (coordinateExteriorRightTubeCharacterRootScale m) := by
  have hlog : Continuous
      (fun q : CoordinateExteriorRightTubeClosed =>
        Real.log (coordinateExteriorRightTubeCharacterScale q)) :=
    by
      rw [continuous_iff_continuousAt]
      intro q
      change ContinuousAt
        (Real.log ∘ coordinateExteriorRightTubeCharacterScale) q
      exact (Real.continuousAt_log
        (coordinateExteriorRightTubeCharacterScale_pos q).ne').comp
          continuous_coordinateExteriorRightTubeCharacterScale.continuousAt
  have hdiv : Continuous
      (fun q : CoordinateExteriorRightTubeClosed =>
        Real.log (coordinateExteriorRightTubeCharacterScale q) / (m : ℝ)) :=
    hlog.div_const _
  exact Real.continuous_exp.comp hdiv

/-- The `m`-th power of the root scale is the character comparison scale. -/
theorem coordinateExteriorRightTubeCharacterRootScale_pow
    (m : ℕ) [NeZero m] (q : CoordinateExteriorRightTubeClosed) :
    coordinateExteriorRightTubeCharacterRootScale m q ^ m =
      coordinateExteriorRightTubeCharacterScale q := by
  rw [coordinateExteriorRightTubeCharacterRootScale, ← Real.exp_nat_mul]
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  rw [show (m : ℝ) *
      (Real.log (coordinateExteriorRightTubeCharacterScale q) / (m : ℝ)) =
      Real.log (coordinateExteriorRightTubeCharacterScale q) by field_simp]
  exact Real.exp_log (coordinateExteriorRightTubeCharacterScale_pos q)

/-- The target character agrees exactly with the established one-handle pullback character. -/
theorem coordinateExteriorRightTubeTargetCharacter_eq_oneHandleCharacter
    (q : CoordinateExteriorRightTubeClosed) :
    (coordinateUnlinkExteriorPushoutRightNormalMap
        (coordinateUnlinkExteriorPushoutOneHandleInclusion
          (coordinateExteriorRightTubeOneHandleDiffeomorph q)) : ℂ) =
      coordinateExteriorRightTubeTargetCharacter q := by
  rw [coordinateUnlinkExteriorPushoutRightNormalMap_oneHandle]
  rw [coordinateExteriorRightTubeTargetCharacter,
    standardUnlinkRightDisplacementComplex,
    standardUnlinkNormalProjection_unlinkAlignedOneHandleSphereMap]

/-- The positive-gauge correction of the power coordinate in the forward comparison. -/
def coordinateExteriorRightTubePowerPullbackForwardPowerCoordinate
    (m : ℕ) [NeZero m]
    (z : CoordinateExteriorRightTubePowerPullback m) : {w : ℂ // w ≠ 0} :=
  ⟨(coordinateExteriorRightTubeCharacterRootScale m z.1.1 : ℂ) * z.1.2.1, by
    apply mul_ne_zero
    · exact_mod_cast
        (coordinateExteriorRightTubeCharacterRootScale_pos m z.1.1).ne'
    · exact z.1.2.2⟩

/-- The corrected forward coordinate has the required one-handle `m`-th power. -/
theorem coordinateExteriorRightTubePowerPullbackForwardPowerCoordinate_pow
    (m : ℕ) [NeZero m]
    (z : CoordinateExteriorRightTubePowerPullback m) :
    (coordinateExteriorRightTubePowerPullbackForwardPowerCoordinate m z : ℂ) ^ m =
      (coordinateUnlinkExteriorPushoutRightNormalMap
        (coordinateUnlinkExteriorPushoutOneHandleInclusion
          (coordinateExteriorRightTubeOneHandleDiffeomorph z.1.1)) : ℂ) := by
  rw [coordinateExteriorRightTubePowerPullbackForwardPowerCoordinate,
    mul_pow]
  have hscale :
      (coordinateExteriorRightTubeCharacterRootScale m z.1.1 : ℂ) ^ m =
        (coordinateExteriorRightTubeCharacterScale z.1.1 : ℂ) := by
    exact_mod_cast coordinateExteriorRightTubeCharacterRootScale_pow m z.1.1
  rw [hscale]
  have hpullback : standardUnlinkRightDisplacementComplex z.1.1.1 =
      z.1.2.1 ^ m := by
    exact congrArg Subtype.val z.2
  rw [← hpullback,
    ← coordinateExteriorRightTubeTargetCharacter_eq_scale_mul,
    ← coordinateExteriorRightTubeTargetCharacter_eq_oneHandleCharacter]

/-- The explicit positive-gauge map to the established one-handle power pullback. -/
def coordinateExteriorRightTubePowerPullbackForward
    (m : ℕ) [NeZero m]
    (z : CoordinateExteriorRightTubePowerPullback m) :
    CoordinateUnlinkExteriorOneHandlePowerPullback m :=
  ⟨(coordinateExteriorRightTubeOneHandleDiffeomorph z.1.1,
      coordinateExteriorRightTubePowerPullbackForwardPowerCoordinate m z), by
    apply Subtype.ext
    exact
      (coordinateExteriorRightTubePowerPullbackForwardPowerCoordinate_pow m z).symm⟩

/-- The explicit positive-gauge forward map is continuous. -/
theorem continuous_coordinateExteriorRightTubePowerPullbackForward
    (m : ℕ) [NeZero m] :
    Continuous (coordinateExteriorRightTubePowerPullbackForward m) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact coordinateExteriorRightTubeOneHandleDiffeomorph.continuous.comp
      (continuous_fst.comp continuous_subtype_val)
  · apply Continuous.subtype_mk
    exact ((Complex.continuous_ofReal.comp
        ((continuous_coordinateExteriorRightTubeCharacterRootScale m).comp
          (continuous_fst.comp continuous_subtype_val))).mul
      (continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val)))

/-- The reciprocal-gauge correction of the inverse power coordinate. -/
def coordinateExteriorRightTubePowerPullbackInversePowerCoordinate
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) : {w : ℂ // w ≠ 0} :=
  ⟨(coordinateExteriorRightTubeCharacterRootScale m
      (coordinateExteriorRightTubeOneHandleDiffeomorph.symm z.1.1) : ℂ)⁻¹ * z.1.2.1, by
    apply mul_ne_zero
    · apply inv_ne_zero
      exact_mod_cast (coordinateExteriorRightTubeCharacterRootScale_pos m
        (coordinateExteriorRightTubeOneHandleDiffeomorph.symm z.1.1)).ne'
    · exact z.1.2.2⟩

/-- The corrected inverse coordinate has the required right-tube `m`-th power. -/
theorem coordinateExteriorRightTubePowerPullbackInversePowerCoordinate_pow
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    (coordinateExteriorRightTubePowerPullbackInversePowerCoordinate m z : ℂ) ^ m =
      (coordinateExteriorRightTubeRightNormalMap
        (coordinateExteriorRightTubeOneHandleDiffeomorph.symm z.1.1) : ℂ) := by
  let q : CoordinateExteriorRightTubeClosed :=
    coordinateExteriorRightTubeOneHandleDiffeomorph.symm z.1.1
  have hbase : coordinateExteriorRightTubeOneHandleDiffeomorph q = z.1.1 :=
    coordinateExteriorRightTubeOneHandleDiffeomorph.apply_symm_apply z.1.1
  have hpullback : coordinateExteriorRightTubeTargetCharacter q =
      z.1.2.1 ^ m := by
    rw [← coordinateExteriorRightTubeTargetCharacter_eq_oneHandleCharacter,
      hbase]
    exact congrArg Subtype.val z.2
  have hscale :
      (coordinateExteriorRightTubeCharacterRootScale m q : ℂ) ^ m =
        (coordinateExteriorRightTubeCharacterScale q : ℂ) := by
    exact_mod_cast coordinateExteriorRightTubeCharacterRootScale_pow m q
  have hscale_ne : (coordinateExteriorRightTubeCharacterScale q : ℂ) ≠ 0 := by
    exact_mod_cast (coordinateExteriorRightTubeCharacterScale_pos q).ne'
  change (((coordinateExteriorRightTubeCharacterRootScale m q : ℂ)⁻¹ *
    z.1.2.1) ^ m) = _
  rw [mul_pow, inv_pow, hscale, ← hpullback,
    coordinateExteriorRightTubeTargetCharacter_eq_scale_mul]
  change (coordinateExteriorRightTubeCharacterScale q : ℂ)⁻¹ *
      ((coordinateExteriorRightTubeCharacterScale q : ℂ) *
        standardUnlinkRightDisplacementComplex q.1) = _
  rw [inv_mul_cancel_left₀ hscale_ne]
  rfl

/-- The explicit reciprocal-gauge inverse map from the one-handle power pullback. -/
def coordinateExteriorRightTubePowerPullbackInverse
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    CoordinateExteriorRightTubePowerPullback m :=
  ⟨(coordinateExteriorRightTubeOneHandleDiffeomorph.symm z.1.1,
      coordinateExteriorRightTubePowerPullbackInversePowerCoordinate m z), by
    apply Subtype.ext
    exact
      (coordinateExteriorRightTubePowerPullbackInversePowerCoordinate_pow m z).symm⟩

/-- The explicit reciprocal-gauge inverse map is continuous. -/
theorem continuous_coordinateExteriorRightTubePowerPullbackInverse
    (m : ℕ) [NeZero m] :
    Continuous (coordinateExteriorRightTubePowerPullbackInverse m) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact coordinateExteriorRightTubeOneHandleDiffeomorph.symm.continuous.comp
      (continuous_fst.comp continuous_subtype_val)
  · apply Continuous.subtype_mk
    exact (((Complex.continuous_ofReal.comp
        ((continuous_coordinateExteriorRightTubeCharacterRootScale m).comp
          (coordinateExteriorRightTubeOneHandleDiffeomorph.symm.continuous.comp
            (continuous_fst.comp continuous_subtype_val)))).inv₀
              (fun z : CoordinateUnlinkExteriorOneHandlePowerPullback m ↦ by
                change (coordinateExteriorRightTubeCharacterRootScale m
                  (coordinateExteriorRightTubeOneHandleDiffeomorph.symm z.1.1) : ℂ) ≠ 0
                exact_mod_cast (coordinateExteriorRightTubeCharacterRootScale_pos m
                  (coordinateExteriorRightTubeOneHandleDiffeomorph.symm z.1.1)).ne')).mul
      (continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val)))

/-- The reciprocal-gauge inverse cancels the forward map. -/
theorem coordinateExteriorRightTubePowerPullbackInverse_forward
    (m : ℕ) [NeZero m]
    (z : CoordinateExteriorRightTubePowerPullback m) :
    coordinateExteriorRightTubePowerPullbackInverse m
        (coordinateExteriorRightTubePowerPullbackForward m z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · exact coordinateExteriorRightTubeOneHandleDiffeomorph.symm_apply_apply z.1.1
  · apply Subtype.ext
    change (coordinateExteriorRightTubeCharacterRootScale m
        (coordinateExteriorRightTubeOneHandleDiffeomorph.symm
          (coordinateExteriorRightTubeOneHandleDiffeomorph z.1.1)) : ℂ)⁻¹ *
        ((coordinateExteriorRightTubeCharacterRootScale m z.1.1 : ℂ) *
          z.1.2.1) = z.1.2.1
    rw [coordinateExteriorRightTubeOneHandleDiffeomorph.symm_apply_apply]
    apply inv_mul_cancel_left₀
    exact_mod_cast
      (coordinateExteriorRightTubeCharacterRootScale_pos m z.1.1).ne'

/-- The positive-gauge forward map cancels the reciprocal-gauge inverse. -/
theorem coordinateExteriorRightTubePowerPullbackForward_inverse
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    coordinateExteriorRightTubePowerPullbackForward m
        (coordinateExteriorRightTubePowerPullbackInverse m z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · exact coordinateExteriorRightTubeOneHandleDiffeomorph.apply_symm_apply z.1.1
  · apply Subtype.ext
    change (coordinateExteriorRightTubeCharacterRootScale m
        (coordinateExteriorRightTubeOneHandleDiffeomorph.symm z.1.1) : ℂ) *
        ((coordinateExteriorRightTubeCharacterRootScale m
          (coordinateExteriorRightTubeOneHandleDiffeomorph.symm z.1.1) : ℂ)⁻¹ *
          z.1.2.1) = z.1.2.1
    apply mul_inv_cancel_left₀
    exact_mod_cast (coordinateExteriorRightTubeCharacterRootScale_pos m
      (coordinateExteriorRightTubeOneHandleDiffeomorph.symm z.1.1)).ne'

/-- The positive gauge gives a homeomorphism of the two power pullbacks over the closed
right-tube diffeomorphism. -/
def coordinateExteriorRightTubePowerPullbackHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateExteriorRightTubePowerPullback m ≃ₜ
      CoordinateUnlinkExteriorOneHandlePowerPullback m where
  toFun := coordinateExteriorRightTubePowerPullbackForward m
  invFun := coordinateExteriorRightTubePowerPullbackInverse m
  left_inv := coordinateExteriorRightTubePowerPullbackInverse_forward m
  right_inv := coordinateExteriorRightTubePowerPullbackForward_inverse m
  continuous_toFun :=
    continuous_coordinateExteriorRightTubePowerPullbackForward m
  continuous_invFun :=
    continuous_coordinateExteriorRightTubePowerPullbackInverse m

/-- The positive-gauge homeomorphism commutes exactly with the two pullback projections. -/
theorem coordinateExteriorRightTubePowerPullbackHomeomorph_proj
    (m : ℕ) [NeZero m]
    (z : CoordinateExteriorRightTubePowerPullback m) :
    coordinateUnlinkExteriorOneHandlePowerPullbackProj m
        (coordinateExteriorRightTubePowerPullbackHomeomorph m z) =
      coordinateExteriorRightTubeOneHandleDiffeomorph
        (coordinateExteriorRightTubePowerPullbackProj m z) :=
  rfl

/-- The gauge-corrected pullback homeomorphism is a diffeomorphism for the actual atlases
pulled back along the two covering projections. -/
def coordinateExteriorRightTubePowerPullbackDiffeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateExteriorRightTubePowerPullbackChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateExteriorRightTubePowerPullback m) :=
      isManifold_coordinateExteriorRightTubePowerPullback m
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    letI : IsManifold oneHandlePieceModel ∞
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
    CoordinateExteriorRightTubePowerPullback m
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, oneHandlePieceModel⟯
        CoordinateUnlinkExteriorOneHandlePowerPullback m := by
  let _ := coordinateExteriorRightTubePowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullback m
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
    (isLocalDiffeomorph_coordinateExteriorRightTubePowerPullbackProj m)
    (isLocalDiffeomorph_coordinateUnlinkExteriorOneHandlePowerPullbackProj m)
    coordinateExteriorRightTubeOneHandleDiffeomorph
    (coordinateExteriorRightTubePowerPullbackHomeomorph m)
    (fun _ ↦ rfl)

/-- The pullback diffeomorphism has the explicit positive-gauge homeomorphism as its map. -/
@[simp]
theorem coordinateExteriorRightTubePowerPullbackDiffeomorph_apply
    (m : ℕ) [NeZero m]
    (z : CoordinateExteriorRightTubePowerPullback m) :
    coordinateExteriorRightTubePowerPullbackDiffeomorph m z =
      coordinateExteriorRightTubePowerPullbackHomeomorph m z :=
  rfl

/-- The underlying homeomorphism of the pullback diffeomorphism is the positive-gauge one. -/
@[simp]
theorem coordinateExteriorRightTubePowerPullbackDiffeomorph_toHomeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateExteriorRightTubePowerPullbackChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateExteriorRightTubePowerPullback m) :=
      isManifold_coordinateExteriorRightTubePowerPullback m
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    letI : IsManifold oneHandlePieceModel ∞
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
    (coordinateExteriorRightTubePowerPullbackDiffeomorph m).toHomeomorph =
      coordinateExteriorRightTubePowerPullbackHomeomorph m :=
  rfl

/-- The closed right-tube power pullback is a genuine smooth one-handle. -/
def coordinateExteriorRightTubePowerPullbackOneHandleDiffeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateExteriorRightTubePowerPullbackChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateExteriorRightTubePowerPullback m) :=
      isManifold_coordinateExteriorRightTubePowerPullback m
    CoordinateExteriorRightTubePowerPullback m
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, oneHandlePieceModel⟯
        OneHandlePiece := by
  let _ := coordinateExteriorRightTubePowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullback m
  let _ : ChartedSpace OneHandleModelSpace
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
  let _ : IsManifold oneHandlePieceModel ∞
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
  exact (coordinateExteriorRightTubePowerPullbackDiffeomorph m).trans
    (coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph m).symm

end SplittingSpheres
