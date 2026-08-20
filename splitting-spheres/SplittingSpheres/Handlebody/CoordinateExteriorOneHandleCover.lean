/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPowerPieceCover

/-!
# The power cover over the whole one-handle piece

On the `S¹ × B³` face the right-normal character factors as

`u * (sphereHandleScale ‖b‖ - (1 / 2) * conj u)`.

The residual factor ranges in the open disk of radius one about `1`, which misses zero.  A
selected continuous `m`th-root branch on that disk therefore removes the residual factor from
the pullback.  What remains is the ordinary degree-`m` power map on the circle.  This gives an
explicit homeomorphism from another copy of `S¹ × B³` to the restricted pullback.

Everything in this file is point-set topology.  No smooth structure on a pullback or
graph-thickening identification is asserted.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-! ## Complex coordinates on the project circle -/

theorem continuous_unlinkUnitCircleComplex : Continuous unlinkUnitCircleComplex := by
  unfold unlinkUnitCircleComplex unlinkNormalPlaneToComplex
  fun_prop

theorem continuous_complexToUnlinkNormalPlane :
    Continuous (complexToUnlinkNormalPlane : ℂ → UnlinkNormalPlane) := by
  unfold complexToUnlinkNormalPlane
  fun_prop

@[simp]
theorem complexToUnlinkNormalPlane_unlinkUnitCircleComplex (u : Sphere 1) :
    complexToUnlinkNormalPlane (unlinkUnitCircleComplex u) = u.1 := by
  ext j
  fin_cases j <;>
    simp [complexToUnlinkNormalPlane, unlinkUnitCircleComplex,
      unlinkNormalPlaneToComplex, Complex.equivRealProdCLM_symm_apply]

/-- The degree-`m` power map on the project's copy of the unit circle. -/
def unlinkUnitCirclePow (m : ℕ) (u : Sphere 1) : Sphere 1 :=
  ⟨complexToUnlinkNormalPlane (unlinkUnitCircleComplex u ^ m), by
    rw [mem_sphere_zero_iff_norm, norm_complexToUnlinkNormalPlane, norm_pow,
      norm_unlinkUnitCircleComplex, one_pow]⟩

@[simp]
theorem unlinkUnitCircleComplex_pow (m : ℕ) (u : Sphere 1) :
    unlinkUnitCircleComplex (unlinkUnitCirclePow m u) =
      unlinkUnitCircleComplex u ^ m :=
  unlinkNormalPlaneToComplex_complexToUnlinkNormalPlane _

theorem continuous_unlinkUnitCirclePow (m : ℕ) :
    Continuous (unlinkUnitCirclePow m) := by
  apply Continuous.subtype_mk
  exact continuous_complexToUnlinkNormalPlane.comp
    (continuous_unlinkUnitCircleComplex.pow m)

/-- The base map displayed by the trivialization: degree `m` on `S¹` and the identity on
`B³`. -/
def coordinateUnlinkExteriorOneHandleBasePowerMap (m : ℕ)
    (x : OneHandlePiece) : OneHandlePiece :=
  (unlinkUnitCirclePow m x.1, x.2)

@[simp]
theorem coordinateUnlinkExteriorOneHandleBasePowerMap_fst (m : ℕ)
    (x : OneHandlePiece) :
    (coordinateUnlinkExteriorOneHandleBasePowerMap m x).1 =
      unlinkUnitCirclePow m x.1 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorOneHandleBasePowerMap_snd (m : ℕ)
    (x : OneHandlePiece) :
    (coordinateUnlinkExteriorOneHandleBasePowerMap m x).2 = x.2 :=
  rfl

theorem continuous_coordinateUnlinkExteriorOneHandleBasePowerMap (m : ℕ) :
    Continuous (coordinateUnlinkExteriorOneHandleBasePowerMap m) :=
  (continuous_unlinkUnitCirclePow m).comp continuous_fst |>.prodMk continuous_snd

/-! ## The residual factor and its root branch -/

/-- The residual factor after extracting the unit-circle coordinate from the one-handle
character. -/
def coordinateUnlinkExteriorOneHandleResidual (x : OneHandlePiece) : ℂ :=
  (sphereHandleScale ‖x.2.1‖ : ℂ) -
    (1 / 2 : ℂ) * starRingEnd ℂ (unlinkUnitCircleComplex x.1)

theorem continuous_coordinateUnlinkExteriorOneHandleResidual :
    Continuous coordinateUnlinkExteriorOneHandleResidual := by
  unfold coordinateUnlinkExteriorOneHandleResidual
  have hscale : Continuous (fun x : OneHandlePiece ↦ sphereHandleScale ‖x.2.1‖) :=
    continuous_sphereHandleScale.comp
      (continuous_norm.comp (continuous_subtype_val.comp continuous_snd))
  exact (Complex.continuous_ofReal.comp hscale).sub
    (continuous_const.mul
      (Complex.continuous_conj.comp
        (continuous_unlinkUnitCircleComplex.comp continuous_fst)))

/-- Exact complex formula for the one-handle character. -/
@[simp]
theorem coordinateUnlinkExteriorPushoutRightNormalMap_oneHandle_complex
    (x : OneHandlePiece) :
    (coordinateUnlinkExteriorPushoutRightNormalMap
        (coordinateUnlinkExteriorPushoutOneHandleInclusion x) : ℂ) =
      (sphereHandleScale ‖x.2.1‖ : ℂ) * unlinkUnitCircleComplex x.1 -
        (1 / 2 : ℂ) := by
  rw [coordinateUnlinkExteriorPushoutRightNormalMap_oneHandle]
  simp [unlinkUnitCircleComplex, unlinkNormalPlaneToComplex,
    standardUnlinkNormalCenter, standardUnlinkHeight,
    Complex.equivRealProdCLM_symm_apply]
  ring

/-- The one-handle character is the unit-circle coordinate times the residual factor. -/
theorem coordinateUnlinkExteriorOneHandle_character_factorization
    (x : OneHandlePiece) :
    unlinkUnitCircleComplex x.1 * coordinateUnlinkExteriorOneHandleResidual x =
      (coordinateUnlinkExteriorPushoutRightNormalMap
        (coordinateUnlinkExteriorPushoutOneHandleInclusion x) : ℂ) := by
  rw [coordinateUnlinkExteriorPushoutRightNormalMap_oneHandle_complex,
    coordinateUnlinkExteriorOneHandleResidual]
  have hunit : unlinkUnitCircleComplex x.1 *
      starRingEnd ℂ (unlinkUnitCircleComplex x.1) = 1 := by
    rw [Complex.mul_conj', norm_unlinkUnitCircleComplex]
    norm_num
  rw [mul_sub, show unlinkUnitCircleComplex x.1 *
      ((1 / 2 : ℂ) * starRingEnd ℂ (unlinkUnitCircleComplex x.1)) =
        (1 / 2 : ℂ) * (unlinkUnitCircleComplex x.1 *
          starRingEnd ℂ (unlinkUnitCircleComplex x.1)) by ring, hunit]
  ring

/-- A convex disk containing every residual value and excluding zero. -/
def coordinateUnlinkExteriorOneHandleResidualBall : Set ℂ :=
  ball (1 : ℂ) 1

theorem isOpen_coordinateUnlinkExteriorOneHandleResidualBall :
    IsOpen coordinateUnlinkExteriorOneHandleResidualBall :=
  isOpen_ball

theorem isSimplyConnected_coordinateUnlinkExteriorOneHandleResidualBall :
    IsSimplyConnected coordinateUnlinkExteriorOneHandleResidualBall := by
  let _ : ContractibleSpace coordinateUnlinkExteriorOneHandleResidualBall :=
    (convex_ball (1 : ℂ) 1).contractibleSpace (nonempty_ball.mpr zero_lt_one)
  change SimplyConnectedSpace coordinateUnlinkExteriorOneHandleResidualBall
  infer_instance

theorem zero_not_mem_coordinateUnlinkExteriorOneHandleResidualBall :
    (0 : ℂ) ∉ coordinateUnlinkExteriorOneHandleResidualBall := by
  simp [coordinateUnlinkExteriorOneHandleResidualBall, mem_ball, Complex.dist_eq]

theorem zero_not_mem_image_id_coordinateUnlinkExteriorOneHandleResidualBall :
    (0 : ℂ) ∉ id '' coordinateUnlinkExteriorOneHandleResidualBall := by
  simpa only [image_id] using
    zero_not_mem_coordinateUnlinkExteriorOneHandleResidualBall

theorem sphereHandleScale_le_one (t : ℝ) : sphereHandleScale t ≤ 1 := by
  rw [sphereHandleScale, Real.sqrt_le_one]
  nlinarith [sq_nonneg sphereHandleRadius, sq_nonneg t]

theorem half_lt_sphereHandleRadius : (1 / 2 : ℝ) < sphereHandleRadius := by
  rw [← sq_lt_sq₀ (by norm_num) sphereHandleRadius_pos.le, sphereHandleRadius_sq]
  norm_num

theorem coordinateUnlinkExteriorOneHandleResidual_mem_ball (x : OneHandlePiece) :
    coordinateUnlinkExteriorOneHandleResidual x ∈
      coordinateUnlinkExteriorOneHandleResidualBall := by
  have hb : ‖x.2.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2.2
  have hslow : sphereHandleRadius ≤ sphereHandleScale ‖x.2.1‖ :=
    sphereHandleRadius_le_scale_on_unit (norm_nonneg _) hb
  have hsle : sphereHandleScale ‖x.2.1‖ ≤ 1 :=
    sphereHandleScale_le_one _
  change dist ((sphereHandleScale ‖x.2.1‖ : ℂ) -
      (1 / 2 : ℂ) * starRingEnd ℂ (unlinkUnitCircleComplex x.1)) 1 < 1
  rw [Complex.dist_eq]
  have hrewrite :
      (sphereHandleScale ‖x.2.1‖ : ℂ) -
          (1 / 2 : ℂ) * starRingEnd ℂ (unlinkUnitCircleComplex x.1) - 1 =
        ((sphereHandleScale ‖x.2.1‖ - 1 : ℝ) : ℂ) -
          (1 / 2 : ℂ) * starRingEnd ℂ (unlinkUnitCircleComplex x.1) := by
    push_cast
    ring
  rw [hrewrite]
  calc
    ‖((sphereHandleScale ‖x.2.1‖ - 1 : ℝ) : ℂ) -
        (1 / 2 : ℂ) * starRingEnd ℂ (unlinkUnitCircleComplex x.1)‖ ≤
        ‖((sphereHandleScale ‖x.2.1‖ - 1 : ℝ) : ℂ)‖ +
          ‖(1 / 2 : ℂ) * starRingEnd ℂ (unlinkUnitCircleComplex x.1)‖ := norm_sub_le _ _
    _ = (1 - sphereHandleScale ‖x.2.1‖) + 1 / 2 := by
      rw [norm_mul, Complex.norm_conj, norm_unlinkUnitCircleComplex]
      simp only [mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonpos (sub_nonpos.mpr hsle), neg_sub]
      norm_num
    _ < 1 := by linarith [half_lt_sphereHandleRadius]

theorem coordinateUnlinkExteriorOneHandleResidual_ne_zero (x : OneHandlePiece) :
    coordinateUnlinkExteriorOneHandleResidual x ≠ 0 := by
  intro hzero
  have hmem := coordinateUnlinkExteriorOneHandleResidual_mem_ball x
  rw [hzero] at hmem
  exact zero_not_mem_coordinateUnlinkExteriorOneHandleResidualBall hmem

theorem exists_coordinateUnlinkExteriorOneHandleResidualPowerRoot
    (m : ℕ) [NeZero m] :
    ∃ f : ℂ → ℂ,
      ContinuousOn f coordinateUnlinkExteriorOneHandleResidualBall ∧
        ∀ z : ℂ, f z ^ m = z := by
  simpa only [id_eq] using
    (Complex.exists_continuousOn_pow_eq
      isSimplyConnected_coordinateUnlinkExteriorOneHandleResidualBall
      isOpen_coordinateUnlinkExteriorOneHandleResidualBall
      (g := id) continuousOn_id
      zero_not_mem_image_id_coordinateUnlinkExteriorOneHandleResidualBall
      (NeZero.ne m))

/-- A selected continuous `m`th-root branch on the residual disk. -/
def coordinateUnlinkExteriorOneHandleResidualPowerRoot
    (m : ℕ) [NeZero m] : ℂ → ℂ :=
  Classical.choose (exists_coordinateUnlinkExteriorOneHandleResidualPowerRoot m)

theorem continuousOn_coordinateUnlinkExteriorOneHandleResidualPowerRoot
    (m : ℕ) [NeZero m] :
    ContinuousOn (coordinateUnlinkExteriorOneHandleResidualPowerRoot m)
      coordinateUnlinkExteriorOneHandleResidualBall :=
  (Classical.choose_spec
    (exists_coordinateUnlinkExteriorOneHandleResidualPowerRoot m)).1

@[simp]
theorem coordinateUnlinkExteriorOneHandleResidualPowerRoot_pow
    (m : ℕ) [NeZero m] (z : ℂ) :
    coordinateUnlinkExteriorOneHandleResidualPowerRoot m z ^ m = z :=
  (Classical.choose_spec
    (exists_coordinateUnlinkExteriorOneHandleResidualPowerRoot m)).2 z

theorem continuous_coordinateUnlinkExteriorOneHandleResidualPowerRoot_comp
    (m : ℕ) [NeZero m] :
    Continuous (fun x : OneHandlePiece ↦
      coordinateUnlinkExteriorOneHandleResidualPowerRoot m
        (coordinateUnlinkExteriorOneHandleResidual x)) :=
  (continuousOn_coordinateUnlinkExteriorOneHandleResidualPowerRoot m).comp_continuous
    continuous_coordinateUnlinkExteriorOneHandleResidual
    coordinateUnlinkExteriorOneHandleResidual_mem_ball

theorem coordinateUnlinkExteriorOneHandleResidualPowerRoot_ne_zero
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    coordinateUnlinkExteriorOneHandleResidualPowerRoot m
        (coordinateUnlinkExteriorOneHandleResidual x) ≠ 0 := by
  intro hzero
  have hp := coordinateUnlinkExteriorOneHandleResidualPowerRoot_pow m
    (coordinateUnlinkExteriorOneHandleResidual x)
  rw [hzero, zero_pow (NeZero.ne m)] at hp
  exact coordinateUnlinkExteriorOneHandleResidual_ne_zero x hp.symm

/-! ## The explicit trivializing homeomorphism -/

/-- Power coordinate used by the forward trivialization. -/
def coordinateUnlinkExteriorOneHandleTrivializationPowerCoordinate
    (m : ℕ) [NeZero m] (x : OneHandlePiece) : {z : ℂ // z ≠ 0} :=
  ⟨unlinkUnitCircleComplex x.1 *
      coordinateUnlinkExteriorOneHandleResidualPowerRoot m
        (coordinateUnlinkExteriorOneHandleResidual
          (coordinateUnlinkExteriorOneHandleBasePowerMap m x)),
    mul_ne_zero (unlinkUnitCircleComplex_ne_zero x.1)
      (coordinateUnlinkExteriorOneHandleResidualPowerRoot_ne_zero m _)⟩

@[simp]
theorem coordinateUnlinkExteriorOneHandleTrivializationPowerCoordinate_pow
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    (coordinateUnlinkExteriorOneHandleTrivializationPowerCoordinate m x : ℂ) ^ m =
      (coordinateUnlinkExteriorPushoutRightNormalMap
        (coordinateUnlinkExteriorPushoutOneHandleInclusion
          (coordinateUnlinkExteriorOneHandleBasePowerMap m x)) : ℂ) := by
  change (unlinkUnitCircleComplex x.1 *
      coordinateUnlinkExteriorOneHandleResidualPowerRoot m
        (coordinateUnlinkExteriorOneHandleResidual
          (coordinateUnlinkExteriorOneHandleBasePowerMap m x))) ^ m = _
  rw [mul_pow, coordinateUnlinkExteriorOneHandleResidualPowerRoot_pow,
    ← coordinateUnlinkExteriorOneHandle_character_factorization,
    coordinateUnlinkExteriorOneHandleBasePowerMap_fst,
    unlinkUnitCircleComplex_pow]

theorem continuous_coordinateUnlinkExteriorOneHandleTrivializationPowerCoordinate
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorOneHandleTrivializationPowerCoordinate m) := by
  apply Continuous.subtype_mk
  exact (continuous_unlinkUnitCircleComplex.comp continuous_fst).mul
    ((continuous_coordinateUnlinkExteriorOneHandleResidualPowerRoot_comp m).comp
      (continuous_coordinateUnlinkExteriorOneHandleBasePowerMap m))

/-- Forward map from a second copy of `S¹ × B³` into the restricted power pullback. -/
def coordinateUnlinkExteriorOneHandlePowerTrivializationForward
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    CoordinateUnlinkExteriorOneHandlePowerPullback m :=
  ⟨(coordinateUnlinkExteriorOneHandleBasePowerMap m x,
      coordinateUnlinkExteriorOneHandleTrivializationPowerCoordinate m x), by
    apply Subtype.ext
    exact (coordinateUnlinkExteriorOneHandleTrivializationPowerCoordinate_pow m x).symm⟩

@[simp]
theorem coordinateUnlinkExteriorOneHandlePowerPullbackProj_trivializationForward
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    coordinateUnlinkExteriorOneHandlePowerPullbackProj m
        (coordinateUnlinkExteriorOneHandlePowerTrivializationForward m x) =
      coordinateUnlinkExteriorOneHandleBasePowerMap m x :=
  rfl

theorem continuous_coordinateUnlinkExteriorOneHandlePowerTrivializationForward
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorOneHandlePowerTrivializationForward m) := by
  apply Continuous.subtype_mk
  exact (continuous_coordinateUnlinkExteriorOneHandleBasePowerMap m).prodMk
    (continuous_coordinateUnlinkExteriorOneHandleTrivializationPowerCoordinate m)

/-- The circle coordinate recovered from a point of the restricted pullback, before bundling it
back into `Sphere 1`. -/
def coordinateUnlinkExteriorOneHandlePowerTrivializationInverseComplex
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) : ℂ :=
  z.1.2.1 /
    coordinateUnlinkExteriorOneHandleResidualPowerRoot m
      (coordinateUnlinkExteriorOneHandleResidual z.1.1)

theorem continuous_coordinateUnlinkExteriorOneHandlePowerTrivializationInverseComplex
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorOneHandlePowerTrivializationInverseComplex m) := by
  have hcoordinate : Continuous
      (fun z : CoordinateUnlinkExteriorOneHandlePowerPullback m ↦ z.1.2.1) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
  have hbase : Continuous
      (fun z : CoordinateUnlinkExteriorOneHandlePowerPullback m ↦ z.1.1) :=
    continuous_fst.comp continuous_subtype_val
  exact hcoordinate.div
    ((continuous_coordinateUnlinkExteriorOneHandleResidualPowerRoot_comp m).comp hbase)
    (fun z ↦ coordinateUnlinkExteriorOneHandleResidualPowerRoot_ne_zero m z.1.1)

@[simp]
theorem coordinateUnlinkExteriorOneHandlePowerTrivializationInverseComplex_pow
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    coordinateUnlinkExteriorOneHandlePowerTrivializationInverseComplex m z ^ m =
      unlinkUnitCircleComplex z.1.1.1 := by
  rw [coordinateUnlinkExteriorOneHandlePowerTrivializationInverseComplex, div_pow,
    coordinateUnlinkExteriorOneHandleResidualPowerRoot_pow]
  have hpullback : z.1.2.1 ^ m =
      (coordinateUnlinkExteriorPushoutRightNormalMap
        (coordinateUnlinkExteriorPushoutOneHandleInclusion z.1.1) : ℂ) :=
    (congrArg Subtype.val z.2).symm
  rw [hpullback, ← coordinateUnlinkExteriorOneHandle_character_factorization]
  exact mul_div_cancel_right₀ _
    (coordinateUnlinkExteriorOneHandleResidual_ne_zero z.1.1)

/-- The recovered complex coordinate has norm one. -/
theorem norm_coordinateUnlinkExteriorOneHandlePowerTrivializationInverseComplex
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    ‖coordinateUnlinkExteriorOneHandlePowerTrivializationInverseComplex m z‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _ ) (NeZero.ne m)).mp
  rw [← norm_pow,
    coordinateUnlinkExteriorOneHandlePowerTrivializationInverseComplex_pow,
    norm_unlinkUnitCircleComplex]

/-- Bundle the recovered unit complex number as the source-circle coordinate. -/
def coordinateUnlinkExteriorOneHandlePowerTrivializationInverseCircle
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) : Sphere 1 :=
  ⟨complexToUnlinkNormalPlane
      (coordinateUnlinkExteriorOneHandlePowerTrivializationInverseComplex m z), by
    rw [mem_sphere_zero_iff_norm, norm_complexToUnlinkNormalPlane,
      norm_coordinateUnlinkExteriorOneHandlePowerTrivializationInverseComplex]⟩

@[simp]
theorem unlinkUnitCircleComplex_trivializationInverseCircle
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    unlinkUnitCircleComplex
        (coordinateUnlinkExteriorOneHandlePowerTrivializationInverseCircle m z) =
      coordinateUnlinkExteriorOneHandlePowerTrivializationInverseComplex m z :=
  unlinkNormalPlaneToComplex_complexToUnlinkNormalPlane _

theorem continuous_coordinateUnlinkExteriorOneHandlePowerTrivializationInverseCircle
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorOneHandlePowerTrivializationInverseCircle m) := by
  apply Continuous.subtype_mk
  exact continuous_complexToUnlinkNormalPlane.comp
      (continuous_coordinateUnlinkExteriorOneHandlePowerTrivializationInverseComplex m)

/-- Inverse map back to `S¹ × B³`. -/
def coordinateUnlinkExteriorOneHandlePowerTrivializationInverse
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) : OneHandlePiece :=
  (coordinateUnlinkExteriorOneHandlePowerTrivializationInverseCircle m z, z.1.1.2)

theorem continuous_coordinateUnlinkExteriorOneHandlePowerTrivializationInverse
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorOneHandlePowerTrivializationInverse m) :=
  (continuous_coordinateUnlinkExteriorOneHandlePowerTrivializationInverseCircle m).prodMk
    (continuous_snd.comp (continuous_fst.comp continuous_subtype_val))

@[simp]
theorem coordinateUnlinkExteriorOneHandleBasePowerMap_trivializationInverse
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    coordinateUnlinkExteriorOneHandleBasePowerMap m
        (coordinateUnlinkExteriorOneHandlePowerTrivializationInverse m z) = z.1.1 := by
  apply Prod.ext
  · apply Subtype.ext
    change (unlinkUnitCirclePow m
        (coordinateUnlinkExteriorOneHandlePowerTrivializationInverseCircle m z)).1 =
      z.1.1.1
    rw [show (unlinkUnitCirclePow m
        (coordinateUnlinkExteriorOneHandlePowerTrivializationInverseCircle m z)).1 =
        complexToUnlinkNormalPlane
          (coordinateUnlinkExteriorOneHandlePowerTrivializationInverseComplex m z ^ m) by rfl,
      coordinateUnlinkExteriorOneHandlePowerTrivializationInverseComplex_pow,
      complexToUnlinkNormalPlane_unlinkUnitCircleComplex]
  · rfl

theorem coordinateUnlinkExteriorOneHandlePowerTrivializationInverse_forward
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    coordinateUnlinkExteriorOneHandlePowerTrivializationInverse m
        (coordinateUnlinkExteriorOneHandlePowerTrivializationForward m x) = x := by
  apply Prod.ext
  · apply Subtype.ext
    change complexToUnlinkNormalPlane
      ((unlinkUnitCircleComplex x.1 *
        coordinateUnlinkExteriorOneHandleResidualPowerRoot m
          (coordinateUnlinkExteriorOneHandleResidual
            (coordinateUnlinkExteriorOneHandleBasePowerMap m x))) /
        coordinateUnlinkExteriorOneHandleResidualPowerRoot m
          (coordinateUnlinkExteriorOneHandleResidual
            (coordinateUnlinkExteriorOneHandleBasePowerMap m x))) = x.1.1
    rw [mul_div_cancel_right₀ _
      (coordinateUnlinkExteriorOneHandleResidualPowerRoot_ne_zero m _),
      complexToUnlinkNormalPlane_unlinkUnitCircleComplex]
  · rfl

theorem coordinateUnlinkExteriorOneHandlePowerTrivializationForward_inverse
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    coordinateUnlinkExteriorOneHandlePowerTrivializationForward m
        (coordinateUnlinkExteriorOneHandlePowerTrivializationInverse m z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · exact coordinateUnlinkExteriorOneHandleBasePowerMap_trivializationInverse m z
  · apply Subtype.ext
    change coordinateUnlinkExteriorOneHandlePowerTrivializationInverseComplex m z *
        coordinateUnlinkExteriorOneHandleResidualPowerRoot m
          (coordinateUnlinkExteriorOneHandleResidual
            (coordinateUnlinkExteriorOneHandleBasePowerMap m
              (coordinateUnlinkExteriorOneHandlePowerTrivializationInverse m z))) =
      z.1.2.1
    rw [coordinateUnlinkExteriorOneHandleBasePowerMap_trivializationInverse,
      coordinateUnlinkExteriorOneHandlePowerTrivializationInverseComplex,
      div_mul_cancel₀ _
        (coordinateUnlinkExteriorOneHandleResidualPowerRoot_ne_zero m z.1.1)]

/-- The restricted degree-`m` power pullback over the whole one-handle is another
`S¹ × B³`. -/
def coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph
    (m : ℕ) [NeZero m] :
    OneHandlePiece ≃ₜ CoordinateUnlinkExteriorOneHandlePowerPullback m where
  toFun := coordinateUnlinkExteriorOneHandlePowerTrivializationForward m
  invFun := coordinateUnlinkExteriorOneHandlePowerTrivializationInverse m
  left_inv := coordinateUnlinkExteriorOneHandlePowerTrivializationInverse_forward m
  right_inv := coordinateUnlinkExteriorOneHandlePowerTrivializationForward_inverse m
  continuous_toFun :=
    continuous_coordinateUnlinkExteriorOneHandlePowerTrivializationForward m
  continuous_invFun :=
    continuous_coordinateUnlinkExteriorOneHandlePowerTrivializationInverse m

@[simp]
theorem coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph_apply
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m x =
      coordinateUnlinkExteriorOneHandlePowerTrivializationForward m x :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph_proj
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    coordinateUnlinkExteriorOneHandlePowerPullbackProj m
        (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m x) =
      coordinateUnlinkExteriorOneHandleBasePowerMap m x :=
  rfl

/-! ## Deck translations in the trivialized coordinates -/

/-- The intrinsic root-of-unity deck action on the restricted pullback. -/
def coordinateUnlinkExteriorOneHandlePowerDeckMap (m : ℕ)
    (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    CoordinateUnlinkExteriorOneHandlePowerPullback m :=
  ⟨(z.1.1, ⟨((u.1 : ℂˣ) : ℂ) * z.1.2.1,
      mul_ne_zero (Units.ne_zero u.1) z.1.2.2⟩), by
    apply Subtype.ext
    change (coordinateUnlinkExteriorPushoutRightNormalMap
        (coordinateUnlinkExteriorPushoutOneHandleInclusion z.1.1) : ℂ) =
      (((u.1 : ℂˣ) : ℂ) * z.1.2.1) ^ m
    rw [mul_pow, (mem_rootsOfUnity' m u.1).mp u.2, one_mul]
    exact congrArg Subtype.val z.2⟩

@[simp]
theorem coordinateUnlinkExteriorOneHandlePowerDeckMap_proj (m : ℕ)
    (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    coordinateUnlinkExteriorOneHandlePowerPullbackProj m
        (coordinateUnlinkExteriorOneHandlePowerDeckMap m u z) =
      coordinateUnlinkExteriorOneHandlePowerPullbackProj m z :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorOneHandlePowerDeckMap_powerCoordinate (m : ℕ)
    (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    ((coordinateUnlinkExteriorOneHandlePowerDeckMap m u z).1.2 : ℂ) =
      ((u.1 : ℂˣ) : ℂ) * z.1.2.1 :=
  rfl

theorem coordinateUnlinkExteriorOneHandlePowerDeckMap_one (m : ℕ)
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    coordinateUnlinkExteriorOneHandlePowerDeckMap m 1 z = z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp

theorem coordinateUnlinkExteriorOneHandlePowerDeckMap_mul (m : ℕ)
    (u v : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    coordinateUnlinkExteriorOneHandlePowerDeckMap m (u * v) z =
      coordinateUnlinkExteriorOneHandlePowerDeckMap m u
        (coordinateUnlinkExteriorOneHandlePowerDeckMap m v z) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change ((((u * v).1 : ℂˣ) : ℂ) * z.1.2.1) =
      ((u.1 : ℂˣ) : ℂ) * (((v.1 : ℂˣ) : ℂ) * z.1.2.1)
    rw [Subgroup.coe_mul, Units.val_mul]
    exact mul_assoc _ _ _

instance coordinateUnlinkExteriorOneHandlePowerPullbackMulAction (m : ℕ) :
    MulAction (rootsOfUnity m ℂ)
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) where
  smul := coordinateUnlinkExteriorOneHandlePowerDeckMap m
  one_smul := coordinateUnlinkExteriorOneHandlePowerDeckMap_one m
  mul_smul := coordinateUnlinkExteriorOneHandlePowerDeckMap_mul m

theorem continuous_coordinateUnlinkExteriorOneHandlePowerDeckMap (m : ℕ)
    (u : rootsOfUnity m ℂ) :
    Continuous (coordinateUnlinkExteriorOneHandlePowerDeckMap m u) := by
  unfold coordinateUnlinkExteriorOneHandlePowerDeckMap
  apply Continuous.subtype_mk
  exact (continuous_fst.comp continuous_subtype_val).prodMk <|
    (continuous_const.mul
      (continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val))).subtype_mk _

/-- A displayed deck transformation of the restricted pullback. -/
def coordinateUnlinkExteriorOneHandlePowerDeckHomeomorph (m : ℕ)
    (u : rootsOfUnity m ℂ) :
    CoordinateUnlinkExteriorOneHandlePowerPullback m ≃ₜ
      CoordinateUnlinkExteriorOneHandlePowerPullback m where
  toFun := (u • ·)
  invFun := (u⁻¹ • ·)
  left_inv z := inv_smul_smul u z
  right_inv z := smul_inv_smul u z
  continuous_toFun := continuous_coordinateUnlinkExteriorOneHandlePowerDeckMap m u
  continuous_invFun := continuous_coordinateUnlinkExteriorOneHandlePowerDeckMap m u⁻¹

@[simp]
theorem coordinateUnlinkExteriorOneHandlePowerDeckHomeomorph_apply (m : ℕ)
    (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    coordinateUnlinkExteriorOneHandlePowerDeckHomeomorph m u z =
      coordinateUnlinkExteriorOneHandlePowerDeckMap m u z :=
  rfl

/-- The restricted-pullback deck homeomorphisms form a group homomorphism. -/
def coordinateUnlinkExteriorOneHandlePowerDeckHom (m : ℕ) :
    rootsOfUnity m ℂ →*
      Homeomorph (CoordinateUnlinkExteriorOneHandlePowerPullback m)
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) where
  toFun := coordinateUnlinkExteriorOneHandlePowerDeckHomeomorph m
  map_one' := by
    apply Homeomorph.ext
    exact coordinateUnlinkExteriorOneHandlePowerDeckMap_one m
  map_mul' u v := by
    apply Homeomorph.ext
    exact coordinateUnlinkExteriorOneHandlePowerDeckMap_mul m u v

/-- The restricted-pullback deck homomorphism under the standard `ZMod m` index. -/
def coordinateUnlinkExteriorOneHandlePowerDeckZModHom (m : ℕ) [NeZero m] :
    Multiplicative (ZMod m) →*
      Homeomorph (CoordinateUnlinkExteriorOneHandlePowerPullback m)
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
  (coordinateUnlinkExteriorOneHandlePowerDeckHom m).comp
    (standardRootsOfUnityZModMulEquiv m).toMonoidHom

@[simp]
theorem coordinateUnlinkExteriorOneHandlePowerDeckZModHom_apply
    (m : ℕ) [NeZero m] (a : ZMod m)
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    coordinateUnlinkExteriorOneHandlePowerDeckZModHom m
        (Multiplicative.ofAdd a) z =
      coordinateUnlinkExteriorOneHandlePowerDeckMap m
        (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)) z :=
  rfl

/-- Multiplication of the source circle by an `m`th root of unity. -/
def coordinateUnlinkExteriorOneHandleCircleDeckTranslation (m : ℕ) [NeZero m]
    (u : rootsOfUnity m ℂ) (v : Sphere 1) : Sphere 1 :=
  ⟨complexToUnlinkNormalPlane
      (((u.1 : ℂˣ) : ℂ) * unlinkUnitCircleComplex v), by
    rw [mem_sphere_zero_iff_norm, norm_complexToUnlinkNormalPlane, norm_mul,
      Complex.norm_eq_one_of_mem_rootsOfUnity u.2,
      norm_unlinkUnitCircleComplex, one_mul]⟩

@[simp]
theorem unlinkUnitCircleComplex_circleDeckTranslation (m : ℕ) [NeZero m]
    (u : rootsOfUnity m ℂ) (v : Sphere 1) :
    unlinkUnitCircleComplex
        (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m u v) =
      ((u.1 : ℂˣ) : ℂ) * unlinkUnitCircleComplex v :=
  unlinkNormalPlaneToComplex_complexToUnlinkNormalPlane _

theorem continuous_coordinateUnlinkExteriorOneHandleCircleDeckTranslation
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ) :
    Continuous (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m u) := by
  apply Continuous.subtype_mk
  exact continuous_complexToUnlinkNormalPlane.comp
    (continuous_const.mul continuous_unlinkUnitCircleComplex)

@[simp]
theorem unlinkUnitCirclePow_circleDeckTranslation (m : ℕ) [NeZero m]
    (u : rootsOfUnity m ℂ) (v : Sphere 1) :
    unlinkUnitCirclePow m
        (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m u v) =
      unlinkUnitCirclePow m v := by
  apply Subtype.ext
  change complexToUnlinkNormalPlane
      ((((u.1 : ℂˣ) : ℂ) * unlinkUnitCircleComplex v) ^ m) =
    complexToUnlinkNormalPlane (unlinkUnitCircleComplex v ^ m)
  rw [mul_pow, (mem_rootsOfUnity' m u.1).mp u.2, one_mul]

/-- The corresponding translation of the trivializing `S¹ × B³`, leaving the ball coordinate
fixed. -/
def coordinateUnlinkExteriorOneHandleDeckTranslation (m : ℕ) [NeZero m]
    (u : rootsOfUnity m ℂ) (x : OneHandlePiece) : OneHandlePiece :=
  (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m u x.1, x.2)

@[simp]
theorem coordinateUnlinkExteriorOneHandleBasePowerMap_deckTranslation
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ) (x : OneHandlePiece) :
    coordinateUnlinkExteriorOneHandleBasePowerMap m
        (coordinateUnlinkExteriorOneHandleDeckTranslation m u x) =
      coordinateUnlinkExteriorOneHandleBasePowerMap m x := by
  apply Prod.ext
  · exact unlinkUnitCirclePow_circleDeckTranslation m u x.1
  · rfl

theorem continuous_coordinateUnlinkExteriorOneHandleDeckTranslation
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ) :
    Continuous (coordinateUnlinkExteriorOneHandleDeckTranslation m u) :=
  (continuous_coordinateUnlinkExteriorOneHandleCircleDeckTranslation m u).comp continuous_fst
    |>.prodMk continuous_snd

/-- In the explicit trivialization, source-circle translation by `u` is exactly the deck
transformation which multiplies the pullback power coordinate by `u`. -/
@[simp]
theorem coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph_deckTranslation
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ) (x : OneHandlePiece) :
    coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m
        (coordinateUnlinkExteriorOneHandleDeckTranslation m u x) =
      coordinateUnlinkExteriorOneHandlePowerDeckHomeomorph m u
        (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m x) := by
  apply Subtype.ext
  apply Prod.ext
  · exact coordinateUnlinkExteriorOneHandleBasePowerMap_deckTranslation m u x
  · apply Subtype.ext
    change (((u.1 : ℂˣ) : ℂ) * unlinkUnitCircleComplex x.1) *
        coordinateUnlinkExteriorOneHandleResidualPowerRoot m
          (coordinateUnlinkExteriorOneHandleResidual
            (coordinateUnlinkExteriorOneHandleBasePowerMap m
              (coordinateUnlinkExteriorOneHandleDeckTranslation m u x))) =
      ((u.1 : ℂˣ) : ℂ) *
        (unlinkUnitCircleComplex x.1 *
          coordinateUnlinkExteriorOneHandleResidualPowerRoot m
            (coordinateUnlinkExteriorOneHandleResidual
              (coordinateUnlinkExteriorOneHandleBasePowerMap m x)))
    rw [coordinateUnlinkExteriorOneHandleBasePowerMap_deckTranslation]
    exact mul_assoc _ _ _

/-- Source translation with the common additive `ZMod m` deck index. -/
def coordinateUnlinkExteriorOneHandleDeckTranslationZMod
    (m : ℕ) [NeZero m] (a : ZMod m) (x : OneHandlePiece) : OneHandlePiece :=
  coordinateUnlinkExteriorOneHandleDeckTranslation m
    (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)) x

@[simp]
theorem unlinkUnitCircleComplex_oneHandleDeckTranslationZMod
    (m : ℕ) [NeZero m] (a : ZMod m) (x : OneHandlePiece) :
    unlinkUnitCircleComplex
        (coordinateUnlinkExteriorOneHandleDeckTranslationZMod m a x).1 =
      Complex.exp (2 * Real.pi * Complex.I * a.val / m) *
        unlinkUnitCircleComplex x.1 := by
  change unlinkUnitCircleComplex
      (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m
        (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)) x.1) = _
  rw [unlinkUnitCircleComplex_circleDeckTranslation,
    standardRootsOfUnityZModMulEquiv_val]

/-- The `ZMod m`-indexed source translation corresponds to the same standard index on the
restricted pullback deck action. -/
@[simp]
theorem coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph_deckTranslationZMod
    (m : ℕ) [NeZero m] (a : ZMod m) (x : OneHandlePiece) :
    coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m
        (coordinateUnlinkExteriorOneHandleDeckTranslationZMod m a x) =
      coordinateUnlinkExteriorOneHandlePowerDeckHomeomorph m
        (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a))
        (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m x) :=
  coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph_deckTranslation m _ x

/-- The same equivariance law expressed directly using the standard `ZMod m` deck homomorphism. -/
@[simp]
theorem coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph_deckZModHom
    (m : ℕ) [NeZero m] (a : ZMod m) (x : OneHandlePiece) :
    coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m
        (coordinateUnlinkExteriorOneHandleDeckTranslationZMod m a x) =
      coordinateUnlinkExteriorOneHandlePowerDeckZModHom m
        (Multiplicative.ofAdd a)
        (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m x) :=
  coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph_deckTranslationZMod m a x

end SplittingSpheres
