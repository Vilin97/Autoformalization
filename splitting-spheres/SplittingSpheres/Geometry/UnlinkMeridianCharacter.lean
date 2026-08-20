/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.BranchLogRoot
public import SplittingSpheres.Geometry.UnlinkExteriorCollar
public import SplittingSpheres.Geometry.UnlinkPowerDeck

/-!
# Coordinate meridians and the unlink power cover

The inner boundary of the concrete radius-`1/8` unlink collar gives a preferred meridian about
each frozen component.  This file packages these circles in the strict unlink complement and
computes their exact value under the complex normal coordinate used to define the power
pullback cover.

The component numbered `1` is the component detected by that cover: its meridian maps to the
radius-`1/8` circle about zero.  The component numbered `0` maps to the radius-`1/8` circle about
`-1`.  The final section records the cover-theoretic conclusion that can be proved without a
separate winding-number API.  It does not identify the fundamental group of the unlink
complement with a two-generator rose, nor prove that these two meridians generate it; that
topological comparison is a separate input needed to promote the endpoint calculations to a
global rose character.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped ContDiff Manifold unitInterval

namespace SplittingSpheres

/-! ## The two explicit meridian families -/

/-- Regard the project unit circle in the normal Euclidean plane as a complex unit. -/
def unlinkUnitCircleComplex (u : Sphere 1) : ℂ :=
  unlinkNormalPlaneToComplex u.1

@[simp]
theorem unlinkUnitCircleComplex_apply (u : Sphere 1) :
    unlinkUnitCircleComplex u =
      (u.1 0 : ℂ) + (u.1 1 : ℂ) * Complex.I := by
  simp [unlinkUnitCircleComplex, unlinkNormalPlaneToComplex,
    Complex.equivRealProdCLM_symm_apply]

/-- The normal-plane/complex identification preserves the Euclidean norm. -/
theorem norm_unlinkNormalPlaneToComplex (v : UnlinkNormalPlane) :
    ‖unlinkNormalPlaneToComplex v‖ = ‖v‖ := by
  have hc : ‖unlinkNormalPlaneToComplex v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [unlinkNormalPlaneToComplex, Complex.equivRealProdCLM_symm_apply]
    ring
  have hv : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
  nlinarith [norm_nonneg (unlinkNormalPlaneToComplex v), norm_nonneg v]

@[simp]
theorem norm_unlinkUnitCircleComplex (u : Sphere 1) :
    ‖unlinkUnitCircleComplex u‖ = 1 := by
  rw [unlinkUnitCircleComplex, norm_unlinkNormalPlaneToComplex]
  exact mem_sphere_zero_iff_norm.mp u.2

theorem unlinkUnitCircleComplex_ne_zero (u : Sphere 1) :
    unlinkUnitCircleComplex u ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [norm_unlinkUnitCircleComplex]; norm_num)

/-- The coordinate inverse from the complex plane to the project's normal Euclidean plane. -/
def complexToUnlinkNormalPlane (z : ℂ) : UnlinkNormalPlane :=
  WithLp.toLp 2 ![z.re, z.im]

@[simp]
theorem unlinkNormalPlaneToComplex_complexToUnlinkNormalPlane (z : ℂ) :
    unlinkNormalPlaneToComplex (complexToUnlinkNormalPlane z) = z := by
  apply Complex.ext
  · simp [unlinkNormalPlaneToComplex, complexToUnlinkNormalPlane,
      Complex.equivRealProdCLM_symm_apply]
  · simp [unlinkNormalPlaneToComplex, complexToUnlinkNormalPlane,
      Complex.equivRealProdCLM_symm_apply]

theorem norm_complexToUnlinkNormalPlane (z : ℂ) :
    ‖complexToUnlinkNormalPlane z‖ = ‖z‖ := by
  rw [← norm_unlinkNormalPlaneToComplex,
    unlinkNormalPlaneToComplex_complexToUnlinkNormalPlane]

/-- The positively oriented complex exponential, regarded as a point of the project's
Euclidean `Sphere 1`. -/
def unlinkMeridianCirclePoint (θ : ℝ) : Sphere 1 :=
  ⟨complexToUnlinkNormalPlane (Complex.exp (θ * Complex.I)), by
    rw [mem_sphere_zero_iff_norm, norm_complexToUnlinkNormalPlane]
    simp⟩

@[simp]
theorem unlinkUnitCircleComplex_circlePoint (θ : ℝ) :
    unlinkUnitCircleComplex (unlinkMeridianCirclePoint θ) =
      Complex.exp (θ * Complex.I) :=
  unlinkNormalPlaneToComplex_complexToUnlinkNormalPlane _

theorem continuous_unlinkMeridianCirclePoint :
    Continuous unlinkMeridianCirclePoint := by
  apply Continuous.subtype_mk
  unfold complexToUnlinkNormalPlane
  fun_prop

/-- The inner radius point in the concrete half-open collar. -/
abbrev coordinateUnlinkExteriorEighthCollarInnerRadius :
    CoordinateUnlinkExteriorEighthCollarRadius :=
  unlinkExteriorCollarInnerRadius (1 / 8 : ℝ) (1 / 4 : ℝ)

/-- The radius-`1/8` meridian of component `i`, at a chosen point of its `S²` factor, bundled
as a point of the strict coordinate-unlink complement. -/
def standardUnlinkMeridian (i : Fin 2) (x : Sphere 2) (u : Sphere 1) :
    StandardUnlinkComplement :=
  coordinateUnlinkExteriorToComplement (r := (1 / 8 : ℝ)) (by norm_num)
    ⟨(standardUnlinkExteriorEighthCollarHomeomorph i
      (x, (u, coordinateUnlinkExteriorEighthCollarInnerRadius))).1,
      (standardUnlinkExteriorEighthCollarHomeomorph i
        (x, (u, coordinateUnlinkExteriorEighthCollarInnerRadius))).2.1⟩

@[simp]
theorem standardUnlinkMeridian_coe (i : Fin 2) (x : Sphere 2) (u : Sphere 1) :
    (standardUnlinkMeridian i x u : Sphere 4) =
      standardUnlinkExteriorCollarBoundaryMap i (r := (1 / 8 : ℝ))
        (R := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (x, u) :=
by
  simp only [standardUnlinkMeridian, coordinateUnlinkExteriorToComplement_coe]
  rfl

theorem continuous_standardUnlinkMeridian (i : Fin 2) (x : Sphere 2) :
    Continuous (standardUnlinkMeridian i x) := by
  apply Continuous.subtype_mk
  have hin : Continuous (fun u : Sphere 1 ↦ (x, u)) :=
    continuous_const.prodMk continuous_id
  have hboundary : Continuous (fun u : Sphere 1 ↦
      standardUnlinkExteriorCollarBoundaryMap i (r := (1 / 8 : ℝ))
        (R := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (x, u)) :=
    (contMDiff_standardUnlinkExteriorCollarBoundaryMap i (r := (1 / 8 : ℝ))
      (R := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).continuous.comp hin
  exact hboundary.congr fun u ↦ (standardUnlinkMeridian_coe i x u).symm

/-- For every selected `S²` point, the resulting meridian is a smooth circle in the strict
unlink complement. -/
theorem contMDiff_standardUnlinkMeridian (i : Fin 2) (x : Sphere 2) :
    ContMDiff (𝓡 1) (𝓡 4) ∞ (standardUnlinkMeridian i x) := by
  rw [← ContMDiff.subtypeVal_comp_iff standardUnlinkComplementOpens]
  have hin : ContMDiff (𝓡 1)
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))) ∞
      (fun u : Sphere 1 ↦ (x, u)) :=
    contMDiff_const.prodMk contMDiff_id
  exact ((contMDiff_standardUnlinkExteriorCollarBoundaryMap i
    (r := (1 / 8 : ℝ)) (R := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).comp hin).congr
      fun u ↦ (standardUnlinkMeridian_coe i x u).symm

/-- The ambient normal coordinate of a meridian is exactly `cᵢ + (1/8)u`. -/
@[simp]
theorem standardUnlinkNormalProjection_standardUnlinkMeridian
    (i : Fin 2) (x : Sphere 2) (u : Sphere 1) :
    standardUnlinkNormalProjection (standardUnlinkMeridian i x u).1 =
      standardUnlinkNormalCenter i + (1 / 8 : ℝ) • u.1 := by
  rw [standardUnlinkMeridian_coe]
  change standardUnlinkNormalProjection
      (standardUnlinkExteriorCollarHomeomorph i (r := (1 / 8 : ℝ))
        (R := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
        (x, (u, unlinkExteriorCollarInnerRadius (1 / 8 : ℝ) (1 / 4 : ℝ)))).1 = _
  rw [standardUnlinkNormalProjection_exteriorCollarHomeomorph,
    unlinkExteriorCollarInnerRadius_value]

/-- The two normal centers differ by the real complex number `-1`, with the sign dictated by
component `0` lying at `x₃=-1/2` and component `1` at `x₃=1/2`. -/
theorem unlinkNormalPlaneToComplex_center_zero_sub_center_one :
    unlinkNormalPlaneToComplex
      (standardUnlinkNormalCenter 0 - standardUnlinkNormalCenter 1) = -1 := by
  simp [unlinkNormalPlaneToComplex, standardUnlinkNormalCenter,
    standardUnlinkHeight, Complex.equivRealProdCLM_symm_apply]
  norm_num

/-- The right-normal character on the right meridian is the positively oriented radius-`1/8`
unit circle. -/
@[simp]
theorem standardUnlinkRightDisplacementComplex_rightMeridian
    (x : Sphere 2) (u : Sphere 1) :
    standardUnlinkRightDisplacementComplex (standardUnlinkMeridian 1 x u).1 =
      (1 / 8 : ℝ) • unlinkUnitCircleComplex u := by
  rw [standardUnlinkRightDisplacementComplex, unlinkUnitCircleComplex,
    standardUnlinkNormalProjection_standardUnlinkMeridian]
  simp only [add_sub_cancel_left]
  simp [unlinkNormalPlaneToComplex, Complex.equivRealProdCLM_symm_apply]
  ring

/-- The same character on the left meridian is the radius-`1/8` circle centered at `-1`. -/
@[simp]
theorem standardUnlinkRightDisplacementComplex_leftMeridian
    (x : Sphere 2) (u : Sphere 1) :
    standardUnlinkRightDisplacementComplex (standardUnlinkMeridian 0 x u).1 =
      (-1 : ℂ) + (1 / 8 : ℝ) • unlinkUnitCircleComplex u := by
  rw [standardUnlinkRightDisplacementComplex, unlinkUnitCircleComplex,
    standardUnlinkNormalProjection_standardUnlinkMeridian]
  rw [show standardUnlinkNormalCenter 0 + (1 / 8 : ℝ) • u.1 -
      standardUnlinkNormalCenter 1 =
        (standardUnlinkNormalCenter 0 - standardUnlinkNormalCenter 1) +
          (1 / 8 : ℝ) • u.1 by abel]
  simp [unlinkNormalPlaneToComplex, standardUnlinkNormalCenter,
    standardUnlinkHeight, Complex.equivRealProdCLM_symm_apply]
  ring

/-! ## Loops and their exact character values -/

/-- Traverse the selected meridian once counterclockwise over the unit interval. -/
def standardUnlinkMeridianLoop (i : Fin 2) (x : Sphere 2) (t : I) :
    StandardUnlinkComplement :=
  standardUnlinkMeridian i x
    (unlinkMeridianCirclePoint (2 * Real.pi * (t : ℝ)))

@[simp]
theorem standardUnlinkMeridianLoop_zero (i : Fin 2) (x : Sphere 2) :
    standardUnlinkMeridianLoop i x 0 = standardUnlinkMeridian i x
      (unlinkMeridianCirclePoint 0) := by
  unfold standardUnlinkMeridianLoop
  simp

@[simp]
theorem standardUnlinkMeridianLoop_one (i : Fin 2) (x : Sphere 2) :
    standardUnlinkMeridianLoop i x 1 = standardUnlinkMeridian i x
      (unlinkMeridianCirclePoint 0) := by
  unfold standardUnlinkMeridianLoop
  apply congrArg (standardUnlinkMeridian i x)
  apply Subtype.ext
  simp [unlinkMeridianCirclePoint, Complex.exp_two_pi_mul_I]

theorem continuous_standardUnlinkMeridianLoop (i : Fin 2) (x : Sphere 2) :
    Continuous (standardUnlinkMeridianLoop i x) := by
  apply Continuous.subtype_mk
  have hangle : Continuous (fun t : I ↦ 2 * Real.pi * (t : ℝ)) := by
    fun_prop
  have hin : Continuous (fun t : I ↦ (x,
      unlinkMeridianCirclePoint (2 * Real.pi * (t : ℝ)))) := by
    exact continuous_const.prodMk (continuous_unlinkMeridianCirclePoint.comp hangle)
  have hboundary : Continuous (fun t : I ↦
      standardUnlinkExteriorCollarBoundaryMap i (r := (1 / 8 : ℝ))
        (R := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
          (x, unlinkMeridianCirclePoint (2 * Real.pi * (t : ℝ)))) :=
    (contMDiff_standardUnlinkExteriorCollarBoundaryMap i (r := (1 / 8 : ℝ))
      (R := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).continuous.comp hin
  exact hboundary.congr fun t ↦ (standardUnlinkMeridian_coe _ _ _).symm

@[simp]
theorem standardUnlinkRightDisplacementComplex_rightMeridianLoop
    (x : Sphere 2) (t : I) :
    standardUnlinkRightDisplacementComplex (standardUnlinkMeridianLoop 1 x t).1 =
      (1 / 8 : ℝ) •
        Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I) := by
  change standardUnlinkRightDisplacementComplex
    (standardUnlinkMeridian 1 x
      (unlinkMeridianCirclePoint (2 * Real.pi * (t : ℝ)))).1 = _
  rw [standardUnlinkRightDisplacementComplex_rightMeridian,
    unlinkUnitCircleComplex_circlePoint]
  congr 2
  push_cast
  rfl

@[simp]
theorem standardUnlinkRightDisplacementComplex_leftMeridianLoop
    (x : Sphere 2) (t : I) :
    standardUnlinkRightDisplacementComplex (standardUnlinkMeridianLoop 0 x t).1 =
      (-1 : ℂ) + (1 / 8 : ℝ) •
        Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I) := by
  change standardUnlinkRightDisplacementComplex
    (standardUnlinkMeridian 0 x
      (unlinkMeridianCirclePoint (2 * Real.pi * (t : ℝ)))).1 = _
  rw [standardUnlinkRightDisplacementComplex_leftMeridian,
    unlinkUnitCircleComplex_circlePoint]
  congr 2
  push_cast
  rfl

/-! ## An explicit lift of the right meridian -/

/-- A selected nonzero `m`th root of the positive real number `1/8`.  No choice of argument is
needed by the monodromy calculation below: any initial root acquires the same root-of-unity
factor after one turn. -/
def unlinkEighthPowerRootUnit (m : ℕ) [NeZero m] : ℂˣ :=
  Classical.choose ((Complex.isQuotientCoveringMap_npow m).surjective
    (Units.mk0 (1 / 8 : ℂ) (by norm_num)))

@[simp]
theorem unlinkEighthPowerRootUnit_pow (m : ℕ) [NeZero m] :
    ((unlinkEighthPowerRootUnit m : ℂˣ) : ℂ) ^ m = (1 / 8 : ℂ) := by
  have h := Classical.choose_spec
    ((Complex.isQuotientCoveringMap_npow m).surjective
      (Units.mk0 (1 / 8 : ℂ) (by norm_num)))
  exact congrArg Units.val h

/-- The positive primitive `m`th root of unity which is picked up by one counterclockwise turn
of the right meridian. -/
def standardUnlinkPowerDeckGenerator (m : ℕ) [NeZero m] : rootsOfUnity m ℂ :=
  ⟨Units.mk0 (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (m : ℂ)))
      (Complex.exp_ne_zero _),
    (mem_rootsOfUnity' m _).mpr
      (Complex.isPrimitiveRoot_exp m (NeZero.ne m)).pow_eq_one⟩

@[simp]
theorem standardUnlinkPowerDeckGenerator_coe (m : ℕ) [NeZero m] :
    (((standardUnlinkPowerDeckGenerator m).1 : ℂˣ) : ℂ) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (m : ℂ)) :=
  rfl

theorem standardUnlinkPowerDeckGenerator_isPrimitiveRoot (m : ℕ) [NeZero m] :
    IsPrimitiveRoot
      ((((standardUnlinkPowerDeckGenerator m).1 : ℂˣ) : ℂ)) m :=
  Complex.isPrimitiveRoot_exp m (NeZero.ne m)

/-- The power coordinate of the explicit lift of the right meridian. -/
def standardUnlinkRightMeridianLiftPowerCoordinate (m : ℕ) [NeZero m] (t : I) :
    {z : ℂ // z ≠ 0} :=
  ⟨((unlinkEighthPowerRootUnit m : ℂˣ) : ℂ) *
      Complex.exp
        ((2 * (Real.pi : ℂ) * Complex.I / (m : ℂ)) * (t : ℝ)),
    mul_ne_zero (Units.ne_zero _) (Complex.exp_ne_zero _)⟩

@[simp]
theorem standardUnlinkRightMeridianLiftPowerCoordinate_pow
    (m : ℕ) [NeZero m] (t : I) :
    ((standardUnlinkRightMeridianLiftPowerCoordinate m t : {z : ℂ // z ≠ 0}) : ℂ) ^ m =
      (1 / 8 : ℝ) •
        Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I) := by
  change ((((unlinkEighthPowerRootUnit m : ℂˣ) : ℂ) *
      Complex.exp
        ((2 * (Real.pi : ℂ) * Complex.I / (m : ℂ)) * (t : ℝ))) ^ m) = _
  rw [mul_pow, unlinkEighthPowerRootUnit_pow, ← Complex.exp_nat_mul]
  rw [Complex.real_smul]
  push_cast
  change (1 / 8 : ℂ) *
      Complex.exp ((m : ℂ) *
        ((2 * (Real.pi : ℂ) * Complex.I / (m : ℂ)) * (t : ℝ))) =
    (1 / 8 : ℂ) *
      Complex.exp ((2 * (Real.pi : ℂ) * (t : ℝ)) * Complex.I)
  congr 2
  field_simp [NeZero.ne m]

theorem continuous_standardUnlinkRightMeridianLiftPowerCoordinate
    (m : ℕ) [NeZero m] :
    Continuous (standardUnlinkRightMeridianLiftPowerCoordinate m) := by
  apply Continuous.subtype_mk
  fun_prop

/-- The counterclockwise right meridian lifted to the raw `m`-power pullback, starting at the
selected root of `1/8`. -/
def standardUnlinkRightMeridianLift (m : ℕ) [NeZero m] (x : Sphere 2) (t : I) :
    StandardUnlinkPowerPullback m :=
  ⟨(standardUnlinkMeridianLoop 1 x t,
      standardUnlinkRightMeridianLiftPowerCoordinate m t), by
    apply Subtype.ext
    change standardUnlinkRightDisplacementComplex
        (standardUnlinkMeridianLoop 1 x t).1 =
      (standardUnlinkRightMeridianLiftPowerCoordinate m t : ℂ) ^ m
    rw [standardUnlinkRightDisplacementComplex_rightMeridianLoop,
      standardUnlinkRightMeridianLiftPowerCoordinate_pow]⟩

@[simp]
theorem standardUnlinkPowerPullbackProj_rightMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) (t : I) :
    standardUnlinkPowerPullbackProj m (standardUnlinkRightMeridianLift m x t) =
      standardUnlinkMeridianLoop 1 x t :=
  rfl

theorem continuous_standardUnlinkRightMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) :
    Continuous (standardUnlinkRightMeridianLift m x) := by
  apply Continuous.subtype_mk
  exact (continuous_standardUnlinkMeridianLoop 1 x).prodMk
    (continuous_standardUnlinkRightMeridianLiftPowerCoordinate m)

/-- Exact monodromy endpoint law: one positive right-meridian turn advances the explicit lift by
the positive primitive deck generator. -/
theorem standardUnlinkRightMeridianLift_one_eq_generator_smul_zero
    (m : ℕ) [NeZero m] (x : Sphere 2) :
    standardUnlinkRightMeridianLift m x 1 =
      standardUnlinkPowerDeckGenerator m •
        standardUnlinkRightMeridianLift m x 0 := by
  rw [standardUnlinkPowerPullback_smul_apply]
  apply Subtype.ext
  apply Prod.ext
  · change standardUnlinkMeridianLoop 1 x 1 = standardUnlinkMeridianLoop 1 x 0
    simp
  · apply Subtype.ext
    rw [standardUnlinkPowerDeckMap_powerCoordinate]
    simp only [standardUnlinkRightMeridianLift,
      standardUnlinkRightMeridianLiftPowerCoordinate,
      standardUnlinkPowerDeckGenerator_coe]
    simp only [Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one,
      Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero]
    exact mul_comm _ _

/-! ## A closed lift of the left meridian -/

/-- The disk which contains the entire left-meridian character circle and misses zero. -/
def unlinkLeftCharacterBall : Set ℂ :=
  ball (-1 : ℂ) (1 / 4 : ℝ)

theorem isOpen_unlinkLeftCharacterBall : IsOpen unlinkLeftCharacterBall :=
  isOpen_ball

theorem isSimplyConnected_unlinkLeftCharacterBall :
    IsSimplyConnected unlinkLeftCharacterBall := by
  let _ : ContractibleSpace unlinkLeftCharacterBall :=
    (convex_ball (-1 : ℂ) (1 / 4 : ℝ)).contractibleSpace
      (nonempty_ball.mpr (by norm_num))
  change SimplyConnectedSpace unlinkLeftCharacterBall
  infer_instance

theorem zero_not_mem_unlinkLeftCharacterBall :
    (0 : ℂ) ∉ unlinkLeftCharacterBall := by
  norm_num [unlinkLeftCharacterBall, mem_ball, Complex.dist_eq]

theorem zero_not_mem_image_id_unlinkLeftCharacterBall :
    (0 : ℂ) ∉ id '' unlinkLeftCharacterBall := by
  simpa only [image_id] using zero_not_mem_unlinkLeftCharacterBall

/-- A continuous branch of the `m`th root exists on a disk containing the complete left
character circle. -/
theorem exists_unlinkLeftCharacterPowerRoot (m : ℕ) [NeZero m] :
    ∃ f : ℂ → ℂ, ContinuousOn f unlinkLeftCharacterBall ∧
      ∀ z : ℂ, f z ^ m = z := by
  simpa only [id_eq] using
    (Complex.exists_continuousOn_pow_eq
      isSimplyConnected_unlinkLeftCharacterBall isOpen_unlinkLeftCharacterBall
      (g := id) continuousOn_id zero_not_mem_image_id_unlinkLeftCharacterBall
      (NeZero.ne m))

/-- A selected continuous `m`th-root branch on `unlinkLeftCharacterBall`. -/
def unlinkLeftCharacterPowerRoot (m : ℕ) [NeZero m] : ℂ → ℂ :=
  Classical.choose (exists_unlinkLeftCharacterPowerRoot m)

theorem continuousOn_unlinkLeftCharacterPowerRoot (m : ℕ) [NeZero m] :
    ContinuousOn (unlinkLeftCharacterPowerRoot m) unlinkLeftCharacterBall :=
  (Classical.choose_spec (exists_unlinkLeftCharacterPowerRoot m)).1

@[simp]
theorem unlinkLeftCharacterPowerRoot_pow (m : ℕ) [NeZero m] (z : ℂ) :
    unlinkLeftCharacterPowerRoot m z ^ m = z :=
  (Classical.choose_spec (exists_unlinkLeftCharacterPowerRoot m)).2 z

theorem standardUnlinkRightDisplacementComplex_leftMeridian_mem_characterBall
    (x : Sphere 2) (u : Sphere 1) :
    standardUnlinkRightDisplacementComplex (standardUnlinkMeridian 0 x u).1 ∈
      unlinkLeftCharacterBall := by
  rw [standardUnlinkRightDisplacementComplex_leftMeridian]
  change dist ((-1 : ℂ) + (1 / 8 : ℝ) • unlinkUnitCircleComplex u) (-1) < 1 / 4
  have hsub : (-1 : ℂ) + (1 / 8 : ℝ) • unlinkUnitCircleComplex u - (-1) =
      (1 / 8 : ℝ) • unlinkUnitCircleComplex u := by ring
  rw [Complex.dist_eq, hsub, norm_smul, norm_unlinkUnitCircleComplex]
  norm_num

theorem continuous_standardUnlinkRightDisplacementComplex_leftMeridian
    (x : Sphere 2) :
    Continuous (fun u : Sphere 1 ↦
      standardUnlinkRightDisplacementComplex (standardUnlinkMeridian 0 x u).1) :=
  continuous_standardUnlinkRightDisplacementComplex.comp
    (continuous_subtype_val.comp (continuous_standardUnlinkMeridian 0 x))

/-- The selected root coordinate above the whole left meridian circle. -/
def standardUnlinkLeftMeridianLiftPowerCoordinate
    (m : ℕ) [NeZero m] (x : Sphere 2) (u : Sphere 1) : {z : ℂ // z ≠ 0} :=
  ⟨unlinkLeftCharacterPowerRoot m
      (standardUnlinkRightDisplacementComplex (standardUnlinkMeridian 0 x u).1), by
    intro hz
    have hp := unlinkLeftCharacterPowerRoot_pow m
      (standardUnlinkRightDisplacementComplex (standardUnlinkMeridian 0 x u).1)
    rw [hz, zero_pow (NeZero.ne m)] at hp
    exact standardUnlinkRightDisplacementComplex_ne_zero
      (standardUnlinkMeridian 0 x u) hp.symm⟩

@[simp]
theorem standardUnlinkLeftMeridianLiftPowerCoordinate_pow
    (m : ℕ) [NeZero m] (x : Sphere 2) (u : Sphere 1) :
    (standardUnlinkLeftMeridianLiftPowerCoordinate m x u : ℂ) ^ m =
      standardUnlinkRightDisplacementComplex (standardUnlinkMeridian 0 x u).1 :=
  unlinkLeftCharacterPowerRoot_pow m _

theorem continuous_standardUnlinkLeftMeridianLiftPowerCoordinate
    (m : ℕ) [NeZero m] (x : Sphere 2) :
    Continuous (standardUnlinkLeftMeridianLiftPowerCoordinate m x) := by
  apply Continuous.subtype_mk
  exact (continuousOn_unlinkLeftCharacterPowerRoot m).comp_continuous
    (continuous_standardUnlinkRightDisplacementComplex_leftMeridian x)
    (standardUnlinkRightDisplacementComplex_leftMeridian_mem_characterBall x)

/-- The complete left meridian circle lifted through the `m`-power pullback. -/
def standardUnlinkLeftMeridianLiftCircle
    (m : ℕ) [NeZero m] (x : Sphere 2) (u : Sphere 1) :
    StandardUnlinkPowerPullback m :=
  ⟨(standardUnlinkMeridian 0 x u,
      standardUnlinkLeftMeridianLiftPowerCoordinate m x u), by
    apply Subtype.ext
    change standardUnlinkRightDisplacementComplex
        (standardUnlinkMeridian 0 x u).1 =
      (standardUnlinkLeftMeridianLiftPowerCoordinate m x u : ℂ) ^ m
    exact (standardUnlinkLeftMeridianLiftPowerCoordinate_pow m x u).symm⟩

@[simp]
theorem standardUnlinkPowerPullbackProj_leftMeridianLiftCircle
    (m : ℕ) [NeZero m] (x : Sphere 2) (u : Sphere 1) :
    standardUnlinkPowerPullbackProj m
      (standardUnlinkLeftMeridianLiftCircle m x u) =
        standardUnlinkMeridian 0 x u :=
  rfl

theorem continuous_standardUnlinkLeftMeridianLiftCircle
    (m : ℕ) [NeZero m] (x : Sphere 2) :
    Continuous (standardUnlinkLeftMeridianLiftCircle m x) := by
  apply Continuous.subtype_mk
  exact (continuous_standardUnlinkMeridian 0 x).prodMk
    (continuous_standardUnlinkLeftMeridianLiftPowerCoordinate m x)

/-- The resulting unit-interval lift of the left meridian. -/
def standardUnlinkLeftMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) (t : I) :
    StandardUnlinkPowerPullback m :=
  standardUnlinkLeftMeridianLiftCircle m x
    (unlinkMeridianCirclePoint (2 * Real.pi * (t : ℝ)))

@[simp]
theorem standardUnlinkPowerPullbackProj_leftMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) (t : I) :
    standardUnlinkPowerPullbackProj m (standardUnlinkLeftMeridianLift m x t) =
      standardUnlinkMeridianLoop 0 x t :=
  rfl

theorem continuous_standardUnlinkLeftMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) :
    Continuous (standardUnlinkLeftMeridianLift m x) := by
  have hangle : Continuous (fun t : I ↦ 2 * Real.pi * (t : ℝ)) := by
    fun_prop
  exact (continuous_standardUnlinkLeftMeridianLiftCircle m x).comp
    (continuous_unlinkMeridianCirclePoint.comp hangle)

/-- Exact endpoint law for the left meridian: its selected lift closes, hence has the trivial
deck element. -/
@[simp]
theorem standardUnlinkLeftMeridianLift_one_eq_zero
    (m : ℕ) [NeZero m] (x : Sphere 2) :
    standardUnlinkLeftMeridianLift m x 1 =
      standardUnlinkLeftMeridianLift m x 0 := by
  unfold standardUnlinkLeftMeridianLift
  congr 1
  apply Subtype.ext
  simp [unlinkMeridianCirclePoint, Complex.exp_two_pi_mul_I]

theorem standardUnlinkLeftMeridianLift_one_eq_one_smul_zero
    (m : ℕ) [NeZero m] (x : Sphere 2) :
    standardUnlinkLeftMeridianLift m x 1 =
      (1 : rootsOfUnity m ℂ) • standardUnlinkLeftMeridianLift m x 0 := by
  simp

end SplittingSpheres
