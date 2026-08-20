/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.BranchLogRoot
public import SplittingSpheres.Geometry.UnlinkMeridianDeckIndex
public import SplittingSpheres.Handlebody.CoordinateExteriorCharacter
public import SplittingSpheres.Handlebody.CoordinateExteriorPowerDeck

/-!
# Monodromy of the one-handle core circle

On the core circle of the whole `S¹ × B³` face, the power-cover character is
`exp(2πit·I) - 1/2`.  We factor this as

`exp(2πit·I) * (1 - (1/2) exp(-2πit·I))`.

The second factor stays in a simply connected disk avoiding zero and therefore has a continuous
`m`th-root branch which closes after one turn.  The first factor contributes exactly the positive
standard deck generator.  This gives an explicit lifted core loop with `ZMod m` endpoint index
`1`, matching the advancing edge of the cyclic rose.

This is a loop-level calculation only, not a fundamental-group or graph-thickening theorem.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped unitInterval

namespace SplittingSpheres

/-- Traverse the core circle of the one-handle face once in the positive complex direction. -/
def coordinateUnlinkExteriorOneHandleCoreLoop (t : I) :
    CoordinateUnlinkExteriorPushout oneEighth_lt_sphereHandleRadius_sub_half :=
  coordinateUnlinkExteriorPushoutOneHandleInclusion
    (coordinateUnlinkExteriorOneHandleCoreCircle
      (unlinkMeridianCirclePoint (2 * Real.pi * (t : ℝ))))

theorem continuous_coordinateUnlinkExteriorOneHandleCoreLoop :
    Continuous coordinateUnlinkExteriorOneHandleCoreLoop := by
  have hangle : Continuous (fun t : I ↦ 2 * Real.pi * (t : ℝ)) := by
    fun_prop
  apply coordinateUnlinkExteriorPushoutOneHandleInclusion.continuous.comp
  unfold coordinateUnlinkExteriorOneHandleCoreCircle
  exact (continuous_unlinkMeridianCirclePoint.comp hangle).prodMk continuous_const

@[simp]
theorem coordinateUnlinkExteriorOneHandleCoreLoop_one_eq_zero :
    coordinateUnlinkExteriorOneHandleCoreLoop 1 =
      coordinateUnlinkExteriorOneHandleCoreLoop 0 := by
  unfold coordinateUnlinkExteriorOneHandleCoreLoop
  congr 2
  apply Subtype.ext
  simp [unlinkMeridianCirclePoint, Complex.exp_two_pi_mul_I]

/-- Exact complex character of the positive one-handle core loop. -/
@[simp]
theorem coordinateUnlinkExteriorPushoutRightNormalMap_oneHandleCoreLoop
    (t : I) :
    (coordinateUnlinkExteriorPushoutRightNormalMap
        (coordinateUnlinkExteriorOneHandleCoreLoop t) : ℂ) =
      Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I) - (1 / 2 : ℂ) := by
  rw [coordinateUnlinkExteriorOneHandleCoreLoop,
    coordinateUnlinkExteriorPushoutRightNormalMap_oneHandleCoreCircle,
    unlinkUnitCircleComplex_circlePoint]
  push_cast
  rfl

/-! ## A closing root branch for the residual factor -/

/-- A disk containing the residual loop `1 - (1/2)e^{-2πitI}` and avoiding zero. -/
def oneHandleCoreResidualBall : Set ℂ :=
  ball (1 : ℂ) (3 / 4 : ℝ)

theorem isOpen_oneHandleCoreResidualBall : IsOpen oneHandleCoreResidualBall :=
  isOpen_ball

theorem isSimplyConnected_oneHandleCoreResidualBall :
    IsSimplyConnected oneHandleCoreResidualBall := by
  let _ : ContractibleSpace oneHandleCoreResidualBall :=
    (convex_ball (1 : ℂ) (3 / 4 : ℝ)).contractibleSpace
      (nonempty_ball.mpr (by norm_num))
  change SimplyConnectedSpace oneHandleCoreResidualBall
  infer_instance

theorem zero_not_mem_oneHandleCoreResidualBall :
    (0 : ℂ) ∉ oneHandleCoreResidualBall := by
  norm_num [oneHandleCoreResidualBall, mem_ball, Complex.dist_eq]

theorem zero_not_mem_image_id_oneHandleCoreResidualBall :
    (0 : ℂ) ∉ id '' oneHandleCoreResidualBall := by
  simpa only [image_id] using zero_not_mem_oneHandleCoreResidualBall

theorem exists_oneHandleCoreResidualPowerRoot (m : ℕ) [NeZero m] :
    ∃ f : ℂ → ℂ, ContinuousOn f oneHandleCoreResidualBall ∧
      ∀ z : ℂ, f z ^ m = z := by
  simpa only [id_eq] using
    (Complex.exists_continuousOn_pow_eq
      isSimplyConnected_oneHandleCoreResidualBall isOpen_oneHandleCoreResidualBall
      (g := id) continuousOn_id zero_not_mem_image_id_oneHandleCoreResidualBall
      (NeZero.ne m))

/-- A selected continuous root branch for the residual factor. -/
def oneHandleCoreResidualPowerRoot (m : ℕ) [NeZero m] : ℂ → ℂ :=
  Classical.choose (exists_oneHandleCoreResidualPowerRoot m)

theorem continuousOn_oneHandleCoreResidualPowerRoot (m : ℕ) [NeZero m] :
    ContinuousOn (oneHandleCoreResidualPowerRoot m) oneHandleCoreResidualBall :=
  (Classical.choose_spec (exists_oneHandleCoreResidualPowerRoot m)).1

@[simp]
theorem oneHandleCoreResidualPowerRoot_pow (m : ℕ) [NeZero m] (z : ℂ) :
    oneHandleCoreResidualPowerRoot m z ^ m = z :=
  (Classical.choose_spec (exists_oneHandleCoreResidualPowerRoot m)).2 z

/-- The residual factor in the core-character factorization. -/
def oneHandleCoreResidual (t : I) : ℂ :=
  1 - (1 / 2 : ℂ) *
    Complex.exp (-((2 * Real.pi * (t : ℝ)) * Complex.I))

theorem continuous_oneHandleCoreResidual : Continuous oneHandleCoreResidual := by
  unfold oneHandleCoreResidual
  fun_prop

theorem oneHandleCoreResidual_mem_ball (t : I) :
    oneHandleCoreResidual t ∈ oneHandleCoreResidualBall := by
  change dist (1 - (1 / 2 : ℂ) *
      Complex.exp (-((2 * Real.pi * (t : ℝ)) * Complex.I))) 1 < 3 / 4
  rw [Complex.dist_eq]
  have hsub : 1 - (1 / 2 : ℂ) *
      Complex.exp (-((2 * Real.pi * (t : ℝ)) * Complex.I)) - 1 =
        -(1 / 2 : ℂ) *
          Complex.exp (-((2 * Real.pi * (t : ℝ)) * Complex.I)) := by ring
  rw [hsub, norm_mul, Complex.norm_exp]
  norm_num

theorem oneHandleCoreResidual_ne_zero (t : I) : oneHandleCoreResidual t ≠ 0 := by
  intro hzero
  have hmem := oneHandleCoreResidual_mem_ball t
  rw [hzero] at hmem
  exact zero_not_mem_oneHandleCoreResidualBall hmem

/-- The character factorization used by the lift. -/
theorem oneHandleCore_character_factorization (t : I) :
    Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I) *
        oneHandleCoreResidual t =
      Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I) - (1 / 2 : ℂ) := by
  let e := Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I)
  have he : e * Complex.exp (-((2 * Real.pi * (t : ℝ)) * Complex.I)) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [oneHandleCoreResidual]
  calc
    e * (1 - (1 / 2 : ℂ) * Complex.exp
        (-((2 * Real.pi * (t : ℝ)) * Complex.I))) =
        e - (1 / 2 : ℂ) *
          (e * Complex.exp (-((2 * Real.pi * (t : ℝ)) * Complex.I))) := by ring
    _ = e - (1 / 2 : ℂ) := by rw [he]; ring

/-! ## The explicit lifted core loop -/

/-- The power coordinate of the lifted one-handle core loop. -/
def coordinateUnlinkExteriorOneHandleCoreLiftPowerCoordinate
    (m : ℕ) [NeZero m] (t : I) : {z : ℂ // z ≠ 0} :=
  ⟨Complex.exp
      ((2 * (Real.pi : ℂ) * Complex.I / (m : ℂ)) * (t : ℝ)) *
      oneHandleCoreResidualPowerRoot m (oneHandleCoreResidual t), by
    apply mul_ne_zero (Complex.exp_ne_zero _)
    intro hzero
    have hp := oneHandleCoreResidualPowerRoot_pow m (oneHandleCoreResidual t)
    rw [hzero, zero_pow (NeZero.ne m)] at hp
    exact oneHandleCoreResidual_ne_zero t hp.symm⟩

@[simp]
theorem coordinateUnlinkExteriorOneHandleCoreLiftPowerCoordinate_pow
    (m : ℕ) [NeZero m] (t : I) :
    (coordinateUnlinkExteriorOneHandleCoreLiftPowerCoordinate m t : ℂ) ^ m =
      Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I) - (1 / 2 : ℂ) := by
  change (Complex.exp
      ((2 * (Real.pi : ℂ) * Complex.I / (m : ℂ)) * (t : ℝ)) *
      oneHandleCoreResidualPowerRoot m (oneHandleCoreResidual t)) ^ m = _
  rw [mul_pow, oneHandleCoreResidualPowerRoot_pow, ← Complex.exp_nat_mul]
  have hexp : Complex.exp ((m : ℂ) *
      ((2 * (Real.pi : ℂ) * Complex.I / (m : ℂ)) * (t : ℝ))) =
      Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I) := by
    congr 1
    field_simp [NeZero.ne m]
  rw [hexp]
  exact oneHandleCore_character_factorization t

theorem continuous_coordinateUnlinkExteriorOneHandleCoreLiftPowerCoordinate
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorOneHandleCoreLiftPowerCoordinate m) := by
  apply Continuous.subtype_mk
  apply Continuous.mul
  · fun_prop
  · exact (continuousOn_oneHandleCoreResidualPowerRoot m).comp_continuous
      continuous_oneHandleCoreResidual oneHandleCoreResidual_mem_ball

/-- The one-handle core loop lifted to the power cover over the exterior pushout. -/
def coordinateUnlinkExteriorOneHandleCoreLift
    (m : ℕ) [NeZero m] (t : I) :
    CoordinateUnlinkExteriorPushoutPowerPullback m :=
  ⟨(coordinateUnlinkExteriorOneHandleCoreLoop t,
      coordinateUnlinkExteriorOneHandleCoreLiftPowerCoordinate m t), by
    apply Subtype.ext
    change (coordinateUnlinkExteriorPushoutRightNormalMap
        (coordinateUnlinkExteriorOneHandleCoreLoop t) : ℂ) =
      (coordinateUnlinkExteriorOneHandleCoreLiftPowerCoordinate m t : ℂ) ^ m
    rw [coordinateUnlinkExteriorPushoutRightNormalMap_oneHandleCoreLoop,
      coordinateUnlinkExteriorOneHandleCoreLiftPowerCoordinate_pow]⟩

@[simp]
theorem coordinateUnlinkExteriorPushoutPowerPullbackProj_oneHandleCoreLift
    (m : ℕ) [NeZero m] (t : I) :
    coordinateUnlinkExteriorPushoutPowerPullbackProj m
        (coordinateUnlinkExteriorOneHandleCoreLift m t) =
      coordinateUnlinkExteriorOneHandleCoreLoop t :=
  rfl

theorem continuous_coordinateUnlinkExteriorOneHandleCoreLift
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorOneHandleCoreLift m) := by
  apply Continuous.subtype_mk
  exact continuous_coordinateUnlinkExteriorOneHandleCoreLoop.prodMk
    (continuous_coordinateUnlinkExteriorOneHandleCoreLiftPowerCoordinate m)

theorem coordinateUnlinkExteriorOneHandleCoreLiftPowerCoordinate_one
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorOneHandleCoreLiftPowerCoordinate m 1 =
      ⟨(((standardUnlinkPowerDeckGenerator m).1 : ℂˣ) : ℂ) *
          (coordinateUnlinkExteriorOneHandleCoreLiftPowerCoordinate m 0 : ℂ),
        mul_ne_zero (Units.ne_zero _)
          (coordinateUnlinkExteriorOneHandleCoreLiftPowerCoordinate m 0).2⟩ := by
  apply Subtype.ext
  simp only [coordinateUnlinkExteriorOneHandleCoreLiftPowerCoordinate,
    standardUnlinkPowerDeckGenerator_coe, Set.Icc.coe_one, Set.Icc.coe_zero,
    Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero]
  have hres : oneHandleCoreResidual (1 : I) = oneHandleCoreResidual (0 : I) := by
    simp [oneHandleCoreResidual, Complex.exp_neg, Complex.exp_two_pi_mul_I]
  rw [hres]
  ring

/-- The positive core loop acquires the same primitive deck generator as the right meridian. -/
theorem coordinateUnlinkExteriorOneHandleCoreLift_one_eq_generator_smul_zero
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorOneHandleCoreLift m 1 =
      standardUnlinkPowerDeckGenerator m •
        coordinateUnlinkExteriorOneHandleCoreLift m 0 := by
  apply (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).injective
  rw [coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_smul]
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg coordinateUnlinkExteriorOneEighthHomeomorph
      coordinateUnlinkExteriorOneHandleCoreLoop_one_eq_zero
  · exact coordinateUnlinkExteriorOneHandleCoreLiftPowerCoordinate_one m

/-- In the common cyclic index, the positive one-handle core loop advances by `1 : ZMod m`. -/
theorem coordinateUnlinkExteriorOneHandleCoreLift_one_eq_zmodOne_smul_zero
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorOneHandleCoreLift m 1 =
      coordinateUnlinkExteriorPushoutPowerDeckZModHom m
          (Multiplicative.ofAdd (1 : ZMod m))
        (coordinateUnlinkExteriorOneHandleCoreLift m 0) := by
  rw [coordinateUnlinkExteriorOneHandleCoreLift_one_eq_generator_smul_zero,
    standardUnlinkPowerDeckGenerator_eq_standardZMod_one]
  rfl

end SplittingSpheres
