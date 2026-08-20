/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkMeridianDeckIndex
public import SplittingSpheres.Handlebody.CoordinateExteriorPowerDeck

/-!
# Meridian lifts on the coordinate-exterior pushout

The radius-`1/8` collar meridians already used in the strict unlink complement lie on the
boundary of the corresponding closed coordinate exterior.  We first retain those same points
and their explicit power lifts in the closed exterior, and then transport them through the
established homeomorphisms to the one-handle/punctured-cap pushout.

The endpoint calculations remain literal calculations for these selected paths: the right
meridian has the standard `ZMod m` index `1`, while the left meridian has index `0`.  No claim
about fundamental-group generation, a smooth structure on the pushout, or a graph thickening is
made here.
-/

@[expose] public section

noncomputable section

open Function Topology
open scoped unitInterval

namespace SplittingSpheres

/-! ## The meridians in the closed radius-`1/8` exterior -/

/-- The collar-boundary meridian, retained as a point of the closed radius-`1/8` exterior. -/
def coordinateUnlinkExteriorEighthMeridian
    (i : Fin 2) (x : Sphere 2) (u : Sphere 1) :
    CoordinateUnlinkExteriorSpace (1 / 8 : ℝ) :=
  ⟨(standardUnlinkExteriorEighthCollarHomeomorph i
      (x, (u, coordinateUnlinkExteriorEighthCollarInnerRadius))).1,
    (standardUnlinkExteriorEighthCollarHomeomorph i
      (x, (u, coordinateUnlinkExteriorEighthCollarInnerRadius))).2.1⟩

/-- Inclusion of the closed-exterior meridian is the previously defined strict-complement
meridian, with no change of parametrization. -/
@[simp]
theorem coordinateUnlinkExteriorToComplement_eighthMeridian
    (i : Fin 2) (x : Sphere 2) (u : Sphere 1) :
    coordinateUnlinkExteriorToComplement (by norm_num)
        (coordinateUnlinkExteriorEighthMeridian i x u) =
      standardUnlinkMeridian i x u :=
  rfl

theorem continuous_coordinateUnlinkExteriorEighthMeridian
    (i : Fin 2) (x : Sphere 2) :
    Continuous (coordinateUnlinkExteriorEighthMeridian i x) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp (continuous_standardUnlinkMeridian i x)).congr
    (fun _ ↦ rfl)

/-- Traverse the retained closed-exterior meridian once counterclockwise. -/
def coordinateUnlinkExteriorEighthMeridianLoop
    (i : Fin 2) (x : Sphere 2) (t : I) :
    CoordinateUnlinkExteriorSpace (1 / 8 : ℝ) :=
  coordinateUnlinkExteriorEighthMeridian i x
    (unlinkMeridianCirclePoint (2 * Real.pi * (t : ℝ)))

@[simp]
theorem coordinateUnlinkExteriorToComplement_eighthMeridianLoop
    (i : Fin 2) (x : Sphere 2) (t : I) :
    coordinateUnlinkExteriorToComplement (by norm_num)
        (coordinateUnlinkExteriorEighthMeridianLoop i x t) =
      standardUnlinkMeridianLoop i x t :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorEighthMeridianLoop_zero
    (i : Fin 2) (x : Sphere 2) :
    coordinateUnlinkExteriorEighthMeridianLoop i x 0 =
      coordinateUnlinkExteriorEighthMeridian i x (unlinkMeridianCirclePoint 0) := by
  unfold coordinateUnlinkExteriorEighthMeridianLoop
  simp

@[simp]
theorem coordinateUnlinkExteriorEighthMeridianLoop_one
    (i : Fin 2) (x : Sphere 2) :
    coordinateUnlinkExteriorEighthMeridianLoop i x 1 =
      coordinateUnlinkExteriorEighthMeridian i x (unlinkMeridianCirclePoint 0) := by
  apply Subtype.ext
  exact congrArg (fun y : StandardUnlinkComplement ↦ (y : Sphere 4))
    (standardUnlinkMeridianLoop_one i x)

theorem continuous_coordinateUnlinkExteriorEighthMeridianLoop
    (i : Fin 2) (x : Sphere 2) :
    Continuous (coordinateUnlinkExteriorEighthMeridianLoop i x) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp (continuous_standardUnlinkMeridianLoop i x)).congr
    (fun _ ↦ rfl)

/-! ## Explicit lifts in the closed exterior -/

/-- The explicit right-meridian lift, with its base point retained in the closed exterior. -/
def coordinateUnlinkExteriorEighthRightMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) (t : I) :
    CoordinateUnlinkExteriorEighthPowerPullback m :=
  ⟨(coordinateUnlinkExteriorEighthMeridianLoop 1 x t,
      standardUnlinkRightMeridianLiftPowerCoordinate m t), by
    apply Subtype.ext
    change standardUnlinkRightDisplacementComplex
        (coordinateUnlinkExteriorEighthMeridianLoop 1 x t).1 =
      (standardUnlinkRightMeridianLiftPowerCoordinate m t : ℂ) ^ m
    rw [show (coordinateUnlinkExteriorEighthMeridianLoop 1 x t).1 =
        (standardUnlinkMeridianLoop 1 x t).1 by rfl,
      standardUnlinkRightDisplacementComplex_rightMeridianLoop,
      standardUnlinkRightMeridianLiftPowerCoordinate_pow]⟩

@[simp]
theorem coordinateUnlinkExteriorEighthPowerPullbackProj_rightMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) (t : I) :
    coordinateUnlinkExteriorEighthPowerPullbackProj m
        (coordinateUnlinkExteriorEighthRightMeridianLift m x t) =
      coordinateUnlinkExteriorEighthMeridianLoop 1 x t :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorEighthPowerPullbackToComplement_rightMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) (t : I) :
    coordinateUnlinkExteriorEighthPowerPullbackToComplement m
        (coordinateUnlinkExteriorEighthRightMeridianLift m x t) =
      standardUnlinkRightMeridianLift m x t :=
  rfl

theorem continuous_coordinateUnlinkExteriorEighthRightMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) :
    Continuous (coordinateUnlinkExteriorEighthRightMeridianLift m x) := by
  apply Continuous.subtype_mk
  exact (continuous_coordinateUnlinkExteriorEighthMeridianLoop 1 x).prodMk
    (continuous_standardUnlinkRightMeridianLiftPowerCoordinate m)

/-- The explicit left-meridian lift, using the selected root branch on the left character
disk. -/
def coordinateUnlinkExteriorEighthLeftMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) (t : I) :
    CoordinateUnlinkExteriorEighthPowerPullback m :=
  ⟨(coordinateUnlinkExteriorEighthMeridianLoop 0 x t,
      standardUnlinkLeftMeridianLiftPowerCoordinate m x
        (unlinkMeridianCirclePoint (2 * Real.pi * (t : ℝ)))), by
    apply Subtype.ext
    change standardUnlinkRightDisplacementComplex
        (coordinateUnlinkExteriorEighthMeridianLoop 0 x t).1 =
      (standardUnlinkLeftMeridianLiftPowerCoordinate m x
        (unlinkMeridianCirclePoint (2 * Real.pi * (t : ℝ))) : ℂ) ^ m
    rw [show (coordinateUnlinkExteriorEighthMeridianLoop 0 x t).1 =
        (standardUnlinkMeridian 0 x
          (unlinkMeridianCirclePoint (2 * Real.pi * (t : ℝ)))).1 by rfl,
      standardUnlinkLeftMeridianLiftPowerCoordinate_pow]⟩

@[simp]
theorem coordinateUnlinkExteriorEighthPowerPullbackProj_leftMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) (t : I) :
    coordinateUnlinkExteriorEighthPowerPullbackProj m
        (coordinateUnlinkExteriorEighthLeftMeridianLift m x t) =
      coordinateUnlinkExteriorEighthMeridianLoop 0 x t :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorEighthPowerPullbackToComplement_leftMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) (t : I) :
    coordinateUnlinkExteriorEighthPowerPullbackToComplement m
        (coordinateUnlinkExteriorEighthLeftMeridianLift m x t) =
      standardUnlinkLeftMeridianLift m x t :=
  rfl

theorem continuous_coordinateUnlinkExteriorEighthLeftMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) :
    Continuous (coordinateUnlinkExteriorEighthLeftMeridianLift m x) := by
  apply Continuous.subtype_mk
  have hangle : Continuous (fun t : I ↦ 2 * Real.pi * (t : ℝ)) := by
    fun_prop
  exact (continuous_coordinateUnlinkExteriorEighthMeridianLoop 0 x).prodMk
    ((continuous_standardUnlinkLeftMeridianLiftPowerCoordinate m x).comp
      (continuous_unlinkMeridianCirclePoint.comp hangle))

/-- The closed-exterior right meridian advances by the standard deck index `1`. -/
theorem coordinateUnlinkExteriorEighthRightMeridianLift_one_eq_zmodOne_smul_zero
    (m : ℕ) [NeZero m] (x : Sphere 2) :
    coordinateUnlinkExteriorEighthRightMeridianLift m x 1 =
      coordinateUnlinkExteriorEighthPowerDeckZModHom m
          (Multiplicative.ofAdd (1 : ZMod m))
        (coordinateUnlinkExteriorEighthRightMeridianLift m x 0) := by
  change coordinateUnlinkExteriorEighthRightMeridianLift m x 1 =
    standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd (1 : ZMod m)) •
      coordinateUnlinkExteriorEighthRightMeridianLift m x 0
  apply coordinateUnlinkExteriorEighthPowerPullbackToComplement_injective m
  rw [coordinateUnlinkExteriorEighthPowerPullbackToComplement_rightMeridianLift,
    coordinateUnlinkExteriorEighthPowerPullbackToComplement_smul,
    coordinateUnlinkExteriorEighthPowerPullbackToComplement_rightMeridianLift]
  exact standardUnlinkRightMeridianLift_one_eq_zmodOne_smul_zero m x

/-- The closed-exterior left meridian closes, hence has standard deck index `0`. -/
theorem coordinateUnlinkExteriorEighthLeftMeridianLift_one_eq_zmodZero_smul_zero
    (m : ℕ) [NeZero m] (x : Sphere 2) :
    coordinateUnlinkExteriorEighthLeftMeridianLift m x 1 =
      coordinateUnlinkExteriorEighthPowerDeckZModHom m
          (Multiplicative.ofAdd (0 : ZMod m))
        (coordinateUnlinkExteriorEighthLeftMeridianLift m x 0) := by
  change coordinateUnlinkExteriorEighthLeftMeridianLift m x 1 =
    standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd (0 : ZMod m)) •
      coordinateUnlinkExteriorEighthLeftMeridianLift m x 0
  apply coordinateUnlinkExteriorEighthPowerPullbackToComplement_injective m
  rw [coordinateUnlinkExteriorEighthPowerPullbackToComplement_leftMeridianLift,
    coordinateUnlinkExteriorEighthPowerPullbackToComplement_smul,
    coordinateUnlinkExteriorEighthPowerPullbackToComplement_leftMeridianLift]
  exact standardUnlinkLeftMeridianLift_one_eq_zmodZero_smul_zero m x

/-! ## Transport to the exterior pushout -/

/-- The selected meridian point transported to the one-handle/punctured-cap pushout. -/
def coordinateUnlinkExteriorPushoutMeridian
    (i : Fin 2) (x : Sphere 2) (u : Sphere 1) :
    CoordinateUnlinkExteriorPushout oneEighth_lt_sphereHandleRadius_sub_half :=
  coordinateUnlinkExteriorOneEighthHomeomorph.symm
    (coordinateUnlinkExteriorEighthMeridian i x u)

@[simp]
theorem coordinateUnlinkExteriorOneEighthHomeomorph_pushoutMeridian
    (i : Fin 2) (x : Sphere 2) (u : Sphere 1) :
    coordinateUnlinkExteriorOneEighthHomeomorph
        (coordinateUnlinkExteriorPushoutMeridian i x u) =
      coordinateUnlinkExteriorEighthMeridian i x u :=
  coordinateUnlinkExteriorOneEighthHomeomorph.apply_symm_apply _

/-- Reading the transported point in the literal exterior and then including it in the strict
complement recovers the original meridian point. -/
@[simp]
theorem coordinateUnlinkExteriorPushoutMeridian_toComplement
    (i : Fin 2) (x : Sphere 2) (u : Sphere 1) :
    coordinateUnlinkExteriorToComplement (by norm_num)
        (coordinateUnlinkExteriorOneEighthHomeomorph
          (coordinateUnlinkExteriorPushoutMeridian i x u)) =
      standardUnlinkMeridian i x u := by
  rw [coordinateUnlinkExteriorOneEighthHomeomorph_pushoutMeridian,
    coordinateUnlinkExteriorToComplement_eighthMeridian]

theorem continuous_coordinateUnlinkExteriorPushoutMeridian
    (i : Fin 2) (x : Sphere 2) :
    Continuous (coordinateUnlinkExteriorPushoutMeridian i x) :=
  coordinateUnlinkExteriorOneEighthHomeomorph.symm.continuous.comp
    (continuous_coordinateUnlinkExteriorEighthMeridian i x)

/-- Traverse the transported meridian once counterclockwise in the exterior pushout. -/
def coordinateUnlinkExteriorPushoutMeridianLoop
    (i : Fin 2) (x : Sphere 2) (t : I) :
    CoordinateUnlinkExteriorPushout oneEighth_lt_sphereHandleRadius_sub_half :=
  coordinateUnlinkExteriorOneEighthHomeomorph.symm
    (coordinateUnlinkExteriorEighthMeridianLoop i x t)

@[simp]
theorem coordinateUnlinkExteriorOneEighthHomeomorph_pushoutMeridianLoop
    (i : Fin 2) (x : Sphere 2) (t : I) :
    coordinateUnlinkExteriorOneEighthHomeomorph
        (coordinateUnlinkExteriorPushoutMeridianLoop i x t) =
      coordinateUnlinkExteriorEighthMeridianLoop i x t :=
  coordinateUnlinkExteriorOneEighthHomeomorph.apply_symm_apply _

/-- Reading the transported loop in the literal exterior and then including it in the strict
complement recovers the original parametrized meridian loop. -/
@[simp]
theorem coordinateUnlinkExteriorPushoutMeridianLoop_toComplement
    (i : Fin 2) (x : Sphere 2) (t : I) :
    coordinateUnlinkExteriorToComplement (by norm_num)
        (coordinateUnlinkExteriorOneEighthHomeomorph
          (coordinateUnlinkExteriorPushoutMeridianLoop i x t)) =
      standardUnlinkMeridianLoop i x t := by
  rw [coordinateUnlinkExteriorOneEighthHomeomorph_pushoutMeridianLoop,
    coordinateUnlinkExteriorToComplement_eighthMeridianLoop]

@[simp]
theorem coordinateUnlinkExteriorPushoutMeridianLoop_zero
    (i : Fin 2) (x : Sphere 2) :
    coordinateUnlinkExteriorPushoutMeridianLoop i x 0 =
      coordinateUnlinkExteriorPushoutMeridian i x (unlinkMeridianCirclePoint 0) := by
  apply coordinateUnlinkExteriorOneEighthHomeomorph.injective
  simp

@[simp]
theorem coordinateUnlinkExteriorPushoutMeridianLoop_one
    (i : Fin 2) (x : Sphere 2) :
    coordinateUnlinkExteriorPushoutMeridianLoop i x 1 =
      coordinateUnlinkExteriorPushoutMeridian i x (unlinkMeridianCirclePoint 0) := by
  apply coordinateUnlinkExteriorOneEighthHomeomorph.injective
  simp

theorem continuous_coordinateUnlinkExteriorPushoutMeridianLoop
    (i : Fin 2) (x : Sphere 2) :
    Continuous (coordinateUnlinkExteriorPushoutMeridianLoop i x) :=
  coordinateUnlinkExteriorOneEighthHomeomorph.symm.continuous.comp
    (continuous_coordinateUnlinkExteriorEighthMeridianLoop i x)

/-- Transport the explicit closed-exterior right-meridian lift to the pushout power cover. -/
def coordinateUnlinkExteriorPushoutRightMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) (t : I) :
    CoordinateUnlinkExteriorPushoutPowerPullback m :=
  (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).symm
    (coordinateUnlinkExteriorEighthRightMeridianLift m x t)

@[simp]
theorem coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_rightMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) (t : I) :
    coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m
        (coordinateUnlinkExteriorPushoutRightMeridianLift m x t) =
      coordinateUnlinkExteriorEighthRightMeridianLift m x t :=
  (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).apply_symm_apply _

@[simp]
theorem coordinateUnlinkExteriorPushoutPowerPullbackProj_rightMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) (t : I) :
    coordinateUnlinkExteriorPushoutPowerPullbackProj m
        (coordinateUnlinkExteriorPushoutRightMeridianLift m x t) =
      coordinateUnlinkExteriorPushoutMeridianLoop 1 x t :=
  rfl

theorem continuous_coordinateUnlinkExteriorPushoutRightMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) :
    Continuous (coordinateUnlinkExteriorPushoutRightMeridianLift m x) :=
  (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).symm.continuous.comp
    (continuous_coordinateUnlinkExteriorEighthRightMeridianLift m x)

/-- Transport the explicit closed-exterior left-meridian lift to the pushout power cover. -/
def coordinateUnlinkExteriorPushoutLeftMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) (t : I) :
    CoordinateUnlinkExteriorPushoutPowerPullback m :=
  (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).symm
    (coordinateUnlinkExteriorEighthLeftMeridianLift m x t)

@[simp]
theorem coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_leftMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) (t : I) :
    coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m
        (coordinateUnlinkExteriorPushoutLeftMeridianLift m x t) =
      coordinateUnlinkExteriorEighthLeftMeridianLift m x t :=
  (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).apply_symm_apply _

@[simp]
theorem coordinateUnlinkExteriorPushoutPowerPullbackProj_leftMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) (t : I) :
    coordinateUnlinkExteriorPushoutPowerPullbackProj m
        (coordinateUnlinkExteriorPushoutLeftMeridianLift m x t) =
      coordinateUnlinkExteriorPushoutMeridianLoop 0 x t :=
  rfl

theorem continuous_coordinateUnlinkExteriorPushoutLeftMeridianLift
    (m : ℕ) [NeZero m] (x : Sphere 2) :
    Continuous (coordinateUnlinkExteriorPushoutLeftMeridianLift m x) :=
  (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).symm.continuous.comp
    (continuous_coordinateUnlinkExteriorEighthLeftMeridianLift m x)

/-- The transported right-meridian lift advances by the standard pushout deck index `1`. -/
theorem coordinateUnlinkExteriorPushoutRightMeridianLift_one_eq_zmodOne_smul_zero
    (m : ℕ) [NeZero m] (x : Sphere 2) :
    coordinateUnlinkExteriorPushoutRightMeridianLift m x 1 =
      coordinateUnlinkExteriorPushoutPowerDeckZModHom m
          (Multiplicative.ofAdd (1 : ZMod m))
        (coordinateUnlinkExteriorPushoutRightMeridianLift m x 0) := by
  apply (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).injective
  rw [coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_rightMeridianLift]
  change coordinateUnlinkExteriorEighthRightMeridianLift m x 1 =
    coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m
      (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd (1 : ZMod m)) •
        coordinateUnlinkExteriorPushoutRightMeridianLift m x 0)
  rw [coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_smul,
    coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_rightMeridianLift]
  exact coordinateUnlinkExteriorEighthRightMeridianLift_one_eq_zmodOne_smul_zero m x

/-- The transported left-meridian lift closes, hence has standard pushout deck index `0`. -/
theorem coordinateUnlinkExteriorPushoutLeftMeridianLift_one_eq_zmodZero_smul_zero
    (m : ℕ) [NeZero m] (x : Sphere 2) :
    coordinateUnlinkExteriorPushoutLeftMeridianLift m x 1 =
      coordinateUnlinkExteriorPushoutPowerDeckZModHom m
          (Multiplicative.ofAdd (0 : ZMod m))
        (coordinateUnlinkExteriorPushoutLeftMeridianLift m x 0) := by
  apply (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).injective
  rw [coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_leftMeridianLift]
  change coordinateUnlinkExteriorEighthLeftMeridianLift m x 1 =
    coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m
      (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd (0 : ZMod m)) •
        coordinateUnlinkExteriorPushoutLeftMeridianLift m x 0)
  rw [coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_smul,
    coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_leftMeridianLift]
  exact coordinateUnlinkExteriorEighthLeftMeridianLift_one_eq_zmodZero_smul_zero m x

end SplittingSpheres
