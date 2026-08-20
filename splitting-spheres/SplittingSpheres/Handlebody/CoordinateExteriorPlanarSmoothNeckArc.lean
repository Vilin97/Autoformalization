/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckArc
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# A smooth complex root along the planar neck arc

The continuous root selected in `CoordinateExteriorPlanarNeckArc` is sufficient for the
topological constructions there, but its choice-based definition carries no smoothness data.
This file gives an independent explicit smooth branch on the same root domain.  Rotating by
negation moves the disk `Metric.ball (-1) 1` into the standard complex slit plane, on which
`Complex.log` is smooth.

Only complex-valued maps are constructed here.  In particular, this file makes no smoothness
claim for the flower subtype, its partial spin, or any later pushout model.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped ContDiff Manifold

namespace SplittingSpheres

/-! ## The explicit smooth branch -/

/-- An explicit `m`-th-root branch on the planar neck root domain.  The formula uses
`log (-z) + πi`, whose exponential is `z`, because `-z` lies in the standard slit plane
whenever `z ∈ ball (-1) 1`. -/
def coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot (m : ℕ) (z : ℂ) : ℂ :=
  Complex.exp
    ((Complex.log (-z) + (Real.pi : ℂ) * Complex.I) / (m : ℂ))

/-- Negation sends the neck root domain into the standard domain of the complex logarithm. -/
theorem neg_mem_slitPlane_of_mem_coordinateUnlinkExteriorPlanarNeckRootDomain
    {z : ℂ} (hz : z ∈ coordinateUnlinkExteriorPlanarNeckRootDomain) :
    -z ∈ Complex.slitPlane := by
  change dist z (-1 : ℂ) < 1 at hz
  apply Complex.ball_one_subset_slitPlane
  rw [mem_ball, dist_eq_norm,
    show -z - 1 = -(z - (-1)) by ring, norm_neg]
  simpa only [dist_eq_norm] using hz

/-- On the neck root domain, the explicit branch has the required `m`-th power. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot_pow
    (m : ℕ) [NeZero m] (z : ℂ)
    (hz : z ∈ coordinateUnlinkExteriorPlanarNeckRootDomain) :
    coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot m z ^ m = z := by
  unfold coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot
  rw [← Complex.exp_nat_mul]
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [show (m : ℂ) *
      ((Complex.log (-z) + (Real.pi : ℂ) * Complex.I) / (m : ℂ)) =
        Complex.log (-z) + (Real.pi : ℂ) * Complex.I by field_simp]
  rw [Complex.exp_add, Complex.exp_log
    (Complex.slitPlane_ne_zero
      (neg_mem_slitPlane_of_mem_coordinateUnlinkExteriorPlanarNeckRootDomain hz)),
    Complex.exp_pi_mul_I]
  ring

/-- The explicit root is nonzero everywhere, independently of the power identity. -/
theorem coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot_ne_zero
    (m : ℕ) (z : ℂ) :
    coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot m z ≠ 0 := by
  exact Complex.exp_ne_zero _

/-- The explicit branch is real-smooth on the entire neck root domain. -/
theorem contDiffOn_coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot (m : ℕ) :
    ContDiffOn ℝ ∞ (coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot m)
      coordinateUnlinkExteriorPlanarNeckRootDomain := by
  intro z hz
  have hneg : ContDiffAt ℝ ∞ (fun w : ℂ ↦ -w) z := contDiffAt_id.neg
  have hlog : ContDiffAt ℝ ∞ (fun w : ℂ ↦ Complex.log (-w)) z :=
    (Complex.contDiffAt_log
      (neg_mem_slitPlane_of_mem_coordinateUnlinkExteriorPlanarNeckRootDomain hz))
        |>.restrict_scalars ℝ |>.comp z hneg
  have harg : ContDiffAt ℝ ∞
      (fun w : ℂ ↦
        (Complex.log (-w) + (Real.pi : ℂ) * Complex.I) / (m : ℂ)) z :=
    (hlog.add contDiffAt_const).div_const _
  exact ((Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp z harg).contDiffWithinAt

/-- Pointwise real smoothness of the explicit branch inside the open root domain. -/
theorem contDiffAt_coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot
    (m : ℕ) {z : ℂ}
    (hz : z ∈ coordinateUnlinkExteriorPlanarNeckRootDomain) :
    ContDiffAt ℝ ∞ (coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot m) z :=
  (contDiffOn_coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot m z hz).contDiffAt
    (isOpen_coordinateUnlinkExteriorPlanarNeckRootDomain.mem_nhds hz)

/-- Manifold-smoothness form of the preceding pointwise statement. -/
theorem contMDiffAt_coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot
    (m : ℕ) {z : ℂ}
    (hz : z ∈ coordinateUnlinkExteriorPlanarNeckRootDomain) :
    ContMDiffAt (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot m) z :=
  contMDiffAt_iff_contDiffAt.mpr
    (contDiffAt_coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot m hz)

/-! ## The smooth complex-valued neck arc -/

/-- The explicit smooth root evaluated along the vertical neck segment, as an ambient complex
map.  This is intentionally not bundled into the topological flower subtype. -/
def coordinateUnlinkExteriorPlanarSmoothNeckArcComplex
    (m : ℕ) (t : CoordinateUnlinkExteriorPlanarNeckInterval) : ℂ :=
  coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot m
    (coordinateUnlinkExteriorPlanarNeckBaseArc t)

/-- The ambient affine formula defining the base neck segment is real-smooth. -/
theorem contDiff_coordinateUnlinkExteriorPlanarNeckBaseArc_ambient :
    ContDiff ℝ ∞ (fun t : ℝ ↦
      (-1 / 2 : ℂ) +
        ((sphereHandleRadius * (2 * t - 1) : ℝ) : ℂ) * Complex.I) := by
  have hreal : ContDiff ℝ ∞
      (fun t : ℝ ↦ sphereHandleRadius * (2 * t - 1)) := by
    fun_prop
  exact contDiff_const.add
    ((Complex.ofRealCLM.contDiff.comp hreal).mul contDiff_const)

/-- The existing base neck segment is smooth from the closed-interval manifold model. -/
theorem contMDiff_coordinateUnlinkExteriorPlanarNeckBaseArc :
    ContMDiff (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf ℝ ℂ) ∞
      coordinateUnlinkExteriorPlanarNeckBaseArc := by
  have hambient : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℂ) ∞ (fun t : ℝ ↦
        (-1 / 2 : ℂ) +
          ((sphereHandleRadius * (2 * t - 1) : ℝ) : ℂ) * Complex.I) :=
    contMDiff_iff_contDiff.mpr
      contDiff_coordinateUnlinkExteriorPlanarNeckBaseArc_ambient
  exact hambient.comp contMDiff_subtypeVal_Icc

/-- The explicit complex-valued neck arc has the prescribed power coordinate. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarSmoothNeckArcComplex_pow
    (m : ℕ) [NeZero m] (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m t ^ m =
      coordinateUnlinkExteriorPlanarNeckBaseArc t :=
  coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot_pow m _
    (coordinateUnlinkExteriorPlanarNeckBaseArc_mem_rootDomain t)

/-- Every value of the explicit complex-valued neck arc is nonzero. -/
theorem coordinateUnlinkExteriorPlanarSmoothNeckArcComplex_ne_zero
    (m : ℕ) (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m t ≠ 0 :=
  coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot_ne_zero m _

/-- The explicit complex-valued neck arc is smooth from the closed-interval model. -/
theorem contMDiff_coordinateUnlinkExteriorPlanarSmoothNeckArcComplex (m : ℕ) :
    ContMDiff (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf ℝ ℂ) ∞
      (coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m) := by
  intro t
  exact (contMDiffAt_coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot m
    (coordinateUnlinkExteriorPlanarNeckBaseArc_mem_rootDomain t)).comp t
      contMDiff_coordinateUnlinkExteriorPlanarNeckBaseArc.contMDiffAt

/-- Exact lower endpoint of the explicit branch. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarSmoothNeckArcComplex_zero (m : ℕ) :
    coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m 0 =
      Complex.exp ((Complex.log
        ((1 / 2 : ℂ) + (sphereHandleRadius : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I) / (m : ℂ)) := by
  unfold coordinateUnlinkExteriorPlanarSmoothNeckArcComplex
  rw [coordinateUnlinkExteriorPlanarNeckBaseArc_zero]
  unfold coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot
  congr 3
  ring_nf

/-- Exact upper endpoint of the explicit branch. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarSmoothNeckArcComplex_one (m : ℕ) :
    coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m 1 =
      Complex.exp ((Complex.log
        ((1 / 2 : ℂ) - (sphereHandleRadius : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I) / (m : ℂ)) := by
  unfold coordinateUnlinkExteriorPlanarSmoothNeckArcComplex
  rw [coordinateUnlinkExteriorPlanarNeckBaseArc_one]
  unfold coordinateUnlinkExteriorPlanarSmoothNeckPowerRoot
  congr 3
  ring_nf

/-! ## Fixed deck translates -/

/-- A fixed roots-of-unity translate of the explicit smooth complex-valued neck arc. -/
def coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) : ℂ :=
  (((standardRootsOfUnityZModMulEquiv m
    (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) *
      coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m t

@[simp]
theorem coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate_apply
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate m a t =
      (((standardRootsOfUnityZModMulEquiv m
        (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) *
        coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m t :=
  rfl

/-- A fixed deck translate has the same prescribed power coordinate. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate_pow
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate m a t ^ m =
      coordinateUnlinkExteriorPlanarNeckBaseArc t := by
  rw [coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate_apply, mul_pow,
    (mem_rootsOfUnity' m
      (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).1).mp
        (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).2,
    one_mul, coordinateUnlinkExteriorPlanarSmoothNeckArcComplex_pow]

/-- Each fixed deck translate is smooth from the closed-interval model. -/
theorem contMDiff_coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate
    (m : ℕ) [NeZero m] (a : ZMod m) :
    ContMDiff (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf ℝ ℂ) ∞
      (coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate m a) := by
  let c : ℂ :=
    (((standardRootsOfUnityZModMulEquiv m
      (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ)
  have hmul : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞ (fun z : ℂ ↦ c * z) :=
    contMDiff_iff_contDiff.mpr (contDiff_const.mul contDiff_id)
  exact hmul.comp (contMDiff_coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m)

/-- Exact lower endpoint of a fixed deck translate. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate_zero
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate m a 0 =
      (((standardRootsOfUnityZModMulEquiv m
        (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) *
        Complex.exp ((Complex.log
          ((1 / 2 : ℂ) + (sphereHandleRadius : ℂ) * Complex.I) +
            (Real.pi : ℂ) * Complex.I) / (m : ℂ)) := by
  rw [coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate_apply,
    coordinateUnlinkExteriorPlanarSmoothNeckArcComplex_zero]

/-- Exact upper endpoint of a fixed deck translate. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate_one
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate m a 1 =
      (((standardRootsOfUnityZModMulEquiv m
        (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) *
        Complex.exp ((Complex.log
          ((1 / 2 : ℂ) - (sphereHandleRadius : ℂ) * Complex.I) +
            (Real.pi : ℂ) * Complex.I) / (m : ℂ)) := by
  rw [coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate_apply,
    coordinateUnlinkExteriorPlanarSmoothNeckArcComplex_one]

end SplittingSpheres
