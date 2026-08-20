/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutHomeomorph
public import SplittingSpheres.Handlebody.PartialSphereSpin
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# The partial sphere spin of an annulus

The literal annulus `S¹ × [0,1]`, attached along its zero end, supplies a radial collar for
the boundary of `S¹ × B³`.  We shrink the original ball to radius `1/2` and map the annulus
times `S²` onto the shell with radii from `1/2` to `1`.  The resulting piece maps identify the
partial `S²`-spin of the annulus with `S¹ × B³`.

This is a point-set homeomorphism.  It makes no smooth gluing, connected-sum, or cutting claim.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped unitInterval

namespace SplittingSpheres

/-- The literal closed annulus used as a planar factor. -/
abbrev PartialSphereSpinAnnulus : Type := Sphere 1 × I

/-- The zero end of the annulus, parametrized by its circle coordinate. -/
def partialSphereSpinAnnulusOuter : C(Sphere 1, PartialSphereSpinAnnulus) where
  toFun u := (u, 0)
  continuous_toFun := continuous_id.prodMk continuous_const

@[simp]
theorem partialSphereSpinAnnulusOuter_apply (u : Sphere 1) :
    partialSphereSpinAnnulusOuter u = (u, 0) :=
  rfl

/-- Shrink the original one-handle ball to the radius-`1/2` inner ball. -/
def partialSphereSpinAnnulusOneHandleMap : C(OneHandlePiece, OneHandlePiece) where
  toFun x := (x.1, ⟨(1 / 2 : ℝ) • x.2.1, by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs]
    have hx := mem_closedBall_zero_iff.mp x.2.2
    norm_num
    linarith⟩)
  continuous_toFun := by
    fun_prop

@[simp]
theorem partialSphereSpinAnnulusOneHandleMap_apply (x : OneHandlePiece) :
    partialSphereSpinAnnulusOneHandleMap x =
      (x.1, ⟨(1 / 2 : ℝ) • x.2.1, by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs]
        have hx := mem_closedBall_zero_iff.mp x.2.2
        norm_num
        linarith⟩) :=
  rfl

/-- The radius of the shell point selected by the annulus coordinate. -/
def partialSphereSpinAnnulusRadius (t : I) : ℝ :=
  1 / 2 + (t : ℝ) / 2

theorem continuous_partialSphereSpinAnnulusRadius :
    Continuous partialSphereSpinAnnulusRadius := by
  unfold partialSphereSpinAnnulusRadius
  fun_prop

theorem partialSphereSpinAnnulusRadius_pos (t : I) :
    0 < partialSphereSpinAnnulusRadius t := by
  unfold partialSphereSpinAnnulusRadius
  linarith [t.2.1]

theorem partialSphereSpinAnnulusRadius_le_one (t : I) :
    partialSphereSpinAnnulusRadius t ≤ 1 := by
  unfold partialSphereSpinAnnulusRadius
  linarith [t.2.2]

@[simp]
theorem partialSphereSpinAnnulusRadius_zero :
    partialSphereSpinAnnulusRadius 0 = 1 / 2 := by
  norm_num [partialSphereSpinAnnulusRadius]

@[simp]
theorem partialSphereSpinAnnulusRadius_one :
    partialSphereSpinAnnulusRadius 1 = 1 := by
  norm_num [partialSphereSpinAnnulusRadius]

/-- Map the annulus times `S²` onto the closed radial shell from radius `1/2` to radius `1`. -/
def partialSphereSpinAnnulusShellMap :
    C(PartialSphereSpinAnnulus × Sphere 2, OneHandlePiece) where
  toFun x := (x.1.1, ⟨partialSphereSpinAnnulusRadius x.1.2 • x.2.1, by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (partialSphereSpinAnnulusRadius_pos x.1.2),
      mem_sphere_zero_iff_norm.mp x.2.2, mul_one]
    exact partialSphereSpinAnnulusRadius_le_one x.1.2⟩)
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_fst
    · apply Continuous.subtype_mk
      exact (continuous_partialSphereSpinAnnulusRadius.comp
        (continuous_snd.comp continuous_fst)).smul
          (continuous_subtype_val.comp continuous_snd)

@[simp]
theorem partialSphereSpinAnnulusShellMap_apply
    (x : PartialSphereSpinAnnulus × Sphere 2) :
    partialSphereSpinAnnulusShellMap x =
      (x.1.1, ⟨partialSphereSpinAnnulusRadius x.1.2 • x.2.1, by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
          abs_of_pos (partialSphereSpinAnnulusRadius_pos x.1.2),
          mem_sphere_zero_iff_norm.mp x.2.2, mul_one]
        exact partialSphereSpinAnnulusRadius_le_one x.1.2⟩) :=
  rfl

/-- The two radial piece maps agree on the attaching boundary. -/
theorem partialSphereSpinAnnulus_piece_compatibility
    (x : OneHandleCapBoundary) :
    partialSphereSpinAnnulusOneHandleMap (oneHandleBoundaryInclusion x) =
      partialSphereSpinAnnulusShellMap
        (partialSphereSpinBoundaryInclusion partialSphereSpinAnnulusOuter x) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp [oneHandleBoundaryInclusion_apply,
      partialSphereSpinBoundaryInclusion_apply]

/-- The one end of the annular shell is exactly the ordinary boundary of the target
one-handle. -/
@[simp]
theorem partialSphereSpinAnnulusShellMap_one
    (x : OneHandleCapBoundary) :
    partialSphereSpinAnnulusShellMap ((x.1, 1), x.2) =
      oneHandleBoundaryInclusion x := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp [oneHandleBoundaryInclusion_apply]

theorem injective_partialSphereSpinAnnulusOuter :
    Injective partialSphereSpinAnnulusOuter := by
  intro u v huv
  exact congrArg Prod.fst huv

theorem injective_partialSphereSpinAnnulusOneHandleMap :
    Injective partialSphereSpinAnnulusOneHandleMap := by
  intro x y hxy
  have hfirstRaw := congrArg (fun z : OneHandlePiece ↦ z.1) hxy
  have hvRaw := congrArg (fun z : OneHandlePiece ↦ z.2.1) hxy
  have hfirst : x.1 = y.1 := hfirstRaw
  have hv : (1 / 2 : ℝ) • x.2.1 = (1 / 2 : ℝ) • y.2.1 := hvRaw
  refine Prod.ext hfirst ?_
  apply Subtype.ext
  exact smul_right_injective _ (by norm_num : (1 / 2 : ℝ) ≠ 0) hv

theorem injective_partialSphereSpinAnnulusShellMap :
    Injective partialSphereSpinAnnulusShellMap := by
  intro x y hxy
  have hfirst : x.1.1 = y.1.1 :=
    congrArg (fun z : OneHandlePiece ↦ z.1) hxy
  have hvec : partialSphereSpinAnnulusRadius x.1.2 • x.2.1 =
      partialSphereSpinAnnulusRadius y.1.2 • y.2.1 :=
    congrArg (fun z : OneHandlePiece ↦ z.2.1) hxy
  have hnorm := congrArg norm hvec
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (partialSphereSpinAnnulusRadius_pos x.1.2),
    abs_of_pos (partialSphereSpinAnnulusRadius_pos y.1.2),
    mem_sphere_zero_iff_norm.mp x.2.2, mem_sphere_zero_iff_norm.mp y.2.2,
    mul_one, mul_one] at hnorm
  have ht : x.1.2 = y.1.2 := by
    apply Subtype.ext
    unfold partialSphereSpinAnnulusRadius at hnorm
    linarith
  have hs : x.2 = y.2 := by
    apply Subtype.ext
    apply smul_right_injective _ (partialSphereSpinAnnulusRadius_pos x.1.2).ne'
    simpa [ht] using hvec
  exact Prod.ext (Prod.ext hfirst ht) hs

/-- The two radial images meet only along their common radius-`1/2` attaching sphere. -/
theorem partialSphereSpinAnnulus_cross
    (x : OneHandlePiece) (y : PartialSphereSpinAnnulus × Sphere 2)
    (hxy : partialSphereSpinAnnulusOneHandleMap x =
      partialSphereSpinAnnulusShellMap y) :
    ∃ a : OneHandleCapBoundary,
      oneHandleBoundaryInclusion a = x ∧
        partialSphereSpinBoundaryInclusion partialSphereSpinAnnulusOuter a = y := by
  have hcircle : x.1 = y.1.1 := congrArg Prod.fst hxy
  have hvec : (1 / 2 : ℝ) • x.2.1 =
      partialSphereSpinAnnulusRadius y.1.2 • y.2.1 :=
    congrArg (fun z : OneHandlePiece ↦ z.2.1) hxy
  have hnorm := congrArg norm hvec
  have hxle := mem_closedBall_zero_iff.mp x.2.2
  have hyrpos := partialSphereSpinAnnulusRadius_pos y.1.2
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_pos hyrpos,
    mem_sphere_zero_iff_norm.mp y.2.2, mul_one] at hnorm
  have hyrge : (1 / 2 : ℝ) ≤ partialSphereSpinAnnulusRadius y.1.2 := by
    unfold partialSphereSpinAnnulusRadius
    linarith [y.1.2.2.1]
  have hxnorm : ‖x.2.1‖ = 1 := by
    nlinarith
  have hyr : partialSphereSpinAnnulusRadius y.1.2 = 1 / 2 := by
    nlinarith
  have htime : y.1.2 = 0 := by
    apply Subtype.ext
    change (y.1.2 : ℝ) = 0
    unfold partialSphereSpinAnnulusRadius at hyr
    linarith
  have hball : x.2.1 = y.2.1 := by
    apply smul_right_injective _ (by norm_num : (1 / 2 : ℝ) ≠ 0)
    simpa [hyr] using hvec
  let a : OneHandleCapBoundary := (x.1, ⟨x.2.1,
    mem_sphere_zero_iff_norm.mpr hxnorm⟩)
  refine ⟨a, ?_, ?_⟩
  · apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  · apply Prod.ext
    · apply Prod.ext
      · exact hcircle
      · exact htime.symm
    · apply Subtype.ext
      exact hball

/-- The shrunken ball and radial shell cover the whole one-handle. -/
theorem partialSphereSpinAnnulus_cover :
    range partialSphereSpinAnnulusOneHandleMap ∪
        range partialSphereSpinAnnulusShellMap =
      (univ : Set OneHandlePiece) := by
  apply Set.eq_univ_of_forall
  intro z
  by_cases hz : ‖z.2.1‖ ≤ 1 / 2
  · left
    let b : EuclideanClosedBall 3 := ⟨(2 : ℝ) • z.2.1, by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs]
      norm_num
      linarith⟩
    refine ⟨(z.1, b), ?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change (1 / 2 : ℝ) • ((2 : ℝ) • z.2.1) = z.2.1
      module
  · right
    have hnorm : 1 / 2 < ‖z.2.1‖ := lt_of_not_ge hz
    have hne : z.2.1 ≠ 0 := fun hzero ↦ by
      rw [hzero, norm_zero] at hnorm
      linarith
    let t : I := ⟨2 * ‖z.2.1‖ - 1, ⟨by linarith,
      by linarith [mem_closedBall_zero_iff.mp z.2.2]⟩⟩
    let s : Sphere 2 := ⟨NormedSpace.normalize z.2.1, by
      rw [mem_sphere_zero_iff_norm, NormedSpace.norm_normalize hne]⟩
    refine ⟨((z.1, t), s), ?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change partialSphereSpinAnnulusRadius t • NormedSpace.normalize z.2.1 = z.2.1
      have hr : partialSphereSpinAnnulusRadius t = ‖z.2.1‖ := by
        unfold partialSphereSpinAnnulusRadius t
        dsimp [t]
        ring
      rw [hr, NormedSpace.norm_smul_normalize]

/-- The partial `S²`-spin of the literal annulus is the compact one-handle `S¹ × B³`. -/
def partialSphereSpinAnnulusHomeomorphOneHandle :
    PartialSphereSpin partialSphereSpinAnnulusOuter ≃ₜ OneHandlePiece :=
  topologicalPushoutHomeomorph
    oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion partialSphereSpinAnnulusOuter)
    partialSphereSpinAnnulusOneHandleMap partialSphereSpinAnnulusShellMap
    partialSphereSpinAnnulus_piece_compatibility
    oneHandleBoundaryInclusion_injective
    injective_partialSphereSpinAnnulusOneHandleMap
    injective_partialSphereSpinAnnulusShellMap
    partialSphereSpinAnnulus_cross
    partialSphereSpinAnnulus_cover

@[simp]
theorem partialSphereSpinAnnulusHomeomorphOneHandle_inl (x : OneHandlePiece) :
    partialSphereSpinAnnulusHomeomorphOneHandle
        (partialSphereSpinInl partialSphereSpinAnnulusOuter x) =
      partialSphereSpinAnnulusOneHandleMap x :=
  topologicalPushoutHomeomorph_inl _ _ _ _ _ _ _ _ _ _ x

@[simp]
theorem partialSphereSpinAnnulusHomeomorphOneHandle_inr
    (x : PartialSphereSpinAnnulus × Sphere 2) :
    partialSphereSpinAnnulusHomeomorphOneHandle
        (partialSphereSpinInr partialSphereSpinAnnulusOuter x) =
      partialSphereSpinAnnulusShellMap x :=
  topologicalPushoutHomeomorph_inr _ _ _ _ _ _ _ _ _ _ x

/-- Under the annulus-spin homeomorphism, the unglued annulus end is literally the boundary of
the resulting one-handle. -/
@[simp]
theorem partialSphereSpinAnnulusHomeomorphOneHandle_innerBoundary
    (x : OneHandleCapBoundary) :
    partialSphereSpinAnnulusHomeomorphOneHandle
        (partialSphereSpinInr partialSphereSpinAnnulusOuter ((x.1, 1), x.2)) =
      oneHandleBoundaryInclusion x := by
  rw [partialSphereSpinAnnulusHomeomorphOneHandle_inr,
    partialSphereSpinAnnulusShellMap_one]

end SplittingSpheres
