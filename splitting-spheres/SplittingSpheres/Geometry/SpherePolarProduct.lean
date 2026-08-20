/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import SplittingSpheres.Geometry.UnlinkTubes

/-!
# Polar product coordinates on the ambient four-sphere

Projection to the last two coordinates identifies the open subset of `S⁴` lying over the
open unit disk with `S² × B²`.  This file constructs that identification directly from the
displayed coordinates.  It is the global coordinate model from which the two standard unlink
tubes are obtained by restricting the normal-disk factor.
-/

@[expose] public section

open Function Metric Set Topology
open TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-- Projection to the first three ambient coordinates. -/
def spherePolarSourceProjection (y : Sphere 4) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![y.1 0, y.1 1, y.1 2]

@[simp]
theorem spherePolarSourceProjection_apply_zero (y : Sphere 4) :
    spherePolarSourceProjection y 0 = y.1 0 := rfl

@[simp]
theorem spherePolarSourceProjection_apply_one (y : Sphere 4) :
    spherePolarSourceProjection y 1 = y.1 1 := rfl

@[simp]
theorem spherePolarSourceProjection_apply_two (y : Sphere 4) :
    spherePolarSourceProjection y 2 = y.1 2 := rfl

/-- Projection to the first three coordinates is continuous. -/
@[continuity, fun_prop]
theorem continuous_spherePolarSourceProjection :
    Continuous spherePolarSourceProjection := by
  unfold spherePolarSourceProjection
  fun_prop

/-- Projection to the first three coordinates is smooth on the ambient sphere. -/
theorem contMDiff_spherePolarSourceProjection :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞
      spherePolarSourceProjection := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) := ⟨by simp⟩
  have hambient : ContDiff ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin 5) ↦
        (WithLp.toLp 2 ![y 0, y 1, y 2] : EuclideanSpace ℝ (Fin 3))) := by
    rw [contDiff_piLp]
    intro j
    fin_cases j <;> simp <;> fun_prop
  exact hambient.comp_contMDiff contMDiff_coe_sphere

/-- The squared norms of the first-three and last-two coordinate projections add to one. -/
theorem spherePolar_norm_decomposition (y : Sphere 4) :
    ‖spherePolarSourceProjection y‖ ^ 2 + ‖standardUnlinkNormalProjection y‖ ^ 2 = 1 := by
  have hy : ‖(y : EuclideanSpace ℝ (Fin 5))‖ ^ 2 = 1 := by
    have hynorm : ‖(y : EuclideanSpace ℝ (Fin 5))‖ = 1 := by
      simpa [mem_sphere_zero_iff_norm] using y.2
    nlinarith
  have hfirst : ‖spherePolarSourceProjection y‖ ^ 2 =
      y.1 0 ^ 2 + (y.1 1 ^ 2 + y.1 2 ^ 2) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [spherePolarSourceProjection, Fin.sum_univ_succ]
  have hnormal : ‖standardUnlinkNormalProjection y‖ ^ 2 =
      y.1 3 ^ 2 + y.1 4 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [standardUnlinkNormalProjection, Fin.sum_univ_succ]
  have hambient := EuclideanSpace.real_norm_sq_eq (y : EuclideanSpace ℝ (Fin 5))
  rw [hy] at hambient
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hambient
  change 1 = y.1 0 ^ 2 + (y.1 1 ^ 2 +
    (y.1 2 ^ 2 + (y.1 3 ^ 2 + y.1 4 ^ 2))) at hambient
  rw [hfirst, hnormal]
  nlinarith

/-- Radial scale of the `S²` factor above a normal coordinate `v`. -/
def spherePolarScale (v : UnlinkNormalPlane) : ℝ :=
  √(1 - ‖v‖ ^ 2)

theorem spherePolarScale_pos {v : UnlinkNormalPlane} (hv : v ∈ ball 0 1) :
    0 < spherePolarScale v := by
  rw [spherePolarScale]
  apply Real.sqrt_pos.mpr
  have hvlt : ‖v‖ < 1 := mem_ball_zero_iff.1 hv
  nlinarith [norm_nonneg v]

theorem spherePolarScale_ne_zero {v : UnlinkNormalPlane} (hv : v ∈ ball 0 1) :
    spherePolarScale v ≠ 0 :=
  (spherePolarScale_pos hv).ne'

theorem spherePolarScale_sq {v : UnlinkNormalPlane} (hv : v ∈ ball 0 1) :
    spherePolarScale v ^ 2 = 1 - ‖v‖ ^ 2 := by
  rw [spherePolarScale, Real.sq_sqrt]
  have hvlt : ‖v‖ < 1 := mem_ball_zero_iff.1 hv
  nlinarith [norm_nonneg v]

/-- The radial scale is continuous on the whole normal plane. -/
@[continuity, fun_prop]
theorem continuous_spherePolarScale : Continuous spherePolarScale := by
  unfold spherePolarScale
  fun_prop

/-- Ambient coordinate formula for the polar product map. -/
def spherePolarAmbientMap (x : EuclideanSpace ℝ (Fin 3)) (v : UnlinkNormalPlane) :
    EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 ![spherePolarScale v * x 0, spherePolarScale v * x 1,
    spherePolarScale v * x 2, v 0, v 1]

@[simp]
theorem spherePolarAmbientMap_apply_zero (x : EuclideanSpace ℝ (Fin 3))
    (v : UnlinkNormalPlane) : spherePolarAmbientMap x v 0 = spherePolarScale v * x 0 := rfl

@[simp]
theorem spherePolarAmbientMap_apply_one (x : EuclideanSpace ℝ (Fin 3))
    (v : UnlinkNormalPlane) : spherePolarAmbientMap x v 1 = spherePolarScale v * x 1 := rfl

@[simp]
theorem spherePolarAmbientMap_apply_two (x : EuclideanSpace ℝ (Fin 3))
    (v : UnlinkNormalPlane) : spherePolarAmbientMap x v 2 = spherePolarScale v * x 2 := rfl

@[simp]
theorem spherePolarAmbientMap_apply_three (x : EuclideanSpace ℝ (Fin 3))
    (v : UnlinkNormalPlane) : spherePolarAmbientMap x v 3 = v 0 := rfl

@[simp]
theorem spherePolarAmbientMap_apply_four (x : EuclideanSpace ℝ (Fin 3))
    (v : UnlinkNormalPlane) : spherePolarAmbientMap x v 4 = v 1 := rfl

/-- The ambient polar formula is jointly continuous. -/
theorem continuous_spherePolarAmbientMap :
    Continuous (fun p : EuclideanSpace ℝ (Fin 3) × UnlinkNormalPlane ↦
      spherePolarAmbientMap p.1 p.2) := by
  unfold spherePolarAmbientMap
  fun_prop

theorem norm_spherePolarAmbientMap_of_mem_sphere_of_mem_ball
    (x : Sphere 2) {v : UnlinkNormalPlane} (hv : v ∈ ball 0 1) :
    ‖spherePolarAmbientMap x.1 v‖ = 1 := by
  have hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 = 1 := by
    have hxnorm : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
      simpa [mem_sphere_zero_iff_norm] using x.2
    nlinarith
  have hsq : ‖spherePolarAmbientMap x.1 v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change (spherePolarScale v * x.1 0) ^ 2 +
      ((spherePolarScale v * x.1 1) ^ 2 +
        ((spherePolarScale v * x.1 2) ^ 2 + (v 0 ^ 2 + v 1 ^ 2))) = 1
    have hxcoords : x.1 0 ^ 2 + (x.1 1 ^ 2 + x.1 2 ^ 2) = 1 := by
      have hcoords := EuclideanSpace.real_norm_sq_eq x.1
      rw [hx] at hcoords
      simpa [Fin.sum_univ_succ] using hcoords.symm
    have hvcoords : v 0 ^ 2 + v 1 ^ 2 = ‖v‖ ^ 2 := by
      have hcoords := EuclideanSpace.real_norm_sq_eq v
      simpa [Fin.sum_univ_succ] using hcoords.symm
    have hscale := spherePolarScale_sq hv
    nlinarith
  nlinarith [norm_nonneg (spherePolarAmbientMap x.1 v)]

/-- The final two coordinates of the ambient polar formula are exactly `v`. -/
theorem standardUnlinkNormalProjection_spherePolarAmbientMap
    (x : EuclideanSpace ℝ (Fin 3)) (v : UnlinkNormalPlane)
    (h : ‖spherePolarAmbientMap x v‖ = 1) :
    standardUnlinkNormalProjection
      (⟨spherePolarAmbientMap x v, by simpa [mem_sphere_zero_iff_norm] using h⟩ : Sphere 4) = v := by
  ext j
  fin_cases j <;> rfl

/-- The open unit disk in the normal coordinate plane, bundled as an open set. -/
def unlinkUnitNormalDisk : Opens UnlinkNormalPlane :=
  ⟨ball 0 1, isOpen_ball⟩

/-- The open unit disk as a manifold subtype. -/
abbrev UnlinkUnitNormalDisk := unlinkUnitNormalDisk

/-- The part of `S⁴` whose normal projection lies in the open unit disk, bundled as an open set. -/
def spherePolarRegion : Opens (Sphere 4) :=
  ⟨standardUnlinkNormalProjection ⁻¹' ball 0 1,
    isOpen_ball.preimage continuous_standardUnlinkNormalProjection⟩

/-- The polar region as a manifold subtype. -/
abbrev SpherePolarRegion := spherePolarRegion

/-- The square-root scale restricted to the open unit disk. -/
def spherePolarScaleOnUnitDisk (v : UnlinkUnitNormalDisk) : ℝ :=
  spherePolarScale v.1

/-- The normal coordinate of a point in the polar region, as a point of the unit disk. -/
def spherePolarNormalDisk (y : SpherePolarRegion) : UnlinkUnitNormalDisk :=
  ⟨standardUnlinkNormalProjection y.1, y.2⟩

/-- The polar scale evaluated on a point of the polar region. -/
def spherePolarScaleOnRegion : SpherePolarRegion → ℝ :=
  spherePolarScaleOnUnitDisk ∘ spherePolarNormalDisk

@[simp]
theorem spherePolarScaleOnUnitDisk_apply (v : UnlinkUnitNormalDisk) :
    spherePolarScaleOnUnitDisk v = spherePolarScale v.1 := rfl

@[simp]
theorem spherePolarNormalDisk_coe (y : SpherePolarRegion) :
    (spherePolarNormalDisk y : UnlinkNormalPlane) =
      standardUnlinkNormalProjection y.1 := rfl

@[simp]
theorem spherePolarScaleOnRegion_apply (y : SpherePolarRegion) :
    spherePolarScaleOnRegion y =
      spherePolarScale (standardUnlinkNormalProjection y.1) := rfl

/-- Polar product map `S² × B² → S⁴`. -/
def spherePolarForward (p : Sphere 2 × UnlinkUnitNormalDisk) : SpherePolarRegion := by
  let hnorm := norm_spherePolarAmbientMap_of_mem_sphere_of_mem_ball p.1 p.2.2
  let y : Sphere 4 := ⟨spherePolarAmbientMap p.1.1 p.2.1, by
    simpa [mem_sphere_zero_iff_norm] using hnorm⟩
  refine ⟨y, ?_⟩
  change standardUnlinkNormalProjection y ∈ ball 0 1
  rw [show standardUnlinkNormalProjection y = p.2.1 by
    exact standardUnlinkNormalProjection_spherePolarAmbientMap p.1.1 p.2.1 hnorm]
  exact p.2.2

@[simp]
theorem spherePolarForward_coe (p : Sphere 2 × UnlinkUnitNormalDisk) :
    ((spherePolarForward p : SpherePolarRegion) : Sphere 4).1 =
      spherePolarAmbientMap p.1.1 p.2.1 := by
  rfl

@[simp]
theorem standardUnlinkNormalProjection_spherePolarForward
    (p : Sphere 2 × UnlinkUnitNormalDisk) :
    standardUnlinkNormalProjection (spherePolarForward p) = p.2.1 := by
  apply standardUnlinkNormalProjection_spherePolarAmbientMap
  exact norm_spherePolarAmbientMap_of_mem_sphere_of_mem_ball p.1 p.2.2

/-- Recover the `S²` coordinate by normalizing the first three coordinates. -/
def spherePolarSource (y : SpherePolarRegion) : Sphere 2 := by
  let s := spherePolarScale (standardUnlinkNormalProjection y.1)
  let x := s⁻¹ • spherePolarSourceProjection y.1
  have hspos : 0 < s := spherePolarScale_pos y.2
  have hfirst : ‖spherePolarSourceProjection y.1‖ ^ 2 = s ^ 2 := by
    rw [spherePolarScale_sq y.2]
    nlinarith [spherePolar_norm_decomposition y.1]
  have hxnorm : ‖x‖ = 1 := by
    have hsne : s ≠ 0 := hspos.ne'
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hspos]
    have hfirstnorm : ‖spherePolarSourceProjection y.1‖ = s := by
      nlinarith [norm_nonneg (spherePolarSourceProjection y.1)]
    rw [hfirstnorm, inv_mul_cancel₀ hsne]
  exact ⟨x, by simpa [mem_sphere_zero_iff_norm] using hxnorm⟩

/-- Inverse polar coordinates on the open region. -/
def spherePolarInverse (y : SpherePolarRegion) : Sphere 2 × UnlinkUnitNormalDisk :=
  (spherePolarSource y, ⟨standardUnlinkNormalProjection y.1, y.2⟩)

@[simp]
theorem spherePolarInverse_snd (y : SpherePolarRegion) :
    (spherePolarInverse y).2.1 = standardUnlinkNormalProjection y.1 := rfl

@[simp]
theorem spherePolarSource_coe (y : SpherePolarRegion) :
    (spherePolarSource y : EuclideanSpace ℝ (Fin 3)) =
      (spherePolarScale (standardUnlinkNormalProjection y.1))⁻¹ •
        spherePolarSourceProjection y.1 := by
  rfl

/-- The first-three coordinates of the forward map are the scaled source point. -/
theorem spherePolarSourceProjection_spherePolarForward
    (p : Sphere 2 × UnlinkUnitNormalDisk) :
    spherePolarSourceProjection (spherePolarForward p) =
      spherePolarScale p.2.1 • p.1.1 := by
  ext j
  fin_cases j <;> rfl

@[simp]
theorem spherePolarSource_spherePolarForward
    (p : Sphere 2 × UnlinkUnitNormalDisk) :
    spherePolarSource (spherePolarForward p) = p.1 := by
  apply Subtype.ext
  rw [spherePolarSource_coe, standardUnlinkNormalProjection_spherePolarForward,
    spherePolarSourceProjection_spherePolarForward, smul_smul,
    inv_mul_cancel₀ (spherePolarScale_ne_zero p.2.2), one_smul]

theorem spherePolarInverse_forward (p : Sphere 2 × UnlinkUnitNormalDisk) :
    spherePolarInverse (spherePolarForward p) = p := by
  apply Prod.ext
  · exact spherePolarSource_spherePolarForward p
  · apply Subtype.ext
    exact standardUnlinkNormalProjection_spherePolarForward p

theorem spherePolarForward_inverse (y : SpherePolarRegion) :
    spherePolarForward (spherePolarInverse y) = y := by
  apply Subtype.ext
  apply Subtype.ext
  ext j
  fin_cases j
  · change spherePolarScale (standardUnlinkNormalProjection y.1) *
      ((spherePolarScale (standardUnlinkNormalProjection y.1))⁻¹ * y.1.1 0) = y.1.1 0
    rw [← mul_assoc, mul_inv_cancel₀ (spherePolarScale_ne_zero y.2)]
    simp
  · change spherePolarScale (standardUnlinkNormalProjection y.1) *
      ((spherePolarScale (standardUnlinkNormalProjection y.1))⁻¹ * y.1.1 1) = y.1.1 1
    rw [← mul_assoc, mul_inv_cancel₀ (spherePolarScale_ne_zero y.2)]
    simp
  · change spherePolarScale (standardUnlinkNormalProjection y.1) *
      ((spherePolarScale (standardUnlinkNormalProjection y.1))⁻¹ * y.1.1 2) = y.1.1 2
    rw [← mul_assoc, mul_inv_cancel₀ (spherePolarScale_ne_zero y.2)]
    simp
  · rfl
  · rfl

/-- The exact polar-coordinate equivalence over the open normal unit disk. -/
def spherePolarEquiv :
    (Sphere 2 × UnlinkUnitNormalDisk) ≃ SpherePolarRegion where
  toFun := spherePolarForward
  invFun := spherePolarInverse
  left_inv := spherePolarInverse_forward
  right_inv := spherePolarForward_inverse

@[simp]
theorem spherePolarEquiv_apply (p : Sphere 2 × UnlinkUnitNormalDisk) :
    spherePolarEquiv p = spherePolarForward p := rfl

@[simp]
theorem spherePolarEquiv_symm_apply (y : SpherePolarRegion) :
    spherePolarEquiv.symm y = spherePolarInverse y := rfl

/-- The square-root scale is smooth on the open unit disk. -/
theorem contMDiff_spherePolarScale_unitDisk :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ∞
      spherePolarScaleOnUnitDisk := by
  change ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
    (modelWithCornersSelf ℝ ℝ) ∞
    (fun v : UnlinkUnitNormalDisk ↦ spherePolarScale v.1)
  intro v
  rw [contMDiffAt_subtype_iff]
  apply ContDiffAt.contMDiffAt
  unfold spherePolarScale
  apply ContDiffAt.sqrt
  · exact contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt
  · have hvlt : ‖(v : UnlinkNormalPlane)‖ < 1 := mem_ball_zero_iff.1 v.2
    nlinarith [norm_nonneg (v : UnlinkNormalPlane)]

/-- The ambient polar formula is jointly smooth on `S² × B²`. -/
theorem contMDiff_spherePolarAmbientMap_unitDisk :
    ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5))) ∞
      (fun p : Sphere 2 × UnlinkUnitNormalDisk ↦
        spherePolarAmbientMap p.1.1 p.2.1) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let raw : Sphere 2 × UnlinkUnitNormalDisk → (Fin 5 → ℝ) :=
    fun p ↦ ![spherePolarScale p.2.1 * p.1.1 0,
      spherePolarScale p.2.1 * p.1.1 1,
      spherePolarScale p.2.1 * p.1.1 2, p.2.1 0, p.2.1 1]
  have hx : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞
      (fun p : Sphere 2 × UnlinkUnitNormalDisk ↦ p.1.1) :=
    contMDiff_coe_sphere.comp contMDiff_fst
  have hv : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞
      (fun p : Sphere 2 × UnlinkUnitNormalDisk ↦ p.2.1) :=
    contMDiff_subtype_val.comp contMDiff_snd
  have hs : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 2 × UnlinkUnitNormalDisk ↦ spherePolarScale p.2.1) :=
    contMDiff_spherePolarScale_unitDisk.comp contMDiff_snd
  have hxcoord (j : Fin 3) : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 2 × UnlinkUnitNormalDisk ↦ p.1.1 j) := by
    have heval : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 3) ↦ x j) := by
      fun_prop
    exact heval.comp_contMDiff hx
  have hvcoord (j : Fin 2) : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 2 × UnlinkUnitNormalDisk ↦ p.2.1 j) := by
    have heval : ContDiff ℝ ∞ (fun v : UnlinkNormalPlane ↦ v j) := by
      fun_prop
    exact heval.comp_contMDiff hv
  have hmul (j : Fin 3) : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 2 × UnlinkUnitNormalDisk ↦
        spherePolarScale p.2.1 * p.1.1 j) :=
    (hs.smul (hxcoord j)).congr fun _ ↦ by simp [smul_eq_mul]
  have hraw : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ (Fin 5 → ℝ)) ∞ raw := by
    rw [contMDiff_pi_space]
    intro j
    fin_cases j
    · simpa [raw] using hmul 0
    · simpa [raw] using hmul 1
    · simpa [raw] using hmul 2
    · simpa [raw] using hvcoord 0
    · simpa [raw] using hvcoord 1
  have htoLp : ContMDiff (modelWithCornersSelf ℝ (Fin 5 → ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5))) ∞
      (WithLp.toLp 2) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 5 ↦ ℝ)).symm.toContinuousLinearMap.contMDiff
  exact (htoLp.comp hraw).congr fun _ ↦ rfl

/-- The forward polar map is smooth as a map of open manifolds. -/
theorem contMDiff_spherePolarForward :
    ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞ spherePolarForward := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) := ⟨by simp⟩
  have hsphere : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun p : Sphere 2 × UnlinkUnitNormalDisk ↦
        (⟨spherePolarAmbientMap p.1.1 p.2.1, by
          simpa [mem_sphere_zero_iff_norm] using
            norm_spherePolarAmbientMap_of_mem_sphere_of_mem_ball p.1 p.2.2⟩ : Sphere 4)) :=
    contMDiff_spherePolarAmbientMap_unitDisk.codRestrict_sphere fun p ↦ by
      simpa [mem_sphere_zero_iff_norm] using
        norm_spherePolarAmbientMap_of_mem_sphere_of_mem_ball p.1 p.2.2
  apply (ContMDiff.subtypeVal_comp_iff spherePolarRegion spherePolarForward).mp
  exact hsphere.congr fun _ ↦ rfl

/-- The ambient normal coordinate, restricted to the polar region, is smooth. -/
theorem contMDiff_spherePolarNormalOnRegion :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞
      (fun y : SpherePolarRegion ↦ standardUnlinkNormalProjection y.1) :=
  contMDiff_standardUnlinkNormalProjection.comp contMDiff_subtype_val

/-- The normal coordinate as a smooth map into the open unit disk. -/
theorem contMDiff_spherePolarNormalDisk :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞
      spherePolarNormalDisk := by
  apply (ContMDiff.subtypeVal_comp_iff unlinkUnitNormalDisk spherePolarNormalDisk).mp
  exact contMDiff_spherePolarNormalOnRegion

/-- The first-three-coordinate projection restricted to the polar region is smooth. -/
theorem contMDiff_spherePolarSourceProjectionOnRegion :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞
      (fun y : SpherePolarRegion ↦ spherePolarSourceProjection y.1) :=
  contMDiff_spherePolarSourceProjection.comp contMDiff_subtype_val

/-- The polar scale evaluated on the normal coordinate is smooth. -/
theorem contMDiff_spherePolarScaleOnRegion :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ ℝ) ∞
      spherePolarScaleOnRegion :=
  contMDiff_spherePolarScale_unitDisk.comp contMDiff_spherePolarNormalDisk

/-- The reciprocal polar scale is smooth on the polar region. -/
theorem contMDiff_spherePolarScaleInvOnRegion :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : SpherePolarRegion ↦
        (spherePolarScale (standardUnlinkNormalProjection y.1))⁻¹) := by
  exact (contMDiff_spherePolarScaleOnRegion.inv₀ fun y ↦
    spherePolarScale_ne_zero y.2).congr fun _ ↦ rfl

/-- The raw normalized first-three-coordinate vector is smooth. -/
theorem contMDiff_spherePolarSourceRaw :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞
      (fun y : SpherePolarRegion ↦
        (spherePolarScale (standardUnlinkNormalProjection y.1))⁻¹ •
          spherePolarSourceProjection y.1) :=
  contMDiff_spherePolarScaleInvOnRegion.smul
    contMDiff_spherePolarSourceProjectionOnRegion

/-- The normalized source-sphere coordinate is smooth. -/
theorem contMDiff_spherePolarSource :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞
      spherePolarSource := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have hcod := contMDiff_spherePolarSourceRaw.codRestrict_sphere (n := 2)
    (fun y ↦ (spherePolarSource y).2)
  exact hcod.congr fun _ ↦ rfl

/-- The inverse polar map is smooth as a map of open manifolds. -/
theorem contMDiff_spherePolarInverse :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))) ∞
      spherePolarInverse := by
  exact (contMDiff_spherePolarSource.prodMk
    contMDiff_spherePolarNormalDisk).congr fun _ ↦ rfl

/-- The polar product coordinates as a genuine smooth diffeomorphism. -/
def spherePolarDiffeomorph :
    (Sphere 2 × UnlinkUnitNormalDisk) ≃ₘ^∞⟮
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))),
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))⟯ SpherePolarRegion where
  toEquiv := spherePolarEquiv
  contMDiff_toFun := contMDiff_spherePolarForward
  contMDiff_invFun := contMDiff_spherePolarInverse

@[simp]
theorem spherePolarDiffeomorph_apply (p : Sphere 2 × UnlinkUnitNormalDisk) :
    spherePolarDiffeomorph p = spherePolarForward p := rfl

@[simp]
theorem spherePolarDiffeomorph_symm_apply (y : SpherePolarRegion) :
    spherePolarDiffeomorph.symm y = spherePolarInverse y := rfl

/-- The forward polar-coordinate map is continuous. -/
theorem continuous_spherePolarForward : Continuous spherePolarForward := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous (fun p : Sphere 2 × UnlinkUnitNormalDisk ↦
    spherePolarAmbientMap p.1.1 p.2.1)
  unfold spherePolarAmbientMap
  fun_prop

/-- The normalized source coordinate is continuous on the polar region. -/
theorem continuous_spherePolarSource : Continuous spherePolarSource := by
  apply Continuous.subtype_mk
  let normal : SpherePolarRegion → UnlinkNormalPlane :=
    fun y ↦ standardUnlinkNormalProjection y.1
  have hnormal : Continuous normal :=
    continuous_standardUnlinkNormalProjection.comp continuous_subtype_val
  have hscale : Continuous (fun y : SpherePolarRegion ↦ spherePolarScale (normal y)) :=
    continuous_spherePolarScale.comp hnormal
  have hscaleInv : Continuous
      (fun y : SpherePolarRegion ↦ (spherePolarScale (normal y))⁻¹) :=
    hscale.inv₀ fun y ↦ spherePolarScale_ne_zero y.2
  have hsource : Continuous
      (fun y : SpherePolarRegion ↦ spherePolarSourceProjection y.1) :=
    continuous_spherePolarSourceProjection.comp continuous_subtype_val
  exact hscaleInv.smul hsource

/-- The inverse polar-coordinate map is continuous. -/
theorem continuous_spherePolarInverse : Continuous spherePolarInverse := by
  have hnormal : Continuous
      (fun y : SpherePolarRegion ↦ standardUnlinkNormalProjection y.1) :=
    continuous_standardUnlinkNormalProjection.comp continuous_subtype_val
  exact continuous_spherePolarSource.prodMk (hnormal.subtype_mk fun y ↦ y.2)

/-- The polar-coordinate equivalence as a homeomorphism. -/
def spherePolarHomeomorph :
    (Sphere 2 × UnlinkUnitNormalDisk) ≃ₜ SpherePolarRegion :=
  Homeomorph.mk spherePolarEquiv continuous_spherePolarForward continuous_spherePolarInverse

@[simp]
theorem spherePolarHomeomorph_apply (p : Sphere 2 × UnlinkUnitNormalDisk) :
    spherePolarHomeomorph p = spherePolarForward p := rfl

@[simp]
theorem spherePolarHomeomorph_symm_apply (y : SpherePolarRegion) :
    spherePolarHomeomorph.symm y = spherePolarInverse y := rfl

@[simp]
theorem norm_standardUnlinkNormalCenter (i : Fin 2) :
    ‖standardUnlinkNormalCenter i‖ = 1 / 2 := by
  have hsq : ‖standardUnlinkNormalCenter i‖ ^ 2 = (1 / 2 : ℝ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    fin_cases i <;>
      simp [standardUnlinkNormalCenter, standardUnlinkHeight, Fin.sum_univ_succ]
  nlinarith [norm_nonneg (standardUnlinkNormalCenter i)]

theorem standardUnlinkNormalCenter_mem_unitBall (i : Fin 2) :
    standardUnlinkNormalCenter i ∈ ball (0 : UnlinkNormalPlane) 1 := by
  rw [mem_ball_zero_iff, norm_standardUnlinkNormalCenter]
  norm_num

@[simp]
theorem spherePolarScale_standardUnlinkNormalCenter (i : Fin 2) :
    spherePolarScale (standardUnlinkNormalCenter i) = standardUnlinkRadius := by
  have hscaleSq := spherePolarScale_sq (standardUnlinkNormalCenter_mem_unitBall i)
  rw [norm_standardUnlinkNormalCenter] at hscaleSq
  have hscalePos := spherePolarScale_pos (standardUnlinkNormalCenter_mem_unitBall i)
  nlinarith [standardUnlinkRadius_sq, standardUnlinkRadius_pos]

/-- Either unlink center regarded as a point of the open unit normal disk. -/
def standardUnlinkNormalCenterInUnitDisk (i : Fin 2) : UnlinkUnitNormalDisk :=
  ⟨standardUnlinkNormalCenter i, standardUnlinkNormalCenter_mem_unitBall i⟩

/-- The polar zero section at a normal center is the displayed unlink parametrization. -/
theorem spherePolarForward_standardUnlinkNormalCenter (i : Fin 2) (x : Sphere 2) :
    (spherePolarForward (x, standardUnlinkNormalCenterInUnitDisk i)).1 =
      standardUnlinkSphereMap i x := by
  apply Subtype.ext
  change spherePolarAmbientMap x.1 (standardUnlinkNormalCenter i) =
    standardUnlinkAmbientMap i x.1
  unfold spherePolarAmbientMap
  rw [spherePolarScale_standardUnlinkNormalCenter]
  ext j
  fin_cases j <;>
    simp [standardUnlinkNormalCenter, standardUnlinkAmbientMap]

/-- A disk of radius below `1/2` around either unlink center lies in the unit normal disk. -/
theorem ball_standardUnlinkNormalCenter_subset_unitBall
    (i : Fin 2) {r : ℝ} (hr : r < 1 / 2) :
    ball (standardUnlinkNormalCenter i) r ⊆ ball (0 : UnlinkNormalPlane) 1 := by
  intro v hv
  rw [mem_ball] at hv ⊢
  calc
    dist v 0 ≤ dist v (standardUnlinkNormalCenter i) +
        dist (standardUnlinkNormalCenter i) 0 := dist_triangle _ _ _
    _ = dist v (standardUnlinkNormalCenter i) + 1 / 2 := by
      rw [dist_zero_right, norm_standardUnlinkNormalCenter]
    _ < r + 1 / 2 := by linarith
    _ < 1 := by linarith

/-- Every sufficiently small coordinate tube lies in the polar region. -/
theorem standardUnlinkOpenTube_subset_polarRegion
    (i : Fin 2) {r : ℝ} (hr : r < 1 / 2) :
    standardUnlinkOpenTube i r ⊆
      {y : Sphere 4 | standardUnlinkNormalProjection y ∈ ball 0 1} :=
  preimage_mono (ball_standardUnlinkNormalCenter_subset_unitBall i hr)

/-- The open disk in the normal plane centered at component `i`, as a bundled open set. -/
def unlinkNormalDisk (i : Fin 2) (r : ℝ) : Opens UnlinkNormalPlane :=
  ⟨ball (standardUnlinkNormalCenter i) r, isOpen_ball⟩

/-- The displayed normal disk as a manifold subtype. -/
abbrev UnlinkNormalDisk (i : Fin 2) (r : ℝ) := unlinkNormalDisk i r

/-- A coordinate tube bundled as an open subset of `S⁴`. -/
def standardUnlinkOpenTubeOpens (i : Fin 2) (r : ℝ) : Opens (Sphere 4) :=
  ⟨standardUnlinkOpenTube i r, isOpen_standardUnlinkOpenTube i r⟩

/-- A coordinate tube regarded as a manifold subspace of `S⁴`. -/
abbrev StandardUnlinkOpenTubeSpace (i : Fin 2) (r : ℝ) :=
  standardUnlinkOpenTubeOpens i r

/-- The corresponding subset on the source of the global polar homeomorphism. -/
def spherePolarTubeDomainSet (i : Fin 2) (r : ℝ) :
    Set (Sphere 2 × UnlinkUnitNormalDisk) :=
  {p | p.2.1 ∈ ball (standardUnlinkNormalCenter i) r}

/-- The corresponding subset on the target of the global polar homeomorphism. -/
def spherePolarTubeRegionSet (i : Fin 2) (r : ℝ) : Set SpherePolarRegion :=
  {y | y.1 ∈ standardUnlinkOpenTube i r}

/-- The global polar map takes the normal-disk restriction to exactly the tube restriction. -/
theorem image_spherePolarForward_spherePolarTubeDomainSet (i : Fin 2) (r : ℝ) :
    spherePolarForward '' spherePolarTubeDomainSet i r =
      spherePolarTubeRegionSet i r := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    change standardUnlinkNormalProjection (spherePolarForward p) ∈
      ball (standardUnlinkNormalCenter i) r
    rw [standardUnlinkNormalProjection_spherePolarForward]
    exact hp
  · intro hy
    refine ⟨spherePolarInverse y, ?_, spherePolarForward_inverse y⟩
    change standardUnlinkNormalProjection y.1 ∈
      ball (standardUnlinkNormalCenter i) r
    exact hy

/-- Restriction of the global polar homeomorphism to one coordinate tube. -/
def spherePolarTubeRestrictionHomeomorph (i : Fin 2) (r : ℝ) :
    spherePolarTubeDomainSet i r ≃ₜ spherePolarTubeRegionSet i r :=
  spherePolarHomeomorph.toPartialHomeomorph.homeomorphOfImageSubsetSource
    (by simp) (image_spherePolarForward_spherePolarTubeDomainSet i r)

/-- Flatten the nested source subtype to `S² ×` the displayed normal disk. -/
def spherePolarTubeDomainHomeomorph (i : Fin 2) (r : ℝ)
    (hsub : ball (standardUnlinkNormalCenter i) r ⊆ ball (0 : UnlinkNormalPlane) 1) :
    (Sphere 2 × UnlinkNormalDisk i r) ≃ₜ spherePolarTubeDomainSet i r where
  toFun p := ⟨(p.1, ⟨p.2.1, hsub p.2.2⟩), p.2.2⟩
  invFun p := (p.1.1, ⟨p.1.2.1, p.2⟩)
  left_inv p := rfl
  right_inv p := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Forget the redundant polar-region subtype on a sufficiently small tube. -/
def spherePolarTubeRegionHomeomorph (i : Fin 2) {r : ℝ} (hr : r < 1 / 2) :
    spherePolarTubeRegionSet i r ≃ₜ StandardUnlinkOpenTubeSpace i r where
  toFun y := ⟨y.1.1, y.2⟩
  invFun y := ⟨⟨y.1, standardUnlinkOpenTube_subset_polarRegion i hr y.2⟩, y.2⟩
  left_inv y := rfl
  right_inv y := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Each sufficiently small coordinate tube is homeomorphic to `S² × B²`. -/
def standardUnlinkOpenTubeHomeomorph (i : Fin 2) {r : ℝ} (hr : r < 1 / 2) :
    (Sphere 2 × UnlinkNormalDisk i r) ≃ₜ StandardUnlinkOpenTubeSpace i r :=
  (spherePolarTubeDomainHomeomorph i r
      (ball_standardUnlinkNormalCenter_subset_unitBall i hr)).trans
    ((spherePolarTubeRestrictionHomeomorph i r).trans
      (spherePolarTubeRegionHomeomorph i hr))

/-- The center of the displayed normal disk, available whenever its radius is positive. -/
def standardUnlinkNormalCenterInDisk (i : Fin 2) {r : ℝ} (hr : 0 < r) :
    UnlinkNormalDisk i r :=
  ⟨standardUnlinkNormalCenter i, mem_ball_self hr⟩

/-- Under the tube product homeomorphism, the center section is exactly the unlink component. -/
theorem standardUnlinkOpenTubeHomeomorph_centerSection
    (i : Fin 2) {r : ℝ} (hr : 0 < r) (hrhalf : r < 1 / 2) (x : Sphere 2) :
    (standardUnlinkOpenTubeHomeomorph i hrhalf
      (x, standardUnlinkNormalCenterInDisk i hr)).1 = standardUnlinkSphereMap i x := by
  apply spherePolarForward_standardUnlinkNormalCenter

/-- Inclusion of a small normal-disk product into the global polar-product domain. -/
def spherePolarTubeDomainInclusion (i : Fin 2) {r : ℝ} (hr : r < 1 / 2) :
    Sphere 2 × UnlinkNormalDisk i r → Sphere 2 × UnlinkUnitNormalDisk :=
  fun p ↦ (p.1, ⟨p.2.1, ball_standardUnlinkNormalCenter_subset_unitBall i hr p.2.2⟩)

/-- The domain inclusion is smooth. -/
theorem contMDiff_spherePolarTubeDomainInclusion (i : Fin 2) {r : ℝ} (hr : r < 1 / 2) :
    ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))) ∞
      (spherePolarTubeDomainInclusion i hr) := by
  have hsub : unlinkNormalDisk i r ≤ unlinkUnitNormalDisk :=
    ball_standardUnlinkNormalCenter_subset_unitBall i hr
  have hinc : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞
      (Opens.inclusion hsub) :=
    contMDiff_inclusion hsub
  exact (contMDiff_fst.prodMk (hinc.comp contMDiff_snd)).congr fun _ ↦ rfl

/-- Inclusion of a small coordinate tube into the global polar region. -/
def spherePolarTubeRegionInclusion (i : Fin 2) {r : ℝ} (hr : r < 1 / 2) :
    StandardUnlinkOpenTubeSpace i r → SpherePolarRegion :=
  fun y ↦ ⟨y.1, standardUnlinkOpenTube_subset_polarRegion i hr y.2⟩

/-- The tube-to-polar-region inclusion is smooth. -/
theorem contMDiff_spherePolarTubeRegionInclusion (i : Fin 2) {r : ℝ} (hr : r < 1 / 2) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (spherePolarTubeRegionInclusion i hr) := by
  have hsub : standardUnlinkOpenTubeOpens i r ≤ spherePolarRegion :=
    standardUnlinkOpenTube_subset_polarRegion i hr
  exact contMDiff_inclusion hsub

/-- Smoothness of the restricted tube homeomorphism. -/
theorem contMDiff_standardUnlinkOpenTubeHomeomorph
    (i : Fin 2) {r : ℝ} (hr : r < 1 / 2) :
    ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (standardUnlinkOpenTubeHomeomorph i hr) := by
  apply (ContMDiff.subtypeVal_comp_iff (standardUnlinkOpenTubeOpens i r) _).mp
  have hpolar := contMDiff_spherePolarForward.comp
    (contMDiff_spherePolarTubeDomainInclusion i hr)
  have hambient := contMDiff_subtype_val.comp hpolar
  exact hambient.congr fun _ ↦ rfl

/-- Smoothness of the inverse restricted tube homeomorphism. -/
theorem contMDiff_standardUnlinkOpenTubeHomeomorph_symm
    (i : Fin 2) {r : ℝ} (hr : r < 1 / 2) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))) ∞
      (standardUnlinkOpenTubeHomeomorph i hr).symm := by
  have hregion := contMDiff_spherePolarTubeRegionInclusion i hr
  have hsource := contMDiff_spherePolarSource.comp hregion
  have hnormal : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞
      (fun y : StandardUnlinkOpenTubeSpace i r ↦
        standardUnlinkNormalProjection y.1) :=
    contMDiff_standardUnlinkNormalProjection.comp contMDiff_subtype_val
  have hnormalDisk : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞
      (fun y : StandardUnlinkOpenTubeSpace i r ↦
        (⟨standardUnlinkNormalProjection y.1, y.2⟩ : UnlinkNormalDisk i r)) := by
    apply (ContMDiff.subtypeVal_comp_iff (unlinkNormalDisk i r) _).mp
    exact hnormal
  exact (hsource.prodMk hnormalDisk).congr fun _ ↦ rfl

/-- Each sufficiently small coordinate tube is smoothly diffeomorphic to `S² × B²`. -/
def standardUnlinkOpenTubeDiffeomorph (i : Fin 2) {r : ℝ} (hr : r < 1 / 2) :
    (Sphere 2 × UnlinkNormalDisk i r) ≃ₘ^∞⟮
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))),
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))⟯
        StandardUnlinkOpenTubeSpace i r where
  toEquiv := (standardUnlinkOpenTubeHomeomorph i hr).toEquiv
  contMDiff_toFun := contMDiff_standardUnlinkOpenTubeHomeomorph i hr
  contMDiff_invFun := contMDiff_standardUnlinkOpenTubeHomeomorph_symm i hr

@[simp]
theorem standardUnlinkOpenTubeDiffeomorph_apply
    (i : Fin 2) {r : ℝ} (hr : r < 1 / 2) (p : Sphere 2 × UnlinkNormalDisk i r) :
    standardUnlinkOpenTubeDiffeomorph i hr p = standardUnlinkOpenTubeHomeomorph i hr p := rfl

/-- The central section of the smooth tube product is exactly the displayed unlink component. -/
theorem standardUnlinkOpenTubeDiffeomorph_centerSection
    (i : Fin 2) {r : ℝ} (hr : 0 < r) (hrhalf : r < 1 / 2) (x : Sphere 2) :
    (standardUnlinkOpenTubeDiffeomorph i hrhalf
      (x, standardUnlinkNormalCenterInDisk i hr)).1 = standardUnlinkSphereMap i x :=
  standardUnlinkOpenTubeHomeomorph_centerSection i hr hrhalf x

end SplittingSpheres
