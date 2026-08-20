/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.EquatorImmersion

/-!
# Smooth parametrizations of the standard unlink components

This file parametrizes the two frozen round `2`-spheres in `S⁴` and proves their smooth-embedding
properties directly.  The immersion proof uses stereographic projection from the corresponding
point of the small round sphere; after translating the target chart, the parametrization is an
exact linear coordinate inclusion with a two-dimensional normal complement.
-/

@[expose] public section

open Metric Set Topology
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace SplittingSpheres

/-- The frozen fourth coordinate of standard unlink component `i`. -/
def standardUnlinkHeight (i : Fin 2) : ℝ :=
  if i = 0 then -(1 / 2 : ℝ) else 1 / 2

@[simp]
theorem standardUnlinkHeight_zero : standardUnlinkHeight 0 = -(1 / 2 : ℝ) := by
  simp [standardUnlinkHeight]

@[simp]
theorem standardUnlinkHeight_one : standardUnlinkHeight 1 = 1 / 2 := by
  simp [standardUnlinkHeight]

@[simp]
theorem standardUnlinkHeight_sq (i : Fin 2) : standardUnlinkHeight i ^ 2 = 1 / 4 := by
  fin_cases i <;> norm_num

/-- The radius `√3 / 2` of either frozen round component. -/
def standardUnlinkRadius : ℝ :=
  Real.sqrt 3 / 2

theorem standardUnlinkRadius_pos : 0 < standardUnlinkRadius := by
  unfold standardUnlinkRadius
  positivity

theorem standardUnlinkRadius_ne_zero : standardUnlinkRadius ≠ 0 :=
  standardUnlinkRadius_pos.ne'

@[simp]
theorem standardUnlinkRadius_sq : standardUnlinkRadius ^ 2 = 3 / 4 := by
  unfold standardUnlinkRadius
  rw [div_pow, Real.sq_sqrt (by positivity)]
  norm_num

/-- The affine ambient map whose restriction to the unit `2`-sphere parametrizes component `i`. -/
def standardUnlinkAmbientMap (i : Fin 2) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 ![standardUnlinkRadius * x 0, standardUnlinkRadius * x 1,
    standardUnlinkRadius * x 2, standardUnlinkHeight i, 0]

@[simp]
theorem standardUnlinkAmbientMap_apply_zero (i : Fin 2)
    (x : EuclideanSpace ℝ (Fin 3)) :
    standardUnlinkAmbientMap i x 0 = standardUnlinkRadius * x 0 := rfl

@[simp]
theorem standardUnlinkAmbientMap_apply_one (i : Fin 2)
    (x : EuclideanSpace ℝ (Fin 3)) :
    standardUnlinkAmbientMap i x 1 = standardUnlinkRadius * x 1 := rfl

@[simp]
theorem standardUnlinkAmbientMap_apply_two (i : Fin 2)
    (x : EuclideanSpace ℝ (Fin 3)) :
    standardUnlinkAmbientMap i x 2 = standardUnlinkRadius * x 2 := rfl

@[simp]
theorem standardUnlinkAmbientMap_apply_three (i : Fin 2)
    (x : EuclideanSpace ℝ (Fin 3)) :
    standardUnlinkAmbientMap i x 3 = standardUnlinkHeight i := rfl

@[simp]
theorem standardUnlinkAmbientMap_apply_four (i : Fin 2)
    (x : EuclideanSpace ℝ (Fin 3)) :
    standardUnlinkAmbientMap i x 4 = 0 := rfl

theorem norm_standardUnlinkAmbientMap_of_mem_sphere (i : Fin 2) (x : Sphere 2) :
    ‖standardUnlinkAmbientMap i x.1‖ = 1 := by
  have hxnorm : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using x.2
  have hxsum : x.1 0 ^ 2 + (x.1 1 ^ 2 + x.1 2 ^ 2) = 1 := by
    simpa [hxnorm, Fin.sum_univ_succ] using
      (EuclideanSpace.real_norm_sq_eq (x : EuclideanSpace ℝ (Fin 3))).symm
  have hsq : ‖standardUnlinkAmbientMap i x.1‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change (standardUnlinkRadius * x.1 0) ^ 2 +
      ((standardUnlinkRadius * x.1 1) ^ 2 +
        ((standardUnlinkRadius * x.1 2) ^ 2 +
          (standardUnlinkHeight i ^ 2 + 0 ^ 2))) = 1
    rw [mul_pow, mul_pow, mul_pow, standardUnlinkRadius_sq,
      standardUnlinkHeight_sq]
    nlinarith
  nlinarith [norm_nonneg (standardUnlinkAmbientMap i x.1)]

/-- The explicit parametrization of standard unlink component `i`. -/
def standardUnlinkSphereMap (i : Fin 2) (x : Sphere 2) : Sphere 4 :=
  ⟨standardUnlinkAmbientMap i x.1, by
    simpa [mem_sphere_zero_iff_norm] using norm_standardUnlinkAmbientMap_of_mem_sphere i x⟩

@[simp]
theorem standardUnlinkSphereMap_coe (i : Fin 2) (x : Sphere 2) :
    (standardUnlinkSphereMap i x).1 = standardUnlinkAmbientMap i x.1 := rfl

theorem standardUnlinkSphereMap_injective (i : Fin 2) :
    Function.Injective (standardUnlinkSphereMap i) := by
  intro x y hxy
  have hval := congrArg Subtype.val hxy
  apply Subtype.ext
  ext j
  fin_cases j
  · have h := congrArg (fun z : EuclideanSpace ℝ (Fin 5) ↦ z 0) hval
    exact (mul_left_cancel₀ standardUnlinkRadius_ne_zero h)
  · have h := congrArg (fun z : EuclideanSpace ℝ (Fin 5) ↦ z 1) hval
    exact (mul_left_cancel₀ standardUnlinkRadius_ne_zero h)
  · have h := congrArg (fun z : EuclideanSpace ℝ (Fin 5) ↦ z 2) hval
    exact (mul_left_cancel₀ standardUnlinkRadius_ne_zero h)

theorem contMDiff_standardUnlinkSphereMap (i : Fin 2) :
    ContMDiff (𝓡 2) (𝓡 4) ∞ (standardUnlinkSphereMap i) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) := ⟨by simp⟩
  have ha : ContDiff ℝ ∞ (standardUnlinkAmbientMap i) := by
    rw [contDiff_piLp]
    intro j
    fin_cases j <;> simp [standardUnlinkAmbientMap] <;> fun_prop
  have h : ContMDiff (𝓡 2) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5))) ∞
      (fun x : Sphere 2 ↦ standardUnlinkAmbientMap i x.1) :=
    ha.comp_contMDiff contMDiff_coe_sphere
  exact (h.codRestrict_sphere (n := 4) fun x ↦ (standardUnlinkSphereMap i x).2).congr
    fun _ ↦ rfl

theorem isEmbedding_standardUnlinkSphereMap (i : Fin 2) :
    IsEmbedding (standardUnlinkSphereMap i) :=
  (contMDiff_standardUnlinkSphereMap i).continuous.isClosedEmbedding
    (standardUnlinkSphereMap_injective i) |>.isEmbedding

/-- Insert a vector in the first three coordinates of `ℝ⁵`. -/
def standardUnlinkAmbientInclusion (u : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 ![u 0, u 1, u 2, 0, 0]

@[simp]
theorem standardUnlinkAmbientInclusion_apply_zero (u : EuclideanSpace ℝ (Fin 3)) :
    standardUnlinkAmbientInclusion u 0 = u 0 := rfl

@[simp]
theorem standardUnlinkAmbientInclusion_apply_one (u : EuclideanSpace ℝ (Fin 3)) :
    standardUnlinkAmbientInclusion u 1 = u 1 := rfl

@[simp]
theorem standardUnlinkAmbientInclusion_apply_two (u : EuclideanSpace ℝ (Fin 3)) :
    standardUnlinkAmbientInclusion u 2 = u 2 := rfl

@[simp]
theorem standardUnlinkAmbientInclusion_apply_three (u : EuclideanSpace ℝ (Fin 3)) :
    standardUnlinkAmbientInclusion u 3 = 0 := rfl

@[simp]
theorem standardUnlinkAmbientInclusion_apply_four (u : EuclideanSpace ℝ (Fin 3)) :
    standardUnlinkAmbientInclusion u 4 = 0 := rfl

theorem norm_standardUnlinkAmbientInclusion (u : EuclideanSpace ℝ (Fin 3)) :
    ‖standardUnlinkAmbientInclusion u‖ = ‖u‖ := by
  have hsq : ‖standardUnlinkAmbientInclusion u‖ ^ 2 = ‖u‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, standardUnlinkAmbientInclusion,
      Fin.sum_univ_succ]
  nlinarith [norm_nonneg (standardUnlinkAmbientInclusion u), norm_nonneg u]

/-- First-three-coordinate insertion as a linear isometry. -/
def standardUnlinkLinearIsometry :
    EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 5) where
  toFun := standardUnlinkAmbientInclusion
  map_add' u v := by
    ext j
    fin_cases j <;> simp [standardUnlinkAmbientInclusion]
  map_smul' c u := by
    ext j
    fin_cases j <;> simp [standardUnlinkAmbientInclusion]
  norm_map' := norm_standardUnlinkAmbientInclusion

@[simp]
theorem standardUnlinkLinearIsometry_apply (u : EuclideanSpace ℝ (Fin 3)) :
    standardUnlinkLinearIsometry u = standardUnlinkAmbientInclusion u := rfl

/-- The coordinate-three unit vector. -/
def standardUnlinkNormalThree : EuclideanSpace ℝ (Fin 5) :=
  EuclideanSpace.single 3 1

/-- The coordinate-four unit vector. -/
def standardUnlinkNormalFour : EuclideanSpace ℝ (Fin 5) :=
  EuclideanSpace.single 4 1

@[simp]
theorem standardUnlinkNormalThree_apply (j : Fin 5) :
    standardUnlinkNormalThree j = if j = 3 then 1 else 0 := by
  simp [standardUnlinkNormalThree]

@[simp]
theorem standardUnlinkNormalFour_apply (j : Fin 5) :
    standardUnlinkNormalFour j = if j = 4 then 1 else 0 := by
  simp [standardUnlinkNormalFour]

theorem standardUnlinkAmbientMap_eq (i : Fin 2) (x : EuclideanSpace ℝ (Fin 3)) :
    standardUnlinkAmbientMap i x =
      standardUnlinkRadius • standardUnlinkLinearIsometry x +
        standardUnlinkHeight i • standardUnlinkNormalThree := by
  ext j
  fin_cases j <;>
    simp [standardUnlinkAmbientMap, standardUnlinkAmbientInclusion,
      standardUnlinkNormalThree]

theorem inner_standardUnlinkAmbientInclusion (u v : EuclideanSpace ℝ (Fin 3)) :
    ⟪standardUnlinkAmbientInclusion u, standardUnlinkAmbientInclusion v⟫_ℝ =
      ⟪u, v⟫_ℝ := by
  exact LinearIsometry.inner_map_map standardUnlinkLinearIsometry u v

theorem inner_standardUnlinkAmbientInclusion_normalThree
    (u : EuclideanSpace ℝ (Fin 3)) :
    ⟪standardUnlinkAmbientInclusion u, standardUnlinkNormalThree⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]
  simp [standardUnlinkAmbientInclusion, standardUnlinkNormalThree]

theorem inner_standardUnlinkNormalThree_ambientInclusion
    (u : EuclideanSpace ℝ (Fin 3)) :
    ⟪standardUnlinkNormalThree, standardUnlinkAmbientInclusion u⟫_ℝ = 0 := by
  rw [real_inner_comm]
  exact inner_standardUnlinkAmbientInclusion_normalThree u

theorem inner_standardUnlinkAmbientInclusion_normalFour
    (u : EuclideanSpace ℝ (Fin 3)) :
    ⟪standardUnlinkAmbientInclusion u, standardUnlinkNormalFour⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]
  simp [standardUnlinkAmbientInclusion, standardUnlinkNormalFour]

@[simp]
theorem inner_standardUnlinkNormalThree_self :
    ⟪standardUnlinkNormalThree, standardUnlinkNormalThree⟫_ℝ = 1 := by
  rw [PiLp.inner_apply]
  simp [standardUnlinkNormalThree]

@[simp]
theorem norm_standardUnlinkNormalThree : ‖standardUnlinkNormalThree‖ = 1 := by
  have h := inner_standardUnlinkNormalThree_self
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg standardUnlinkNormalThree]

@[simp]
theorem inner_standardUnlinkNormalFour_self :
    ⟪standardUnlinkNormalFour, standardUnlinkNormalFour⟫_ℝ = 1 := by
  rw [PiLp.inner_apply]
  simp [standardUnlinkNormalFour]

@[simp]
theorem inner_standardUnlinkNormalThree_normalFour :
    ⟪standardUnlinkNormalThree, standardUnlinkNormalFour⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]
  simp [standardUnlinkNormalThree, standardUnlinkNormalFour]

theorem inner_standardUnlinkAmbientMap (i : Fin 2) (x z : EuclideanSpace ℝ (Fin 3)) :
    ⟪standardUnlinkAmbientMap i x, standardUnlinkAmbientMap i z⟫_ℝ =
      standardUnlinkRadius ^ 2 * ⟪x, z⟫_ℝ + standardUnlinkHeight i ^ 2 := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [standardUnlinkAmbientMap, Fin.sum_univ_succ]
  ring_nf
  rw [standardUnlinkRadius_sq, standardUnlinkHeight_sq]
  ring

/-- The other unit tangent direction in the meridian plane of the small round sphere. -/
def standardUnlinkMeridianNormal (i : Fin 2) (x : Sphere 2) :
    EuclideanSpace ℝ (Fin 5) :=
  standardUnlinkHeight i • standardUnlinkLinearIsometry x.1 +
    standardUnlinkRadius • standardUnlinkNormalThree

@[simp]
theorem standardUnlinkMeridianNormal_apply_three (i : Fin 2) (x : Sphere 2) :
    standardUnlinkMeridianNormal i x 3 = standardUnlinkRadius := by
  simp [standardUnlinkMeridianNormal, standardUnlinkNormalThree]

@[simp]
theorem standardUnlinkMeridianNormal_apply_four (i : Fin 2) (x : Sphere 2) :
    standardUnlinkMeridianNormal i x 4 = 0 := by
  simp [standardUnlinkMeridianNormal, standardUnlinkNormalThree]

theorem standardUnlinkSphereMap_neg_source_coe (i : Fin 2) (x : Sphere 2) :
    ((standardUnlinkSphereMap i (-x) : Sphere 4) : EuclideanSpace ℝ (Fin 5)) =
      -standardUnlinkRadius • standardUnlinkLinearIsometry x.1 +
        standardUnlinkHeight i • standardUnlinkNormalThree := by
  rw [standardUnlinkSphereMap_coe, standardUnlinkAmbientMap_eq]
  change standardUnlinkRadius • standardUnlinkLinearIsometry
      (-(x : EuclideanSpace ℝ (Fin 3))) + _ = _
  rw [map_neg, smul_neg]
  simp

theorem inner_standardUnlinkPole_meridian (i : Fin 2) (x : Sphere 2) :
    ⟪((standardUnlinkSphereMap i (-x) : Sphere 4) : EuclideanSpace ℝ (Fin 5)),
      standardUnlinkMeridianNormal i x⟫_ℝ = 0 := by
  have hxnorm : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using x.2
  rw [standardUnlinkSphereMap_neg_source_coe]
  simp only [standardUnlinkMeridianNormal, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, standardUnlinkLinearIsometry_apply,
    real_inner_self_eq_norm_sq, map_neg, RCLike.star_def]
  rw [norm_standardUnlinkAmbientInclusion, hxnorm, norm_standardUnlinkNormalThree,
    inner_standardUnlinkAmbientInclusion_normalThree,
    inner_standardUnlinkNormalThree_ambientInclusion]
  norm_num
  ring

theorem inner_standardUnlinkPole_map (i : Fin 2) (x z : Sphere 2) :
    ⟪((standardUnlinkSphereMap i (-x) : Sphere 4) : EuclideanSpace ℝ (Fin 5)),
      ((standardUnlinkSphereMap i z : Sphere 4) : EuclideanSpace ℝ (Fin 5))⟫_ℝ =
        standardUnlinkHeight i ^ 2 -
          standardUnlinkRadius ^ 2 * ⟪(x : EuclideanSpace ℝ (Fin 3)), z⟫_ℝ := by
  change ⟪standardUnlinkAmbientMap i (-(x : EuclideanSpace ℝ (Fin 3))),
    standardUnlinkAmbientMap i (z : EuclideanSpace ℝ (Fin 3))⟫_ℝ = _
  rw [inner_standardUnlinkAmbientMap, inner_neg_left]
  simp
  ring

/-- The constant part of the raw target stereographic coordinates of a component. -/
def standardUnlinkStereoOffset (i : Fin 2) (x : Sphere 2) :
    EuclideanSpace ℝ (Fin 5) :=
  (2 * standardUnlinkHeight i ^ 2 / standardUnlinkRadius) •
      standardUnlinkLinearIsometry x.1 +
    (2 * standardUnlinkHeight i) • standardUnlinkNormalThree

theorem source_stereographic_denominator_ne_zero {x z : Sphere 2} (hz : z ≠ -x) :
    1 + ⟪(x : EuclideanSpace ℝ (Fin 3)), z⟫_ℝ ≠ 0 := by
  have hxnorm : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using x.2
  have hznorm : ‖(z : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using z.2
  intro hzero
  have hinner : ⟪(x : EuclideanSpace ℝ (Fin 3)), z⟫_ℝ = -1 := by
    linarith
  have hval : (x : EuclideanSpace ℝ (Fin 3)) = -(z : EuclideanSpace ℝ (Fin 3)) :=
    (inner_eq_neg_one_iff_of_norm_eq_one hxnorm hznorm).mp hinner
  apply hz
  apply Subtype.ext
  simpa only [coe_neg_sphere, neg_neg] using (congrArg Neg.neg hval).symm

/-- Stereographic projection from the corresponding point on the small round sphere is affine in
the preferred source stereographic coordinates. -/
theorem coe_stereoToFun_standardUnlink (i : Fin 2) (x z : Sphere 2) (hz : z ≠ -x) :
    ((stereoToFun
      ((standardUnlinkSphereMap i (-x) : Sphere 4) : EuclideanSpace ℝ (Fin 5))
      ((standardUnlinkSphereMap i z : Sphere 4) : EuclideanSpace ℝ (Fin 5)) :
        (ℝ ∙ ((standardUnlinkSphereMap i (-x) : Sphere 4) :
          EuclideanSpace ℝ (Fin 5)))ᗮ) : EuclideanSpace ℝ (Fin 5)) =
      standardUnlinkRadius⁻¹ • standardUnlinkLinearIsometry
        ((stereoToFun (-(x : EuclideanSpace ℝ (Fin 3)))
          (z : EuclideanSpace ℝ (Fin 3)) :
            (ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 3))))ᗮ) :
              EuclideanSpace ℝ (Fin 3)) +
        standardUnlinkStereoOffset i x := by
  rw [stereoToFun_apply, stereoToFun_apply]
  change
    (2 / (1 - ⟪((standardUnlinkSphereMap i (-x) : Sphere 4) :
      EuclideanSpace ℝ (Fin 5)),
        ((standardUnlinkSphereMap i z : Sphere 4) : EuclideanSpace ℝ (Fin 5))⟫_ℝ)) •
      ((((ℝ ∙ ((standardUnlinkSphereMap i (-x) : Sphere 4) :
        EuclideanSpace ℝ (Fin 5)))ᗮ).orthogonalProjectionOnto
          ((standardUnlinkSphereMap i z : Sphere 4) : EuclideanSpace ℝ (Fin 5)) :
            (ℝ ∙ ((standardUnlinkSphereMap i (-x) : Sphere 4) :
              EuclideanSpace ℝ (Fin 5)))ᗮ) : EuclideanSpace ℝ (Fin 5)) =
    standardUnlinkRadius⁻¹ • standardUnlinkLinearIsometry
      ((2 / (1 - ⟪-(x : EuclideanSpace ℝ (Fin 3)),
        (z : EuclideanSpace ℝ (Fin 3))⟫_ℝ)) •
        ((((ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 3))))ᗮ).orthogonalProjectionOnto
          (z : EuclideanSpace ℝ (Fin 3)) :
            (ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 3))))ᗮ) :
              EuclideanSpace ℝ (Fin 3))) + standardUnlinkStereoOffset i x
  have hpoleNorm :
      ‖((standardUnlinkSphereMap i (-x) : Sphere 4) : EuclideanSpace ℝ (Fin 5))‖ = 1 := by
    simpa using norm_eq_of_mem_sphere (standardUnlinkSphereMap i (-x))
  have hsourceNorm : ‖-(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simp
  rw [coe_orthogonalProjectionOnto_span_orthogonal_apply _ _ hpoleNorm,
    coe_orthogonalProjectionOnto_span_orthogonal_apply _ _ hsourceNorm,
    inner_standardUnlinkPole_map]
  have hden := source_stereographic_denominator_ne_zero hz
  have htargetDen :
      1 - (standardUnlinkHeight i ^ 2 - standardUnlinkRadius ^ 2 *
        ⟪(x : EuclideanSpace ℝ (Fin 3)), z⟫_ℝ) =
        standardUnlinkRadius ^ 2 *
          (1 + ⟪(x : EuclideanSpace ℝ (Fin 3)), z⟫_ℝ) := by
    rw [standardUnlinkHeight_sq, standardUnlinkRadius_sq]
    ring
  rw [htargetDen]
  rw [inner_neg_left]
  simp only [map_neg, RCLike.star_def, neg_mul, sub_neg_eq_add]
  have hdenQuarter :
      3 / 4 + ⟪(x : EuclideanSpace ℝ (Fin 3)), z⟫_ℝ * (3 / 4) ≠ 0 := by
    intro hzero
    apply hden
    nlinarith
  unfold standardUnlinkStereoOffset
  ext j
  fin_cases j <;>
    simp [standardUnlinkSphereMap, standardUnlinkAmbientMap,
      standardUnlinkAmbientInclusion, standardUnlinkNormalThree]
  all_goals field_simp [standardUnlinkRadius_ne_zero, hden, hdenQuarter]
  all_goals try simp only [standardUnlinkRadius_sq]
  all_goals ring

theorem inner_standardUnlinkPole_inclusion (i : Fin 2) (x : Sphere 2)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ⟪((standardUnlinkSphereMap i (-x) : Sphere 4) : EuclideanSpace ℝ (Fin 5)),
      standardUnlinkAmbientInclusion u⟫_ℝ =
        -standardUnlinkRadius * ⟪(x : EuclideanSpace ℝ (Fin 3)), u⟫_ℝ := by
  rw [standardUnlinkSphereMap_neg_source_coe]
  simp [inner_add_left, inner_smul_left, standardUnlinkLinearIsometry_apply,
    inner_standardUnlinkAmbientInclusion,
    inner_standardUnlinkNormalThree_ambientInclusion]

theorem inner_standardUnlinkPole_normalFour (i : Fin 2) (x : Sphere 2) :
    ⟪((standardUnlinkSphereMap i (-x) : Sphere 4) : EuclideanSpace ℝ (Fin 5)),
      standardUnlinkNormalFour⟫_ℝ = 0 := by
  rw [standardUnlinkSphereMap_neg_source_coe]
  simp [inner_add_left, inner_smul_left, standardUnlinkLinearIsometry_apply,
    inner_standardUnlinkAmbientInclusion_normalFour,
    inner_standardUnlinkNormalThree_normalFour]

/-- The linear normal form obtained by adjoining the meridian and coordinate-four normals to the
two-dimensional tangent image. -/
def standardUnlinkTangentSumLinearMap (i : Fin 2) (x : Sphere 2) :
    (((ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 3))))ᗮ) × (ℝ × ℝ)) →ₗ[ℝ]
      (ℝ ∙ ((standardUnlinkSphereMap i (-x) : Sphere 4) :
        EuclideanSpace ℝ (Fin 5)))ᗮ where
  toFun p := ⟨standardUnlinkRadius⁻¹ • standardUnlinkLinearIsometry p.1.1 +
      p.2.1 • standardUnlinkMeridianNormal i x +
      p.2.2 • standardUnlinkNormalFour, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have hp : ⟪-(x : EuclideanSpace ℝ (Fin 3)), p.1.1⟫_ℝ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp p.1.2
    have hxu : ⟪(x : EuclideanSpace ℝ (Fin 3)), p.1.1⟫_ℝ = 0 := by
      rw [inner_neg_left] at hp
      simpa using hp
    simp only [inner_add_right, inner_smul_right,
      standardUnlinkLinearIsometry_apply, inner_standardUnlinkPole_inclusion,
      inner_standardUnlinkPole_meridian, inner_standardUnlinkPole_normalFour,
      hxu, mul_zero, add_zero]⟩
  map_add' p q := by
    apply Subtype.ext
    change standardUnlinkRadius⁻¹ • standardUnlinkLinearIsometry (p.1.1 + q.1.1) +
        (p.2.1 + q.2.1) • standardUnlinkMeridianNormal i x +
        (p.2.2 + q.2.2) • standardUnlinkNormalFour =
      (standardUnlinkRadius⁻¹ • standardUnlinkLinearIsometry p.1.1 +
          p.2.1 • standardUnlinkMeridianNormal i x +
          p.2.2 • standardUnlinkNormalFour) +
        (standardUnlinkRadius⁻¹ • standardUnlinkLinearIsometry q.1.1 +
          q.2.1 • standardUnlinkMeridianNormal i x +
          q.2.2 • standardUnlinkNormalFour)
    rw [map_add, smul_add, add_smul, add_smul]
    abel
  map_smul' c p := by
    apply Subtype.ext
    change standardUnlinkRadius⁻¹ • standardUnlinkLinearIsometry (c • p.1.1) +
        (c * p.2.1) • standardUnlinkMeridianNormal i x +
        (c * p.2.2) • standardUnlinkNormalFour =
      c • (standardUnlinkRadius⁻¹ • standardUnlinkLinearIsometry p.1.1 +
        p.2.1 • standardUnlinkMeridianNormal i x +
        p.2.2 • standardUnlinkNormalFour)
    rw [map_smul, smul_add, smul_add, smul_smul, smul_smul]
    simp only [mul_smul]
    rw [smul_comm standardUnlinkRadius⁻¹ c]

theorem standardUnlinkTangentSumLinearMap_injective (i : Fin 2) (x : Sphere 2) :
    Function.Injective (standardUnlinkTangentSumLinearMap i x) := by
  intro p q hpq
  have hpqVal := congrArg Subtype.val hpq
  change standardUnlinkRadius⁻¹ • standardUnlinkLinearIsometry p.1.1 +
      p.2.1 • standardUnlinkMeridianNormal i x +
      p.2.2 • standardUnlinkNormalFour =
    standardUnlinkRadius⁻¹ • standardUnlinkLinearIsometry q.1.1 +
      q.2.1 • standardUnlinkMeridianNormal i x +
      q.2.2 • standardUnlinkNormalFour at hpqVal
  have hfour := congrArg (fun y : EuclideanSpace ℝ (Fin 5) ↦ y 4) hpqVal
  have hsecond : p.2.2 = q.2.2 := by
    simpa [standardUnlinkMeridianNormal, standardUnlinkAmbientInclusion,
      standardUnlinkNormalThree, standardUnlinkNormalFour] using hfour
  have hthree := congrArg (fun y : EuclideanSpace ℝ (Fin 5) ↦ y 3) hpqVal
  have hfirst : p.2.1 = q.2.1 := by
    have hr : p.2.1 * standardUnlinkRadius = q.2.1 * standardUnlinkRadius := by
      simpa [standardUnlinkMeridianNormal, standardUnlinkAmbientInclusion,
        standardUnlinkNormalThree, standardUnlinkNormalFour] using hthree
    exact mul_right_cancel₀ standardUnlinkRadius_ne_zero hr
  rw [hfirst, hsecond] at hpqVal
  have htangentScaled :
      standardUnlinkRadius⁻¹ • standardUnlinkLinearIsometry p.1.1 =
        standardUnlinkRadius⁻¹ • standardUnlinkLinearIsometry q.1.1 := by
    exact add_right_cancel (add_right_cancel hpqVal)
  have htangentImage :
      standardUnlinkLinearIsometry p.1.1 = standardUnlinkLinearIsometry q.1.1 :=
    smul_right_injective _ (inv_ne_zero standardUnlinkRadius_ne_zero) htangentScaled
  have htangent : p.1 = q.1 :=
    Subtype.ext (standardUnlinkLinearIsometry.injective htangentImage)
  exact Prod.ext htangent (Prod.ext hfirst hsecond)

theorem finrank_standardUnlinkSourceTangent (x : Sphere 2) :
    Module.finrank ℝ ((ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 3))))ᗮ) = 2 := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  exact Submodule.finrank_orthogonal_span_singleton
    (n := 2) (ne_zero_of_mem_unit_sphere (-x))

theorem finrank_standardUnlinkTargetTangent (i : Fin 2) (x : Sphere 2) :
    Module.finrank ℝ
      ((ℝ ∙ ((standardUnlinkSphereMap i (-x) : Sphere 4) :
        EuclideanSpace ℝ (Fin 5)))ᗮ) = 4 := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) := ⟨by simp⟩
  exact Submodule.finrank_orthogonal_span_singleton
    (n := 4) (ne_zero_of_mem_unit_sphere (standardUnlinkSphereMap i (-x)))

theorem finrank_standardUnlinkTangentSum_eq (i : Fin 2) (x : Sphere 2) :
    Module.finrank ℝ
      (((ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 3))))ᗮ) × (ℝ × ℝ)) =
    Module.finrank ℝ
      ((ℝ ∙ ((standardUnlinkSphereMap i (-x) : Sphere 4) :
        EuclideanSpace ℝ (Fin 5)))ᗮ) := by
  rw [Module.finrank_prod, Module.finrank_prod, finrank_standardUnlinkSourceTangent,
    finrank_standardUnlinkTargetTangent]
  norm_num

/-- The tangent normal form as a continuous linear equivalence. -/
def standardUnlinkTangentSumEquiv (i : Fin 2) (x : Sphere 2) :
    (((ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 3))))ᗮ) × (ℝ × ℝ)) ≃L[ℝ]
      (ℝ ∙ ((standardUnlinkSphereMap i (-x) : Sphere 4) :
        EuclideanSpace ℝ (Fin 5)))ᗮ :=
  ((standardUnlinkTangentSumLinearMap i x).linearEquivOfInjective
    (standardUnlinkTangentSumLinearMap_injective i x)
    (finrank_standardUnlinkTangentSum_eq i x)).toContinuousLinearEquiv

@[simp]
theorem standardUnlinkTangentSumEquiv_apply (i : Fin 2) (x : Sphere 2)
    (p : ((ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 3))))ᗮ) × (ℝ × ℝ)) :
    standardUnlinkTangentSumEquiv i x p =
      standardUnlinkTangentSumLinearMap i x p := rfl

/-- Orthonormal coordinates used by the preferred source-sphere chart. -/
def standardUnlinkSourceTangentRepr (x : Sphere 2) :
    ((ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 3))))ᗮ) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin 2) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  exact (OrthonormalBasis.fromOrthogonalSpanSingleton
    (𝕜 := ℝ) 2 (ne_zero_of_mem_unit_sphere (-x))).repr

/-- Orthonormal coordinates used by stereographic projection from the corresponding point of the
small round component. -/
def standardUnlinkTargetTangentRepr (i : Fin 2) (x : Sphere 2) :
    ((ℝ ∙ ((standardUnlinkSphereMap i (-x) : Sphere 4) :
      EuclideanSpace ℝ (Fin 5)))ᗮ) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin 4) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) := ⟨by simp⟩
  exact (OrthonormalBasis.fromOrthogonalSpanSingleton
    (𝕜 := ℝ) 4 (ne_zero_of_mem_unit_sphere (standardUnlinkSphereMap i (-x)))).repr

/-- The continuous linear equivalence appearing in the component immersion normal form. -/
def standardUnlinkChartLinearEquiv (i : Fin 2) (x : Sphere 2) :
    (EuclideanSpace ℝ (Fin 2) × (ℝ × ℝ)) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  ((((standardUnlinkSourceTangentRepr x).symm.toContinuousLinearEquiv.prodCongr
      (ContinuousLinearEquiv.refl ℝ (ℝ × ℝ))).trans
    (standardUnlinkTangentSumEquiv i x)).trans
    (standardUnlinkTargetTangentRepr i x).toContinuousLinearEquiv)

@[simp]
theorem standardUnlinkChartLinearEquiv_apply (i : Fin 2) (x : Sphere 2)
    (p : EuclideanSpace ℝ (Fin 2) × (ℝ × ℝ)) :
    standardUnlinkChartLinearEquiv i x p =
      standardUnlinkTargetTangentRepr i x
        (standardUnlinkTangentSumLinearMap i x
          ((standardUnlinkSourceTangentRepr x).symm p.1, p.2)) := rfl

/-- A target chart centered at `standardUnlinkSphereMap i x`: stereographic projection from the
corresponding opposite source point, followed by translation of its value at the center to zero. -/
def standardUnlinkTargetChart (i : Fin 2) (x : Sphere 2) :
    OpenPartialHomeomorph (Sphere 4) (EuclideanSpace ℝ (Fin 4)) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (4 + 1))) = 4 + 1) := ⟨by simp⟩
  let raw := stereographic' 4 (standardUnlinkSphereMap i (-x))
  let c : EuclideanSpace ℝ (Fin 4) := raw (standardUnlinkSphereMap i x)
  exact raw ≫ₕ (Homeomorph.addRight (-c)).toOpenPartialHomeomorph

@[simp]
theorem standardUnlinkTargetChart_source (i : Fin 2) (x : Sphere 2) :
    (standardUnlinkTargetChart i x).source =
      ({standardUnlinkSphereMap i (-x)}ᶜ : Set (Sphere 4)) := by
  simp [standardUnlinkTargetChart]

@[simp]
theorem standardUnlinkTargetChart_target (i : Fin 2) (x : Sphere 2) :
    (standardUnlinkTargetChart i x).target = Set.univ := by
  simp [standardUnlinkTargetChart]

theorem standardUnlinkSphereMap_mem_targetChart_source (i : Fin 2) (x : Sphere 2) :
    standardUnlinkSphereMap i x ∈ (standardUnlinkTargetChart i x).source := by
  rw [standardUnlinkTargetChart_source]
  simp only [mem_compl_iff, mem_singleton_iff]
  intro h
  have hxneg : x = -x := standardUnlinkSphereMap_injective i h
  exact ne_neg_of_mem_unit_sphere ℝ x hxneg

section ComponentCharts

local instance standardUnlinkSourceFinrankFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1) := ⟨by simp⟩

local instance standardUnlinkTargetFinrankFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (4 + 1))) = 4 + 1) := ⟨by simp⟩

/-- In the translated component chart, the parametrization is exactly the zero-normal slice of
the continuous linear equivalence. -/
theorem standardUnlinkTargetChart_map_eq (i : Fin 2) (x z : Sphere 2) (hz : z ≠ -x) :
    standardUnlinkTargetChart i x (standardUnlinkSphereMap i z) =
      standardUnlinkChartLinearEquiv i x (stereographic' 2 (-x) z, (0, 0)) := by
  change
    standardUnlinkTargetTangentRepr i x
        (stereoToFun
          ((standardUnlinkSphereMap i (-x) : Sphere 4) : EuclideanSpace ℝ (Fin 5))
          ((standardUnlinkSphereMap i z : Sphere 4) : EuclideanSpace ℝ (Fin 5))) +
      -(standardUnlinkTargetTangentRepr i x
        (stereoToFun
          ((standardUnlinkSphereMap i (-x) : Sphere 4) : EuclideanSpace ℝ (Fin 5))
          ((standardUnlinkSphereMap i x : Sphere 4) : EuclideanSpace ℝ (Fin 5)))) =
    standardUnlinkTargetTangentRepr i x
      (standardUnlinkTangentSumLinearMap i x
        ((standardUnlinkSourceTangentRepr x).symm
          (standardUnlinkSourceTangentRepr x
            (stereoToFun (-(x : EuclideanSpace ℝ (Fin 3)))
              (z : EuclideanSpace ℝ (Fin 3)))), (0, 0)))
  rw [LinearIsometryEquiv.symm_apply_apply]
  rw [← map_neg, ← map_add]
  congr 1
  apply Subtype.ext
  change
    ((stereoToFun
      ((standardUnlinkSphereMap i (-x) : Sphere 4) : EuclideanSpace ℝ (Fin 5))
      ((standardUnlinkSphereMap i z : Sphere 4) : EuclideanSpace ℝ (Fin 5)) :
        (ℝ ∙ ((standardUnlinkSphereMap i (-x) : Sphere 4) :
          EuclideanSpace ℝ (Fin 5)))ᗮ) : EuclideanSpace ℝ (Fin 5)) -
      ((stereoToFun
        ((standardUnlinkSphereMap i (-x) : Sphere 4) : EuclideanSpace ℝ (Fin 5))
        ((standardUnlinkSphereMap i x : Sphere 4) : EuclideanSpace ℝ (Fin 5)) :
          (ℝ ∙ ((standardUnlinkSphereMap i (-x) : Sphere 4) :
            EuclideanSpace ℝ (Fin 5)))ᗮ) : EuclideanSpace ℝ (Fin 5)) =
    standardUnlinkRadius⁻¹ • standardUnlinkLinearIsometry
      ((stereoToFun (-(x : EuclideanSpace ℝ (Fin 3)))
        (z : EuclideanSpace ℝ (Fin 3)) :
          (ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 3))))ᗮ) :
            EuclideanSpace ℝ (Fin 3)) +
      (0 : ℝ) • standardUnlinkMeridianNormal i x +
      (0 : ℝ) • standardUnlinkNormalFour
  have hx : x ≠ -x := ne_neg_of_mem_unit_sphere ℝ x
  rw [coe_stereoToFun_standardUnlink i x z hz,
    coe_stereoToFun_standardUnlink i x x hx]
  have hsourceZero :
      ((stereoToFun (-(x : EuclideanSpace ℝ (Fin 3)))
        (x : EuclideanSpace ℝ (Fin 3)) :
          (ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 3))))ᗮ) :
            EuclideanSpace ℝ (Fin 3)) = 0 := by
    change ((stereographic (norm_eq_of_mem_sphere (-x)) x :
      (ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 3))))ᗮ) :
        EuclideanSpace ℝ (Fin 3)) = 0
    exact congrArg Subtype.val (stereographic_neg_apply x)
  rw [hsourceZero, map_zero]
  simp

end ComponentCharts

/-- The translated stereographic target chart belongs to the smooth maximal atlas. -/
theorem standardUnlinkTargetChart_mem_maximalAtlas (i : Fin 2) (x : Sphere 2) :
    standardUnlinkTargetChart i x ∈
      IsManifold.maximalAtlas (𝓡 4) ∞ (Sphere 4) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (4 + 1))) = 4 + 1) := ⟨by simp⟩
  let raw := stereographic' 4 (standardUnlinkSphereMap i (-x))
  let c : EuclideanSpace ℝ (Fin 4) := raw (standardUnlinkSphereMap i x)
  have hrawAtlas : raw ∈ atlas (EuclideanSpace ℝ (Fin 4)) (Sphere 4) :=
    ⟨standardUnlinkSphereMap i (-x), rfl⟩
  have hrawMax : raw ∈ IsManifold.maximalAtlas (𝓡 4) ∞ (Sphere 4) :=
    IsManifold.subset_maximalAtlas hrawAtlas
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · have hshift : ContMDiff (𝓡 4) (𝓡 4) ∞
        (fun u : EuclideanSpace ℝ (Fin 4) ↦ u + -c) :=
      (contDiff_id.add contDiff_const).contMDiff
    have hcomp := hshift.comp_contMDiffOn
      (contMDiffOn_of_mem_maximalAtlas hrawMax)
    simpa [standardUnlinkTargetChart, raw, c, Function.comp_def] using hcomp
  · have hshift : ContMDiff (𝓡 4) (𝓡 4) ∞
        (fun u : EuclideanSpace ℝ (Fin 4) ↦ u + c) :=
      (contDiff_id.add contDiff_const).contMDiff
    have hshiftOn : ContMDiffOn (𝓡 4) (𝓡 4) ∞
        (fun u : EuclideanSpace ℝ (Fin 4) ↦ u + c) Set.univ :=
      hshift.contMDiffOn
    have hcomp := (contMDiffOn_symm_of_mem_maximalAtlas hrawMax).comp
      hshiftOn (by simp [raw])
    simpa [standardUnlinkTargetChart, raw, c, Function.comp_def,
      Homeomorph.addRight] using hcomp

/-- Each frozen component has a global two-dimensional smooth normal complement. -/
theorem isImmersionOfComplement_standardUnlinkSphereMap (i : Fin 2) :
    Manifold.IsImmersionOfComplement (ℝ × ℝ) (𝓡 2) (𝓡 4) ∞
      (standardUnlinkSphereMap i) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1) := ⟨by simp⟩
  intro x
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (contMDiff_standardUnlinkSphereMap i).continuous.continuousAt
    (standardUnlinkChartLinearEquiv i x)
    (chartAt (EuclideanSpace ℝ (Fin 2)) x)
    (standardUnlinkTargetChart i x)
    (mem_chart_source _ x)
    (standardUnlinkSphereMap_mem_targetChart_source i x)
    (IsManifold.chart_mem_maximalAtlas x)
    (standardUnlinkTargetChart_mem_maximalAtlas i x)
  intro u hu
  rw [OpenPartialHomeomorph.extend_target] at hu
  have huTarget :
      u ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).target := by
    simpa only [modelWithCornersSelf_coe_symm, preimage_id_eq, id_eq] using hu.1
  have hzSource :
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm u ∈
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).source :=
    (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm.map_source huTarget
  have hz : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm u ≠ -x := by
    have hsource : (chartAt (EuclideanSpace ℝ (Fin 2)) x).source =
        ({-x}ᶜ : Set (Sphere 2)) := by
      change (stereographic' 2 (-x)).source = ({-x}ᶜ : Set (Sphere 2))
      exact stereographic'_source (-x)
    rw [hsource] at hzSource
    simpa only [mem_compl_iff, mem_singleton_iff] using hzSource
  simp only [Function.comp_apply, mfld_simps]
  calc
    _ = standardUnlinkChartLinearEquiv i x
        ((chartAt (EuclideanSpace ℝ (Fin 2)) x
          ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm u)),
            (0 : ℝ × ℝ)) := by
      exact standardUnlinkTargetChart_map_eq i x
        ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm u) hz
    _ = _ := by
      rw [(chartAt (EuclideanSpace ℝ (Fin 2)) x).right_inv huTarget]

/-- Each explicit component parametrization is a smooth immersion. -/
theorem isImmersion_standardUnlinkSphereMap (i : Fin 2) :
    Manifold.IsImmersion (𝓡 2) (𝓡 4) ∞ (standardUnlinkSphereMap i) :=
  (isImmersionOfComplement_standardUnlinkSphereMap i).isImmersion

/-- Delete the two frozen coordinates and rescale by the component radius. -/
def standardUnlinkSourceProjection (y : EuclideanSpace ℝ (Fin 5)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![y 0 / standardUnlinkRadius, y 1 / standardUnlinkRadius,
    y 2 / standardUnlinkRadius]

theorem norm_standardUnlinkSourceProjection_of_component (i : Fin 2) (y : Sphere 4)
    (hy : y ∈ standardUnlinkComponent i) :
    ‖standardUnlinkSourceProjection y.1‖ = 1 := by
  have hynorm : ‖(y : EuclideanSpace ℝ (Fin 5))‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using y.2
  have hycoords : y.1 3 = standardUnlinkHeight i ∧ y.1 4 = 0 := by
    simpa [standardUnlinkComponent, standardUnlinkHeight] using hy
  have hfirst : y.1 0 ^ 2 + (y.1 1 ^ 2 + y.1 2 ^ 2) = 3 / 4 := by
    have hall : y.1 0 ^ 2 + (y.1 1 ^ 2 + (y.1 2 ^ 2 +
        (y.1 3 ^ 2 + y.1 4 ^ 2))) = 1 := by
      simpa [hynorm, Fin.sum_univ_succ] using
        (EuclideanSpace.real_norm_sq_eq (y : EuclideanSpace ℝ (Fin 5))).symm
    rw [hycoords.1, hycoords.2, standardUnlinkHeight_sq] at hall
    nlinarith
  have hsq : ‖standardUnlinkSourceProjection y.1‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change (y.1 0 / standardUnlinkRadius) ^ 2 +
      ((y.1 1 / standardUnlinkRadius) ^ 2 +
        (y.1 2 / standardUnlinkRadius) ^ 2) = 1
    rw [div_pow, div_pow, div_pow, standardUnlinkRadius_sq]
    field_simp
    nlinarith
  nlinarith [norm_nonneg (standardUnlinkSourceProjection y.1)]

/-- The explicit parametrization has exactly the frozen component as its image. -/
theorem range_standardUnlinkSphereMap (i : Fin 2) :
    range (standardUnlinkSphereMap i) = standardUnlinkComponent i := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp [standardUnlinkComponent, standardUnlinkHeight]
  · intro hy
    let x : Sphere 2 := ⟨standardUnlinkSourceProjection y.1, by
      simpa [mem_sphere_zero_iff_norm] using
        norm_standardUnlinkSourceProjection_of_component i y hy⟩
    refine ⟨x, Subtype.ext ?_⟩
    have hycoords : y.1 3 = standardUnlinkHeight i ∧ y.1 4 = 0 := by
      simpa [standardUnlinkComponent, standardUnlinkHeight] using hy
    ext j
    fin_cases j
    · exact mul_div_cancel₀ _ standardUnlinkRadius_ne_zero
    · exact mul_div_cancel₀ _ standardUnlinkRadius_ne_zero
    · exact mul_div_cancel₀ _ standardUnlinkRadius_ne_zero
    · exact hycoords.1.symm
    · exact hycoords.2.symm

theorem disjoint_range_standardUnlinkSphereMap :
    Disjoint (range (standardUnlinkSphereMap 0))
      (range (standardUnlinkSphereMap 1)) := by
  rw [range_standardUnlinkSphereMap, range_standardUnlinkSphereMap, Set.disjoint_left]
  intro y hy0 hy1
  change y.1 3 = -(1 / 2 : ℝ) ∧ y.1 4 = 0 at hy0
  change y.1 3 = (1 / 2 : ℝ) ∧ y.1 4 = 0 at hy1
  linarith [hy0.1, hy1.1]

theorem union_range_standardUnlinkSphereMap :
    range (standardUnlinkSphereMap 0) ∪ range (standardUnlinkSphereMap 1) =
      standardUnlinkCarrier := by
  rw [range_standardUnlinkSphereMap, range_standardUnlinkSphereMap]
  rfl

/-- Component `i` of the frozen standard unlink, bundled as a smooth embedding of `S²` in `S⁴`. -/
def standardUnlinkEmbedding (i : Fin 2) : SmoothSphereEmbedding 2 4 :=
  TauCeti.SmoothEmbedding.ofIsSmoothEmbedding (standardUnlinkSphereMap i)
    ⟨isImmersion_standardUnlinkSphereMap i, isEmbedding_standardUnlinkSphereMap i⟩

@[simp]
theorem standardUnlinkEmbedding_apply (i : Fin 2) (x : Sphere 2) :
    standardUnlinkEmbedding i x = standardUnlinkSphereMap i x := by
  simp [standardUnlinkEmbedding]

/-- The bundled component embedding has exactly the prescribed frozen-coordinate image. -/
theorem range_standardUnlinkEmbedding (i : Fin 2) :
    range (standardUnlinkEmbedding i) = standardUnlinkComponent i := by
  have hfun : (standardUnlinkEmbedding i : Sphere 2 → Sphere 4) =
      standardUnlinkSphereMap i := by
    funext x
    exact standardUnlinkEmbedding_apply i x
  rw [hfun]
  exact range_standardUnlinkSphereMap i

/-- The two bundled component embeddings have disjoint images. -/
theorem disjoint_range_standardUnlinkEmbedding :
    Disjoint (range (standardUnlinkEmbedding 0))
      (range (standardUnlinkEmbedding 1)) := by
  rw [range_standardUnlinkEmbedding, range_standardUnlinkEmbedding]
  have h := disjoint_range_standardUnlinkSphereMap
  rw [range_standardUnlinkSphereMap, range_standardUnlinkSphereMap] at h
  exact h

/-- The two bundled component images exhaust the frozen standard unlink carrier. -/
theorem union_range_standardUnlinkEmbedding :
    range (standardUnlinkEmbedding 0) ∪ range (standardUnlinkEmbedding 1) =
      standardUnlinkCarrier := by
  rw [range_standardUnlinkEmbedding, range_standardUnlinkEmbedding]
  rfl

end SplittingSpheres
