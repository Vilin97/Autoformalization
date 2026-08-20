/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.SphereHandleSmoothness

/-!
# Interior product coordinates on the one-handle region of the four-sphere

The direct one-handle parameterization restricts away from its attaching boundary to smooth
product coordinates

`S¹ × {b : ℝ³ | ‖b‖ < 1} ≃ {q : S⁴ | ‖q.second‖ < 1 / √2}`.

Both sides are literal open submanifolds.  The inverse normalizes the nonzero first coordinate
block and rescales the second block.  Thus this file does not use or assert any induced smooth
structure on the boundary of the compact handle piece.
-/

@[expose] public section

noncomputable section

open Function Metric Set
open TopologicalSpace
open scoped ContDiff Manifold Topology

namespace SplittingSpheres

/-- The model coordinate range for `S¹` times the open three-ball. -/
abbrev SphereHandleInteriorModelSpace :=
  ModelProd (EuclideanSpace ℝ (Fin 1)) SphereHandleSecond

/-- The ordinary product model used on `S¹` times the open three-ball. -/
abbrev sphereHandleInteriorProductModel :
    ModelWithCorners ℝ
      (EuclideanSpace ℝ (Fin 1) × SphereHandleSecond)
      SphereHandleInteriorModelSpace :=
  (𝓡 1).prod (modelWithCornersSelf ℝ SphereHandleSecond)

/-- The open unit ball in the three-dimensional factor of the one-handle. -/
def sphereHandleOpenUnitBall : Opens SphereHandleSecond :=
  ⟨ball 0 1, isOpen_ball⟩

/-- The open unit three-ball, regarded as its manifold subtype. -/
abbrev SphereHandleOpenUnitBall := sphereHandleOpenUnitBall

/-- Projection to the second block in the coordinate splitting of the ambient five-space. -/
def sphereHandleSecondProjection (q : Sphere 4) : SphereHandleSecond :=
  (sphereHandleSplitEquiv q.1).2

/-- Projection to the first block in the coordinate splitting of the ambient five-space. -/
def sphereHandleFirstProjection (q : Sphere 4) : SphereHandleFirst :=
  (sphereHandleSplitEquiv q.1).1

theorem continuous_sphereHandleSecondProjection :
    Continuous sphereHandleSecondProjection :=
  continuous_snd.comp (sphereHandleSplitEquiv.continuous.comp continuous_subtype_val)

theorem continuous_sphereHandleFirstProjection :
    Continuous sphereHandleFirstProjection :=
  continuous_fst.comp (sphereHandleSplitEquiv.continuous.comp continuous_subtype_val)

/-- The open part of `S⁴` occupied by the interior of the direct one-handle face. -/
def sphereHandleOneRegion : Opens (Sphere 4) :=
  ⟨{x | ‖sphereHandleSecondProjection x‖ < sphereHandleRadius},
    isOpen_lt (continuous_norm.comp continuous_sphereHandleSecondProjection) continuous_const⟩

/-- The open one-handle region, regarded as its manifold subtype. -/
abbrev SphereHandleOneRegion := sphereHandleOneRegion

@[simp]
theorem mem_sphereHandleOneRegion {q : Sphere 4} :
    q ∈ sphereHandleOneRegion ↔ ‖sphereHandleSecondProjection q‖ < sphereHandleRadius :=
  Iff.rfl

/-- Regard a point of the open unit ball as a point of the closed unit ball. -/
def sphereHandleOpenBallToClosedBall
    (b : SphereHandleOpenUnitBall) : EuclideanClosedBall 3 :=
  ⟨b.1, mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp b.2).le⟩

@[simp]
theorem sphereHandleOpenBallToClosedBall_coe (b : SphereHandleOpenUnitBall) :
    (sphereHandleOpenBallToClosedBall b : SphereHandleSecond) = b.1 :=
  rfl

/-- The direct one-handle map, restricted to the open ball and corestricted to its open image. -/
def sphereHandleInteriorForward
    (p : Sphere 1 × SphereHandleOpenUnitBall) : SphereHandleOneRegion := by
  let x : OneHandlePiece := (p.1, sphereHandleOpenBallToClosedBall p.2)
  refine ⟨oneHandleSphereMap x, ?_⟩
  rw [mem_sphereHandleOneRegion, sphereHandleSecondProjection,
    sphereHandleSplitEquiv_oneHandleSphereMap, norm_smul, Real.norm_eq_abs,
    abs_of_pos sphereHandleRadius_pos]
  change sphereHandleRadius * ‖p.2.1‖ < sphereHandleRadius
  simpa only [mul_one] using
    mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp p.2.2) sphereHandleRadius_pos

@[simp]
theorem sphereHandleInteriorForward_coe
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    (sphereHandleInteriorForward p : Sphere 4) =
      oneHandleSphereMap (p.1, sphereHandleOpenBallToClosedBall p.2) :=
  rfl

@[simp]
theorem sphereHandleSplitEquiv_interiorForward
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    sphereHandleSplitEquiv (sphereHandleInteriorForward p).1.1 =
      (sphereHandleScale ‖p.2.1‖ • p.1.1, sphereHandleRadius • p.2.1) := by
  exact sphereHandleSplitEquiv_oneHandleSphereMap
    (p.1, sphereHandleOpenBallToClosedBall p.2)

/-- The first coordinate block never vanishes on the open one-handle region. -/
theorem sphereHandleOneRegion_first_norm_pos (q : SphereHandleOneRegion) :
    0 < ‖(sphereHandleSplitEquiv q.1.1).1‖ := by
  let u : SphereHandleFirst := (sphereHandleSplitEquiv q.1.1).1
  let v : SphereHandleSecond := (sphereHandleSplitEquiv q.1.1).2
  have hsum : ‖u‖ ^ 2 + ‖v‖ ^ 2 = 1 :=
    sphereHandleSplitEquiv_sphere_norm_sq q.1
  have hvlt : ‖v‖ < sphereHandleRadius := q.2
  have hvsq : ‖v‖ ^ 2 < sphereHandleRadius ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) sphereHandleRadius_pos.le).2 hvlt
  have hu_sq_pos : 0 < ‖u‖ ^ 2 := by
    rw [sphereHandleRadius_sq] at hvsq
    nlinarith
  exact lt_of_le_of_ne (norm_nonneg _) (sq_pos_iff.mp hu_sq_pos).symm

/-- Recover the circle coordinate by normalizing the first coordinate block. -/
def sphereHandleInteriorCircleCoordinate (q : SphereHandleOneRegion) : Sphere 1 := by
  let u : SphereHandleFirst := (sphereHandleSplitEquiv q.1.1).1
  have hu_pos : 0 < ‖u‖ := sphereHandleOneRegion_first_norm_pos q
  have hnorm : ‖‖u‖⁻¹ • u‖ = 1 := by
    simp only [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu_pos.ne']
  exact ⟨‖u‖⁻¹ • u, mem_sphere_zero_iff_norm.mpr hnorm⟩

/-- Recover the open-ball coordinate by rescaling the second coordinate block. -/
def sphereHandleInteriorBallCoordinate
    (q : SphereHandleOneRegion) : SphereHandleOpenUnitBall := by
  let v : SphereHandleSecond := (sphereHandleSplitEquiv q.1.1).2
  have hmem : ‖sphereHandleRadius⁻¹ • v‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr sphereHandleRadius_pos)]
    exact (inv_mul_lt_one₀ sphereHandleRadius_pos).2 q.2
  exact ⟨sphereHandleRadius⁻¹ • v, mem_ball_zero_iff.mpr hmem⟩

/-- Explicit inverse coordinates on the open one-handle region. -/
def sphereHandleInteriorInverse
    (q : SphereHandleOneRegion) : Sphere 1 × SphereHandleOpenUnitBall :=
  (sphereHandleInteriorCircleCoordinate q, sphereHandleInteriorBallCoordinate q)

@[simp]
theorem sphereHandleInteriorCircleCoordinate_coe (q : SphereHandleOneRegion) :
    (sphereHandleInteriorCircleCoordinate q : SphereHandleFirst) =
      ‖(sphereHandleSplitEquiv q.1.1).1‖⁻¹ •
        (sphereHandleSplitEquiv q.1.1).1 :=
  rfl

@[simp]
theorem sphereHandleInteriorBallCoordinate_coe (q : SphereHandleOneRegion) :
    (sphereHandleInteriorBallCoordinate q : SphereHandleSecond) =
      sphereHandleRadius⁻¹ • (sphereHandleSplitEquiv q.1.1).2 :=
  rfl

@[simp]
theorem sphereHandleInteriorInverse_fst (q : SphereHandleOneRegion) :
    (sphereHandleInteriorInverse q).1 = sphereHandleInteriorCircleCoordinate q :=
  rfl

@[simp]
theorem sphereHandleInteriorInverse_snd (q : SphereHandleOneRegion) :
    (sphereHandleInteriorInverse q).2 = sphereHandleInteriorBallCoordinate q :=
  rfl

/-- The recovered circle coordinate of a directly parameterized point is the original one. -/
@[simp]
theorem sphereHandleInteriorCircleCoordinate_forward
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    sphereHandleInteriorCircleCoordinate (sphereHandleInteriorForward p) = p.1 := by
  apply Subtype.ext
  rw [sphereHandleInteriorCircleCoordinate_coe,
    sphereHandleSplitEquiv_interiorForward]
  have hb0 : 0 ≤ ‖p.2.1‖ := norm_nonneg _
  have hb1 : ‖p.2.1‖ ≤ 1 := (mem_ball_zero_iff.mp p.2.2).le
  have hspos : 0 < sphereHandleScale ‖p.2.1‖ :=
    sphereHandleScale_pos hb0 hb1
  have hz : ‖p.1.1‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos, hz, mul_one,
    smul_smul, inv_mul_cancel₀ hspos.ne', one_smul]

/-- The recovered ball coordinate of a directly parameterized point is the original one. -/
@[simp]
theorem sphereHandleInteriorBallCoordinate_forward
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    sphereHandleInteriorBallCoordinate (sphereHandleInteriorForward p) = p.2 := by
  apply Subtype.ext
  rw [sphereHandleInteriorBallCoordinate_coe,
    sphereHandleSplitEquiv_interiorForward, smul_smul,
    inv_mul_cancel₀ sphereHandleRadius_ne_zero, one_smul]

theorem sphereHandleInteriorInverse_forward
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    sphereHandleInteriorInverse (sphereHandleInteriorForward p) = p := by
  exact Prod.ext (sphereHandleInteriorCircleCoordinate_forward p)
    (sphereHandleInteriorBallCoordinate_forward p)

/-- The complementary scale of the recovered ball coordinate is the norm of the first block. -/
theorem sphereHandleScale_ballCoordinate (q : SphereHandleOneRegion) :
    sphereHandleScale ‖(sphereHandleInteriorBallCoordinate q : SphereHandleSecond)‖ =
      ‖(sphereHandleSplitEquiv q.1.1).1‖ := by
  let u : SphereHandleFirst := (sphereHandleSplitEquiv q.1.1).1
  let v : SphereHandleSecond := (sphereHandleSplitEquiv q.1.1).2
  have hsum : ‖u‖ ^ 2 + ‖v‖ ^ 2 = 1 :=
    sphereHandleSplitEquiv_sphere_norm_sq q.1
  have hbmem : ‖sphereHandleRadius⁻¹ • v‖ ≤ 1 :=
    (mem_ball_zero_iff.mp (sphereHandleInteriorBallCoordinate q).2).le
  have hbnorm : ‖sphereHandleRadius⁻¹ • v‖ = sphereHandleRadius⁻¹ * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr sphereHandleRadius_pos)]
  change sphereHandleScale ‖sphereHandleRadius⁻¹ • v‖ = ‖u‖
  apply (sq_eq_sq₀ (sphereHandleScale_nonneg _) (norm_nonneg _)).mp
  rw [sphereHandleScale_sq (norm_nonneg _) hbmem, hbnorm]
  have hcancel :
      sphereHandleRadius ^ 2 * (sphereHandleRadius⁻¹ * ‖v‖) ^ 2 = ‖v‖ ^ 2 := by
    field_simp [sphereHandleRadius_ne_zero]
  rw [hcancel]
  nlinarith

theorem sphereHandleInteriorForward_inverse (q : SphereHandleOneRegion) :
    sphereHandleInteriorForward (sphereHandleInteriorInverse q) = q := by
  apply Subtype.ext
  apply Subtype.ext
  apply sphereHandleSplitEquiv.injective
  rw [sphereHandleSplitEquiv_interiorForward]
  change
    (sphereHandleScale ‖(sphereHandleInteriorBallCoordinate q : SphereHandleSecond)‖ •
        (‖(sphereHandleSplitEquiv q.1.1).1‖⁻¹ •
          (sphereHandleSplitEquiv q.1.1).1),
      sphereHandleRadius •
        (sphereHandleRadius⁻¹ • (sphereHandleSplitEquiv q.1.1).2)) =
      sphereHandleSplitEquiv q.1.1
  rw [sphereHandleScale_ballCoordinate, smul_smul,
    mul_inv_cancel₀ (sphereHandleOneRegion_first_norm_pos q).ne', one_smul,
    smul_smul, mul_inv_cancel₀ sphereHandleRadius_ne_zero, one_smul]

/-- The exact equivalence underlying the open one-handle product coordinates. -/
def sphereHandleInteriorEquiv :
    (Sphere 1 × SphereHandleOpenUnitBall) ≃ SphereHandleOneRegion where
  toFun := sphereHandleInteriorForward
  invFun := sphereHandleInteriorInverse
  left_inv := sphereHandleInteriorInverse_forward
  right_inv := sphereHandleInteriorForward_inverse

@[simp]
theorem sphereHandleInteriorEquiv_apply
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    sphereHandleInteriorEquiv p = sphereHandleInteriorForward p :=
  rfl

@[simp]
theorem sphereHandleInteriorEquiv_symm_apply (q : SphereHandleOneRegion) :
    sphereHandleInteriorEquiv.symm q = sphereHandleInteriorInverse q :=
  rfl

/-- As a subset of the literal four-sphere, the image is exactly the strict second-block
region used in the target subtype. -/
theorem range_sphereHandleInteriorForward_coe :
    range (fun p : Sphere 1 × SphereHandleOpenUnitBall ↦
      ((sphereHandleInteriorForward p : SphereHandleOneRegion) : Sphere 4)) =
      (sphereHandleOneRegion : Set (Sphere 4)) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact (sphereHandleInteriorForward p).2
  · intro hq
    let q' : SphereHandleOneRegion := ⟨q, hq⟩
    refine ⟨sphereHandleInteriorInverse q', ?_⟩
    exact congr_arg Subtype.val (sphereHandleInteriorForward_inverse q')

/-- The complementary square-root scale is smooth on the open unit three-ball. -/
theorem contMDiff_sphereHandleScale_openBall :
    ContMDiff (modelWithCornersSelf ℝ SphereHandleSecond)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun b : SphereHandleOpenUnitBall ↦ sphereHandleScale ‖b.1‖) := by
  intro b
  have hradicand : ContDiffAt ℝ ∞
      (fun v : SphereHandleSecond ↦
        1 - sphereHandleRadius ^ 2 * ‖v‖ ^ 2) b.1 :=
    contDiffAt_const.sub (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt)
  have hne : 1 - sphereHandleRadius ^ 2 * ‖b.1‖ ^ 2 ≠ 0 := by
    have hb : ‖(b : SphereHandleSecond)‖ < 1 := mem_ball_zero_iff.mp b.2
    have hbsq : ‖(b : SphereHandleSecond)‖ ^ 2 < 1 :=
      by simpa using (sq_lt_sq₀ (norm_nonneg _) zero_le_one).2 hb
    rw [sphereHandleRadius_sq]
    nlinarith
  have hsqrt : ContDiffAt ℝ ∞
      (fun v : SphereHandleSecond ↦
        Real.sqrt (1 - sphereHandleRadius ^ 2 * ‖v‖ ^ 2)) b.1 :=
    hradicand.sqrt hne
  have hcomp := hsqrt.contMDiffAt.comp b contMDiff_subtype_val.contMDiffAt
  exact hcomp.congr_of_eventuallyEq <| Filter.Eventually.of_forall fun _ ↦ rfl

/-- The ambient formula underlying the restricted one-handle parameterization is smooth. -/
theorem contMDiff_sphereHandleInteriorForwardAmbient :
    ContMDiff sphereHandleInteriorProductModel
      (modelWithCornersSelf ℝ SphereHandleAmbient) ∞
      (fun p : Sphere 1 × SphereHandleOpenUnitBall ↦
        (sphereHandleInteriorForward p : Sphere 4).1) := by
  let : Fact (Module.finrank ℝ SphereHandleFirst = 1 + 1) := ⟨by simp⟩
  have hz : ContMDiff sphereHandleInteriorProductModel
      (modelWithCornersSelf ℝ SphereHandleFirst) ∞
      (fun p : Sphere 1 × SphereHandleOpenUnitBall ↦ p.1.1) :=
    contMDiff_coe_sphere.comp contMDiff_fst
  have hb : ContMDiff sphereHandleInteriorProductModel
      (modelWithCornersSelf ℝ SphereHandleSecond) ∞
      (fun p : Sphere 1 × SphereHandleOpenUnitBall ↦ p.2.1) :=
    contMDiff_subtype_val.comp contMDiff_snd
  have hs : ContMDiff sphereHandleInteriorProductModel
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 1 × SphereHandleOpenUnitBall ↦ sphereHandleScale ‖p.2.1‖) :=
    contMDiff_sphereHandleScale_openBall.comp contMDiff_snd
  have hfirst : ContMDiff sphereHandleInteriorProductModel
      (modelWithCornersSelf ℝ SphereHandleFirst) ∞
      (fun p : Sphere 1 × SphereHandleOpenUnitBall ↦
        sphereHandleScale ‖p.2.1‖ • p.1.1) :=
    hs.smul hz
  have hsecond : ContMDiff sphereHandleInteriorProductModel
      (modelWithCornersSelf ℝ SphereHandleSecond) ∞
      (fun p : Sphere 1 × SphereHandleOpenUnitBall ↦ sphereHandleRadius • p.2.1) :=
    (show ContMDiff sphereHandleInteriorProductModel (modelWithCornersSelf ℝ ℝ) ∞
        (fun _ : Sphere 1 × SphereHandleOpenUnitBall ↦ sphereHandleRadius) from
      contMDiff_const).smul hb
  have hpair : ContMDiff sphereHandleInteriorProductModel
      (modelWithCornersSelf ℝ (SphereHandleFirst × SphereHandleSecond)) ∞
      (fun p : Sphere 1 × SphereHandleOpenUnitBall ↦
        (sphereHandleScale ‖p.2.1‖ • p.1.1, sphereHandleRadius • p.2.1)) :=
    (contMDiff_prod_module_iff _).2 ⟨hfirst, hsecond⟩
  have hraw := sphereHandleSplitEquiv.symm.contDiff.comp_contMDiff hpair
  apply hraw.congr
  intro p
  change (sphereHandleInteriorForward p : Sphere 4).1 =
    sphereHandleSplitEquiv.symm
      (sphereHandleScale ‖p.2.1‖ • p.1.1, sphereHandleRadius • p.2.1)
  apply sphereHandleSplitEquiv.injective
  rw [sphereHandleSplitEquiv_interiorForward]
  exact (sphereHandleSplitEquiv.apply_symm_apply _).symm

/-- The restricted direct one-handle parameterization is smooth between the two open
submanifolds. -/
theorem contMDiff_sphereHandleInteriorForward :
    ContMDiff sphereHandleInteriorProductModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      sphereHandleInteriorForward := by
  let : Fact (Module.finrank ℝ SphereHandleAmbient = 4 + 1) := ⟨by simp⟩
  have hsphere : ContMDiff sphereHandleInteriorProductModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun p : Sphere 1 × SphereHandleOpenUnitBall ↦
        ((sphereHandleInteriorForward p : SphereHandleOneRegion) : Sphere 4)) :=
    (contMDiff_sphereHandleInteriorForwardAmbient.codRestrict_sphere
      (fun p ↦ (sphereHandleInteriorForward p).1.2)).congr fun _ ↦ rfl
  apply (ContMDiff.subtypeVal_comp_iff sphereHandleOneRegion
    sphereHandleInteriorForward).mp
  exact hsphere

/-- The first coordinate projection of the spherical splitting is smooth. -/
theorem contMDiff_sphereHandleFirstProjection :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ SphereHandleFirst) ∞ sphereHandleFirstProjection := by
  let : Fact (Module.finrank ℝ SphereHandleAmbient = 4 + 1) := ⟨by simp⟩
  have hsplit : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (SphereHandleFirst × SphereHandleSecond)) ∞
      (fun q : Sphere 4 ↦ sphereHandleSplitEquiv q.1) :=
    sphereHandleSplitEquiv.contDiff.comp_contMDiff contMDiff_coe_sphere
  exact ((contMDiff_prod_module_iff _).mp hsplit).1

/-- The second coordinate projection of the spherical splitting is smooth. -/
theorem contMDiff_sphereHandleSecondProjection :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ SphereHandleSecond) ∞ sphereHandleSecondProjection := by
  let : Fact (Module.finrank ℝ SphereHandleAmbient = 4 + 1) := ⟨by simp⟩
  have hsplit : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (SphereHandleFirst × SphereHandleSecond)) ∞
      (fun q : Sphere 4 ↦ sphereHandleSplitEquiv q.1) :=
    sphereHandleSplitEquiv.contDiff.comp_contMDiff contMDiff_coe_sphere
  exact ((contMDiff_prod_module_iff _).mp hsplit).2

/-- The first coordinate block, restricted to the open one-handle region, is smooth. -/
theorem contMDiff_sphereHandleFirstOnOneRegion :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ SphereHandleFirst) ∞
      (fun q : SphereHandleOneRegion ↦ sphereHandleFirstProjection q.1) :=
  contMDiff_sphereHandleFirstProjection.comp contMDiff_subtype_val

/-- The second coordinate block, restricted to the open one-handle region, is smooth. -/
theorem contMDiff_sphereHandleSecondOnOneRegion :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ SphereHandleSecond) ∞
      (fun q : SphereHandleOneRegion ↦ sphereHandleSecondProjection q.1) :=
  contMDiff_sphereHandleSecondProjection.comp contMDiff_subtype_val

/-- The norm of the nonzero first block is smooth on the open one-handle region. -/
theorem contMDiff_sphereHandleFirstNormOnOneRegion :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun q : SphereHandleOneRegion ↦ ‖sphereHandleFirstProjection q.1‖) := by
  intro q
  have hfirst : ContMDiffAt
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ SphereHandleFirst) ∞
      (fun y : SphereHandleOneRegion ↦ sphereHandleFirstProjection y.1) q :=
    contMDiff_sphereHandleFirstOnOneRegion.contMDiffAt
  have hu_ne : sphereHandleFirstProjection q.1 ≠ 0 := by
    apply norm_pos_iff.mp
    simpa [sphereHandleFirstProjection] using sphereHandleOneRegion_first_norm_pos q
  have hnorm := (contDiffAt_norm ℝ hu_ne).contMDiffAt.comp q hfirst
  exact hnorm.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- Normalization of the first block is smooth on the open one-handle region. -/
theorem contMDiff_sphereHandleInteriorCircleRaw :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ SphereHandleFirst) ∞
      (fun q : SphereHandleOneRegion ↦
        ‖sphereHandleFirstProjection q.1‖⁻¹ • sphereHandleFirstProjection q.1) :=
  (contMDiff_sphereHandleFirstNormOnOneRegion.inv₀
    (fun q ↦ (sphereHandleOneRegion_first_norm_pos q).ne')).smul
      contMDiff_sphereHandleFirstOnOneRegion

/-- The recovered circle coordinate is smooth. -/
theorem contMDiff_sphereHandleInteriorCircleCoordinate :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ∞
      sphereHandleInteriorCircleCoordinate := by
  let : Fact (Module.finrank ℝ SphereHandleFirst = 1 + 1) := ⟨by simp⟩
  have hcod := contMDiff_sphereHandleInteriorCircleRaw.codRestrict_sphere (n := 1)
    (fun q ↦ (sphereHandleInteriorCircleCoordinate q).2)
  exact hcod.congr fun _ ↦ rfl

/-- The recovered open-ball coordinate is smooth. -/
theorem contMDiff_sphereHandleInteriorBallCoordinate :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ SphereHandleSecond) ∞
      sphereHandleInteriorBallCoordinate := by
  apply (ContMDiff.subtypeVal_comp_iff sphereHandleOpenUnitBall
    sphereHandleInteriorBallCoordinate).mp
  exact ((show ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun _ : SphereHandleOneRegion ↦ sphereHandleRadius⁻¹) from
    contMDiff_const).smul contMDiff_sphereHandleSecondOnOneRegion).congr fun _ ↦ rfl

/-- The explicit inverse product coordinates are smooth. -/
theorem contMDiff_sphereHandleInteriorInverse :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      sphereHandleInteriorProductModel ∞ sphereHandleInteriorInverse :=
  (contMDiff_sphereHandleInteriorCircleCoordinate.prodMk
    contMDiff_sphereHandleInteriorBallCoordinate).congr fun _ ↦ rfl

/-- The interior of the direct one-handle face is genuinely diffeomorphic to a circle times an
open unit three-ball. -/
def sphereHandleInteriorDiffeomorph :
    (Sphere 1 × SphereHandleOpenUnitBall) ≃ₘ^∞⟮
      sphereHandleInteriorProductModel,
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))⟯ SphereHandleOneRegion where
  toEquiv := sphereHandleInteriorEquiv
  contMDiff_toFun := contMDiff_sphereHandleInteriorForward
  contMDiff_invFun := contMDiff_sphereHandleInteriorInverse

@[simp]
theorem sphereHandleInteriorDiffeomorph_apply
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    sphereHandleInteriorDiffeomorph p = sphereHandleInteriorForward p :=
  rfl

@[simp]
theorem sphereHandleInteriorDiffeomorph_apply_coe
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    ((sphereHandleInteriorDiffeomorph p : SphereHandleOneRegion) : Sphere 4) =
      oneHandleSphereMap (p.1, sphereHandleOpenBallToClosedBall p.2) :=
  rfl

@[simp]
theorem sphereHandleInteriorDiffeomorph_symm_apply (q : SphereHandleOneRegion) :
    sphereHandleInteriorDiffeomorph.symm q = sphereHandleInteriorInverse q :=
  rfl

end SplittingSpheres
