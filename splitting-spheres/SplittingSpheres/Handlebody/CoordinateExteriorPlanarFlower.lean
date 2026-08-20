/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPowerTrivializedPushout

/-!
# A planar flower model for the punctured-cap power pullback

The power coordinate alone determines a point of the planar punctured-cap pullback.  Its image
is the explicit subset of the nonzero complex plane cut out by

* `‖z ^ m + 1 / 2‖ ≤ sphereHandleRadius`,
* `1 / 8 ≤ ‖z ^ m‖`, and
* `1 / 8 ≤ ‖z ^ m + 1‖`.

This file constructs the resulting point-set homeomorphism, including degree `m = 0` (when both
sides are empty).  It makes no compact-surface classification, disk-lobe, ribbon-thickening, or
smoothness claim.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-- The explicit planar image of the degree-`m` punctured-normal-disk pullback. -/
def coordinateUnlinkExteriorPlanarFlowerSet (m : ℕ) : Set {z : ℂ // z ≠ 0} :=
  {z |
    ‖z.1 ^ m + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius ∧
      (1 / 8 : ℝ) ≤ ‖z.1 ^ m‖ ∧
        (1 / 8 : ℝ) ≤ ‖z.1 ^ m + 1‖}

/-- The planar flower as a topological subtype of the punctured complex plane. -/
abbrev CoordinateUnlinkExteriorPlanarFlower (m : ℕ) : Type :=
  ↑(coordinateUnlinkExteriorPlanarFlowerSet m)

/-- At raw degree zero the displayed inequalities are inconsistent. -/
theorem coordinateUnlinkExteriorPlanarFlower_zero_isEmpty :
    IsEmpty (CoordinateUnlinkExteriorPlanarFlower 0) := by
  constructor
  intro z
  have h := z.2.1
  norm_num at h
  linarith [sphereHandleRadius_le_one]

theorem mem_coordinateUnlinkExteriorPlanarFlowerSet_iff
    (m : ℕ) (z : {z : ℂ // z ≠ 0}) :
    z ∈ coordinateUnlinkExteriorPlanarFlowerSet m ↔
      ‖z.1 ^ m + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius ∧
        (1 / 8 : ℝ) ≤ ‖z.1 ^ m‖ ∧
          (1 / 8 : ℝ) ≤ ‖z.1 ^ m + 1‖ :=
  Iff.rfl

theorem sphereHandleRadius_mul_oneEighth_div_sphereHandleRadius :
    sphereHandleRadius * ((1 / 8 : ℝ) / sphereHandleRadius) = (1 / 8 : ℝ) := by
  field_simp [sphereHandleRadius_ne_zero]

/-! ## Affine coordinate identities -/

/-- The explicit complex-to-normal-plane map is also a left inverse. -/
@[simp]
theorem complexToUnlinkNormalPlane_unlinkNormalPlaneToComplex
    (v : UnlinkNormalPlane) :
    complexToUnlinkNormalPlane (unlinkNormalPlaneToComplex v) = v := by
  ext j
  fin_cases j <;>
    simp [complexToUnlinkNormalPlane, unlinkNormalPlaneToComplex,
      Complex.equivRealProdCLM_symm_apply]

/-- In complex coordinates the planar character is the cap coordinate scaled by the seam
radius and translated by `-1/2`. -/
theorem coordinateUnlinkExteriorPuncturedNormalDiskCharacter_affine
    (a : CoordinateUnlinkExteriorPuncturedNormalDisk) :
    (coordinateUnlinkExteriorPuncturedNormalDiskCharacter a : ℂ) =
      (sphereHandleRadius : ℂ) * unlinkNormalPlaneToComplex a.1.1 - (1 / 2 : ℂ) := by
  rw [coordinateUnlinkExteriorPuncturedNormalDiskCharacter_coe]
  simp [unlinkNormalPlaneToComplex, standardUnlinkNormalCenter,
    standardUnlinkHeight, Complex.equivRealProdCLM_symm_apply]
  ring

theorem coordinateUnlinkExteriorPuncturedNormalDiskCharacter_add_half
    (a : CoordinateUnlinkExteriorPuncturedNormalDisk) :
    (coordinateUnlinkExteriorPuncturedNormalDiskCharacter a : ℂ) + (1 / 2 : ℂ) =
      unlinkNormalPlaneToComplex (sphereHandleRadius • a.1.1) := by
  rw [coordinateUnlinkExteriorPuncturedNormalDiskCharacter_affine]
  simp [unlinkNormalPlaneToComplex, Complex.equivRealProdCLM_symm_apply]
  ring

theorem coordinateUnlinkExteriorPuncturedNormalDiskCharacter_add_one
    (a : CoordinateUnlinkExteriorPuncturedNormalDisk) :
    (coordinateUnlinkExteriorPuncturedNormalDiskCharacter a : ℂ) + 1 =
      unlinkNormalPlaneToComplex
        (sphereHandleRadius • a.1.1 - standardUnlinkNormalCenter 0) := by
  rw [coordinateUnlinkExteriorPuncturedNormalDiskCharacter_coe]
  simp [unlinkNormalPlaneToComplex, standardUnlinkNormalCenter,
    standardUnlinkHeight, Complex.equivRealProdCLM_symm_apply]
  ring

theorem norm_coordinateUnlinkExteriorPuncturedNormalDiskCharacter
    (a : CoordinateUnlinkExteriorPuncturedNormalDisk) :
    ‖(coordinateUnlinkExteriorPuncturedNormalDiskCharacter a : ℂ)‖ =
      sphereHandleRadius * dist a.1.1 (unlinkCapCoordinateCenter 1) := by
  rw [coordinateUnlinkExteriorPuncturedNormalDiskCharacter_coe,
    norm_unlinkNormalPlaneToComplex, ← dist_eq_norm,
    dist_sphereHandleRadius_smul_unlinkCapCoordinateCenter]

theorem norm_coordinateUnlinkExteriorPuncturedNormalDiskCharacter_add_one
    (a : CoordinateUnlinkExteriorPuncturedNormalDisk) :
    ‖(coordinateUnlinkExteriorPuncturedNormalDiskCharacter a : ℂ) + 1‖ =
      sphereHandleRadius * dist a.1.1 (unlinkCapCoordinateCenter 0) := by
  rw [coordinateUnlinkExteriorPuncturedNormalDiskCharacter_add_one,
    norm_unlinkNormalPlaneToComplex, ← dist_eq_norm,
    dist_sphereHandleRadius_smul_unlinkCapCoordinateCenter]

/-! ## Forward map -/

theorem coordinateUnlinkExteriorPlanarFlower_mem_of_pullback
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :
    z.1.2 ∈ coordinateUnlinkExteriorPlanarFlowerSet m := by
  let a : CoordinateUnlinkExteriorPuncturedNormalDisk := z.1.1
  have hpow : (coordinateUnlinkExteriorPuncturedNormalDiskCharacter a : ℂ) = z.1.2.1 ^ m :=
    congrArg Subtype.val z.2
  have hball : ‖a.1.1‖ ≤ 1 := mem_closedBall_zero_iff.mp a.1.2
  refine ⟨?_, ?_, ?_⟩
  · rw [← hpow, coordinateUnlinkExteriorPuncturedNormalDiskCharacter_add_half,
      norm_unlinkNormalPlaneToComplex, norm_smul, Real.norm_eq_abs,
      abs_of_pos sphereHandleRadius_pos]
    simpa using mul_le_mul_of_nonneg_left hball sphereHandleRadius_pos.le
  · calc
      (1 / 8 : ℝ) = sphereHandleRadius *
          ((1 / 8 : ℝ) / sphereHandleRadius) :=
        sphereHandleRadius_mul_oneEighth_div_sphereHandleRadius.symm
      _ ≤ sphereHandleRadius * dist a.1.1 (unlinkCapCoordinateCenter 1) :=
        mul_le_mul_of_nonneg_left a.2.2 sphereHandleRadius_pos.le
      _ = ‖(coordinateUnlinkExteriorPuncturedNormalDiskCharacter a : ℂ)‖ :=
        (norm_coordinateUnlinkExteriorPuncturedNormalDiskCharacter a).symm
      _ = ‖z.1.2.1 ^ m‖ := congrArg norm hpow
  · calc
      (1 / 8 : ℝ) = sphereHandleRadius *
          ((1 / 8 : ℝ) / sphereHandleRadius) :=
        sphereHandleRadius_mul_oneEighth_div_sphereHandleRadius.symm
      _ ≤ sphereHandleRadius * dist a.1.1 (unlinkCapCoordinateCenter 0) :=
        mul_le_mul_of_nonneg_left a.2.1 sphereHandleRadius_pos.le
      _ = ‖(coordinateUnlinkExteriorPuncturedNormalDiskCharacter a : ℂ) + 1‖ :=
        (norm_coordinateUnlinkExteriorPuncturedNormalDiskCharacter_add_one a).symm
      _ = ‖z.1.2.1 ^ m + 1‖ := congrArg norm (congrArg (· + 1) hpow)

/-- Forget the reconstructed disk coordinate and retain the pullback power coordinate. -/
def coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackToPlanarFlower
    (m : ℕ) : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m →
      CoordinateUnlinkExteriorPlanarFlower m :=
  fun z ↦ ⟨z.1.2, coordinateUnlinkExteriorPlanarFlower_mem_of_pullback m z⟩

@[simp]
theorem coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackToPlanarFlower_val
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :
    (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackToPlanarFlower m z).1.1 =
      z.1.2.1 :=
  rfl

theorem continuous_coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackToPlanarFlower
    (m : ℕ) :
    Continuous (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackToPlanarFlower m) :=
  Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _

/-! ## Inverse affine reconstruction -/

/-- Reconstruct the aligned cap-disk coordinate from a prospective power coordinate. -/
def coordinateUnlinkExteriorPlanarFlowerBaseRaw
    (m : ℕ) (z : {z : ℂ // z ≠ 0}) : SphereHandleFirst :=
  sphereHandleRadius⁻¹ •
    complexToUnlinkNormalPlane (z.1 ^ m + (1 / 2 : ℂ))

@[simp]
theorem sphereHandleRadius_smul_coordinateUnlinkExteriorPlanarFlowerBaseRaw
    (m : ℕ) (z : {z : ℂ // z ≠ 0}) :
    sphereHandleRadius • coordinateUnlinkExteriorPlanarFlowerBaseRaw m z =
      complexToUnlinkNormalPlane (z.1 ^ m + (1 / 2 : ℂ)) := by
  rw [coordinateUnlinkExteriorPlanarFlowerBaseRaw, smul_smul,
    mul_inv_cancel₀ sphereHandleRadius_ne_zero, one_smul]

theorem coordinateUnlinkExteriorPlanarFlowerBaseRaw_norm_le_one
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlower m) :
    ‖coordinateUnlinkExteriorPlanarFlowerBaseRaw m z.1‖ ≤ 1 := by
  rw [coordinateUnlinkExteriorPlanarFlowerBaseRaw, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr sphereHandleRadius_pos), norm_complexToUnlinkNormalPlane]
  exact (inv_mul_le_one₀ sphereHandleRadius_pos).2 z.2.1

theorem dist_planarFlowerBaseRaw_center_one
    (m : ℕ) (z : {z : ℂ // z ≠ 0}) :
    sphereHandleRadius *
        dist (coordinateUnlinkExteriorPlanarFlowerBaseRaw m z)
          (unlinkCapCoordinateCenter 1) =
      ‖z.1 ^ m‖ := by
  have hdist := dist_sphereHandleRadius_smul_unlinkCapCoordinateCenter
    (1 : Fin 2) (coordinateUnlinkExteriorPlanarFlowerBaseRaw m z)
  rw [sphereHandleRadius_smul_coordinateUnlinkExteriorPlanarFlowerBaseRaw,
    dist_eq_norm] at hdist
  have hvec : complexToUnlinkNormalPlane (z.1 ^ m + (1 / 2 : ℂ)) -
      standardUnlinkNormalCenter 1 = complexToUnlinkNormalPlane (z.1 ^ m) := by
    ext j
    fin_cases j <;>
      simp [complexToUnlinkNormalPlane, standardUnlinkNormalCenter,
        standardUnlinkHeight]
  rw [hvec, norm_complexToUnlinkNormalPlane] at hdist
  exact hdist.symm

theorem dist_planarFlowerBaseRaw_center_zero
    (m : ℕ) (z : {z : ℂ // z ≠ 0}) :
    sphereHandleRadius *
        dist (coordinateUnlinkExteriorPlanarFlowerBaseRaw m z)
          (unlinkCapCoordinateCenter 0) =
      ‖z.1 ^ m + 1‖ := by
  have hdist := dist_sphereHandleRadius_smul_unlinkCapCoordinateCenter
    (0 : Fin 2) (coordinateUnlinkExteriorPlanarFlowerBaseRaw m z)
  rw [sphereHandleRadius_smul_coordinateUnlinkExteriorPlanarFlowerBaseRaw,
    dist_eq_norm] at hdist
  have hvec : complexToUnlinkNormalPlane (z.1 ^ m + (1 / 2 : ℂ)) -
      standardUnlinkNormalCenter 0 = complexToUnlinkNormalPlane (z.1 ^ m + 1) := by
    ext j
    fin_cases j
    · simp [complexToUnlinkNormalPlane, standardUnlinkNormalCenter,
        standardUnlinkHeight]
      ring
    · simp [complexToUnlinkNormalPlane, standardUnlinkNormalCenter,
        standardUnlinkHeight]
  rw [hvec, norm_complexToUnlinkNormalPlane] at hdist
  exact hdist.symm

/-- The disk coordinate reconstructed from a flower point, bundled in the exact punctured disk. -/
def coordinateUnlinkExteriorPlanarFlowerBase
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlower m) :
    CoordinateUnlinkExteriorPuncturedNormalDisk := by
  refine ⟨⟨coordinateUnlinkExteriorPlanarFlowerBaseRaw m z.1,
    mem_closedBall_zero_iff.mpr
      (coordinateUnlinkExteriorPlanarFlowerBaseRaw_norm_le_one m z)⟩, ?_⟩
  change (1 / 8 : ℝ) / sphereHandleRadius ≤
        dist (coordinateUnlinkExteriorPlanarFlowerBaseRaw m z.1)
          (unlinkCapCoordinateCenter 0) ∧
      (1 / 8 : ℝ) / sphereHandleRadius ≤
        dist (coordinateUnlinkExteriorPlanarFlowerBaseRaw m z.1)
          (unlinkCapCoordinateCenter 1)
  constructor
  · apply le_of_mul_le_mul_left _ sphereHandleRadius_pos
    rw [sphereHandleRadius_mul_oneEighth_div_sphereHandleRadius,
      dist_planarFlowerBaseRaw_center_zero]
    exact z.2.2.2
  · apply le_of_mul_le_mul_left _ sphereHandleRadius_pos
    rw [sphereHandleRadius_mul_oneEighth_div_sphereHandleRadius,
      dist_planarFlowerBaseRaw_center_one]
    exact z.2.2.1

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerBase_val
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlower m) :
    (coordinateUnlinkExteriorPlanarFlowerBase m z).1.1 =
      sphereHandleRadius⁻¹ •
        complexToUnlinkNormalPlane (z.1.1 ^ m + (1 / 2 : ℂ)) :=
  rfl

theorem continuous_coordinateUnlinkExteriorPlanarFlowerBase (m : ℕ) :
    Continuous (coordinateUnlinkExteriorPlanarFlowerBase m) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  unfold coordinateUnlinkExteriorPlanarFlowerBaseRaw complexToUnlinkNormalPlane
  fun_prop

@[simp]
theorem coordinateUnlinkExteriorPuncturedNormalDiskCharacter_planarFlowerBase
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlower m) :
    (coordinateUnlinkExteriorPuncturedNormalDiskCharacter
        (coordinateUnlinkExteriorPlanarFlowerBase m z) : ℂ) = z.1.1 ^ m := by
  rw [coordinateUnlinkExteriorPuncturedNormalDiskCharacter_coe,
    coordinateUnlinkExteriorPlanarFlowerBase_val]
  change unlinkNormalPlaneToComplex
      (sphereHandleRadius • coordinateUnlinkExteriorPlanarFlowerBaseRaw m z.1 -
        standardUnlinkNormalCenter 1) = z.1.1 ^ m
  rw [sphereHandleRadius_smul_coordinateUnlinkExteriorPlanarFlowerBaseRaw]
  have hvec : complexToUnlinkNormalPlane (z.1.1 ^ m + (1 / 2 : ℂ)) -
      standardUnlinkNormalCenter 1 = complexToUnlinkNormalPlane (z.1.1 ^ m) := by
    ext j
    fin_cases j <;>
      simp [complexToUnlinkNormalPlane, standardUnlinkNormalCenter,
        standardUnlinkHeight]
  rw [hvec, unlinkNormalPlaneToComplex_complexToUnlinkNormalPlane]

/-- Reconstruct a pullback point from a planar flower point. -/
def coordinateUnlinkExteriorPlanarFlowerToPuncturedNormalDiskPowerPullback
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlower m) :
    CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m :=
  ⟨(coordinateUnlinkExteriorPlanarFlowerBase m z, z.1), by
    apply Subtype.ext
    rw [coordinateUnlinkExteriorPuncturedNormalDiskCharacter_planarFlowerBase,
      nonzeroComplexPow_coe]⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerToPuncturedNormalDiskPowerPullback_base
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlower m) :
    (coordinateUnlinkExteriorPlanarFlowerToPuncturedNormalDiskPowerPullback m z).1.1 =
      coordinateUnlinkExteriorPlanarFlowerBase m z :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerToPuncturedNormalDiskPowerPullback_powerCoordinate
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlower m) :
    (coordinateUnlinkExteriorPlanarFlowerToPuncturedNormalDiskPowerPullback m z).1.2 = z.1 :=
  rfl

theorem continuous_coordinateUnlinkExteriorPlanarFlowerToPuncturedNormalDiskPowerPullback
    (m : ℕ) :
    Continuous
      (coordinateUnlinkExteriorPlanarFlowerToPuncturedNormalDiskPowerPullback m) := by
  apply Continuous.subtype_mk
  exact (continuous_coordinateUnlinkExteriorPlanarFlowerBase m).prodMk continuous_subtype_val

/-! ## The homeomorphism -/

theorem coordinateUnlinkExteriorPlanarFlowerBase_forward
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :
    coordinateUnlinkExteriorPlanarFlowerBase m
        (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackToPlanarFlower m z) =
      z.1.1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply smul_right_injective SphereHandleFirst sphereHandleRadius_ne_zero
  change sphereHandleRadius • coordinateUnlinkExteriorPlanarFlowerBaseRaw m z.1.2 =
    sphereHandleRadius • z.1.1.1
  rw [sphereHandleRadius_smul_coordinateUnlinkExteriorPlanarFlowerBaseRaw]
  have hpow : z.1.2.1 ^ m =
      (coordinateUnlinkExteriorPuncturedNormalDiskCharacter z.1.1 : ℂ) :=
    (congrArg Subtype.val z.2).symm
  rw [hpow, coordinateUnlinkExteriorPuncturedNormalDiskCharacter_add_half,
    complexToUnlinkNormalPlane_unlinkNormalPlaneToComplex]

/-- The power coordinate is a complete point-set coordinate on the planar pullback. -/
def coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph
    (m : ℕ) :
    CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m ≃ₜ
      CoordinateUnlinkExteriorPlanarFlower m where
  toFun := coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackToPlanarFlower m
  invFun := coordinateUnlinkExteriorPlanarFlowerToPuncturedNormalDiskPowerPullback m
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact coordinateUnlinkExteriorPlanarFlowerBase_forward m z
    · rfl
  right_inv z := by
    apply Subtype.ext
    rfl
  continuous_toFun :=
    continuous_coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackToPlanarFlower m
  continuous_invFun :=
    continuous_coordinateUnlinkExteriorPlanarFlowerToPuncturedNormalDiskPowerPullback m

@[simp]
theorem coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph_apply
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :
    (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m z).1 =
      z.1.2 :=
  rfl

theorem coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph_apply_pow
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :
    (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m z).1.1 ^ m =
      (coordinateUnlinkExteriorPuncturedNormalDiskCharacter z.1.1 : ℂ) :=
  (congrArg Subtype.val z.2).symm

@[simp]
theorem coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph_base
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :
    coordinateUnlinkExteriorPlanarFlowerBase m
        (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m z) =
      z.1.1 :=
  coordinateUnlinkExteriorPlanarFlowerBase_forward m z

@[simp]
theorem coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph_symm_base
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlower m) :
    (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m).symm z
        |>.1.1 = coordinateUnlinkExteriorPlanarFlowerBase m z :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph_symm_power
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlower m) :
    (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m).symm z
        |>.1.2 = z.1 :=
  rfl

/-- Consequently the raw degree-zero planar pullback is empty as well. -/
theorem coordinateUnlinkExteriorPuncturedNormalDiskPowerPullback_zero_isEmpty :
    IsEmpty (CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback 0) := by
  constructor
  intro z
  exact coordinateUnlinkExteriorPlanarFlower_zero_isEmpty.false
    (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph 0 z)

/-! ## Root-of-unity equivariance -/

/-- The intrinsic root-of-unity action on the planar pullback power coordinate. -/
def coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap
    (m : ℕ) (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :
    CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m :=
  ⟨(z.1.1, ⟨((u.1 : ℂˣ) : ℂ) * z.1.2.1,
      mul_ne_zero (Units.ne_zero u.1) z.1.2.2⟩), by
    apply Subtype.ext
    change (coordinateUnlinkExteriorPuncturedNormalDiskCharacter z.1.1 : ℂ) =
      (((u.1 : ℂˣ) : ℂ) * z.1.2.1) ^ m
    rw [mul_pow, (mem_rootsOfUnity' m u.1).mp u.2, one_mul]
    exact congrArg Subtype.val z.2⟩

@[simp]
theorem coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap_base
    (m : ℕ) (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :
    (coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap m u z).1.1 = z.1.1 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap_powerCoordinate
    (m : ℕ) (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :
    ((coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap m u z).1.2 : ℂ) =
      ((u.1 : ℂˣ) : ℂ) * z.1.2.1 :=
  rfl

theorem coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap_one
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :
    coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap m 1 z = z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp

theorem coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap_mul
    (m : ℕ) (u v : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :
    coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap m (u * v) z =
      coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap m u
        (coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap m v z) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change ((((u * v).1 : ℂˣ) : ℂ) * z.1.2.1) =
      ((u.1 : ℂˣ) : ℂ) * (((v.1 : ℂˣ) : ℂ) * z.1.2.1)
    rw [Subgroup.coe_mul, Units.val_mul]
    exact mul_assoc _ _ _

instance coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackMulAction (m : ℕ) :
    MulAction (rootsOfUnity m ℂ)
      (CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) where
  smul := coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap m
  one_smul := coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap_one m
  mul_smul := coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap_mul m

theorem continuous_coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap
    (m : ℕ) (u : rootsOfUnity m ℂ) :
    Continuous (coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap m u) := by
  unfold coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap
  apply Continuous.subtype_mk
  exact (continuous_fst.comp continuous_subtype_val).prodMk <|
    (continuous_const.mul
      (continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val))).subtype_mk _

/-- The root-of-unity action on the flower's displayed complex coordinate. -/
def coordinateUnlinkExteriorPlanarFlowerDeckMap
    (m : ℕ) (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorPlanarFlower m) :
    CoordinateUnlinkExteriorPlanarFlower m :=
  ⟨⟨((u.1 : ℂˣ) : ℂ) * z.1.1,
      mul_ne_zero (Units.ne_zero u.1) z.1.2⟩, by
    change ‖(((u.1 : ℂˣ) : ℂ) * z.1.1) ^ m + (1 / 2 : ℂ)‖ ≤
        sphereHandleRadius ∧
      (1 / 8 : ℝ) ≤ ‖(((u.1 : ℂˣ) : ℂ) * z.1.1) ^ m‖ ∧
        (1 / 8 : ℝ) ≤ ‖(((u.1 : ℂˣ) : ℂ) * z.1.1) ^ m + 1‖
    rw [mul_pow, (mem_rootsOfUnity' m u.1).mp u.2, one_mul]
    exact z.2⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerDeckMap_val
    (m : ℕ) (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorPlanarFlower m) :
    (coordinateUnlinkExteriorPlanarFlowerDeckMap m u z).1.1 =
      ((u.1 : ℂˣ) : ℂ) * z.1.1 :=
  rfl

theorem coordinateUnlinkExteriorPlanarFlowerDeckMap_one
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlower m) :
    coordinateUnlinkExteriorPlanarFlowerDeckMap m 1 z = z := by
  apply Subtype.ext
  apply Subtype.ext
  simp

theorem coordinateUnlinkExteriorPlanarFlowerDeckMap_mul
    (m : ℕ) (u v : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorPlanarFlower m) :
    coordinateUnlinkExteriorPlanarFlowerDeckMap m (u * v) z =
      coordinateUnlinkExteriorPlanarFlowerDeckMap m u
        (coordinateUnlinkExteriorPlanarFlowerDeckMap m v z) := by
  apply Subtype.ext
  apply Subtype.ext
  change ((((u * v).1 : ℂˣ) : ℂ) * z.1.1) =
    ((u.1 : ℂˣ) : ℂ) * (((v.1 : ℂˣ) : ℂ) * z.1.1)
  rw [Subgroup.coe_mul, Units.val_mul]
  exact mul_assoc _ _ _

instance coordinateUnlinkExteriorPlanarFlowerMulAction (m : ℕ) :
    MulAction (rootsOfUnity m ℂ) (CoordinateUnlinkExteriorPlanarFlower m) where
  smul := coordinateUnlinkExteriorPlanarFlowerDeckMap m
  one_smul := coordinateUnlinkExteriorPlanarFlowerDeckMap_one m
  mul_smul := coordinateUnlinkExteriorPlanarFlowerDeckMap_mul m

theorem continuous_coordinateUnlinkExteriorPlanarFlowerDeckMap
    (m : ℕ) (u : rootsOfUnity m ℂ) :
    Continuous (coordinateUnlinkExteriorPlanarFlowerDeckMap m u) := by
  unfold coordinateUnlinkExteriorPlanarFlowerDeckMap
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_const.mul
    (continuous_subtype_val.comp continuous_subtype_val)

/-- The planar flower identification is exactly equivariant for multiplication of the power
coordinate by an `m`th root of unity. -/
@[simp]
theorem coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph_smul
    (m : ℕ) (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :
    coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m (u • z) =
      u • coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m z := by
  apply Subtype.ext
  rfl

def coordinateUnlinkExteriorPlanarFlowerDeckHomeomorph
    (m : ℕ) (u : rootsOfUnity m ℂ) :
    CoordinateUnlinkExteriorPlanarFlower m ≃ₜ
      CoordinateUnlinkExteriorPlanarFlower m where
  toFun := (u • ·)
  invFun := (u⁻¹ • ·)
  left_inv z := inv_smul_smul u z
  right_inv z := smul_inv_smul u z
  continuous_toFun := continuous_coordinateUnlinkExteriorPlanarFlowerDeckMap m u
  continuous_invFun := continuous_coordinateUnlinkExteriorPlanarFlowerDeckMap m u⁻¹

end SplittingSpheres
