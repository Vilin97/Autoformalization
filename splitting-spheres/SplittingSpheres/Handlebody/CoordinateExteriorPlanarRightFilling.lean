/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import SplittingSpheres.Foundations.TopologicalPushoutHomeomorph
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarFlower

/-!
# Filling the right hole of the planar flower

Dropping the lower bound on `‖z ^ m‖` from the planar flower fills its right-hand hole.  For
nonzero degree the filling piece is the literal closed complex disk of radius
`(1 / 8) ^ (1 / m)`, and its attaching boundary is the corresponding metric circle.  The old
flower and this disk cover the filled flower and meet exactly on that circle, giving a
point-set pushout homeomorphism.

No surface classification, smooth structure, or graph-thickening statement is made here.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-! ## The filled flower and its radial threshold -/

/-- The ambient planar set obtained by dropping the right-hole inequality and allowing `z = 0`. -/
def coordinateUnlinkExteriorPlanarRightFilledSet (m : ℕ) : Set ℂ :=
  {z |
    ‖z ^ m + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius ∧
      (1 / 8 : ℝ) ≤ ‖z ^ m + 1‖}

/-- The filled flower as a topological subtype of the whole complex plane. -/
abbrev CoordinateUnlinkExteriorPlanarRightFilledFlower (m : ℕ) : Type :=
  ↑(coordinateUnlinkExteriorPlanarRightFilledSet m)

theorem mem_coordinateUnlinkExteriorPlanarRightFilledSet_iff
    (m : ℕ) (z : ℂ) :
    z ∈ coordinateUnlinkExteriorPlanarRightFilledSet m ↔
      ‖z ^ m + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius ∧
        (1 / 8 : ℝ) ≤ ‖z ^ m + 1‖ :=
  Iff.rfl

/-- The raw degree-zero filled set is empty, just as the raw degree-zero flower is. -/
theorem coordinateUnlinkExteriorPlanarRightFilledFlower_zero_isEmpty :
    IsEmpty (CoordinateUnlinkExteriorPlanarRightFilledFlower 0) := by
  constructor
  intro z
  have h := z.2.1
  norm_num at h
  linarith [sphereHandleRadius_le_one]

theorem isClosed_coordinateUnlinkExteriorPlanarRightFilledSet (m : ℕ) :
    IsClosed (coordinateUnlinkExteriorPlanarRightFilledSet m) := by
  exact (isClosed_le
    (((continuous_id.pow m).add continuous_const).norm) continuous_const).inter
      (isClosed_le continuous_const
        (((continuous_id.pow m).add continuous_const).norm))

/-- Radius of the disk which fills the right hole. -/
def coordinateUnlinkExteriorPlanarRightFillingRadius (m : ℕ) : ℝ :=
  Real.rpow (1 / 8 : ℝ) (1 / (m : ℝ))

theorem coordinateUnlinkExteriorPlanarRightFillingRadius_pos (m : ℕ) :
    0 < coordinateUnlinkExteriorPlanarRightFillingRadius m :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem coordinateUnlinkExteriorPlanarRightFillingRadius_nonneg (m : ℕ) :
    0 ≤ coordinateUnlinkExteriorPlanarRightFillingRadius m :=
  (coordinateUnlinkExteriorPlanarRightFillingRadius_pos m).le

@[simp]
theorem coordinateUnlinkExteriorPlanarRightFillingRadius_pow
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarRightFillingRadius m ^ m = (1 / 8 : ℝ) := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  calc
    coordinateUnlinkExteriorPlanarRightFillingRadius m ^ m =
        Real.rpow (Real.rpow (1 / 8 : ℝ) (1 / (m : ℝ))) (m : ℝ) := by
      rw [coordinateUnlinkExteriorPlanarRightFillingRadius]
      exact (Real.rpow_natCast _ m).symm
    _ = Real.rpow (1 / 8 : ℝ) ((1 / (m : ℝ)) * (m : ℝ)) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 8) _ _).symm
    _ = (1 / 8 : ℝ) := by
      rw [div_mul_cancel₀ _ hm]
      exact Real.rpow_one _

theorem norm_pow_le_oneEighth_iff_le_rightFillingRadius
    (m : ℕ) [NeZero m] (z : ℂ) :
    ‖z ^ m‖ ≤ (1 / 8 : ℝ) ↔
      ‖z‖ ≤ coordinateUnlinkExteriorPlanarRightFillingRadius m := by
  rw [norm_pow, ← coordinateUnlinkExteriorPlanarRightFillingRadius_pow m]
  constructor
  · exact fun h ↦ le_of_pow_le_pow_left₀ (NeZero.ne m)
      (coordinateUnlinkExteriorPlanarRightFillingRadius_nonneg m) h
  · exact fun h ↦ pow_le_pow_left₀ (norm_nonneg z) h m

theorem norm_pow_lt_oneEighth_iff_lt_rightFillingRadius
    (m : ℕ) [NeZero m] (z : ℂ) :
    ‖z ^ m‖ < (1 / 8 : ℝ) ↔
      ‖z‖ < coordinateUnlinkExteriorPlanarRightFillingRadius m := by
  rw [norm_pow, ← coordinateUnlinkExteriorPlanarRightFillingRadius_pow m]
  constructor
  · exact fun h ↦ lt_of_pow_lt_pow_left₀ m
      (coordinateUnlinkExteriorPlanarRightFillingRadius_nonneg m) h
  · exact fun h ↦ pow_lt_pow_left₀ h
      (norm_nonneg z) (NeZero.ne m)

theorem norm_pow_eq_oneEighth_iff_eq_rightFillingRadius
    (m : ℕ) [NeZero m] (z : ℂ) :
    ‖z ^ m‖ = (1 / 8 : ℝ) ↔
      ‖z‖ = coordinateUnlinkExteriorPlanarRightFillingRadius m := by
  constructor
  · intro h
    apply le_antisymm
    · exact (norm_pow_le_oneEighth_iff_le_rightFillingRadius m z).mp h.le
    · apply le_of_pow_le_pow_left₀ (NeZero.ne m) (norm_nonneg z)
      rw [coordinateUnlinkExteriorPlanarRightFillingRadius_pow, ← norm_pow, h]
  · intro h
    rw [norm_pow, h, coordinateUnlinkExteriorPlanarRightFillingRadius_pow]

theorem fiveEighth_lt_sphereHandleRadius : (5 / 8 : ℝ) < sphereHandleRadius := by
  rw [← sq_lt_sq₀ (by norm_num) sphereHandleRadius_pos.le, sphereHandleRadius_sq]
  norm_num

/-- Every point whose `m`th power lies in the radius-`1/8` disk automatically satisfies the
two inequalities defining the filled flower. -/
theorem coordinateUnlinkExteriorPlanarRightFilledSet_mem_of_norm_pow_le
    (m : ℕ) {z : ℂ} (hz : ‖z ^ m‖ ≤ (1 / 8 : ℝ)) :
    z ∈ coordinateUnlinkExteriorPlanarRightFilledSet m := by
  constructor
  · calc
      ‖z ^ m + (1 / 2 : ℂ)‖ ≤ ‖z ^ m‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
      _ = ‖z ^ m‖ + 1 / 2 := by norm_num
      _ ≤ 1 / 8 + 1 / 2 := add_le_add hz le_rfl
      _ = 5 / 8 := by norm_num
      _ ≤ sphereHandleRadius := fiveEighth_lt_sphereHandleRadius.le
  · have hreverse : (1 : ℝ) - ‖z ^ m‖ ≤ ‖z ^ m + 1‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (-z ^ m)
      simpa [norm_neg, add_comm, sub_eq_add_neg] using h
    linarith

/-! ## The old flower and the literal filling disk -/

/-- Include the old flower in the filled flower by forgetting its nonvanishing and right-hole
proofs. -/
def coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower
    (m : ℕ) : C(CoordinateUnlinkExteriorPlanarFlower m,
      CoordinateUnlinkExteriorPlanarRightFilledFlower m) where
  toFun z := ⟨z.1.1, z.2.1, z.2.2.2⟩
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower_coe
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlower m) :
    (coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m z : ℂ) = z.1.1 :=
  rfl

theorem injective_coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower
    (m : ℕ) :
    Injective (coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m) := by
  intro z w h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun q : CoordinateUnlinkExteriorPlanarRightFilledFlower m ↦ q.1) h

/-- The open right hole, intrinsically as the strict power-preimage inside the filled flower. -/
def coordinateUnlinkExteriorPlanarRightOpenPowerDisk (m : ℕ) :
    Set (CoordinateUnlinkExteriorPlanarRightFilledFlower m) :=
  {z | ‖z.1 ^ m‖ < (1 / 8 : ℝ)}

theorem isOpen_coordinateUnlinkExteriorPlanarRightOpenPowerDisk (m : ℕ) :
    IsOpen (coordinateUnlinkExteriorPlanarRightOpenPowerDisk m) :=
  isOpen_lt
    (((continuous_subtype_val.pow m).norm)) continuous_const

/-- For nonzero degree the intrinsic power-preimage is literally the ambient open disk of the
selected filling radius. -/
theorem coordinateUnlinkExteriorPlanarRightOpenPowerDisk_eq_preimage_ball
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarRightOpenPowerDisk m =
      ((↑) : CoordinateUnlinkExteriorPlanarRightFilledFlower m → ℂ) ⁻¹'
        ball 0 (coordinateUnlinkExteriorPlanarRightFillingRadius m) := by
  ext z
  rw [coordinateUnlinkExteriorPlanarRightOpenPowerDisk, mem_ofPred_eq,
    mem_preimage, mem_ball_zero_iff,
    norm_pow_lt_oneEighth_iff_lt_rightFillingRadius]

/-- The old flower is exactly the complement of the open right disk in the filled flower. -/
theorem range_coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower
    (m : ℕ) :
    range (coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m) =
      (coordinateUnlinkExteriorPlanarRightOpenPowerDisk m)ᶜ := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact not_lt.mpr w.2.2.1
  · intro hz
    have hlower : (1 / 8 : ℝ) ≤ ‖z.1 ^ m‖ := not_lt.mp hz
    have hne : z.1 ≠ 0 := by
      intro hzero
      by_cases hm : m = 0
      · subst m
        exact coordinateUnlinkExteriorPlanarRightFilledFlower_zero_isEmpty.false z
      · rw [hzero, zero_pow hm, norm_zero] at hlower
        norm_num at hlower
    exact ⟨⟨⟨z.1, hne⟩, z.2.1, hlower, z.2.2⟩, rfl⟩

/-- The literal complex disk which fills the right hole. -/
abbrev CoordinateUnlinkExteriorPlanarRightFillingDisk (m : ℕ) : Type :=
  ↑(closedBall (0 : ℂ) (coordinateUnlinkExteriorPlanarRightFillingRadius m))

/-- The literal metric circle along which the filling disk is attached. -/
abbrev CoordinateUnlinkExteriorPlanarRightFillingBoundary (m : ℕ) : Type :=
  ↑(sphere (0 : ℂ) (coordinateUnlinkExteriorPlanarRightFillingRadius m))

/-- Include the filling disk into the filled flower. -/
def coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarRightFillingDisk m,
      CoordinateUnlinkExteriorPlanarRightFilledFlower m) where
  toFun z := ⟨z.1,
    coordinateUnlinkExteriorPlanarRightFilledSet_mem_of_norm_pow_le m <|
      (norm_pow_le_oneEighth_iff_le_rightFillingRadius m z.1).2 <|
        mem_closedBall_zero_iff.mp z.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower_coe
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarRightFillingDisk m) :
    (coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower m z : ℂ) = z.1 :=
  rfl

theorem injective_coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower m) := by
  intro z w h
  apply Subtype.ext
  exact congrArg
    (fun q : CoordinateUnlinkExteriorPlanarRightFilledFlower m ↦ q.1) h

/-- The metric-circle inclusion into the filling disk. -/
def coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk
    (m : ℕ) :
    C(CoordinateUnlinkExteriorPlanarRightFillingBoundary m,
      CoordinateUnlinkExteriorPlanarRightFillingDisk m) where
  toFun z := ⟨z.1, sphere_subset_closedBall z.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk_coe
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarRightFillingBoundary m) :
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m z : ℂ) = z.1 :=
  rfl

theorem injective_coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk
    (m : ℕ) :
    Injective (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m) := by
  intro z w h
  apply Subtype.ext
  exact congrArg
    (fun q : CoordinateUnlinkExteriorPlanarRightFillingDisk m ↦ q.1) h

/-- The same metric circle included into the old flower. -/
def coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarRightFillingBoundary m,
      CoordinateUnlinkExteriorPlanarFlower m) where
  toFun z := by
    have hnorm : ‖z.1‖ = coordinateUnlinkExteriorPlanarRightFillingRadius m :=
      mem_sphere_zero_iff_norm.mp z.2
    have hpow : ‖z.1 ^ m‖ = (1 / 8 : ℝ) :=
      (norm_pow_eq_oneEighth_iff_eq_rightFillingRadius m z.1).2 hnorm
    have hfilled := coordinateUnlinkExteriorPlanarRightFilledSet_mem_of_norm_pow_le m hpow.le
    refine ⟨⟨z.1, ?_⟩, hfilled.1, hpow.ge, hfilled.2⟩
    intro hzero
    rw [hzero, norm_zero] at hnorm
    exact (coordinateUnlinkExteriorPlanarRightFillingRadius_pos m).ne' hnorm.symm
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.subtype_mk _

@[simp]
theorem coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower_coe
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarRightFillingBoundary m) :
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m z).1.1 = z.1 :=
  rfl

@[simp]
theorem norm_pow_coordinateUnlinkExteriorPlanarRightFillingBoundary
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarRightFillingBoundary m) :
    ‖z.1 ^ m‖ = (1 / 8 : ℝ) :=
  (norm_pow_eq_oneEighth_iff_eq_rightFillingRadius m z.1).2
    (mem_sphere_zero_iff_norm.mp z.2)

theorem injective_coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m) := by
  intro z w h
  apply Subtype.ext
  exact congrArg (fun q : CoordinateUnlinkExteriorPlanarFlower m ↦ q.1.1) h

@[simp]
theorem coordinateUnlinkExteriorPlanarRightFilling_compatibility
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarRightFillingBoundary m) :
    coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m
        (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m z) =
      coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower m
        (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m z) := by
  apply Subtype.ext
  rfl

/-! ## Compactness of the two closed pieces -/

theorem coordinateUnlinkExteriorPlanarRightFilledSet_subset_closedBall_two
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarRightFilledSet m ⊆
      closedBall (0 : ℂ) 2 := by
  intro z hz
  rw [mem_closedBall_zero_iff]
  by_contra hle
  have htwo : (2 : ℝ) < ‖z‖ := lt_of_not_ge hle
  have hone : (1 : ℝ) ≤ ‖z‖ := by linarith
  have hself : ‖z‖ ≤ ‖z‖ ^ m := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
    rw [pow_succ]
    calc
      ‖z‖ = 1 * ‖z‖ := by rw [one_mul]
      _ ≤ ‖z‖ ^ k * ‖z‖ :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ hone) (norm_nonneg z)
  have hupper : ‖z ^ m‖ ≤ (3 / 2 : ℝ) := by
    calc
      ‖z ^ m‖ = ‖(z ^ m + (1 / 2 : ℂ)) - (1 / 2 : ℂ)‖ := by
        congr 1
        ring
      _ ≤ ‖z ^ m + (1 / 2 : ℂ)‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
      _ = ‖z ^ m + (1 / 2 : ℂ)‖ + 1 / 2 := by norm_num
      _ ≤ sphereHandleRadius + 1 / 2 := add_le_add hz.1 le_rfl
      _ ≤ 1 + 1 / 2 := add_le_add sphereHandleRadius_le_one le_rfl
      _ = 3 / 2 := by norm_num
  have hlower : (2 : ℝ) < ‖z ^ m‖ := by
    rw [norm_pow]
    exact htwo.trans_le hself
  linarith

theorem isCompact_coordinateUnlinkExteriorPlanarRightFilledSet
    (m : ℕ) [NeZero m] :
    IsCompact (coordinateUnlinkExteriorPlanarRightFilledSet m) :=
  (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset
    (isClosed_coordinateUnlinkExteriorPlanarRightFilledSet m)
    (coordinateUnlinkExteriorPlanarRightFilledSet_subset_closedBall_two m)

theorem compactSpace_coordinateUnlinkExteriorPlanarRightFilledFlower
    (m : ℕ) [NeZero m] :
    CompactSpace (CoordinateUnlinkExteriorPlanarRightFilledFlower m) :=
  isCompact_iff_compactSpace.mp
    (isCompact_coordinateUnlinkExteriorPlanarRightFilledSet m)

/-- The old closed threshold region, expressed intrinsically in the filled flower. -/
def coordinateUnlinkExteriorPlanarRightOldPartSet (m : ℕ) :
    Set (CoordinateUnlinkExteriorPlanarRightFilledFlower m) :=
  {z | (1 / 8 : ℝ) ≤ ‖z.1 ^ m‖}

theorem isClosed_coordinateUnlinkExteriorPlanarRightOldPartSet (m : ℕ) :
    IsClosed (coordinateUnlinkExteriorPlanarRightOldPartSet m) :=
  isClosed_le continuous_const ((continuous_subtype_val.pow m).norm)

/-- The old flower is canonically homeomorphic to the old closed threshold region inside the
filled flower. -/
def coordinateUnlinkExteriorPlanarFlowerRightOldPartHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarFlower m ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarRightOldPartSet m) where
  toFun z := ⟨coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m z, z.2.2.1⟩
  invFun z := by
    refine ⟨⟨z.1.1, ?_⟩, z.1.2.1, z.2, z.1.2.2⟩
    intro hzero
    have hz := z.2
    change (1 / 8 : ℝ) ≤ ‖z.1.1 ^ m‖ at hz
    rw [hzero, zero_pow (NeZero.ne m), norm_zero] at hz
    norm_num at hz
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  continuous_toFun := by
    exact (coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m).continuous.subtype_mk _
  continuous_invFun := by
    have hcomplex : Continuous
        (fun z : ↑(coordinateUnlinkExteriorPlanarRightOldPartSet m) ↦ z.1.1) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (hcomplex.subtype_mk _).subtype_mk _

theorem compactSpace_coordinateUnlinkExteriorPlanarFlower
    (m : ℕ) [NeZero m] :
    CompactSpace (CoordinateUnlinkExteriorPlanarFlower m) := by
  let _ : CompactSpace (CoordinateUnlinkExteriorPlanarRightFilledFlower m) :=
    compactSpace_coordinateUnlinkExteriorPlanarRightFilledFlower m
  let _ : CompactSpace ↑(coordinateUnlinkExteriorPlanarRightOldPartSet m) :=
    isCompact_iff_compactSpace.mp
      (isClosed_coordinateUnlinkExteriorPlanarRightOldPartSet m).isCompact
  exact (coordinateUnlinkExteriorPlanarFlowerRightOldPartHomeomorph m).symm.compactSpace

/-- The filling-disk image is exactly the complementary closed threshold region. -/
theorem range_coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower
    (m : ℕ) [NeZero m] :
    range (coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower m) =
      {z : CoordinateUnlinkExteriorPlanarRightFilledFlower m |
        ‖z.1 ^ m‖ ≤ (1 / 8 : ℝ)} := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact (norm_pow_le_oneEighth_iff_le_rightFillingRadius m w.1).2
      (mem_closedBall_zero_iff.mp w.2)
  · intro hz
    refine ⟨⟨z.1, mem_closedBall_zero_iff.mpr
      ((norm_pow_le_oneEighth_iff_le_rightFillingRadius m z.1).1 hz)⟩, ?_⟩
    apply Subtype.ext
    rfl

/-! ## Exact gluing and pushout recognition -/

/-- The old flower capped by the literal right filling disk along their common metric circle. -/
abbrev CoordinateUnlinkExteriorPlanarRightFilledPushout
    (m : ℕ) [NeZero m] : Type :=
  TopologicalPushout
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m)

/-- A cross-piece equality in the filled flower occurs at a unique displayed boundary point. -/
theorem coordinateUnlinkExteriorPlanarRightFilling_cross
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarFlower m)
    (y : CoordinateUnlinkExteriorPlanarRightFillingDisk m)
    (hxy : coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m x =
      coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower m y) :
    ∃ a : CoordinateUnlinkExteriorPlanarRightFillingBoundary m,
      coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m a = x ∧
        coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m a = y := by
  have hval : x.1.1 = y.1 :=
    congrArg (fun q : CoordinateUnlinkExteriorPlanarRightFilledFlower m ↦ q.1) hxy
  have hyupper : ‖y.1 ^ m‖ ≤ (1 / 8 : ℝ) :=
    (norm_pow_le_oneEighth_iff_le_rightFillingRadius m y.1).2
      (mem_closedBall_zero_iff.mp y.2)
  have hylower : (1 / 8 : ℝ) ≤ ‖y.1 ^ m‖ := by
    rw [← hval]
    exact x.2.2.1
  have hypow : ‖y.1 ^ m‖ = (1 / 8 : ℝ) := le_antisymm hyupper hylower
  have hynorm : ‖y.1‖ = coordinateUnlinkExteriorPlanarRightFillingRadius m :=
    (norm_pow_eq_oneEighth_iff_eq_rightFillingRadius m y.1).mp hypow
  let a : CoordinateUnlinkExteriorPlanarRightFillingBoundary m :=
    ⟨y.1, mem_sphere_zero_iff_norm.mpr hynorm⟩
  refine ⟨a, ?_, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact hval.symm
  · apply Subtype.ext
    rfl

/-- The old flower and the right filling disk jointly cover the filled flower. -/
theorem range_coordinateUnlinkExteriorPlanarRightFilling_union
    (m : ℕ) [NeZero m] :
    range (coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m) ∪
        range (coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower m) = univ := by
  rw [eq_univ_iff_forall]
  intro z
  rcases le_total (1 / 8 : ℝ) ‖z.1 ^ m‖ with hlower | hupper
  · left
    have hne : z.1 ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow (NeZero.ne m), norm_zero] at hlower
      norm_num at hlower
    let x : CoordinateUnlinkExteriorPlanarFlower m :=
      ⟨⟨z.1, hne⟩, z.2.1, hlower, z.2.2⟩
    exact ⟨x, by apply Subtype.ext; rfl⟩
  · right
    let y : CoordinateUnlinkExteriorPlanarRightFillingDisk m :=
      ⟨z.1, mem_closedBall_zero_iff.mpr
        ((norm_pow_le_oneEighth_iff_le_rightFillingRadius m z.1).mp hupper)⟩
    exact ⟨y, by apply Subtype.ext; rfl⟩

/-- The exact overlap of the two piece images is the image of the attaching metric circle. -/
theorem range_coordinateUnlinkExteriorPlanarRightFilling_intersection
    (m : ℕ) [NeZero m] :
    range (coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m) ∩
        range (coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower m) =
      range (coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m ∘
        coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m) := by
  ext z
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hxy : coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m x =
        coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower m y := hx.trans hy.symm
    obtain ⟨a, ha, -⟩ := coordinateUnlinkExteriorPlanarRightFilling_cross m x y hxy
    refine ⟨a, ?_⟩
    change coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m
        (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m a) = z
    rw [ha, hx]
  · rintro ⟨a, rfl⟩
    constructor
    · exact ⟨coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m a, rfl⟩
    · exact ⟨coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m a,
        (coordinateUnlinkExteriorPlanarRightFilling_compatibility m a).symm⟩

/-- Filling the right hole is exactly the topological pushout of the old flower and the literal
closed complex disk along their common metric circle. -/
def coordinateUnlinkExteriorPlanarRightFilledPushoutHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarRightFilledPushout m ≃ₜ
      CoordinateUnlinkExteriorPlanarRightFilledFlower m := by
  let _ : CompactSpace (CoordinateUnlinkExteriorPlanarFlower m) :=
    compactSpace_coordinateUnlinkExteriorPlanarFlower m
  exact topologicalPushoutHomeomorph
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m)
    (coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m)
    (coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower m)
    (coordinateUnlinkExteriorPlanarRightFilling_compatibility m)
    (injective_coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
    (injective_coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m)
    (injective_coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower m)
    (coordinateUnlinkExteriorPlanarRightFilling_cross m)
    (range_coordinateUnlinkExteriorPlanarRightFilling_union m)

@[simp]
theorem coordinateUnlinkExteriorPlanarRightFilledPushoutHomeomorph_inl
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarFlower m) :
    coordinateUnlinkExteriorPlanarRightFilledPushoutHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
          (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m) x) =
      coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m x := by
  let _ : CompactSpace (CoordinateUnlinkExteriorPlanarFlower m) :=
    compactSpace_coordinateUnlinkExteriorPlanarFlower m
  simp [coordinateUnlinkExteriorPlanarRightFilledPushoutHomeomorph]

@[simp]
theorem coordinateUnlinkExteriorPlanarRightFilledPushoutHomeomorph_inr
    (m : ℕ) [NeZero m]
    (y : CoordinateUnlinkExteriorPlanarRightFillingDisk m) :
    coordinateUnlinkExteriorPlanarRightFilledPushoutHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
          (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m) y) =
      coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower m y := by
  let _ : CompactSpace (CoordinateUnlinkExteriorPlanarFlower m) :=
    compactSpace_coordinateUnlinkExteriorPlanarFlower m
  simp [coordinateUnlinkExteriorPlanarRightFilledPushoutHomeomorph]

end SplittingSpheres
