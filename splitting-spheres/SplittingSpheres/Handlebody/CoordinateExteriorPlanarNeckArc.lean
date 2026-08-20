/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarOuterDiskSpin

/-!
# Lifted vertical arcs in the planar power flower

The vertical segment

`-1/2 + sphereHandleRadius * (2t - 1) * I`, for `0 ≤ t ≤ 1`,

lies in the polynomial outer disk and avoids both deleted character disks.  A continuous branch
of the `m`th root on the disk `ball (-1) 1` therefore gives one lifted arc in the planar flower.
Its `ZMod m` deck translates form a jointly injective family parameterized by the closed
interval.

Only these explicit point-set and continuity statements are made.  There is no cutting,
separation, neck-sphere, surface-classification, or smoothness claim.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-! ## The vertical character arc -/

/-- The closed unit interval used to parameterize the neck arcs. -/
abbrev CoordinateUnlinkExteriorPlanarNeckInterval : Type :=
  Set.Icc (0 : ℝ) 1

/-- The vertical character segment in the polynomial outer disk. -/
def coordinateUnlinkExteriorPlanarNeckBaseArc
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) : ℂ :=
  (-1 / 2 : ℂ) +
    ((sphereHandleRadius * (2 * (t : ℝ) - 1) : ℝ) : ℂ) * Complex.I

theorem continuous_coordinateUnlinkExteriorPlanarNeckBaseArc :
    Continuous coordinateUnlinkExteriorPlanarNeckBaseArc := by
  unfold coordinateUnlinkExteriorPlanarNeckBaseArc
  fun_prop

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckBaseArc_re
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarNeckBaseArc t).re = -1 / 2 := by
  simp [coordinateUnlinkExteriorPlanarNeckBaseArc]

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckBaseArc_im
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarNeckBaseArc t).im =
      sphereHandleRadius * (2 * (t : ℝ) - 1) := by
  simp [coordinateUnlinkExteriorPlanarNeckBaseArc]

theorem coordinateUnlinkExteriorPlanarNeckBaseArc_add_half
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarNeckBaseArc t + (1 / 2 : ℂ) =
      ((sphereHandleRadius * (2 * (t : ℝ) - 1) : ℝ) : ℂ) * Complex.I := by
  simp [coordinateUnlinkExteriorPlanarNeckBaseArc]
  ring

theorem coordinateUnlinkExteriorPlanarNeckBaseArc_add_one
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarNeckBaseArc t + 1 =
      (1 / 2 : ℂ) +
        ((sphereHandleRadius * (2 * (t : ℝ) - 1) : ℝ) : ℂ) * Complex.I := by
  simp [coordinateUnlinkExteriorPlanarNeckBaseArc]
  ring

/-- The parameter `0` is the lower endpoint of the vertical segment. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckBaseArc_zero :
    coordinateUnlinkExteriorPlanarNeckBaseArc 0 =
      (-1 / 2 : ℂ) - (sphereHandleRadius : ℂ) * Complex.I := by
  simp [coordinateUnlinkExteriorPlanarNeckBaseArc]
  ring

/-- The parameter `1` is the upper endpoint of the vertical segment. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckBaseArc_one :
    coordinateUnlinkExteriorPlanarNeckBaseArc 1 =
      (-1 / 2 : ℂ) + (sphereHandleRadius : ℂ) * Complex.I := by
  simp [coordinateUnlinkExteriorPlanarNeckBaseArc]
  ring

theorem abs_two_mul_sub_one_le_one_on_neckInterval
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    |2 * (t : ℝ) - 1| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [t.2.1, t.2.2]

theorem norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_half
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    ‖coordinateUnlinkExteriorPlanarNeckBaseArc t + (1 / 2 : ℂ)‖ =
      sphereHandleRadius * |2 * (t : ℝ) - 1| := by
  rw [coordinateUnlinkExteriorPlanarNeckBaseArc_add_half, norm_mul,
    Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_mul, abs_of_pos sphereHandleRadius_pos]

theorem norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_half_le
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    ‖coordinateUnlinkExteriorPlanarNeckBaseArc t + (1 / 2 : ℂ)‖ ≤
      sphereHandleRadius := by
  rw [norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_half]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left
      (abs_two_mul_sub_one_le_one_on_neckInterval t) sphereHandleRadius_pos.le

theorem norm_coordinateUnlinkExteriorPlanarNeckBaseArc_ge_half
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (1 / 2 : ℝ) ≤ ‖coordinateUnlinkExteriorPlanarNeckBaseArc t‖ := by
  calc
    (1 / 2 : ℝ) = |(coordinateUnlinkExteriorPlanarNeckBaseArc t).re| := by
      rw [coordinateUnlinkExteriorPlanarNeckBaseArc_re]
      norm_num
    _ ≤ ‖coordinateUnlinkExteriorPlanarNeckBaseArc t‖ :=
      Complex.abs_re_le_norm _

theorem norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_one_ge_half
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (1 / 2 : ℝ) ≤ ‖coordinateUnlinkExteriorPlanarNeckBaseArc t + 1‖ := by
  calc
    (1 / 2 : ℝ) = |(coordinateUnlinkExteriorPlanarNeckBaseArc t + 1).re| := by
      rw [Complex.add_re, coordinateUnlinkExteriorPlanarNeckBaseArc_re]
      norm_num
    _ ≤ ‖coordinateUnlinkExteriorPlanarNeckBaseArc t + 1‖ :=
      Complex.abs_re_le_norm _

theorem coordinateUnlinkExteriorPlanarNeckBaseArc_ne_zero
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarNeckBaseArc t ≠ 0 := by
  intro hzero
  have h := norm_coordinateUnlinkExteriorPlanarNeckBaseArc_ge_half t
  rw [hzero, norm_zero] at h
  norm_num at h

theorem injective_coordinateUnlinkExteriorPlanarNeckBaseArc :
    Injective coordinateUnlinkExteriorPlanarNeckBaseArc := by
  intro t s hts
  apply Subtype.ext
  have him := congrArg Complex.im hts
  simp only [coordinateUnlinkExteriorPlanarNeckBaseArc_im] at him
  nlinarith [sphereHandleRadius_pos]

/-! ## A selected continuous root branch -/

/-- A simply connected root domain containing the complete vertical character segment. -/
def coordinateUnlinkExteriorPlanarNeckRootDomain : Set ℂ :=
  ball (-1 : ℂ) 1

theorem isOpen_coordinateUnlinkExteriorPlanarNeckRootDomain :
    IsOpen coordinateUnlinkExteriorPlanarNeckRootDomain :=
  isOpen_ball

theorem isSimplyConnected_coordinateUnlinkExteriorPlanarNeckRootDomain :
    IsSimplyConnected coordinateUnlinkExteriorPlanarNeckRootDomain := by
  let _ : ContractibleSpace coordinateUnlinkExteriorPlanarNeckRootDomain :=
    (convex_ball (-1 : ℂ) 1).contractibleSpace (nonempty_ball.mpr zero_lt_one)
  change SimplyConnectedSpace coordinateUnlinkExteriorPlanarNeckRootDomain
  infer_instance

theorem zero_not_mem_coordinateUnlinkExteriorPlanarNeckRootDomain :
    (0 : ℂ) ∉ coordinateUnlinkExteriorPlanarNeckRootDomain := by
  norm_num [coordinateUnlinkExteriorPlanarNeckRootDomain, mem_ball, Complex.dist_eq]

theorem zero_not_mem_image_id_coordinateUnlinkExteriorPlanarNeckRootDomain :
    (0 : ℂ) ∉ id '' coordinateUnlinkExteriorPlanarNeckRootDomain := by
  simpa only [image_id] using
    zero_not_mem_coordinateUnlinkExteriorPlanarNeckRootDomain

theorem coordinateUnlinkExteriorPlanarNeckBaseArc_mem_rootDomain
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarNeckBaseArc t ∈
      coordinateUnlinkExteriorPlanarNeckRootDomain := by
  change dist (coordinateUnlinkExteriorPlanarNeckBaseArc t) (-1 : ℂ) < 1
  rw [Complex.dist_eq]
  have hsub : coordinateUnlinkExteriorPlanarNeckBaseArc t - (-1 : ℂ) =
      (1 / 2 : ℂ) +
        ((sphereHandleRadius * (2 * (t : ℝ) - 1) : ℝ) : ℂ) * Complex.I := by
    rw [sub_neg_eq_add, coordinateUnlinkExteriorPlanarNeckBaseArc_add_one]
  rw [hsub, ← sq_lt_sq₀ (norm_nonneg _) zero_le_one, Complex.sq_norm]
  have hy : (2 * (t : ℝ) - 1) ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one (2 * (t : ℝ) - 1)).2
      (abs_two_mul_sub_one_le_one_on_neckInterval t)
  rw [Complex.normSq_apply]
  norm_num [Complex.mul_re, Complex.mul_im]
  nlinarith [sphereHandleRadius_sq]

theorem exists_coordinateUnlinkExteriorPlanarNeckPowerRoot
    (m : ℕ) [NeZero m] :
    ∃ f : ℂ → ℂ,
      ContinuousOn f coordinateUnlinkExteriorPlanarNeckRootDomain ∧
        ∀ z : ℂ, f z ^ m = z := by
  simpa only [id_eq] using
    (Complex.exists_continuousOn_pow_eq
      isSimplyConnected_coordinateUnlinkExteriorPlanarNeckRootDomain
      isOpen_coordinateUnlinkExteriorPlanarNeckRootDomain
      (g := id) continuousOn_id
      zero_not_mem_image_id_coordinateUnlinkExteriorPlanarNeckRootDomain
      (NeZero.ne m))

/-- A selected continuous `m`th-root branch on the neck root domain. -/
def coordinateUnlinkExteriorPlanarNeckPowerRoot
    (m : ℕ) [NeZero m] : ℂ → ℂ :=
  Classical.choose (exists_coordinateUnlinkExteriorPlanarNeckPowerRoot m)

theorem continuousOn_coordinateUnlinkExteriorPlanarNeckPowerRoot
    (m : ℕ) [NeZero m] :
    ContinuousOn (coordinateUnlinkExteriorPlanarNeckPowerRoot m)
      coordinateUnlinkExteriorPlanarNeckRootDomain :=
  (Classical.choose_spec (exists_coordinateUnlinkExteriorPlanarNeckPowerRoot m)).1

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckPowerRoot_pow
    (m : ℕ) [NeZero m] (z : ℂ) :
    coordinateUnlinkExteriorPlanarNeckPowerRoot m z ^ m = z :=
  (Classical.choose_spec (exists_coordinateUnlinkExteriorPlanarNeckPowerRoot m)).2 z

theorem continuous_coordinateUnlinkExteriorPlanarNeckPowerRoot_comp
    (m : ℕ) [NeZero m] :
    Continuous (fun t : CoordinateUnlinkExteriorPlanarNeckInterval ↦
      coordinateUnlinkExteriorPlanarNeckPowerRoot m
      (coordinateUnlinkExteriorPlanarNeckBaseArc t)) :=
  (continuousOn_coordinateUnlinkExteriorPlanarNeckPowerRoot m).comp_continuous
    continuous_coordinateUnlinkExteriorPlanarNeckBaseArc
    coordinateUnlinkExteriorPlanarNeckBaseArc_mem_rootDomain

theorem coordinateUnlinkExteriorPlanarNeckPowerRoot_ne_zero
    (m : ℕ) [NeZero m] (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarNeckPowerRoot m
        (coordinateUnlinkExteriorPlanarNeckBaseArc t) ≠ 0 := by
  intro hzero
  have hp := coordinateUnlinkExteriorPlanarNeckPowerRoot_pow m
    (coordinateUnlinkExteriorPlanarNeckBaseArc t)
  rw [hzero, zero_pow (NeZero.ne m)] at hp
  exact coordinateUnlinkExteriorPlanarNeckBaseArc_ne_zero t hp.symm

/-! ## The selected arc in the flower -/

/-- The selected root lift of the vertical character segment, bundled in the planar flower. -/
def coordinateUnlinkExteriorPlanarNeckArc
    (m : ℕ) [NeZero m] (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    CoordinateUnlinkExteriorPlanarFlower m :=
  ⟨⟨coordinateUnlinkExteriorPlanarNeckPowerRoot m
      (coordinateUnlinkExteriorPlanarNeckBaseArc t),
    coordinateUnlinkExteriorPlanarNeckPowerRoot_ne_zero (m := m) t⟩, by
      rw [mem_coordinateUnlinkExteriorPlanarFlowerSet_iff,
        coordinateUnlinkExteriorPlanarNeckPowerRoot_pow]
      exact ⟨norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_half_le t,
        le_trans (by norm_num) (norm_coordinateUnlinkExteriorPlanarNeckBaseArc_ge_half t),
        le_trans (by norm_num)
          (norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_one_ge_half t)⟩⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckArc_val
    (m : ℕ) [NeZero m] (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarNeckArc m t).1.1 =
      coordinateUnlinkExteriorPlanarNeckPowerRoot m
        (coordinateUnlinkExteriorPlanarNeckBaseArc t) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckArc_pow
    (m : ℕ) [NeZero m] (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarNeckArc m t).1.1 ^ m =
      coordinateUnlinkExteriorPlanarNeckBaseArc t :=
  coordinateUnlinkExteriorPlanarNeckPowerRoot_pow m _

theorem continuous_coordinateUnlinkExteriorPlanarNeckArc
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarNeckArc m) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_coordinateUnlinkExteriorPlanarNeckPowerRoot_comp (m := m)

theorem injective_coordinateUnlinkExteriorPlanarNeckArc
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckArc m) := by
  intro t s hts
  apply injective_coordinateUnlinkExteriorPlanarNeckBaseArc
  rw [← coordinateUnlinkExteriorPlanarNeckArc_pow m t,
    ← coordinateUnlinkExteriorPlanarNeckArc_pow m s, hts]

/-! ## Endpoint and interior geometry -/

theorem coordinateUnlinkExteriorPlanarNeckArc_outer_norm
    (m : ℕ) [NeZero m] (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    ‖(coordinateUnlinkExteriorPlanarNeckArc m t).1.1 ^ m + (1 / 2 : ℂ)‖ =
      sphereHandleRadius * |2 * (t : ℝ) - 1| := by
  rw [coordinateUnlinkExteriorPlanarNeckArc_pow,
    norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_half]

theorem coordinateUnlinkExteriorPlanarNeckArc_zero_mem_outerBoundary
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarNeckArc m 0).1.1 ∈
      coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m := by
  change ‖(coordinateUnlinkExteriorPlanarNeckArc m 0).1.1 ^ m + (1 / 2 : ℂ)‖ =
    sphereHandleRadius
  rw [coordinateUnlinkExteriorPlanarNeckArc_outer_norm]
  norm_num

theorem coordinateUnlinkExteriorPlanarNeckArc_one_mem_outerBoundary
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarNeckArc m 1).1.1 ∈
      coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m := by
  change ‖(coordinateUnlinkExteriorPlanarNeckArc m 1).1.1 ^ m + (1 / 2 : ℂ)‖ =
    sphereHandleRadius
  rw [coordinateUnlinkExteriorPlanarNeckArc_outer_norm]
  norm_num

/-- Away from the two interval endpoints, the lifted arc lies strictly inside the polynomial
outer boundary. -/
theorem coordinateUnlinkExteriorPlanarNeckArc_outer_norm_lt
    (m : ℕ) [NeZero m] (t : CoordinateUnlinkExteriorPlanarNeckInterval)
    (ht : (t : ℝ) ∈ Ioo 0 1) :
    ‖(coordinateUnlinkExteriorPlanarNeckArc m t).1.1 ^ m + (1 / 2 : ℂ)‖ <
      sphereHandleRadius := by
  rw [coordinateUnlinkExteriorPlanarNeckArc_outer_norm]
  have habs : |2 * (t : ℝ) - 1| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  simpa only [mul_one] using
    mul_lt_mul_of_pos_left habs sphereHandleRadius_pos

/-! ## All deck translates -/

/-- The translate of the selected arc with deck index `a`. -/
def coordinateUnlinkExteriorPlanarNeckArcTranslate
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    CoordinateUnlinkExteriorPlanarFlower m :=
  coordinateUnlinkExteriorPlanarFlowerDeckMap m
    (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a))
    (coordinateUnlinkExteriorPlanarNeckArc m t)

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckArcTranslate_val
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarNeckArcTranslate m a t).1.1 =
      (((standardRootsOfUnityZModMulEquiv m
        (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) *
        (coordinateUnlinkExteriorPlanarNeckArc m t).1.1 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckArcTranslate_pow
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarNeckArcTranslate m a t).1.1 ^ m =
      coordinateUnlinkExteriorPlanarNeckBaseArc t := by
  rw [coordinateUnlinkExteriorPlanarNeckArcTranslate_val, mul_pow,
    (mem_rootsOfUnity' m
      (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).1).mp
        (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).2,
    one_mul, coordinateUnlinkExteriorPlanarNeckArc_pow]

theorem coordinateUnlinkExteriorPlanarNeckArcTranslate_outer_norm
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    ‖(coordinateUnlinkExteriorPlanarNeckArcTranslate m a t).1.1 ^ m +
        (1 / 2 : ℂ)‖ = sphereHandleRadius * |2 * (t : ℝ) - 1| := by
  rw [coordinateUnlinkExteriorPlanarNeckArcTranslate_pow,
    norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_half]

theorem coordinateUnlinkExteriorPlanarNeckArcTranslate_zero_mem_outerBoundary
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (coordinateUnlinkExteriorPlanarNeckArcTranslate m a 0).1.1 ∈
      coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m := by
  change ‖(coordinateUnlinkExteriorPlanarNeckArcTranslate m a 0).1.1 ^ m +
    (1 / 2 : ℂ)‖ = sphereHandleRadius
  rw [coordinateUnlinkExteriorPlanarNeckArcTranslate_outer_norm]
  norm_num

theorem coordinateUnlinkExteriorPlanarNeckArcTranslate_one_mem_outerBoundary
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (coordinateUnlinkExteriorPlanarNeckArcTranslate m a 1).1.1 ∈
      coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m := by
  change ‖(coordinateUnlinkExteriorPlanarNeckArcTranslate m a 1).1.1 ^ m +
    (1 / 2 : ℂ)‖ = sphereHandleRadius
  rw [coordinateUnlinkExteriorPlanarNeckArcTranslate_outer_norm]
  norm_num

theorem continuous_coordinateUnlinkExteriorPlanarNeckArcTranslate
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Continuous (coordinateUnlinkExteriorPlanarNeckArcTranslate m a) :=
  (continuous_coordinateUnlinkExteriorPlanarFlowerDeckMap m _).comp
    (continuous_coordinateUnlinkExteriorPlanarNeckArc m)

/-- Applying deck index `a` to the arc indexed by `b` adds their `ZMod m` labels. -/
theorem coordinateUnlinkExteriorPlanarNeckArcTranslate_add
    (m : ℕ) [NeZero m] (a b : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarFlowerDeckMap m
        (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a))
        (coordinateUnlinkExteriorPlanarNeckArcTranslate m b t) =
      coordinateUnlinkExteriorPlanarNeckArcTranslate m (a + b) t := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [coordinateUnlinkExteriorPlanarNeckArcTranslate_val,
    coordinateUnlinkExteriorPlanarFlowerDeckMap_val]
  rw [← mul_assoc]
  congr 1
  exact congrArg (fun u : rootsOfUnity m ℂ ↦ ((u.1 : ℂˣ) : ℂ)) <|
    (standardRootsOfUnityZModMulEquiv m).map_mul
      (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) |>.symm

/-- The whole `ZMod m`-indexed family is jointly injective, including both endpoints. -/
theorem injective_coordinateUnlinkExteriorPlanarNeckArcTranslate
    (m : ℕ) [NeZero m] :
    Injective (fun x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval ↦
      coordinateUnlinkExteriorPlanarNeckArcTranslate m x.1 x.2) := by
  rintro ⟨a, t⟩ ⟨b, s⟩ hab
  have hp := congrArg
    (fun z : CoordinateUnlinkExteriorPlanarFlower m ↦ z.1.1 ^ m) hab
  have hts : t = s := injective_coordinateUnlinkExteriorPlanarNeckBaseArc <| by
    simpa only [coordinateUnlinkExteriorPlanarNeckArcTranslate_pow] using hp
  subst s
  have hval := congrArg
    (fun z : CoordinateUnlinkExteriorPlanarFlower m ↦ z.1.1) hab
  have hroot :
      (((standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) =
        (((standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd b)).1 : ℂˣ) : ℂ) := by
    apply mul_right_cancel₀
      (coordinateUnlinkExteriorPlanarNeckPowerRoot_ne_zero (m := m) t)
    exact hval
  have hroots :
      standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a) =
        standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd b) := by
    apply Subtype.ext
    apply Units.ext
    exact hroot
  have hindex : a = b := Multiplicative.ofAdd.injective <|
    (standardRootsOfUnityZModMulEquiv m).injective hroots
  exact Prod.ext hindex rfl

set_option maxHeartbeats 400000 in
-- Expanding the two nested flower subtypes makes the continuity goal unusually large.
theorem continuous_coordinateUnlinkExteriorPlanarNeckArcTranslateFamily
    (m : ℕ) [NeZero m] :
    Continuous (fun x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval ↦
      coordinateUnlinkExteriorPlanarNeckArcTranslate m x.1 x.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  have hindex : Continuous (fun a : ZMod m ↦
      (((standardRootsOfUnityZModMulEquiv m
        (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ)) :=
    continuous_of_discreteTopology
  exact (hindex.comp continuous_fst).mul <|
    continuous_coordinateUnlinkExteriorPlanarNeckPowerRoot_comp (m := m) |>.comp
      continuous_snd

private theorem disjoint_range_prod_mk_of_injective
    {A B C : Type*} (f : A × B → C) (hf : Injective f)
    {a b : A} (hab : a ≠ b) :
    Disjoint (range (fun t ↦ f (a, t))) (range (fun t ↦ f (b, t))) := by
  refine Set.disjoint_left.2 ?_
  rintro z ⟨t, ht⟩ ⟨s, hs⟩
  have hp : (a, t) = (b, s) := hf (ht.trans hs.symm)
  exact hab (congrArg Prod.fst hp)

/-- Distinct deck labels have disjoint full arc ranges, including both endpoints. -/
theorem disjoint_range_coordinateUnlinkExteriorPlanarNeckArcTranslate
    (m : ℕ) [NeZero m] {a b : ZMod m} (hab : a ≠ b) :
    Disjoint (range (coordinateUnlinkExteriorPlanarNeckArcTranslate m a))
      (range (coordinateUnlinkExteriorPlanarNeckArcTranslate m b)) := by
  exact disjoint_range_prod_mk_of_injective
    (fun x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval ↦
      coordinateUnlinkExteriorPlanarNeckArcTranslate m x.1 x.2)
    (injective_coordinateUnlinkExteriorPlanarNeckArcTranslate m) hab

end SplittingSpheres
