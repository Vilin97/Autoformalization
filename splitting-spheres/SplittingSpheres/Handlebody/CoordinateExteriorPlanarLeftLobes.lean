/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarInnerBoundaryLift
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarRightFilling

/-!
# The closed left lobes of the planar power flower

The closed character disk `closedBall (-1) (1 / 8)` lies inside the disk on which the selected
left-character `m`th-root branch is continuous.  That branch embeds one closed disk in the
power-coordinate plane.  Its `ZMod m` deck translates are pairwise disjoint and exhaust the
full inverse image `{z | ‖z ^ m + 1‖ ≤ 1 / 8}`.

The boundary maps below agree literally with the previously constructed lifted left inner
circles after applying the planar-flower homeomorphism.  Everything is point-set topology; no
orientation or surface-classification assertion is made.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-! ## The selected root disk -/

/-- The closed disk of radius `1/8` about the left character center `-1`. -/
abbrev CoordinateUnlinkExteriorPlanarLeftCharacterDisk : Type :=
  ↑(closedBall (-1 : ℂ) (1 / 8 : ℝ))

/-- Its literal boundary circle. -/
abbrev CoordinateUnlinkExteriorPlanarLeftCharacterBoundary : Type :=
  ↑(sphere (-1 : ℂ) (1 / 8 : ℝ))

theorem coordinateUnlinkExteriorPlanarLeftCharacterDisk_mem_leftCharacterBall
    (w : CoordinateUnlinkExteriorPlanarLeftCharacterDisk) :
    w.1 ∈ unlinkLeftCharacterBall := by
  change dist w.1 (-1 : ℂ) < 1 / 4
  have hw : dist w.1 (-1 : ℂ) ≤ 1 / 8 := by
    simpa only [mem_closedBall] using w.2
  linarith

theorem coordinateUnlinkExteriorPlanarLeftCharacterDisk_ne_zero
    (w : CoordinateUnlinkExteriorPlanarLeftCharacterDisk) :
    w.1 ≠ 0 := by
  intro hw
  have hdist : dist w.1 (-1 : ℂ) ≤ 1 / 8 := by
    simpa only [mem_closedBall] using w.2
  rw [hw] at hdist
  norm_num [Complex.dist_eq] at hdist

/-- The selected root branch, restricted to the closed left character disk. -/
def coordinateUnlinkExteriorPlanarLeftRootDiskMap
    (m : ℕ) [NeZero m]
    (w : CoordinateUnlinkExteriorPlanarLeftCharacterDisk) : ℂ :=
  unlinkLeftCharacterPowerRoot m w.1

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftRootDiskMap_pow
    (m : ℕ) [NeZero m]
    (w : CoordinateUnlinkExteriorPlanarLeftCharacterDisk) :
    coordinateUnlinkExteriorPlanarLeftRootDiskMap m w ^ m = w.1 :=
  unlinkLeftCharacterPowerRoot_pow m w.1

theorem coordinateUnlinkExteriorPlanarLeftRootDiskMap_ne_zero
    (m : ℕ) [NeZero m]
    (w : CoordinateUnlinkExteriorPlanarLeftCharacterDisk) :
    coordinateUnlinkExteriorPlanarLeftRootDiskMap m w ≠ 0 := by
  intro hzero
  have hp := coordinateUnlinkExteriorPlanarLeftRootDiskMap_pow m w
  rw [hzero, zero_pow (NeZero.ne m)] at hp
  exact coordinateUnlinkExteriorPlanarLeftCharacterDisk_ne_zero w hp.symm

theorem continuous_coordinateUnlinkExteriorPlanarLeftRootDiskMap
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarLeftRootDiskMap m) := by
  exact (continuousOn_unlinkLeftCharacterPowerRoot m).comp_continuous
    continuous_subtype_val
    coordinateUnlinkExteriorPlanarLeftCharacterDisk_mem_leftCharacterBall

theorem injective_coordinateUnlinkExteriorPlanarLeftRootDiskMap
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarLeftRootDiskMap m) := by
  intro w v hwv
  apply Subtype.ext
  rw [← coordinateUnlinkExteriorPlanarLeftRootDiskMap_pow m w,
    ← coordinateUnlinkExteriorPlanarLeftRootDiskMap_pow m v, hwv]

theorem isEmbedding_coordinateUnlinkExteriorPlanarLeftRootDiskMap
    (m : ℕ) [NeZero m] :
    IsEmbedding (coordinateUnlinkExteriorPlanarLeftRootDiskMap m) :=
  (continuous_coordinateUnlinkExteriorPlanarLeftRootDiskMap m).isClosedEmbedding
    (injective_coordinateUnlinkExteriorPlanarLeftRootDiskMap m) |>.isEmbedding

/-! ## All deck-translated lobes -/

/-- The closed left lobe indexed by `a : ZMod m`. -/
def coordinateUnlinkExteriorPlanarLeftLobeMap
    (m : ℕ) [NeZero m] (a : ZMod m)
    (w : CoordinateUnlinkExteriorPlanarLeftCharacterDisk) : ℂ :=
  (((standardRootsOfUnityZModMulEquiv m
      (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) *
    coordinateUnlinkExteriorPlanarLeftRootDiskMap m w

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLobeMap_pow
    (m : ℕ) [NeZero m] (a : ZMod m)
    (w : CoordinateUnlinkExteriorPlanarLeftCharacterDisk) :
    coordinateUnlinkExteriorPlanarLeftLobeMap m a w ^ m = w.1 := by
  rw [coordinateUnlinkExteriorPlanarLeftLobeMap, mul_pow,
    (mem_rootsOfUnity' m
      (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).1).mp
        (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).2,
    one_mul, coordinateUnlinkExteriorPlanarLeftRootDiskMap_pow]

theorem coordinateUnlinkExteriorPlanarLeftLobeMap_ne_zero
    (m : ℕ) [NeZero m] (a : ZMod m)
    (w : CoordinateUnlinkExteriorPlanarLeftCharacterDisk) :
    coordinateUnlinkExteriorPlanarLeftLobeMap m a w ≠ 0 :=
  mul_ne_zero (Units.ne_zero _)
    (coordinateUnlinkExteriorPlanarLeftRootDiskMap_ne_zero m w)

theorem continuous_coordinateUnlinkExteriorPlanarLeftLobeMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Continuous (coordinateUnlinkExteriorPlanarLeftLobeMap m a) :=
  continuous_const.mul
    (continuous_coordinateUnlinkExteriorPlanarLeftRootDiskMap m)

theorem injective_coordinateUnlinkExteriorPlanarLeftLobeMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Injective (coordinateUnlinkExteriorPlanarLeftLobeMap m a) := by
  intro w v hwv
  apply Subtype.ext
  have hp := congrArg (fun z : ℂ ↦ z ^ m) hwv
  simpa only [coordinateUnlinkExteriorPlanarLeftLobeMap_pow] using hp

theorem isEmbedding_coordinateUnlinkExteriorPlanarLeftLobeMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsEmbedding (coordinateUnlinkExteriorPlanarLeftLobeMap m a) :=
  (continuous_coordinateUnlinkExteriorPlanarLeftLobeMap m a).isClosedEmbedding
    (injective_coordinateUnlinkExteriorPlanarLeftLobeMap m a) |>.isEmbedding

/-- Distinct deck indices give disjoint closed lobe images. -/
theorem disjoint_range_coordinateUnlinkExteriorPlanarLeftLobeMap
    (m : ℕ) [NeZero m] {a b : ZMod m} (hab : a ≠ b) :
    Disjoint
      (Set.range (coordinateUnlinkExteriorPlanarLeftLobeMap m a))
      (Set.range (coordinateUnlinkExteriorPlanarLeftLobeMap m b)) := by
  rw [Set.disjoint_left]
  rintro z ⟨w, rfl⟩ ⟨v, hvw⟩
  have hp := congrArg (fun q : ℂ ↦ q ^ m) hvw
  have hwv : w = v := by
    apply Subtype.ext
    simpa only [coordinateUnlinkExteriorPlanarLeftLobeMap_pow] using hp.symm
  subst v
  have hroot :
      (((standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) =
        (((standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd b)).1 : ℂˣ) : ℂ) := by
    apply mul_right_cancel₀
      (coordinateUnlinkExteriorPlanarLeftRootDiskMap_ne_zero m w)
    exact hvw.symm
  have hroots :
      standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a) =
        standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd b) := by
    apply Subtype.ext
    apply Units.ext
    exact hroot
  have hab' : Multiplicative.ofAdd a = Multiplicative.ofAdd b :=
    (standardRootsOfUnityZModMulEquiv m).injective hroots
  exact hab (Multiplicative.ofAdd.injective hab')

/-- The full inverse image of the closed left character disk under `z ↦ z ^ m`. -/
def coordinateUnlinkExteriorPlanarLeftLobesSet (m : ℕ) : Set ℂ :=
  {z | ‖z ^ m + 1‖ ≤ (1 / 8 : ℝ)}

theorem coordinateUnlinkExteriorPlanarLeftLobesSet_ne_zero
    (m : ℕ) [NeZero m] {z : ℂ}
    (hz : z ∈ coordinateUnlinkExteriorPlanarLeftLobesSet m) :
    z ≠ 0 := by
  intro hzero
  change ‖z ^ m + 1‖ ≤ (1 / 8 : ℝ) at hz
  rw [hzero, zero_pow (NeZero.ne m), zero_add, norm_one] at hz
  norm_num at hz

/-- The translated root disks exhaust the whole left polynomial inverse image. -/
theorem iUnion_range_coordinateUnlinkExteriorPlanarLeftLobeMap
    (m : ℕ) [NeZero m] :
    (⋃ a : ZMod m, Set.range (coordinateUnlinkExteriorPlanarLeftLobeMap m a)) =
      coordinateUnlinkExteriorPlanarLeftLobesSet m := by
  ext z
  constructor
  · intro hz
    simp only [Set.mem_iUnion, Set.mem_range] at hz
    rcases hz with ⟨a, w, rfl⟩
    change ‖coordinateUnlinkExteriorPlanarLeftLobeMap m a w ^ m + 1‖ ≤
      (1 / 8 : ℝ)
    rw [coordinateUnlinkExteriorPlanarLeftLobeMap_pow]
    have hw : dist w.1 (-1 : ℂ) ≤ 1 / 8 := by
      simpa only [mem_closedBall] using w.2
    simpa [Complex.dist_eq] using hw
  · intro hz
    have hz0 : z ≠ 0 :=
      coordinateUnlinkExteriorPlanarLeftLobesSet_ne_zero m hz
    change ‖z ^ m + 1‖ ≤ (1 / 8 : ℝ) at hz
    let w : CoordinateUnlinkExteriorPlanarLeftCharacterDisk :=
      ⟨z ^ m, by
        change dist (z ^ m) (-1 : ℂ) ≤ 1 / 8
        simpa [Complex.dist_eq] using hz⟩
    let r : ℂ := coordinateUnlinkExteriorPlanarLeftRootDiskMap m w
    have hr : r ≠ 0 :=
      coordinateUnlinkExteriorPlanarLeftRootDiskMap_ne_zero m w
    have hrpow : r ^ m = z ^ m := by
      change coordinateUnlinkExteriorPlanarLeftRootDiskMap m w ^ m = z ^ m
      exact coordinateUnlinkExteriorPlanarLeftRootDiskMap_pow m w
    let q : ℂˣ := Units.mk0 (z / r) (div_ne_zero hz0 hr)
    have hq : (q : ℂ) ^ m = 1 := by
      change (z / r) ^ m = 1
      rw [div_pow, hrpow, div_self (pow_ne_zero m hz0)]
    let u : rootsOfUnity m ℂ :=
      ⟨q, (mem_rootsOfUnity' m q).mpr hq⟩
    let b : Multiplicative (ZMod m) :=
      (standardRootsOfUnityZModMulEquiv m).symm u
    simp only [Set.mem_iUnion, Set.mem_range]
    refine ⟨b.toAdd, w, ?_⟩
    change (((standardRootsOfUnityZModMulEquiv m b).1 : ℂˣ) : ℂ) * r = z
    rw [(standardRootsOfUnityZModMulEquiv m).apply_symm_apply]
    change (z / r) * r = z
    exact div_mul_cancel₀ z hr

/-! ## Literal boundary circles -/

/-- Include the literal character boundary in its closed disk. -/
def coordinateUnlinkExteriorPlanarLeftCharacterBoundaryToDisk :
    C(CoordinateUnlinkExteriorPlanarLeftCharacterBoundary,
      CoordinateUnlinkExteriorPlanarLeftCharacterDisk) where
  toFun w := ⟨w.1, sphere_subset_closedBall w.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftCharacterBoundaryToDisk_coe
    (w : CoordinateUnlinkExteriorPlanarLeftCharacterBoundary) :
    (coordinateUnlinkExteriorPlanarLeftCharacterBoundaryToDisk w : ℂ) = w.1 :=
  rfl

/-- The standard unit-circle parameterization of the literal left character boundary. -/
def coordinateUnlinkExteriorPlanarLeftCharacterBoundaryCircle
    (u : Sphere 1) : CoordinateUnlinkExteriorPlanarLeftCharacterBoundary :=
  ⟨(-1 : ℂ) + (1 / 8 : ℂ) * unlinkUnitCircleComplex u, by
    rw [mem_sphere, Complex.dist_eq]
    have hsub : (-1 : ℂ) + (1 / 8 : ℂ) * unlinkUnitCircleComplex u - (-1) =
        (1 / 8 : ℂ) * unlinkUnitCircleComplex u := by ring
    rw [hsub, norm_mul, norm_unlinkUnitCircleComplex]
    norm_num⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftCharacterBoundaryCircle_coe
    (u : Sphere 1) :
    (coordinateUnlinkExteriorPlanarLeftCharacterBoundaryCircle u : ℂ) =
      (-1 : ℂ) + (1 / 8 : ℂ) * unlinkUnitCircleComplex u :=
  rfl

theorem continuous_coordinateUnlinkExteriorPlanarLeftCharacterBoundaryCircle :
    Continuous coordinateUnlinkExteriorPlanarLeftCharacterBoundaryCircle := by
  apply Continuous.subtype_mk
  exact continuous_const.add (continuous_const.mul continuous_unlinkUnitCircleComplex)

theorem injective_coordinateUnlinkExteriorPlanarLeftCharacterBoundaryCircle :
    Injective coordinateUnlinkExteriorPlanarLeftCharacterBoundaryCircle := by
  intro u v huv
  apply injective_unlinkUnitCircleComplex
  have h := congrArg
    (fun w : CoordinateUnlinkExteriorPlanarLeftCharacterBoundary ↦ w.1) huv
  have hmul : (1 / 8 : ℂ) * unlinkUnitCircleComplex u =
      (1 / 8 : ℂ) * unlinkUnitCircleComplex v := add_left_cancel h
  exact mul_left_cancel₀ (by norm_num : (1 / 8 : ℂ) ≠ 0) hmul

/-- The boundary of lobe `a`, parameterized by the literal character circle. -/
def coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap
    (m : ℕ) [NeZero m] (a : ZMod m)
    (w : CoordinateUnlinkExteriorPlanarLeftCharacterBoundary) : ℂ :=
  coordinateUnlinkExteriorPlanarLeftLobeMap m a
    (coordinateUnlinkExteriorPlanarLeftCharacterBoundaryToDisk w)

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap_pow
    (m : ℕ) [NeZero m] (a : ZMod m)
    (w : CoordinateUnlinkExteriorPlanarLeftCharacterBoundary) :
    coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap m a w ^ m = w.1 :=
  coordinateUnlinkExteriorPlanarLeftLobeMap_pow m a _

theorem continuous_coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Continuous (coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap m a) :=
  (continuous_coordinateUnlinkExteriorPlanarLeftLobeMap m a).comp
    coordinateUnlinkExteriorPlanarLeftCharacterBoundaryToDisk.continuous

theorem injective_coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Injective (coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap m a) := by
  intro w v hwv
  apply Subtype.ext
  have hp := congrArg (fun z : ℂ ↦ z ^ m) hwv
  simpa only [coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap_pow] using hp

theorem isEmbedding_coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsEmbedding (coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap m a) :=
  (continuous_coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap m a).isClosedEmbedding
    (injective_coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap m a) |>.isEmbedding

/-- The same boundary, parameterized by the project's standard `Sphere 1`. -/
def coordinateUnlinkExteriorPlanarLeftLobeBoundaryCircle
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1) : ℂ :=
  coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap m a
    (coordinateUnlinkExteriorPlanarLeftCharacterBoundaryCircle u)

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLobeBoundaryCircle_pow
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1) :
    coordinateUnlinkExteriorPlanarLeftLobeBoundaryCircle m a u ^ m =
      (-1 : ℂ) + (1 / 8 : ℂ) * unlinkUnitCircleComplex u :=
  coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap_pow m a _

theorem continuous_coordinateUnlinkExteriorPlanarLeftLobeBoundaryCircle
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Continuous (coordinateUnlinkExteriorPlanarLeftLobeBoundaryCircle m a) :=
  (continuous_coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap m a).comp
    continuous_coordinateUnlinkExteriorPlanarLeftCharacterBoundaryCircle

/-! ## Compatibility with the old planar flower -/

/-- Forget all flower inequalities and retain its displayed complex coordinate. -/
def coordinateUnlinkExteriorPlanarFlowerToComplex (m : ℕ) :
    C(CoordinateUnlinkExteriorPlanarFlower m, ℂ) where
  toFun z := z.1.1
  continuous_toFun := continuous_subtype_val.comp continuous_subtype_val

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerToComplex_apply
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlower m) :
    coordinateUnlinkExteriorPlanarFlowerToComplex m z = z.1.1 :=
  rfl

/-- Exact power-coordinate compatibility with the already constructed lifted left inner
boundary. -/
theorem coordinateUnlinkExteriorPlanarFlowerHomeomorph_leftInnerLiftTranslate_val
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1) :
    coordinateUnlinkExteriorPlanarFlowerToComplex m
        (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m
          (coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate m a u)) =
      coordinateUnlinkExteriorPlanarLeftLobeBoundaryCircle m a u := by
  change (((standardRootsOfUnityZModMulEquiv m
        (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) *
      (coordinateUnlinkExteriorPlanarLeftInnerLiftPowerCoordinate m u : ℂ) =
    (((standardRootsOfUnityZModMulEquiv m
        (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) *
      unlinkLeftCharacterPowerRoot m
        ((-1 : ℂ) + (1 / 8 : ℂ) * unlinkUnitCircleComplex u)
  congr 1
  change unlinkLeftCharacterPowerRoot m
      (coordinateUnlinkExteriorPuncturedNormalDiskCharacter
        (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0 u) : ℂ) = _
  rw [coordinateUnlinkExteriorPuncturedNormalDiskCharacter_innerBoundary_zero]

/-! ## Exact boundary intersection with the old flower -/

@[simp]
theorem norm_add_one_coordinateUnlinkExteriorPlanarLeftCharacterBoundary
    (w : CoordinateUnlinkExteriorPlanarLeftCharacterBoundary) :
    ‖w.1 + 1‖ = (1 / 8 : ℝ) := by
  have hw : dist w.1 (-1 : ℂ) = 1 / 8 := by
    simpa only [mem_sphere] using w.2
  simpa [Complex.dist_eq] using hw

theorem oneEighth_le_norm_coordinateUnlinkExteriorPlanarLeftCharacterBoundary
    (w : CoordinateUnlinkExteriorPlanarLeftCharacterBoundary) :
    (1 / 8 : ℝ) ≤ ‖w.1‖ := by
  have htri := dist_triangle (0 : ℂ) w.1 (-1 : ℂ)
  have hdist : dist w.1 (-1 : ℂ) = 1 / 8 := by
    simpa only [mem_sphere] using w.2
  have h : (1 : ℝ) ≤ ‖w.1‖ + 1 / 8 := by
    rw [hdist] at htri
    simpa [Complex.dist_eq] using htri
  linarith

theorem norm_add_half_coordinateUnlinkExteriorPlanarLeftCharacterBoundary_le
    (w : CoordinateUnlinkExteriorPlanarLeftCharacterBoundary) :
    ‖w.1 + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius := by
  calc
    ‖w.1 + (1 / 2 : ℂ)‖ =
        ‖(w.1 + 1) + (-1 / 2 : ℂ)‖ := by
      congr 1
      ring
    _ ≤ ‖w.1 + 1‖ + ‖(-1 / 2 : ℂ)‖ := norm_add_le _ _
    _ = 5 / 8 := by
      rw [norm_add_one_coordinateUnlinkExteriorPlanarLeftCharacterBoundary]
      norm_num
    _ ≤ sphereHandleRadius := fiveEighth_lt_sphereHandleRadius.le

/-- A lobe boundary, bundled in the old planar flower by the three exact inequalities. -/
def coordinateUnlinkExteriorPlanarLeftLobeBoundaryToPlanarFlower
    (m : ℕ) [NeZero m] (a : ZMod m)
    (w : CoordinateUnlinkExteriorPlanarLeftCharacterBoundary) :
    CoordinateUnlinkExteriorPlanarFlower m := by
  let z : ℂ := coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap m a w
  refine ⟨⟨z, ?_⟩, ?_, ?_, ?_⟩
  · exact coordinateUnlinkExteriorPlanarLeftLobeMap_ne_zero m a
      (coordinateUnlinkExteriorPlanarLeftCharacterBoundaryToDisk w)
  · change ‖z ^ m + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius
    rw [show z ^ m = w.1 by
      exact coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap_pow m a w]
    exact norm_add_half_coordinateUnlinkExteriorPlanarLeftCharacterBoundary_le w
  · change (1 / 8 : ℝ) ≤ ‖z ^ m‖
    rw [show z ^ m = w.1 by
      exact coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap_pow m a w]
    exact oneEighth_le_norm_coordinateUnlinkExteriorPlanarLeftCharacterBoundary w
  · change (1 / 8 : ℝ) ≤ ‖z ^ m + 1‖
    rw [show z ^ m = w.1 by
      exact coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap_pow m a w,
      norm_add_one_coordinateUnlinkExteriorPlanarLeftCharacterBoundary]

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLobeBoundaryToPlanarFlower_val
    (m : ℕ) [NeZero m] (a : ZMod m)
    (w : CoordinateUnlinkExteriorPlanarLeftCharacterBoundary) :
    (coordinateUnlinkExteriorPlanarLeftLobeBoundaryToPlanarFlower m a w).1.1 =
      coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap m a w :=
  rfl

theorem continuous_coordinateUnlinkExteriorPlanarLeftLobeBoundaryToPlanarFlower
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Continuous (coordinateUnlinkExteriorPlanarLeftLobeBoundaryToPlanarFlower m a) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap m a

/-- Structure-level form of compatibility with the lifted left inner boundary. -/
theorem coordinateUnlinkExteriorPlanarLeftLobeBoundaryCircle_eq_innerLiftTranslate
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1) :
    coordinateUnlinkExteriorPlanarLeftLobeBoundaryToPlanarFlower m a
        (coordinateUnlinkExteriorPlanarLeftCharacterBoundaryCircle u) =
      coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m
        (coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate m a u) := by
  apply Subtype.ext
  apply Subtype.ext
  exact (coordinateUnlinkExteriorPlanarFlowerHomeomorph_leftInnerLiftTranslate_val
    m a u).symm

/-- Each individual closed lobe meets the old flower in exactly its displayed boundary circle. -/
theorem range_coordinateUnlinkExteriorPlanarLeftLobeMap_inter_planarFlower
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Set.range (coordinateUnlinkExteriorPlanarLeftLobeMap m a) ∩
        Set.range (coordinateUnlinkExteriorPlanarFlowerToComplex m) =
      Set.range (coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap m a) := by
  ext z
  constructor
  · rintro ⟨⟨w, rfl⟩, ⟨v, hv⟩⟩
    have hupper : ‖w.1 + 1‖ ≤ (1 / 8 : ℝ) := by
      have hw : dist w.1 (-1 : ℂ) ≤ 1 / 8 := by
        simpa only [mem_closedBall] using w.2
      simpa [Complex.dist_eq] using hw
    have hlower : (1 / 8 : ℝ) ≤ ‖w.1 + 1‖ := by
      have hvleft := v.2.2.2
      change (1 / 8 : ℝ) ≤ ‖v.1.1 ^ m + 1‖ at hvleft
      change v.1.1 = coordinateUnlinkExteriorPlanarLeftLobeMap m a w at hv
      rw [hv, coordinateUnlinkExteriorPlanarLeftLobeMap_pow] at hvleft
      exact hvleft
    have heq : ‖w.1 + 1‖ = (1 / 8 : ℝ) := le_antisymm hupper hlower
    let b : CoordinateUnlinkExteriorPlanarLeftCharacterBoundary :=
      ⟨w.1, by
        rw [mem_sphere, Complex.dist_eq]
        simpa using heq⟩
    refine ⟨b, ?_⟩
    apply congrArg (coordinateUnlinkExteriorPlanarLeftLobeMap m a)
    apply Subtype.ext
    rfl
  · rintro ⟨w, rfl⟩
    constructor
    · exact ⟨coordinateUnlinkExteriorPlanarLeftCharacterBoundaryToDisk w, rfl⟩
    · exact ⟨coordinateUnlinkExteriorPlanarLeftLobeBoundaryToPlanarFlower m a w, rfl⟩

/-- Globally, the union of all closed lobes meets the old flower in the union of their pairwise
disjoint boundary circles. -/
theorem iUnion_range_coordinateUnlinkExteriorPlanarLeftLobeMap_inter_planarFlower
    (m : ℕ) [NeZero m] :
    (⋃ a : ZMod m, Set.range (coordinateUnlinkExteriorPlanarLeftLobeMap m a)) ∩
        Set.range (coordinateUnlinkExteriorPlanarFlowerToComplex m) =
      ⋃ a : ZMod m,
        Set.range (coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap m a) := by
  ext z
  constructor
  · rintro ⟨hz, hflower⟩
    simp only [Set.mem_iUnion] at hz ⊢
    obtain ⟨a, ha⟩ := hz
    refine ⟨a, ?_⟩
    rw [← range_coordinateUnlinkExteriorPlanarLeftLobeMap_inter_planarFlower m a]
    exact ⟨ha, hflower⟩
  · intro hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨a, ha⟩ := hz
    have hinter : z ∈ Set.range (coordinateUnlinkExteriorPlanarLeftLobeMap m a) ∩
        Set.range (coordinateUnlinkExteriorPlanarFlowerToComplex m) := by
      rw [range_coordinateUnlinkExteriorPlanarLeftLobeMap_inter_planarFlower m a]
      exact ha
    refine ⟨?_, hinter.2⟩
    simp only [Set.mem_iUnion]
    exact ⟨a, hinter.1⟩

end SplittingSpheres
