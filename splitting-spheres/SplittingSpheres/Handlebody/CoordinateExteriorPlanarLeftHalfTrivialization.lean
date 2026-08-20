/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckAnnuli

/-!
# Sheet trivialization over the left polynomial half

The closed left polynomial base half lies strictly inside the disk `ball (-1) 1`.  Restricting
the selected root branch from `CoordinateExteriorPlanarNeckArc` therefore trivializes its full
degree-`m` inverse image as `ZMod m` copies of the base half.

The inverse sheet label is given explicitly by dividing a point by the selected root and using
the standard equivalence between `ZMod m` and the complex `m`th roots of unity.  Its continuity
is obtained from compactness and the Hausdorff property, not merely from discreteness of the
label space.  The chosen trivialization agrees literally with the existing translated neck arcs
on the vertical seam.

Everything here is point-set topology.  There is no orientation, cutting, separation, or
surface-classification assertion.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-! ## Restricting the selected root branch -/

/-- The entire closed left polynomial base half lies in the root disk used for the neck arcs. -/
theorem coordinateUnlinkExteriorPlanarBaseLeftHalf_mem_neckRootDomain
    (w : CoordinateUnlinkExteriorPlanarBaseLeftHalf) :
    (w : ℂ) ∈ coordinateUnlinkExteriorPlanarNeckRootDomain := by
  rw [coordinateUnlinkExteriorPlanarNeckRootDomain, mem_ball, Complex.dist_eq]
  have hw := mem_coordinateUnlinkExteriorPlanarBaseLeftHalfSet_iff w.1 |>.mp w.2
  have hsq : ‖(w : ℂ) + 1‖ ^ 2 ≤ 3 / 4 := by
    have houterSq : ‖(w : ℂ) + (1 / 2 : ℂ)‖ ^ 2 ≤ 1 / 2 := by
      rw [← sphereHandleRadius_sq]
      exact (sq_le_sq₀ (norm_nonneg _) sphereHandleRadius_pos.le).2 hw.1
    have hre : ((w : ℂ) + (1 / 2 : ℂ)).re ≤ 0 := by
      rw [Complex.add_re]
      norm_num
      linarith [hw.2.2.2]
    have hid : ‖(w : ℂ) + 1‖ ^ 2 =
        ‖((w : ℂ) + (1 / 2 : ℂ))‖ ^ 2 +
          ((w : ℂ) + (1 / 2 : ℂ)).re + 1 / 4 := by
      simpa only [show (w : ℂ) + 1 =
          ((w : ℂ) + (1 / 2 : ℂ)) + (1 / 2 : ℂ) by ring] using
        norm_add_half_sq ((w : ℂ) + (1 / 2 : ℂ))
    rw [hid]
    linarith
  have hnorm : ‖(w : ℂ) + 1‖ < 1 := by
    rw [← sq_lt_sq₀ (norm_nonneg _) zero_le_one]
    linarith
  simpa only [sub_neg_eq_add] using hnorm

theorem coordinateUnlinkExteriorPlanarBaseLeftHalf_ne_zero
    (w : CoordinateUnlinkExteriorPlanarBaseLeftHalf) :
    (w : ℂ) ≠ 0 := by
  intro hzero
  have hw := w.2.1.2.1
  rw [hzero, norm_zero] at hw
  norm_num at hw

/-- The neck root branch restricted to the complete left polynomial base half. -/
def coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot
    (m : ℕ) [NeZero m]
    (w : CoordinateUnlinkExteriorPlanarBaseLeftHalf) : ℂ :=
  coordinateUnlinkExteriorPlanarNeckPowerRoot m w.1

@[simp]
theorem coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot_pow
    (m : ℕ) [NeZero m]
    (w : CoordinateUnlinkExteriorPlanarBaseLeftHalf) :
    coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot m w ^ m = w.1 :=
  coordinateUnlinkExteriorPlanarNeckPowerRoot_pow m w.1

theorem coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot_ne_zero
    (m : ℕ) [NeZero m]
    (w : CoordinateUnlinkExteriorPlanarBaseLeftHalf) :
    coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot m w ≠ 0 := by
  intro hzero
  have hp := coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot_pow m w
  rw [hzero, zero_pow (NeZero.ne m)] at hp
  exact coordinateUnlinkExteriorPlanarBaseLeftHalf_ne_zero w hp.symm

theorem continuous_coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot m) :=
  (continuousOn_coordinateUnlinkExteriorPlanarNeckPowerRoot m).comp_continuous
    continuous_subtype_val
    coordinateUnlinkExteriorPlanarBaseLeftHalf_mem_neckRootDomain

/-! ## The forward sheet map -/

/-- The standard complex root-of-unity multiplier indexed by `ZMod m`. -/
def coordinateUnlinkExteriorPlanarLeftHalfRootMultiplier
    (m : ℕ) [NeZero m] (a : ZMod m) : ℂ :=
  (((standardRootsOfUnityZModMulEquiv m
      (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ)

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftHalfRootMultiplier_pow
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarLeftHalfRootMultiplier m a ^ m = 1 := by
  exact (mem_rootsOfUnity' m
    (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).1).mp
      (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).2

theorem coordinateUnlinkExteriorPlanarLeftHalfRootMultiplier_ne_zero
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarLeftHalfRootMultiplier m a ≠ 0 :=
  Units.ne_zero _

theorem continuous_coordinateUnlinkExteriorPlanarLeftHalfRootMultiplier
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarLeftHalfRootMultiplier m) :=
  continuous_of_discreteTopology

/-- The underlying complex coordinate of the left-half sheet trivialization. -/
def coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftHalf) : ℂ :=
  coordinateUnlinkExteriorPlanarLeftHalfRootMultiplier m x.1 *
    coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot m x.2

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw_pow
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftHalf) :
    coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw m x ^ m = x.2.1 := by
  rw [coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw, mul_pow,
    coordinateUnlinkExteriorPlanarLeftHalfRootMultiplier_pow, one_mul,
    coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot_pow]

theorem coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw_ne_zero
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftHalf) :
    coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw m x ≠ 0 :=
  mul_ne_zero
    (coordinateUnlinkExteriorPlanarLeftHalfRootMultiplier_ne_zero m x.1)
    (coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot_ne_zero m x.2)

/-- Multiply the selected root by the sheet label and bundle the result in the left flower half. -/
def coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftHalf) :
    CoordinateUnlinkExteriorPlanarFlowerLeftHalf m :=
  ⟨⟨⟨coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw m x,
      coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw_ne_zero m x⟩, by
      rw [mem_coordinateUnlinkExteriorPlanarFlowerSet_iff,
        coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw_pow]
      exact x.2.2.1⟩, by
    change (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw m x ^ m).re ≤
      -1 / 2
    rw [coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw_pow]
    exact x.2.2.2⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap_coe
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftHalf) :
    (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap m x).1.1.1 =
      coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw m x :=
  rfl

theorem continuous_coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap m) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact
    ((continuous_coordinateUnlinkExteriorPlanarLeftHalfRootMultiplier m).comp continuous_fst).mul
      ((continuous_coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot m).comp continuous_snd)

/-! ## Explicit algebraic inverse -/

/-- The polynomial power projection from the left flower half to the left base half. -/
def coordinateUnlinkExteriorPlanarFlowerLeftHalfPowerProjection
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarFlowerLeftHalf m) :
    CoordinateUnlinkExteriorPlanarBaseLeftHalf :=
  ⟨z.1.1.1 ^ m, by
    rw [mem_coordinateUnlinkExteriorPlanarBaseLeftHalfSet_iff]
    exact ⟨z.1.2.1, z.1.2.2.1, z.1.2.2.2, z.2⟩⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerLeftHalfPowerProjection_coe
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarFlowerLeftHalf m) :
    (coordinateUnlinkExteriorPlanarFlowerLeftHalfPowerProjection m z : ℂ) =
      z.1.1.1 ^ m :=
  rfl

theorem continuous_coordinateUnlinkExteriorPlanarFlowerLeftHalfPowerProjection
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarFlowerLeftHalfPowerProjection m) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp
    (continuous_subtype_val.comp continuous_subtype_val)).pow m

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerLeftHalfPowerProjection_map
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftHalf) :
    coordinateUnlinkExteriorPlanarFlowerLeftHalfPowerProjection m
        (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap m x) = x.2 := by
  apply Subtype.ext
  exact coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw_pow m x

/-- The quotient of a flower point by the selected root, bundled as an `m`th root of unity. -/
def coordinateUnlinkExteriorPlanarFlowerLeftHalfInverseRootUnit
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarFlowerLeftHalf m) : rootsOfUnity m ℂ := by
  let r := coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot m
    (coordinateUnlinkExteriorPlanarFlowerLeftHalfPowerProjection m z)
  have hr : r ≠ 0 := coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot_ne_zero m
    (coordinateUnlinkExteriorPlanarFlowerLeftHalfPowerProjection m z)
  let q : ℂˣ := Units.mk0 (z.1.1.1 / r) (div_ne_zero z.1.1.2 hr)
  have hq : (q : ℂ) ^ m = 1 := by
    change (z.1.1.1 / r) ^ m = 1
    rw [div_pow]
    have hrpow : r ^ m = z.1.1.1 ^ m :=
      coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot_pow m
        (coordinateUnlinkExteriorPlanarFlowerLeftHalfPowerProjection m z)
    rw [hrpow, div_self (pow_ne_zero m z.1.1.2)]
  exact ⟨q, (mem_rootsOfUnity' m q).mpr hq⟩

/-- The explicit sheet label recovered from a point of the left flower half. -/
def coordinateUnlinkExteriorPlanarFlowerLeftHalfInverseLabel
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarFlowerLeftHalf m) : ZMod m :=
  ((standardRootsOfUnityZModMulEquiv m).symm
    (coordinateUnlinkExteriorPlanarFlowerLeftHalfInverseRootUnit m z)).toAdd

/-- The explicit set-theoretic inverse of the left-half sheet map. -/
def coordinateUnlinkExteriorPlanarFlowerLeftHalfExplicitInverse
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarFlowerLeftHalf m) :
    ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftHalf :=
  (coordinateUnlinkExteriorPlanarFlowerLeftHalfInverseLabel m z,
    coordinateUnlinkExteriorPlanarFlowerLeftHalfPowerProjection m z)

theorem coordinateUnlinkExteriorPlanarLeftHalfRootMultiplier_inverseLabel
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarFlowerLeftHalf m) :
    coordinateUnlinkExteriorPlanarLeftHalfRootMultiplier m
        (coordinateUnlinkExteriorPlanarFlowerLeftHalfInverseLabel m z) =
      (((coordinateUnlinkExteriorPlanarFlowerLeftHalfInverseRootUnit m z).1 : ℂˣ) : ℂ) := by
  change ((((standardRootsOfUnityZModMulEquiv m
      (Multiplicative.ofAdd
        (coordinateUnlinkExteriorPlanarFlowerLeftHalfInverseLabel m z))).1 : ℂˣ) : ℂ)) = _
  have h := (standardRootsOfUnityZModMulEquiv m).apply_symm_apply
    (coordinateUnlinkExteriorPlanarFlowerLeftHalfInverseRootUnit m z)
  exact congrArg (fun u : rootsOfUnity m ℂ ↦ ((u.1 : ℂˣ) : ℂ)) h

theorem coordinateUnlinkExteriorPlanarFlowerLeftHalf_map_explicitInverse
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarFlowerLeftHalf m) :
    coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap m
        (coordinateUnlinkExteriorPlanarFlowerLeftHalfExplicitInverse m z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change coordinateUnlinkExteriorPlanarLeftHalfRootMultiplier m
        (coordinateUnlinkExteriorPlanarFlowerLeftHalfInverseLabel m z) *
      coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot m
        (coordinateUnlinkExteriorPlanarFlowerLeftHalfPowerProjection m z) = z.1.1.1
  rw [coordinateUnlinkExteriorPlanarLeftHalfRootMultiplier_inverseLabel]
  change (z.1.1.1 /
      coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot m
        (coordinateUnlinkExteriorPlanarFlowerLeftHalfPowerProjection m z)) *
      coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot m
        (coordinateUnlinkExteriorPlanarFlowerLeftHalfPowerProjection m z) = z.1.1.1
  exact div_mul_cancel₀ _ <|
    coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot_ne_zero m
      (coordinateUnlinkExteriorPlanarFlowerLeftHalfPowerProjection m z)

theorem injective_coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap m) := by
  rintro ⟨a, w⟩ ⟨b, v⟩ h
  have hraw :
      coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw m (a, w) =
        coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw m (b, v) := by
    simpa only [coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap_coe] using
      congrArg (fun z ↦ z.1.1.1) h
  have hwv : w = v := by
    apply Subtype.ext
    have hp := congrArg (fun z : ℂ ↦ z ^ m) hraw
    rw [coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw_pow,
      coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw_pow] at hp
    exact hp
  subst v
  have hmult :
      coordinateUnlinkExteriorPlanarLeftHalfRootMultiplier m a =
        coordinateUnlinkExteriorPlanarLeftHalfRootMultiplier m b := by
    apply mul_right_cancel₀
      (coordinateUnlinkExteriorPlanarBaseLeftHalfPowerRoot_ne_zero m w)
    exact hraw
  have hroots :
      standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a) =
        standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd b) := by
    apply Subtype.ext
    apply Units.ext
    exact hmult
  have hab : a = b := Multiplicative.ofAdd.injective <|
    (standardRootsOfUnityZModMulEquiv m).injective hroots
  exact Prod.ext hab rfl

theorem coordinateUnlinkExteriorPlanarFlowerLeftHalf_explicitInverse_map
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftHalf) :
    coordinateUnlinkExteriorPlanarFlowerLeftHalfExplicitInverse m
        (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap m x) = x := by
  apply injective_coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap m
  rw [coordinateUnlinkExteriorPlanarFlowerLeftHalf_map_explicitInverse]

theorem bijective_coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap
    (m : ℕ) [NeZero m] :
    Bijective (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap m) :=
  ⟨injective_coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap m,
    fun z ↦ ⟨coordinateUnlinkExteriorPlanarFlowerLeftHalfExplicitInverse m z,
      coordinateUnlinkExteriorPlanarFlowerLeftHalf_map_explicitInverse m z⟩⟩

/-! ## The homeomorphism and seam law -/

/-- The left flower half is the product of its polynomial base half with its `ZMod m` sheets. -/
def coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization
    (m : ℕ) [NeZero m] :
    ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftHalf ≃ₜ
      CoordinateUnlinkExteriorPlanarFlowerLeftHalf m := by
  let _ : CompactSpace CoordinateUnlinkExteriorPlanarBaseLeftHalf :=
    coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.compactSpace
  exact IsHomeomorph.homeomorph
    (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap m) <|
      (isHomeomorph_iff_continuous_bijective).mpr
        ⟨continuous_coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap m,
          bijective_coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap m⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization_apply
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftHalf) :
    coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m x =
      coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap m x :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization_symm_apply
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarFlowerLeftHalf m) :
    (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m).symm z =
      coordinateUnlinkExteriorPlanarFlowerLeftHalfExplicitInverse m z := by
  apply (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m).injective
  rw [(coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m).apply_symm_apply,
    coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization_apply,
    coordinateUnlinkExteriorPlanarFlowerLeftHalf_map_explicitInverse]

theorem continuous_coordinateUnlinkExteriorPlanarFlowerLeftHalfInverseLabel
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarFlowerLeftHalfInverseLabel m) := by
  have h := (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m).symm.continuous.fst
  simpa only [coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization_symm_apply,
    coordinateUnlinkExteriorPlanarFlowerLeftHalfExplicitInverse] using h

/-- The vertical base arc, regarded as a map into the closed left polynomial base half. -/
def coordinateUnlinkExteriorPlanarNeckBaseArcToBaseLeftHalf
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    CoordinateUnlinkExteriorPlanarBaseLeftHalf :=
  ⟨coordinateUnlinkExteriorPlanarNeckBaseArc t, by
    rw [mem_coordinateUnlinkExteriorPlanarBaseLeftHalfSet_iff]
    exact ⟨norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_half_le t,
      le_trans (by norm_num) (norm_coordinateUnlinkExteriorPlanarNeckBaseArc_ge_half t),
      le_trans (by norm_num)
        (norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_one_ge_half t), by simp⟩⟩

/-- On the vertical seam, the sheet trivialization is literally the existing translated arc. -/
theorem coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization_neckArc
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m
        (a, coordinateUnlinkExteriorPlanarNeckBaseArcToBaseLeftHalf t) =
      coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m (a, t) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization_apply,
    coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap_coe,
    coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw,
    coordinateUnlinkExteriorPlanarNeckArcToLeftHalf_val,
    coordinateUnlinkExteriorPlanarNeckArcFamily_apply,
    coordinateUnlinkExteriorPlanarNeckArcTranslate_val]
  rfl

end SplittingSpheres
