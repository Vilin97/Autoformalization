/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutHomeomorph
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckArc

/-!
# Cutting the planar flower into its two polynomial half-spaces

The vertical base arc is the common boundary of the two closed conditions

`re (z ^ m) ≤ -1/2` and `-1/2 ≤ re (z ^ m)`.

This file proves that its `ZMod m`-indexed lifts exhaust that common boundary and recognizes the
whole planar flower as the topological pushout of the two closed halves along the lifted arcs.

The halves are not yet identified with annuli here.  Consequently this file makes no surface
classification, separation-after-cutting, partial-spin, or connected-sum claim.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-! ## Closed polynomial halves -/

/-- The part of the flower over the closed left half of the polynomial outer disk. -/
def coordinateUnlinkExteriorPlanarFlowerLeftHalfSet
    (m : ℕ) : Set (CoordinateUnlinkExteriorPlanarFlower m) :=
  {z | (z.1.1 ^ m).re ≤ -1 / 2}

/-- The part of the flower over the closed right half of the polynomial outer disk. -/
def coordinateUnlinkExteriorPlanarFlowerRightHalfSet
    (m : ℕ) : Set (CoordinateUnlinkExteriorPlanarFlower m) :=
  {z | -1 / 2 ≤ (z.1.1 ^ m).re}

abbrev CoordinateUnlinkExteriorPlanarFlowerLeftHalf (m : ℕ) : Type :=
  ↑(coordinateUnlinkExteriorPlanarFlowerLeftHalfSet m)

abbrev CoordinateUnlinkExteriorPlanarFlowerRightHalf (m : ℕ) : Type :=
  ↑(coordinateUnlinkExteriorPlanarFlowerRightHalfSet m)

@[simp]
theorem mem_coordinateUnlinkExteriorPlanarFlowerLeftHalfSet_iff
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlower m) :
    z ∈ coordinateUnlinkExteriorPlanarFlowerLeftHalfSet m ↔
      (z.1.1 ^ m).re ≤ -1 / 2 :=
  Iff.rfl

@[simp]
theorem mem_coordinateUnlinkExteriorPlanarFlowerRightHalfSet_iff
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlower m) :
    z ∈ coordinateUnlinkExteriorPlanarFlowerRightHalfSet m ↔
      -1 / 2 ≤ (z.1.1 ^ m).re :=
  Iff.rfl

theorem isClosed_coordinateUnlinkExteriorPlanarFlowerLeftHalfSet (m : ℕ) :
    IsClosed (coordinateUnlinkExteriorPlanarFlowerLeftHalfSet m) := by
  exact isClosed_le (by fun_prop) continuous_const

theorem isClosed_coordinateUnlinkExteriorPlanarFlowerRightHalfSet (m : ℕ) :
    IsClosed (coordinateUnlinkExteriorPlanarFlowerRightHalfSet m) := by
  exact isClosed_le continuous_const (by fun_prop)

noncomputable instance compactSpace_coordinateUnlinkExteriorPlanarFlowerLeftHalf
    (m : ℕ) [NeZero m] :
    CompactSpace (CoordinateUnlinkExteriorPlanarFlowerLeftHalf m) := by
  let _ : CompactSpace (CoordinateUnlinkExteriorPlanarFlower m) :=
    compactSpace_coordinateUnlinkExteriorPlanarFlower m
  exact isCompact_iff_compactSpace.mp
    (isClosed_coordinateUnlinkExteriorPlanarFlowerLeftHalfSet m).isCompact

noncomputable instance compactSpace_coordinateUnlinkExteriorPlanarFlowerRightHalf
    (m : ℕ) [NeZero m] :
    CompactSpace (CoordinateUnlinkExteriorPlanarFlowerRightHalf m) := by
  let _ : CompactSpace (CoordinateUnlinkExteriorPlanarFlower m) :=
    compactSpace_coordinateUnlinkExteriorPlanarFlower m
  exact isCompact_iff_compactSpace.mp
    (isClosed_coordinateUnlinkExteriorPlanarFlowerRightHalfSet m).isCompact

/-- Inclusion of the left closed half in the whole flower. -/
def coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion (m : ℕ) :
    C(CoordinateUnlinkExteriorPlanarFlowerLeftHalf m,
      CoordinateUnlinkExteriorPlanarFlower m) where
  toFun z := z.1
  continuous_toFun := continuous_subtype_val

/-- Inclusion of the right closed half in the whole flower. -/
def coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion (m : ℕ) :
    C(CoordinateUnlinkExteriorPlanarFlowerRightHalf m,
      CoordinateUnlinkExteriorPlanarFlower m) where
  toFun z := z.1
  continuous_toFun := continuous_subtype_val

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion_apply
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlowerLeftHalf m) :
    coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion m z = z.1 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion_apply
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlowerRightHalf m) :
    coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion m z = z.1 :=
  rfl

/-! ## The exact common boundary -/

/-- The jointly parameterized family of all lifted vertical arcs. -/
def coordinateUnlinkExteriorPlanarNeckArcFamily
    (m : ℕ) [NeZero m] :
    C(ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval,
      CoordinateUnlinkExteriorPlanarFlower m) where
  toFun x := coordinateUnlinkExteriorPlanarNeckArcTranslate m x.1 x.2
  continuous_toFun :=
    continuous_coordinateUnlinkExteriorPlanarNeckArcTranslateFamily m

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckArcFamily_apply
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarNeckArcFamily m x =
      coordinateUnlinkExteriorPlanarNeckArcTranslate m x.1 x.2 :=
  rfl

theorem coordinateUnlinkExteriorPlanarNeckArcFamily_mem_leftHalf
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarNeckArcFamily m x ∈
      coordinateUnlinkExteriorPlanarFlowerLeftHalfSet m := by
  change ((coordinateUnlinkExteriorPlanarNeckArcTranslate m x.1 x.2).1.1 ^ m).re ≤
      -1 / 2
  rw [coordinateUnlinkExteriorPlanarNeckArcTranslate_pow,
    coordinateUnlinkExteriorPlanarNeckBaseArc_re]

theorem coordinateUnlinkExteriorPlanarNeckArcFamily_mem_rightHalf
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarNeckArcFamily m x ∈
      coordinateUnlinkExteriorPlanarFlowerRightHalfSet m := by
  change -1 / 2 ≤
    ((coordinateUnlinkExteriorPlanarNeckArcTranslate m x.1 x.2).1.1 ^ m).re
  rw [coordinateUnlinkExteriorPlanarNeckArcTranslate_pow,
    coordinateUnlinkExteriorPlanarNeckBaseArc_re]

/-- Regard every lifted arc as a map into the left half. -/
def coordinateUnlinkExteriorPlanarNeckArcToLeftHalf
    (m : ℕ) [NeZero m] :
    C(ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval,
      CoordinateUnlinkExteriorPlanarFlowerLeftHalf m) where
  toFun x := ⟨coordinateUnlinkExteriorPlanarNeckArcFamily m x,
    coordinateUnlinkExteriorPlanarNeckArcFamily_mem_leftHalf m x⟩
  continuous_toFun :=
    (coordinateUnlinkExteriorPlanarNeckArcFamily m).continuous.subtype_mk _

/-- Regard every lifted arc as a map into the right half. -/
def coordinateUnlinkExteriorPlanarNeckArcToRightHalf
    (m : ℕ) [NeZero m] :
    C(ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval,
      CoordinateUnlinkExteriorPlanarFlowerRightHalf m) where
  toFun x := ⟨coordinateUnlinkExteriorPlanarNeckArcFamily m x,
    coordinateUnlinkExteriorPlanarNeckArcFamily_mem_rightHalf m x⟩
  continuous_toFun :=
    (coordinateUnlinkExteriorPlanarNeckArcFamily m).continuous.subtype_mk _

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckArcToLeftHalf_val
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m x).1 =
      coordinateUnlinkExteriorPlanarNeckArcFamily m x :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckArcToRightHalf_val
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarNeckArcToRightHalf m x).1 =
      coordinateUnlinkExteriorPlanarNeckArcFamily m x :=
  rfl

theorem injective_coordinateUnlinkExteriorPlanarNeckArcFamily
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckArcFamily m) :=
  injective_coordinateUnlinkExteriorPlanarNeckArcTranslate m

theorem injective_coordinateUnlinkExteriorPlanarNeckArcToLeftHalf
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m) := by
  intro x y h
  apply injective_coordinateUnlinkExteriorPlanarNeckArcFamily m
  have hval := congrArg Subtype.val h
  simpa only [coordinateUnlinkExteriorPlanarNeckArcToLeftHalf_val] using hval

theorem injective_coordinateUnlinkExteriorPlanarNeckArcToRightHalf
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckArcToRightHalf m) := by
  intro x y h
  apply injective_coordinateUnlinkExteriorPlanarNeckArcFamily m
  have hval := congrArg Subtype.val h
  simpa only [coordinateUnlinkExteriorPlanarNeckArcToRightHalf_val] using hval

/-- Recover the interval parameter of a flower point lying over the vertical diameter. -/
def coordinateUnlinkExteriorPlanarNeckParameter
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlower m)
    (_hre : (z.1.1 ^ m).re = -1 / 2) :
    CoordinateUnlinkExteriorPlanarNeckInterval := by
  let y : ℝ := (z.1.1 ^ m).im / sphereHandleRadius
  have him_le_norm : |(z.1.1 ^ m).im| ≤
      ‖z.1.1 ^ m + (1 / 2 : ℂ)‖ := by
    calc
      |(z.1.1 ^ m).im| = |(z.1.1 ^ m + (1 / 2 : ℂ)).im| := by simp
      _ ≤ ‖z.1.1 ^ m + (1 / 2 : ℂ)‖ := Complex.abs_im_le_norm _
  have him : |(z.1.1 ^ m).im| ≤ sphereHandleRadius :=
    him_le_norm.trans z.2.1
  have him_bounds := abs_le.mp him
  have hy_lower : -1 ≤ y := by
    apply (le_div_iff₀ sphereHandleRadius_pos).2
    dsimp [y]
    linarith
  have hy_upper : y ≤ 1 := by
    apply (div_le_iff₀ sphereHandleRadius_pos).2
    simpa only [one_mul] using him_bounds.2
  exact ⟨(y + 1) / 2, ⟨by linarith, by linarith⟩⟩

theorem coordinateUnlinkExteriorPlanarNeckBaseArc_parameter
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarFlower m)
    (hre : (z.1.1 ^ m).re = -1 / 2) :
    coordinateUnlinkExteriorPlanarNeckBaseArc
        (coordinateUnlinkExteriorPlanarNeckParameter m z hre) =
      z.1.1 ^ m := by
  apply Complex.ext
  · rw [coordinateUnlinkExteriorPlanarNeckBaseArc_re]
    exact hre.symm
  · rw [coordinateUnlinkExteriorPlanarNeckBaseArc_im]
    simp only [coordinateUnlinkExteriorPlanarNeckParameter]
    field_simp [sphereHandleRadius_ne_zero]
    ring

/-- Every point on the common closed-half boundary lies on one unique lifted arc. -/
theorem range_coordinateUnlinkExteriorPlanarNeckArcFamily
    (m : ℕ) [NeZero m] :
    range (coordinateUnlinkExteriorPlanarNeckArcFamily m) =
      coordinateUnlinkExteriorPlanarFlowerLeftHalfSet m ∩
        coordinateUnlinkExteriorPlanarFlowerRightHalfSet m := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨coordinateUnlinkExteriorPlanarNeckArcFamily_mem_leftHalf m x,
      coordinateUnlinkExteriorPlanarNeckArcFamily_mem_rightHalf m x⟩
  · intro hz
    have hre : (z.1.1 ^ m).re = -1 / 2 := le_antisymm hz.1 hz.2
    let t := coordinateUnlinkExteriorPlanarNeckParameter m z hre
    let r := coordinateUnlinkExteriorPlanarNeckArc m t
    have hpow : r.1.1 ^ m = z.1.1 ^ m := by
      rw [coordinateUnlinkExteriorPlanarNeckArc_pow,
        coordinateUnlinkExteriorPlanarNeckBaseArc_parameter m z hre]
    let q : ℂˣ := Units.mk0 (z.1.1 / r.1.1) (div_ne_zero z.1.2 r.1.2)
    have hqpow : (q : ℂ) ^ m = 1 := by
      change (z.1.1 / r.1.1) ^ m = 1
      rw [div_pow, hpow, div_self (pow_ne_zero m z.1.2)]
    let u : rootsOfUnity m ℂ :=
      ⟨q, (mem_rootsOfUnity' m q).mpr hqpow⟩
    let a : Multiplicative (ZMod m) :=
      (standardRootsOfUnityZModMulEquiv m).symm u
    refine ⟨(a.toAdd, t), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change ((((standardRootsOfUnityZModMulEquiv m a).1 : ℂˣ) : ℂ) * r.1.1) =
      z.1.1
    rw [(standardRootsOfUnityZModMulEquiv m).apply_symm_apply]
    exact div_mul_cancel₀ z.1.1 r.1.2

/-! ## Pushout recognition -/

theorem coordinateUnlinkExteriorPlanarNeckArc_half_compatibility
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion m
        (coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m x) =
      coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion m
        (coordinateUnlinkExteriorPlanarNeckArcToRightHalf m x) := by
  rfl

theorem coordinateUnlinkExteriorPlanarFlowerHalf_cross
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarFlowerLeftHalf m)
    (y : CoordinateUnlinkExteriorPlanarFlowerRightHalf m)
    (hxy : coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion m x =
      coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion m y) :
    ∃ a : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval,
      coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m a = x ∧
        coordinateUnlinkExteriorPlanarNeckArcToRightHalf m a = y := by
  have hval : x.1 = y.1 := by
    simpa only [coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion_apply,
      coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion_apply] using hxy
  have hxmem : x.1 ∈ coordinateUnlinkExteriorPlanarFlowerLeftHalfSet m ∩
      coordinateUnlinkExteriorPlanarFlowerRightHalfSet m := ⟨x.2, hval ▸ y.2⟩
  rw [← range_coordinateUnlinkExteriorPlanarNeckArcFamily m] at hxmem
  obtain ⟨a, ha⟩ := hxmem
  refine ⟨a, ?_, ?_⟩
  · apply Subtype.ext
    simpa only [coordinateUnlinkExteriorPlanarNeckArcToLeftHalf_val] using ha
  · apply Subtype.ext
    simpa only [coordinateUnlinkExteriorPlanarNeckArcToRightHalf_val] using ha.trans hval

theorem coordinateUnlinkExteriorPlanarFlowerHalf_cover
    (m : ℕ) :
    range (coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion m) ∪
        range (coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion m) =
      (univ : Set (CoordinateUnlinkExteriorPlanarFlower m)) := by
  apply Set.eq_univ_of_forall
  intro z
  rcases le_total (z.1.1 ^ m).re (-1 / 2) with hleft | hright
  · exact Or.inl ⟨⟨z, hleft⟩, by
      rfl⟩
  · exact Or.inr ⟨⟨z, hright⟩, by
      rfl⟩

/-- The whole flower is exactly the pushout of its two closed polynomial halves along all
`ZMod m`-indexed lifted vertical arcs. -/
def coordinateUnlinkExteriorPlanarFlowerNeckPushoutHomeomorph
    (m : ℕ) [NeZero m] :
    TopologicalPushout
        (coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m)
        (coordinateUnlinkExteriorPlanarNeckArcToRightHalf m) ≃ₜ
      CoordinateUnlinkExteriorPlanarFlower m :=
  topologicalPushoutHomeomorph
    (coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m)
    (coordinateUnlinkExteriorPlanarNeckArcToRightHalf m)
    (coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion m)
    (coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion m)
    (coordinateUnlinkExteriorPlanarNeckArc_half_compatibility m)
    (injective_coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m)
    (fun _ _ h ↦ Subtype.ext h) (fun _ _ h ↦ Subtype.ext h)
    (coordinateUnlinkExteriorPlanarFlowerHalf_cross m)
    (coordinateUnlinkExteriorPlanarFlowerHalf_cover m)

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerNeckPushoutHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarFlowerLeftHalf m) :
    coordinateUnlinkExteriorPlanarFlowerNeckPushoutHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m)
          (coordinateUnlinkExteriorPlanarNeckArcToRightHalf m) x) =
      x.1 :=
  topologicalPushoutHomeomorph_inl _ _ _ _ _ _ _ _ _ _ x

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerNeckPushoutHomeomorph_inr
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarFlowerRightHalf m) :
    coordinateUnlinkExteriorPlanarFlowerNeckPushoutHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m)
          (coordinateUnlinkExteriorPlanarNeckArcToRightHalf m) x) =
      x.1 :=
  topologicalPushoutHomeomorph_inr _ _ _ _ _ _ _ _ _ _ x

end SplittingSpheres
