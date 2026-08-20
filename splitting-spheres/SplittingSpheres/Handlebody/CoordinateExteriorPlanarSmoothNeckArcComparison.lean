/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarSmoothNeckArc

/-!
# Comparing the explicit smooth neck root with the selected topological root

The explicit smooth complex root and the previously selected continuous root have the same
nonzero `m`-th power.  Their quotient is therefore a continuous map from the connected neck
interval to the finite, discrete group of `m`-th roots of unity, hence is constant.  This
produces one fixed `ZMod m` shift relating the two complete deck-translate families.

The explicit complex arc is also bundled into the existing point-set flower, and this bundled
map is proved continuous.  No smooth structure or smoothness claim on the flower subtype is
introduced here.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-! ## The constant roots-of-unity quotient -/

/-- The quotient of the explicit smooth root by the selected continuous root. -/
def coordinateUnlinkExteriorPlanarSmoothNeckRootRatio
    (m : ℕ) [NeZero m]
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    rootsOfUnity m ℂ :=
  ⟨Units.mk0
      (coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m t /
        (coordinateUnlinkExteriorPlanarNeckArc m t).1.1)
      (div_ne_zero
        (coordinateUnlinkExteriorPlanarSmoothNeckArcComplex_ne_zero m t)
        (coordinateUnlinkExteriorPlanarNeckPowerRoot_ne_zero m t)),
    (mem_rootsOfUnity' m _).2 (by
      change
        (coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m t /
          (coordinateUnlinkExteriorPlanarNeckArc m t).1.1) ^ m = 1
      rw [div_pow, coordinateUnlinkExteriorPlanarSmoothNeckArcComplex_pow,
        coordinateUnlinkExteriorPlanarNeckArc_pow]
      exact div_self (coordinateUnlinkExteriorPlanarNeckBaseArc_ne_zero t))⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarSmoothNeckRootRatio_val
    (m : ℕ) [NeZero m]
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (((coordinateUnlinkExteriorPlanarSmoothNeckRootRatio m t).1 : ℂˣ) : ℂ) =
      coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m t /
        (coordinateUnlinkExteriorPlanarNeckArc m t).1.1 :=
  rfl

/-- The roots-of-unity quotient is continuous. -/
theorem continuous_coordinateUnlinkExteriorPlanarSmoothNeckRootRatio
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarSmoothNeckRootRatio m) := by
  have hemb : IsEmbedding
      (fun u : rootsOfUnity m ℂ ↦ ((u.1 : ℂˣ) : ℂ)) :=
    Units.isEmbedding_val₀.comp IsEmbedding.subtypeVal
  apply hemb.continuous_iff.mpr
  change Continuous (fun t ↦
    coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m t /
      (coordinateUnlinkExteriorPlanarNeckArc m t).1.1)
  exact
    (contMDiff_coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m).continuous.div
      (continuous_subtype_val.comp <|
        continuous_subtype_val.comp <|
          continuous_coordinateUnlinkExteriorPlanarNeckArc m)
      (coordinateUnlinkExteriorPlanarNeckPowerRoot_ne_zero m)

/-- The quotient has the same value everywhere as at the lower endpoint. -/
theorem coordinateUnlinkExteriorPlanarSmoothNeckRootRatio_eq_zero
    (m : ℕ) [NeZero m]
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarSmoothNeckRootRatio m t =
      coordinateUnlinkExteriorPlanarSmoothNeckRootRatio m 0 := by
  have hlocal : IsLocallyConstant
      (coordinateUnlinkExteriorPlanarSmoothNeckRootRatio m) :=
    (IsLocallyConstant.iff_continuous _).2
      (continuous_coordinateUnlinkExteriorPlanarSmoothNeckRootRatio m)
  exact congrFun (hlocal.eq_const 0) t

/-- The unique fixed label shift determined by the quotient at the lower endpoint. -/
def coordinateUnlinkExteriorPlanarSmoothNeckShift
    (m : ℕ) [NeZero m] : ZMod m :=
  ((standardRootsOfUnityZModMulEquiv m).symm
    (coordinateUnlinkExteriorPlanarSmoothNeckRootRatio m 0)).toAdd

/-- The explicit smooth root is the selected root multiplied by the fixed root of unity. -/
theorem coordinateUnlinkExteriorPlanarSmoothNeckArcComplex_eq_shift_mul_selected
    (m : ℕ) [NeZero m]
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m t =
      (((standardRootsOfUnityZModMulEquiv m
        (Multiplicative.ofAdd
          (coordinateUnlinkExteriorPlanarSmoothNeckShift m))).1 : ℂˣ) : ℂ) *
        (coordinateUnlinkExteriorPlanarNeckArc m t).1.1 := by
  have hratio := congrArg
    (fun u : rootsOfUnity m ℂ ↦ ((u.1 : ℂˣ) : ℂ))
    (coordinateUnlinkExteriorPlanarSmoothNeckRootRatio_eq_zero m t)
  rw [coordinateUnlinkExteriorPlanarSmoothNeckRootRatio_val,
    coordinateUnlinkExteriorPlanarSmoothNeckRootRatio_val] at hratio
  have hshift :
      standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd
            (coordinateUnlinkExteriorPlanarSmoothNeckShift m)) =
        coordinateUnlinkExteriorPlanarSmoothNeckRootRatio m 0 :=
    (standardRootsOfUnityZModMulEquiv m).apply_symm_apply _
  have hshiftval := congrArg
    (fun u : rootsOfUnity m ℂ ↦ ((u.1 : ℂˣ) : ℂ)) hshift
  rw [coordinateUnlinkExteriorPlanarSmoothNeckRootRatio_val] at hshiftval
  calc
    coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m t =
        (coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m t /
          (coordinateUnlinkExteriorPlanarNeckArc m t).1.1) *
            (coordinateUnlinkExteriorPlanarNeckArc m t).1.1 :=
      (div_mul_cancel₀ _
        (coordinateUnlinkExteriorPlanarNeckPowerRoot_ne_zero m t)).symm
    _ = (coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m 0 /
          (coordinateUnlinkExteriorPlanarNeckArc m 0).1.1) *
            (coordinateUnlinkExteriorPlanarNeckArc m t).1.1 := by
      rw [hratio]
    _ = _ := congrArg
      (fun z : ℂ ↦ z * (coordinateUnlinkExteriorPlanarNeckArc m t).1.1)
      hshiftval.symm

/-- Complex-coordinate comparison with the selected translated arc. -/
theorem coordinateUnlinkExteriorPlanarSmoothNeckArcComplex_eq_selectedTranslate_val
    (m : ℕ) [NeZero m]
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m t =
      (coordinateUnlinkExteriorPlanarNeckArcTranslate m
        (coordinateUnlinkExteriorPlanarSmoothNeckShift m) t).1.1 := by
  rw [coordinateUnlinkExteriorPlanarNeckArcTranslate_val]
  exact
    coordinateUnlinkExteriorPlanarSmoothNeckArcComplex_eq_shift_mul_selected m t

/-! ## Bundling the explicit arc into the point-set flower -/

/-- The explicit smooth complex root bundled into the existing point-set flower. -/
def coordinateUnlinkExteriorPlanarSmoothNeckArc
    (m : ℕ) [NeZero m]
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    CoordinateUnlinkExteriorPlanarFlower m :=
  ⟨⟨coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m t,
      coordinateUnlinkExteriorPlanarSmoothNeckArcComplex_ne_zero m t⟩, by
    rw [mem_coordinateUnlinkExteriorPlanarFlowerSet_iff,
      coordinateUnlinkExteriorPlanarSmoothNeckArcComplex_pow]
    exact ⟨norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_half_le t,
      le_trans (by norm_num)
        (norm_coordinateUnlinkExteriorPlanarNeckBaseArc_ge_half t),
      le_trans (by norm_num)
        (norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_one_ge_half t)⟩⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarSmoothNeckArc_val
    (m : ℕ) [NeZero m]
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarSmoothNeckArc m t).1.1 =
      coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m t :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarSmoothNeckArc_pow
    (m : ℕ) [NeZero m]
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarSmoothNeckArc m t).1.1 ^ m =
      coordinateUnlinkExteriorPlanarNeckBaseArc t :=
  coordinateUnlinkExteriorPlanarSmoothNeckArcComplex_pow m t

/-- The bundled explicit arc is continuous.  This is not a smoothness statement about the
flower subtype. -/
theorem continuous_coordinateUnlinkExteriorPlanarSmoothNeckArc
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarSmoothNeckArc m) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (contMDiff_coordinateUnlinkExteriorPlanarSmoothNeckArcComplex m).continuous

/-- The bundled explicit arc is exactly one fixed selected translate. -/
theorem coordinateUnlinkExteriorPlanarSmoothNeckArc_eq_selectedTranslate
    (m : ℕ) [NeZero m]
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarSmoothNeckArc m t =
      coordinateUnlinkExteriorPlanarNeckArcTranslate m
        (coordinateUnlinkExteriorPlanarSmoothNeckShift m) t := by
  apply Subtype.ext
  apply Subtype.ext
  exact
    coordinateUnlinkExteriorPlanarSmoothNeckArcComplex_eq_selectedTranslate_val m t

/-- The fixed shift is the unique label representing the bundled explicit arc. -/
theorem coordinateUnlinkExteriorPlanarSmoothNeckShift_unique
    (m : ℕ) [NeZero m] (a : ZMod m)
    (ha : ∀ t, coordinateUnlinkExteriorPlanarSmoothNeckArc m t =
      coordinateUnlinkExteriorPlanarNeckArcTranslate m a t) :
    a = coordinateUnlinkExteriorPlanarSmoothNeckShift m := by
  have htranslate :
      coordinateUnlinkExteriorPlanarNeckArcTranslate m a 0 =
        coordinateUnlinkExteriorPlanarNeckArcTranslate m
          (coordinateUnlinkExteriorPlanarSmoothNeckShift m) 0 :=
    (ha 0).symm.trans
      (coordinateUnlinkExteriorPlanarSmoothNeckArc_eq_selectedTranslate m 0)
  have hp : (a, (0 : CoordinateUnlinkExteriorPlanarNeckInterval)) =
      (coordinateUnlinkExteriorPlanarSmoothNeckShift m, 0) :=
    injective_coordinateUnlinkExteriorPlanarNeckArcTranslate m htranslate
  exact congrArg Prod.fst hp

/-! ## The full translated family -/

/-- A deck translate of the explicitly bundled arc. -/
def coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    CoordinateUnlinkExteriorPlanarFlower m :=
  coordinateUnlinkExteriorPlanarFlowerDeckMap m
    (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a))
    (coordinateUnlinkExteriorPlanarSmoothNeckArc m t)

@[simp]
theorem coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate_val
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate m a t).1.1 =
      coordinateUnlinkExteriorPlanarSmoothNeckArcComplexTranslate m a t :=
  rfl

/-- Every explicit translate is the selected translate with its label shifted on the right. -/
theorem coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate_eq_selectedTranslate_add
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate m a t =
      coordinateUnlinkExteriorPlanarNeckArcTranslate m
        (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) t := by
  rw [coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate,
    coordinateUnlinkExteriorPlanarSmoothNeckArc_eq_selectedTranslate,
    coordinateUnlinkExteriorPlanarNeckArcTranslate_add]

/-- The fixed translation of labels relating the explicit and selected families. -/
def coordinateUnlinkExteriorPlanarSmoothNeckLabelEquiv
    (m : ℕ) [NeZero m] : ZMod m ≃ ZMod m :=
  Equiv.addRight (coordinateUnlinkExteriorPlanarSmoothNeckShift m)

@[simp]
theorem coordinateUnlinkExteriorPlanarSmoothNeckLabelEquiv_apply
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarSmoothNeckLabelEquiv m a =
      a + coordinateUnlinkExteriorPlanarSmoothNeckShift m :=
  rfl

/-- Per label, the explicit arc range is the selected range at the shifted label. -/
theorem range_coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate
    (m : ℕ) [NeZero m] (a : ZMod m) :
    range (coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate m a) =
      range (coordinateUnlinkExteriorPlanarNeckArcTranslate m
        (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t,
      (coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate_eq_selectedTranslate_add
        m a t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t,
      coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate_eq_selectedTranslate_add
        m a t⟩

/-- The two jointly parameterized translated families have exactly the same total range. -/
theorem range_coordinateUnlinkExteriorPlanarSmoothNeckArcTranslateFamily
    (m : ℕ) [NeZero m] :
    range (fun x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval ↦
      coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate m x.1 x.2) =
      range (fun x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval ↦
        coordinateUnlinkExteriorPlanarNeckArcTranslate m x.1 x.2) := by
  ext z
  constructor
  · rintro ⟨⟨a, t⟩, rfl⟩
    refine ⟨
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m, t), ?_⟩
    exact
      (coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate_eq_selectedTranslate_add
        m a t).symm
  · rintro ⟨⟨b, t⟩, rfl⟩
    refine ⟨
      (b - coordinateUnlinkExteriorPlanarSmoothNeckShift m, t), ?_⟩
    change coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate m
      (b - coordinateUnlinkExteriorPlanarSmoothNeckShift m) t = _
    simpa using
      coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate_eq_selectedTranslate_add
        m (b - coordinateUnlinkExteriorPlanarSmoothNeckShift m) t

/-- The two `ZMod m`-indexed collections of individual arc ranges are exactly equal. -/
theorem range_range_coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate
    (m : ℕ) [NeZero m] :
    range (fun a : ZMod m ↦
      range (coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate m a)) =
      range (fun a : ZMod m ↦
        range (coordinateUnlinkExteriorPlanarNeckArcTranslate m a)) := by
  ext s
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a + coordinateUnlinkExteriorPlanarSmoothNeckShift m, ?_⟩
    exact
      (range_coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate m a).symm
  · rintro ⟨b, rfl⟩
    refine ⟨b - coordinateUnlinkExteriorPlanarSmoothNeckShift m, ?_⟩
    change range (coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate m
      (b - coordinateUnlinkExteriorPlanarSmoothNeckShift m)) = _
    simpa using range_coordinateUnlinkExteriorPlanarSmoothNeckArcTranslate m
      (b - coordinateUnlinkExteriorPlanarSmoothNeckShift m)

end SplittingSpheres
