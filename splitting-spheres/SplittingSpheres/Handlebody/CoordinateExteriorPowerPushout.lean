/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPowerPieceCover

/-!
# Gluing the restricted power pullbacks

The radius-`1/8` exterior is a pushout of its whole one-handle and punctured-cap pieces.  Pulling
the power cover back to the attaching boundary gives compatible maps into the two restricted
total spaces.  Their topological pushout has a canonical continuous map to the global total
space.  Here we prove that map is bijective, with exact formulas on both pieces.

This file deliberately stops at a continuous bijection.  A homeomorphism will follow once the
restricted total spaces have the required compactness (or an explicit inverse is shown
continuous).  No such separation or compactness premise is hidden in the present statement.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

/-! ## The pullback over the attaching boundary -/

/-- The power pullback over the common `S¹ × S²` attaching boundary, written using the
one-handle attaching map. -/
abbrev CoordinateUnlinkExteriorBoundaryPowerPullback (m : ℕ) : Type :=
  TopologicalCoverPullback (nonzeroComplexPow m)
    ((coordinateUnlinkExteriorPushoutRightNormalMap ∘
      coordinateUnlinkExteriorPushoutOneHandleInclusion) ∘
        oneHandleBoundaryInclusion)

/-- Projection from the attaching-boundary pullback. -/
def coordinateUnlinkExteriorBoundaryPowerPullbackProj (m : ℕ) :
    CoordinateUnlinkExteriorBoundaryPowerPullback m → OneHandleCapBoundary :=
  topologicalCoverPullbackProj (nonzeroComplexPow m)
    ((coordinateUnlinkExteriorPushoutRightNormalMap ∘
      coordinateUnlinkExteriorPushoutOneHandleInclusion) ∘
        oneHandleBoundaryInclusion)

@[simp]
theorem coordinateUnlinkExteriorBoundaryPowerPullbackProj_apply (m : ℕ)
    (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    coordinateUnlinkExteriorBoundaryPowerPullbackProj m z = z.1.1 :=
  rfl

/-- Include the boundary pullback into the one-handle restricted pullback. -/
def coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle (m : ℕ) :
    CoordinateUnlinkExteriorBoundaryPowerPullback m →
      CoordinateUnlinkExteriorOneHandlePowerPullback m :=
  topologicalCoverPullbackRestrictionMap (nonzeroComplexPow m)
    (coordinateUnlinkExteriorPushoutRightNormalMap ∘
      coordinateUnlinkExteriorPushoutOneHandleInclusion)
    oneHandleBoundaryInclusion

@[simp]
theorem coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle_base
    (m : ℕ) (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    (coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m z).1.1 =
      oneHandleBoundaryInclusion z.1.1 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle_fiberCoordinate
    (m : ℕ) (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    (coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m z).1.2 = z.1.2 :=
  rfl

theorem continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle (m : ℕ) :
    Continuous (coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m) :=
  continuous_topologicalCoverPullbackRestrictionMap _ _
    oneHandleBoundaryInclusion.continuous

theorem injective_coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle (m : ℕ) :
    Injective (coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m) :=
  injective_topologicalCoverPullbackRestrictionMap _ _
    oneHandleBoundaryInclusion_injective

/-- Include the same boundary pullback into the punctured-cap restricted pullback.  Its legality
uses the base pushout compatibility equation. -/
def coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap (m : ℕ) :
    CoordinateUnlinkExteriorBoundaryPowerPullback m →
      CoordinateUnlinkExteriorPuncturedCapPowerPullback m :=
  fun z ↦ ⟨(unlinkPuncturedCapBoundaryInclusion
      oneEighth_lt_sphereHandleRadius_sub_half z.1.1, z.1.2), by
    change coordinateUnlinkExteriorPushoutRightNormalMap
        (coordinateUnlinkExteriorPushoutPuncturedCapInclusion
          (unlinkPuncturedCapBoundaryInclusion
            oneEighth_lt_sphereHandleRadius_sub_half z.1.1)) =
      nonzeroComplexPow m z.1.2
    rw [← topologicalPushout_condition oneHandleBoundaryInclusion
      (unlinkPuncturedCapBoundaryInclusion
        oneEighth_lt_sphereHandleRadius_sub_half) z.1.1]
    exact z.2⟩

@[simp]
theorem coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap_base
    (m : ℕ) (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    (coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m z).1.1 =
      unlinkPuncturedCapBoundaryInclusion
        oneEighth_lt_sphereHandleRadius_sub_half z.1.1 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap_fiberCoordinate
    (m : ℕ) (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    (coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m z).1.2 = z.1.2 :=
  rfl

theorem continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap (m : ℕ) :
    Continuous (coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m) := by
  apply Continuous.subtype_mk
  exact ((unlinkPuncturedCapBoundaryInclusion
    oneEighth_lt_sphereHandleRadius_sub_half).continuous.comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
    (continuous_snd.comp continuous_subtype_val)

theorem injective_coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap (m : ℕ) :
    Injective (coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m) := by
  intro z w hzw
  apply Subtype.ext
  apply Prod.ext
  · apply unlinkPuncturedCapBoundaryInclusion_injective
    exact congrArg
      (fun q : CoordinateUnlinkExteriorPuncturedCapPowerPullback m ↦ q.1.1) hzw
  · exact congrArg
      (fun q : CoordinateUnlinkExteriorPuncturedCapPowerPullback m ↦ q.1.2) hzw

/-! ## The pushout of total-space pieces -/

/-- Glue the two restricted total spaces along their common boundary pullback. -/
abbrev CoordinateUnlinkExteriorPowerPullbackPushout (m : ℕ) : Type :=
  TopologicalPushout
    ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m,
      continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m⟩
    ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m,
      continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m⟩

/-- The two maps from restricted total spaces to the global total space agree on the lifted
attaching boundary. -/
theorem coordinateUnlinkExteriorPowerPullback_piece_compatibility
    (m : ℕ) (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    coordinateUnlinkExteriorOneHandlePowerPullbackToPushout m
        (coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m z) =
      coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout m
        (coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m z) := by
  apply Subtype.ext
  apply Prod.ext
  · exact topologicalPushout_condition oneHandleBoundaryInclusion
      (unlinkPuncturedCapBoundaryInclusion
        oneEighth_lt_sphereHandleRadius_sub_half) z.1.1
  · rfl

/-- The canonical continuous map from the glued restricted total spaces to the global power
pullback. -/
def coordinateUnlinkExteriorPowerPullbackPushoutDesc (m : ℕ) :
    C(CoordinateUnlinkExteriorPowerPullbackPushout m,
      CoordinateUnlinkExteriorPushoutPowerPullback m) :=
  topologicalPushoutDesc
    ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m,
      continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m⟩
    ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m,
      continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m⟩
    ⟨coordinateUnlinkExteriorOneHandlePowerPullbackToPushout m,
      continuous_coordinateUnlinkExteriorOneHandlePowerPullbackToPushout m⟩
    ⟨coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout m,
      continuous_coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout m⟩
    (coordinateUnlinkExteriorPowerPullback_piece_compatibility m)

@[simp]
theorem coordinateUnlinkExteriorPowerPullbackPushoutDesc_inl
    (m : ℕ) (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    coordinateUnlinkExteriorPowerPullbackPushoutDesc m
        (topologicalPushoutInl
          ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m,
            continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m⟩
          ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m,
            continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m⟩ z) =
      coordinateUnlinkExteriorOneHandlePowerPullbackToPushout m z :=
  topologicalPushoutDesc_inl _ _ _ _ _ z

@[simp]
theorem coordinateUnlinkExteriorPowerPullbackPushoutDesc_inr
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedCapPowerPullback m) :
    coordinateUnlinkExteriorPowerPullbackPushoutDesc m
        (topologicalPushoutInr
          ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m,
            continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m⟩
          ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m,
            continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m⟩ z) =
      coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout m z :=
  topologicalPushoutDesc_inr _ _ _ _ _ z

/-! ## Exact overlap and coverage -/

theorem coordinateUnlinkExteriorPowerPullback_piece_cross
    (m : ℕ) (x : CoordinateUnlinkExteriorOneHandlePowerPullback m)
    (y : CoordinateUnlinkExteriorPuncturedCapPowerPullback m)
    (hxy : coordinateUnlinkExteriorOneHandlePowerPullbackToPushout m x =
      coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout m y) :
    ∃ z : CoordinateUnlinkExteriorBoundaryPowerPullback m,
      coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m z = x ∧
        coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m z = y := by
  have hbase : coordinateUnlinkExteriorPushoutOneHandleInclusion x.1.1 =
      coordinateUnlinkExteriorPushoutPuncturedCapInclusion y.1.1 :=
    congrArg (fun q : CoordinateUnlinkExteriorPushoutPowerPullback m ↦ q.1.1) hxy
  obtain ⟨a, haX, haY⟩ :=
    (topologicalPushoutInl_eq_inr_iff oneHandleBoundaryInclusion
      (unlinkPuncturedCapBoundaryInclusion
        oneEighth_lt_sphereHandleRadius_sub_half)
      oneHandleBoundaryInclusion_injective x.1.1 y.1.1).mp hbase
  have hfiber : x.1.2 = y.1.2 :=
    congrArg (fun q : CoordinateUnlinkExteriorPushoutPowerPullback m ↦ q.1.2) hxy
  let z : CoordinateUnlinkExteriorBoundaryPowerPullback m :=
    ⟨(a, x.1.2), by
      change coordinateUnlinkExteriorPushoutRightNormalMap
          (coordinateUnlinkExteriorPushoutOneHandleInclusion
            (oneHandleBoundaryInclusion a)) = nonzeroComplexPow m x.1.2
      rw [haX]
      exact x.2⟩
  refine ⟨z, ?_, ?_⟩
  · apply Subtype.ext
    apply Prod.ext
    · exact haX
    · rfl
  · apply Subtype.ext
    apply Prod.ext
    · exact haY
    · exact hfiber

theorem range_coordinateUnlinkExteriorPowerPullback_piece_union :
    range (coordinateUnlinkExteriorOneHandlePowerPullbackToPushout m) ∪
        range (coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout m) = univ := by
  ext z
  constructor
  · exact fun _ ↦ mem_univ z
  · intro _
    rcases topologicalPushout_jointly_surjective oneHandleBoundaryInclusion
        (unlinkPuncturedCapBoundaryInclusion
          oneEighth_lt_sphereHandleRadius_sub_half) z.1.1 with
      ⟨x, hx⟩ | ⟨y, hy⟩
    · apply Or.inl
      let w : CoordinateUnlinkExteriorOneHandlePowerPullback m :=
        ⟨(x, z.1.2), by
          change coordinateUnlinkExteriorPushoutRightNormalMap
              (coordinateUnlinkExteriorPushoutOneHandleInclusion x) =
            nonzeroComplexPow m z.1.2
          rw [hx]
          exact z.2⟩
      refine ⟨w, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · exact hx
      · rfl
    · apply Or.inr
      let w : CoordinateUnlinkExteriorPuncturedCapPowerPullback m :=
        ⟨(y, z.1.2), by
          change coordinateUnlinkExteriorPushoutRightNormalMap
              (coordinateUnlinkExteriorPushoutPuncturedCapInclusion y) =
            nonzeroComplexPow m z.1.2
          rw [hy]
          exact z.2⟩
      refine ⟨w, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · exact hy
      · rfl

/-- The canonical map from the glued restricted pullbacks to the global pullback is bijective. -/
theorem coordinateUnlinkExteriorPowerPullbackPushoutDesc_bijective (m : ℕ) :
    Bijective (coordinateUnlinkExteriorPowerPullbackPushoutDesc m) :=
  topologicalPushoutDesc_bijective _ _ _ _ _
    (injective_coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m)
    (isEmbedding_coordinateUnlinkExteriorOneHandlePowerPullbackToPushout m).injective
    (isEmbedding_coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout m).injective
    (coordinateUnlinkExteriorPowerPullback_piece_cross m)
    range_coordinateUnlinkExteriorPowerPullback_piece_union

/-- The underlying set equivalence between the glued restricted pullbacks and the global power
pullback.  The forward map is the canonical continuous descended map. -/
def coordinateUnlinkExteriorPowerPullbackPushoutEquiv (m : ℕ) :
    CoordinateUnlinkExteriorPowerPullbackPushout m ≃
      CoordinateUnlinkExteriorPushoutPowerPullback m :=
  Equiv.ofBijective (coordinateUnlinkExteriorPowerPullbackPushoutDesc m)
    (coordinateUnlinkExteriorPowerPullbackPushoutDesc_bijective m)

@[simp]
theorem coordinateUnlinkExteriorPowerPullbackPushoutEquiv_apply (m : ℕ)
    (z : CoordinateUnlinkExteriorPowerPullbackPushout m) :
    coordinateUnlinkExteriorPowerPullbackPushoutEquiv m z =
      coordinateUnlinkExteriorPowerPullbackPushoutDesc m z :=
  rfl

theorem continuous_coordinateUnlinkExteriorPowerPullbackPushoutEquiv (m : ℕ) :
    Continuous (coordinateUnlinkExteriorPowerPullbackPushoutEquiv m) :=
  (coordinateUnlinkExteriorPowerPullbackPushoutDesc m).continuous

end SplittingSpheres
