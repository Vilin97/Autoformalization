/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalCoverPullbackRestriction
public import SplittingSpheres.Handlebody.CoordinateExteriorCharacter

/-!
# Restricting the coordinate-exterior power cover to its two pushout pieces

The radius-`1/8` coordinate exterior is a topological pushout of a whole one-handle and a
punctured cap.  This file restricts the explicit power pullback to each coprojection.  Both
coprojections are genuine embeddings: after composing with the established exterior
homeomorphism they are continuous injections from compact spaces into a Hausdorff space.

Consequently each restricted pullback is homeomorphic to the exact inverse-image piece of the
global pullback.  These are point-set covering statements; no smooth structure or graph
thickening of either total space is asserted.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

/-! ## Embedded pushout faces -/

/-- The whole one-handle coprojection is a topological embedding. -/
theorem isEmbedding_coordinateUnlinkExteriorPushoutOneHandleInclusion :
    IsEmbedding coordinateUnlinkExteriorPushoutOneHandleInclusion := by
  let H := coordinateUnlinkExteriorOneEighthHomeomorph
  have hcomp : IsEmbedding
      (H ∘ coordinateUnlinkExteriorPushoutOneHandleInclusion) := by
    have hmap : IsEmbedding
        (unlinkAlignedOneHandleExteriorMap
          oneEighth_lt_sphereHandleRadius_sub_half) :=
      ((unlinkAlignedOneHandleExteriorMap
          oneEighth_lt_sphereHandleRadius_sub_half).continuous.isClosedEmbedding
        (unlinkAlignedOneHandleExteriorMap_injective
          oneEighth_lt_sphereHandleRadius_sub_half)).isEmbedding
    have heq : H ∘ coordinateUnlinkExteriorPushoutOneHandleInclusion =
        unlinkAlignedOneHandleExteriorMap
          oneEighth_lt_sphereHandleRadius_sub_half := by
      funext x
      exact coordinateUnlinkExteriorPushoutHomeomorph_inl (by norm_num)
        oneEighth_lt_sphereHandleRadius_sub_half x
    rw [heq]
    exact hmap
  exact IsEmbedding.of_comp
    coordinateUnlinkExteriorPushoutOneHandleInclusion.continuous H.continuous hcomp

/-- The punctured-cap coprojection is a topological embedding. -/
theorem isEmbedding_coordinateUnlinkExteriorPushoutPuncturedCapInclusion :
    IsEmbedding coordinateUnlinkExteriorPushoutPuncturedCapInclusion := by
  let H := coordinateUnlinkExteriorOneEighthHomeomorph
  have hcomp : IsEmbedding
      (H ∘ coordinateUnlinkExteriorPushoutPuncturedCapInclusion) := by
    have hmap : IsEmbedding
        (unlinkAlignedPuncturedCapExteriorMap (1 / 8 : ℝ)) :=
      ((unlinkAlignedPuncturedCapExteriorMap (1 / 8 : ℝ)).continuous.isClosedEmbedding
        (unlinkAlignedPuncturedCapExteriorMap_injective (1 / 8 : ℝ))).isEmbedding
    have heq : H ∘ coordinateUnlinkExteriorPushoutPuncturedCapInclusion =
        unlinkAlignedPuncturedCapExteriorMap (1 / 8 : ℝ) := by
      funext x
      exact coordinateUnlinkExteriorPushoutHomeomorph_inr (by norm_num)
        oneEighth_lt_sphereHandleRadius_sub_half x
    rw [heq]
    exact hmap
  exact IsEmbedding.of_comp
    coordinateUnlinkExteriorPushoutPuncturedCapInclusion.continuous H.continuous hcomp

/-! ## The two restricted pullbacks -/

/-- The power pullback restricted to the whole `S¹ × B³` face. -/
abbrev CoordinateUnlinkExteriorOneHandlePowerPullback (m : ℕ) : Type :=
  TopologicalCoverPullback (nonzeroComplexPow m)
    (coordinateUnlinkExteriorPushoutRightNormalMap ∘
      coordinateUnlinkExteriorPushoutOneHandleInclusion)

/-- Projection of the restricted one-handle power pullback. -/
def coordinateUnlinkExteriorOneHandlePowerPullbackProj (m : ℕ) :
    CoordinateUnlinkExteriorOneHandlePowerPullback m → OneHandlePiece :=
  topologicalCoverPullbackProj (nonzeroComplexPow m)
    (coordinateUnlinkExteriorPushoutRightNormalMap ∘
      coordinateUnlinkExteriorPushoutOneHandleInclusion)

@[simp]
theorem coordinateUnlinkExteriorOneHandlePowerPullbackProj_apply (m : ℕ)
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    coordinateUnlinkExteriorOneHandlePowerPullbackProj m z = z.1.1 :=
  rfl

/-- The power pullback restricted to the punctured-cap face. -/
abbrev CoordinateUnlinkExteriorPuncturedCapPowerPullback (m : ℕ) : Type :=
  TopologicalCoverPullback (nonzeroComplexPow m)
    (coordinateUnlinkExteriorPushoutRightNormalMap ∘
      coordinateUnlinkExteriorPushoutPuncturedCapInclusion)

/-- Projection of the restricted punctured-cap power pullback. -/
def coordinateUnlinkExteriorPuncturedCapPowerPullbackProj (m : ℕ) :
    CoordinateUnlinkExteriorPuncturedCapPowerPullback m →
      UnlinkPuncturedCap (1 / 8 : ℝ) :=
  topologicalCoverPullbackProj (nonzeroComplexPow m)
    (coordinateUnlinkExteriorPushoutRightNormalMap ∘
      coordinateUnlinkExteriorPushoutPuncturedCapInclusion)

@[simp]
theorem coordinateUnlinkExteriorPuncturedCapPowerPullbackProj_apply (m : ℕ)
    (z : CoordinateUnlinkExteriorPuncturedCapPowerPullback m) :
    coordinateUnlinkExteriorPuncturedCapPowerPullbackProj m z = z.1.1 :=
  rfl

/-! ## Maps to the global pullback -/

/-- Include the restricted one-handle pullback into the global pushout pullback. -/
def coordinateUnlinkExteriorOneHandlePowerPullbackToPushout (m : ℕ) :
    CoordinateUnlinkExteriorOneHandlePowerPullback m →
      CoordinateUnlinkExteriorPushoutPowerPullback m :=
  topologicalCoverPullbackRestrictionMap (nonzeroComplexPow m)
    coordinateUnlinkExteriorPushoutRightNormalMap
    coordinateUnlinkExteriorPushoutOneHandleInclusion

@[simp]
theorem coordinateUnlinkExteriorOneHandlePowerPullbackToPushout_proj
    (m : ℕ) (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    coordinateUnlinkExteriorPushoutPowerPullbackProj m
        (coordinateUnlinkExteriorOneHandlePowerPullbackToPushout m z) =
      coordinateUnlinkExteriorPushoutOneHandleInclusion
        (coordinateUnlinkExteriorOneHandlePowerPullbackProj m z) :=
  rfl

theorem continuous_coordinateUnlinkExteriorOneHandlePowerPullbackToPushout (m : ℕ) :
    Continuous (coordinateUnlinkExteriorOneHandlePowerPullbackToPushout m) :=
  continuous_topologicalCoverPullbackRestrictionMap _ _
    coordinateUnlinkExteriorPushoutOneHandleInclusion.continuous

theorem isEmbedding_coordinateUnlinkExteriorOneHandlePowerPullbackToPushout (m : ℕ) :
    IsEmbedding (coordinateUnlinkExteriorOneHandlePowerPullbackToPushout m) :=
  isEmbedding_topologicalCoverPullbackRestrictionMap _ _
    isEmbedding_coordinateUnlinkExteriorPushoutOneHandleInclusion

/-- Include the restricted punctured-cap pullback into the global pushout pullback. -/
def coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout (m : ℕ) :
    CoordinateUnlinkExteriorPuncturedCapPowerPullback m →
      CoordinateUnlinkExteriorPushoutPowerPullback m :=
  topologicalCoverPullbackRestrictionMap (nonzeroComplexPow m)
    coordinateUnlinkExteriorPushoutRightNormalMap
    coordinateUnlinkExteriorPushoutPuncturedCapInclusion

@[simp]
theorem coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout_proj
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedCapPowerPullback m) :
    coordinateUnlinkExteriorPushoutPowerPullbackProj m
        (coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout m z) =
      coordinateUnlinkExteriorPushoutPuncturedCapInclusion
        (coordinateUnlinkExteriorPuncturedCapPowerPullbackProj m z) :=
  rfl

theorem continuous_coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout (m : ℕ) :
    Continuous (coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout m) :=
  continuous_topologicalCoverPullbackRestrictionMap _ _
    coordinateUnlinkExteriorPushoutPuncturedCapInclusion.continuous

theorem isEmbedding_coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout (m : ℕ) :
    IsEmbedding (coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout m) :=
  isEmbedding_topologicalCoverPullbackRestrictionMap _ _
    isEmbedding_coordinateUnlinkExteriorPushoutPuncturedCapInclusion

/-! ## Exact inverse-image identifications -/

/-- The one-handle restricted pullback is exactly the part of the global pullback over the
one-handle coprojection range. -/
def coordinateUnlinkExteriorOneHandlePowerPullbackRangeHomeomorph (m : ℕ) :
    CoordinateUnlinkExteriorOneHandlePowerPullback m ≃ₜ
      topologicalCoverPullbackRestrictionRange (nonzeroComplexPow m)
        coordinateUnlinkExteriorPushoutRightNormalMap
        coordinateUnlinkExteriorPushoutOneHandleInclusion :=
  topologicalCoverPullbackRestrictionRangeHomeomorph _ _ _
    isEmbedding_coordinateUnlinkExteriorPushoutOneHandleInclusion

/-- The punctured-cap restricted pullback is exactly the part of the global pullback over the
punctured-cap coprojection range. -/
def coordinateUnlinkExteriorPuncturedCapPowerPullbackRangeHomeomorph (m : ℕ) :
    CoordinateUnlinkExteriorPuncturedCapPowerPullback m ≃ₜ
      topologicalCoverPullbackRestrictionRange (nonzeroComplexPow m)
        coordinateUnlinkExteriorPushoutRightNormalMap
        coordinateUnlinkExteriorPushoutPuncturedCapInclusion :=
  topologicalCoverPullbackRestrictionRangeHomeomorph _ _ _
    isEmbedding_coordinateUnlinkExteriorPushoutPuncturedCapInclusion

/-! ## Covering and fiber cardinality -/

theorem isCoveringMap_coordinateUnlinkExteriorOneHandlePowerPullbackProj
    (m : ℕ) [NeZero m] :
    IsCoveringMap (coordinateUnlinkExteriorOneHandlePowerPullbackProj m) :=
  SplittingSpheres.IsCoveringMap.pullback (isCoveringMap_nonzeroComplexPow m)
    (continuous_coordinateUnlinkExteriorPushoutRightNormalMap.comp
      coordinateUnlinkExteriorPushoutOneHandleInclusion.continuous)

theorem isCoveringMap_coordinateUnlinkExteriorPuncturedCapPowerPullbackProj
    (m : ℕ) [NeZero m] :
    IsCoveringMap (coordinateUnlinkExteriorPuncturedCapPowerPullbackProj m) :=
  SplittingSpheres.IsCoveringMap.pullback (isCoveringMap_nonzeroComplexPow m)
    (continuous_coordinateUnlinkExteriorPushoutRightNormalMap.comp
      coordinateUnlinkExteriorPushoutPuncturedCapInclusion.continuous)

theorem natCard_coordinateUnlinkExteriorOneHandlePowerPullbackProj_fiber
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    Nat.card (coordinateUnlinkExteriorOneHandlePowerPullbackProj m ⁻¹' {x}) = m := by
  calc
    Nat.card (coordinateUnlinkExteriorOneHandlePowerPullbackProj m ⁻¹' {x}) =
        Nat.card (nonzeroComplexPow m ⁻¹'
          {(coordinateUnlinkExteriorPushoutRightNormalMap ∘
            coordinateUnlinkExteriorPushoutOneHandleInclusion) x}) :=
      Nat.card_congr (topologicalCoverPullbackFiberEquiv
        (nonzeroComplexPow m)
        (coordinateUnlinkExteriorPushoutRightNormalMap ∘
          coordinateUnlinkExteriorPushoutOneHandleInclusion) x)
    _ = m := natCard_nonzeroComplexPow_fiber m _

theorem natCard_coordinateUnlinkExteriorPuncturedCapPowerPullbackProj_fiber
    (m : ℕ) [NeZero m] (x : UnlinkPuncturedCap (1 / 8 : ℝ)) :
    Nat.card (coordinateUnlinkExteriorPuncturedCapPowerPullbackProj m ⁻¹' {x}) = m := by
  calc
    Nat.card (coordinateUnlinkExteriorPuncturedCapPowerPullbackProj m ⁻¹' {x}) =
        Nat.card (nonzeroComplexPow m ⁻¹'
          {(coordinateUnlinkExteriorPushoutRightNormalMap ∘
            coordinateUnlinkExteriorPushoutPuncturedCapInclusion) x}) :=
      Nat.card_congr (topologicalCoverPullbackFiberEquiv
        (nonzeroComplexPow m)
        (coordinateUnlinkExteriorPushoutRightNormalMap ∘
          coordinateUnlinkExteriorPushoutPuncturedCapInclusion) x)
    _ = m := natCard_nonzeroComplexPow_fiber m _

end SplittingSpheres
