/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckCompactCutSmooth

/-!
# Comparing the compact cut carriers with the neck-star pieces

The compact coordinate exterior is already homeomorphic to the full neck star.  This file
restricts that homeomorphism to the two closed cut carriers.  Each restriction is identified
with the image of the corresponding pushout coprojection and hence with the original left or
right neck-star source piece.

These are point-set homeomorphisms.  No smoothness of the old neck-star source pieces or of their
coprojections is asserted.
-/

@[expose] public section

open Function Set Topology
open scoped Topology

noncomputable section

namespace SplittingSpheres

variable (m : ℕ) [NeZero m]

local notation "F" => coordinateUnlinkExteriorPlanarNeckStarToLeft
local notation "G" => coordinateUnlinkExteriorPlanarNeckStarToRight

/-- A compact point lies in the left cut carrier exactly when its neck-star image lies in the
left coprojection range. -/
theorem compactNeckStar_mem_range_inl_iff_leftCut
    (z : CoordinateUnlinkExteriorEighthPowerPullback m) :
    coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m z ∈
        range (topologicalPushoutInl (F m) (G m)) ↔
      z ∈ coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m := by
  rw [range_topologicalPushoutInl_eq_compl_image_inr_compl_range
    (F m) (G m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m).injective]
  rfl

/-- Restrict the compact-to-star homeomorphism to the left coprojection range. -/
def compactNeckLeftCutHomeomorphRangeInl :
    CompactNeckLeftCut m ≃ₜ
      ↑(range (topologicalPushoutInl (F m) (G m))) :=
  (coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m).subtype
    (fun z => (compactNeckStar_mem_range_inl_iff_leftCut m z).symm)

/-- The left neck-star source is homeomorphic to the image of its coprojection. -/
def neckStarLeftComplementHomeomorphRangeInl :
    CoordinateUnlinkExteriorPlanarNeckLeftComplement m ≃ₜ
      ↑(range (topologicalPushoutInl (F m) (G m))) :=
  (Homeomorph.Set.univ
      (CoordinateUnlinkExteriorPlanarNeckLeftComplement m)).symm.trans <|
    ((isEmbedding_topologicalPushoutInl (F m) (G m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToRight m)).homeomorphImage
          univ).trans
        (Homeomorph.setCongr (by rw [image_univ]))

/-- The closed left compact cut carrier is homeomorphic to the old left neck-star source. -/
def compactNeckLeftCutHomeomorphNeckLeftComplement :
    CompactNeckLeftCut m ≃ₜ
      CoordinateUnlinkExteriorPlanarNeckLeftComplement m :=
  (compactNeckLeftCutHomeomorphRangeInl m).trans
    (neckStarLeftComplementHomeomorphRangeInl m).symm

/-- The left comparison commutes exactly with inclusion into the full neck star. -/
@[simp]
theorem compactNeckLeftCutHomeomorphNeckLeftComplement_inclusion
    (z : CompactNeckLeftCut m) :
    topologicalPushoutInl (F m) (G m)
        (compactNeckLeftCutHomeomorphNeckLeftComplement m z) =
      coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m z := by
  have h := (neckStarLeftComplementHomeomorphRangeInl m).apply_symm_apply
    (compactNeckLeftCutHomeomorphRangeInl m z)
  exact congrArg Subtype.val h

/-- A compact point lies in the right cut carrier exactly when its neck-star image lies in the
right coprojection range. -/
theorem compactNeckStar_mem_range_inr_iff_rightCut
    (z : CoordinateUnlinkExteriorEighthPowerPullback m) :
    coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m z ∈
        range (topologicalPushoutInr (F m) (G m)) ↔
      z ∈ coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m := by
  rw [range_topologicalPushoutInr_eq_compl_image_inl_compl_range
    (F m) (G m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToRight m).injective]
  rfl

/-- Restrict the compact-to-star homeomorphism to the right coprojection range. -/
def compactNeckRightCutHomeomorphRangeInr :
    CompactNeckRightCut m ≃ₜ
      ↑(range (topologicalPushoutInr (F m) (G m))) :=
  (coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m).subtype
    (fun z => (compactNeckStar_mem_range_inr_iff_rightCut m z).symm)

/-- The right neck-star source is homeomorphic to the image of its coprojection. -/
def neckStarRightComplementHomeomorphRangeInr :
    CoordinateUnlinkExteriorPlanarNeckRightComplement m ≃ₜ
      ↑(range (topologicalPushoutInr (F m) (G m))) :=
  (Homeomorph.Set.univ
      (CoordinateUnlinkExteriorPlanarNeckRightComplement m)).symm.trans <|
    ((isEmbedding_topologicalPushoutInr (F m) (G m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m)).homeomorphImage
          univ).trans
        (Homeomorph.setCongr (by rw [image_univ]))

/-- The closed right compact cut carrier is homeomorphic to the old right neck-star source. -/
def compactNeckRightCutHomeomorphNeckRightComplement :
    CompactNeckRightCut m ≃ₜ
      CoordinateUnlinkExteriorPlanarNeckRightComplement m :=
  (compactNeckRightCutHomeomorphRangeInr m).trans
    (neckStarRightComplementHomeomorphRangeInr m).symm

/-- The right comparison commutes exactly with inclusion into the full neck star. -/
@[simp]
theorem compactNeckRightCutHomeomorphNeckRightComplement_inclusion
    (z : CompactNeckRightCut m) :
    topologicalPushoutInr (F m) (G m)
        (compactNeckRightCutHomeomorphNeckRightComplement m z) =
      coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m z := by
  have h := (neckStarRightComplementHomeomorphRangeInr m).apply_symm_apply
    (compactNeckRightCutHomeomorphRangeInr m z)
  exact congrArg Subtype.val h

end SplittingSpheres

end
