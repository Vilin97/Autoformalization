/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutSeparation
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckStar

/-!
# Separation by the full neck family in the literal star

The literal neck star is a pushout of the labelled left complement and the central right
complement along `ZMod m × Sphere 3`.  This file proves that both attaching maps are closed
embeddings and applies the point-set pushout separation theorem: removing the image of the
whole labelled neck family leaves two disjoint open sides.

This is simultaneous-family separation.  It does not assert that removing one selected
three-sphere separates the star; that requires the label-by-label star cut.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

/-- The left attaching map of the literal neck star is a closed embedding. -/
theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft
    (m : ℕ) [NeZero m] :
    IsClosedEmbedding (coordinateUnlinkExteriorPlanarNeckStarToLeft m) := by
  have heq :
      (coordinateUnlinkExteriorPlanarNeckStarToLeft m :
        ZMod m × Sphere 3 →
          CoordinateUnlinkExteriorPlanarNeckLeftComplement m) =
        (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement
          m) ∘
          (coordinateUnlinkExteriorPlanarNeckGridDiagram
            m).verticalCenterToLeft ∘
            (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph
              m).symm := by
    funext x
    rfl
  rw [heq]
  have h :=
    (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement
      m).isClosedEmbedding.comp <|
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckGridVerticalCenterToLeft
        m).comp
          (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph
            m).symm.isClosedEmbedding
  exact h

/-- The right attaching map of the literal neck star is a closed embedding. -/
theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToRight
    (m : ℕ) [NeZero m] :
    IsClosedEmbedding (coordinateUnlinkExteriorPlanarNeckStarToRight m) := by
  have heq :
      (coordinateUnlinkExteriorPlanarNeckStarToRight m :
        ZMod m × Sphere 3 →
          CoordinateUnlinkExteriorPlanarNeckRightComplement m) =
        (coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement
          m) ∘
          (coordinateUnlinkExteriorPlanarNeckGridDiagram
            m).verticalCenterToRight ∘
            (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph
              m).symm := by
    funext x
    rfl
  rw [heq]
  have h :=
    (coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement
      m).isClosedEmbedding.comp <|
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckGridVerticalCenterToRight
        m).comp
          (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph
            m).symm.isClosedEmbedding
  exact h

/-- The common image of the full labelled neck family in the literal star. -/
abbrev coordinateUnlinkExteriorPlanarNeckStarSeam
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorPlanarNeckStar m) :=
  topologicalPushoutSeam
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)

/-- The part of the labelled left complement away from the full neck family. -/
abbrev coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorPlanarNeckStar m) :=
  topologicalPushoutInlOffSeam
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)

/-- The part of the central right complement away from the full neck family. -/
abbrev coordinateUnlinkExteriorPlanarNeckStarRightOffSeam
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorPlanarNeckStar m) :=
  topologicalPushoutInrOffSeam
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)

theorem isOpen_coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam
    (m : ℕ) [NeZero m] :
    IsOpen (coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam m) :=
  isOpen_topologicalPushoutInlOffSeam
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToRight m)

theorem isOpen_coordinateUnlinkExteriorPlanarNeckStarRightOffSeam
    (m : ℕ) [NeZero m] :
    IsOpen (coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m) :=
  isOpen_topologicalPushoutInrOffSeam
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToRight m)

theorem disjoint_coordinateUnlinkExteriorPlanarNeckStarOffSeam
    (m : ℕ) [NeZero m] :
    Disjoint (coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam m)
      (coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m) :=
  disjoint_topologicalPushoutOffSeam
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m).injective

theorem union_coordinateUnlinkExteriorPlanarNeckStarOffSeam
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam m ∪
        coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m =
      (coordinateUnlinkExteriorPlanarNeckStarSeam m)ᶜ :=
  union_topologicalPushoutOffSeam
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m).injective
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToRight m).injective

/-! ## Comparison with the original neck family -/

/-- The carrier of the original labelled family of neck three-spheres. -/
def coordinateUnlinkExteriorPlanarNeckSphereFamilyCarrier
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m) :=
  range (coordinateUnlinkExteriorPlanarNeckSphereFamily m)

/-- The flower-to-star homeomorphism sends the old neck family pointwise to the normalized
star seam, with its label and sphere parameter unchanged. -/
@[simp]
theorem
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar_neckSphereFamily
    (m : ℕ) [NeZero m] (x : ZMod m × Sphere 3) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
        (coordinateUnlinkExteriorPlanarNeckSphereFamily m x) =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m x) := by
  change
    coordinateUnlinkExteriorPlanarNeckGridColumnFirstHomeomorphStar m
        (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst
          m (coordinateUnlinkExteriorPlanarNeckSphereFamily m x)) = _
  rw [coordinateUnlinkExteriorPlanarNeckSphereFamily_regrouping_left,
    coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyLeft_apply,
    coordinateUnlinkExteriorPlanarNeckGridColumnFirstHomeomorphStar_inl]
  rfl

/-- The carrier of the original family is carried exactly onto the full star seam. -/
theorem
    image_coordinateUnlinkExteriorPlanarNeckSphereFamilyCarrier_homeomorphNeckStar
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m ''
        coordinateUnlinkExteriorPlanarNeckSphereFamilyCarrier m =
      coordinateUnlinkExteriorPlanarNeckStarSeam m := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x,
      coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar_neckSphereFamily
        m x |>.symm⟩
  · rintro ⟨x, rfl⟩
    exact
      ⟨coordinateUnlinkExteriorPlanarNeckSphereFamily m x, ⟨x, rfl⟩,
        coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar_neckSphereFamily
          m x⟩

/-- Equivalently, the inverse image of the normalized seam is the original family carrier. -/
theorem
    preimage_coordinateUnlinkExteriorPlanarNeckStarSeam_homeomorphNeckStar
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m ⁻¹'
        coordinateUnlinkExteriorPlanarNeckStarSeam m =
      coordinateUnlinkExteriorPlanarNeckSphereFamilyCarrier m := by
  rw [←
    image_coordinateUnlinkExteriorPlanarNeckSphereFamilyCarrier_homeomorphNeckStar]
  exact
    (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar
      m).preimage_image _

/-- The left side of the old neck family, transported back from the literal star. -/
def coordinateUnlinkExteriorPlanarNeckSphereFamilyLeftSide
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m) :=
  coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m ⁻¹'
    coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam m

/-- The right side of the old neck family, transported back from the literal star. -/
def coordinateUnlinkExteriorPlanarNeckSphereFamilyRightSide
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m) :=
  coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m ⁻¹'
    coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m

theorem isOpen_coordinateUnlinkExteriorPlanarNeckSphereFamilyLeftSide
    (m : ℕ) [NeZero m] :
    IsOpen (coordinateUnlinkExteriorPlanarNeckSphereFamilyLeftSide m) :=
  (isOpen_coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam m).preimage
    (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar
      m).continuous

theorem isOpen_coordinateUnlinkExteriorPlanarNeckSphereFamilyRightSide
    (m : ℕ) [NeZero m] :
    IsOpen (coordinateUnlinkExteriorPlanarNeckSphereFamilyRightSide m) :=
  (isOpen_coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m).preimage
    (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar
      m).continuous

theorem disjoint_coordinateUnlinkExteriorPlanarNeckSphereFamilySides
    (m : ℕ) [NeZero m] :
    Disjoint (coordinateUnlinkExteriorPlanarNeckSphereFamilyLeftSide m)
      (coordinateUnlinkExteriorPlanarNeckSphereFamilyRightSide m) :=
  (disjoint_coordinateUnlinkExteriorPlanarNeckStarOffSeam m).preimage
    (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m)

theorem union_coordinateUnlinkExteriorPlanarNeckSphereFamilySides
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarNeckSphereFamilyLeftSide m ∪
        coordinateUnlinkExteriorPlanarNeckSphereFamilyRightSide m =
      (coordinateUnlinkExteriorPlanarNeckSphereFamilyCarrier m)ᶜ := by
  rw [coordinateUnlinkExteriorPlanarNeckSphereFamilyLeftSide,
    coordinateUnlinkExteriorPlanarNeckSphereFamilyRightSide,
    ← preimage_union,
    union_coordinateUnlinkExteriorPlanarNeckStarOffSeam,
    preimage_compl,
    preimage_coordinateUnlinkExteriorPlanarNeckStarSeam_homeomorphNeckStar]

/-- Opposite transported sides of the old full neck family lie in distinct relative connected
components of its complement. -/
theorem
    connectedComponentIn_ne_of_mem_coordinateUnlinkExteriorPlanarNeckSphereFamilySides
    (m : ℕ) [NeZero m]
    (x y : CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m)
    (hxCarrier : x ∉ coordinateUnlinkExteriorPlanarNeckSphereFamilyCarrier m)
    (hyCarrier : y ∉ coordinateUnlinkExteriorPlanarNeckSphereFamilyCarrier m)
    (hx : x ∈ coordinateUnlinkExteriorPlanarNeckSphereFamilyLeftSide m)
    (hy : y ∈ coordinateUnlinkExteriorPlanarNeckSphereFamilyRightSide m) :
    connectedComponentIn
        (coordinateUnlinkExteriorPlanarNeckSphereFamilyCarrier m)ᶜ x ≠
      connectedComponentIn
        (coordinateUnlinkExteriorPlanarNeckSphereFamilyCarrier m)ᶜ y := by
  let H :=
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
  have hxStar : H x ∉ coordinateUnlinkExteriorPlanarNeckStarSeam m := by
    intro h
    apply hxCarrier
    have : x ∈ H ⁻¹' coordinateUnlinkExteriorPlanarNeckStarSeam m := h
    rwa [preimage_coordinateUnlinkExteriorPlanarNeckStarSeam_homeomorphNeckStar]
      at this
  have hyStar : H y ∉ coordinateUnlinkExteriorPlanarNeckStarSeam m := by
    intro h
    apply hyCarrier
    have : y ∈ H ⁻¹' coordinateUnlinkExteriorPlanarNeckStarSeam m := h
    rwa [preimage_coordinateUnlinkExteriorPlanarNeckStarSeam_homeomorphNeckStar]
      at this
  have htarget :=
    connectedComponentIn_ne_of_mem_topologicalPushoutOffSeam
      (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
      (coordinateUnlinkExteriorPlanarNeckStarToRight m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToRight m)
      (H x) (H y) hxStar hyStar hx hy
  intro hsource
  apply htarget
  have himage := congrArg (fun s : Set
      (CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m) ↦ H '' s) hsource
  rw [H.image_connectedComponentIn (show
      x ∈ (coordinateUnlinkExteriorPlanarNeckSphereFamilyCarrier m)ᶜ from hxCarrier),
    H.image_connectedComponentIn (show
      y ∈ (coordinateUnlinkExteriorPlanarNeckSphereFamilyCarrier m)ᶜ from hyCarrier)]
    at himage
  have hcompl :
      H '' (coordinateUnlinkExteriorPlanarNeckSphereFamilyCarrier m)ᶜ =
        (coordinateUnlinkExteriorPlanarNeckStarSeam m)ᶜ := by
    rw [H.image_compl,
      image_coordinateUnlinkExteriorPlanarNeckSphereFamilyCarrier_homeomorphNeckStar]
  rwa [hcompl] at himage

/-- Opposite off-seam points lie in distinct relative connected components after removing the
whole labelled neck family. -/
theorem connectedComponentIn_ne_of_mem_coordinateUnlinkExteriorPlanarNeckStarOffSeam
    (m : ℕ) [NeZero m]
    (x y : CoordinateUnlinkExteriorPlanarNeckStar m)
    (hxSeam : x ∉ coordinateUnlinkExteriorPlanarNeckStarSeam m)
    (hySeam : y ∉ coordinateUnlinkExteriorPlanarNeckStarSeam m)
    (hx : x ∈ coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam m)
    (hy : y ∈ coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m) :
    connectedComponentIn
        (coordinateUnlinkExteriorPlanarNeckStarSeam m)ᶜ x ≠
      connectedComponentIn
        (coordinateUnlinkExteriorPlanarNeckStarSeam m)ᶜ y :=
  connectedComponentIn_ne_of_mem_topologicalPushoutOffSeam
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToRight m)
    x y hxSeam hySeam hx hy

end SplittingSpheres
