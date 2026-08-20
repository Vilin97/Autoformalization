/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutEmbedding
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckGridVerticalCenter

/-!
# Comparing the planar neck spheres with the central grid column

The original labelled neck-sphere family was defined before the planar flower was cut into
left and right pieces.  After the exact grid regrouping, this file identifies that family with
the common central-column attaching map.  The comparison retains the unevaluated endpoint
relabeling offset; in particular, it makes no cyclic-order claim.

As a point-set consequence, both attaching maps out of the central vertical pushout are closed
topological embeddings.  No smoothness, separation, capping, or connected-sum assertion is
made.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-! ## Two convenient forms of the common family -/

/-- The common central family, included through the left column. -/
def coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyLeft
    (m : ℕ) [NeZero m] :
    C(ZMod m × Sphere 3,
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).columnFirst) where
  toFun x :=
    topologicalPushoutInl
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight
      ((coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
        ((coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm x))
  continuous_toFun :=
    (topologicalPushoutInl
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight).continuous.comp <|
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft.continuous.comp
        (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm.continuous

/-- The common central family, included through the right column. -/
def coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyRight
    (m : ℕ) [NeZero m] :
    C(ZMod m × Sphere 3,
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).columnFirst) where
  toFun x :=
    topologicalPushoutInr
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight
      ((coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight
        ((coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm x))
  continuous_toFun :=
    (topologicalPushoutInr
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight).continuous.comp <|
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight.continuous.comp
        (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm.continuous

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyLeft_apply
    (m : ℕ) [NeZero m] (x : ZMod m × Sphere 3) :
    coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyLeft m x =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight
        ((coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
          ((coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm x)) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyRight_apply
    (m : ℕ) [NeZero m] (x : ZMod m × Sphere 3) :
    coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyRight m x =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight
        ((coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight
          ((coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm x)) :=
  rfl

/-! ## Inverse formulas on the two faces of the standard three-sphere -/

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_symm_side
    (m : ℕ) [NeZero m] (a : ZMod m) (x : ProductFourSidePiece) :
    (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm
        (a, productFourBoundaryPushoutHomeomorphSphere
          (topologicalPushoutInl productFourCornerToSide productFourCornerToEnd x)) =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToTop
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToBottom
        ((a, euclideanClosedBallOneHomeomorphUnitInterval x.1), x.2) := by
  apply (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).injective
  rw [(coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).apply_symm_apply,
    coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_inr]
  rw [euclideanClosedBallOneHomeomorphUnitInterval.symm_apply_apply]

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_symm_end
    (m : ℕ) [NeZero m] (a : ZMod m) (x : ProductFourEndPiece) :
    (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm
        (a, productFourBoundaryPushoutHomeomorphSphere
          (topologicalPushoutInr productFourCornerToSide productFourCornerToEnd x)) =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToTop
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToBottom
        (((coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m).symm
          (a, x.1)), x.2) := by
  apply (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).injective
  rw [(coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).apply_symm_apply,
    coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_inl]
  have h := (coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m).apply_symm_apply
    (a, x.1)
  rw [coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph_apply] at h
  apply Prod.ext
  · exact (congrArg Prod.fst h).symm
  · apply congrArg productFourBoundaryPushoutHomeomorphSphere
    apply congrArg (topologicalPushoutInr productFourCornerToSide productFourCornerToEnd)
    exact Prod.ext (congrArg Prod.snd h).symm rfl

/-! ## Exact comparison with the pre-cut neck family -/

/-- Before changing from the product-four pushout to the literal sphere, the old neck map is
the left-column copy of the central vertical pushout. -/
theorem coordinateUnlinkExteriorPlanarNeckBoundaryMap_regrouping_left
    (m : ℕ) [NeZero m] (a : ZMod m) (x : ProductFourBoundaryPushout) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
        (coordinateUnlinkExteriorPlanarNeckBoundaryMap m a x) =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight
        ((coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
          ((coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm
            (a, productFourBoundaryPushoutHomeomorphSphere x))) := by
  rcases topologicalPushout_jointly_surjective
      productFourCornerToSide productFourCornerToEnd x with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [coordinateUnlinkExteriorPlanarNeckBoundaryMap_inl,
      coordinateUnlinkExteriorPlanarNeckSideMap_apply,
      coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_symm_side,
      TopologicalPushoutGridDiagram.verticalCenterToLeft_inr]
    rw [show (coordinateUnlinkExteriorPlanarNeckGridDiagram m).bottomToBottomLeft
        ((a, euclideanClosedBallOneHomeomorphUnitInterval x.1), x.2) =
          (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m
            (a, euclideanClosedBallOneHomeomorphUnitInterval x.1), x.2) from rfl]
    change
      coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
          (partialSphereSpinInr (coordinateUnlinkExteriorPlanarFlowerOuter m)
            (coordinateUnlinkExteriorPlanarNeckArcTranslate m a
              (euclideanClosedBallOneHomeomorphUnitInterval x.1), x.2)) =
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).columnFirstBottomLeft
          (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m
            (a, euclideanClosedBallOneHomeomorphUnitInterval x.1), x.2)
    simpa only [coordinateUnlinkExteriorPlanarNormalizedLeftSeam_conjugacy,
      coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion_apply,
      coordinateUnlinkExteriorPlanarNeckArcToLeftHalf_val,
      coordinateUnlinkExteriorPlanarNeckArcFamily_apply] using
        coordinateUnlinkExteriorPlanarNeckGridRegrouping_bottomLeft_apply m
          (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m
            (a, euclideanClosedBallOneHomeomorphUnitInterval x.1)) x.2
  · let y :=
      (coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m).symm (a, x.1)
    have hy :
        ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m y).1, y.2) =
          (a, x.1) := by
      simpa only [y,
        coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph_apply] using
          (coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m).apply_symm_apply
            (a, x.1)
    rw [coordinateUnlinkExteriorPlanarNeckBoundaryMap_inr,
      coordinateUnlinkExteriorPlanarNeckEndMap_apply,
      coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_symm_end,
      TopologicalPushoutGridDiagram.verticalCenterToLeft_inl]
    rw [show (coordinateUnlinkExteriorPlanarNeckGridDiagram m).topToTopLeft
        (y, x.2) =
          (coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter m y, x.2) from rfl]
    change
      coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
          (partialSphereSpinInl (coordinateUnlinkExteriorPlanarFlowerOuter m)
            (coordinateUnlinkExteriorPlanarNeckOuterParameter m a x.1, x.2)) =
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).columnFirstTopLeft
          ((coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter m y), x.2)
    rw [← coordinateUnlinkExteriorPlanarLeftOuterSectorParameter_endpoint m a x.1,
      coordinateUnlinkExteriorPlanarNeckGridRegrouping_topLeft_apply]
    apply congrArg (coordinateUnlinkExteriorPlanarNeckGridDiagram m).columnFirstTopLeft
    apply Prod.ext
    · rw [coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter_apply]
      exact Prod.ext (congrArg Prod.fst hy).symm <|
        congrArg coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc
          (congrArg Prod.snd hy).symm
    · rfl

/-- The grid regrouping carries the previously defined joint family of neck spheres to the
central vertical family, viewed from the left column. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckSphereFamily_regrouping_left
    (m : ℕ) [NeZero m] (x : ZMod m × Sphere 3) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
        (coordinateUnlinkExteriorPlanarNeckSphereFamily m x) =
      coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyLeft m x := by
  change
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
        (coordinateUnlinkExteriorPlanarNeckBoundaryMap m x.1
          (productFourBoundaryPushoutHomeomorphSphere.symm x.2)) =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight
        ((coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
          ((coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm x))
  rw [coordinateUnlinkExteriorPlanarNeckBoundaryMap_regrouping_left,
    productFourBoundaryPushoutHomeomorphSphere.apply_symm_apply]

/-- The two coprojections give the same common family, by the defining pushout relation. -/
theorem coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyLeft_eq_right
    (m : ℕ) [NeZero m] (x : ZMod m × Sphere 3) :
    coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyLeft m x =
      coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyRight m x := by
  rw [coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyLeft_apply,
    coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyRight_apply]
  exact topologicalPushout_condition
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight
    ((coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm x)

/-- Symmetric right-column form of the exact neck-family comparison. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckSphereFamily_regrouping_right
    (m : ℕ) [NeZero m] (x : ZMod m × Sphere 3) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
        (coordinateUnlinkExteriorPlanarNeckSphereFamily m x) =
      coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyRight m x :=
  (coordinateUnlinkExteriorPlanarNeckSphereFamily_regrouping_left m x).trans
    (coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyLeft_eq_right m x)

/-- Expanded left-column form of the comparison, with no wrapper around the attaching map. -/
theorem coordinateUnlinkExteriorPlanarNeckSphereFamily_regrouping_left_apply
    (m : ℕ) [NeZero m] (x : ZMod m × Sphere 3) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
        (coordinateUnlinkExteriorPlanarNeckSphereFamily m x) =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight
        ((coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
          ((coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm x)) := by
  rw [coordinateUnlinkExteriorPlanarNeckSphereFamily_regrouping_left,
    coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyLeft_apply]

/-- Expanded right-column form; equality with the left form is precisely the pushout
condition. -/
theorem coordinateUnlinkExteriorPlanarNeckSphereFamily_regrouping_right_apply
    (m : ℕ) [NeZero m] (x : ZMod m × Sphere 3) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
        (coordinateUnlinkExteriorPlanarNeckSphereFamily m x) =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight
        ((coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight
          ((coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm x)) := by
  rw [coordinateUnlinkExteriorPlanarNeckSphereFamily_regrouping_right,
    coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyRight_apply]

/-! ## Embedding consequences -/

theorem isEmbedding_coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyLeft
    (m : ℕ) [NeZero m] :
    IsEmbedding (coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyLeft m) := by
  have heq :
      (coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyLeft m :
          ZMod m × Sphere 3 →
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).columnFirst) =
        fun x ↦
          coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
            (coordinateUnlinkExteriorPlanarNeckSphereFamily m x) := by
    funext x
    exact (coordinateUnlinkExteriorPlanarNeckSphereFamily_regrouping_left m x).symm
  rw [heq]
  let H :=
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
  exact H.isEmbedding.comp (isEmbedding_coordinateUnlinkExteriorPlanarNeckSphereFamily m)

theorem isEmbedding_coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyRight
    (m : ℕ) [NeZero m] :
    IsEmbedding (coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyRight m) := by
  have heq :
      (coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyRight m :
          ZMod m × Sphere 3 →
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).columnFirst) =
        fun x ↦
          coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
            (coordinateUnlinkExteriorPlanarNeckSphereFamily m x) := by
    funext x
    exact (coordinateUnlinkExteriorPlanarNeckSphereFamily_regrouping_right m x).symm
  rw [heq]
  let H :=
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
  exact H.isEmbedding.comp (isEmbedding_coordinateUnlinkExteriorPlanarNeckSphereFamily m)

/-- The left attaching map from the common neck family into the left grid column is a
topological embedding. -/
theorem isEmbedding_coordinateUnlinkExteriorPlanarNeckGridVerticalCenterToLeft
    (m : ℕ) [NeZero m] :
    IsEmbedding
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  let V := coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m
  have hcomp : IsEmbedding (fun q : D.verticalCenter ↦
      topologicalPushoutInl D.verticalCenterToLeft D.verticalCenterToRight
        (D.verticalCenterToLeft q)) := by
    have h :=
      (isEmbedding_coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyLeft m).comp
        V.isEmbedding
    change IsEmbedding (fun q : D.verticalCenter ↦
      coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyLeft m (V q)) at h
    have heq :
        (fun q : D.verticalCenter ↦
          coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyLeft m (V q)) =
        fun q ↦ topologicalPushoutInl D.verticalCenterToLeft D.verticalCenterToRight
          (D.verticalCenterToLeft q) := by
      funext q
      rw [coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyLeft_apply,
        V.symm_apply_apply]
    rw [heq] at h
    exact h
  exact IsEmbedding.of_comp
    D.verticalCenterToLeft.continuous
    (topologicalPushoutInl D.verticalCenterToLeft D.verticalCenterToRight).continuous hcomp

/-- The right attaching map from the common neck family into the right grid column is a
topological embedding. -/
theorem isEmbedding_coordinateUnlinkExteriorPlanarNeckGridVerticalCenterToRight
    (m : ℕ) [NeZero m] :
    IsEmbedding
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  let V := coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m
  have hcomp : IsEmbedding (fun q : D.verticalCenter ↦
      topologicalPushoutInr D.verticalCenterToLeft D.verticalCenterToRight
        (D.verticalCenterToRight q)) := by
    have h :=
      (isEmbedding_coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyRight m).comp
        V.isEmbedding
    change IsEmbedding (fun q : D.verticalCenter ↦
      coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyRight m (V q)) at h
    have heq :
        (fun q : D.verticalCenter ↦
          coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyRight m (V q)) =
        fun q ↦ topologicalPushoutInr D.verticalCenterToLeft D.verticalCenterToRight
          (D.verticalCenterToRight q) := by
      funext q
      rw [coordinateUnlinkExteriorPlanarNeckGridCommonVerticalCenterFamilyRight_apply,
        V.symm_apply_apply]
    rw [heq] at h
    exact h
  exact IsEmbedding.of_comp
    D.verticalCenterToRight.continuous
    (topologicalPushoutInr D.verticalCenterToLeft D.verticalCenterToRight).continuous hcomp

/-! The targets of the two attaching maps need not carry global Hausdorff instances a priori.
They inherit them from their compact-to-Hausdorff coprojections into the recognized full grid. -/

theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckGridVerticalCenterToLeft
    (m : ℕ) [NeZero m] :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  let H :=
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
  let _ : T2Space (CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m) :=
    (coordinateUnlinkExteriorPlanarFlowerSpinCapComplementHomeomorphSphere m).symm.t2Space
  let _ : T2Space D.columnFirst := H.t2Space
  have hright :=
    isEmbedding_coordinateUnlinkExteriorPlanarNeckGridVerticalCenterToRight m
  have hinl : IsClosedEmbedding
      (topologicalPushoutInl D.verticalCenterToLeft D.verticalCenterToRight) :=
    isClosedEmbedding_topologicalPushoutInl_of_compact_t2
      D.verticalCenterToLeft D.verticalCenterToRight hright.injective
  let _ : T2Space D.verticalLeft := hinl.isEmbedding.t2Space
  exact D.verticalCenterToLeft.continuous.isClosedEmbedding
    (isEmbedding_coordinateUnlinkExteriorPlanarNeckGridVerticalCenterToLeft m).injective

theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckGridVerticalCenterToRight
    (m : ℕ) [NeZero m] :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  let H :=
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
  let _ : T2Space (CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m) :=
    (coordinateUnlinkExteriorPlanarFlowerSpinCapComplementHomeomorphSphere m).symm.t2Space
  let _ : T2Space D.columnFirst := H.t2Space
  have hleft :=
    isEmbedding_coordinateUnlinkExteriorPlanarNeckGridVerticalCenterToLeft m
  have hinr : IsClosedEmbedding
      (topologicalPushoutInr D.verticalCenterToLeft D.verticalCenterToRight) :=
    isClosedEmbedding_topologicalPushoutInr_of_compact_t2
      D.verticalCenterToLeft D.verticalCenterToRight hleft.injective
  let _ : T2Space D.verticalRight := hinr.isEmbedding.t2Space
  exact D.verticalCenterToRight.continuous.isClosedEmbedding
    (isEmbedding_coordinateUnlinkExteriorPlanarNeckGridVerticalCenterToRight m).injective

end SplittingSpheres
