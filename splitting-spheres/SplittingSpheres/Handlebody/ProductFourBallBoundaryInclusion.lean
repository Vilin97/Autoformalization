/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.ProductFourBoundaryAttachment

/-!
# The standard three-sphere as the boundary of the product four-ball

The boundary of `D¹ × B³` was previously recognized as the project's literal `Sphere 3`.
This file records the resulting canonical inclusion into the product four-ball, its exact
range, and its formulas on the two faces of the boundary pushout.

Everything here is topological.  No smooth boundary structure or collar is asserted.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-- Include the standard three-sphere as the model boundary of the product four-ball
`D¹ × B³`. -/
def productFourSphereBoundaryInclusion : C(Sphere 3, ProductFourBall) where
  toFun s := (productFourBallBoundaryHomeomorphSphere.symm s).1
  continuous_toFun :=
    continuous_subtype_val.comp productFourBallBoundaryHomeomorphSphere.symm.continuous

@[simp]
theorem productFourSphereBoundaryInclusion_apply (s : Sphere 3) :
    productFourSphereBoundaryInclusion s =
      (productFourBallBoundaryHomeomorphSphere.symm s).1 :=
  rfl

/-- The boundary inclusion is injective. -/
theorem injective_productFourSphereBoundaryInclusion :
    Injective productFourSphereBoundaryInclusion :=
  Subtype.val_injective.comp productFourBallBoundaryHomeomorphSphere.symm.injective

/-- The boundary inclusion is a closed topological embedding. -/
theorem isClosedEmbedding_productFourSphereBoundaryInclusion :
    IsClosedEmbedding productFourSphereBoundaryInclusion :=
  productFourSphereBoundaryInclusion.continuous.isClosedEmbedding
    injective_productFourSphereBoundaryInclusion

/-- The boundary inclusion is a topological embedding. -/
theorem isEmbedding_productFourSphereBoundaryInclusion :
    IsEmbedding productFourSphereBoundaryInclusion :=
  isClosedEmbedding_productFourSphereBoundaryInclusion.isEmbedding

/-- The image of the standard sphere is exactly the model boundary of `D¹ × B³`. -/
theorem range_productFourSphereBoundaryInclusion :
    range productFourSphereBoundaryInclusion =
      productFourBallModel.boundary ProductFourBall := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact (productFourBallBoundaryHomeomorphSphere.symm s).2
  · intro hx
    let y : ProductFourBallBoundary := ⟨x, hx⟩
    refine ⟨productFourBallBoundaryHomeomorphSphere y, ?_⟩
    change (productFourBallBoundaryHomeomorphSphere.symm
      (productFourBallBoundaryHomeomorphSphere y)).1 = x
    rw [productFourBallBoundaryHomeomorphSphere.symm_apply_apply]

/-- The complement of the embedded sphere is exactly the model interior of the product
four-ball. -/
theorem compl_range_productFourSphereBoundaryInclusion :
    (range productFourSphereBoundaryInclusion)ᶜ =
      productFourBallModel.interior ProductFourBall := by
  rw [range_productFourSphereBoundaryInclusion,
    ModelWithCorners.compl_boundary]

/-- The standard sphere inclusion agrees exactly with the boundary-pushout realization. -/
@[simp]
theorem productFourSphereBoundaryInclusion_pushout
    (x : ProductFourBoundaryPushout) :
    productFourSphereBoundaryInclusion
        (productFourBoundaryPushoutHomeomorphSphere x) =
      (productFourBoundaryPushoutHomeomorph x).1 := by
  change (productFourBallBoundaryHomeomorphSphere.symm
      (productFourBallBoundaryHomeomorphSphere
        (productFourBoundaryPushoutHomeomorph x))).1 = _
  rw [productFourBallBoundaryHomeomorphSphere.symm_apply_apply]

/-- Exact formula on the `D¹ × S²` side face. -/
@[simp]
theorem productFourSphereBoundaryInclusion_side
    (x : ProductFourSidePiece) :
    productFourSphereBoundaryInclusion
        (productFourBoundaryPushoutHomeomorphSphere
          (topologicalPushoutInl productFourCornerToSide productFourCornerToEnd x)) =
      (x.1, ⟨x.2.1, sphere_subset_closedBall x.2.2⟩) := by
  rw [productFourSphereBoundaryInclusion_pushout,
    productFourBoundaryPushoutHomeomorph_inl,
    productFourSideToBoundary_apply_val]

/-- Exact formula on the `S⁰ × B³` end face. -/
@[simp]
theorem productFourSphereBoundaryInclusion_end
    (x : ProductFourEndPiece) :
    productFourSphereBoundaryInclusion
        (productFourBoundaryPushoutHomeomorphSphere
          (topologicalPushoutInr productFourCornerToSide productFourCornerToEnd x)) =
      (⟨x.1.1, sphere_subset_closedBall x.1.2⟩, x.2) := by
  rw [productFourSphereBoundaryInclusion_pushout,
    productFourBoundaryPushoutHomeomorph_inr,
    productFourEndToBoundary_apply_val]

end SplittingSpheres
