/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Instances.ZMod
public import SplittingSpheres.Handlebody.ProductFourBallBoundaryInclusion

/-!
# Comparing the product and Euclidean four-balls

The convex product body `D¹ × B³` was previously rescaled to the Euclidean unit ball in order to
identify its boundary with `Sphere 3`.  This file restricts that same ambient rescaling to the
whole compact body.  The resulting homeomorphism agrees exactly with the established boundary
parametrizations, both forward and backward, and is applied componentwise to labelled families.

This is a point-set comparison only.  In particular, no diffeomorphism between the product model
with corners and the direct common-model Euclidean-ball atlas is asserted.
-/

@[expose] public section

open Function Metric Set Topology
open scoped Topology

noncomputable section

namespace SplittingSpheres

/-- Transport the product body from product coordinates into Euclidean four-space. -/
def productFourBallBodyHomeomorphEuclidean :
    (productFourBallBody : Set ProductFourAmbient) ≃ₜ
      productFourBallEuclideanBody :=
  (Homeomorph.image productFourBallSplitEquiv.toHomeomorph.symm
    productFourBallBody).trans
      (Homeomorph.setCongr productFourBallSplitEquiv_symm_image_body)

/-- Restrict the ambient gauge rescaling to a homeomorphism from the transported product body to
the Euclidean closed unit four-ball. -/
def productFourBallEuclideanBodyHomeomorphClosedBall :
    productFourBallEuclideanBody ≃ₜ EuclideanFourBall :=
  (Homeomorph.image productFourBallGaugeHomeomorph
    productFourBallEuclideanBody).trans
      (Homeomorph.setCongr productFourBallGaugeHomeomorph_image_body)

/-- The full product four-ball is homeomorphic to the literal Euclidean closed four-ball. -/
def productFourBallHomeomorphEuclideanFourBall :
    ProductFourBall ≃ₜ EuclideanFourBall :=
  productFourBallBodyHomeomorph.trans <|
    productFourBallBodyHomeomorphEuclidean.trans
      productFourBallEuclideanBodyHomeomorphClosedBall

/-- The underlying Euclidean coordinate of the comparison is the established gauge rescaling. -/
@[simp]
theorem productFourBallHomeomorphEuclideanFourBall_apply_val
    (x : ProductFourBall) :
    (productFourBallHomeomorphEuclideanFourBall x :
      ProductFourEuclideanAmbient) =
      productFourBallGaugeHomeomorph
        (productFourBallSplitEquiv.symm (x.1.1, x.2.1)) :=
  rfl

/-- On the product model boundary, the full comparison has the established spherical
coordinate. -/
theorem productFourBallHomeomorphEuclideanFourBall_boundary_coe
    (x : ProductFourBallBoundary) :
    (productFourBallHomeomorphEuclideanFourBall x.1 :
      ProductFourEuclideanAmbient) =
      productFourBallBoundaryHomeomorphSphere x := by
  rfl

/-- The comparison carries the standard product-ball boundary inclusion to the literal
Euclidean-ball boundary inclusion with the same sphere parameter. -/
theorem productFourBallHomeomorphEuclideanFourBall_boundary_inclusion
    (s : Sphere 3) :
    productFourBallHomeomorphEuclideanFourBall
        (productFourSphereBoundaryInclusion s) =
      (euclideanFourBallBoundaryHomeomorphSphereThree.symm s).1 := by
  apply Subtype.ext
  let x : ProductFourBallBoundary :=
    productFourBallBoundaryHomeomorphSphere.symm s
  change (productFourBallHomeomorphEuclideanFourBall x.1 :
      ProductFourEuclideanAmbient) =
    ((euclideanFourBallBoundaryHomeomorphSphereThree.symm s).1 :
      ProductFourEuclideanAmbient)
  rw [productFourBallHomeomorphEuclideanFourBall_boundary_coe]
  calc
    (productFourBallBoundaryHomeomorphSphere x :
        ProductFourEuclideanAmbient) = s :=
      congrArg Subtype.val
        (productFourBallBoundaryHomeomorphSphere.apply_symm_apply s)
    _ = ((euclideanFourBallBoundaryHomeomorphSphereThree.symm s).1 :
        ProductFourEuclideanAmbient) :=
      by
        change (s : ProductFourEuclideanAmbient) =
          (((closedUnitBallBoundaryHomeomorph
            ProductFourEuclideanAmbient).symm s).1.1 :
              ProductFourEuclideanAmbient)
        exact (closedUnitBallBoundaryHomeomorph_symm_apply_val
          ProductFourEuclideanAmbient s).symm

/-- The inverse comparison carries the Euclidean boundary inclusion back to the standard
product-ball boundary inclusion with the same sphere parameter. -/
theorem productFourBallHomeomorphEuclideanFourBall_symm_boundary_inclusion
    (s : Sphere 3) :
    productFourBallHomeomorphEuclideanFourBall.symm
        (euclideanFourBallBoundaryHomeomorphSphereThree.symm s).1 =
      productFourSphereBoundaryInclusion s := by
  apply productFourBallHomeomorphEuclideanFourBall.injective
  rw [productFourBallHomeomorphEuclideanFourBall.apply_symm_apply,
    productFourBallHomeomorphEuclideanFourBall_boundary_inclusion]

/-- Apply the product-to-Euclidean comparison independently in every discrete labelled sheet. -/
def productFourBallFamilyHomeomorphEuclideanFourBall (m : ℕ) :
    ZMod m × ProductFourBall ≃ₜ ZMod m × EuclideanFourBall :=
  (Homeomorph.refl (ZMod m)).prodCongr
    productFourBallHomeomorphEuclideanFourBall

/-- The labelled comparison preserves the label and applies the ball comparison. -/
@[simp]
theorem productFourBallFamilyHomeomorphEuclideanFourBall_apply
    (m : ℕ) (p : ZMod m × ProductFourBall) :
    productFourBallFamilyHomeomorphEuclideanFourBall m p =
      (p.1, productFourBallHomeomorphEuclideanFourBall p.2) :=
  rfl

/-- The inverse labelled comparison preserves the label and applies the inverse ball
comparison. -/
@[simp]
theorem productFourBallFamilyHomeomorphEuclideanFourBall_symm_apply
    (m : ℕ) (p : ZMod m × EuclideanFourBall) :
    (productFourBallFamilyHomeomorphEuclideanFourBall m).symm p =
      (p.1, productFourBallHomeomorphEuclideanFourBall.symm p.2) :=
  rfl

/-- The labelled comparison carries every standard product-cap attaching point to the Euclidean
attaching point with the same label and sphere parameter. -/
theorem productFourBallFamilyHomeomorphEuclideanFourBall_boundary_inclusion
    (m : ℕ) (p : ZMod m × Sphere 3) :
    productFourBallFamilyHomeomorphEuclideanFourBall m
        (p.1, productFourSphereBoundaryInclusion p.2) =
      (p.1, (euclideanFourBallBoundaryHomeomorphSphereThree.symm p.2).1) := by
  rw [productFourBallFamilyHomeomorphEuclideanFourBall_apply,
    productFourBallHomeomorphEuclideanFourBall_boundary_inclusion]

/-- The inverse labelled comparison carries every Euclidean attaching point to the standard
product-cap attaching point with the same label and sphere parameter. -/
theorem productFourBallFamilyHomeomorphEuclideanFourBall_symm_boundary_inclusion
    (m : ℕ) (p : ZMod m × Sphere 3) :
    (productFourBallFamilyHomeomorphEuclideanFourBall m).symm
        (p.1, (euclideanFourBallBoundaryHomeomorphSphereThree.symm p.2).1) =
      (p.1, productFourSphereBoundaryInclusion p.2) := by
  rw [productFourBallFamilyHomeomorphEuclideanFourBall_symm_apply,
    productFourBallHomeomorphEuclideanFourBall_symm_boundary_inclusion]

end SplittingSpheres

end
