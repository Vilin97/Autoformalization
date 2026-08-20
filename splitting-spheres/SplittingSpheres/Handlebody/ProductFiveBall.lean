/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import SplittingSpheres.Geometry.ClosedBall
public import SplittingSpheres.Statement

/-!
# The product five-ball

This file packages the convex product body `D² × B³`.  Its product model with corners
has the expected two boundary faces.  We then identify its model-boundary subtype topologically
with the standard four-sphere.

There is a genuine norm issue in this construction: Mathlib equips a product of normed spaces with
the supremum norm, whereas `Sphere 4` uses the Euclidean norm on `ℝ⁵`.  We therefore first
transport the product body to Euclidean five-space through `EuclideanSpace.finAddEquivProd`, and
then use the convex gauge-rescaling homeomorphism to send its frontier to the Euclidean unit
sphere.

Everything here is topological.  In particular, no induced smooth structure on a boundary
subtype, smooth boundary diffeomorphism, boundary flattening, or half-space-model equivalence is
asserted.
-/

@[expose] public section

open Bornology Function Metric Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace SplittingSpheres

/-- The ambient product vector space of the convex body `D² × B³`.

Its norm is Mathlib's product supremum norm. -/
abbrev ProductFiveAmbient : Type :=
  EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3)

/-- Euclidean five-space, used for the literal target `Sphere 4`. -/
abbrev ProductFiveEuclideanAmbient : Type :=
  EuclideanSpace ℝ (Fin 5)

/-- The compact product body `D² × B³`. -/
abbrev ProductFiveBall : Type :=
  EuclideanClosedBall 2 × EuclideanClosedBall 3

/-- The tagged coordinate space of the product model. -/
abbrev ProductFiveBallModelSpace : Type :=
  ModelProd (EuclideanClosedBall 2) (EuclideanClosedBall 3)

/-- The product convex-range model with corners on `D² × B³`. -/
abbrev productFiveBallModel :
    ModelWithCorners ℝ ProductFiveAmbient ProductFiveBallModelSpace :=
  (euclideanClosedBallModel 2).prod (euclideanClosedBallModel 3)

/-- The model vector space of the product body has dimension five. -/
theorem productFiveBallModel_finrank :
    Module.finrank ℝ ProductFiveAmbient = 5 := by
  simp [ProductFiveAmbient]

/-- The product body is a manifold with corners to every regularity. -/
theorem isManifold_productFiveBall (n : ℕ∞ω) :
    IsManifold productFiveBallModel n ProductFiveBall :=
  inferInstance

/-- The literal two-face subset of `D² × B³`. -/
def productFiveBallBoundarySet : Set ProductFiveBall :=
  (univ : Set (EuclideanClosedBall 2)) ×ˢ
      (Subtype.val ⁻¹' sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∪
    (Subtype.val ⁻¹' sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ×ˢ
      (univ : Set (EuclideanClosedBall 3))

/-- The model boundary is exactly the union of its `D² × S²` and `S¹ × B³`
faces. -/
theorem productFiveBallModel_boundary :
    productFiveBallModel.boundary ProductFiveBall = productFiveBallBoundarySet := by
  rw [ModelWithCorners.boundary_prod, closedUnitBallModel_boundary,
    closedUnitBallModel_boundary]
  rfl

/-- The product of the two ambient closed unit balls. -/
def productFiveBallBody : Set ProductFiveAmbient :=
  closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ
    closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The ambient product body is closed. -/
theorem isClosed_productFiveBallBody : IsClosed productFiveBallBody :=
  isClosed_closedBall.prod isClosed_closedBall

/-- The ambient frontier of the product body is the union of its two faces. -/
theorem productFiveBallBody_frontier :
    frontier productFiveBallBody =
      closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ
          sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ∪
        sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ
          closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [productFiveBallBody, frontier_prod_eq,
    isClosed_closedBall.closure_eq, isClosed_closedBall.closure_eq,
    frontier_closedBall _ one_ne_zero, frontier_closedBall _ one_ne_zero]

/-- The product of ball subtypes is canonically homeomorphic to the subtype of their product
body. -/
def productFiveBallBodyHomeomorph :
    ProductFiveBall ≃ₜ ↥productFiveBallBody :=
  (Homeomorph.Set.prod
    (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)).symm

@[simp]
theorem productFiveBallBodyHomeomorph_apply_val (x : ProductFiveBall) :
    (productFiveBallBodyHomeomorph x : ProductFiveAmbient) = (x.1.1, x.2.1) :=
  rfl

@[simp]
theorem productFiveBallBodyHomeomorph_symm_apply_fst_val
    (x : ↥productFiveBallBody) :
    (productFiveBallBodyHomeomorph.symm x).1.1 = x.1.1 :=
  rfl

@[simp]
theorem productFiveBallBodyHomeomorph_symm_apply_snd_val
    (x : ↥productFiveBallBody) :
    (productFiveBallBodyHomeomorph.symm x).2.1 = x.1.2 :=
  rfl

/-- The model-boundary subtype is canonically homeomorphic to the ambient frontier subtype in
the product supremum norm. -/
def productFiveBallBoundaryHomeomorphFrontier :
    ↥(productFiveBallModel.boundary ProductFiveBall) ≃ₜ
      ↥(frontier productFiveBallBody) :=
  Homeomorph.mk
    { toFun := fun x ↦
        ⟨(x.1.1.1, x.1.2.1), by
          have hx : x.1 ∈ productFiveBallBoundarySet :=
            (Set.ext_iff.mp productFiveBallModel_boundary x.1).mp x.2
          apply (Set.ext_iff.mp productFiveBallBody_frontier _).mpr
          rcases hx with hx | hx
          · exact Or.inl ⟨x.1.1.2, hx.2⟩
          · exact Or.inr ⟨hx.1, x.1.2.2⟩⟩
      invFun := fun y ↦
        ⟨(⟨y.1.1, by
              have hy : y.1 ∈ productFiveBallBody := by
                exact (Set.ext_iff.mp isClosed_productFiveBallBody.closure_eq y.1).mp
                  (frontier_subset_closure y.2)
              exact hy.1⟩,
            ⟨y.1.2, by
              have hy : y.1 ∈ productFiveBallBody := by
                exact (Set.ext_iff.mp isClosed_productFiveBallBody.closure_eq y.1).mp
                  (frontier_subset_closure y.2)
              exact hy.2⟩), by
          apply (Set.ext_iff.mp productFiveBallModel_boundary _).mpr
          have hy := (Set.ext_iff.mp productFiveBallBody_frontier y.1).mp y.2
          rcases hy with hy | hy
          · exact Or.inl ⟨mem_univ _, hy.2⟩
          · exact Or.inr ⟨hy.1, mem_univ _⟩⟩
      left_inv := fun x ↦ by
        apply Subtype.ext
        exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
      right_inv := fun y ↦ by
        apply Subtype.ext
        rfl }
    (by fun_prop)
    (by fun_prop)

@[simp]
theorem productFiveBallBoundaryHomeomorphFrontier_apply_val
    (x : ↥(productFiveBallModel.boundary ProductFiveBall)) :
    (productFiveBallBoundaryHomeomorphFrontier x : ProductFiveAmbient) =
      (x.1.1.1, x.1.2.1) :=
  rfl

/-- The canonical linear homeomorphism from Euclidean five-space to the product ambient space.

This is a continuous linear equivalence, not an isometry for the product supremum norm. -/
abbrev productFiveBallSplitEquiv :
    ProductFiveEuclideanAmbient ≃L[ℝ] ProductFiveAmbient :=
  EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 3)

/-- The product body transported into Euclidean five-space. -/
def productFiveBallEuclideanBody : Set ProductFiveEuclideanAmbient :=
  productFiveBallSplitEquiv ⁻¹' productFiveBallBody

/-- Applying the inverse splitting equivalence to the product body gives its Euclidean
transport. -/
theorem productFiveBallSplitEquiv_symm_image_body :
    productFiveBallSplitEquiv.symm '' productFiveBallBody =
      productFiveBallEuclideanBody := by
  exact congrFun productFiveBallSplitEquiv.toHomeomorph.image_symm productFiveBallBody

/-- The splitting equivalence carries the product frontier to the frontier of the transported
Euclidean body. -/
theorem productFiveBallSplitEquiv_symm_image_frontier :
    productFiveBallSplitEquiv.symm '' frontier productFiveBallBody =
      frontier productFiveBallEuclideanBody := by
  calc
    productFiveBallSplitEquiv.symm '' frontier productFiveBallBody =
        frontier (productFiveBallSplitEquiv.symm '' productFiveBallBody) :=
      productFiveBallSplitEquiv.toHomeomorph.symm.image_frontier _
    _ = frontier productFiveBallEuclideanBody := by
      rw [productFiveBallSplitEquiv_symm_image_body]

/-- The product frontier transported to Euclidean five-space. -/
def productFiveBallFrontierHomeomorphEuclidean :
    ↥(frontier productFiveBallBody) ≃ₜ
      ↥(frontier productFiveBallEuclideanBody) :=
  (Homeomorph.image productFiveBallSplitEquiv.toHomeomorph.symm
    (frontier productFiveBallBody)).trans
      (Homeomorph.setCongr productFiveBallSplitEquiv_symm_image_frontier)

@[simp]
theorem productFiveBallFrontierHomeomorphEuclidean_apply_val
    (x : ↥(frontier productFiveBallBody)) :
    (productFiveBallFrontierHomeomorphEuclidean x :
      ProductFiveEuclideanAmbient) = productFiveBallSplitEquiv.symm x.1 :=
  rfl

/-- The transported Euclidean body is convex. -/
theorem convex_productFiveBallEuclideanBody :
    Convex ℝ productFiveBallEuclideanBody := by
  exact ((convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).prod
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)).linear_preimage
      productFiveBallSplitEquiv.toLinearMap

/-- The transported Euclidean body is a neighbourhood of the origin. -/
theorem productFiveBallEuclideanBody_mem_nhds :
    productFiveBallEuclideanBody ∈ 𝓝 (0 : ProductFiveEuclideanAmbient) := by
  apply productFiveBallSplitEquiv.continuous.continuousAt.preimage_mem_nhds
  change productFiveBallBody ∈
    𝓝 ((0 : EuclideanSpace ℝ (Fin 2)), (0 : EuclideanSpace ℝ (Fin 3)))
  exact prod_mem_nhds
    (closedBall_mem_nhds (0 : EuclideanSpace ℝ (Fin 2)) one_pos)
    (closedBall_mem_nhds (0 : EuclideanSpace ℝ (Fin 3)) one_pos)

/-- The transported Euclidean body is bounded. -/
theorem isBounded_productFiveBallEuclideanBody :
    IsBounded productFiveBallEuclideanBody := by
  exact productFiveBallSplitEquiv.antilipschitz.isBounded_preimage
    (isBounded_closedBall.prod isBounded_closedBall)

/-- The transported Euclidean body is von Neumann bounded. -/
theorem isVonNBounded_productFiveBallEuclideanBody :
    IsVonNBounded ℝ productFiveBallEuclideanBody :=
  NormedSpace.isVonNBounded_of_isBounded ℝ
    isBounded_productFiveBallEuclideanBody

/-- The transported Euclidean body is closed. -/
theorem isClosed_productFiveBallEuclideanBody :
    IsClosed productFiveBallEuclideanBody :=
  isClosed_productFiveBallBody.preimage productFiveBallSplitEquiv.continuous

/-- Radial gauge rescaling from the transported product body to the Euclidean closed unit ball. -/
def productFiveBallGaugeHomeomorph :
    ProductFiveEuclideanAmbient ≃ₜ ProductFiveEuclideanAmbient :=
  gaugeRescaleHomeomorph productFiveBallEuclideanBody
    (closedBall (0 : ProductFiveEuclideanAmbient) 1)
    convex_productFiveBallEuclideanBody
    productFiveBallEuclideanBody_mem_nhds
    isVonNBounded_productFiveBallEuclideanBody
    (convex_closedBall 0 1)
    (closedBall_mem_nhds 0 one_pos)
    (NormedSpace.isVonNBounded_closedBall ℝ ProductFiveEuclideanAmbient 1)

/-- Gauge rescaling sends the transported product body onto the Euclidean closed unit ball. -/
theorem productFiveBallGaugeHomeomorph_image_body :
    productFiveBallGaugeHomeomorph '' productFiveBallEuclideanBody =
      closedBall (0 : ProductFiveEuclideanAmbient) 1 := by
  simpa [productFiveBallGaugeHomeomorph,
    isClosed_productFiveBallEuclideanBody.closure_eq,
    isClosed_closedBall.closure_eq] using
    (image_gaugeRescaleHomeomorph_closure
      convex_productFiveBallEuclideanBody
      productFiveBallEuclideanBody_mem_nhds
      isVonNBounded_productFiveBallEuclideanBody
      (convex_closedBall (0 : ProductFiveEuclideanAmbient) 1)
      (closedBall_mem_nhds (0 : ProductFiveEuclideanAmbient) one_pos)
      (NormedSpace.isVonNBounded_closedBall ℝ ProductFiveEuclideanAmbient 1))

/-- Gauge rescaling sends the transported frontier onto the literal Euclidean unit sphere. -/
theorem productFiveBallGaugeHomeomorph_image_frontier :
    productFiveBallGaugeHomeomorph '' frontier productFiveBallEuclideanBody =
      sphere (0 : ProductFiveEuclideanAmbient) 1 := by
  rw [productFiveBallGaugeHomeomorph.image_frontier,
    productFiveBallGaugeHomeomorph_image_body,
    frontier_closedBall _ one_ne_zero]

/-- The literal model-boundary subtype of the product five-ball. -/
abbrev ProductFiveBallBoundary : Type :=
  ↥(productFiveBallModel.boundary ProductFiveBall)

/-- Gauge rescaling restricted to the frontier, with literal target `Sphere 4`. -/
def productFiveBallGaugeFrontierHomeomorph :
    ↥(frontier productFiveBallEuclideanBody) ≃ₜ Sphere 4 :=
  (Homeomorph.image productFiveBallGaugeHomeomorph
    (frontier productFiveBallEuclideanBody)).trans
      (Homeomorph.setCongr productFiveBallGaugeHomeomorph_image_frontier)

/-- The model-boundary subtype of `D² × B³` is homeomorphic to the standard
four-sphere. -/
def productFiveBallBoundaryHomeomorphSphere :
    ProductFiveBallBoundary ≃ₜ Sphere 4 :=
  productFiveBallBoundaryHomeomorphFrontier.trans <|
    productFiveBallFrontierHomeomorphEuclidean.trans
      productFiveBallGaugeFrontierHomeomorph

/-- Coordinate formula for the complete boundary-to-sphere homeomorphism. -/
@[simp]
theorem productFiveBallBoundaryHomeomorphSphere_apply_val
    (x : ProductFiveBallBoundary) :
    (productFiveBallBoundaryHomeomorphSphere x : ProductFiveEuclideanAmbient) =
      productFiveBallGaugeHomeomorph
        (productFiveBallSplitEquiv.symm (x.1.1.1, x.1.2.1)) :=
  rfl

end SplittingSpheres
