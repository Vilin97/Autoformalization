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
# The product four-ball

This file packages the convex product body `D¹ × B³`.  Its product model with corners has the
expected two boundary faces, and its model-boundary subtype is identified topologically with the
standard three-sphere.

Mathlib gives a product of normed spaces the supremum norm, whereas `Sphere 3` uses the Euclidean
norm on `ℝ⁴`.  We therefore transport the product body through
`EuclideanSpace.finAddEquivProd` and then use convex gauge rescaling.  Everything here is
topological; no smooth boundary or gluing assertion is made.
-/

@[expose] public section

open Bornology Function Metric Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace SplittingSpheres

/-- The ambient product vector space of `D¹ × B³`, carrying the product supremum norm. -/
abbrev ProductFourAmbient : Type :=
  EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)

/-- Euclidean four-space, used for the literal target `Sphere 3`. -/
abbrev ProductFourEuclideanAmbient : Type :=
  EuclideanSpace ℝ (Fin 4)

/-- The compact product body `D¹ × B³`. -/
abbrev ProductFourBall : Type :=
  EuclideanClosedBall 1 × EuclideanClosedBall 3

/-- The tagged coordinate space of the product model. -/
abbrev ProductFourBallModelSpace : Type :=
  ModelProd (EuclideanClosedBall 1) (EuclideanClosedBall 3)

/-- The product convex-range model with corners on `D¹ × B³`. -/
abbrev productFourBallModel :
    ModelWithCorners ℝ ProductFourAmbient ProductFourBallModelSpace :=
  (euclideanClosedBallModel 1).prod (euclideanClosedBallModel 3)

/-- The model vector space of the product body has dimension four. -/
theorem productFourBallModel_finrank :
    Module.finrank ℝ ProductFourAmbient = 4 := by
  simp [ProductFourAmbient]

/-- The product body is a manifold with corners to every regularity. -/
theorem isManifold_productFourBall (n : ℕ∞ω) :
    IsManifold productFourBallModel n ProductFourBall :=
  inferInstance

/-- The literal two-face subset of `D¹ × B³`. -/
def productFourBallBoundarySet : Set ProductFourBall :=
  (univ : Set (EuclideanClosedBall 1)) ×ˢ
      (Subtype.val ⁻¹' sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∪
    (Subtype.val ⁻¹' sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) ×ˢ
      (univ : Set (EuclideanClosedBall 3))

/-- The model boundary is exactly the union of its `D¹ × S²` and `S⁰ × B³` faces. -/
theorem productFourBallModel_boundary :
    productFourBallModel.boundary ProductFourBall = productFourBallBoundarySet := by
  rw [ModelWithCorners.boundary_prod, closedUnitBallModel_boundary,
    closedUnitBallModel_boundary]
  rfl

/-- The product of the two ambient closed unit balls. -/
def productFourBallBody : Set ProductFourAmbient :=
  closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ×ˢ
    closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1

theorem isClosed_productFourBallBody : IsClosed productFourBallBody :=
  isClosed_closedBall.prod isClosed_closedBall

/-- The ambient product frontier is the union of its two faces. -/
theorem productFourBallBody_frontier :
    frontier productFourBallBody =
      closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ×ˢ
          sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ∪
        sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 ×ˢ
          closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [productFourBallBody, frontier_prod_eq,
    isClosed_closedBall.closure_eq, isClosed_closedBall.closure_eq,
    frontier_closedBall _ one_ne_zero, frontier_closedBall _ one_ne_zero]

/-- The product of ball subtypes is canonically homeomorphic to the product-body subtype. -/
def productFourBallBodyHomeomorph :
    ProductFourBall ≃ₜ ↥productFourBallBody :=
  (Homeomorph.Set.prod
    (closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)).symm

@[simp]
theorem productFourBallBodyHomeomorph_apply_val (x : ProductFourBall) :
    (productFourBallBodyHomeomorph x : ProductFourAmbient) = (x.1.1, x.2.1) :=
  rfl

@[simp]
theorem productFourBallBodyHomeomorph_symm_apply_fst_val
    (x : ↥productFourBallBody) :
    (productFourBallBodyHomeomorph.symm x).1.1 = x.1.1 :=
  rfl

@[simp]
theorem productFourBallBodyHomeomorph_symm_apply_snd_val
    (x : ↥productFourBallBody) :
    (productFourBallBodyHomeomorph.symm x).2.1 = x.1.2 :=
  rfl

/-- The model-boundary subtype is canonically homeomorphic to the ambient frontier subtype in the
product supremum norm. -/
def productFourBallBoundaryHomeomorphFrontier :
    ↥(productFourBallModel.boundary ProductFourBall) ≃ₜ
      ↥(frontier productFourBallBody) :=
  Homeomorph.mk
    { toFun := fun x ↦
        ⟨(x.1.1.1, x.1.2.1), by
          have hx : x.1 ∈ productFourBallBoundarySet :=
            (Set.ext_iff.mp productFourBallModel_boundary x.1).mp x.2
          apply (Set.ext_iff.mp productFourBallBody_frontier _).mpr
          rcases hx with hx | hx
          · exact Or.inl ⟨x.1.1.2, hx.2⟩
          · exact Or.inr ⟨hx.1, x.1.2.2⟩⟩
      invFun := fun y ↦
        ⟨(⟨y.1.1, by
              have hy : y.1 ∈ productFourBallBody := by
                exact (Set.ext_iff.mp isClosed_productFourBallBody.closure_eq y.1).mp
                  (frontier_subset_closure y.2)
              exact hy.1⟩,
            ⟨y.1.2, by
              have hy : y.1 ∈ productFourBallBody := by
                exact (Set.ext_iff.mp isClosed_productFourBallBody.closure_eq y.1).mp
                  (frontier_subset_closure y.2)
              exact hy.2⟩), by
          apply (Set.ext_iff.mp productFourBallModel_boundary _).mpr
          have hy := (Set.ext_iff.mp productFourBallBody_frontier y.1).mp y.2
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
theorem productFourBallBoundaryHomeomorphFrontier_apply_val
    (x : ↥(productFourBallModel.boundary ProductFourBall)) :
    (productFourBallBoundaryHomeomorphFrontier x : ProductFourAmbient) =
      (x.1.1.1, x.1.2.1) :=
  rfl

/-- The canonical linear homeomorphism from Euclidean four-space to the product ambient space. -/
abbrev productFourBallSplitEquiv :
    ProductFourEuclideanAmbient ≃L[ℝ] ProductFourAmbient :=
  EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 3)

/-- The product body transported into Euclidean four-space. -/
def productFourBallEuclideanBody : Set ProductFourEuclideanAmbient :=
  productFourBallSplitEquiv ⁻¹' productFourBallBody

theorem productFourBallSplitEquiv_symm_image_body :
    productFourBallSplitEquiv.symm '' productFourBallBody =
      productFourBallEuclideanBody := by
  exact congrFun productFourBallSplitEquiv.toHomeomorph.image_symm productFourBallBody

theorem productFourBallSplitEquiv_symm_image_frontier :
    productFourBallSplitEquiv.symm '' frontier productFourBallBody =
      frontier productFourBallEuclideanBody := by
  calc
    productFourBallSplitEquiv.symm '' frontier productFourBallBody =
        frontier (productFourBallSplitEquiv.symm '' productFourBallBody) :=
      productFourBallSplitEquiv.toHomeomorph.symm.image_frontier _
    _ = frontier productFourBallEuclideanBody := by
      rw [productFourBallSplitEquiv_symm_image_body]

/-- The product frontier transported to Euclidean four-space. -/
def productFourBallFrontierHomeomorphEuclidean :
    ↥(frontier productFourBallBody) ≃ₜ
      ↥(frontier productFourBallEuclideanBody) :=
  (Homeomorph.image productFourBallSplitEquiv.toHomeomorph.symm
    (frontier productFourBallBody)).trans
      (Homeomorph.setCongr productFourBallSplitEquiv_symm_image_frontier)

@[simp]
theorem productFourBallFrontierHomeomorphEuclidean_apply_val
    (x : ↥(frontier productFourBallBody)) :
    (productFourBallFrontierHomeomorphEuclidean x :
      ProductFourEuclideanAmbient) = productFourBallSplitEquiv.symm x.1 :=
  rfl

theorem convex_productFourBallEuclideanBody :
    Convex ℝ productFourBallEuclideanBody := by
  exact ((convex_closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1).prod
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)).linear_preimage
      productFourBallSplitEquiv.toLinearMap

theorem productFourBallEuclideanBody_mem_nhds :
    productFourBallEuclideanBody ∈ 𝓝 (0 : ProductFourEuclideanAmbient) := by
  apply productFourBallSplitEquiv.continuous.continuousAt.preimage_mem_nhds
  change productFourBallBody ∈
    𝓝 ((0 : EuclideanSpace ℝ (Fin 1)), (0 : EuclideanSpace ℝ (Fin 3)))
  exact prod_mem_nhds
    (closedBall_mem_nhds (0 : EuclideanSpace ℝ (Fin 1)) one_pos)
    (closedBall_mem_nhds (0 : EuclideanSpace ℝ (Fin 3)) one_pos)

theorem isBounded_productFourBallEuclideanBody :
    IsBounded productFourBallEuclideanBody := by
  exact productFourBallSplitEquiv.antilipschitz.isBounded_preimage
    (isBounded_closedBall.prod isBounded_closedBall)

theorem isVonNBounded_productFourBallEuclideanBody :
    IsVonNBounded ℝ productFourBallEuclideanBody :=
  NormedSpace.isVonNBounded_of_isBounded ℝ
    isBounded_productFourBallEuclideanBody

theorem isClosed_productFourBallEuclideanBody :
    IsClosed productFourBallEuclideanBody :=
  isClosed_productFourBallBody.preimage productFourBallSplitEquiv.continuous

/-- Radial gauge rescaling from the transported product body to the Euclidean closed unit ball. -/
def productFourBallGaugeHomeomorph :
    ProductFourEuclideanAmbient ≃ₜ ProductFourEuclideanAmbient :=
  gaugeRescaleHomeomorph productFourBallEuclideanBody
    (closedBall (0 : ProductFourEuclideanAmbient) 1)
    convex_productFourBallEuclideanBody
    productFourBallEuclideanBody_mem_nhds
    isVonNBounded_productFourBallEuclideanBody
    (convex_closedBall 0 1)
    (closedBall_mem_nhds 0 one_pos)
    (NormedSpace.isVonNBounded_closedBall ℝ ProductFourEuclideanAmbient 1)

theorem productFourBallGaugeHomeomorph_image_body :
    productFourBallGaugeHomeomorph '' productFourBallEuclideanBody =
      closedBall (0 : ProductFourEuclideanAmbient) 1 := by
  simpa [productFourBallGaugeHomeomorph,
    isClosed_productFourBallEuclideanBody.closure_eq,
    isClosed_closedBall.closure_eq] using
    (image_gaugeRescaleHomeomorph_closure
      convex_productFourBallEuclideanBody
      productFourBallEuclideanBody_mem_nhds
      isVonNBounded_productFourBallEuclideanBody
      (convex_closedBall (0 : ProductFourEuclideanAmbient) 1)
      (closedBall_mem_nhds (0 : ProductFourEuclideanAmbient) one_pos)
      (NormedSpace.isVonNBounded_closedBall ℝ ProductFourEuclideanAmbient 1))

theorem productFourBallGaugeHomeomorph_image_frontier :
    productFourBallGaugeHomeomorph '' frontier productFourBallEuclideanBody =
      sphere (0 : ProductFourEuclideanAmbient) 1 := by
  rw [productFourBallGaugeHomeomorph.image_frontier,
    productFourBallGaugeHomeomorph_image_body,
    frontier_closedBall _ one_ne_zero]

/-- The literal model-boundary subtype of the product four-ball. -/
abbrev ProductFourBallBoundary : Type :=
  ↥(productFourBallModel.boundary ProductFourBall)

/-- Gauge rescaling restricted to the frontier, with literal target `Sphere 3`. -/
def productFourBallGaugeFrontierHomeomorph :
    ↥(frontier productFourBallEuclideanBody) ≃ₜ Sphere 3 :=
  (Homeomorph.image productFourBallGaugeHomeomorph
    (frontier productFourBallEuclideanBody)).trans
      (Homeomorph.setCongr productFourBallGaugeHomeomorph_image_frontier)

/-- The model-boundary subtype of `D¹ × B³` is homeomorphic to the standard three-sphere. -/
def productFourBallBoundaryHomeomorphSphere :
    ProductFourBallBoundary ≃ₜ Sphere 3 :=
  productFourBallBoundaryHomeomorphFrontier.trans <|
    productFourBallFrontierHomeomorphEuclidean.trans
      productFourBallGaugeFrontierHomeomorph

@[simp]
theorem productFourBallBoundaryHomeomorphSphere_apply_val
    (x : ProductFourBallBoundary) :
    (productFourBallBoundaryHomeomorphSphere x : ProductFourEuclideanAmbient) =
      productFourBallGaugeHomeomorph
        (productFourBallSplitEquiv.symm (x.1.1.1, x.1.2.1)) :=
  rfl

end SplittingSpheres
