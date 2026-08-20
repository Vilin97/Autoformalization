/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutHomeomorph
public import SplittingSpheres.Handlebody.ProductFourBall

/-!
# The boundary of `D¹ × B³` as a two-face pushout

The boundary of the product four-ball is the union of the side `D¹ × S²` and the two end balls
`S⁰ × B³`, meeting in `S⁰ × S²`.  This file recognizes that literal union as a topological
pushout and hence as `Sphere 3`.

This is point-set topology only.  In particular, no smooth structure or smooth gluing theorem is
asserted for the pushout or its boundary homeomorphism.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped Topology

namespace SplittingSpheres

/-! ## The one-dimensional ball as an interval -/

theorem norm_euclideanSpace_fin_one (x : EuclideanSpace ℝ (Fin 1)) :
    ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

theorem euclideanClosedBallOne_coordinate_bounds (x : EuclideanClosedBall 1) :
    -1 ≤ x.1 0 ∧ x.1 0 ≤ 1 := by
  apply abs_le.mp
  rw [← norm_euclideanSpace_fin_one]
  exact mem_closedBall_zero_iff.mp x.2

/-- Affine coordinate from the one-dimensional closed ball to `[0,1]`. -/
def euclideanClosedBallOneToUnitInterval
    (x : EuclideanClosedBall 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨(x.1 0 + 1) / 2, by
    linarith [euclideanClosedBallOne_coordinate_bounds x |>.1], by
    linarith [euclideanClosedBallOne_coordinate_bounds x |>.2]⟩

/-- The inverse affine coordinate from `[0,1]` to the one-dimensional closed ball. -/
def unitIntervalToEuclideanClosedBallOne
    (t : Set.Icc (0 : ℝ) 1) : EuclideanClosedBall 1 := by
  let x : EuclideanSpace ℝ (Fin 1) :=
    (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ 2 * (t : ℝ) - 1)
  refine ⟨x, ?_⟩
  rw [mem_closedBall_zero_iff, norm_euclideanSpace_fin_one]
  change |2 * (t : ℝ) - 1| ≤ 1
  rw [abs_le]
  constructor <;> linarith [t.2.1, t.2.2]

@[simp]
theorem euclideanClosedBallOneToUnitInterval_coe (x : EuclideanClosedBall 1) :
    (euclideanClosedBallOneToUnitInterval x : ℝ) = (x.1 0 + 1) / 2 :=
  rfl

@[simp]
theorem unitIntervalToEuclideanClosedBallOne_apply
    (t : Set.Icc (0 : ℝ) 1) (i : Fin 1) :
    (unitIntervalToEuclideanClosedBallOne t).1 i = 2 * (t : ℝ) - 1 :=
  rfl

/-- The one-dimensional Euclidean closed ball is the unit interval. -/
def euclideanClosedBallOneHomeomorphUnitInterval :
    EuclideanClosedBall 1 ≃ₜ Set.Icc (0 : ℝ) 1 where
  toFun := euclideanClosedBallOneToUnitInterval
  invFun := unitIntervalToEuclideanClosedBallOne
  left_inv x := by
    apply Subtype.ext
    apply (EuclideanSpace.equiv (Fin 1) ℝ).injective
    funext i
    fin_cases i
    change 2 * ((x.1 0 + 1) / 2) - 1 = x.1 0
    ring
  right_inv t := by
    apply Subtype.ext
    change ((2 * (t : ℝ) - 1) + 1) / 2 = t
    ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous (fun t : Set.Icc (0 : ℝ) 1 ↦
      (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ 2 * (t : ℝ) - 1))
    fun_prop

theorem euclideanClosedBallOneToUnitInterval_of_mem_sphere
    (x : EuclideanClosedBall 1)
    (hx : x.1 ∈ sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    euclideanClosedBallOneToUnitInterval x = 0 ∨
      euclideanClosedBallOneToUnitInterval x = 1 := by
  have habs : |x.1 0| = 1 := by
    rw [← norm_euclideanSpace_fin_one]
    exact mem_sphere_zero_iff_norm.mp hx
  rcases (abs_eq zero_le_one).mp habs with h | h
  · right
    apply Subtype.ext
    simp [euclideanClosedBallOneToUnitInterval, h]
  · left
    apply Subtype.ext
    simp [euclideanClosedBallOneToUnitInterval, h]

/-- The side face `D¹ × S²`. -/
abbrev ProductFourSidePiece : Type :=
  EuclideanClosedBall 1 × Sphere 2

/-- The pair of end faces `S⁰ × B³`. -/
abbrev ProductFourEndPiece : Type :=
  sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 × EuclideanClosedBall 3

/-- The common corner `S⁰ × S²`. -/
abbrev ProductFourCorner : Type :=
  sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 × Sphere 2

/-- Include the corner in the side face. -/
def productFourCornerToSide : C(ProductFourCorner, ProductFourSidePiece) where
  toFun x := (⟨x.1.1, sphere_subset_closedBall x.1.2⟩, x.2)
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd

/-- Include the corner in the two end faces. -/
def productFourCornerToEnd : C(ProductFourCorner, ProductFourEndPiece) where
  toFun x := (x.1, ⟨x.2.1, sphere_subset_closedBall x.2.2⟩)
  continuous_toFun :=
    continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

@[simp]
theorem productFourCornerToSide_apply (x : ProductFourCorner) :
    productFourCornerToSide x =
      (⟨x.1.1, sphere_subset_closedBall x.1.2⟩, x.2) :=
  rfl

@[simp]
theorem productFourCornerToEnd_apply (x : ProductFourCorner) :
    productFourCornerToEnd x =
      (x.1, ⟨x.2.1, sphere_subset_closedBall x.2.2⟩) :=
  rfl

theorem injective_productFourCornerToSide : Injective productFourCornerToSide := by
  intro x y h
  exact Prod.ext (Subtype.ext <| congrArg (fun z : ProductFourSidePiece ↦ z.1.1) h)
    (congrArg (fun z : ProductFourSidePiece ↦ z.2) h)

theorem injective_productFourCornerToEnd : Injective productFourCornerToEnd := by
  intro x y h
  exact Prod.ext (congrArg (fun z : ProductFourEndPiece ↦ z.1) h)
    (Subtype.ext <| congrArg (fun z : ProductFourEndPiece ↦ z.2.1) h)

/-- Include the side face in the model boundary of the product four-ball. -/
def productFourSideToBoundary : C(ProductFourSidePiece, ProductFourBallBoundary) where
  toFun x :=
    ⟨(x.1, ⟨x.2.1, sphere_subset_closedBall x.2.2⟩), by
      apply (Set.ext_iff.mp productFourBallModel_boundary _).mpr
      exact Or.inl ⟨mem_univ _, x.2.2⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

/-- Include the two end faces in the model boundary of the product four-ball. -/
def productFourEndToBoundary : C(ProductFourEndPiece, ProductFourBallBoundary) where
  toFun x :=
    ⟨(⟨x.1.1, sphere_subset_closedBall x.1.2⟩, x.2), by
      apply (Set.ext_iff.mp productFourBallModel_boundary _).mpr
      exact Or.inr ⟨x.1.2, mem_univ _⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd

@[simp]
theorem productFourSideToBoundary_apply_val (x : ProductFourSidePiece) :
    (productFourSideToBoundary x : ProductFourBall) =
      (x.1, ⟨x.2.1, sphere_subset_closedBall x.2.2⟩) :=
  rfl

@[simp]
theorem productFourEndToBoundary_apply_val (x : ProductFourEndPiece) :
    (productFourEndToBoundary x : ProductFourBall) =
      (⟨x.1.1, sphere_subset_closedBall x.1.2⟩, x.2) :=
  rfl

theorem productFourFace_compatibility (z : ProductFourCorner) :
    productFourSideToBoundary (productFourCornerToSide z) =
      productFourEndToBoundary (productFourCornerToEnd z) := by
  apply Subtype.ext
  rfl

theorem injective_productFourSideToBoundary : Injective productFourSideToBoundary := by
  intro x y h
  have hval := congrArg Subtype.val h
  exact Prod.ext (congrArg (fun z : ProductFourBall ↦ z.1) hval)
    (Subtype.ext <| congrArg (fun z : ProductFourBall ↦ z.2.1) hval)

theorem injective_productFourEndToBoundary : Injective productFourEndToBoundary := by
  intro x y h
  have hval := congrArg Subtype.val h
  exact Prod.ext
    (Subtype.ext <| congrArg (fun z : ProductFourBall ↦ z.1.1) hval)
    (congrArg (fun z : ProductFourBall ↦ z.2) hval)

theorem productFourFaces_cross_overlap
    (x : ProductFourSidePiece) (y : ProductFourEndPiece)
    (h : productFourSideToBoundary x = productFourEndToBoundary y) :
    ∃ z : ProductFourCorner,
      productFourCornerToSide z = x ∧ productFourCornerToEnd z = y := by
  have hval := congrArg Subtype.val h
  have hfst := congrArg Prod.fst hval
  have hsnd := congrArg Prod.snd hval
  refine ⟨(y.1, x.2), ?_, ?_⟩
  · exact Prod.ext (Subtype.ext <| (congrArg Subtype.val hfst).symm) rfl
  · exact Prod.ext rfl (Subtype.ext <| congrArg Subtype.val hsnd)

theorem range_productFourFaces :
    range productFourSideToBoundary ∪ range productFourEndToBoundary = univ := by
  apply Set.eq_univ_of_forall
  intro z
  have hz : z.1 ∈ productFourBallBoundarySet :=
    (Set.ext_iff.mp productFourBallModel_boundary z.1).mp z.2
  rcases hz with hz | hz
  · apply Or.inl
    let x : ProductFourSidePiece := (z.1.1, ⟨z.1.2.1, hz.2⟩)
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl (Subtype.ext rfl)
  · apply Or.inr
    let y : ProductFourEndPiece := (⟨z.1.1.1, hz.1⟩, z.1.2)
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact Prod.ext (Subtype.ext rfl) rfl

/-- The two-face pushout model of the product-four-ball boundary. -/
abbrev ProductFourBoundaryPushout : Type :=
  TopologicalPushout productFourCornerToSide productFourCornerToEnd

/-- The two-face pushout is the literal model boundary of `D¹ × B³`. -/
def productFourBoundaryPushoutHomeomorph :
    ProductFourBoundaryPushout ≃ₜ ProductFourBallBoundary :=
  topologicalPushoutHomeomorph
    productFourCornerToSide productFourCornerToEnd
    productFourSideToBoundary productFourEndToBoundary
    productFourFace_compatibility
    injective_productFourCornerToSide
    injective_productFourSideToBoundary
    injective_productFourEndToBoundary
    productFourFaces_cross_overlap
    range_productFourFaces

@[simp]
theorem productFourBoundaryPushoutHomeomorph_inl (x : ProductFourSidePiece) :
    productFourBoundaryPushoutHomeomorph
        (topologicalPushoutInl productFourCornerToSide productFourCornerToEnd x) =
      productFourSideToBoundary x :=
  topologicalPushoutHomeomorph_inl _ _ _ _ _ _ _ _ _ _ x

@[simp]
theorem productFourBoundaryPushoutHomeomorph_inr (x : ProductFourEndPiece) :
    productFourBoundaryPushoutHomeomorph
        (topologicalPushoutInr productFourCornerToSide productFourCornerToEnd x) =
      productFourEndToBoundary x :=
  topologicalPushoutHomeomorph_inr _ _ _ _ _ _ _ _ _ _ x

/-- The two-face pushout is homeomorphic to the standard three-sphere. -/
def productFourBoundaryPushoutHomeomorphSphere :
    ProductFourBoundaryPushout ≃ₜ Sphere 3 :=
  productFourBoundaryPushoutHomeomorph.trans productFourBallBoundaryHomeomorphSphere

end SplittingSpheres
