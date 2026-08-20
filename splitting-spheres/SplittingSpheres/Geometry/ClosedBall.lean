/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# The closed Euclidean ball as a model with corners

Mathlib's pinned manifold library has no charted-space instance putting the standard half-space
model `𝓡∂ n` on a closed ball.  It does, however, allow any closed convex subset with nonempty
interior to be the range of a `ModelWithCorners`.  This file applies that API honestly to the
closed unit ball.

The resulting model has one global coordinate map: the inclusion of the closed ball into its
ambient normed vector space.  It gives the closed ball a genuine smooth-manifold-with-corners
structure in Mathlib's sense.  Its manifold interior is exactly the open unit ball, its manifold
boundary is exactly the unit sphere, and its inclusion is a smooth embedding.  The immersion part
is proved directly from Mathlib's chart-normal-form definition, including at regularity `∞`.

This file does **not** claim that this convex-range model is locally diffeomorphic to the standard
Euclidean half-space model.  Establishing that stronger statement requires explicit local
boundary-flattening charts; the pinned library contains no theorem constructing them for a smooth
strictly convex set.  Likewise, Mathlib does not currently put an induced manifold structure on a
manifold boundary subtype, so the boundary identification below is a homeomorphism, not a claimed
diffeomorphism.
-/

@[expose] public section

open Function Metric Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace SplittingSpheres

universe u

section RadialRetraction

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial retraction of a real normed vector space onto its closed unit ball. -/
def closedUnitBallRadialRetraction (x : E) : closedBall (0 : E) 1 :=
  ⟨(max 1 ‖x‖)⁻¹ • x, by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (zero_lt_one.trans_le (le_max_left 1 ‖x‖)))]
    exact (inv_mul_le_one₀ (zero_lt_one.trans_le (le_max_left 1 ‖x‖))).2
      (le_max_right 1 ‖x‖)⟩

@[simp]
theorem closedUnitBallRadialRetraction_coe (x : E) :
    (closedUnitBallRadialRetraction x : E) = (max 1 ‖x‖)⁻¹ • x :=
  rfl

/-- The radial retraction is the identity on the closed unit ball. -/
@[simp]
theorem closedUnitBallRadialRetraction_coe_of_mem {x : E}
    (hx : x ∈ closedBall (0 : E) 1) :
    (closedUnitBallRadialRetraction x : E) = x := by
  have hxnorm : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  simp [closedUnitBallRadialRetraction, max_eq_left hxnorm]

/-- The radial retraction fixes the closed-ball subtype pointwise. -/
@[simp]
theorem closedUnitBallRadialRetraction_coeSubtype
    (x : closedBall (0 : E) 1) : closedUnitBallRadialRetraction (x : E) = x := by
  apply Subtype.ext
  exact closedUnitBallRadialRetraction_coe_of_mem x.property

/-- The radial retraction is continuous, including across the unit sphere. -/
theorem continuous_closedUnitBallRadialRetraction :
    Continuous (closedUnitBallRadialRetraction : E → closedBall (0 : E) 1) := by
  let d : E → ℝ := fun x ↦ max 1 ‖x‖
  have hd : Continuous d := continuous_const.max continuous_norm
  have hd_ne : ∀ x, d x ≠ 0 := fun x ↦
    (zero_lt_one.trans_le (le_max_left 1 ‖x‖)).ne'
  apply Continuous.subtype_mk
  change Continuous fun x : E ↦ (d x)⁻¹ • x
  exact (hd.inv₀ hd_ne).smul continuous_id

/-- The inclusion of the closed unit ball and the radial retraction form a partial equivalence
whose source is the whole subtype and whose target is the ambient closed ball. -/
def closedUnitBallPartialEquiv : PartialEquiv (closedBall (0 : E) 1) E where
  toFun := Subtype.val
  invFun := closedUnitBallRadialRetraction
  source := univ
  target := closedBall 0 1
  map_source' x _ := x.property
  map_target' _ _ := mem_univ _
  left_inv' x _ := closedUnitBallRadialRetraction_coeSubtype x
  right_inv' _ hx := closedUnitBallRadialRetraction_coe_of_mem hx

@[simp]
theorem closedUnitBallPartialEquiv_source :
    (closedUnitBallPartialEquiv (E := E)).source = univ :=
  rfl

@[simp]
theorem closedUnitBallPartialEquiv_target :
    (closedUnitBallPartialEquiv (E := E)).target = closedBall (0 : E) 1 :=
  rfl

@[simp]
theorem closedUnitBallPartialEquiv_apply (x : closedBall (0 : E) 1) :
    closedUnitBallPartialEquiv x = (x : E) :=
  rfl

end RadialRetraction

section ConvexModel

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed unit ball, used as its own model space. -/
abbrev ClosedUnitBall := closedBall (0 : E) 1

/-- The closed unit ball as a convex-range `ModelWithCorners` in its ambient vector space. -/
def closedUnitBallModel : ModelWithCorners ℝ E (ClosedUnitBall E) :=
  ModelWithCorners.ofConvexRange
    (closedUnitBallPartialEquiv (E := E)) rfl (convex_closedBall 0 1)
    continuous_subtype_val continuous_closedUnitBallRadialRetraction (by
      change (interior (closedBall (0 : E) 1)).Nonempty
      rw [interior_closedBall (0 : E) one_ne_zero]
      exact ⟨0, by simp⟩)

@[simp]
theorem closedUnitBallModel_apply (x : ClosedUnitBall E) :
    closedUnitBallModel E x = (x : E) :=
  rfl

@[simp]
theorem range_closedUnitBallModel :
    range (closedUnitBallModel E) = closedBall (0 : E) 1 := by
  exact Subtype.range_val

/-- The closed ball is a manifold to every regularity with respect to its convex-range model. -/
theorem isManifold_closedUnitBall (n : ℕ∞ω) :
    IsManifold (closedUnitBallModel E) n (ClosedUnitBall E) :=
  inferInstance

/-- The global closed-ball coordinate map is smooth to every order. -/
theorem contMDiff_closedUnitBall_inclusion {n : ℕ∞ω} :
    ContMDiff (closedUnitBallModel E) (modelWithCornersSelf ℝ E) n
      (Subtype.val : ClosedUnitBall E → E) := by
  have hfun : (Subtype.val : ClosedUnitBall E → E) = closedUnitBallModel E := by
    funext x
    rfl
  rw [hfun]
  exact (closedUnitBallModel E).contMDiff

/-- The closed-ball inclusion has the zero-dimensional `PUnit` complement in the literal local
normal form used by Mathlib's definition of immersion. -/
theorem isImmersionAtOfComplement_closedUnitBall_inclusion {n : ℕ∞ω}
    (x : ClosedUnitBall E) :
    Manifold.IsImmersionAtOfComplement PUnit.{u + 1} (closedUnitBallModel E)
      (modelWithCornersSelf ℝ E) n (Subtype.val : ClosedUnitBall E → E) x := by
  have hfun : (Subtype.val : ClosedUnitBall E → E) = closedUnitBallModel E := by
    funext y
    rfl
  rw [hfun]
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (closedUnitBallModel E).continuousAt (.prodUnique ℝ E PUnit.{u + 1})
    (.refl _) (.refl _) (by simp) (by simp)
    (IsManifold.subset_maximalAtlas (by simp))
    (IsManifold.subset_maximalAtlas (by simp))
  simp only [OpenPartialHomeomorph.extend, OpenPartialHomeomorph.refl_partialEquiv,
    modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, PartialEquiv.refl_coe,
    PartialEquiv.refl_trans, ModelWithCorners.toPartialEquiv_coe_symm, CompTriple.comp_eq,
    PUnit.zero_eq, ModelWithCorners.target_eq, range_closedUnitBallModel]
  intro y hy
  apply (closedUnitBallModel E).right_inv
  rw [range_closedUnitBallModel]
  exact hy

/-- The closed-ball inclusion is an immersion to every regularity, including `∞`. -/
theorem isImmersion_closedUnitBall_inclusion {n : ℕ∞ω} :
    Manifold.IsImmersion (closedUnitBallModel E) (modelWithCornersSelf ℝ E) n
      (Subtype.val : ClosedUnitBall E → E) := by
  have h : Manifold.IsImmersionOfComplement PUnit.{u + 1} (closedUnitBallModel E)
      (modelWithCornersSelf ℝ E) n (Subtype.val : ClosedUnitBall E → E) :=
    fun x ↦ isImmersionAtOfComplement_closedUnitBall_inclusion E x
  exact h.isImmersion

/-- The closed-ball inclusion is a smooth embedding to every regularity, including `∞`. -/
theorem isSmoothEmbedding_closedUnitBall_inclusion {n : ℕ∞ω} :
    Manifold.IsSmoothEmbedding (closedUnitBallModel E) (modelWithCornersSelf ℝ E) n
      (Subtype.val : ClosedUnitBall E → E) := by
  exact ⟨isImmersion_closedUnitBall_inclusion E, Topology.IsEmbedding.subtypeVal⟩

/-- The manifold interior of the convex closed-ball model is exactly the ambient open ball. -/
theorem closedUnitBallModel_interior :
    (closedUnitBallModel E).interior (ClosedUnitBall E) =
      Subtype.val ⁻¹' ball (0 : E) 1 := by
  ext x
  simp only [ModelWithCorners.interior, ModelWithCorners.IsInteriorPoint,
    extChartAt_self_apply, range_closedUnitBallModel, interior_closedBall (0 : E) one_ne_zero,
    mem_preimage, closedUnitBallModel_apply]
  rfl

/-- The manifold boundary of the convex closed-ball model is exactly the ambient unit sphere. -/
theorem closedUnitBallModel_boundary :
    (closedUnitBallModel E).boundary (ClosedUnitBall E) =
      Subtype.val ⁻¹' sphere (0 : E) 1 := by
  ext x
  simp only [ModelWithCorners.boundary, ModelWithCorners.IsBoundaryPoint,
    extChartAt_self_apply, range_closedUnitBallModel, frontier_closedBall (0 : E) one_ne_zero,
    mem_preimage, closedUnitBallModel_apply]
  rfl

/-- The boundary subtype of the convex closed-ball model is canonically homeomorphic to the
ambient unit sphere.  No induced smooth structure on the boundary subtype is asserted. -/
def closedUnitBallBoundaryHomeomorph :
    ↥((closedUnitBallModel E).boundary (ClosedUnitBall E)) ≃ₜ sphere (0 : E) 1 :=
  Homeomorph.mk
    { toFun := fun x ↦ ⟨x.1.1, by
        exact (Set.ext_iff.mp (closedUnitBallModel_boundary E) x.1).mp x.2⟩
      invFun := fun y ↦
        ⟨⟨y.1, sphere_subset_closedBall y.2⟩, by
          exact (Set.ext_iff.mp (closedUnitBallModel_boundary E)
            ⟨y.1, sphere_subset_closedBall y.2⟩).mpr y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
    (by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val)
    (by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val)

@[simp]
theorem closedUnitBallBoundaryHomeomorph_apply_val
    (x : ↥((closedUnitBallModel E).boundary (ClosedUnitBall E))) :
    (closedUnitBallBoundaryHomeomorph E x : E) = x.1.1 :=
  by simp [closedUnitBallBoundaryHomeomorph]

@[simp]
theorem closedUnitBallBoundaryHomeomorph_symm_apply_val
    (x : sphere (0 : E) 1) :
    (((closedUnitBallBoundaryHomeomorph E).symm x).1.1 : E) = x :=
  by simp [closedUnitBallBoundaryHomeomorph]

end ConvexModel

section EuclideanSpecialization

/-- The closed unit ball in Euclidean `n`-space. -/
abbrev EuclideanClosedBall (n : ℕ) :=
  ClosedUnitBall (EuclideanSpace ℝ (Fin n))

/-- The convex-range model on the closed unit ball in Euclidean `n`-space. -/
abbrev euclideanClosedBallModel (n : ℕ) :=
  closedUnitBallModel (EuclideanSpace ℝ (Fin n))

/-- The boundary of the Euclidean `(n+1)`-ball is canonically homeomorphic to the standard unit
`n`-sphere, with both sides realized using their literal Euclidean coordinate subtypes. -/
def euclideanClosedBallBoundaryHomeomorphSphere (n : ℕ) :
    ↥((euclideanClosedBallModel (n + 1)).boundary (EuclideanClosedBall (n + 1))) ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  closedUnitBallBoundaryHomeomorph (EuclideanSpace ℝ (Fin (n + 1)))

@[simp]
theorem euclideanClosedBallBoundaryHomeomorphSphere_apply_val (n : ℕ)
    (x : ↥((euclideanClosedBallModel (n + 1)).boundary (EuclideanClosedBall (n + 1)))) :
    (euclideanClosedBallBoundaryHomeomorphSphere n x :
      EuclideanSpace ℝ (Fin (n + 1))) = x.1.1 :=
  by simp [euclideanClosedBallBoundaryHomeomorphSphere]

/-- The Euclidean closed unit ball is compact. -/
theorem isCompact_euclideanClosedBall (n : ℕ) :
    IsCompact (univ : Set (EuclideanClosedBall n)) := by
  apply isCompact_univ_iff.mpr
  exact isCompact_iff_compactSpace.mp
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- The Euclidean closed unit ball is path connected. -/
theorem isPathConnected_euclideanClosedBall (n : ℕ) :
    IsPathConnected (univ : Set (EuclideanClosedBall n)) := by
  apply pathConnectedSpace_iff_univ.mp
  exact isPathConnected_iff_pathConnectedSpace.mp <|
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).isPathConnected ⟨0, by simp⟩

/-- The closed Euclidean four-ball used by the support and capping constructions. -/
abbrev EuclideanFourBall := EuclideanClosedBall 4

/-- The convex-range model on the closed Euclidean four-ball. -/
abbrev euclideanFourBallModel := euclideanClosedBallModel 4

/-- The closed four-ball inclusion is a smooth embedding into standard Euclidean four-space. -/
theorem isSmoothEmbedding_euclideanFourBall_inclusion :
    Manifold.IsSmoothEmbedding euclideanFourBallModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (Subtype.val : EuclideanFourBall → EuclideanSpace ℝ (Fin 4)) :=
  isSmoothEmbedding_closedUnitBall_inclusion (EuclideanSpace ℝ (Fin 4))

/-- The model boundary of the closed Euclidean four-ball is homeomorphic to the literal unit
three-sphere in Euclidean four-space. -/
def euclideanFourBallBoundaryHomeomorphSphereThree :
    ↥(euclideanFourBallModel.boundary EuclideanFourBall) ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  euclideanClosedBallBoundaryHomeomorphSphere 3

end EuclideanSpecialization

end SplittingSpheres
