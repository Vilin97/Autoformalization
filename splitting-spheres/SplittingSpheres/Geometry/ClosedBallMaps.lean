/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.ClosedBall

/-!
# Smooth maps into the convex closed-ball model

For the convex-range model on a closed unit ball, a subtype-valued map is smooth exactly when
its ambient vector-valued map is smooth.  This file packages that criterion and convenient
codomain restrictions, both generically and for `EuclideanClosedBall`.

The proof uses the actual global convex-range model and the local normal form of its inclusion
into the ambient vector space.  It does not identify the closed ball with a half-space model.
-/

@[expose] public section

noncomputable section

open Metric Set
open scoped ContDiff Manifold

namespace SplittingSpheres

universe u v w uF

section CodRestrict

variable {E : Type u} [NormedAddCommGroup E]

/-- Restrict the codomain of an ambient map to the closed unit ball. -/
def closedUnitBallCodRestrict {X : Type*} (f : X → E)
    (hf : ∀ x, f x ∈ closedBall (0 : E) 1) : X → ClosedUnitBall E :=
  Set.codRestrict f (closedBall (0 : E) 1) hf

@[simp]
theorem closedUnitBallCodRestrict_apply {X : Type*} (f : X → E)
    (hf : ∀ x, f x ∈ closedBall (0 : E) 1) (x : X) :
    closedUnitBallCodRestrict f hf x = ⟨f x, hf x⟩ :=
  rfl

@[simp]
theorem closedUnitBallCodRestrict_coe {X : Type*} (f : X → E)
    (hf : ∀ x, f x ∈ closedBall (0 : E) 1) (x : X) :
    (closedUnitBallCodRestrict f hf x : E) = f x :=
  rfl

/-- Restricting the ambient values of an already subtype-valued map recovers the map exactly. -/
@[simp]
theorem closedUnitBallCodRestrict_eta {X : Type*} (f : X → ClosedUnitBall E) :
    closedUnitBallCodRestrict (fun x ↦ (f x : E)) (fun x ↦ (f x).2) = f := by
  funext x
  exact Subtype.ext rfl

end CodRestrict

section SmoothMaps

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type v} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ F H}
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : ℕ∞ω}

/-- The closed-ball inclusion has the explicit zero-dimensional complement used by the generic
composition criterion for immersions. -/
theorem isImmersionOfComplement_closedUnitBall_inclusion :
    Manifold.IsImmersionOfComplement PUnit.{u + 1}
      (closedUnitBallModel E) (modelWithCornersSelf ℝ E) n
      (Subtype.val : ClosedUnitBall E → E) :=
  fun x ↦ isImmersionAtOfComplement_closedUnitBall_inclusion E x

/-- A map into the convex closed-ball model is smooth if and only if its ambient values are
smooth.  Ambient smoothness already implies continuity into the closed-ball subtype. -/
theorem contMDiff_closedUnitBall_iff_ambient {f : M → ClosedUnitBall E} :
    ContMDiff I (closedUnitBallModel E) n f ↔
      ContMDiff I (modelWithCornersSelf ℝ E) n (fun x ↦ (f x : E)) := by
  rw [ContMDiff.iff_comp_isImmersionOfComplement
    (isImmersionOfComplement_closedUnitBall_inclusion (E := E) (n := n))]
  constructor
  · rintro ⟨_, hf⟩
    exact hf.congr fun _ ↦ rfl
  · intro hf
    refine ⟨hf.continuous.subtype_mk (fun x ↦ (f x).2), ?_⟩
    exact hf.congr fun _ ↦ rfl

/-- Composition-form version of `contMDiff_closedUnitBall_iff_ambient`. -/
theorem contMDiff_closedUnitBall_iff_comp_subtypeVal {f : M → ClosedUnitBall E} :
    ContMDiff I (closedUnitBallModel E) n f ↔
      ContMDiff I (modelWithCornersSelf ℝ E) n
        ((Subtype.val : ClosedUnitBall E → E) ∘ f) := by
  constructor
  · intro hf
    exact (contMDiff_closedUnitBall_iff_ambient.mp hf).congr fun _ ↦ rfl
  · intro hf
    apply contMDiff_closedUnitBall_iff_ambient.mpr
    exact hf.congr fun _ ↦ rfl

/-- Package ambient smoothness as smoothness into the convex closed-ball model. -/
theorem contMDiff_closedUnitBall_of_contMDiff_val {f : M → ClosedUnitBall E}
    (hf : ContMDiff I (modelWithCornersSelf ℝ E) n (fun x ↦ (f x : E))) :
    ContMDiff I (closedUnitBallModel E) n f :=
  contMDiff_closedUnitBall_iff_ambient.mpr hf

/-- A smooth ambient map whose values lie in the closed unit ball remains smooth after restricting
its codomain to the convex closed-ball model. -/
theorem ContMDiff.codRestrict_closedUnitBall {f : M → E}
    (hf : ContMDiff I (modelWithCornersSelf ℝ E) n f)
    (hmem : ∀ x, f x ∈ closedBall (0 : E) 1) :
    ContMDiff I (closedUnitBallModel E) n (closedUnitBallCodRestrict f hmem) := by
  apply contMDiff_closedUnitBall_of_contMDiff_val
  exact hf.congr fun _ ↦ rfl

end SmoothMaps

section EuclideanSpecialization

variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type v} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ F H}
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : ℕ∞ω} {d : ℕ}

/-- Restrict a Euclidean-valued map to the literal closed Euclidean unit ball. -/
def euclideanClosedBallCodRestrict {X : Type*}
    (f : X → EuclideanSpace ℝ (Fin d))
    (hf : ∀ x, f x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :
    X → EuclideanClosedBall d :=
  closedUnitBallCodRestrict f hf

@[simp]
theorem euclideanClosedBallCodRestrict_apply {X : Type*}
    (f : X → EuclideanSpace ℝ (Fin d))
    (hf : ∀ x, f x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) (x : X) :
    euclideanClosedBallCodRestrict f hf x = ⟨f x, hf x⟩ :=
  rfl

@[simp]
theorem euclideanClosedBallCodRestrict_coe {X : Type*}
    (f : X → EuclideanSpace ℝ (Fin d))
    (hf : ∀ x, f x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) (x : X) :
    (euclideanClosedBallCodRestrict f hf x : EuclideanSpace ℝ (Fin d)) = f x :=
  rfl

/-- The Euclidean codomain restriction is an exact identity on subtype-valued maps. -/
@[simp]
theorem euclideanClosedBallCodRestrict_eta {X : Type*} (f : X → EuclideanClosedBall d) :
    euclideanClosedBallCodRestrict
      (fun x ↦ (f x : EuclideanSpace ℝ (Fin d))) (fun x ↦ (f x).2) = f :=
  closedUnitBallCodRestrict_eta f

/-- Euclidean specialization of `contMDiff_closedUnitBall_iff_ambient`. -/
theorem contMDiff_euclideanClosedBall_iff_ambient {f : M → EuclideanClosedBall d} :
    ContMDiff I (euclideanClosedBallModel d) n f ↔
      ContMDiff I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d))) n
        (fun x ↦ (f x : EuclideanSpace ℝ (Fin d))) :=
  contMDiff_closedUnitBall_iff_ambient

/-- Composition-form Euclidean specialization of the closed-ball smoothness criterion. -/
theorem contMDiff_euclideanClosedBall_iff_comp_subtypeVal
    {f : M → EuclideanClosedBall d} :
    ContMDiff I (euclideanClosedBallModel d) n f ↔
      ContMDiff I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d))) n
        ((Subtype.val : EuclideanClosedBall d → EuclideanSpace ℝ (Fin d)) ∘ f) :=
  contMDiff_closedUnitBall_iff_comp_subtypeVal

/-- Package ambient Euclidean smoothness as smoothness into the convex closed-ball model. -/
theorem contMDiff_euclideanClosedBall_of_contMDiff_val {f : M → EuclideanClosedBall d}
    (hf : ContMDiff I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d))) n
      (fun x ↦ (f x : EuclideanSpace ℝ (Fin d)))) :
    ContMDiff I (euclideanClosedBallModel d) n f :=
  contMDiff_euclideanClosedBall_iff_ambient.mpr hf

/-- Restricting the codomain of a smooth Euclidean map to the closed unit ball preserves
smoothness. -/
theorem ContMDiff.codRestrict_euclideanClosedBall
    {f : M → EuclideanSpace ℝ (Fin d)}
    (hf : ContMDiff I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d))) n f)
    (hmem : ∀ x, f x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :
    ContMDiff I (euclideanClosedBallModel d) n
      (euclideanClosedBallCodRestrict f hmem) := by
  apply contMDiff_euclideanClosedBall_of_contMDiff_val
  exact hf.congr fun _ ↦ rfl

end EuclideanSpecialization

end SplittingSpheres
