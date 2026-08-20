/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushout

/-!
# Associativity of successive topological pushouts

Suppose `X` is attached to `Y` along `A`, and `Y` is attached to `Z` along `B`.  Attaching
`X` to `Y` first and then attaching `Z` gives the same topological space as attaching `Y` to
`Z` first and then attaching `X`.  This file constructs the canonical homeomorphism directly
from the two pushout universal properties and records its exact action on all three pieces.

No embedding, Hausdorff, compactness, or manifold hypotheses are required.
-/

@[expose] public section

noncomputable section

open Topology

universe u

namespace SplittingSpheres

variable {A B X Y Z : Type u}
variable [TopologicalSpace A] [TopologicalSpace B]
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- First attach `X` to `Y` along `A`, then attach `Z` along the copy of `B` in `Y`. -/
abbrev TopologicalPushoutAssocLeft
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) : Type u :=
  TopologicalPushout
    ((topologicalPushoutInr f g).comp h)
    k

/-- First attach `Y` to `Z` along `B`, then attach `X` along the copy of `A` in `Y`. -/
abbrev TopologicalPushoutAssocRight
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) : Type u :=
  TopologicalPushout
    f
    ((topologicalPushoutInl h k).comp g)

/-- Map the intermediate `X ∪_A Y` pushout into the right-associated pushout. -/
def topologicalPushoutAssocForwardXY
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) :
    C(TopologicalPushout f g, TopologicalPushoutAssocRight f g h k) :=
  topologicalPushoutDesc f g
    (topologicalPushoutInl f ((topologicalPushoutInl h k).comp g))
    ((topologicalPushoutInr f ((topologicalPushoutInl h k).comp g)).comp
      (topologicalPushoutInl h k))
    (fun a ↦ topologicalPushout_condition
      f ((topologicalPushoutInl h k).comp g) a)

@[simp]
theorem topologicalPushoutAssocForwardXY_inl
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) (x : X) :
    topologicalPushoutAssocForwardXY f g h k (topologicalPushoutInl f g x) =
      topologicalPushoutInl f ((topologicalPushoutInl h k).comp g) x :=
  topologicalPushoutDesc_inl _ _ _ _ _ x

@[simp]
theorem topologicalPushoutAssocForwardXY_inr
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) (y : Y) :
    topologicalPushoutAssocForwardXY f g h k (topologicalPushoutInr f g y) =
      topologicalPushoutInr f ((topologicalPushoutInl h k).comp g)
        (topologicalPushoutInl h k y) :=
  topologicalPushoutDesc_inr _ _ _ _ _ y

/-- The forward map from the left-associated to the right-associated pushout. -/
def topologicalPushoutAssocForward
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) :
    C(TopologicalPushoutAssocLeft f g h k,
      TopologicalPushoutAssocRight f g h k) :=
  topologicalPushoutDesc
    ((topologicalPushoutInr f g).comp h) k
    (topologicalPushoutAssocForwardXY f g h k)
    ((topologicalPushoutInr f ((topologicalPushoutInl h k).comp g)).comp
      (topologicalPushoutInr h k))
    (fun b ↦ by
      simp only [ContinuousMap.comp_apply]
      rw [topologicalPushoutAssocForwardXY_inr]
      exact congrArg
        (topologicalPushoutInr f ((topologicalPushoutInl h k).comp g))
        (topologicalPushout_condition h k b))

/-- Map the intermediate `Y ∪_B Z` pushout into the left-associated pushout. -/
def topologicalPushoutAssocBackwardYZ
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) :
    C(TopologicalPushout h k, TopologicalPushoutAssocLeft f g h k) :=
  topologicalPushoutDesc h k
    ((topologicalPushoutInl ((topologicalPushoutInr f g).comp h) k).comp
      (topologicalPushoutInr f g))
    (topologicalPushoutInr ((topologicalPushoutInr f g).comp h) k)
    (fun b ↦ topologicalPushout_condition
      ((topologicalPushoutInr f g).comp h) k b)

@[simp]
theorem topologicalPushoutAssocBackwardYZ_inl
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) (y : Y) :
    topologicalPushoutAssocBackwardYZ f g h k (topologicalPushoutInl h k y) =
      topologicalPushoutInl ((topologicalPushoutInr f g).comp h) k
        (topologicalPushoutInr f g y) :=
  topologicalPushoutDesc_inl _ _ _ _ _ y

@[simp]
theorem topologicalPushoutAssocBackwardYZ_inr
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) (z : Z) :
    topologicalPushoutAssocBackwardYZ f g h k (topologicalPushoutInr h k z) =
      topologicalPushoutInr ((topologicalPushoutInr f g).comp h) k z :=
  topologicalPushoutDesc_inr _ _ _ _ _ z

/-- The backward map from the right-associated to the left-associated pushout. -/
def topologicalPushoutAssocBackward
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) :
    C(TopologicalPushoutAssocRight f g h k,
      TopologicalPushoutAssocLeft f g h k) :=
  topologicalPushoutDesc
    f ((topologicalPushoutInl h k).comp g)
    ((topologicalPushoutInl ((topologicalPushoutInr f g).comp h) k).comp
      (topologicalPushoutInl f g))
    (topologicalPushoutAssocBackwardYZ f g h k)
    (fun a ↦ by
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply,
        topologicalPushoutAssocBackwardYZ_inl]
      exact congrArg
        (topologicalPushoutInl ((topologicalPushoutInr f g).comp h) k)
        (topologicalPushout_condition f g a))

/-! ## Exact formulas on the three original pieces -/

@[simp]
theorem topologicalPushoutAssocForward_X
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) (x : X) :
    topologicalPushoutAssocForward f g h k
        (topologicalPushoutInl ((topologicalPushoutInr f g).comp h) k
          (topologicalPushoutInl f g x)) =
      topologicalPushoutInl f ((topologicalPushoutInl h k).comp g) x := by
  unfold topologicalPushoutAssocForward
  rw [topologicalPushoutDesc_inl, topologicalPushoutAssocForwardXY_inl]

@[simp]
theorem topologicalPushoutAssocForward_Y
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) (y : Y) :
    topologicalPushoutAssocForward f g h k
        (topologicalPushoutInl ((topologicalPushoutInr f g).comp h) k
          (topologicalPushoutInr f g y)) =
      topologicalPushoutInr f ((topologicalPushoutInl h k).comp g)
        (topologicalPushoutInl h k y) := by
  unfold topologicalPushoutAssocForward
  rw [topologicalPushoutDesc_inl, topologicalPushoutAssocForwardXY_inr]

@[simp]
theorem topologicalPushoutAssocForward_Z
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) (z : Z) :
    topologicalPushoutAssocForward f g h k
        (topologicalPushoutInr ((topologicalPushoutInr f g).comp h) k z) =
      topologicalPushoutInr f ((topologicalPushoutInl h k).comp g)
        (topologicalPushoutInr h k z) := by
  unfold topologicalPushoutAssocForward
  rw [topologicalPushoutDesc_inr]
  rfl

@[simp]
theorem topologicalPushoutAssocBackward_X
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) (x : X) :
    topologicalPushoutAssocBackward f g h k
        (topologicalPushoutInl f ((topologicalPushoutInl h k).comp g) x) =
      topologicalPushoutInl ((topologicalPushoutInr f g).comp h) k
        (topologicalPushoutInl f g x) := by
  unfold topologicalPushoutAssocBackward
  rw [topologicalPushoutDesc_inl]
  rfl

@[simp]
theorem topologicalPushoutAssocBackward_Y
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) (y : Y) :
    topologicalPushoutAssocBackward f g h k
        (topologicalPushoutInr f ((topologicalPushoutInl h k).comp g)
          (topologicalPushoutInl h k y)) =
      topologicalPushoutInl ((topologicalPushoutInr f g).comp h) k
        (topologicalPushoutInr f g y) := by
  unfold topologicalPushoutAssocBackward
  rw [topologicalPushoutDesc_inr, topologicalPushoutAssocBackwardYZ_inl]

@[simp]
theorem topologicalPushoutAssocBackward_Z
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) (z : Z) :
    topologicalPushoutAssocBackward f g h k
        (topologicalPushoutInr f ((topologicalPushoutInl h k).comp g)
          (topologicalPushoutInr h k z)) =
      topologicalPushoutInr ((topologicalPushoutInr f g).comp h) k z := by
  unfold topologicalPushoutAssocBackward
  rw [topologicalPushoutDesc_inr, topologicalPushoutAssocBackwardYZ_inr]

/-- Canonical reassociation of two successive topological attachments. -/
def topologicalPushoutAssoc
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) :
    TopologicalPushoutAssocLeft f g h k ≃ₜ
      TopologicalPushoutAssocRight f g h k where
  toFun := topologicalPushoutAssocForward f g h k
  invFun := topologicalPushoutAssocBackward f g h k
  left_inv z := by
    rcases topologicalPushout_jointly_surjective
        ((topologicalPushoutInr f g).comp h) k z with ⟨xy, rfl⟩ | ⟨z, rfl⟩
    · rcases topologicalPushout_jointly_surjective f g xy with ⟨x, rfl⟩ | ⟨y, rfl⟩
      · simp
      · simp
    · simp
  right_inv z := by
    rcases topologicalPushout_jointly_surjective
        f ((topologicalPushoutInl h k).comp g) z with ⟨x, rfl⟩ | ⟨yz, rfl⟩
    · simp
    · rcases topologicalPushout_jointly_surjective h k yz with ⟨y, rfl⟩ | ⟨z, rfl⟩
      · simp
      · simp
  continuous_toFun := (topologicalPushoutAssocForward f g h k).continuous
  continuous_invFun := (topologicalPushoutAssocBackward f g h k).continuous

@[simp]
theorem topologicalPushoutAssoc_apply_X
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) (x : X) :
    topologicalPushoutAssoc f g h k
        (topologicalPushoutInl ((topologicalPushoutInr f g).comp h) k
          (topologicalPushoutInl f g x)) =
      topologicalPushoutInl f ((topologicalPushoutInl h k).comp g) x :=
  topologicalPushoutAssocForward_X f g h k x

@[simp]
theorem topologicalPushoutAssoc_apply_Y
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) (y : Y) :
    topologicalPushoutAssoc f g h k
        (topologicalPushoutInl ((topologicalPushoutInr f g).comp h) k
          (topologicalPushoutInr f g y)) =
      topologicalPushoutInr f ((topologicalPushoutInl h k).comp g)
        (topologicalPushoutInl h k y) :=
  topologicalPushoutAssocForward_Y f g h k y

@[simp]
theorem topologicalPushoutAssoc_apply_Z
    (f : C(A, X)) (g : C(A, Y)) (h : C(B, Y)) (k : C(B, Z)) (z : Z) :
    topologicalPushoutAssoc f g h k
        (topologicalPushoutInr ((topologicalPushoutInr f g).comp h) k z) =
      topologicalPushoutInr f ((topologicalPushoutInl h k).comp g)
        (topologicalPushoutInr h k z) :=
  topologicalPushoutAssocForward_Z f g h k z

end SplittingSpheres
