/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushout

/-!
# Symmetry of a topological pushout

Swapping the two legs of a span swaps the two coprojections and leaves its topological pushout
unchanged up to a canonical homeomorphism.  The construction is directly by the pushout
universal property and records exact computation laws on both pieces.
-/

@[expose] public section

noncomputable section

open Topology

universe u

namespace SplittingSpheres

variable {A X Y : Type u}
variable [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]

/-- The continuous map which swaps the two pieces of a topological pushout. -/
def topologicalPushoutCommMap (f : C(A, X)) (g : C(A, Y)) :
    C(TopologicalPushout f g, TopologicalPushout g f) :=
  topologicalPushoutDesc f g
    (topologicalPushoutInr g f)
    (topologicalPushoutInl g f)
    (fun a ↦ (topologicalPushout_condition g f a).symm)

@[simp]
theorem topologicalPushoutCommMap_inl
    (f : C(A, X)) (g : C(A, Y)) (x : X) :
    topologicalPushoutCommMap f g (topologicalPushoutInl f g x) =
      topologicalPushoutInr g f x :=
  topologicalPushoutDesc_inl _ _ _ _ _ x

@[simp]
theorem topologicalPushoutCommMap_inr
    (f : C(A, X)) (g : C(A, Y)) (y : Y) :
    topologicalPushoutCommMap f g (topologicalPushoutInr f g y) =
      topologicalPushoutInl g f y :=
  topologicalPushoutDesc_inr _ _ _ _ _ y

/-- The canonical homeomorphism obtained by swapping the two legs of a topological pushout. -/
def topologicalPushoutComm (f : C(A, X)) (g : C(A, Y)) :
    TopologicalPushout f g ≃ₜ TopologicalPushout g f where
  toFun := topologicalPushoutCommMap f g
  invFun := topologicalPushoutCommMap g f
  left_inv z := by
    rcases topologicalPushout_jointly_surjective f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · simp
    · simp
  right_inv z := by
    rcases topologicalPushout_jointly_surjective g f z with ⟨y, rfl⟩ | ⟨x, rfl⟩
    · simp
    · simp
  continuous_toFun := (topologicalPushoutCommMap f g).continuous
  continuous_invFun := (topologicalPushoutCommMap g f).continuous

@[simp]
theorem topologicalPushoutComm_inl
    (f : C(A, X)) (g : C(A, Y)) (x : X) :
    topologicalPushoutComm f g (topologicalPushoutInl f g x) =
      topologicalPushoutInr g f x :=
  topologicalPushoutCommMap_inl f g x

@[simp]
theorem topologicalPushoutComm_inr
    (f : C(A, X)) (g : C(A, Y)) (y : Y) :
    topologicalPushoutComm f g (topologicalPushoutInr f g y) =
      topologicalPushoutInl g f y :=
  topologicalPushoutCommMap_inr f g y

@[simp]
theorem topologicalPushoutComm_symm_inl
    (f : C(A, X)) (g : C(A, Y)) (y : Y) :
    (topologicalPushoutComm f g).symm (topologicalPushoutInl g f y) =
      topologicalPushoutInr f g y :=
  topologicalPushoutCommMap_inl g f y

@[simp]
theorem topologicalPushoutComm_symm_inr
    (f : C(A, X)) (g : C(A, Y)) (x : X) :
    (topologicalPushoutComm f g).symm (topologicalPushoutInr g f x) =
      topologicalPushoutInl f g x :=
  topologicalPushoutCommMap_inr g f x

/-- Swapping the two legs twice is the identity homeomorphism. -/
theorem topologicalPushoutComm_trans
    (f : C(A, X)) (g : C(A, Y)) :
    (topologicalPushoutComm f g).trans (topologicalPushoutComm g f) =
      Homeomorph.refl (TopologicalPushout f g) := by
  ext z
  rcases topologicalPushout_jointly_surjective f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · simp
  · simp

end SplittingSpheres
