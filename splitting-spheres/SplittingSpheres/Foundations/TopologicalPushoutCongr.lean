/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushout

/-!
# Transporting a topological pushout diagram

Compatible homeomorphisms of an attaching space and its two target pieces induce a
homeomorphism of the corresponding topological pushouts.  The construction is directly by the
pushout universal property, and its action on both coprojections is literal.
-/

@[expose] public section

noncomputable section

open Function Topology

universe u

namespace SplittingSpheres

variable {A A' X X' Y Y' : Type u}
variable [TopologicalSpace A] [TopologicalSpace A']
variable [TopologicalSpace X] [TopologicalSpace X']
variable [TopologicalSpace Y] [TopologicalSpace Y']

/-- The descended forward map induced by a compatible equivalence of pushout diagrams. -/
def topologicalPushoutCongrMap
    (f : C(A, X)) (g : C(A, Y)) (f' : C(A', X')) (g' : C(A', Y'))
    (eA : A ≃ₜ A') (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (hf : ∀ a, eX (f a) = f' (eA a))
    (hg : ∀ a, eY (g a) = g' (eA a)) :
    C(TopologicalPushout f g, TopologicalPushout f' g') :=
  topologicalPushoutDesc f g
    ((topologicalPushoutInl f' g').comp ⟨eX, eX.continuous⟩)
    ((topologicalPushoutInr f' g').comp ⟨eY, eY.continuous⟩) (by
      intro a
      change topologicalPushoutInl f' g' (eX (f a)) =
        topologicalPushoutInr f' g' (eY (g a))
      rw [hf, hg]
      exact topologicalPushout_condition f' g' (eA a))

@[simp]
theorem topologicalPushoutCongrMap_inl
    (f : C(A, X)) (g : C(A, Y)) (f' : C(A', X')) (g' : C(A', Y'))
    (eA : A ≃ₜ A') (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (hf : ∀ a, eX (f a) = f' (eA a))
    (hg : ∀ a, eY (g a) = g' (eA a)) (x : X) :
    topologicalPushoutCongrMap f g f' g' eA eX eY hf hg
        (topologicalPushoutInl f g x) =
      topologicalPushoutInl f' g' (eX x) :=
  topologicalPushoutDesc_inl _ _ _ _ _ x

@[simp]
theorem topologicalPushoutCongrMap_inr
    (f : C(A, X)) (g : C(A, Y)) (f' : C(A', X')) (g' : C(A', Y'))
    (eA : A ≃ₜ A') (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (hf : ∀ a, eX (f a) = f' (eA a))
    (hg : ∀ a, eY (g a) = g' (eA a)) (y : Y) :
    topologicalPushoutCongrMap f g f' g' eA eX eY hf hg
        (topologicalPushoutInr f g y) =
      topologicalPushoutInr f' g' (eY y) :=
  topologicalPushoutDesc_inr _ _ _ _ _ y

/-- Compatibility of the inverse homeomorphisms on the left leg. -/
theorem topologicalPushoutCongr_symm_left
    (f : C(A, X)) (f' : C(A', X'))
    (eA : A ≃ₜ A') (eX : X ≃ₜ X')
    (hf : ∀ a, eX (f a) = f' (eA a)) (a' : A') :
    eX.symm (f' a') = f (eA.symm a') := by
  apply eX.injective
  rw [eX.apply_symm_apply, hf, eA.apply_symm_apply]

/-- Compatibility of the inverse homeomorphisms on the right leg. -/
theorem topologicalPushoutCongr_symm_right
    (g : C(A, Y)) (g' : C(A', Y'))
    (eA : A ≃ₜ A') (eY : Y ≃ₜ Y')
    (hg : ∀ a, eY (g a) = g' (eA a)) (a' : A') :
    eY.symm (g' a') = g (eA.symm a') := by
  apply eY.injective
  rw [eY.apply_symm_apply, hg, eA.apply_symm_apply]

/-- Compatible homeomorphisms of a pushout diagram induce a homeomorphism of pushouts. -/
def topologicalPushoutCongr
    (f : C(A, X)) (g : C(A, Y)) (f' : C(A', X')) (g' : C(A', Y'))
    (eA : A ≃ₜ A') (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (hf : ∀ a, eX (f a) = f' (eA a))
    (hg : ∀ a, eY (g a) = g' (eA a)) :
    TopologicalPushout f g ≃ₜ TopologicalPushout f' g' where
  toFun := topologicalPushoutCongrMap f g f' g' eA eX eY hf hg
  invFun := topologicalPushoutCongrMap f' g' f g eA.symm eX.symm eY.symm
    (topologicalPushoutCongr_symm_left f f' eA eX hf)
    (topologicalPushoutCongr_symm_right g g' eA eY hg)
  left_inv z := by
    rcases topologicalPushout_jointly_surjective f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · simp
    · simp
  right_inv z := by
    rcases topologicalPushout_jointly_surjective f' g' z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · simp
    · simp
  continuous_toFun :=
    (topologicalPushoutCongrMap f g f' g' eA eX eY hf hg).continuous
  continuous_invFun :=
    (topologicalPushoutCongrMap f' g' f g eA.symm eX.symm eY.symm
      (topologicalPushoutCongr_symm_left f f' eA eX hf)
      (topologicalPushoutCongr_symm_right g g' eA eY hg)).continuous

@[simp]
theorem topologicalPushoutCongr_inl
    (f : C(A, X)) (g : C(A, Y)) (f' : C(A', X')) (g' : C(A', Y'))
    (eA : A ≃ₜ A') (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (hf : ∀ a, eX (f a) = f' (eA a))
    (hg : ∀ a, eY (g a) = g' (eA a)) (x : X) :
    topologicalPushoutCongr f g f' g' eA eX eY hf hg
        (topologicalPushoutInl f g x) =
      topologicalPushoutInl f' g' (eX x) :=
  topologicalPushoutCongrMap_inl f g f' g' eA eX eY hf hg x

@[simp]
theorem topologicalPushoutCongr_inr
    (f : C(A, X)) (g : C(A, Y)) (f' : C(A', X')) (g' : C(A', Y'))
    (eA : A ≃ₜ A') (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (hf : ∀ a, eX (f a) = f' (eA a))
    (hg : ∀ a, eY (g a) = g' (eA a)) (y : Y) :
    topologicalPushoutCongr f g f' g' eA eX eY hf hg
        (topologicalPushoutInr f g y) =
      topologicalPushoutInr f' g' (eY y) :=
  topologicalPushoutCongrMap_inr f g f' g' eA eX eY hf hg y

@[simp]
theorem topologicalPushoutCongr_symm_inl
    (f : C(A, X)) (g : C(A, Y)) (f' : C(A', X')) (g' : C(A', Y'))
    (eA : A ≃ₜ A') (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (hf : ∀ a, eX (f a) = f' (eA a))
    (hg : ∀ a, eY (g a) = g' (eA a)) (x : X') :
    (topologicalPushoutCongr f g f' g' eA eX eY hf hg).symm
        (topologicalPushoutInl f' g' x) =
      topologicalPushoutInl f g (eX.symm x) :=
  topologicalPushoutCongrMap_inl f' g' f g eA.symm eX.symm eY.symm
    (topologicalPushoutCongr_symm_left f f' eA eX hf)
    (topologicalPushoutCongr_symm_right g g' eA eY hg) x

@[simp]
theorem topologicalPushoutCongr_symm_inr
    (f : C(A, X)) (g : C(A, Y)) (f' : C(A', X')) (g' : C(A', Y'))
    (eA : A ≃ₜ A') (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (hf : ∀ a, eX (f a) = f' (eA a))
    (hg : ∀ a, eY (g a) = g' (eA a)) (y : Y') :
    (topologicalPushoutCongr f g f' g' eA eX eY hf hg).symm
        (topologicalPushoutInr f' g' y) =
      topologicalPushoutInr f g (eY.symm y) :=
  topologicalPushoutCongrMap_inr f' g' f g eA.symm eX.symm eY.symm
    (topologicalPushoutCongr_symm_left f f' eA eX hf)
    (topologicalPushoutCongr_symm_right g g' eA eY hg) y

end SplittingSpheres
