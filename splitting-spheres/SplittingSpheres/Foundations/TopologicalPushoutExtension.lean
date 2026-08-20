/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushout

/-!
# Extending a homeomorphism across a topological pushout

If a homeomorphism of the left piece fixes the attaching image pointwise, it extends over
`X ∪_A Y` by the identity on the right piece.  This file constructs the extension directly from
the pushout universal property and proves its inverse and exact action on both pieces.

This is a topological extension theorem.  It does not assert that a smooth diffeomorphism extends
smoothly across a manifold gluing.
-/

@[expose] public section

noncomputable section

open Function Topology

universe u

namespace SplittingSpheres

variable {A X Y : Type u}
variable [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]

section Left

variable (f : C(A, X)) (g : C(A, Y))

/-- The descended continuous map which applies `e` on the left piece and the identity on the
right piece. -/
def topologicalPushoutLeftExtensionMap (e : X ≃ₜ X) (he : ∀ a, e (f a) = f a) :
    C(TopologicalPushout f g, TopologicalPushout f g) :=
  topologicalPushoutDesc f g
    ((topologicalPushoutInl f g).comp ⟨fun x ↦ e x, e.continuous⟩)
    (topologicalPushoutInr f g) (by
      intro a
      change topologicalPushoutInl f g (e (f a)) = topologicalPushoutInr f g (g a)
      rw [he]
      exact topologicalPushout_condition f g a)

@[simp]
theorem topologicalPushoutLeftExtensionMap_inl
    (e : X ≃ₜ X) (he : ∀ a, e (f a) = f a) (x : X) :
    topologicalPushoutLeftExtensionMap f g e he (topologicalPushoutInl f g x) =
      topologicalPushoutInl f g (e x) :=
  topologicalPushoutDesc_inl _ _ _ _ _ x

@[simp]
theorem topologicalPushoutLeftExtensionMap_inr
    (e : X ≃ₜ X) (he : ∀ a, e (f a) = f a) (y : Y) :
    topologicalPushoutLeftExtensionMap f g e he (topologicalPushoutInr f g y) =
      topologicalPushoutInr f g y :=
  topologicalPushoutDesc_inr _ _ _ _ _ y

theorem topologicalPushoutLeftExtension_symm_fixes
    (e : X ≃ₜ X) (he : ∀ a, e (f a) = f a) (a : A) :
    e.symm (f a) = f a := by
  apply e.injective
  rw [e.apply_symm_apply, he]

/-- Extend a left-piece homeomorphism which fixes the attaching image, using the identity on the
right piece. -/
def topologicalPushoutLeftExtension (e : X ≃ₜ X) (he : ∀ a, e (f a) = f a) :
    TopologicalPushout f g ≃ₜ TopologicalPushout f g where
  toFun := topologicalPushoutLeftExtensionMap f g e he
  invFun := topologicalPushoutLeftExtensionMap f g e.symm
    (topologicalPushoutLeftExtension_symm_fixes f e he)
  left_inv z := by
    rcases topologicalPushout_jointly_surjective f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · simp
    · simp
  right_inv z := by
    rcases topologicalPushout_jointly_surjective f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · simp
    · simp
  continuous_toFun := (topologicalPushoutLeftExtensionMap f g e he).continuous
  continuous_invFun :=
    (topologicalPushoutLeftExtensionMap f g e.symm
      (topologicalPushoutLeftExtension_symm_fixes f e he)).continuous

@[simp]
theorem topologicalPushoutLeftExtension_inl
    (e : X ≃ₜ X) (he : ∀ a, e (f a) = f a) (x : X) :
    topologicalPushoutLeftExtension f g e he (topologicalPushoutInl f g x) =
      topologicalPushoutInl f g (e x) :=
  topologicalPushoutLeftExtensionMap_inl f g e he x

@[simp]
theorem topologicalPushoutLeftExtension_inr
    (e : X ≃ₜ X) (he : ∀ a, e (f a) = f a) (y : Y) :
    topologicalPushoutLeftExtension f g e he (topologicalPushoutInr f g y) =
      topologicalPushoutInr f g y :=
  topologicalPushoutLeftExtensionMap_inr f g e he y

/-- The extension fixes a point of the left piece whenever the original homeomorphism does. -/
theorem topologicalPushoutLeftExtension_inl_eq_of_eq
    (e : X ≃ₜ X) (he : ∀ a, e (f a) = f a) {x : X} (hx : e x = x) :
    topologicalPushoutLeftExtension f g e he (topologicalPushoutInl f g x) =
      topologicalPushoutInl f g x := by
  rw [topologicalPushoutLeftExtension_inl, hx]

/-- The identity homeomorphism fixes the attaching image. -/
theorem topologicalPushoutLeftExtension_refl_fixes (a : A) :
    Homeomorph.refl X (f a) = f a := rfl

/-- Extending the identity gives the identity homeomorphism. -/
theorem topologicalPushoutLeftExtension_refl :
    topologicalPushoutLeftExtension f g (Homeomorph.refl X)
        (topologicalPushoutLeftExtension_refl_fixes f) =
      Homeomorph.refl (TopologicalPushout f g) := by
  ext z
  rcases topologicalPushout_jointly_surjective f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · change topologicalPushoutLeftExtensionMap f g (Homeomorph.refl X)
        (topologicalPushoutLeftExtension_refl_fixes f)
        (topologicalPushoutInl f g x) = topologicalPushoutInl f g x
    rw [topologicalPushoutLeftExtensionMap_inl]
    rfl
  · change topologicalPushoutLeftExtensionMap f g (Homeomorph.refl X)
        (topologicalPushoutLeftExtension_refl_fixes f)
        (topologicalPushoutInr f g y) = topologicalPushoutInr f g y
    rw [topologicalPushoutLeftExtensionMap_inr]

/-- The inverse extension acts by the inverse homeomorphism on the left piece. -/
@[simp]
theorem topologicalPushoutLeftExtension_symm_apply_inl
    (e : X ≃ₜ X) (he : ∀ a, e (f a) = f a) (x : X) :
    (topologicalPushoutLeftExtension f g e he).symm (topologicalPushoutInl f g x) =
      topologicalPushoutInl f g (e.symm x) :=
  topologicalPushoutLeftExtensionMap_inl f g e.symm
    (topologicalPushoutLeftExtension_symm_fixes f e he) x

/-- The inverse extension remains the identity on the right piece. -/
@[simp]
theorem topologicalPushoutLeftExtension_symm_apply_inr
    (e : X ≃ₜ X) (he : ∀ a, e (f a) = f a) (y : Y) :
    (topologicalPushoutLeftExtension f g e he).symm (topologicalPushoutInr f g y) =
      topologicalPushoutInr f g y :=
  topologicalPushoutLeftExtensionMap_inr f g e.symm
    (topologicalPushoutLeftExtension_symm_fixes f e he) y

/-- Extension commutes with composition in the literal `Homeomorph.trans` order. -/
theorem topologicalPushoutLeftExtension_trans
    (e d : X ≃ₜ X) (he : ∀ a, e (f a) = f a) (hd : ∀ a, d (f a) = f a) :
    topologicalPushoutLeftExtension f g (e.trans d) (fun a ↦ by simp [he, hd]) =
      (topologicalPushoutLeftExtension f g e he).trans
        (topologicalPushoutLeftExtension f g d hd) := by
  ext z
  rcases topologicalPushout_jointly_surjective f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩ <;> simp

/-- Extension commutes with inversion. -/
theorem topologicalPushoutLeftExtension_symm
    (e : X ≃ₜ X) (he : ∀ a, e (f a) = f a) :
    topologicalPushoutLeftExtension f g e.symm
        (topologicalPushoutLeftExtension_symm_fixes f e he) =
      (topologicalPushoutLeftExtension f g e he).symm := by
  ext z
  rcases topologicalPushout_jointly_surjective f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · rw [topologicalPushoutLeftExtension_inl,
      topologicalPushoutLeftExtension_symm_apply_inl]
  · rw [topologicalPushoutLeftExtension_inr,
      topologicalPushoutLeftExtension_symm_apply_inr]

end Left

end SplittingSpheres
