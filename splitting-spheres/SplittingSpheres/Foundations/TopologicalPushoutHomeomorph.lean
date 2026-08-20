module

public import Mathlib.Topology.Homeomorph.Lemmas
public import SplittingSpheres.Foundations.TopologicalPushout

/-!
# Recognizing a concrete topological pushout

This file gives a compact-to-Hausdorff recognition principle for the pushouts defined in
`TopologicalPushout.lean`.  To identify a pushout `X ∪_A Y` with a concrete target `Z`, it is
enough to give compatible continuous maps from the pieces, prove that each piece map is
injective, that their images cover `Z`, and that a cross-piece equality occurs only at a common
attaching point.

The theorem is purely topological.  It does not promote smooth piece maps to a smooth structure
or a diffeomorphism on the pushout.
-/

@[expose] public section

noncomputable section

open Function Set Topology

universe u

namespace SplittingSpheres

variable {A X Y Z : Type u}
variable [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalSpace Z]

section Bijective

variable (f : C(A, X)) (g : C(A, Y))
variable (p : C(X, Z)) (q : C(Y, Z))
variable (h : ∀ a, p (f a) = q (g a))

/-- Piecewise injectivity and an exact cross-piece overlap imply injectivity of the descended
map from the pushout. -/
theorem topologicalPushoutDesc_injective
    (hf : Injective f) (hp : Injective p) (hq : Injective q)
    (hcross : ∀ x y, p x = q y → ∃ a, f a = x ∧ g a = y) :
    Injective (topologicalPushoutDesc f g p q h) := by
  intro z w hzw
  rcases topologicalPushout_jointly_surjective f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩ <;>
    rcases topologicalPushout_jointly_surjective f g w with ⟨x', rfl⟩ | ⟨y', rfl⟩
  · rw [topologicalPushoutDesc_inl, topologicalPushoutDesc_inl] at hzw
    rw [hp hzw]
  · rw [topologicalPushoutDesc_inl, topologicalPushoutDesc_inr] at hzw
    exact (topologicalPushoutInl_eq_inr_iff f g hf x y').mpr (hcross x y' hzw)
  · rw [topologicalPushoutDesc_inr, topologicalPushoutDesc_inl] at hzw
    exact ((topologicalPushoutInl_eq_inr_iff f g hf x' y).mpr
      (hcross x' y hzw.symm)).symm
  · rw [topologicalPushoutDesc_inr, topologicalPushoutDesc_inr] at hzw
    rw [hq hzw]

/-- If the two piece images cover the target, the descended map is surjective. -/
theorem topologicalPushoutDesc_surjective
    (hcover : range p ∪ range q = univ) :
    Surjective (topologicalPushoutDesc f g p q h) := by
  intro z
  have hz : z ∈ range p ∪ range q := by
    rw [hcover]
    exact mem_univ z
  rcases hz with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact ⟨topologicalPushoutInl f g x, topologicalPushoutDesc_inl f g p q h x⟩
  · exact ⟨topologicalPushoutInr f g y, topologicalPushoutDesc_inr f g p q h y⟩

theorem topologicalPushoutDesc_bijective
    (hf : Injective f) (hp : Injective p) (hq : Injective q)
    (hcross : ∀ x y, p x = q y → ∃ a, f a = x ∧ g a = y)
    (hcover : range p ∪ range q = univ) :
    Bijective (topologicalPushoutDesc f g p q h) :=
  ⟨topologicalPushoutDesc_injective f g p q h hf hp hq hcross,
    topologicalPushoutDesc_surjective f g p q h hcover⟩

end Bijective

section Homeomorph

variable (f : C(A, X)) (g : C(A, Y))
variable (p : C(X, Z)) (q : C(Y, Z))
variable (h : ∀ a, p (f a) = q (g a))
variable [CompactSpace X] [CompactSpace Y] [T2Space Z]

/-- Recognize a concrete Hausdorff target as a pushout of two compact spaces. -/
def topologicalPushoutHomeomorph
    (hf : Injective f) (hp : Injective p) (hq : Injective q)
    (hcross : ∀ x y, p x = q y → ∃ a, f a = x ∧ g a = y)
    (hcover : range p ∪ range q = univ) :
    TopologicalPushout f g ≃ₜ Z :=
  ((isHomeomorph_iff_continuous_bijective).mpr
    ⟨(topologicalPushoutDesc f g p q h).continuous,
      topologicalPushoutDesc_bijective f g p q h hf hp hq hcross hcover⟩).homeomorph
        (topologicalPushoutDesc f g p q h)

@[simp]
theorem topologicalPushoutHomeomorph_inl
    (hf : Injective f) (hp : Injective p) (hq : Injective q)
    (hcross : ∀ x y, p x = q y → ∃ a, f a = x ∧ g a = y)
    (hcover : range p ∪ range q = univ) (x : X) :
    topologicalPushoutHomeomorph f g p q h hf hp hq hcross hcover
        (topologicalPushoutInl f g x) = p x :=
  topologicalPushoutDesc_inl f g p q h x

@[simp]
theorem topologicalPushoutHomeomorph_inr
    (hf : Injective f) (hp : Injective p) (hq : Injective q)
    (hcross : ∀ x y, p x = q y → ∃ a, f a = x ∧ g a = y)
    (hcover : range p ∪ range q = univ) (y : Y) :
    topologicalPushoutHomeomorph f g p q h hf hp hq hcross hcover
        (topologicalPushoutInr f g y) = q y :=
  topologicalPushoutDesc_inr f g p q h y

end Homeomorph

end SplittingSpheres
