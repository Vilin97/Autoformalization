/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutHomeomorph

/-!
# Products of topological pushouts

This file identifies the pushout obtained by taking the product of both legs of a topological
pushout diagram with a fixed compact Hausdorff space.  Under injectivity of the original
attaching maps, the resulting pushout is canonically homeomorphic to the product of the
original pushout with that space.

The construction uses the compact-to-Hausdorff recognition theorem for concrete topological
pushouts.  Its action on both coprojections is literal.
-/

@[expose] public section

noncomputable section

open Function Set Topology

universe u

namespace SplittingSpheres

variable {A X Y : Type u}
variable [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]

section Product

variable (f : C(A, X)) (g : C(A, Y)) (Z : Type u)
variable [TopologicalSpace Z]
variable [CompactSpace X] [CompactSpace Y] [CompactSpace Z]
variable [T2Space (TopologicalPushout f g)] [T2Space Z]

/-- Taking a product with a compact Hausdorff space distributes over a topological pushout,
provided both original attaching maps are injective. -/
def topologicalPushoutProductHomeomorph
    (hf : Injective f) (hg : Injective g) :
    TopologicalPushout
        (f.prodMap (ContinuousMap.id Z))
        (g.prodMap (ContinuousMap.id Z)) ≃ₜ
      TopologicalPushout f g × Z :=
  topologicalPushoutHomeomorph
    (f.prodMap (ContinuousMap.id Z))
    (g.prodMap (ContinuousMap.id Z))
    ((topologicalPushoutInl f g).prodMap (ContinuousMap.id Z))
    ((topologicalPushoutInr f g).prodMap (ContinuousMap.id Z))
    (by
      rintro ⟨a, z⟩
      exact Prod.ext (topologicalPushout_condition f g a) rfl)
    (hf.prodMap injective_id)
    ((topologicalPushoutInl_injective f g hg).prodMap injective_id)
    ((topologicalPushoutInr_injective f g hf).prodMap injective_id)
    (by
      rintro ⟨x, z⟩ ⟨y, w⟩ hxy
      have hfirst : topologicalPushoutInl f g x =
          topologicalPushoutInr f g y :=
        congrArg Prod.fst hxy
      have hsecond : z = w := congrArg Prod.snd hxy
      obtain ⟨a, hfa, hga⟩ :=
        (topologicalPushoutInl_eq_inr_iff f g hf x y).mp hfirst
      exact ⟨(a, z), Prod.ext hfa rfl, Prod.ext hga hsecond⟩)
    (by
      ext wz
      constructor
      · exact fun _ ↦ mem_univ wz
      · intro _
        rcases wz with ⟨w, z⟩
        rcases topologicalPushout_jointly_surjective f g w with
          ⟨x, rfl⟩ | ⟨y, rfl⟩
        · exact Or.inl ⟨(x, z), rfl⟩
        · exact Or.inr ⟨(y, z), rfl⟩)

@[simp]
theorem topologicalPushoutProductHomeomorph_inl
    (hf : Injective f) (hg : Injective g) (x : X) (z : Z) :
    topologicalPushoutProductHomeomorph f g Z hf hg
        (topologicalPushoutInl
          (f.prodMap (ContinuousMap.id Z))
          (g.prodMap (ContinuousMap.id Z)) (x, z)) =
      (topologicalPushoutInl f g x, z) := by
  apply topologicalPushoutHomeomorph_inl

@[simp]
theorem topologicalPushoutProductHomeomorph_inr
    (hf : Injective f) (hg : Injective g) (y : Y) (z : Z) :
    topologicalPushoutProductHomeomorph f g Z hf hg
        (topologicalPushoutInr
          (f.prodMap (ContinuousMap.id Z))
          (g.prodMap (ContinuousMap.id Z)) (y, z)) =
      (topologicalPushoutInr f g y, z) := by
  apply topologicalPushoutHomeomorph_inr

end Product

end SplittingSpheres
