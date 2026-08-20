/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutCongr
public import SplittingSpheres.Foundations.TopologicalPushoutProduct

/-!
# Left products of topological pushouts

This file is the factor-swapped companion to `TopologicalPushoutProduct`.  Under the same
compactness, Hausdorffness, and injectivity hypotheses, it identifies the pushout obtained by
placing a fixed space on the left of every object with the product of that space and the
original pushout.

The proof first swaps the two factors in the complete pushout diagram, applies the existing
right-product theorem, and swaps the factors back.  The two coprojection formulas are literal.
-/

@[expose] public section

noncomputable section

open Function Topology

universe u

namespace SplittingSpheres

variable {A X Y : Type u}
variable [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]

section LeftProduct

variable (Z : Type u) [TopologicalSpace Z]
variable (f : C(A, X)) (g : C(A, Y))
variable [CompactSpace X] [CompactSpace Y] [CompactSpace Z]
variable [T2Space (TopologicalPushout f g)] [T2Space Z]

/-- Taking a compact Hausdorff factor on the left distributes over a topological pushout,
provided both original attaching maps are injective. -/
def topologicalPushoutLeftProductHomeomorph
    (hf : Injective f) (hg : Injective g) :
    TopologicalPushout
        ((ContinuousMap.id Z).prodMap f)
        ((ContinuousMap.id Z).prodMap g) ≃ₜ
      Z × TopologicalPushout f g :=
  (topologicalPushoutCongr
      ((ContinuousMap.id Z).prodMap f)
      ((ContinuousMap.id Z).prodMap g)
      (f.prodMap (ContinuousMap.id Z))
      (g.prodMap (ContinuousMap.id Z))
      (Homeomorph.prodComm Z A)
      (Homeomorph.prodComm Z X)
      (Homeomorph.prodComm Z Y)
      (by rintro ⟨z, a⟩; rfl) (by rintro ⟨z, a⟩; rfl)).trans <|
    (topologicalPushoutProductHomeomorph f g Z hf hg).trans
      (Homeomorph.prodComm (TopologicalPushout f g) Z)

@[simp]
theorem topologicalPushoutLeftProductHomeomorph_inl
    (hf : Injective f) (hg : Injective g) (z : Z) (x : X) :
    topologicalPushoutLeftProductHomeomorph Z f g hf hg
        (topologicalPushoutInl
          ((ContinuousMap.id Z).prodMap f)
          ((ContinuousMap.id Z).prodMap g) (z, x)) =
      (z, topologicalPushoutInl f g x) := by
  rw [topologicalPushoutLeftProductHomeomorph, Homeomorph.trans_apply,
    Homeomorph.trans_apply, topologicalPushoutCongr_inl,
    topologicalPushoutProductHomeomorph_inl]
  rfl

@[simp]
theorem topologicalPushoutLeftProductHomeomorph_inr
    (hf : Injective f) (hg : Injective g) (z : Z) (y : Y) :
    topologicalPushoutLeftProductHomeomorph Z f g hf hg
        (topologicalPushoutInr
          ((ContinuousMap.id Z).prodMap f)
          ((ContinuousMap.id Z).prodMap g) (z, y)) =
      (z, topologicalPushoutInr f g y) := by
  rw [topologicalPushoutLeftProductHomeomorph, Homeomorph.trans_apply,
    Homeomorph.trans_apply, topologicalPushoutCongr_inr,
    topologicalPushoutProductHomeomorph_inr]
  rfl

end LeftProduct

end SplittingSpheres
