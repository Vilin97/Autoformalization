/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalCoverPullback

/-!
# Transporting a topological pullback along a base homeomorphism

If `e : Y ≃ₜ Z`, the pullback of `p` along `f ∘ e` is canonically homeomorphic to the pullback
along `f`.  The homeomorphism changes only the base coordinate.  This point-set construction is
useful for moving explicit covers across a geometric decomposition without assigning any smooth
structure to the new base.
-/

@[expose] public section

noncomputable section

open Function Topology

namespace SplittingSpheres

universe uE uX uY uZ

variable {E : Type uE} {X : Type uX} {Y : Type uY} {Z : Type uZ}
variable [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Change the base coordinate of a pullback by a homeomorphism. -/
def topologicalCoverPullbackBaseHomeomorph (p : E → X) (f : Z → X)
    (e : Y ≃ₜ Z) :
    TopologicalCoverPullback p (f ∘ e) ≃ₜ TopologicalCoverPullback p f where
  toFun z := ⟨(e z.1.1, z.1.2), z.2⟩
  invFun z := ⟨(e.symm z.1.1, z.1.2), by
    change f (e (e.symm z.1.1)) = p z.1.2
    rw [e.apply_symm_apply]
    exact z.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact e.symm_apply_apply z.1.1
    · rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact e.apply_symm_apply z.1.1
    · rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (e.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (e.symm.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)

omit [TopologicalSpace X] in
@[simp]
theorem topologicalCoverPullbackBaseHomeomorph_base (p : E → X) (f : Z → X)
    (e : Y ≃ₜ Z) (z : TopologicalCoverPullback p (f ∘ e)) :
    (topologicalCoverPullbackBaseHomeomorph p f e z).1.1 = e z.1.1 :=
  rfl

omit [TopologicalSpace X] in
@[simp]
theorem topologicalCoverPullbackBaseHomeomorph_fiberCoordinate
    (p : E → X) (f : Z → X) (e : Y ≃ₜ Z)
    (z : TopologicalCoverPullback p (f ∘ e)) :
    (topologicalCoverPullbackBaseHomeomorph p f e z).1.2 = z.1.2 :=
  rfl

omit [TopologicalSpace X] in
@[simp]
theorem topologicalCoverPullbackBaseHomeomorph_proj (p : E → X) (f : Z → X)
    (e : Y ≃ₜ Z) (z : TopologicalCoverPullback p (f ∘ e)) :
    topologicalCoverPullbackProj p f
        (topologicalCoverPullbackBaseHomeomorph p f e z) =
      e (topologicalCoverPullbackProj p (f ∘ e) z) :=
  rfl

omit [TopologicalSpace X] in
@[simp]
theorem topologicalCoverPullbackBaseHomeomorph_symm_proj
    (p : E → X) (f : Z → X) (e : Y ≃ₜ Z)
    (z : TopologicalCoverPullback p f) :
    topologicalCoverPullbackProj p (f ∘ e)
        ((topologicalCoverPullbackBaseHomeomorph p f e).symm z) =
      e.symm (topologicalCoverPullbackProj p f z) :=
  rfl

end SplittingSpheres
