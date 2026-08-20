/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushout

/-!
# Closed embeddings into topological pushouts

This file records the final-topology description of a topological pushout and uses it to prove
the standard closed-attachment theorem.  If one attaching map is a closed embedding, then the
coprojection of the opposite piece is a closed embedding.  No compactness or separation
hypothesis is needed.

The cross-preimage formulas below also describe exactly how the images of the two pieces meet.
These are point-set topological results; they do not assert that a pushout carries a manifold or
smooth gluing structure.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Function Set Topology

universe u

namespace SplittingSpheres

variable {A X Y : Type u}
variable [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(A, X)) (g : C(A, Y))

/-! ## The final topology and cross-piece fibers -/

/-- A set in a topological pushout is closed exactly when its inverse images in both pieces are
closed.  The condition at the central object of the walking span follows from either piece by
continuity of the corresponding attaching map. -/
theorem isClosed_topologicalPushout_iff (s : Set (TopologicalPushout f g)) :
    IsClosed s ↔
      IsClosed ((topologicalPushoutInl f g) ⁻¹' s) ∧
        IsClosed ((topologicalPushoutInr f g) ⁻¹' s) := by
  rw [TopCat.isClosed_iff_of_isColimit
    (pushout.cocone (TopCat.ofHom f) (TopCat.ofHom g))
    (pushout.isColimit (TopCat.ofHom f) (TopCat.ofHom g))]
  constructor
  · intro h
    exact ⟨h WalkingSpan.left, h WalkingSpan.right⟩
  · rintro ⟨hX, hY⟩ j
    rcases j with _ | j
    · rw [PushoutCocone.condition_zero]
      change IsClosed ((fun a ↦ topologicalPushoutInl f g (f a)) ⁻¹' s)
      simpa only [Set.preimage_preimage] using hX.preimage f.continuous
    · rcases j with _ | _
      · exact hX
      · exact hY

/-- Symmetric form of `topologicalPushoutInl_eq_inr_iff`: injectivity of the right attaching
map is enough to characterize a cross-piece equality by a common attaching point. -/
theorem topologicalPushoutInl_eq_inr_iff_of_injective_g
    (hg : Injective g) (x : X) (y : Y) :
    topologicalPushoutInl f g x = topologicalPushoutInr f g y ↔
      ∃ a, f a = x ∧ g a = y := by
  have h := Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
    (PushoutCocone.flipIsColimit (topologicalPushout_isPushout f g).isColimit)
    hg y x
  rw [eq_comm]
  exact h.trans <| by
    constructor
    · rintro ⟨a, ha, hb⟩
      exact ⟨a, hb, ha⟩
    · rintro ⟨a, ha, hb⟩
      exact ⟨a, hb, ha⟩

/-- The inverse image in the right piece of the image of a left subset consists exactly of
the points obtained from attaching points whose left image belongs to that subset. -/
theorem preimage_topologicalPushoutInr_image_inl_of_injective_g
    (hg : Injective g) (s : Set X) :
    (topologicalPushoutInr f g) ⁻¹' ((topologicalPushoutInl f g) '' s) =
      g '' (f ⁻¹' s) := by
  ext y
  constructor
  · rintro ⟨x, hxs, hxy⟩
    obtain ⟨a, hfa, hga⟩ :=
      (topologicalPushoutInl_eq_inr_iff_of_injective_g f g hg x y).mp hxy
    refine ⟨a, ?_, hga⟩
    change f a ∈ s
    rwa [hfa]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨f a, ha, topologicalPushout_condition f g a⟩

/-- The inverse image in the left piece of the image of a right subset consists exactly of
the points obtained from attaching points whose right image belongs to that subset. -/
theorem preimage_topologicalPushoutInl_image_inr_of_injective_f
    (hf : Injective f) (s : Set Y) :
    (topologicalPushoutInl f g) ⁻¹' ((topologicalPushoutInr f g) '' s) =
      f '' (g ⁻¹' s) := by
  ext x
  constructor
  · rintro ⟨y, hys, hyx⟩
    obtain ⟨a, hfa, hga⟩ :=
      (topologicalPushoutInl_eq_inr_iff f g hf x y).mp hyx.symm
    refine ⟨a, ?_, hfa⟩
    change g a ∈ s
    rwa [hga]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨g a, ha, (topologicalPushout_condition f g a).symm⟩

/-- If the left attaching map is injective, the left piece is exactly the complement of the
image of the part of the right piece which lies away from its attaching locus. -/
theorem range_topologicalPushoutInl_eq_compl_image_inr_compl_range
    (hf : Injective f) :
    range (topologicalPushoutInl f g) =
      ((topologicalPushoutInr f g) '' (range g)ᶜ)ᶜ := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩ hz
    obtain ⟨y, hy, hyx⟩ := hz
    obtain ⟨a, _hfa, hga⟩ :=
      (topologicalPushoutInl_eq_inr_iff f g hf x y).mp hyx.symm
    exact hy ⟨a, hga⟩
  · intro hz
    rcases topologicalPushout_jointly_surjective f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨x, rfl⟩
    · by_cases hy : y ∈ range g
      · obtain ⟨a, rfl⟩ := hy
        exact ⟨f a, topologicalPushout_condition f g a⟩
      · exact False.elim <| hz ⟨y, hy, rfl⟩

/-- Symmetrically, if the right attaching map is injective, the right piece is exactly the
complement of the image of the part of the left piece away from its attaching locus. -/
theorem range_topologicalPushoutInr_eq_compl_image_inl_compl_range
    (hg : Injective g) :
    range (topologicalPushoutInr f g) =
      ((topologicalPushoutInl f g) '' (range f)ᶜ)ᶜ := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩ hz
    obtain ⟨x, hx, hxy⟩ := hz
    obtain ⟨a, hfa, _hga⟩ :=
      (topologicalPushoutInl_eq_inr_iff_of_injective_g f g hg x y).mp hxy
    exact hx ⟨a, hfa⟩
  · intro hz
    rcases topologicalPushout_jointly_surjective f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · by_cases hx : x ∈ range f
      · obtain ⟨a, rfl⟩ := hx
        exact ⟨g a, (topologicalPushout_condition f g a).symm⟩
      · exact False.elim <| hz ⟨x, hx, rfl⟩
    · exact ⟨y, rfl⟩

/-! ## Closed embeddings of the two pieces -/

/-- A closed embedding on the right attaching leg makes the left coprojection a closed
embedding. -/
theorem isClosedEmbedding_topologicalPushoutInl
    (hg : IsClosedEmbedding g) :
    IsClosedEmbedding (topologicalPushoutInl f g) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
  · exact (topologicalPushoutInl f g).continuous
  · exact topologicalPushoutInl_injective f g hg.injective
  · intro s hs
    rw [isClosed_topologicalPushout_iff f g]
    constructor
    · rwa [preimage_image_eq _ (topologicalPushoutInl_injective f g hg.injective)]
    · rw [preimage_topologicalPushoutInr_image_inl_of_injective_g f g hg.injective]
      exact hg.isClosedMap _ (hs.preimage f.continuous)

/-- A closed embedding on the left attaching leg makes the right coprojection a closed
embedding. -/
theorem isClosedEmbedding_topologicalPushoutInr
    (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (topologicalPushoutInr f g) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
  · exact (topologicalPushoutInr f g).continuous
  · exact topologicalPushoutInr_injective f g hf.injective
  · intro s hs
    rw [isClosed_topologicalPushout_iff f g]
    constructor
    · rw [preimage_topologicalPushoutInl_image_inr_of_injective_f f g hf.injective]
      exact hf.isClosedMap _ (hs.preimage g.continuous)
    · rwa [preimage_image_eq _ (topologicalPushoutInr_injective f g hf.injective)]

/-! ## Compact-to-Hausdorff fallbacks -/

/-- In the compact-to-Hausdorff setting, injectivity of the right attaching map alone makes
the left coprojection a closed embedding. -/
theorem isClosedEmbedding_topologicalPushoutInl_of_compact_t2
    [CompactSpace X] [T2Space (TopologicalPushout f g)]
    (hg : Injective g) :
    IsClosedEmbedding (topologicalPushoutInl f g) :=
  (topologicalPushoutInl f g).continuous.isClosedEmbedding
    (topologicalPushoutInl_injective f g hg)

/-- In the compact-to-Hausdorff setting, injectivity of the left attaching map alone makes
the right coprojection a closed embedding. -/
theorem isClosedEmbedding_topologicalPushoutInr_of_compact_t2
    [CompactSpace Y] [T2Space (TopologicalPushout f g)]
    (hf : Injective f) :
    IsClosedEmbedding (topologicalPushoutInr f g) :=
  (topologicalPushoutInr f g).continuous.isClosedEmbedding
    (topologicalPushoutInr_injective f g hf)

/-- The corresponding embedding statement for the left coprojection. -/
theorem isEmbedding_topologicalPushoutInl
    (hg : IsClosedEmbedding g) :
    IsEmbedding (topologicalPushoutInl f g) :=
  (isClosedEmbedding_topologicalPushoutInl f g hg).isEmbedding

/-- The corresponding embedding statement for the right coprojection. -/
theorem isEmbedding_topologicalPushoutInr
    (hf : IsClosedEmbedding f) :
    IsEmbedding (topologicalPushoutInr f g) :=
  (isClosedEmbedding_topologicalPushoutInr f g hf).isEmbedding

/-- The left piece has closed image when the right attaching leg is a closed embedding. -/
theorem isClosed_range_topologicalPushoutInl
    (hg : IsClosedEmbedding g) :
    IsClosed (range (topologicalPushoutInl f g)) :=
  (isClosedEmbedding_topologicalPushoutInl f g hg).isClosed_range

/-- The right piece has closed image when the left attaching leg is a closed embedding. -/
theorem isClosed_range_topologicalPushoutInr
    (hf : IsClosedEmbedding f) :
    IsClosed (range (topologicalPushoutInr f g)) :=
  (isClosedEmbedding_topologicalPushoutInr f g hf).isClosed_range

/-- Under closed-embedding attaching maps, the two closed piece images meet exactly in the
image of the common attaching space. -/
theorem range_topologicalPushoutInl_inter_range_topologicalPushoutInr_of_closedEmbeddings
    (hf : IsClosedEmbedding f) (_hg : IsClosedEmbedding g) :
    range (topologicalPushoutInl f g) ∩ range (topologicalPushoutInr f g) =
      range (fun a ↦ topologicalPushoutInl f g (f a)) :=
  range_topologicalPushoutInl_inter_range_topologicalPushoutInr f g hf.injective

end SplittingSpheres
