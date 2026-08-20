/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutSeparation

/-!
# Separation by one labelled fiber of a topological pushout seam

Suppose the attaching source of a topological pushout is `I × A`, where `I` is discrete,
and the left target has a continuous label map to `I` which the left attaching map preserves.
For each `i : I`, removing only the `i`-labelled part of the seam separates the interior of
the `i`-labelled left piece from the rest of the pushout.

The theorem is point-set and does not assert that either side is nonempty.  Concrete
applications must provide witnesses away from the attaching locus.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Function Set Topology
open Set.Notation

universe u

namespace SplittingSpheres

variable {I A X Y : Type u}
variable [TopologicalSpace I] [TopologicalSpace A]
variable [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(I × A, X)) (g : C(I × A, Y))
variable (label : C(X, I))

/-- The `i`-labelled part of the common seam. -/
def topologicalPushoutFiberSeam (i : I) : Set (TopologicalPushout f g) :=
  range (fun a ↦ topologicalPushoutInl f g (f (i, a)))

/-- The `i`-labelled part of the left piece, away from the full attaching locus. -/
def topologicalPushoutInlFiberOffSeam (i : I) :
    Set (TopologicalPushout f g) :=
  topologicalPushoutInl f g '' {x | label x = i ∧ x ∉ range f}

/-- Everything outside the selected seam except its labelled left off-seam side. -/
def topologicalPushoutFiberRest (i : I) : Set (TopologicalPushout f g) :=
  (topologicalPushoutFiberSeam f g i)ᶜ \
    topologicalPushoutInlFiberOffSeam f g label i

/-- A fiber of a closed-embedded map from a discrete product has closed range. -/
theorem isClosed_range_continuousMap_fiber [DiscreteTopology I]
    (hf : IsClosedEmbedding f) (i : I) :
    IsClosed (range (fun a ↦ f (i, a))) := by
  have hs : IsClosed ({z : I × A | z.1 = i}) := by
    exact (isClosed_discrete {i}).preimage continuous_fst
  have hi : f '' {z : I × A | z.1 = i} =
      range (fun a ↦ f (i, a)) := by
    ext x
    constructor
    · rintro ⟨⟨j, a⟩, hj, rfl⟩
      change j = i at hj
      subst j
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(i, a), rfl, rfl⟩
  rw [← hi]
  exact hf.isClosedMap _ hs

private theorem preimage_topologicalPushoutInlFiberOffSeam_inl
    (hg : IsClosedEmbedding g) (i : I) :
    topologicalPushoutInl f g ⁻¹'
        topologicalPushoutInlFiberOffSeam f g label i =
      {x | label x = i ∧ x ∉ range f} := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := (topologicalPushoutInl_injective f g hg.injective) hxy
    rwa [this] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem preimage_topologicalPushoutInlFiberOffSeam_inr
    (hf : IsClosedEmbedding f) (i : I) :
    topologicalPushoutInr f g ⁻¹'
        topologicalPushoutInlFiberOffSeam f g label i = ∅ := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨z, hzx, _⟩ :=
      (topologicalPushoutInl_eq_inr_iff f g hf.injective x y).mp hxy
    exact False.elim (hx.2 ⟨z, hzx⟩)
  · simp

/-- The selected labelled left side is open. -/
theorem isOpen_topologicalPushoutInlFiberOffSeam [DiscreteTopology I]
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) (i : I) :
    IsOpen (topologicalPushoutInlFiberOffSeam f g label i) := by
  rw [isOpen_topologicalPushout_iff]
  rw [preimage_topologicalPushoutInlFiberOffSeam_inl f g label hg,
    preimage_topologicalPushoutInlFiberOffSeam_inr f g label hf]
  constructor
  · exact ((isOpen_discrete {i}).preimage label.continuous).inter
      hf.isClosed_range.isOpen_compl
  · exact isOpen_empty

private theorem preimage_topologicalPushoutFiberRest_inl
    (hg : IsClosedEmbedding g) (hlabel : ∀ z, label (f z) = z.1)
    (i : I) :
    topologicalPushoutInl f g ⁻¹'
        topologicalPushoutFiberRest f g label i =
      label ⁻¹' {i}ᶜ := by
  ext x
  constructor
  · rintro ⟨hxSeam, hxOff⟩
    simp only [mem_preimage, mem_compl_iff, mem_singleton_iff]
    intro hxi
    apply hxOff
    by_cases hxf : x ∈ range f
    · obtain ⟨⟨j, a⟩, hja⟩ := hxf
      have hj : j = i := by
        rw [← hxi, ← hja, hlabel]
      subst j
      apply False.elim
      apply hxSeam
      exact ⟨a, congrArg (topologicalPushoutInl f g) hja⟩
    · exact ⟨x, ⟨hxi, hxf⟩, rfl⟩
  · intro hxi
    have hxi' : label x ≠ i := by simpa using hxi
    constructor
    · rintro ⟨a, ha⟩
      have hxf : x = f (i, a) :=
        (topologicalPushoutInl_injective f g hg.injective) ha.symm
      exact hxi' (by rw [hxf, hlabel])
    · rintro ⟨y, hy, hxy⟩
      have hyx : y = x :=
        (topologicalPushoutInl_injective f g hg.injective) hxy
      exact hxi' (hyx ▸ hy.1)

private theorem preimage_topologicalPushoutFiberSeam_inr
    (hf : IsClosedEmbedding f) (i : I) :
    topologicalPushoutInr f g ⁻¹' topologicalPushoutFiberSeam f g i =
      range (fun a ↦ g (i, a)) := by
  ext y
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨z, hzf, hzg⟩ :=
      (topologicalPushoutInl_eq_inr_iff f g hf.injective
        (f (i, a)) y).mp ha
    have hz : z = (i, a) := hf.injective hzf
    subst z
    exact ⟨a, hzg⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, topologicalPushout_condition f g (i, a)⟩

private theorem preimage_topologicalPushoutFiberRest_inr
    (hf : IsClosedEmbedding f) (i : I) :
    topologicalPushoutInr f g ⁻¹'
        topologicalPushoutFiberRest f g label i =
      (range (fun a ↦ g (i, a)))ᶜ := by
  rw [topologicalPushoutFiberRest, preimage_sdiff, preimage_compl,
    preimage_topologicalPushoutFiberSeam_inr f g hf,
    preimage_topologicalPushoutInlFiberOffSeam_inr f g label hf]
  simp

/-- The rest of the pushout away from the selected fiber seam is open. -/
theorem isOpen_topologicalPushoutFiberRest [DiscreteTopology I]
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (hlabel : ∀ z, label (f z) = z.1) (i : I) :
    IsOpen (topologicalPushoutFiberRest f g label i) := by
  rw [isOpen_topologicalPushout_iff,
    preimage_topologicalPushoutFiberRest_inl f g label hg hlabel,
    preimage_topologicalPushoutFiberRest_inr f g label hf]
  exact ⟨(isOpen_discrete _).preimage label.continuous,
    (isClosed_range_continuousMap_fiber g hg i).isOpen_compl⟩

private theorem topologicalPushoutInlFiberOffSeam_subset_compl
    (hg : IsClosedEmbedding g) (i : I) :
    topologicalPushoutInlFiberOffSeam f g label i ⊆
      (topologicalPushoutFiberSeam f g i)ᶜ := by
  rintro _ ⟨x, hx, rfl⟩ ⟨a, ha⟩
  have hxf : x = f (i, a) :=
    (topologicalPushoutInl_injective f g hg.injective) ha.symm
  exact hx.2 ⟨(i, a), hxf.symm⟩

/-- The two displayed sides cover the complement of the selected fiber seam. -/
theorem union_topologicalPushoutFiberSides
    (hg : IsClosedEmbedding g) (i : I) :
    topologicalPushoutInlFiberOffSeam f g label i ∪
        topologicalPushoutFiberRest f g label i =
      (topologicalPushoutFiberSeam f g i)ᶜ := by
  rw [topologicalPushoutFiberRest]
  exact union_sdiff_cancel
    (topologicalPushoutInlFiberOffSeam_subset_compl f g label hg i)

/-- The selected labelled left side and the rest are disjoint. -/
theorem disjoint_topologicalPushoutFiberSides (i : I) :
    Disjoint (topologicalPushoutInlFiberOffSeam f g label i)
      (topologicalPushoutFiberRest f g label i) := by
  rw [topologicalPushoutFiberRest]
  exact disjoint_sdiff_right

/-- Inside the complement of one fiber seam, its labelled left side is clopen. -/
theorem isClopen_topologicalPushoutInlFiberOffSeam_restrict
    [DiscreteTopology I]
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (hlabel : ∀ z, label (f z) = z.1) (i : I) :
    IsClopen (((topologicalPushoutFiberSeam f g i)ᶜ) ↓∩
      topologicalPushoutInlFiberOffSeam f g label i) := by
  have hoff :=
    isOpen_topologicalPushoutInlFiberOffSeam f g label hf hg i
  have hrest := isOpen_topologicalPushoutFiberRest f g label hf hg hlabel i
  constructor
  · rw [← isOpen_compl_iff]
    have heq : ((((topologicalPushoutFiberSeam f g i)ᶜ) ↓∩
        topologicalPushoutInlFiberOffSeam f g label i) :
          Set (↑(topologicalPushoutFiberSeam f g i)ᶜ))ᶜ =
        (((topologicalPushoutFiberSeam f g i)ᶜ) ↓∩
          topologicalPushoutFiberRest f g label i) := by
      ext z
      have hzcover := congrArg
        (fun s : Set (TopologicalPushout f g) ↦ z.1 ∈ s)
        (union_topologicalPushoutFiberSides f g label hg i)
      have hzdisjoint := Set.disjoint_left.1
        (disjoint_topologicalPushoutFiberSides f g label i)
      simp only [Set.mem_compl_iff, Set.mem_preimage] at hzcover ⊢
      constructor
      · intro hznot
        rcases hzcover.mpr z.2 with hzoff | hzrest
        · exact False.elim (hznot hzoff)
        · exact hzrest
      · intro hzrest hzoff
        exact hzdisjoint hzoff hzrest
    rw [heq]
    exact hrest.preimage continuous_subtype_val
  · exact hoff.preimage continuous_subtype_val

/-- Witnesses on the two sides lie in distinct relative connected components after removing
the selected fiber seam. -/
theorem connectedComponentIn_ne_of_mem_topologicalPushoutFiberSides
    [DiscreteTopology I]
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (hlabel : ∀ z, label (f z) = z.1) (i : I)
    (x y : TopologicalPushout f g)
    (hxSeam : x ∉ topologicalPushoutFiberSeam f g i)
    (hySeam : y ∉ topologicalPushoutFiberSeam f g i)
    (hx : x ∈ topologicalPushoutInlFiberOffSeam f g label i)
    (hy : y ∈ topologicalPushoutFiberRest f g label i) :
    connectedComponentIn (topologicalPushoutFiberSeam f g i)ᶜ x ≠
      connectedComponentIn (topologicalPushoutFiberSeam f g i)ᶜ y := by
  let xs : ↑(topologicalPushoutFiberSeam f g i)ᶜ := ⟨x, hxSeam⟩
  let ys : ↑(topologicalPushoutFiberSeam f g i)ᶜ := ⟨y, hySeam⟩
  intro hxy
  have himage :
      ((fun z : ↑(topologicalPushoutFiberSeam f g i)ᶜ ↦ z.1) ''
          connectedComponent xs) =
        ((fun z : ↑(topologicalPushoutFiberSeam f g i)ᶜ ↦ z.1) ''
          connectedComponent ys) := by
    rw [← connectedComponentIn_eq_image xs.2,
      ← connectedComponentIn_eq_image ys.2]
    exact hxy
  have hcomponents : connectedComponent xs = connectedComponent ys :=
    (Set.image_injective.mpr Subtype.val_injective) himage
  have hx' : xs ∈ (((topologicalPushoutFiberSeam f g i)ᶜ) ↓∩
      topologicalPushoutInlFiberOffSeam f g label i) := hx
  have hycomp : ys ∈ connectedComponent xs := by
    rw [hcomponents]
    exact mem_connectedComponent
  have hyleft :=
    (isClopen_topologicalPushoutInlFiberOffSeam_restrict
      f g label hf hg hlabel i).connectedComponent_subset hx' hycomp
  exact Set.disjoint_left.1
    (disjoint_topologicalPushoutFiberSides f g label i) hyleft hy

end SplittingSpheres
