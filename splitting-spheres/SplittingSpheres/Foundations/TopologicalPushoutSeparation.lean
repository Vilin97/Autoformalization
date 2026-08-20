/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutEmbedding

/-!
# Separation by the seam of a topological pushout

For a pushout of two closed embeddings, removing the common attaching image leaves two open,
disjoint off-seam images.  They cover the seam complement and become complementary clopen sets
inside it.  Consequently points on opposite sides lie in distinct relative connected
components.

These are point-set results.  Nonemptiness of either side must be supplied by a concrete
application, and no path-connectedness or manifold claim is made.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Function Set Topology
open Set.Notation

universe u

namespace SplittingSpheres

variable {A X Y : Type u}
variable [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(A, X)) (g : C(A, Y))

/-- The final topology of a topological pushout, in open-set form. -/
theorem isOpen_topologicalPushout_iff (s : Set (TopologicalPushout f g)) :
    IsOpen s ↔
      IsOpen ((topologicalPushoutInl f g) ⁻¹' s) ∧
        IsOpen ((topologicalPushoutInr f g) ⁻¹' s) := by
  rw [← isClosed_compl_iff, isClosed_topologicalPushout_iff]
  simp only [preimage_compl, isClosed_compl_iff]

/-- The common attaching image in a topological pushout. -/
def topologicalPushoutSeam : Set (TopologicalPushout f g) :=
  range (fun a ↦ topologicalPushoutInl f g (f a))

/-- The image of the part of the left piece away from its attaching locus. -/
def topologicalPushoutInlOffSeam : Set (TopologicalPushout f g) :=
  topologicalPushoutInl f g '' (range f)ᶜ

/-- The image of the part of the right piece away from its attaching locus. -/
def topologicalPushoutInrOffSeam : Set (TopologicalPushout f g) :=
  topologicalPushoutInr f g '' (range g)ᶜ

/-- The left off-seam image is open when both attaching maps are closed embeddings. -/
theorem isOpen_topologicalPushoutInlOffSeam
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    IsOpen (topologicalPushoutInlOffSeam f g) := by
  rw [show topologicalPushoutInlOffSeam f g =
      (range (topologicalPushoutInr f g))ᶜ by
    rw [range_topologicalPushoutInr_eq_compl_image_inl_compl_range
      f g hg.injective]
    simp [topologicalPushoutInlOffSeam]]
  exact (isClosed_range_topologicalPushoutInr f g hf).isOpen_compl

/-- The right off-seam image is open when both attaching maps are closed embeddings. -/
theorem isOpen_topologicalPushoutInrOffSeam
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    IsOpen (topologicalPushoutInrOffSeam f g) := by
  rw [show topologicalPushoutInrOffSeam f g =
      (range (topologicalPushoutInl f g))ᶜ by
    rw [range_topologicalPushoutInl_eq_compl_image_inr_compl_range
      f g hf.injective]
    simp [topologicalPushoutInrOffSeam]]
  exact (isClosed_range_topologicalPushoutInl f g hg).isOpen_compl

/-- The two off-seam images are disjoint.  Injectivity of the left attaching map is enough. -/
theorem disjoint_topologicalPushoutOffSeam (hf : Injective f) :
    Disjoint (topologicalPushoutInlOffSeam f g)
      (topologicalPushoutInrOffSeam f g) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, _hy, hxy⟩
  obtain ⟨a, hfa, _hga⟩ :=
    (topologicalPushoutInl_eq_inr_iff f g hf x y).mp hxy.symm
  exact hx ⟨a, hfa⟩

/-- The two off-seam images cover exactly the complement of the attaching image. -/
theorem union_topologicalPushoutOffSeam
    (hf : Injective f) (hg : Injective g) :
    topologicalPushoutInlOffSeam f g ∪
        topologicalPushoutInrOffSeam f g =
      (topologicalPushoutSeam f g)ᶜ := by
  ext z
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩) hseam
    · obtain ⟨a, ha⟩ := hseam
      have hxf : x = f a :=
        (topologicalPushoutInl_injective f g hg) ha.symm
      exact hx ⟨a, hxf.symm⟩
    · obtain ⟨a, ha⟩ := hseam
      obtain ⟨b, _hfb, hgb⟩ :=
        (topologicalPushoutInl_eq_inr_iff f g hf (f a) y).mp ha
      exact hy ⟨b, hgb⟩
  · intro hz
    rcases topologicalPushout_jointly_surjective f g z with
      ⟨x, rfl⟩ | ⟨y, rfl⟩
    · by_cases hx : x ∈ range f
      · obtain ⟨a, rfl⟩ := hx
        exact False.elim (hz ⟨a, rfl⟩)
      · exact Or.inl ⟨x, hx, rfl⟩
    · by_cases hy : y ∈ range g
      · obtain ⟨a, rfl⟩ := hy
        exact False.elim
          (hz ⟨a, topologicalPushout_condition f g a⟩)
      · exact Or.inr ⟨y, hy, rfl⟩

/-- Inside the seam complement, the left off-seam image is clopen. -/
theorem isClopen_topologicalPushoutInlOffSeam_restrict
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    IsClopen (((topologicalPushoutSeam f g)ᶜ) ↓∩
      topologicalPushoutInlOffSeam f g) := by
  have hleft := isOpen_topologicalPushoutInlOffSeam f g hf hg
  have hright := isOpen_topologicalPushoutInrOffSeam f g hf hg
  constructor
  · rw [← isOpen_compl_iff]
    have heq : ((((topologicalPushoutSeam f g)ᶜ) ↓∩
        topologicalPushoutInlOffSeam f g) :
          Set (↥(topologicalPushoutSeam f g)ᶜ))ᶜ =
        (((topologicalPushoutSeam f g)ᶜ) ↓∩
          topologicalPushoutInrOffSeam f g) := by
      ext z
      have hzcover := congrArg
        (fun s : Set (TopologicalPushout f g) ↦ z.1 ∈ s)
        (union_topologicalPushoutOffSeam f g hf.injective hg.injective)
      have hzdisjoint := Set.disjoint_left.1
        (disjoint_topologicalPushoutOffSeam f g hf.injective)
      simp only [Set.mem_compl_iff, Set.mem_preimage] at hzcover ⊢
      constructor
      · intro hznot
        rcases hzcover.mpr z.2 with hzleft | hzright
        · exact False.elim (hznot hzleft)
        · exact hzright
      · intro hzright hzleft
        exact hzdisjoint hzleft hzright
    rw [heq]
    exact hright.preimage continuous_subtype_val
  · exact hleft.preimage continuous_subtype_val

/-- Inside the seam complement, the right off-seam image is clopen. -/
theorem isClopen_topologicalPushoutInrOffSeam_restrict
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    IsClopen (((topologicalPushoutSeam f g)ᶜ) ↓∩
      topologicalPushoutInrOffSeam f g) := by
  have hleft := isOpen_topologicalPushoutInlOffSeam f g hf hg
  have hright := isOpen_topologicalPushoutInrOffSeam f g hf hg
  constructor
  · rw [← isOpen_compl_iff]
    have heq : ((((topologicalPushoutSeam f g)ᶜ) ↓∩
        topologicalPushoutInrOffSeam f g) :
          Set (↥(topologicalPushoutSeam f g)ᶜ))ᶜ =
        (((topologicalPushoutSeam f g)ᶜ) ↓∩
          topologicalPushoutInlOffSeam f g) := by
      ext z
      have hzcover := congrArg
        (fun s : Set (TopologicalPushout f g) ↦ z.1 ∈ s)
        (union_topologicalPushoutOffSeam f g hf.injective hg.injective)
      have hzdisjoint := Set.disjoint_left.1
        (disjoint_topologicalPushoutOffSeam f g hf.injective)
      simp only [Set.mem_compl_iff, Set.mem_preimage] at hzcover ⊢
      constructor
      · intro hznot
        rcases hzcover.mpr z.2 with hzleft | hzright
        · exact hzleft
        · exact False.elim (hznot hzright)
      · intro hzleft hzright
        exact hzdisjoint hzleft hzright
    rw [heq]
    exact hleft.preimage continuous_subtype_val
  · exact hright.preimage continuous_subtype_val

/-- Opposite off-seam witnesses lie in distinct connected components of the seam complement. -/
theorem connectedComponentIn_ne_of_mem_topologicalPushoutOffSeam
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (x y : TopologicalPushout f g)
    (hxSeam : x ∉ topologicalPushoutSeam f g)
    (hySeam : y ∉ topologicalPushoutSeam f g)
    (hx : x ∈ topologicalPushoutInlOffSeam f g)
    (hy : y ∈ topologicalPushoutInrOffSeam f g) :
    connectedComponentIn (topologicalPushoutSeam f g)ᶜ x ≠
      connectedComponentIn (topologicalPushoutSeam f g)ᶜ y := by
  let xs : ↥(topologicalPushoutSeam f g)ᶜ := ⟨x, hxSeam⟩
  let ys : ↥(topologicalPushoutSeam f g)ᶜ := ⟨y, hySeam⟩
  intro hxy
  have himage :
      ((fun z : ↥(topologicalPushoutSeam f g)ᶜ ↦ z.1) ''
          connectedComponent xs) =
        ((fun z : ↥(topologicalPushoutSeam f g)ᶜ ↦ z.1) ''
          connectedComponent ys) := by
    rw [← connectedComponentIn_eq_image xs.2,
      ← connectedComponentIn_eq_image ys.2]
    exact hxy
  have hcomponents : connectedComponent xs = connectedComponent ys :=
    (Set.image_injective.mpr Subtype.val_injective) himage
  have hx' : xs ∈ (((topologicalPushoutSeam f g)ᶜ) ↓∩
      topologicalPushoutInlOffSeam f g) := hx
  have hy' : ys ∈ (((topologicalPushoutSeam f g)ᶜ) ↓∩
      topologicalPushoutInrOffSeam f g) := hy
  have hycomp : ys ∈ connectedComponent xs := by
    rw [hcomponents]
    exact mem_connectedComponent
  have hyleft :=
    (isClopen_topologicalPushoutInlOffSeam_restrict f g hf hg)
      |>.connectedComponent_subset hx' hycomp
  exact Set.disjoint_left.1
    (disjoint_topologicalPushoutOffSeam f g hf.injective) hyleft hy'

end SplittingSpheres
