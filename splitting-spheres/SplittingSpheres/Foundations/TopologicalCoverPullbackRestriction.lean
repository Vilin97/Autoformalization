/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import SplittingSpheres.Foundations.TopologicalCoverPullback

/-!
# Restricting the base of a topological pullback

For maps `p : E → X`, `f : Y → X`, and `g : A → Y`, there is a canonical map from the
pullback of `p` along `f ∘ g` to the pullback along `f`.  It changes the base coordinate by `g`
and leaves the old-total-space coordinate unchanged.

Continuity and injectivity of this map require only the corresponding properties of `g`.  If
`g` is an embedding, the map is canonically homeomorphic onto the exact part of the larger
pullback lying over `Set.range g`.  The final specialization records this homeomorphism for a
literal subtype inclusion.  These statements are point-set topology only: no covering-map or
smoothness conclusion is asserted here.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

universe uE uX uY uA uB

variable {E : Type uE} {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
variable [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalSpace A] [TopologicalSpace B]

/-- Change the base coordinate of a pullback point by `g`, leaving its fiber coordinate fixed. -/
def topologicalCoverPullbackRestrictionMap (p : E → X) (f : Y → X) (g : A → Y) :
    TopologicalCoverPullback p (f ∘ g) → TopologicalCoverPullback p f :=
  fun z ↦ ⟨(g z.1.1, z.1.2), z.2⟩

omit [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] in
@[simp]
theorem topologicalCoverPullbackRestrictionMap_base
    (p : E → X) (f : Y → X) (g : A → Y)
    (z : TopologicalCoverPullback p (f ∘ g)) :
    (topologicalCoverPullbackRestrictionMap p f g z).1.1 = g z.1.1 :=
  rfl

omit [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] in
@[simp]
theorem topologicalCoverPullbackRestrictionMap_fiberCoordinate
    (p : E → X) (f : Y → X) (g : A → Y)
    (z : TopologicalCoverPullback p (f ∘ g)) :
    (topologicalCoverPullbackRestrictionMap p f g z).1.2 = z.1.2 :=
  rfl

omit [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] in
/-- The canonical restriction map lies over `g`. -/
@[simp]
theorem topologicalCoverPullbackRestrictionMap_proj
    (p : E → X) (f : Y → X) (g : A → Y)
    (z : TopologicalCoverPullback p (f ∘ g)) :
    topologicalCoverPullbackProj p f
        (topologicalCoverPullbackRestrictionMap p f g z) =
      g (topologicalCoverPullbackProj p (f ∘ g) z) :=
  rfl

omit [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] in
/-- Formula on a pullback point built from explicit coordinates. -/
@[simp]
theorem topologicalCoverPullbackRestrictionMap_mk
    (p : E → X) (f : Y → X) (g : A → Y)
    (a : A) (e : E) (h : (f ∘ g) a = p e) :
    topologicalCoverPullbackRestrictionMap p f g
        (topologicalCoverPullbackMk p (f ∘ g) a e h) =
      topologicalCoverPullbackMk p f (g a) e h :=
  rfl

omit [TopologicalSpace X] in
/-- A continuous base map induces a continuous map between the two pullbacks. -/
theorem continuous_topologicalCoverPullbackRestrictionMap
    (p : E → X) (f : Y → X) {g : A → Y} (hg : Continuous g) :
    Continuous (topologicalCoverPullbackRestrictionMap p f g) := by
  apply Continuous.subtype_mk
  exact (hg.comp (continuous_fst.comp continuous_subtype_val)).prodMk
    (continuous_snd.comp continuous_subtype_val)

omit [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] in
/-- An injective base map induces an injective map between the two pullbacks. -/
theorem injective_topologicalCoverPullbackRestrictionMap
    (p : E → X) (f : Y → X) {g : A → Y} (hg : Injective g) :
    Injective (topologicalCoverPullbackRestrictionMap p f g) := by
  intro z w hzw
  apply Subtype.ext
  apply Prod.ext
  · apply hg
    exact congrArg (fun q : TopologicalCoverPullback p f ↦ q.1.1) hzw
  · exact congrArg (fun q : TopologicalCoverPullback p f ↦ q.1.2) hzw

omit [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] in
/-- Restricting first along `g` and then along `h` agrees literally with restricting along their
composite.  This is the useful functoriality law for nested piece inclusions. -/
@[simp]
theorem topologicalCoverPullbackRestrictionMap_comp
    (p : E → X) (f : Y → X) (g : A → Y) (h : B → A)
    (z : TopologicalCoverPullback p (f ∘ (g ∘ h))) :
    topologicalCoverPullbackRestrictionMap p f (g ∘ h) z =
      topologicalCoverPullbackRestrictionMap p f g
        (topologicalCoverPullbackRestrictionMap p (f ∘ g) h z) :=
  rfl

omit [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] in
/-- Restriction along the identity does not change a pullback point. -/
@[simp]
theorem topologicalCoverPullbackRestrictionMap_id
    (p : E → X) (f : Y → X) (z : TopologicalCoverPullback p (f ∘ id)) :
    topologicalCoverPullbackRestrictionMap p f id z = z :=
  rfl

/-- The exact part of the larger pullback lying over the image of `g`. -/
def topologicalCoverPullbackRestrictionRange
    (p : E → X) (f : Y → X) (g : A → Y) :
    Set (TopologicalCoverPullback p f) :=
  topologicalCoverPullbackProj p f ⁻¹' Set.range g

omit [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] in
@[simp]
theorem mem_topologicalCoverPullbackRestrictionRange
    (p : E → X) (f : Y → X) (g : A → Y)
    (z : TopologicalCoverPullback p f) :
    z ∈ topologicalCoverPullbackRestrictionRange p f g ↔ z.1.1 ∈ Set.range g :=
  Iff.rfl

omit [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] in
/-- The image of the restriction map is exactly the part of the larger pullback lying over the
image of the base map.  No injectivity hypothesis is needed for this set equality. -/
theorem range_topologicalCoverPullbackRestrictionMap
    (p : E → X) (f : Y → X) (g : A → Y) :
    Set.range (topologicalCoverPullbackRestrictionMap p f g) =
      topologicalCoverPullbackRestrictionRange p f g := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.1.1, rfl⟩
  · rintro ⟨a, ha⟩
    refine ⟨⟨(a, z.1.2), ?_⟩, ?_⟩
    · change f (g a) = p z.1.2
      rw [ha]
      exact z.2
    · apply Subtype.ext
      apply Prod.ext
      · exact ha
      · rfl

/-- If the base map is an embedding, restriction is a homeomorphism onto the exact part of the
larger pullback lying over its range. -/
noncomputable def topologicalCoverPullbackRestrictionRangeHomeomorph
    (p : E → X) (f : Y → X) (g : A → Y) (hg : IsEmbedding g) :
    TopologicalCoverPullback p (f ∘ g) ≃ₜ
      topologicalCoverPullbackRestrictionRange p f g where
  toFun z := ⟨topologicalCoverPullbackRestrictionMap p f g z, ⟨z.1.1, rfl⟩⟩
  invFun z :=
    let a := hg.toHomeomorph.symm ⟨z.1.1.1, z.2⟩
    ⟨(a, z.1.1.2), by
      change f (g a) = p z.1.1.2
      have ha : g a = z.1.1.1 :=
        congrArg Subtype.val (hg.toHomeomorph.apply_symm_apply ⟨z.1.1.1, z.2⟩)
      rw [ha]
      exact z.1.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact hg.toHomeomorph_symm_apply z.1.1
    · rfl
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        (hg.toHomeomorph.apply_symm_apply ⟨z.1.1.1, z.2⟩)
    · rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_topologicalCoverPullbackRestrictionMap p f hg.continuous
  continuous_invFun := by
    have hbase : Continuous (fun z : topologicalCoverPullbackRestrictionRange p f g ↦
        (⟨z.1.1.1, z.2⟩ : Set.range g)) := by
      apply Continuous.subtype_mk
      exact continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hfiber : Continuous (fun z : topologicalCoverPullbackRestrictionRange p f g ↦
        z.1.1.2) :=
      continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)
    apply Continuous.subtype_mk
    exact (hg.toHomeomorph.symm.continuous.comp hbase).prodMk hfiber

omit [TopologicalSpace X] in
@[simp]
theorem topologicalCoverPullbackRestrictionRangeHomeomorph_apply_coe
    (p : E → X) (f : Y → X) (g : A → Y) (hg : IsEmbedding g)
    (z : TopologicalCoverPullback p (f ∘ g)) :
    ((topologicalCoverPullbackRestrictionRangeHomeomorph p f g hg z :
        topologicalCoverPullbackRestrictionRange p f g) :
      TopologicalCoverPullback p f) =
      topologicalCoverPullbackRestrictionMap p f g z :=
  rfl

omit [TopologicalSpace X] in
@[simp]
theorem topologicalCoverPullbackRestrictionRangeHomeomorph_proj
    (p : E → X) (f : Y → X) (g : A → Y) (hg : IsEmbedding g)
    (z : TopologicalCoverPullback p (f ∘ g)) :
    topologicalCoverPullbackProj p f
        (topologicalCoverPullbackRestrictionRangeHomeomorph p f g hg z).1 =
      g (topologicalCoverPullbackProj p (f ∘ g) z) :=
  rfl

omit [TopologicalSpace X] in
@[simp]
theorem topologicalCoverPullbackRestrictionRangeHomeomorph_symm_proj
    (p : E → X) (f : Y → X) (g : A → Y) (hg : IsEmbedding g)
    (z : topologicalCoverPullbackRestrictionRange p f g) :
    topologicalCoverPullbackProj p (f ∘ g)
        ((topologicalCoverPullbackRestrictionRangeHomeomorph p f g hg).symm z) =
      hg.toHomeomorph.symm
        ⟨topologicalCoverPullbackProj p f z.1, z.2⟩ :=
  rfl

omit [TopologicalSpace X] in
@[simp]
theorem topologicalCoverPullbackRestrictionRangeHomeomorph_symm_fiberCoordinate
    (p : E → X) (f : Y → X) (g : A → Y) (hg : IsEmbedding g)
    (z : topologicalCoverPullbackRestrictionRange p f g) :
    ((topologicalCoverPullbackRestrictionRangeHomeomorph p f g hg).symm z).1.2 =
      z.1.1.2 :=
  rfl

omit [TopologicalSpace X] in
/-- An embedded base restriction induces an embedding of pullback total spaces. -/
theorem isEmbedding_topologicalCoverPullbackRestrictionMap
    (p : E → X) (f : Y → X) {g : A → Y} (hg : IsEmbedding g) :
    IsEmbedding (topologicalCoverPullbackRestrictionMap p f g) := by
  have h := IsEmbedding.subtypeVal.comp
    (topologicalCoverPullbackRestrictionRangeHomeomorph p f g hg).isEmbedding
  change IsEmbedding (topologicalCoverPullbackRestrictionMap p f g) at h
  exact h

/-- For a literal subset `s ⊆ Y`, restriction is homeomorphic to the exact inverse image of
`s` under the larger pullback projection.  This is the form intended for piece inclusions. -/
noncomputable def topologicalCoverPullbackSubtypeRestrictionHomeomorph
    (p : E → X) (f : Y → X) (s : Set Y) :
    TopologicalCoverPullback p (f ∘ ((↑) : s → Y)) ≃ₜ
      (topologicalCoverPullbackProj p f ⁻¹' s) :=
  (topologicalCoverPullbackRestrictionRangeHomeomorph p f ((↑) : s → Y)
      IsEmbedding.subtypeVal).trans
    (Homeomorph.setCongr (by
      ext z
      simp [topologicalCoverPullbackRestrictionRange]))

omit [TopologicalSpace X] in
@[simp]
theorem topologicalCoverPullbackSubtypeRestrictionHomeomorph_apply_coe
    (p : E → X) (f : Y → X) (s : Set Y)
    (z : TopologicalCoverPullback p (f ∘ ((↑) : s → Y))) :
    ((topologicalCoverPullbackSubtypeRestrictionHomeomorph p f s z :
        (topologicalCoverPullbackProj p f ⁻¹' s)) :
      TopologicalCoverPullback p f) =
      topologicalCoverPullbackRestrictionMap p f ((↑) : s → Y) z :=
  rfl

omit [TopologicalSpace X] in
@[simp]
theorem topologicalCoverPullbackSubtypeRestrictionHomeomorph_proj
    (p : E → X) (f : Y → X) (s : Set Y)
    (z : TopologicalCoverPullback p (f ∘ ((↑) : s → Y))) :
    topologicalCoverPullbackProj p f
        (topologicalCoverPullbackSubtypeRestrictionHomeomorph p f s z).1 =
      (z.1.1 : Y) :=
  rfl

end SplittingSpheres
