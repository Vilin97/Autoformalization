module

public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Connected.PathConnected

/-!
# Concrete topological pushouts

This file packages the ordinary pushout in `TopCat` in a form convenient for attaching compact
manifold pieces along a common boundary.  It proves only topological facts.  In particular, it
does not put a smooth structure on the pushout or assert that a boundary attachment is a smooth
manifold gluing.

For continuous maps `f : A → X` and `g : A → Y`, `TopologicalPushout f g` is the colimit
of `X ← A → Y` in topological spaces.  The forgetful functor from `TopCat` preserves this
colimit, which lets us transport the precise set-level description of a pushout of types.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Function Set Topology

universe u

namespace SplittingSpheres

variable {A X Y Z : Type u}
variable [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]

/-- The topological adjunction space obtained from `X ← A → Y`. -/
abbrev TopologicalPushout (f : C(A, X)) (g : C(A, Y)) : TopCat.{u} :=
  pushout (TopCat.ofHom f) (TopCat.ofHom g)

/-- The left coprojection into a topological pushout. -/
abbrev topologicalPushoutInl (f : C(A, X)) (g : C(A, Y)) :
    C(X, TopologicalPushout f g) :=
  (pushout.inl (TopCat.ofHom f) (TopCat.ofHom g)).hom

/-- The right coprojection into a topological pushout. -/
abbrev topologicalPushoutInr (f : C(A, X)) (g : C(A, Y)) :
    C(Y, TopologicalPushout f g) :=
  (pushout.inr (TopCat.ofHom f) (TopCat.ofHom g)).hom

theorem topologicalPushout_condition (f : C(A, X)) (g : C(A, Y)) (a : A) :
    topologicalPushoutInl f g (f a) = topologicalPushoutInr f g (g a) := by
  exact ConcreteCategory.congr_hom
    (pushout.condition (f := TopCat.ofHom f) (g := TopCat.ofHom g)) a

variable [TopologicalSpace Z]

theorem topologicalPushout_desc_condition (f : C(A, X)) (g : C(A, Y))
    (p : C(X, Z)) (q : C(Y, Z)) (h : ∀ a, p (f a) = q (g a)) :
    TopCat.ofHom f ≫ TopCat.ofHom p = TopCat.ofHom g ≫ TopCat.ofHom q := by
  ext a
  exact h a

/-- Descend compatible continuous maps from the two pieces to the pushout. -/
def topologicalPushoutDesc (f : C(A, X)) (g : C(A, Y))
    (p : C(X, Z)) (q : C(Y, Z)) (h : ∀ a, p (f a) = q (g a)) :
    C(TopologicalPushout f g, Z) :=
  (pushout.desc (TopCat.ofHom p) (TopCat.ofHom q)
    (topologicalPushout_desc_condition f g p q h)).hom

@[simp]
theorem topologicalPushoutDesc_inl (f : C(A, X)) (g : C(A, Y))
    (p : C(X, Z)) (q : C(Y, Z)) (h : ∀ a, p (f a) = q (g a)) (x : X) :
    topologicalPushoutDesc f g p q h (topologicalPushoutInl f g x) = p x := by
  exact ConcreteCategory.congr_hom
    (pushout.inl_desc (TopCat.ofHom p) (TopCat.ofHom q)
      (topologicalPushout_desc_condition f g p q h)) x

@[simp]
theorem topologicalPushoutDesc_inr (f : C(A, X)) (g : C(A, Y))
    (p : C(X, Z)) (q : C(Y, Z)) (h : ∀ a, p (f a) = q (g a)) (y : Y) :
    topologicalPushoutDesc f g p q h (topologicalPushoutInr f g y) = q y := by
  exact ConcreteCategory.congr_hom
    (pushout.inr_desc (TopCat.ofHom p) (TopCat.ofHom q)
      (topologicalPushout_desc_condition f g p q h)) y

/-- Continuous maps out of a topological pushout are determined on its two pieces. -/
theorem topologicalPushout_hom_ext (f : C(A, X)) (g : C(A, Y))
    {p q : C(TopologicalPushout f g, Z)}
    (hX : ∀ x, p (topologicalPushoutInl f g x) = q (topologicalPushoutInl f g x))
    (hY : ∀ y, p (topologicalPushoutInr f g y) = q (topologicalPushoutInr f g y)) :
    p = q := by
  have hX' : pushout.inl (TopCat.ofHom f) (TopCat.ofHom g) ≫ TopCat.ofHom p =
      pushout.inl (TopCat.ofHom f) (TopCat.ofHom g) ≫ TopCat.ofHom q := by
    ext x
    exact hX x
  have hY' : pushout.inr (TopCat.ofHom f) (TopCat.ofHom g) ≫ TopCat.ofHom p =
      pushout.inr (TopCat.ofHom f) (TopCat.ofHom g) ≫ TopCat.ofHom q := by
    ext y
    exact hY y
  have hpq : TopCat.ofHom p = TopCat.ofHom q := pushout.hom_ext hX' hY'
  ext z
  exact ConcreteCategory.congr_hom hpq z

section UnderlyingType

variable (f : C(A, X)) (g : C(A, Y))

/-- The underlying square of a topological pushout is a pushout square of types. -/
theorem topologicalPushout_isPushout :
    @IsPushout (Type u) CategoryTheory.types A X Y (TopologicalPushout f g)
      (↾(⇑f)) (↾(⇑g)) (↾(⇑(topologicalPushoutInl f g)))
      (↾(⇑(topologicalPushoutInr f g))) := by
  simpa only [TopCat.coe_of] using
    (IsPushout.of_hasPushout (TopCat.ofHom f) (TopCat.ofHom g)).map (forget TopCat)

/-- Every point of a topological pushout comes from one of its two pieces. -/
theorem topologicalPushout_jointly_surjective (z : TopologicalPushout f g) :
    (∃ x, topologicalPushoutInl f g x = z) ∨
      ∃ y, topologicalPushoutInr f g y = z :=
  Types.eq_or_eq_of_isPushout (topologicalPushout_isPushout f g) z

theorem range_topologicalPushoutInl_union_range_topologicalPushoutInr :
    range (topologicalPushoutInl f g) ∪ range (topologicalPushoutInr f g) = univ := by
  ext z
  constructor
  · exact fun _ ↦ mem_univ z
  · intro _
    rcases topologicalPushout_jointly_surjective f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨x, rfl⟩
    · exact Or.inr ⟨y, rfl⟩

/-- If the right attaching map is injective, the left piece embeds set-theoretically. -/
theorem topologicalPushoutInl_injective (hg : Injective g) :
    Injective (topologicalPushoutInl f g) := by
  exact Types.pushoutCocone_inr_injective_of_isColimit
    (PushoutCocone.flipIsColimit (topologicalPushout_isPushout f g).isColimit) hg

/-- If the left attaching map is injective, the right piece embeds set-theoretically. -/
theorem topologicalPushoutInr_injective (hf : Injective f) :
    Injective (topologicalPushoutInr f g) :=
  Types.pushoutCocone_inr_injective_of_isColimit
    (topologicalPushout_isPushout f g).isColimit hf

/-- A point of the left piece and a point of the right piece agree exactly when they are the
images of a common attaching point. -/
theorem topologicalPushoutInl_eq_inr_iff (hf : Injective f) (x : X) (y : Y) :
    topologicalPushoutInl f g x = topologicalPushoutInr f g y ↔
      ∃ a, f a = x ∧ g a = y :=
  Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
    (topologicalPushout_isPushout f g).isColimit hf x y

/-- For injective attaching maps, the two pieces intersect in precisely the glued copy of the
attaching space. -/
theorem range_topologicalPushoutInl_inter_range_topologicalPushoutInr
    (hf : Injective f) :
    range (topologicalPushoutInl f g) ∩ range (topologicalPushoutInr f g) =
      range (fun a ↦ topologicalPushoutInl f g (f a)) := by
  ext z
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hxy : topologicalPushoutInl f g x = topologicalPushoutInr f g y :=
      hx.trans hy.symm
    obtain ⟨a, ha, _⟩ := (topologicalPushoutInl_eq_inr_iff f g hf x y).mp hxy
    exact ⟨a, congr_arg (topologicalPushoutInl f g) ha |>.trans hx⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨f a, rfl⟩, ⟨g a, (topologicalPushout_condition f g a).symm⟩⟩

end UnderlyingType

section Compact

variable (f : C(A, X)) (g : C(A, Y))
variable [CompactSpace X] [CompactSpace Y]

theorem isCompact_univ_topologicalPushout :
    IsCompact (univ : Set (TopologicalPushout f g)) := by
  rw [← range_topologicalPushoutInl_union_range_topologicalPushoutInr f g]
  simpa only [image_univ] using
    (isCompact_univ.image (topologicalPushoutInl f g).continuous).union
      (isCompact_univ.image (topologicalPushoutInr f g).continuous)

/-- A pushout of two compact spaces is compact. -/
instance topologicalPushoutCompactSpace : CompactSpace (TopologicalPushout f g) :=
  ⟨isCompact_univ_topologicalPushout f g⟩

end Compact

section PathConnected

variable (f : C(A, X)) (g : C(A, Y))
variable [PathConnectedSpace X] [PathConnectedSpace Y] [Nonempty A]

theorem isPathConnected_univ_topologicalPushout :
    IsPathConnected (univ : Set (TopologicalPushout f g)) := by
  rw [← range_topologicalPushoutInl_union_range_topologicalPushoutInr f g]
  apply (isPathConnected_range (topologicalPushoutInl f g).continuous).union
    (isPathConnected_range (topologicalPushoutInr f g).continuous)
  obtain ⟨a⟩ := (inferInstance : Nonempty A)
  exact ⟨topologicalPushoutInl f g (f a), ⟨⟨f a, rfl⟩,
    ⟨g a, (topologicalPushout_condition f g a).symm⟩⟩⟩

/-- Gluing two path-connected spaces along a nonempty space is path-connected. -/
instance topologicalPushoutPathConnectedSpace :
    PathConnectedSpace (TopologicalPushout f g) :=
  pathConnectedSpace_iff_univ.mpr (isPathConnected_univ_topologicalPushout f g)

end PathConnected

end SplittingSpheres
