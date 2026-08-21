/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import SplittingSpheres.Foundations.TopologicalPushoutSeparation

/-!
# Collared topological pushouts

This file gives the reusable point-set and atlas layer for gluing two charted spaces along a
common closed-embedded locus.  A signed parametrization supplies a literal piecewise map into the
topological pushout.  Exact boundary detection and openness of its two half-images make that map
an open embedding once its inducing property has been proved.  The two off-seam coprojections and
the seam embedding then give a concrete atlas on the pushout.

The final manifold theorem is conditional on compatibility of those explicit atlas charts.  In
particular, this file does not construct collars, a cut space, a cap, or the mixed smooth
transition maps required by an application.  It also does not transport a charted-space structure
through an unrelated homeomorphism.
-/

@[expose] public section

noncomputable section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

universe u

namespace SplittingSpheres

variable {A X Y H : Type u}
variable [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalSpace H]

section OffSeam

variable (f : C(A, X)) (g : C(A, Y))

/-- The part of the left piece away from its attaching range. -/
abbrev TopologicalPushoutInlOffSeamDomain := ↑(range f)ᶜ

/-- The part of the right piece away from its attaching range. -/
abbrev TopologicalPushoutInrOffSeamDomain := ↑(range g)ᶜ

/-- Restrict the left coprojection to the complement of the attaching range. -/
def topologicalPushoutInlOffSeamMap :
    TopologicalPushoutInlOffSeamDomain f → TopologicalPushout f g :=
  fun x ↦ topologicalPushoutInl f g x.1

/-- Restrict the right coprojection to the complement of the attaching range. -/
def topologicalPushoutInrOffSeamMap :
    TopologicalPushoutInrOffSeamDomain g → TopologicalPushout f g :=
  fun y ↦ topologicalPushoutInr f g y.1

theorem range_topologicalPushoutInlOffSeamMap :
    range (topologicalPushoutInlOffSeamMap f g) =
      topologicalPushoutInlOffSeam f g := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem range_topologicalPushoutInrOffSeamMap :
    range (topologicalPushoutInrOffSeamMap f g) =
      topologicalPushoutInrOffSeam f g := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, y.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

/-- The left coprojection is an open embedding away from the seam. -/
theorem isOpenEmbedding_topologicalPushoutInlOffSeamMap
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    IsOpenEmbedding (topologicalPushoutInlOffSeamMap f g) := by
  refine ⟨(isEmbedding_topologicalPushoutInl f g hg).comp
      IsEmbedding.subtypeVal, ?_⟩
  rw [range_topologicalPushoutInlOffSeamMap]
  exact isOpen_topologicalPushoutInlOffSeam f g hf hg

/-- The right coprojection is an open embedding away from the seam. -/
theorem isOpenEmbedding_topologicalPushoutInrOffSeamMap
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    IsOpenEmbedding (topologicalPushoutInrOffSeamMap f g) := by
  refine ⟨(isEmbedding_topologicalPushoutInr f g hf).comp
      IsEmbedding.subtypeVal, ?_⟩
  rw [range_topologicalPushoutInrOffSeamMap]
  exact isOpen_topologicalPushoutInrOffSeam f g hf hg

end OffSeam

section Seam

variable {N : Type u}
variable (f : C(A, X)) (g : C(A, Y))
variable (tau : N → ℝ) (left : N → X) (right : N → Y)

/-- Glue two signed collar halves through the literal topological pushout.  The zero level is
taken from the left; compatibility at zero makes this convention immaterial. -/
def topologicalPushoutSeamMap (p : N) : TopologicalPushout f g :=
  if tau p ≤ 0 then
    topologicalPushoutInl f g (left p)
  else
    topologicalPushoutInr f g (right p)

/-- The piecewise seam map is continuous when the two collar maps agree in the pushout at the
zero level. -/
theorem continuous_topologicalPushoutSeamMap
    [TopologicalSpace N]
    (htau : Continuous tau) (hleft : Continuous left)
    (hright : Continuous right)
    (hzero : ∀ p, tau p = 0 →
      topologicalPushoutInl f g (left p) =
        topologicalPushoutInr f g (right p)) :
    Continuous (topologicalPushoutSeamMap f g tau left right) := by
  unfold topologicalPushoutSeamMap
  apply Continuous.if_le
  · exact (topologicalPushoutInl f g).continuous.comp hleft
  · exact (topologicalPushoutInr f g).continuous.comp hright
  · exact htau
  · exact continuous_const
  · intro p hp
    exact hzero p hp

/-- Halfwise injectivity and exact detection of the right attaching range make the piecewise seam
map injective.  Only right boundary detection is needed because the zero level is assigned to the
left branch. -/
theorem injective_topologicalPushoutSeamMap
    (hf : Injective f) (hg : Injective g)
    (hleft : ∀ p q, tau p ≤ 0 → tau q ≤ 0 →
      left p = left q → p = q)
    (hright : ∀ p q, 0 < tau p → 0 < tau q →
      right p = right q → p = q)
    (hrightBoundary : ∀ p, right p ∈ range g → tau p = 0) :
    Injective (topologicalPushoutSeamMap f g tau left right) := by
  intro p q hpq
  by_cases hp : tau p ≤ 0 <;> by_cases hq : tau q ≤ 0
  · simp only [topologicalPushoutSeamMap, hp, hq, ↓reduceIte] at hpq
    apply hleft p q hp hq
    exact topologicalPushoutInl_injective f g hg hpq
  · simp only [topologicalPushoutSeamMap, hp, hq, ↓reduceIte] at hpq
    have hqpos : 0 < tau q := lt_of_not_ge hq
    obtain ⟨a, _ha, hga⟩ :=
      (topologicalPushoutInl_eq_inr_iff f g hf (left p) (right q)).mp hpq
    exact False.elim ((ne_of_gt hqpos) (hrightBoundary q ⟨a, hga⟩))
  · simp only [topologicalPushoutSeamMap, hp, hq, ↓reduceIte] at hpq
    have hppos : 0 < tau p := lt_of_not_ge hp
    obtain ⟨a, _hfa, hga⟩ :=
      (topologicalPushoutInl_eq_inr_iff f g hf (left q) (right p)).mp hpq.symm
    exact False.elim ((ne_of_gt hppos) (hrightBoundary p ⟨a, hga⟩))
  · simp only [topologicalPushoutSeamMap, hp, hq, ↓reduceIte] at hpq
    apply hright p q (lt_of_not_ge hp) (lt_of_not_ge hq)
    exact topologicalPushoutInr_injective f g hf hpq

/-- The left-piece preimage of the seam range is exactly the nonpositive collar half. -/
theorem preimage_topologicalPushoutInl_range_seamMap
    (hf : Injective f) (hg : Injective g)
    (hrightBoundary : ∀ p, right p ∈ range g → tau p = 0) :
    (topologicalPushoutInl f g) ⁻¹'
        range (topologicalPushoutSeamMap f g tau left right) =
      left '' {p | tau p ≤ 0} := by
  ext x
  constructor
  · rintro ⟨p, hp⟩
    unfold topologicalPushoutSeamMap at hp
    split_ifs at hp with hpt
    · exact ⟨p, hpt, topologicalPushoutInl_injective f g hg hp⟩
    · have hptpos : 0 < tau p := lt_of_not_ge hpt
      obtain ⟨a, _hfa, hga⟩ :=
        (topologicalPushoutInl_eq_inr_iff f g hf x (right p)).mp hp.symm
      exact False.elim ((ne_of_gt hptpos) (hrightBoundary p ⟨a, hga⟩))
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p, ?_⟩
    have hpt : tau p ≤ 0 := hp
    simp only [topologicalPushoutSeamMap, hpt, ↓reduceIte]

/-- The right-piece preimage of the seam range is exactly the nonnegative collar half. -/
theorem preimage_topologicalPushoutInr_range_seamMap
    (hf : Injective f)
    (hzero : ∀ p, tau p = 0 → ∃ a, f a = left p ∧ g a = right p)
    (hleftBoundary : ∀ p, left p ∈ range f → tau p = 0) :
    (topologicalPushoutInr f g) ⁻¹'
        range (topologicalPushoutSeamMap f g tau left right) =
      right '' {p | 0 ≤ tau p} := by
  ext y
  constructor
  · rintro ⟨p, hp⟩
    unfold topologicalPushoutSeamMap at hp
    split_ifs at hp with hpt
    · obtain ⟨a, hfa, hga⟩ :=
        (topologicalPushoutInl_eq_inr_iff f g hf (left p) y).mp hp
      have hptzero : tau p = 0 := hleftBoundary p ⟨a, hfa⟩
      obtain ⟨b, hfb, hgb⟩ := hzero p hptzero
      have hab : a = b := hf (hfa.trans hfb.symm)
      exact ⟨p, hptzero.ge, by rw [← hga, ← hgb, hab]⟩
    · exact ⟨p, (lt_of_not_ge hpt).le,
        topologicalPushoutInr_injective f g hf hp⟩
  · rintro ⟨p, hp, rfl⟩
    have hp' : 0 ≤ tau p := hp
    rcases hp'.eq_or_lt with hzeroTau | hpos
    · obtain ⟨a, hfa, hga⟩ := hzero p hzeroTau.symm
      refine ⟨p, ?_⟩
      simp only [topologicalPushoutSeamMap, hzeroTau, le_refl, ↓reduceIte]
      rw [← hfa, ← hga]
      exact topologicalPushout_condition f g a
    · refine ⟨p, ?_⟩
      simp only [topologicalPushoutSeamMap, not_le_of_gt hpos, ↓reduceIte]

/-- Exact boundary detection and open one-sided collar images make the piecewise seam range open
in the final topology of the pushout. -/
theorem isOpen_range_topologicalPushoutSeamMap
    (hf : Injective f) (hg : Injective g)
    (hzero : ∀ p, tau p = 0 → ∃ a, f a = left p ∧ g a = right p)
    (hleftBoundary : ∀ p, left p ∈ range f → tau p = 0)
    (hrightBoundary : ∀ p, right p ∈ range g → tau p = 0)
    (hleftOpen : IsOpen (left '' {p | tau p ≤ 0}))
    (hrightOpen : IsOpen (right '' {p | 0 ≤ tau p})) :
    IsOpen (range (topologicalPushoutSeamMap f g tau left right)) := by
  rw [isOpen_topologicalPushout_iff]
  rw [preimage_topologicalPushoutInl_range_seamMap f g tau left right
      hf hg hrightBoundary,
    preimage_topologicalPushoutInr_range_seamMap f g tau left right
      hf hzero hleftBoundary]
  exact ⟨hleftOpen, hrightOpen⟩

/-- Package the point-set seam construction as an open embedding.  The separate embedding
hypothesis is the collar's inducing assertion; the preceding lemmas supply continuity,
injectivity, and openness without hiding it. -/
theorem isOpenEmbedding_topologicalPushoutSeamMap
    [TopologicalSpace N]
    (hf : Injective f) (hg : Injective g)
    (hzero : ∀ p, tau p = 0 → ∃ a, f a = left p ∧ g a = right p)
    (hleftBoundary : ∀ p, left p ∈ range f → tau p = 0)
    (hrightBoundary : ∀ p, right p ∈ range g → tau p = 0)
    (hleftOpen : IsOpen (left '' {p | tau p ≤ 0}))
    (hrightOpen : IsOpen (right '' {p | 0 ≤ tau p}))
    (hemb : IsEmbedding (topologicalPushoutSeamMap f g tau left right)) :
    IsOpenEmbedding (topologicalPushoutSeamMap f g tau left right) :=
  ⟨hemb, isOpen_range_topologicalPushoutSeamMap f g tau left right hf hg
    hzero hleftBoundary hrightBoundary hleftOpen hrightOpen⟩

end Seam

section Atlas

variable {N : Type u} [TopologicalSpace N]
variable [Nonempty H] [ChartedSpace H X] [ChartedSpace H Y] [ChartedSpace H N]
variable (f : C(A, X)) (g : C(A, Y))

def topologicalPushoutInlOffSeamOpens
    (hf : IsClosedEmbedding f) : Opens X :=
  ⟨(range f)ᶜ, hf.isClosed_range.isOpen_compl⟩

def topologicalPushoutInrOffSeamOpens
    (hg : IsClosedEmbedding g) : Opens Y :=
  ⟨(range g)ᶜ, hg.isClosed_range.isOpen_compl⟩

def topologicalPushoutInlOffSeamMap'
    (hf : IsClosedEmbedding f) :
    ↑(topologicalPushoutInlOffSeamOpens f hf) → TopologicalPushout f g :=
  fun x ↦ topologicalPushoutInl f g x.1

def topologicalPushoutInrOffSeamMap'
    (hg : IsClosedEmbedding g) :
    ↑(topologicalPushoutInrOffSeamOpens g hg) → TopologicalPushout f g :=
  fun y ↦ topologicalPushoutInr f g y.1

theorem isOpenEmbedding_topologicalPushoutInlOffSeamMap'
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    IsOpenEmbedding (topologicalPushoutInlOffSeamMap' f g hf) := by
  refine ⟨(isEmbedding_topologicalPushoutInl f g hg).comp
      IsEmbedding.subtypeVal, ?_⟩
  have hrange : range (topologicalPushoutInlOffSeamMap' f g hf) =
      topologicalPushoutInlOffSeam f g := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange]
  exact isOpen_topologicalPushoutInlOffSeam f g hf hg

theorem isOpenEmbedding_topologicalPushoutInrOffSeamMap'
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    IsOpenEmbedding (topologicalPushoutInrOffSeamMap' f g hg) := by
  refine ⟨(isEmbedding_topologicalPushoutInr f g hf).comp
      IsEmbedding.subtypeVal, ?_⟩
  have hrange : range (topologicalPushoutInrOffSeamMap' f g hg) =
      topologicalPushoutInrOffSeam f g := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [hrange]
  exact isOpen_topologicalPushoutInrOffSeam f g hf hg

/-- The three kinds of charts in the collared pushout atlas. -/
inductive TopologicalPushoutAtlasIndex
    (f : C(A, X)) (g : C(A, Y)) (N : Type u) where
  | inl : TopologicalPushoutInlOffSeamDomain f →
      TopologicalPushoutAtlasIndex f g N
  | inr : TopologicalPushoutInrOffSeamDomain g →
      TopologicalPushoutAtlasIndex f g N
  | seam : N → TopologicalPushoutAtlasIndex f g N

/-- A native left chart restricted away from the attaching range and lifted into the pushout. -/
def topologicalPushoutInlOffSeamChart
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (x : TopologicalPushoutInlOffSeamDomain f) :
    OpenPartialHomeomorph (TopologicalPushout f g) H :=
  let x' : ↑(topologicalPushoutInlOffSeamOpens f hf) := ⟨x.1, x.2⟩
  ((chartAt H x.1).subtypeRestr
      (s := topologicalPushoutInlOffSeamOpens f hf) ⟨x'⟩).lift_openEmbedding
    (isOpenEmbedding_topologicalPushoutInlOffSeamMap' f g hf hg)

/-- A native right chart restricted away from the attaching range and lifted into the pushout. -/
def topologicalPushoutInrOffSeamChart
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (y : TopologicalPushoutInrOffSeamDomain g) :
    OpenPartialHomeomorph (TopologicalPushout f g) H :=
  let y' : ↑(topologicalPushoutInrOffSeamOpens g hg) := ⟨y.1, y.2⟩
  ((chartAt H y.1).subtypeRestr
      (s := topologicalPushoutInrOffSeamOpens g hg) ⟨y'⟩).lift_openEmbedding
    (isOpenEmbedding_topologicalPushoutInrOffSeamMap' f g hf hg)

/-- A chart on the signed seam domain lifted along the seam open embedding. -/
def topologicalPushoutSeamChart
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    (q : N) : OpenPartialHomeomorph (TopologicalPushout f g) H :=
  (chartAt H q).lift_openEmbedding hseam

/-- The concrete chart represented by an index of the collared pushout atlas. -/
def topologicalPushoutAtlasChart
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam) :
    TopologicalPushoutAtlasIndex f g N →
      OpenPartialHomeomorph (TopologicalPushout f g) H
  | .inl x => topologicalPushoutInlOffSeamChart f g hf hg x
  | .inr y => topologicalPushoutInrOffSeamChart f g hf hg y
  | .seam q => topologicalPushoutSeamChart f g seam hseam q

omit [ChartedSpace H Y] in
theorem mem_topologicalPushoutInlOffSeamChart_source
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (x : TopologicalPushoutInlOffSeamDomain f) :
    topologicalPushoutInlOffSeamMap f g x ∈
      (topologicalPushoutInlOffSeamChart (H := H) f g hf hg x).source := by
  rw [topologicalPushoutInlOffSeamChart,
    OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.subtypeRestr_source]
  exact ⟨⟨x.1, x.2⟩, mem_chart_source H x.1, rfl⟩

omit [ChartedSpace H X] in
theorem mem_topologicalPushoutInrOffSeamChart_source
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (y : TopologicalPushoutInrOffSeamDomain g) :
    topologicalPushoutInrOffSeamMap f g y ∈
      (topologicalPushoutInrOffSeamChart (H := H) f g hf hg y).source := by
  rw [topologicalPushoutInrOffSeamChart,
    OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.subtypeRestr_source]
  exact ⟨⟨y.1, y.2⟩, mem_chart_source H y.1, rfl⟩

omit [ChartedSpace H X] [ChartedSpace H Y] in
theorem mem_topologicalPushoutSeamChart_source
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    (q : N) :
    seam q ∈ (topologicalPushoutSeamChart (H := H) f g seam hseam q).source := by
  rw [topologicalPushoutSeamChart,
    OpenPartialHomeomorph.lift_openEmbedding_source]
  exact ⟨q, mem_chart_source H q, rfl⟩

/-- The two off-seam chart families and the seam family cover the pushout. -/
theorem topologicalPushoutAtlasChart_covers
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    (hzero : ∀ a, ∃ q, seam q = topologicalPushoutInl f g (f a))
    (z : TopologicalPushout f g) :
    ∃ i : TopologicalPushoutAtlasIndex f g N,
      z ∈ (topologicalPushoutAtlasChart (H := H) f g hf hg seam hseam i).source := by
  rcases topologicalPushout_jointly_surjective f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · by_cases hx : x ∈ range f
    · obtain ⟨a, rfl⟩ := hx
      obtain ⟨q, hq⟩ := hzero a
      refine ⟨TopologicalPushoutAtlasIndex.seam q, ?_⟩
      rw [← hq]
      exact mem_topologicalPushoutSeamChart_source (H := H) f g seam hseam q
    · let x' : TopologicalPushoutInlOffSeamDomain f := ⟨x, hx⟩
      refine ⟨TopologicalPushoutAtlasIndex.inl x', ?_⟩
      exact mem_topologicalPushoutInlOffSeamChart_source (H := H) f g hf hg x'
  · by_cases hy : y ∈ range g
    · obtain ⟨a, rfl⟩ := hy
      obtain ⟨q, hq⟩ := hzero a
      refine ⟨TopologicalPushoutAtlasIndex.seam q, ?_⟩
      rw [← topologicalPushout_condition f g a, ← hq]
      exact mem_topologicalPushoutSeamChart_source (H := H) f g seam hseam q
    · let y' : TopologicalPushoutInrOffSeamDomain g := ⟨y, hy⟩
      refine ⟨TopologicalPushoutAtlasIndex.inr y', ?_⟩
      exact mem_topologicalPushoutInrOffSeamChart_source (H := H) f g hf hg y'

noncomputable def topologicalPushoutPreferredChart
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    (hzero : ∀ a, ∃ q, seam q = topologicalPushoutInl f g (f a))
    (z : TopologicalPushout f g) :
    OpenPartialHomeomorph (TopologicalPushout f g) H :=
  topologicalPushoutAtlasChart (H := H) f g hf hg seam hseam
    (topologicalPushoutAtlasChart_covers (H := H)
      f g hf hg seam hseam hzero z).choose

/-- The charted-space structure generated directly by native off-seam charts and seam charts. -/
@[instance_reducible]
noncomputable def topologicalPushoutChartedSpace
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    (hzero : ∀ a, ∃ q, seam q = topologicalPushoutInl f g (f a)) :
    ChartedSpace H (TopologicalPushout f g) where
  atlas := range (topologicalPushoutAtlasChart (H := H) f g hf hg seam hseam)
  chartAt := topologicalPushoutPreferredChart (H := H) f g hf hg seam hseam hzero
  mem_chart_source z :=
    (topologicalPushoutAtlasChart_covers (H := H)
      f g hf hg seam hseam hzero z).choose_spec
  chart_mem_atlas _ := ⟨_, rfl⟩

section Manifold

variable {𝕜 E : Type u} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)

/-- Once transitions between the three explicit chart classes have been verified, the collared
pushout atlas is a manifold atlas.  The compatibility hypothesis refers to the concrete charts
above; it does not assume an unrelated smooth structure on the pushout. -/
theorem isManifold_topologicalPushoutChartedSpace
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    (hzero : ∀ a, ∃ q, seam q = topologicalPushoutInl f g (f a))
    (hcompat : ∀ i j : TopologicalPushoutAtlasIndex f g N,
      (topologicalPushoutAtlasChart (H := H) f g hf hg seam hseam i).symm.trans
          (topologicalPushoutAtlasChart (H := H) f g hf hg seam hseam j) ∈
        contDiffGroupoid n I) :
    letI := topologicalPushoutChartedSpace (H := H)
      f g hf hg seam hseam hzero
    IsManifold I n (TopologicalPushout f g) := by
  let _ := topologicalPushoutChartedSpace (H := H)
    f g hf hg seam hseam hzero
  refine { compatible := ?_ }
  intro e e' he he'
  obtain ⟨i, rfl⟩ := he
  obtain ⟨j, rfl⟩ := he'
  exact hcompat i j

end Manifold

end Atlas

end SplittingSpheres

end
