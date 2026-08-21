/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.CollaredTopologicalPushout
public import SplittingSpheres.Foundations.CollaredCutSideManifold

/-!
# Automatic smooth manifolds on collared topological pushouts

This file automates compatibility of the three explicit chart families on a collared topological
pushout.  The two canonical seam/off-seam overlaps are open partial homeomorphisms between the
signed seam source and the corresponding open subspaces of the left and right pieces.  Smoothness
of each overlap and its inverse suffices for every chart transition: same-family transitions come
from the native maximal atlases, while left/right off-seam transitions have empty source.

For a literal signed seam map, local diffeomorphism of the left and right branch maps on exactly
their canonical overlap sources supplies both directions of overlap smoothness.  The inverse
argument is local and does not assume global injectivity of either branch.  No smooth structure on
the pushout is used as an input.
-/

@[expose] public section

noncomputable section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

universe u

namespace SplittingSpheres

variable {A X Y N H : Type u}
variable [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalSpace N] [TopologicalSpace H]

variable (f : C(A, X)) (g : C(A, Y))

/-- The canonical coordinate change from the signed seam source to the open part of the left
piece away from the attaching range. -/
noncomputable def topologicalPushoutSeamInlOffSeamOverlap
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    [Nonempty N]
    [Nonempty ↑(topologicalPushoutInlOffSeamOpens f hf)] :
    OpenPartialHomeomorph N
      ↑(topologicalPushoutInlOffSeamOpens f hf) :=
  openEmbeddingOverlap hseam
    (isOpenEmbedding_topologicalPushoutInlOffSeamMap' f g hf hg)

/-- The canonical coordinate change from the signed seam source to the open part of the right
piece away from the attaching range. -/
noncomputable def topologicalPushoutSeamInrOffSeamOverlap
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    [Nonempty N]
    [Nonempty ↑(topologicalPushoutInrOffSeamOpens g hg)] :
    OpenPartialHomeomorph N
      ↑(topologicalPushoutInrOffSeamOpens g hg) :=
  openEmbeddingOverlap hseam
    (isOpenEmbedding_topologicalPushoutInrOffSeamMap' f g hf hg)

theorem range_topologicalPushoutInlOffSeamMap'
    (hf : IsClosedEmbedding f) :
    range (topologicalPushoutInlOffSeamMap' f g hf) =
      topologicalPushoutInlOffSeam f g := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem range_topologicalPushoutInrOffSeamMap'
    (hg : IsClosedEmbedding g) :
    range (topologicalPushoutInrOffSeamMap' f g hg) =
      topologicalPushoutInrOffSeam f g := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, y.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

theorem topologicalPushoutSeamInlOffSeamOverlap_source
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    [Nonempty N]
    [Nonempty ↑(topologicalPushoutInlOffSeamOpens f hf)] :
    (topologicalPushoutSeamInlOffSeamOverlap
      f g hf hg seam hseam).source =
      seam ⁻¹' topologicalPushoutInlOffSeam f g := by
  rw [topologicalPushoutSeamInlOffSeamOverlap, openEmbeddingOverlap,
    OpenPartialHomeomorph.trans_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_source,
    univ_inter,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply,
    OpenPartialHomeomorph.symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target,
    range_topologicalPushoutInlOffSeamMap' f g hf]

theorem topologicalPushoutSeamInrOffSeamOverlap_source
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    [Nonempty N]
    [Nonempty ↑(topologicalPushoutInrOffSeamOpens g hg)] :
    (topologicalPushoutSeamInrOffSeamOverlap
      f g hf hg seam hseam).source =
      seam ⁻¹' topologicalPushoutInrOffSeam f g := by
  rw [topologicalPushoutSeamInrOffSeamOverlap, openEmbeddingOverlap,
    OpenPartialHomeomorph.trans_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_source,
    univ_inter,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply,
    OpenPartialHomeomorph.symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target,
    range_topologicalPushoutInrOffSeamMap' f g hg]

theorem topologicalPushoutSeamInlOffSeamOverlap_pushout_apply
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    [Nonempty N]
    [Nonempty ↑(topologicalPushoutInlOffSeamOpens f hf)]
    {p : N}
    (hp : p ∈ (topologicalPushoutSeamInlOffSeamOverlap
      f g hf hg seam hseam).source) :
    topologicalPushoutInlOffSeamMap' f g hf
        (topologicalPushoutSeamInlOffSeamOverlap
          f g hf hg seam hseam p) = seam p := by
  let hleft := isOpenEmbedding_topologicalPushoutInlOffSeamMap' f g hf hg
  change hleft.toOpenPartialHomeomorph
      (topologicalPushoutInlOffSeamMap' f g hf)
        ((hleft.toOpenPartialHomeomorph
          (topologicalPushoutInlOffSeamMap' f g hf)).symm (seam p)) = seam p
  apply hleft.toOpenPartialHomeomorph_right_inv
  simpa [topologicalPushoutSeamInlOffSeamOverlap,
    openEmbeddingOverlap] using hp

theorem topologicalPushoutSeamInrOffSeamOverlap_pushout_apply
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    [Nonempty N]
    [Nonempty ↑(topologicalPushoutInrOffSeamOpens g hg)]
    {p : N}
    (hp : p ∈ (topologicalPushoutSeamInrOffSeamOverlap
      f g hf hg seam hseam).source) :
    topologicalPushoutInrOffSeamMap' f g hg
        (topologicalPushoutSeamInrOffSeamOverlap
          f g hf hg seam hseam p) = seam p := by
  let hright := isOpenEmbedding_topologicalPushoutInrOffSeamMap' f g hf hg
  change hright.toOpenPartialHomeomorph
      (topologicalPushoutInrOffSeamMap' f g hg)
        ((hright.toOpenPartialHomeomorph
          (topologicalPushoutInrOffSeamMap' f g hg)).symm (seam p)) = seam p
  apply hright.toOpenPartialHomeomorph_right_inv
  simpa [topologicalPushoutSeamInrOffSeamOverlap,
    openEmbeddingOverlap] using hp

omit [TopologicalSpace N] in
theorem topologicalPushoutSeamMap_eq_inl_of_mem_inlOffSeam
    (tau : N → ℝ) (left : N → X) (right : N → Y)
    (hf : Injective f)
    (hrightBoundary : ∀ p, right p ∈ range g → tau p = 0)
    {p : N}
    (hp : topologicalPushoutSeamMap f g tau left right p ∈
      topologicalPushoutInlOffSeam f g) :
    topologicalPushoutSeamMap f g tau left right p =
      topologicalPushoutInl f g (left p) := by
  by_cases hpt : tau p ≤ 0
  · simp [topologicalPushoutSeamMap, hpt]
  · have hptpos : 0 < tau p := lt_of_not_ge hpt
    rcases hp with ⟨x, hx, hxp⟩
    have hcross : topologicalPushoutInl f g x =
        topologicalPushoutInr f g (right p) := by
      simpa [topologicalPushoutSeamMap, hpt] using hxp
    obtain ⟨a, _hfa, hga⟩ :=
      (topologicalPushoutInl_eq_inr_iff f g hf x (right p)).mp hcross
    exact False.elim ((ne_of_gt hptpos)
      (hrightBoundary p ⟨a, hga⟩))

omit [TopologicalSpace N] in
theorem topologicalPushoutSeamMap_eq_inr_of_mem_inrOffSeam
    (tau : N → ℝ) (left : N → X) (right : N → Y)
    (hf : Injective f)
    (hzero : ∀ p, tau p = 0 →
      ∃ a, f a = left p ∧ g a = right p)
    (hleftBoundary : ∀ p, left p ∈ range f → tau p = 0)
    {p : N}
    (hp : topologicalPushoutSeamMap f g tau left right p ∈
      topologicalPushoutInrOffSeam f g) :
    topologicalPushoutSeamMap f g tau left right p =
      topologicalPushoutInr f g (right p) := by
  by_cases hpt : tau p ≤ 0
  · rcases hp with ⟨y, hy, hyp⟩
    have hcross : topologicalPushoutInl f g (left p) =
        topologicalPushoutInr f g y := by
      simpa [topologicalPushoutSeamMap, hpt] using hyp.symm
    obtain ⟨a, hfa, _hga⟩ :=
      (topologicalPushoutInl_eq_inr_iff f g hf (left p) y).mp hcross
    have hptzero : tau p = 0 := hleftBoundary p ⟨a, hfa⟩
    obtain ⟨b, hfb, hgb⟩ := hzero p hptzero
    simp only [topologicalPushoutSeamMap, hpt, ↓reduceIte]
    rw [← hfb, ← hgb]
    exact topologicalPushout_condition f g b
  · simp [topologicalPushoutSeamMap, hpt]

lemma lift_openEmbedding_symm_trans_lift_openEmbedding_source_eq_empty
    {U V Z : Type*}
    [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace Z]
    [Nonempty H]
    {a : U → Z} {b : V → Z}
    (e : OpenPartialHomeomorph U H) (e' : OpenPartialHomeomorph V H)
    (ha : IsOpenEmbedding a) (hb : IsOpenEmbedding b)
    (hd : Disjoint (range a) (range b)) :
    ((e.lift_openEmbedding ha).symm.trans
      (e'.lift_openEmbedding hb)).source = ∅ := by
  ext z
  constructor
  · intro hz
    have hz' := hz
    simp only [OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.lift_openEmbedding_symm_source,
      OpenPartialHomeomorph.lift_openEmbedding_symm,
      OpenPartialHomeomorph.lift_openEmbedding_source,
      mem_inter_iff, mem_preimage, comp_apply] at hz'
    rcases hz'.2 with ⟨v, hv, hvz⟩
    exact (Set.disjoint_left.1 hd)
      ⟨e.symm z, rfl⟩ ⟨v, hvz⟩
  · simp

section Manifold

variable [Nonempty H] [ChartedSpace H X] [ChartedSpace H Y]
variable [ChartedSpace H N]
variable {𝕜 E : Type u} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)

omit [Nonempty H] in
theorem contMDiffOn_openPartialHomeomorphToOpens_of_contMDiffOn
    (U : Opens X) (q : OpenPartialHomeomorph N ↑U)
    (c : N → X)
    (happly : ∀ p, p ∈ q.source → (q p : X) = c p)
    (hc : ContMDiffOn I I n c q.source) :
    ContMDiffOn I I n q q.source := by
  have hambient : ContMDiffOn I I n
      ((Subtype.val : ↑U → X) ∘ q) q.source :=
    hc.congr fun p hp ↦ happly p hp
  intro p hp
  exact (contMDiffWithinAt_subtypeVal_comp_iff_of_order
    I n U q q.source p).mp (hambient p hp)

omit [Nonempty H] in
theorem contMDiffOn_openPartialHomeomorphToOpens_symm_of_localDiffeomorphOn
    (U : Opens X) (q : OpenPartialHomeomorph N ↑U)
    (c : N → X)
    (happly : ∀ p, p ∈ q.source → (q p : X) = c p)
    (hlocal : IsLocalDiffeomorphOn I I n c q.source) :
    ContMDiffOn I I n q.symm q.target := by
  intro y hy
  let p := q.symm y
  have hp : p ∈ q.source := q.symm.mapsTo hy
  let hld : IsLocalDiffeomorphAt I I n c p := hlocal ⟨p, hp⟩
  have hcpeqy : c p = y.1 := by
    rw [← happly p hp]
    exact congrArg Subtype.val (q.right_inv hy)
  have hval : ContMDiffAt I I n (Subtype.val : ↑U → X) y :=
    (contMDiff_subtype_val (I := I) (U := U)).contMDiffAt
  have hsmooth : ContMDiffAt I I n
      (hld.localInverse ∘ (Subtype.val : ↑U → X)) y :=
    hld.localInverse_contMDiffAt.comp_of_eq hval hcpeqy.symm
  have hyinv : y.1 ∈ hld.localInverse.source := by
    rw [← hcpeqy]
    exact hld.localInverse_mem_source
  have hqinvtarget :
      q.symm ⁻¹' hld.localInverse.target ∈ 𝓝 y :=
    q.continuousAt_symm hy
      (hld.localInverse.open_target.mem_nhds
        hld.localInverse_mem_target)
  have hevent : q.symm =ᶠ[𝓝 y]
      hld.localInverse ∘ (Subtype.val : ↑U → X) := by
    filter_upwards [
      (q.open_target.inter
        (hld.localInverse_open_source.preimage continuous_subtype_val)).mem_nhds
          ⟨hy, hyinv⟩,
      hqinvtarget] with z hz hzTarget
    have hcq : c (q.symm z) = z.1 := by
      rw [← happly (q.symm z) (q.symm.mapsTo hz.1), q.right_inv hz.1]
    have hcinv : c (hld.localInverse z.1) = z.1 :=
      hld.localInverse_right_inv hz.2
    calc
      q.symm z = hld.localInverse (c (q.symm z)) :=
        (hld.localInverse_left_inv hzTarget).symm
      _ = hld.localInverse (c (hld.localInverse z.1)) := by
        rw [hcq, hcinv]
      _ = hld.localInverse z.1 :=
        hld.localInverse_left_inv (hld.localInverse.map_source hz.2)
  exact (hsmooth.congr_of_eventuallyEq hevent).contMDiffWithinAt

theorem topologicalPushoutAtlasChart_compatible_of_overlaps
    [IsManifold I n X] [IsManifold I n Y] [IsManifold I n N]
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    [Nonempty N]
    [Nonempty ↑(topologicalPushoutInlOffSeamOpens f hf)]
    [Nonempty ↑(topologicalPushoutInrOffSeamOpens g hg)]
    (hleft : ContMDiffOn I I n
      (topologicalPushoutSeamInlOffSeamOverlap f g hf hg seam hseam)
      (topologicalPushoutSeamInlOffSeamOverlap f g hf hg seam hseam).source)
    (hleft' : ContMDiffOn I I n
      (topologicalPushoutSeamInlOffSeamOverlap f g hf hg seam hseam).symm
      (topologicalPushoutSeamInlOffSeamOverlap f g hf hg seam hseam).target)
    (hright : ContMDiffOn I I n
      (topologicalPushoutSeamInrOffSeamOverlap f g hf hg seam hseam)
      (topologicalPushoutSeamInrOffSeamOverlap f g hf hg seam hseam).source)
    (hright' : ContMDiffOn I I n
      (topologicalPushoutSeamInrOffSeamOverlap f g hf hg seam hseam).symm
      (topologicalPushoutSeamInrOffSeamOverlap f g hf hg seam hseam).target) :
    ∀ i j : TopologicalPushoutAtlasIndex f g N,
      (topologicalPushoutAtlasChart (H := H)
        f g hf hg seam hseam i).symm.trans
          (topologicalPushoutAtlasChart (H := H)
            f g hf hg seam hseam j) ∈
        contDiffGroupoid n I := by
  intro i j
  cases i with
  | inl x =>
      cases j with
      | inl y =>
          let U := topologicalPushoutInlOffSeamOpens f hf
          let xU : ↑U := ⟨x.1, x.2⟩
          let yU : ↑U := ⟨y.1, y.2⟩
          change
            ((chartAt H xU).lift_openEmbedding
              (isOpenEmbedding_topologicalPushoutInlOffSeamMap' f g hf hg)).symm.trans
                ((chartAt H yU).lift_openEmbedding
                  (isOpenEmbedding_topologicalPushoutInlOffSeamMap' f g hf hg)) ∈
              contDiffGroupoid n I
          rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
          exact (inferInstance : IsManifold I n ↑U).compatible
            (chart_mem_atlas H xU) (chart_mem_atlas H yU)
      | inr y =>
          let U := topologicalPushoutInlOffSeamOpens f hf
          let V := topologicalPushoutInrOffSeamOpens g hg
          let xU : ↑U := ⟨x.1, x.2⟩
          let yV : ↑V := ⟨y.1, y.2⟩
          change
            ((chartAt H xU).lift_openEmbedding
              (isOpenEmbedding_topologicalPushoutInlOffSeamMap' f g hf hg)).symm.trans
                ((chartAt H yV).lift_openEmbedding
                  (isOpenEmbedding_topologicalPushoutInrOffSeamMap' f g hf hg)) ∈
              contDiffGroupoid n I
          apply ContDiffGroupoid.mem_of_source_eq_empty
          apply lift_openEmbedding_symm_trans_lift_openEmbedding_source_eq_empty
          rw [range_topologicalPushoutInlOffSeamMap' f g hf,
            range_topologicalPushoutInrOffSeamMap' f g hg]
          exact disjoint_topologicalPushoutOffSeam f g hf.injective
      | seam q =>
          let U := topologicalPushoutInlOffSeamOpens f hf
          let xU : ↑U := ⟨x.1, x.2⟩
          let eU : OpenPartialHomeomorph ↑U H :=
            (chartAt H x.1).subtypeRestr ⟨xU⟩
          have heU : eU ∈ IsManifold.maximalAtlas I n ↑U :=
            StructureGroupoid.subtypeRestr_mem_maximalAtlas
              (G := contDiffGroupoid n I)
              (chart_mem_atlas H x.1) ⟨xU⟩
          have htransition :=
            maximalAtlas_symm_trans_openPartialHomeomorph_trans_maximalAtlas_mem_contDiffGroupoid
              I n (chartAt H q)
              ((contDiffGroupoid n I).chart_mem_maximalAtlas q)
              (topologicalPushoutSeamInlOffSeamOverlap f g hf hg seam hseam)
              hleft hleft' eU heU
          have heq := lift_openEmbedding_symm_trans_lift_openEmbedding
            (chartAt H q) eU hseam
            (isOpenEmbedding_topologicalPushoutInlOffSeamMap' f g hf hg)
          have hdirect :
              (topologicalPushoutSeamChart (H := H) f g seam hseam q).symm.trans
                  (topologicalPushoutInlOffSeamChart (H := H) f g hf hg x) ∈
                contDiffGroupoid n I := by
            apply (contDiffGroupoid n I).mem_of_eqOnSource htransition
            convert heq using 1
            all_goals
              ext z <;> simp [topologicalPushoutSeamChart,
                topologicalPushoutInlOffSeamChart,
                topologicalPushoutInlOffSeamMap',
                topologicalPushoutSeamInlOffSeamOverlap,
                eU, U, openEmbeddingOverlap]
          have hs := (contDiffGroupoid n I).symm hdirect
          change
            (topologicalPushoutInlOffSeamChart (H := H) f g hf hg x).symm.trans
                (topologicalPushoutSeamChart (H := H) f g seam hseam q) ∈
              contDiffGroupoid n I
          change
            ((topologicalPushoutSeamChart (H := H) f g seam hseam q).symm.trans
              (topologicalPushoutInlOffSeamChart (H := H) f g hf hg x)).symm ∈
                contDiffGroupoid n I
          exact hs
  | inr y =>
      cases j with
      | inl x =>
          let U := topologicalPushoutInlOffSeamOpens f hf
          let V := topologicalPushoutInrOffSeamOpens g hg
          let xU : ↑U := ⟨x.1, x.2⟩
          let yV : ↑V := ⟨y.1, y.2⟩
          change
            ((chartAt H yV).lift_openEmbedding
              (isOpenEmbedding_topologicalPushoutInrOffSeamMap' f g hf hg)).symm.trans
                ((chartAt H xU).lift_openEmbedding
                  (isOpenEmbedding_topologicalPushoutInlOffSeamMap' f g hf hg)) ∈
              contDiffGroupoid n I
          apply ContDiffGroupoid.mem_of_source_eq_empty
          apply lift_openEmbedding_symm_trans_lift_openEmbedding_source_eq_empty
          rw [range_topologicalPushoutInrOffSeamMap' f g hg,
            range_topologicalPushoutInlOffSeamMap' f g hf]
          exact (disjoint_topologicalPushoutOffSeam f g hf.injective).symm
      | inr z =>
          let V := topologicalPushoutInrOffSeamOpens g hg
          let yV : ↑V := ⟨y.1, y.2⟩
          let zV : ↑V := ⟨z.1, z.2⟩
          change
            ((chartAt H yV).lift_openEmbedding
              (isOpenEmbedding_topologicalPushoutInrOffSeamMap' f g hf hg)).symm.trans
                ((chartAt H zV).lift_openEmbedding
                  (isOpenEmbedding_topologicalPushoutInrOffSeamMap' f g hf hg)) ∈
              contDiffGroupoid n I
          rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
          exact (inferInstance : IsManifold I n ↑V).compatible
            (chart_mem_atlas H yV) (chart_mem_atlas H zV)
      | seam q =>
          let V := topologicalPushoutInrOffSeamOpens g hg
          let yV : ↑V := ⟨y.1, y.2⟩
          let eV : OpenPartialHomeomorph ↑V H :=
            (chartAt H y.1).subtypeRestr ⟨yV⟩
          have heV : eV ∈ IsManifold.maximalAtlas I n ↑V :=
            StructureGroupoid.subtypeRestr_mem_maximalAtlas
              (G := contDiffGroupoid n I)
              (chart_mem_atlas H y.1) ⟨yV⟩
          have htransition :=
            maximalAtlas_symm_trans_openPartialHomeomorph_trans_maximalAtlas_mem_contDiffGroupoid
              I n (chartAt H q)
              ((contDiffGroupoid n I).chart_mem_maximalAtlas q)
              (topologicalPushoutSeamInrOffSeamOverlap f g hf hg seam hseam)
              hright hright' eV heV
          have heq := lift_openEmbedding_symm_trans_lift_openEmbedding
            (chartAt H q) eV hseam
            (isOpenEmbedding_topologicalPushoutInrOffSeamMap' f g hf hg)
          have hdirect :
              (topologicalPushoutSeamChart (H := H) f g seam hseam q).symm.trans
                  (topologicalPushoutInrOffSeamChart (H := H) f g hf hg y) ∈
                contDiffGroupoid n I := by
            apply (contDiffGroupoid n I).mem_of_eqOnSource htransition
            convert heq using 1
            all_goals
              ext z <;> simp [topologicalPushoutSeamChart,
                topologicalPushoutInrOffSeamChart,
                topologicalPushoutInrOffSeamMap',
                topologicalPushoutSeamInrOffSeamOverlap,
                eV, V, openEmbeddingOverlap]
          have hs := (contDiffGroupoid n I).symm hdirect
          change
            (topologicalPushoutInrOffSeamChart (H := H) f g hf hg y).symm.trans
                (topologicalPushoutSeamChart (H := H) f g seam hseam q) ∈
              contDiffGroupoid n I
          change
            ((topologicalPushoutSeamChart (H := H) f g seam hseam q).symm.trans
              (topologicalPushoutInrOffSeamChart (H := H) f g hf hg y)).symm ∈
                contDiffGroupoid n I
          exact hs
  | seam p =>
      cases j with
      | inl x =>
          let U := topologicalPushoutInlOffSeamOpens f hf
          let xU : ↑U := ⟨x.1, x.2⟩
          let eU : OpenPartialHomeomorph ↑U H :=
            (chartAt H x.1).subtypeRestr ⟨xU⟩
          have heU : eU ∈ IsManifold.maximalAtlas I n ↑U :=
            StructureGroupoid.subtypeRestr_mem_maximalAtlas
              (G := contDiffGroupoid n I)
              (chart_mem_atlas H x.1) ⟨xU⟩
          have htransition :=
            maximalAtlas_symm_trans_openPartialHomeomorph_trans_maximalAtlas_mem_contDiffGroupoid
              I n (chartAt H p)
              ((contDiffGroupoid n I).chart_mem_maximalAtlas p)
              (topologicalPushoutSeamInlOffSeamOverlap f g hf hg seam hseam)
              hleft hleft' eU heU
          have heq := lift_openEmbedding_symm_trans_lift_openEmbedding
            (chartAt H p) eU hseam
            (isOpenEmbedding_topologicalPushoutInlOffSeamMap' f g hf hg)
          change
            (topologicalPushoutSeamChart (H := H) f g seam hseam p).symm.trans
                (topologicalPushoutInlOffSeamChart (H := H) f g hf hg x) ∈
              contDiffGroupoid n I
          apply (contDiffGroupoid n I).mem_of_eqOnSource htransition
          convert heq using 1
          all_goals
            ext z <;> simp [topologicalPushoutSeamChart,
              topologicalPushoutInlOffSeamChart,
              topologicalPushoutInlOffSeamMap',
              topologicalPushoutSeamInlOffSeamOverlap,
              eU, U, openEmbeddingOverlap]
      | inr y =>
          let V := topologicalPushoutInrOffSeamOpens g hg
          let yV : ↑V := ⟨y.1, y.2⟩
          let eV : OpenPartialHomeomorph ↑V H :=
            (chartAt H y.1).subtypeRestr ⟨yV⟩
          have heV : eV ∈ IsManifold.maximalAtlas I n ↑V :=
            StructureGroupoid.subtypeRestr_mem_maximalAtlas
              (G := contDiffGroupoid n I)
              (chart_mem_atlas H y.1) ⟨yV⟩
          have htransition :=
            maximalAtlas_symm_trans_openPartialHomeomorph_trans_maximalAtlas_mem_contDiffGroupoid
              I n (chartAt H p)
              ((contDiffGroupoid n I).chart_mem_maximalAtlas p)
              (topologicalPushoutSeamInrOffSeamOverlap f g hf hg seam hseam)
              hright hright' eV heV
          have heq := lift_openEmbedding_symm_trans_lift_openEmbedding
            (chartAt H p) eV hseam
            (isOpenEmbedding_topologicalPushoutInrOffSeamMap' f g hf hg)
          change
            (topologicalPushoutSeamChart (H := H) f g seam hseam p).symm.trans
                (topologicalPushoutInrOffSeamChart (H := H) f g hf hg y) ∈
              contDiffGroupoid n I
          apply (contDiffGroupoid n I).mem_of_eqOnSource htransition
          convert heq using 1
          all_goals
            ext z <;> simp [topologicalPushoutSeamChart,
              topologicalPushoutInrOffSeamChart,
              topologicalPushoutInrOffSeamMap',
              topologicalPushoutSeamInrOffSeamOverlap,
              eV, V, openEmbeddingOverlap]
      | seam q =>
          change
            ((chartAt H p).lift_openEmbedding hseam).symm.trans
                ((chartAt H q).lift_openEmbedding hseam) ∈
              contDiffGroupoid n I
          rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
          exact (inferInstance : IsManifold I n N).compatible
            (chart_mem_atlas H p) (chart_mem_atlas H q)

theorem topologicalPushoutAtlasChart_compatible_of_localDiffeomorphOn
    [IsManifold I n X] [IsManifold I n Y] [IsManifold I n N]
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (seam : N → TopologicalPushout f g) (hseam : IsOpenEmbedding seam)
    (left : N → X) (right : N → Y)
    [Nonempty N]
    [Nonempty ↑(topologicalPushoutInlOffSeamOpens f hf)]
    [Nonempty ↑(topologicalPushoutInrOffSeamOpens g hg)]
    (hleftBranch : ∀ p,
      p ∈ (topologicalPushoutSeamInlOffSeamOverlap
        f g hf hg seam hseam).source →
      seam p = topologicalPushoutInl f g (left p))
    (hrightBranch : ∀ p,
      p ∈ (topologicalPushoutSeamInrOffSeamOverlap
        f g hf hg seam hseam).source →
      seam p = topologicalPushoutInr f g (right p))
    (hleftLocal : IsLocalDiffeomorphOn I I n left
      (topologicalPushoutSeamInlOffSeamOverlap
        f g hf hg seam hseam).source)
    (hrightLocal : IsLocalDiffeomorphOn I I n right
      (topologicalPushoutSeamInrOffSeamOverlap
        f g hf hg seam hseam).source) :
    ∀ i j : TopologicalPushoutAtlasIndex f g N,
      (topologicalPushoutAtlasChart (H := H)
        f g hf hg seam hseam i).symm.trans
          (topologicalPushoutAtlasChart (H := H)
            f g hf hg seam hseam j) ∈
        contDiffGroupoid n I := by
  let U := topologicalPushoutInlOffSeamOpens f hf
  let V := topologicalPushoutInrOffSeamOpens g hg
  let qleft := topologicalPushoutSeamInlOffSeamOverlap
    f g hf hg seam hseam
  let qright := topologicalPushoutSeamInrOffSeamOverlap
    f g hf hg seam hseam
  have hleftApply : ∀ p, p ∈ qleft.source →
      (qleft p : X) = left p := by
    intro p hp
    apply topologicalPushoutInl_injective f g hg.injective
    change topologicalPushoutInlOffSeamMap' f g hf (qleft p) =
      topologicalPushoutInl f g (left p)
    exact (topologicalPushoutSeamInlOffSeamOverlap_pushout_apply
      f g hf hg seam hseam hp).trans (hleftBranch p hp)
  have hrightApply : ∀ p, p ∈ qright.source →
      (qright p : Y) = right p := by
    intro p hp
    apply topologicalPushoutInr_injective f g hf.injective
    change topologicalPushoutInrOffSeamMap' f g hg (qright p) =
      topologicalPushoutInr f g (right p)
    exact (topologicalPushoutSeamInrOffSeamOverlap_pushout_apply
      f g hf hg seam hseam hp).trans (hrightBranch p hp)
  exact topologicalPushoutAtlasChart_compatible_of_overlaps
    f g I n hf hg seam hseam
      (contMDiffOn_openPartialHomeomorphToOpens_of_contMDiffOn
        I n U qleft left hleftApply hleftLocal.contMDiffOn)
      (contMDiffOn_openPartialHomeomorphToOpens_symm_of_localDiffeomorphOn
        I n U qleft left hleftApply hleftLocal)
      (contMDiffOn_openPartialHomeomorphToOpens_of_contMDiffOn
        I n V qright right hrightApply hrightLocal.contMDiffOn)
      (contMDiffOn_openPartialHomeomorphToOpens_symm_of_localDiffeomorphOn
        I n V qright right hrightApply hrightLocal)

theorem topologicalPushoutSeamMap_atlasChart_compatible_of_localDiffeomorphOn
    [IsManifold I n X] [IsManifold I n Y] [IsManifold I n N]
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (tau : N → ℝ) (left : N → X) (right : N → Y)
    (hseam : IsOpenEmbedding
      (topologicalPushoutSeamMap f g tau left right))
    [Nonempty N]
    [Nonempty ↑(topologicalPushoutInlOffSeamOpens f hf)]
    [Nonempty ↑(topologicalPushoutInrOffSeamOpens g hg)]
    (hzero : ∀ p, tau p = 0 →
      ∃ a, f a = left p ∧ g a = right p)
    (hleftBoundary : ∀ p, left p ∈ range f → tau p = 0)
    (hrightBoundary : ∀ p, right p ∈ range g → tau p = 0)
    (hleftLocal : IsLocalDiffeomorphOn I I n left
      (topologicalPushoutSeamInlOffSeamOverlap f g hf hg
        (topologicalPushoutSeamMap f g tau left right) hseam).source)
    (hrightLocal : IsLocalDiffeomorphOn I I n right
      (topologicalPushoutSeamInrOffSeamOverlap f g hf hg
        (topologicalPushoutSeamMap f g tau left right) hseam).source) :
    ∀ i j : TopologicalPushoutAtlasIndex f g N,
      (topologicalPushoutAtlasChart (H := H) f g hf hg
        (topologicalPushoutSeamMap f g tau left right) hseam i).symm.trans
          (topologicalPushoutAtlasChart (H := H) f g hf hg
            (topologicalPushoutSeamMap f g tau left right) hseam j) ∈
        contDiffGroupoid n I := by
  apply topologicalPushoutAtlasChart_compatible_of_localDiffeomorphOn
    f g I n hf hg (topologicalPushoutSeamMap f g tau left right)
      hseam left right
  · intro p hp
    rw [topologicalPushoutSeamInlOffSeamOverlap_source
      f g hf hg (topologicalPushoutSeamMap f g tau left right) hseam] at hp
    exact topologicalPushoutSeamMap_eq_inl_of_mem_inlOffSeam
      f g tau left right hf.injective hrightBoundary hp
  · intro p hp
    rw [topologicalPushoutSeamInrOffSeamOverlap_source
      f g hf hg (topologicalPushoutSeamMap f g tau left right) hseam] at hp
    exact topologicalPushoutSeamMap_eq_inr_of_mem_inrOffSeam
      f g tau left right hf.injective hzero hleftBoundary hp
  · exact hleftLocal
  · exact hrightLocal

theorem isManifold_topologicalPushoutChartedSpace_of_signed_localDiffeomorphOn
    [IsManifold I n X] [IsManifold I n Y] [IsManifold I n N]
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (tau : N → ℝ) (left : N → X) (right : N → Y)
    (hseam : IsOpenEmbedding
      (topologicalPushoutSeamMap f g tau left right))
    (hcover : ∀ a, ∃ q,
      topologicalPushoutSeamMap f g tau left right q =
        topologicalPushoutInl f g (f a))
    [Nonempty N]
    [Nonempty ↑(topologicalPushoutInlOffSeamOpens f hf)]
    [Nonempty ↑(topologicalPushoutInrOffSeamOpens g hg)]
    (hzero : ∀ p, tau p = 0 →
      ∃ a, f a = left p ∧ g a = right p)
    (hleftBoundary : ∀ p, left p ∈ range f → tau p = 0)
    (hrightBoundary : ∀ p, right p ∈ range g → tau p = 0)
    (hleftLocal : IsLocalDiffeomorphOn I I n left
      (topologicalPushoutSeamInlOffSeamOverlap f g hf hg
        (topologicalPushoutSeamMap f g tau left right) hseam).source)
    (hrightLocal : IsLocalDiffeomorphOn I I n right
      (topologicalPushoutSeamInrOffSeamOverlap f g hf hg
        (topologicalPushoutSeamMap f g tau left right) hseam).source) :
    letI := topologicalPushoutChartedSpace (H := H) f g hf hg
      (topologicalPushoutSeamMap f g tau left right) hseam hcover
    IsManifold I n (TopologicalPushout f g) :=
  isManifold_topologicalPushoutChartedSpace f g I n hf hg
    (topologicalPushoutSeamMap f g tau left right) hseam hcover
      (topologicalPushoutSeamMap_atlasChart_compatible_of_localDiffeomorphOn
        f g I n hf hg tau left right hseam hzero
          hleftBoundary hrightBoundary hleftLocal hrightLocal)

end Manifold

end SplittingSpheres

end
