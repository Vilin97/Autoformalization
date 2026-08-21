/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.CollaredCutSide
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Automatic smooth manifolds on collared cut sides

This file proves that the direct atlas of a collared cut side is automatically smooth when the
ambient space and collar source use the same model with corners.  The only genuinely mixed input
is local diffeomorphism of the ambient collar map over the off-boundary overlap.  A global local
diffeomorphism is neither assumed nor appropriate for a one-sided collar, whose full range need
not be ambient-open.

The lower-level API exposes the canonical partial homeomorphism from the collar source to the
ambient-open off-boundary region.  Smoothness in its two directions suffices for all mixed chart
changes.  The application-facing API derives those two directions from local diffeomorphism on
exactly the overlap.  Global smoothness of the collar map is needed only for smoothness of the
cut-side inclusion at the new boundary.
-/

@[expose] public section

noncomputable section


open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

universe u v w

namespace SplittingSpheres

section Topology

variable {X Y Z H : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalSpace Z] [TopologicalSpace H] [Nonempty H]
variable [Nonempty X] [Nonempty Y]
variable {f : X → Z} {g : Y → Z}

noncomputable def openEmbeddingOverlap
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) :
    OpenPartialHomeomorph X Y :=
  (hf.toOpenPartialHomeomorph f).trans
    (hg.toOpenPartialHomeomorph g).symm

lemma lift_openEmbedding_symm_trans_lift_openEmbedding
    (e : OpenPartialHomeomorph X H) (e' : OpenPartialHomeomorph Y H)
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) :
    (e.lift_openEmbedding hf).symm.trans
        (e'.lift_openEmbedding hg) ≈
      (e.symm.trans (openEmbeddingOverlap hf hg)).trans e' := by
  constructor
  · ext z
    simp only [OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.lift_openEmbedding_symm,
      OpenPartialHomeomorph.lift_openEmbedding_source,
      mem_inter_iff, mem_preimage, comp_apply,
      openEmbeddingOverlap,
      IsOpenEmbedding.toOpenPartialHomeomorph_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_target,
      IsOpenEmbedding.toOpenPartialHomeomorph_apply,
      univ_inter,
      OpenPartialHomeomorph.symm_source]
    constructor
    · rintro ⟨hz, x, hx, hxf⟩
      refine ⟨⟨hz, ⟨x, hxf⟩⟩, ?_⟩
      change (hg.toOpenPartialHomeomorph g).symm
        (f (e.symm z)) ∈ e'.source
      rw [← hxf, hg.toOpenPartialHomeomorph_left_inv]
      exact hx
    · rintro ⟨⟨hz, hrange⟩, hx⟩
      refine ⟨hz, ?_⟩
      refine ⟨(hg.toOpenPartialHomeomorph g).symm
        (f (e.symm z)), hx, ?_⟩
      exact hg.toOpenPartialHomeomorph_right_inv g hrange
  · intro z hz
    simp only [OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.lift_openEmbedding_symm,
      OpenPartialHomeomorph.lift_openEmbedding_source,
      mem_inter_iff, mem_preimage, comp_apply] at hz
    rcases hz.2 with ⟨x, hx, hxf⟩
    simp only [OpenPartialHomeomorph.trans_apply,
      OpenPartialHomeomorph.lift_openEmbedding_symm,
      OpenPartialHomeomorph.lift_openEmbedding_toFun,
      comp_apply, openEmbeddingOverlap,
      IsOpenEmbedding.toOpenPartialHomeomorph_apply]
    rw [← hxf, hg.injective.extend_apply e',
      hg.toOpenPartialHomeomorph_left_inv]

end Topology

variable {M P H : Type*}
variable [TopologicalSpace M] [TopologicalSpace P] [TopologicalSpace H]

section Atlas

variable [Nonempty H] [ChartedSpace H M] [ChartedSpace H P]

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)

omit [Nonempty H] in
lemma mem_contDiffGroupoid_of_contMDiffOn
    (e : OpenPartialHomeomorph H H)
    (he : ContMDiffOn I I n e e.source)
    (he' : ContMDiffOn I I n e.symm e.target) :
    e ∈ contDiffGroupoid n I := by
  have hmax : e ∈ IsManifold.maximalAtlas I n H :=
    e.mem_maximalAtlas_of_contMDiffOn he he'
  have h := (hmax (OpenPartialHomeomorph.refl H) (by simp)).2
  change (OpenPartialHomeomorph.refl H).trans e ∈
    contDiffGroupoid n I at h
  simpa only [OpenPartialHomeomorph.refl_trans] using h

omit [Nonempty H] in
lemma contMDiffOn_maximalAtlas_symm_trans_openPartialHomeomorph_trans_maximalAtlas
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace H X] [ChartedSpace H Y]
    [IsManifold I n X] [IsManifold I n Y]
    (e : OpenPartialHomeomorph X H)
    (he : e ∈ IsManifold.maximalAtlas I n X)
    (q : OpenPartialHomeomorph X Y)
    (hq : ContMDiffOn I I n q q.source)
    (e' : OpenPartialHomeomorph Y H)
    (he' : e' ∈ IsManifold.maximalAtlas I n Y) :
    ContMDiffOn I I n ((e.symm.trans q).trans e')
      ((e.symm.trans q).trans e').source := by
  have h₁ : ContMDiffOn I I n e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas he
  have h₂ := hq.comp' h₁
  have h₃ := (contMDiffOn_of_mem_maximalAtlas he').comp' h₂
  change ContMDiffOn I I n
    (fun z ↦ e' (q (e.symm z)))
    (e.target ∩ e.symm ⁻¹' q.source ∩
      (fun z ↦ q (e.symm z)) ⁻¹' e'.source)
  exact h₃

omit [Nonempty H] in
lemma maximalAtlas_symm_trans_openPartialHomeomorph_trans_maximalAtlas_mem_contDiffGroupoid
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace H X] [ChartedSpace H Y]
    [IsManifold I n X] [IsManifold I n Y]
    (e : OpenPartialHomeomorph X H)
    (he : e ∈ IsManifold.maximalAtlas I n X)
    (q : OpenPartialHomeomorph X Y)
    (hq : ContMDiffOn I I n q q.source)
    (hq' : ContMDiffOn I I n q.symm q.target)
    (e' : OpenPartialHomeomorph Y H)
    (he' : e' ∈ IsManifold.maximalAtlas I n Y) :
    (e.symm.trans q).trans e' ∈ contDiffGroupoid n I := by
  apply mem_contDiffGroupoid_of_contMDiffOn I n
  · exact contMDiffOn_maximalAtlas_symm_trans_openPartialHomeomorph_trans_maximalAtlas
      I n e he q hq e' he'
  · change ContMDiffOn I I n (((e.symm.trans q).trans e').symm)
      (((e.symm.trans q).trans e').symm).source
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
    rw [← OpenPartialHomeomorph.trans_assoc]
    exact contMDiffOn_maximalAtlas_symm_trans_openPartialHomeomorph_trans_maximalAtlas
      I n e' he' q.symm hq' e he

def collaredCutSideOffBoundaryOpensMap
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (x : ↑(collaredCutSideOffBoundaryOpens C B hopen)) :
    CollaredCutSide C :=
  ⟨x.1, x.2.1⟩

theorem range_collaredCutSideOffBoundaryOpensMap
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B)) :
    range (collaredCutSideOffBoundaryOpensMap C B hopen) =
      (Subtype.val : CollaredCutSide C → M) ⁻¹'
        collaredCutSideOffBoundary C B := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hz
    exact ⟨⟨z.1, hz⟩, Subtype.ext rfl⟩

theorem isOpenEmbedding_collaredCutSideOffBoundaryOpensMap
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B)) :
    IsOpenEmbedding (collaredCutSideOffBoundaryOpensMap C B hopen) := by
  refine ⟨?_, ?_⟩
  · apply Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
    change IsEmbedding
      (Subtype.val : ↑(collaredCutSideOffBoundaryOpens C B hopen) → M)
    exact Topology.IsEmbedding.subtypeVal
  · have hrange : range (collaredCutSideOffBoundaryOpensMap C B hopen) =
        (Subtype.val : CollaredCutSide C → M) ⁻¹'
          collaredCutSideOffBoundary C B :=
      range_collaredCutSideOffBoundaryOpensMap C B hopen
    rw [hrange]
    exact hopen.preimage continuous_subtype_val

noncomputable def collaredCutSideOverlap
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    [Nonempty P]
    [Nonempty ↑(collaredCutSideOffBoundaryOpens C B hopen)] :
    OpenPartialHomeomorph P
      ↑(collaredCutSideOffBoundaryOpens C B hopen) :=
  openEmbeddingOverlap hcollar
    (isOpenEmbedding_collaredCutSideOffBoundaryOpensMap C B hopen)

theorem collaredCutSideOverlap_source
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    [Nonempty P]
    [Nonempty ↑(collaredCutSideOffBoundaryOpens C B hopen)] :
    (collaredCutSideOverlap C B hopen c hc hcollar).source =
      c ⁻¹' collaredCutSideOffBoundary C B := by
  rw [collaredCutSideOverlap, openEmbeddingOverlap,
    OpenPartialHomeomorph.trans_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_source,
    univ_inter,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply,
    OpenPartialHomeomorph.symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target,
    range_collaredCutSideOffBoundaryOpensMap]
  rfl

theorem collaredCutSideOverlap_coe_apply
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    [Nonempty P]
    [Nonempty ↑(collaredCutSideOffBoundaryOpens C B hopen)]
    {p : P} (hp : p ∈ (collaredCutSideOverlap C B hopen c hc hcollar).source) :
    ((collaredCutSideOverlap C B hopen c hc hcollar p :
      ↑(collaredCutSideOffBoundaryOpens C B hopen)) : M) = c p := by
  have hp' : c p ∈ collaredCutSideOffBoundary C B := by
    rw [collaredCutSideOverlap_source C B hopen c hc hcollar] at hp
    exact hp
  let y : ↑(collaredCutSideOffBoundaryOpens C B hopen) := ⟨c p, hp'⟩
  have heq : collaredCutSideOffBoundaryOpensMap C B hopen y =
      collaredCutSideHalfCollarMap C c hc p := Subtype.ext rfl
  let hj := isOpenEmbedding_collaredCutSideOffBoundaryOpensMap C B hopen
  have hqy : collaredCutSideOverlap C B hopen c hc hcollar p = y := by
    change
      (hj.toOpenPartialHomeomorph
          (collaredCutSideOffBoundaryOpensMap C B hopen)).symm
            (collaredCutSideHalfCollarMap C c hc p) = y
    rw [← heq]
    rw [hj.toOpenPartialHomeomorph_left_inv]
  simpa only [y] using congrArg Subtype.val hqy

theorem collaredCutSideOverlap_symm_coe_apply
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    [Nonempty P]
    [Nonempty ↑(collaredCutSideOffBoundaryOpens C B hopen)]
    {y : ↑(collaredCutSideOffBoundaryOpens C B hopen)}
    (hy : y ∈ (collaredCutSideOverlap C B hopen c hc hcollar).target) :
    c ((collaredCutSideOverlap C B hopen c hc hcollar).symm y) = y.1 := by
  have hright := (collaredCutSideOverlap C B hopen c hc hcollar).right_inv hy
  have happ := collaredCutSideOverlap_coe_apply C B hopen c hc hcollar
    ((collaredCutSideOverlap C B hopen c hc hcollar).symm.mapsTo hy)
  rw [← happ]
  exact congrArg Subtype.val hright

omit [Nonempty H] in
lemma contMDiffWithinAt_subtypeVal_comp_iff_of_order
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace H X] [ChartedSpace H Y]
    (U : Opens Y) (f : X → U) (s : Set X) (x : X) :
    ContMDiffWithinAt I I n (Subtype.val ∘ f) s x ↔
      ContMDiffWithinAt I I n f s x :=
  ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff f s x

omit [Nonempty H] in
theorem contMDiffOn_collaredCutSideOverlap
    [IsManifold I n M] [IsManifold I n P]
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    [Nonempty P]
    [Nonempty ↑(collaredCutSideOffBoundaryOpens C B hopen)]
    (hcmooth : ContMDiffOn I I n c
      (c ⁻¹' collaredCutSideOffBoundary C B)) :
    ContMDiffOn I I n (collaredCutSideOverlap C B hopen c hc hcollar)
      (collaredCutSideOverlap C B hopen c hc hcollar).source := by
  let U := collaredCutSideOffBoundaryOpens C B hopen
  let q := collaredCutSideOverlap C B hopen c hc hcollar
  have hcsource : ContMDiffOn I I n c q.source := by
    rw [collaredCutSideOverlap_source C B hopen c hc hcollar]
    exact hcmooth
  have hambient : ContMDiffOn I I n
      ((Subtype.val : ↑U → M) ∘ q) q.source :=
    hcsource.congr fun p hp ↦
      collaredCutSideOverlap_coe_apply C B hopen c hc hcollar hp
  intro p hp
  exact (contMDiffWithinAt_subtypeVal_comp_iff_of_order I n U q q.source p).mp
    (hambient p hp)

omit [Nonempty H] in
theorem contMDiffOn_collaredCutSideOverlap_symm_of_localDiffeomorphOn
    [IsManifold I n M] [IsManifold I n P]
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    [Nonempty P]
    [Nonempty ↑(collaredCutSideOffBoundaryOpens C B hopen)]
    (hlocal : IsLocalDiffeomorphOn I I n c
      (c ⁻¹' collaredCutSideOffBoundary C B)) :
    ContMDiffOn I I n
      (collaredCutSideOverlap C B hopen c hc hcollar).symm
      (collaredCutSideOverlap C B hopen c hc hcollar).target := by
  let U := collaredCutSideOffBoundaryOpens C B hopen
  let q := collaredCutSideOverlap C B hopen c hc hcollar
  have hcinj : Injective c := by
    intro a b hab
    apply hcollar.injective
    exact Subtype.ext hab
  intro y hy
  let p := q.symm y
  have hp : p ∈ q.source := q.symm.mapsTo hy
  have hp' : p ∈ c ⁻¹' collaredCutSideOffBoundary C B := by
    rw [← collaredCutSideOverlap_source C B hopen c hc hcollar]
    exact hp
  let hld : IsLocalDiffeomorphAt I I n c p := hlocal ⟨p, hp'⟩
  have hcpeqy : c p = y.1 :=
    collaredCutSideOverlap_symm_coe_apply C B hopen c hc hcollar hy
  have hval : ContMDiffAt I I n (Subtype.val : ↑U → M) y :=
    (contMDiff_subtype_val (I := I) (U := U)).contMDiffAt
  have hsmooth : ContMDiffAt I I n
      (hld.localInverse ∘ (Subtype.val : ↑U → M)) y :=
    hld.localInverse_contMDiffAt.comp_of_eq hval hcpeqy.symm
  have hyinv : y.1 ∈ hld.localInverse.source := by
    rw [← hcpeqy]
    exact hld.localInverse_mem_source
  have hevent : q.symm =ᶠ[𝓝 y]
      hld.localInverse ∘ (Subtype.val : ↑U → M) := by
    filter_upwards [
      (q.open_target.inter
        (hld.localInverse_open_source.preimage continuous_subtype_val)).mem_nhds
          ⟨hy, hyinv⟩] with z hz
    apply hcinj
    rw [collaredCutSideOverlap_symm_coe_apply C B hopen c hc hcollar hz.1]
    exact (hld.localInverse_right_inv hz.2).symm
  exact (hsmooth.congr_of_eventuallyEq hevent).contMDiffWithinAt

theorem collaredCutSideAtlasChart_compatible_of_overlap
    [IsManifold I n M] [IsManifold I n P]
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    [Nonempty P]
    [Nonempty ↑(collaredCutSideOffBoundaryOpens C B hopen)]
    (hoverlap : ContMDiffOn I I n
      (collaredCutSideOverlap C B hopen c hc hcollar)
      (collaredCutSideOverlap C B hopen c hc hcollar).source)
    (hoverlap' : ContMDiffOn I I n
      (collaredCutSideOverlap C B hopen c hc hcollar).symm
      (collaredCutSideOverlap C B hopen c hc hcollar).target) :
    ∀ i j : CollaredCutSideAtlasIndex C B P,
      (collaredCutSideAtlasChart (H := H)
        C B hopen c hc hcollar i).symm.trans
          (collaredCutSideAtlasChart (H := H)
            C B hopen c hc hcollar j) ∈
        contDiffGroupoid n I := by
  intro i j
  cases i with
  | native x =>
      cases j with
      | native y =>
          let xU : ↑(collaredCutSideOffBoundaryOpens C B hopen) :=
            ⟨x.1, x.2⟩
          let yU : ↑(collaredCutSideOffBoundaryOpens C B hopen) :=
            ⟨y.1, y.2⟩
          change
            ((chartAt H xU).lift_openEmbedding
              (isOpenEmbedding_collaredCutSideOffBoundaryOpensMap C B hopen)).symm.trans
                ((chartAt H yU).lift_openEmbedding
                  (isOpenEmbedding_collaredCutSideOffBoundaryOpensMap C B hopen)) ∈
              contDiffGroupoid n I
          rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
          exact (inferInstance : IsManifold I n
            ↑(collaredCutSideOffBoundaryOpens C B hopen)).compatible
              (chart_mem_atlas H xU) (chart_mem_atlas H yU)
      | collar p =>
          let U := collaredCutSideOffBoundaryOpens C B hopen
          let xU : ↑U :=
            ⟨x.1, x.2⟩
          let eU : OpenPartialHomeomorph ↑U H :=
            (chartAt H x.1).subtypeRestr ⟨xU⟩
          have hmap :
              (fun y : ↑U ↦ (⟨y.1, y.2.1⟩ : CollaredCutSide C)) =
                collaredCutSideOffBoundaryOpensMap C B hopen := by
            rfl
          have heU : eU ∈ IsManifold.maximalAtlas I n ↑U :=
            StructureGroupoid.subtypeRestr_mem_maximalAtlas
              (G := contDiffGroupoid n I)
              (chart_mem_atlas H x.1) ⟨xU⟩
          have hreverse :=
            maximalAtlas_symm_trans_openPartialHomeomorph_trans_maximalAtlas_mem_contDiffGroupoid
              I n (chartAt H p)
              ((contDiffGroupoid n I).chart_mem_maximalAtlas p)
              (collaredCutSideOverlap C B hopen c hc hcollar)
              hoverlap hoverlap' eU heU
          have heq := lift_openEmbedding_symm_trans_lift_openEmbedding
            (chartAt H p)
            eU
            hcollar
            (isOpenEmbedding_collaredCutSideOffBoundaryOpensMap C B hopen)
          have hdirect :
              (collaredCutSideCollarChart (H := H) C c hc hcollar p).symm.trans
                  (collaredCutSideNativeChart (H := H) C B hopen x) ∈
                contDiffGroupoid n I := by
            apply (contDiffGroupoid n I).mem_of_eqOnSource hreverse
            convert heq using 1
            all_goals
              ext z <;> simp [collaredCutSideCollarChart,
                collaredCutSideNativeChart,
                collaredCutSideOffBoundaryOpensMap,
                eU, U, hmap,
                collaredCutSideOverlap]
          have hs := (contDiffGroupoid n I).symm hdirect
          change
            (collaredCutSideNativeChart (H := H) C B hopen x).symm.trans
                (collaredCutSideCollarChart (H := H) C c hc hcollar p) ∈
              contDiffGroupoid n I
          change
            ((collaredCutSideCollarChart (H := H) C c hc hcollar p).symm.trans
              (collaredCutSideNativeChart (H := H) C B hopen x)).symm ∈
                contDiffGroupoid n I
          exact hs
  | collar p =>
      cases j with
      | native x =>
          let U := collaredCutSideOffBoundaryOpens C B hopen
          let xU : ↑U :=
            ⟨x.1, x.2⟩
          let eU : OpenPartialHomeomorph ↑U H :=
            (chartAt H x.1).subtypeRestr ⟨xU⟩
          have hmap :
              (fun y : ↑U ↦ (⟨y.1, y.2.1⟩ : CollaredCutSide C)) =
                collaredCutSideOffBoundaryOpensMap C B hopen := by
            rfl
          have heU : eU ∈ IsManifold.maximalAtlas I n ↑U :=
            StructureGroupoid.subtypeRestr_mem_maximalAtlas
              (G := contDiffGroupoid n I)
              (chart_mem_atlas H x.1) ⟨xU⟩
          have htransition :=
            maximalAtlas_symm_trans_openPartialHomeomorph_trans_maximalAtlas_mem_contDiffGroupoid
              I n (chartAt H p)
              ((contDiffGroupoid n I).chart_mem_maximalAtlas p)
              (collaredCutSideOverlap C B hopen c hc hcollar)
              hoverlap hoverlap' eU heU
          have heq := lift_openEmbedding_symm_trans_lift_openEmbedding
            (chartAt H p)
            eU
            hcollar
            (isOpenEmbedding_collaredCutSideOffBoundaryOpensMap C B hopen)
          change
            (collaredCutSideCollarChart (H := H) C c hc hcollar p).symm.trans
                (collaredCutSideNativeChart (H := H) C B hopen x) ∈
              contDiffGroupoid n I
          apply (contDiffGroupoid n I).mem_of_eqOnSource htransition
          convert heq using 1
          all_goals
            ext z <;> simp [collaredCutSideCollarChart,
              collaredCutSideNativeChart,
              collaredCutSideOffBoundaryOpensMap,
              eU, U, hmap,
              collaredCutSideOverlap]
      | collar q =>
          change
            ((chartAt H p).lift_openEmbedding hcollar).symm.trans
                ((chartAt H q).lift_openEmbedding hcollar) ∈
              contDiffGroupoid n I
          rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
          exact (inferInstance : IsManifold I n P).compatible
            (chart_mem_atlas H p) (chart_mem_atlas H q)

theorem collaredCutSideAtlasChart_compatible_of_localDiffeomorphOn_of_nonempty
    [IsManifold I n M] [IsManifold I n P]
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    [Nonempty P]
    [Nonempty ↑(collaredCutSideOffBoundaryOpens C B hopen)]
    (hlocal : IsLocalDiffeomorphOn I I n c
      (c ⁻¹' collaredCutSideOffBoundary C B)) :
    ∀ i j : CollaredCutSideAtlasIndex C B P,
      (collaredCutSideAtlasChart (H := H)
        C B hopen c hc hcollar i).symm.trans
          (collaredCutSideAtlasChart (H := H)
            C B hopen c hc hcollar j) ∈
        contDiffGroupoid n I :=
  collaredCutSideAtlasChart_compatible_of_overlap I n
    C B hopen c hc hcollar
      (contMDiffOn_collaredCutSideOverlap I n
        C B hopen c hc hcollar hlocal.contMDiffOn)
      (contMDiffOn_collaredCutSideOverlap_symm_of_localDiffeomorphOn I n
        C B hopen c hc hcollar hlocal)

theorem collaredCutSideAtlasChart_compatible_of_localDiffeomorphOn
    [IsManifold I n M] [IsManifold I n P]
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    (hlocal : IsLocalDiffeomorphOn I I n c
      (c ⁻¹' collaredCutSideOffBoundary C B)) :
    ∀ i j : CollaredCutSideAtlasIndex C B P,
      (collaredCutSideAtlasChart (H := H)
        C B hopen c hc hcollar i).symm.trans
          (collaredCutSideAtlasChart (H := H)
            C B hopen c hc hcollar j) ∈
        contDiffGroupoid n I := by
  intro i j
  cases i with
  | native x =>
      cases j with
      | native y =>
          let xU : ↑(collaredCutSideOffBoundaryOpens C B hopen) :=
            ⟨x.1, x.2⟩
          let yU : ↑(collaredCutSideOffBoundaryOpens C B hopen) :=
            ⟨y.1, y.2⟩
          change
            ((chartAt H xU).lift_openEmbedding
              (isOpenEmbedding_collaredCutSideOffBoundaryOpensMap C B hopen)).symm.trans
                ((chartAt H yU).lift_openEmbedding
                  (isOpenEmbedding_collaredCutSideOffBoundaryOpensMap C B hopen)) ∈
              contDiffGroupoid n I
          rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
          exact (inferInstance : IsManifold I n
            ↑(collaredCutSideOffBoundaryOpens C B hopen)).compatible
              (chart_mem_atlas H xU) (chart_mem_atlas H yU)
      | collar p =>
          let xU : ↑(collaredCutSideOffBoundaryOpens C B hopen) :=
            ⟨x.1, x.2⟩
          let _ : Nonempty P := ⟨p⟩
          let _ : Nonempty ↑(collaredCutSideOffBoundaryOpens C B hopen) := ⟨xU⟩
          exact collaredCutSideAtlasChart_compatible_of_localDiffeomorphOn_of_nonempty
            I n C B hopen c hc hcollar hlocal
              (CollaredCutSideAtlasIndex.native x)
              (CollaredCutSideAtlasIndex.collar p)
  | collar p =>
      cases j with
      | native x =>
          let xU : ↑(collaredCutSideOffBoundaryOpens C B hopen) :=
            ⟨x.1, x.2⟩
          let _ : Nonempty P := ⟨p⟩
          let _ : Nonempty ↑(collaredCutSideOffBoundaryOpens C B hopen) := ⟨xU⟩
          exact collaredCutSideAtlasChart_compatible_of_localDiffeomorphOn_of_nonempty
            I n C B hopen c hc hcollar hlocal
              (CollaredCutSideAtlasIndex.collar p)
              (CollaredCutSideAtlasIndex.native x)
      | collar q =>
          change
            ((chartAt H p).lift_openEmbedding hcollar).symm.trans
                ((chartAt H q).lift_openEmbedding hcollar) ∈
              contDiffGroupoid n I
          rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
          exact (inferInstance : IsManifold I n P).compatible
            (chart_mem_atlas H p) (chart_mem_atlas H q)

theorem contMDiffOn_collaredCutSideAtlasChart_symm_subtypeVal
    [IsManifold I n M] [IsManifold I n P]
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    (hcmooth : ContMDiff I I n c) :
    ∀ i : CollaredCutSideAtlasIndex C B P,
      ContMDiffOn I I n
        ((Subtype.val : CollaredCutSide C → M) ∘
          (collaredCutSideAtlasChart (H := H)
            C B hopen c hc hcollar i).symm)
        (collaredCutSideAtlasChart (H := H)
          C B hopen c hc hcollar i).target := by
  intro i
  cases i with
  | native x =>
      let U := collaredCutSideOffBoundaryOpens C B hopen
      let xU : ↑U := ⟨x.1, x.2⟩
      let eU : OpenPartialHomeomorph ↑U H :=
        (chartAt H x.1).subtypeRestr ⟨xU⟩
      have heU : eU ∈ IsManifold.maximalAtlas I n ↑U :=
        StructureGroupoid.subtypeRestr_mem_maximalAtlas
          (G := contDiffGroupoid n I)
          (chart_mem_atlas H x.1) ⟨xU⟩
      have hsmooth : ContMDiffOn I I n
          ((Subtype.val : ↑U → M) ∘ eU.symm) eU.target :=
        (contMDiff_subtype_val (I := I) (U := U)).comp_contMDiffOn
          (contMDiffOn_symm_of_mem_maximalAtlas heU)
      convert hsmooth using 1
      · funext z
        simp [collaredCutSideAtlasChart, collaredCutSideNativeChart,
          eU, U]
      · simp [collaredCutSideAtlasChart, collaredCutSideNativeChart,
          eU, U]
  | collar p =>
      have hsmooth : ContMDiffOn I I n
          (c ∘ (chartAt H p).symm) (chartAt H p).target :=
        hcmooth.comp_contMDiffOn contMDiffOn_chart_symm
      convert hsmooth using 1
      · funext z
        simp [collaredCutSideAtlasChart, collaredCutSideCollarChart]
      · simp [collaredCutSideAtlasChart, collaredCutSideCollarChart]

theorem isManifold_collaredCutSideChartedSpace_of_overlap
    [IsManifold I n M] [IsManifold I n P]
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    (hcover : ∀ z : CollaredCutSide C,
      z.1 ∈ collaredCutSideOffBoundary C B ∨ z.1 ∈ range c)
    [Nonempty P]
    [Nonempty ↑(collaredCutSideOffBoundaryOpens C B hopen)]
    (hoverlap : ContMDiffOn I I n
      (collaredCutSideOverlap C B hopen c hc hcollar)
      (collaredCutSideOverlap C B hopen c hc hcollar).source)
    (hoverlap' : ContMDiffOn I I n
      (collaredCutSideOverlap C B hopen c hc hcollar).symm
      (collaredCutSideOverlap C B hopen c hc hcollar).target) :
    letI := collaredCutSideChartedSpace (H := H)
      C B hopen c hc hcollar hcover
    IsManifold I n (CollaredCutSide C) :=
  isManifold_collaredCutSideChartedSpace I n
    C B hopen c hc hcollar hcover
      (collaredCutSideAtlasChart_compatible_of_overlap I n
        C B hopen c hc hcollar hoverlap hoverlap')

theorem contMDiff_collaredCutSideSubtypeVal_of_overlap
    [IsManifold I n M] [IsManifold I n P]
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    (hcover : ∀ z : CollaredCutSide C,
      z.1 ∈ collaredCutSideOffBoundary C B ∨ z.1 ∈ range c)
    [Nonempty P]
    [Nonempty ↑(collaredCutSideOffBoundaryOpens C B hopen)]
    (hoverlap : ContMDiffOn I I n
      (collaredCutSideOverlap C B hopen c hc hcollar)
      (collaredCutSideOverlap C B hopen c hc hcollar).source)
    (hoverlap' : ContMDiffOn I I n
      (collaredCutSideOverlap C B hopen c hc hcollar).symm
      (collaredCutSideOverlap C B hopen c hc hcollar).target)
    (hcmooth : ContMDiff I I n c) :
    letI := collaredCutSideChartedSpace (H := H)
      C B hopen c hc hcollar hcover
    ContMDiff I I n (Subtype.val : CollaredCutSide C → M) :=
  contMDiff_collaredCutSideSubtypeVal I n I
    C B hopen c hc hcollar hcover
      (collaredCutSideAtlasChart_compatible_of_overlap I n
        C B hopen c hc hcollar hoverlap hoverlap')
      (contMDiffOn_collaredCutSideAtlasChart_symm_subtypeVal I n
        C B hopen c hc hcollar hcmooth)

theorem isManifold_collaredCutSideChartedSpace_of_localDiffeomorphOn
    [IsManifold I n M] [IsManifold I n P]
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    (hcover : ∀ z : CollaredCutSide C,
      z.1 ∈ collaredCutSideOffBoundary C B ∨ z.1 ∈ range c)
    (hlocal : IsLocalDiffeomorphOn I I n c
      (c ⁻¹' collaredCutSideOffBoundary C B)) :
    letI := collaredCutSideChartedSpace (H := H)
      C B hopen c hc hcollar hcover
    IsManifold I n (CollaredCutSide C) :=
  isManifold_collaredCutSideChartedSpace I n
    C B hopen c hc hcollar hcover
      (collaredCutSideAtlasChart_compatible_of_localDiffeomorphOn I n
        C B hopen c hc hcollar hlocal)

theorem contMDiff_collaredCutSideSubtypeVal_of_localDiffeomorphOn
    [IsManifold I n M] [IsManifold I n P]
    (C B : Set M)
    (hopen : IsOpen (collaredCutSideOffBoundary C B))
    (c : P → M) (hc : range c ⊆ C)
    (hcollar : IsOpenEmbedding (collaredCutSideHalfCollarMap C c hc))
    (hcover : ∀ z : CollaredCutSide C,
      z.1 ∈ collaredCutSideOffBoundary C B ∨ z.1 ∈ range c)
    (hlocal : IsLocalDiffeomorphOn I I n c
      (c ⁻¹' collaredCutSideOffBoundary C B))
    (hcmooth : ContMDiff I I n c) :
    letI := collaredCutSideChartedSpace (H := H)
      C B hopen c hc hcollar hcover
    ContMDiff I I n (Subtype.val : CollaredCutSide C → M) :=
  contMDiff_collaredCutSideSubtypeVal I n I
    C B hopen c hc hcollar hcover
      (collaredCutSideAtlasChart_compatible_of_localDiffeomorphOn I n
        C B hopen c hc hcollar hlocal)
      (contMDiffOn_collaredCutSideAtlasChart_symm_subtypeVal I n
        C B hopen c hc hcollar hcmooth)

end Atlas

end SplittingSpheres
