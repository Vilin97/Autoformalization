/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# Smoothness detected through a local diffeomorphism

A continuous map into the source of a local diffeomorphism is smooth whenever its composite
with that local diffeomorphism is smooth.  Locally, the original map is the smooth local inverse
composed with its projection.

This elementary result is useful for lifts into covering spaces equipped with the atlas pulled
back from the base.  Continuity is essential: it ensures that the lift remains in the selected
local sheet near the point under consideration.

The same local-inverse argument reflects the chart-normal-form definition of an immersion, and
hence reflects smooth embeddings.  The latter result is stated for local diffeomorphisms whose
source and target use the same model; this is exactly the situation for a smooth covering map.
-/

@[expose] public section

open Function Filter Set Topology
open scoped ContDiff Manifold

namespace SplittingSpheres

universe uM uE uX uH uH' uH''

variable {EModel : Type*} [NormedAddCommGroup EModel] [NormedSpace ℝ EModel]
variable {FModel : Type*} [NormedAddCommGroup FModel] [NormedSpace ℝ FModel]
variable {GModel : Type*} [NormedAddCommGroup GModel] [NormedSpace ℝ GModel]
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {E : Type uE} [TopologicalSpace E] [ChartedSpace H' E]
variable {X : Type uX} [TopologicalSpace X] [ChartedSpace H'' X]
variable (IM : ModelWithCorners ℝ EModel H)
variable (IE : ModelWithCorners ℝ FModel H')
variable (IX : ModelWithCorners ℝ GModel H'')
variable {n : ℕ∞ω}

/-- A continuous local lift of a smooth map through a local diffeomorphism is smooth at the
chosen point. -/
theorem contMDiffAt_of_comp_isLocalDiffeomorphAt
    {p : E → X} {f : M → E} {x : M}
    (hp : IsLocalDiffeomorphAt IE IX n p (f x))
    (hf : ContinuousAt f x)
    (hpf : ContMDiffAt IM IX n (p ∘ f) x) :
    ContMDiffAt IM IE n f x := by
  have hsmooth : ContMDiffAt IM IE n
      (hp.localInverse ∘ (p ∘ f)) x :=
    hp.localInverse_contMDiffAt.comp x hpf
  apply hsmooth.congr_of_eventuallyEq
  filter_upwards [hf.eventually
    (hp.localInverse.open_target.mem_nhds hp.localInverse_mem_target)] with y hy
  exact (hp.localInverse_left_inv hy).symm

/-- A continuous lift through a local diffeomorphism is smooth if its projection is smooth. -/
theorem contMDiff_of_comp_isLocalDiffeomorph
    {p : E → X} {f : M → E}
    (hp : IsLocalDiffeomorph IE IX n p)
    (hf : Continuous f)
    (hpf : ContMDiff IM IX n (p ∘ f)) :
    ContMDiff IM IE n f := by
  intro x
  exact contMDiffAt_of_comp_isLocalDiffeomorphAt IM IE IX
    (hp (f x)) hf.continuousAt (hpf x)

end SplittingSpheres

namespace Manifold

universe uE

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EModel : Type uE} [NormedAddCommGroup EModel] [NormedSpace 𝕜 EModel]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 EModel H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω}

variable {FModel : Type*} [NormedAddCommGroup FModel] [NormedSpace 𝕜 FModel]
  {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 FModel H'}
  {Q R : Type*} [TopologicalSpace Q] [ChartedSpace H' Q]
    [TopologicalSpace R] [ChartedSpace H' R]

/-- Pulling a maximal-atlas chart back along a partial diffeomorphism whose source and target
have the same manifold model again gives a maximal-atlas chart. -/
theorem PartialDiffeomorph.symm_trans_mem_maximalAtlas
    [IsManifold J n Q] [IsManifold J n R]
    (e : PartialDiffeomorph J J Q R n)
    (c : OpenPartialHomeomorph Q H')
    (hc : c ∈ IsManifold.maximalAtlas J n Q) :
    e.toOpenPartialHomeomorph.symm.trans c ∈ IsManifold.maximalAtlas J n R := by
  let d : OpenPartialHomeomorph R H' :=
    e.toOpenPartialHomeomorph.symm.trans c
  apply d.mem_maximalAtlas_of_contMDiffOn
  · rw [show (d : R → H') = c ∘ e.symm by rfl]
    apply (contMDiffOn_of_mem_maximalAtlas hc).comp
      (e.symm.contMDiffOn.mono ?_) ?_
    · intro z hz
      exact hz.1
    · intro z hz
      exact hz.2
  · rw [show (d.symm : H' → R) = e ∘ c.symm by rfl]
    apply e.contMDiffOn.comp
      ((contMDiffOn_symm_of_mem_maximalAtlas hc).mono ?_) ?_
    · intro z hz
      exact hz.1
    · intro z hz
      exact hz.2

/-- Postcomposition by a same-model partial diffeomorphism preserves an immersion normal form at
any point whose image lies in the partial diffeomorphism's source. -/
theorem IsImmersionAtOfComplement.postcomp_partialDiffeomorph
    [IsManifold I n M] [IsManifold J n Q] [IsManifold J n R]
    {Complement : Type*} [NormedAddCommGroup Complement] [NormedSpace 𝕜 Complement]
    {f : M → Q} {x : M}
    (hf : IsImmersionAtOfComplement Complement I J n f x)
    (e : PartialDiffeomorph J J Q R n) (hfx : f x ∈ e.source) :
    IsImmersionAtOfComplement Complement I J n (e ∘ f) x := by
  obtain ⟨U, hU, hUopen, hxU⟩ := mem_nhds_iff.mp <|
    hf.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hfx)
  let c : OpenPartialHomeomorph M H := hf.domChart.restr U
  let d : OpenPartialHomeomorph R H' :=
    e.toOpenPartialHomeomorph.symm.trans hf.codChart
  have hxc : x ∈ c.source := by
    simp only [c, OpenPartialHomeomorph.restr_source, hUopen.interior_eq,
      mem_inter_iff]
    exact ⟨hf.mem_domChart_source, hxU⟩
  have hefxd : e (f x) ∈ d.source := by
    simp only [d, OpenPartialHomeomorph.trans_source, mem_inter_iff,
      OpenPartialHomeomorph.symm_source, mem_preimage]
    refine ⟨e.map_source hfx, ?_⟩
    have happ : e.toOpenPartialHomeomorph (f x) = e (f x) := by
      change e.toOpenPartialHomeomorph.toPartialEquiv (f x) = e.toPartialEquiv (f x)
      rw [PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv]
    rw [← happ, e.toOpenPartialHomeomorph.left_inv hfx]
    exact hf.mem_codChart_source
  have hcmax : c ∈ IsManifold.maximalAtlas I n M :=
    restr_mem_maximalAtlas (contDiffGroupoid n I)
      hf.domChart_mem_maximalAtlas hUopen
  have hdmax : d ∈ IsManifold.maximalAtlas J n R :=
    PartialDiffeomorph.symm_trans_mem_maximalAtlas
      e hf.codChart hf.codChart_mem_maximalAtlas
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    ((e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hfx)).continuousAt.comp
      hf.continuousAt)
    hf.equiv c d hxc hefxd hcmax hdmax
  intro y hy
  have hyOld : y ∈ (hf.domChart.extend I).target := by
    rw [c.extend_target] at hy
    rw [hf.domChart.extend_target]
    refine ⟨?_, hy.2⟩
    change I.symm y ∈ hf.domChart.target
    exact hy.1.1
  have hbase := hf.writtenInCharts hyOld
  have hyI : I.symm y ∈ c.target := by
    change I.toPartialEquiv.invFun y ∈ c.target
    exact hy.2
  have hcy : c.symm (I.symm y) ∈ c.source := c.symm.map_source hyI
  have hfy : f (c.symm (I.symm y)) ∈ e.source := by
    apply hU
    simpa only [hUopen.interior_eq] using hcy.2
  rw [OpenPartialHomeomorph.extend_coe] at hbase ⊢
  change J (d (e (f (c.symm (I.symm y))))) = _
  change J (hf.codChart (e.toOpenPartialHomeomorph.symm
    (e.toOpenPartialHomeomorph (f (c.symm (I.symm y)))))) = _
  rw [e.toOpenPartialHomeomorph.left_inv hfy]
  exact hbase

/-- A continuous map is an immersion if its composite with a same-model local diffeomorphism is
an immersion.  Continuity is necessary to prevent the map from jumping between local sheets. -/
theorem IsImmersion.reflect_isLocalDiffeomorph
    [IsManifold I n M] [IsManifold J n Q] [IsManifold J n R]
    {p : Q → R} {f : M → Q}
    (hp : IsLocalDiffeomorph J J n p)
    (hf : Continuous f)
    (hpf : IsImmersion I J n (p ∘ f)) :
    IsImmersion I J n f := by
  refine (show IsImmersionOfComplement hpf.complement I J n f from ?_).isImmersion
  intro x
  let hpx := hp (f x)
  have hpost : IsImmersionAtOfComplement hpf.complement I J n
      (hpx.localInverse ∘ (p ∘ f)) x :=
    IsImmersionAtOfComplement.postcomp_partialDiffeomorph
      (hpf.isImmersionOfComplement_complement x) hpx.localInverse
      hpx.localInverse_mem_source
  apply hpost.congr_of_eventuallyEq
  filter_upwards [hpx.localInverse_eventuallyEq_left.comp_tendsto
    hf.continuousAt] with y hy
  simpa only [Function.comp_apply, id_eq] using hy

/-- A continuous map is a smooth embedding if its composite with a same-model local
diffeomorphism is a smooth embedding.  This applies in particular to smooth covering maps. -/
theorem IsSmoothEmbedding.reflect_isLocalDiffeomorph
    [IsManifold I n M] [IsManifold J n Q] [IsManifold J n R]
    {p : Q → R} {f : M → Q}
    (hp : IsLocalDiffeomorph J J n p)
    (hf : Continuous f)
    (hpf : IsSmoothEmbedding I J n (p ∘ f)) :
    IsSmoothEmbedding I J n f where
  isImmersion := hpf.isImmersion.reflect_isLocalDiffeomorph hp hf
  isEmbedding := IsEmbedding.of_comp hf hp.contMDiff.continuous hpf.isEmbedding

end Manifold
