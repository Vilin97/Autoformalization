/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import SplittingSpheres.Statement

/-!
# Smooth-embedding transport for splitting spheres

Mathlib's chart-normal-form definition of an immersion does not yet provide generic composition
of immersions or the theorem that a local diffeomorphism is an immersion.  This file proves the
same-model cases directly from transported maximal-atlas charts.  These cases include all source
and ambient self-diffeomorphisms of the standard spheres used in this project.

The resulting API bundles pre- and postcomposition by diffeomorphisms for
`TauCeti.SmoothEmbedding`, records exact range formulas, and supplies the constant jointly smooth
sphere isotopy.

No derivative criterion for immersions is assumed: the key proof constructs a `PUnit` complement
and verifies the required local normal form in charts.
-/

@[expose] public section

open Function Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace Manifold

universe uE

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H N]
  {n : ℕ∞ω}

/-- A partial diffeomorphism between manifolds with the same model is locally an immersion with
zero-dimensional complement. -/
theorem PartialDiffeomorph.isImmersionAtOfComplement
    [IsManifold I n M] [IsManifold I n N]
    (Φ : PartialDiffeomorph I I M N n) {x : M} (hx : x ∈ Φ.source) :
    IsImmersionAtOfComplement PUnit.{uE + 1} I I n Φ x := by
  let c : OpenPartialHomeomorph M H := (chartAt H x).restr Φ.source
  let d : OpenPartialHomeomorph N H := Φ.toOpenPartialHomeomorph.symm.trans c
  have hc_source : c.source ⊆ Φ.source := by
    intro z hz
    simp only [c, OpenPartialHomeomorph.restr_source, Φ.open_source.interior_eq,
      mem_inter_iff] at hz
    exact hz.2
  have hxc : x ∈ c.source := by
    simpa [c, Φ.open_source.interior_eq] using hx
  have hΦxd : Φ x ∈ d.source := by
    simp only [d, OpenPartialHomeomorph.trans_source, mem_inter_iff,
      OpenPartialHomeomorph.symm_source, mem_preimage]
    refine ⟨Φ.map_source hx, ?_⟩
    have hleft := Φ.toOpenPartialHomeomorph.left_inv hx
    have happ : Φ.toOpenPartialHomeomorph x = Φ x := by
      change Φ.toOpenPartialHomeomorph.toPartialEquiv x = Φ.toPartialEquiv x
      rw [PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv]
    rw [← happ]
    rw [hleft]
    exact hxc
  have hc_max : c ∈ IsManifold.maximalAtlas I n M := by
    exact restr_mem_maximalAtlas (contDiffGroupoid n I)
      (IsManifold.chart_mem_maximalAtlas x) Φ.open_source
  have hd_smooth : ContMDiffOn I I n d d.source := by
    rw [show (d : N → H) = c ∘ Φ.symm by rfl]
    apply (contMDiffOn_of_mem_maximalAtlas hc_max).comp
      (Φ.symm.contMDiffOn.mono ?_) ?_
    · intro z hz
      exact hz.1
    · intro z hz
      exact hz.2
  have hd_symm_smooth : ContMDiffOn I I n d.symm d.target := by
    rw [show (d.symm : H → N) = Φ ∘ c.symm by rfl]
    apply Φ.contMDiffOn.comp
      ((contMDiffOn_symm_of_mem_maximalAtlas hc_max).mono ?_) ?_
    · intro z hz
      exact hz.1
    · intro z hz
      exact hz.2
  have hd_max : d ∈ IsManifold.maximalAtlas I n N :=
    d.mem_maximalAtlas_of_contMDiffOn hd_smooth hd_symm_smooth
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (Φ.contMDiffOn.contMDiffAt (Φ.open_source.mem_nhds hx)).continuousAt
    (.prodUnique 𝕜 E PUnit.{uE + 1}) c d hxc hΦxd hc_max hd_max
  intro y hy
  dsimp only [Function.comp_apply]
  have hyI : I.symm y ∈ c.target := by
    change I.toPartialEquiv.invFun y ∈ c.target
    exact hy.2
  have hy_range : y ∈ range I := by
    simpa only [ModelWithCorners.target_eq] using hy.1
  have hcy : c.symm (I.symm y) ∈ c.source := c.symm.map_source hyI
  have hΦcy : c.symm (I.symm y) ∈ Φ.source := hc_source hcy
  have hd_left : d (Φ (c.symm (I.symm y))) = c (c.symm (I.symm y)) := by
    change c (Φ.symm (Φ (c.symm (I.symm y)))) = c (c.symm (I.symm y))
    exact congrArg c (Φ.left_inv hΦcy)
  have hc_right : c (c.symm (I.symm y)) = I.symm y := c.right_inv hyI
  rw [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm]
  change I (d (Φ (c.symm (I.symm y)))) = y
  rw [hd_left, hc_right, I.right_inv hy_range]

/-- A same-model local diffeomorphism is an immersion at every point of its local domain. -/
theorem IsLocalDiffeomorphAt.isImmersionAtOfComplement_sameModel
    [IsManifold I n M] [IsManifold I n N]
    {f : M → N} {x : M} (hf : IsLocalDiffeomorphAt I I n f x) :
    IsImmersionAtOfComplement PUnit.{uE + 1} I I n f x := by
  let Φ : PartialDiffeomorph I I M N n := hf.localInverse.symm
  have hΦx : x ∈ Φ.source := hf.localInverse_mem_target
  apply (Manifold.PartialDiffeomorph.isImmersionAtOfComplement Φ hΦx).congr_of_eventuallyEq
  filter_upwards
    [hf.localInverse.open_target.mem_nhds hf.localInverse_mem_target,
      hf.contMDiffAt.continuousAt.preimage_mem_nhds
        (hf.localInverse.open_source.mem_nhds hf.localInverse_mem_source),
      hf.localInverse_eventuallyEq_left]
    with y hyTarget hySource hyLeft
  change hf.localInverse.symm y = f y
  exact ((hf.localInverse.eq_symm_apply hySource hyTarget).2 hyLeft).symm

/-- A same-model local diffeomorphism has the zero-dimensional `PUnit` immersion complement. -/
theorem IsLocalDiffeomorph.isImmersionOfComplement_sameModel
    [IsManifold I n M] [IsManifold I n N]
    {f : M → N} (hf : IsLocalDiffeomorph I I n f) :
    IsImmersionOfComplement PUnit.{uE + 1} I I n f :=
  fun x => Manifold.IsLocalDiffeomorphAt.isImmersionAtOfComplement_sameModel (hf x)

/-- A same-model local diffeomorphism is an immersion. -/
theorem IsLocalDiffeomorph.isImmersion_sameModel
    [IsManifold I n M] [IsManifold I n N]
    {f : M → N} (hf : IsLocalDiffeomorph I I n f) :
    IsImmersion I I n f :=
  (Manifold.IsLocalDiffeomorph.isImmersionOfComplement_sameModel hf).isImmersion

/-- A diffeomorphism between manifolds with the same model is a smooth embedding. -/
theorem Diffeomorph.isSmoothEmbedding_sameModel
    [IsManifold I n M] [IsManifold I n N]
    (e : M ≃ₘ^n⟮I, I⟯ N) : IsSmoothEmbedding I I n e where
  isImmersion := Manifold.IsLocalDiffeomorph.isImmersion_sameModel e.isLocalDiffeomorph
  isEmbedding := e.toHomeomorph.isEmbedding

/-- Pulling a maximal-atlas chart back along a same-model diffeomorphism gives another
maximal-atlas chart. -/
theorem Diffeomorph.symm_trans_mem_maximalAtlas
    [IsManifold I n M] [IsManifold I n N]
    (e : M ≃ₘ^n⟮I, I⟯ N) (c : OpenPartialHomeomorph M H)
    (hc : c ∈ IsManifold.maximalAtlas I n M) :
    e.toHomeomorph.toOpenPartialHomeomorph.symm.trans c ∈
      IsManifold.maximalAtlas I n N := by
  let d : OpenPartialHomeomorph N H :=
    e.toHomeomorph.toOpenPartialHomeomorph.symm.trans c
  apply d.mem_maximalAtlas_of_contMDiffOn
  · rw [show (d : N → H) = c ∘ e.symm by rfl]
    apply (contMDiffOn_of_mem_maximalAtlas hc).comp
      (e.symm.contMDiff.contMDiffOn (s := d.source))
    intro z hz
    simp only [d, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source,
      Homeomorph.toOpenPartialHomeomorph_target, univ_inter] at hz
    have hz' := hz
    rw [← e.toHomeomorph.symm_toOpenPartialHomeomorph,
      Homeomorph.toOpenPartialHomeomorph_apply] at hz'
    exact hz'
  · rw [show (d.symm : H → N) = e ∘ c.symm by rfl]
    have hc_symm : ContMDiffOn I I n c.symm d.target :=
      (contMDiffOn_symm_of_mem_maximalAtlas hc).mono (by
        intro z hz
        simpa only [d, OpenPartialHomeomorph.trans_target,
          OpenPartialHomeomorph.symm_target,
          Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ] using hz)
    exact (e.contMDiff.contMDiffOn (s := univ)).comp hc_symm (by simp)

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'}
  {Q R : Type*} [TopologicalSpace Q] [ChartedSpace H' Q]
    [TopologicalSpace R] [ChartedSpace H' R]
  {f : M → Q}

/-- Postcomposition by a same-model diffeomorphism preserves the local immersion normal form. -/
theorem IsImmersionAtOfComplement.postcomp_diffeomorph
    [IsManifold I n M] [IsManifold J n Q] [IsManifold J n R]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (hf : IsImmersionAtOfComplement F I J n f x)
    (e : Q ≃ₘ^n⟮J, J⟯ R) :
    IsImmersionAtOfComplement F I J n (e ∘ f) x := by
  let d : OpenPartialHomeomorph R H' :=
    e.toHomeomorph.toOpenPartialHomeomorph.symm.trans hf.codChart
  have hfxd : e (f x) ∈ d.source := by
    simp only [d, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Homeomorph.toOpenPartialHomeomorph_target,
      univ_inter, mem_preimage]
    simpa using hf.mem_codChart_source
  have hd_max : d ∈ IsManifold.maximalAtlas J n R :=
    Diffeomorph.symm_trans_mem_maximalAtlas e hf.codChart hf.codChart_mem_maximalAtlas
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (e.continuous.continuousAt.comp hf.continuousAt) hf.equiv hf.domChart d
    hf.mem_domChart_source hfxd hf.domChart_mem_maximalAtlas hd_max
  intro y hy
  have hbase := hf.writtenInCharts hy
  rw [OpenPartialHomeomorph.extend_coe] at hbase ⊢
  change J (d (e (f ((hf.domChart.extend I).symm y)))) = _
  change J (hf.codChart (e.symm (e (f ((hf.domChart.extend I).symm y))))) = _
  rw [e.symm_apply_apply]
  exact hbase

/-- Postcomposition by a same-model diffeomorphism preserves a global chosen complement. -/
theorem IsImmersionOfComplement.postcomp_diffeomorph
    [IsManifold I n M] [IsManifold J n Q] [IsManifold J n R]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (hf : IsImmersionOfComplement F I J n f)
    (e : Q ≃ₘ^n⟮J, J⟯ R) :
    IsImmersionOfComplement F I J n (e ∘ f) :=
  fun x => (hf x).postcomp_diffeomorph e

/-- Postcomposition by a same-model diffeomorphism preserves immersions. -/
theorem IsImmersion.postcomp_diffeomorph
    [IsManifold I n M] [IsManifold J n Q] [IsManifold J n R]
    (hf : IsImmersion I J n f) (e : Q ≃ₘ^n⟮J, J⟯ R) :
    IsImmersion I J n (e ∘ f) :=
  (hf.isImmersionOfComplement_complement.postcomp_diffeomorph e).isImmersion

/-- Precomposition by a same-model diffeomorphism preserves the local immersion normal form. -/
theorem IsImmersionAtOfComplement.precomp_diffeomorph
    [IsManifold I n N] [IsManifold I n M] [IsManifold J n Q]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {e : N ≃ₘ^n⟮I, I⟯ M} {x : N}
    (hf : IsImmersionAtOfComplement F I J n f (e x)) :
    IsImmersionAtOfComplement F I J n (f ∘ e) x := by
  let c : OpenPartialHomeomorph N H :=
    e.toHomeomorph.toOpenPartialHomeomorph.trans hf.domChart
  have hxc : x ∈ c.source := by
    simp only [c, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, univ_inter, mem_preimage,
      Homeomorph.toOpenPartialHomeomorph_apply]
    exact hf.mem_domChart_source
  have hc_max : c ∈ IsManifold.maximalAtlas I n N := by
    have := Diffeomorph.symm_trans_mem_maximalAtlas e.symm hf.domChart
      hf.domChart_mem_maximalAtlas
    simpa only [Diffeomorph.symm_toHomeomorph,
      Homeomorph.symm_toOpenPartialHomeomorph,
      OpenPartialHomeomorph.symm_symm] using this
  have hc_target : c.target = hf.domChart.target := by
    simp only [c, OpenPartialHomeomorph.trans_target,
      Homeomorph.toOpenPartialHomeomorph_target,
      preimage_univ, inter_univ]
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (hf.continuousAt.comp e.continuous.continuousAt) hf.equiv c hf.codChart
    hxc hf.mem_codChart_source hc_max hf.codChart_mem_maximalAtlas
  intro y hy
  have hy' : y ∈ (hf.domChart.extend I).target := by
    rw [OpenPartialHomeomorph.extend_target] at hy ⊢
    rwa [hc_target] at hy
  have hbase := hf.writtenInCharts hy'
  rw [OpenPartialHomeomorph.extend_coe_symm] at hbase ⊢
  change (hf.codChart.extend J)
    (f (e (c.symm (I.symm y)))) = _
  change (hf.codChart.extend J)
    (f (e (e.symm (hf.domChart.symm (I.symm y))))) = _
  rw [e.apply_symm_apply]
  exact hbase

/-- Precomposition by a same-model diffeomorphism preserves a global chosen complement. -/
theorem IsImmersionOfComplement.precomp_diffeomorph
    [IsManifold I n N] [IsManifold I n M] [IsManifold J n Q]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (hf : IsImmersionOfComplement F I J n f) (e : N ≃ₘ^n⟮I, I⟯ M) :
    IsImmersionOfComplement F I J n (f ∘ e) :=
  fun x => (hf (e x)).precomp_diffeomorph

/-- Precomposition by a same-model diffeomorphism preserves immersions. -/
theorem IsImmersion.precomp_diffeomorph
    [IsManifold I n N] [IsManifold I n M] [IsManifold J n Q]
    (hf : IsImmersion I J n f) (e : N ≃ₘ^n⟮I, I⟯ M) :
    IsImmersion I J n (f ∘ e) :=
  (hf.isImmersionOfComplement_complement.precomp_diffeomorph e).isImmersion

/-- Postcomposition by a same-model diffeomorphism preserves smooth embeddings. -/
theorem IsSmoothEmbedding.postcomp_diffeomorph
    [IsManifold I n M] [IsManifold J n Q] [IsManifold J n R]
    (hf : IsSmoothEmbedding I J n f) (e : Q ≃ₘ^n⟮J, J⟯ R) :
    IsSmoothEmbedding I J n (e ∘ f) where
  isImmersion := hf.isImmersion.postcomp_diffeomorph e
  isEmbedding := e.toHomeomorph.isEmbedding.comp hf.isEmbedding

/-- Precomposition by a same-model diffeomorphism preserves smooth embeddings. -/
theorem IsSmoothEmbedding.precomp_diffeomorph
    [IsManifold I n N] [IsManifold I n M] [IsManifold J n Q]
    (hf : IsSmoothEmbedding I J n f) (e : N ≃ₘ^n⟮I, I⟯ M) :
    IsSmoothEmbedding I J n (f ∘ e) where
  isImmersion := hf.isImmersion.precomp_diffeomorph e
  isEmbedding := hf.isEmbedding.comp e.toHomeomorph.isEmbedding

end Manifold

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {L M : Type*} [TopologicalSpace L] [ChartedSpace H L]
    [TopologicalSpace M] [ChartedSpace H M]
  {N P : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    [TopologicalSpace P] [ChartedSpace H' P]
  {n : ℕ∞ω}

/-- Regard a diffeomorphism between manifolds with the same model as a bundled smooth embedding. -/
def ofDiffeomorph [IsManifold I n L] [IsManifold I n M]
    (e : L ≃ₘ^n⟮I, I⟯ M) : TauCeti.SmoothEmbedding I I n L M :=
  .ofIsSmoothEmbedding e (Manifold.Diffeomorph.isSmoothEmbedding_sameModel e)

@[simp]
theorem ofDiffeomorph_apply [IsManifold I n L] [IsManifold I n M]
    (e : L ≃ₘ^n⟮I, I⟯ M) (x : L) : ofDiffeomorph e x = e x := by
  exact ofIsSmoothEmbedding_apply e (Manifold.Diffeomorph.isSmoothEmbedding_sameModel e) x

@[simp]
theorem ofDiffeomorph_coe [IsManifold I n L] [IsManifold I n M]
    (e : L ≃ₘ^n⟮I, I⟯ M) : ⇑(ofDiffeomorph e) = e := by
  funext x
  exact ofDiffeomorph_apply e x

/-- Postcompose a bundled smooth embedding by a same-model diffeomorphism. -/
def postcompDiffeomorph [IsManifold I n M] [IsManifold J n N] [IsManifold J n P]
    (f : TauCeti.SmoothEmbedding I J n M N) (e : N ≃ₘ^n⟮J, J⟯ P) :
    TauCeti.SmoothEmbedding I J n M P :=
  .ofIsSmoothEmbedding (e ∘ f)
    (Manifold.IsSmoothEmbedding.postcomp_diffeomorph f.isSmoothEmbedding e)

@[simp]
theorem postcompDiffeomorph_apply
    [IsManifold I n M] [IsManifold J n N] [IsManifold J n P]
    (f : TauCeti.SmoothEmbedding I J n M N) (e : N ≃ₘ^n⟮J, J⟯ P) (x : M) :
    postcompDiffeomorph f e x = e (f x) := by
  exact ofIsSmoothEmbedding_apply (e ∘ f)
    (Manifold.IsSmoothEmbedding.postcomp_diffeomorph f.isSmoothEmbedding e) x

@[simp]
theorem postcompDiffeomorph_coe
    [IsManifold I n M] [IsManifold J n N] [IsManifold J n P]
    (f : TauCeti.SmoothEmbedding I J n M N) (e : N ≃ₘ^n⟮J, J⟯ P) :
    ⇑(postcompDiffeomorph f e) = e ∘ f := by
  funext x
  exact postcompDiffeomorph_apply f e x

/-- The range of a postcomposition is the image of the original range. -/
theorem range_postcompDiffeomorph
    [IsManifold I n M] [IsManifold J n N] [IsManifold J n P]
    (f : TauCeti.SmoothEmbedding I J n M N) (e : N ≃ₘ^n⟮J, J⟯ P) :
    range (postcompDiffeomorph f e) = e '' range f := by
  rw [postcompDiffeomorph_coe, Set.range_comp]

/-- Equivalently, the range after postcomposition is the inverse image of the old range under the
inverse diffeomorphism. -/
theorem range_postcompDiffeomorph_eq_preimage
    [IsManifold I n M] [IsManifold J n N] [IsManifold J n P]
    (f : TauCeti.SmoothEmbedding I J n M N) (e : N ≃ₘ^n⟮J, J⟯ P) :
    range (postcompDiffeomorph f e) = e.symm ⁻¹' range f := by
  rw [postcompDiffeomorph_coe]
  exact e.range_comp f

/-- Precompose a bundled smooth embedding by a same-model diffeomorphism. -/
def precompDiffeomorph [IsManifold I n L] [IsManifold I n M] [IsManifold J n N]
    (f : TauCeti.SmoothEmbedding I J n M N) (e : L ≃ₘ^n⟮I, I⟯ M) :
    TauCeti.SmoothEmbedding I J n L N :=
  .ofIsSmoothEmbedding (f ∘ e)
    (Manifold.IsSmoothEmbedding.precomp_diffeomorph f.isSmoothEmbedding e)

@[simp]
theorem precompDiffeomorph_apply
    [IsManifold I n L] [IsManifold I n M] [IsManifold J n N]
    (f : TauCeti.SmoothEmbedding I J n M N) (e : L ≃ₘ^n⟮I, I⟯ M) (x : L) :
    precompDiffeomorph f e x = f (e x) := by
  exact ofIsSmoothEmbedding_apply (f ∘ e)
    (Manifold.IsSmoothEmbedding.precomp_diffeomorph f.isSmoothEmbedding e) x

@[simp]
theorem precompDiffeomorph_coe
    [IsManifold I n L] [IsManifold I n M] [IsManifold J n N]
    (f : TauCeti.SmoothEmbedding I J n M N) (e : L ≃ₘ^n⟮I, I⟯ M) :
    ⇑(precompDiffeomorph f e) = f ∘ e := by
  funext x
  exact precompDiffeomorph_apply f e x

/-- Precomposition by a diffeomorphism does not change the range. -/
@[simp]
theorem range_precompDiffeomorph
    [IsManifold I n L] [IsManifold I n M] [IsManifold J n N]
    (f : TauCeti.SmoothEmbedding I J n M N) (e : L ≃ₘ^n⟮I, I⟯ M) :
    range (precompDiffeomorph f e) = range f := by
  rw [precompDiffeomorph_coe]
  exact e.surjective.range_comp f

end TauCeti.SmoothEmbedding

namespace SplittingSpheres

/-- The constant smooth isotopy of an embedded `3`-sphere. -/
def SmoothSphereIsotopy.refl (S : SmoothSphereEmbedding 3 4) :
    SmoothSphereIsotopy S S where
  toFun := fun p => S p.2
  contMDiff_toFun := S.contMDiff.comp contMDiff_snd
  isSmoothEmbedding_slice := fun _ => S.isSmoothEmbedding
  range_zero := rfl
  range_one := rfl

/-- A sphere disjoint from the unlink carrier is isotopic to itself in the complement. -/
theorem smoothlyIsotopicInComplement_refl_of_disjoint
    {S : SmoothSphereEmbedding 3 4}
    (hS : Disjoint (range S) standardUnlinkCarrier) :
    SmoothlyIsotopicInComplement S S := by
  refine ⟨SmoothSphereIsotopy.refl S, ?_⟩
  rintro ⟨t, x⟩ hx
  exact Set.disjoint_left.mp hS (mem_range_self x) hx

/-- Smooth isotopy in the complement is reflexive on splitting spheres. -/
theorem smoothlyIsotopicInComplement_refl
    {S : SmoothSphereEmbedding 3 4} (hS : IsSplittingSphere S) :
    SmoothlyIsotopicInComplement S S :=
  smoothlyIsotopicInComplement_refl_of_disjoint (by
    simpa only [standardUnlinkCarrier] using hS.1)

end SplittingSpheres
