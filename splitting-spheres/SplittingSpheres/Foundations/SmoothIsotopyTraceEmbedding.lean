/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothIsotopyRealTimeExtension
public import SplittingSpheres.Foundations.SplitDerivativeImmersion
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Smooth embedding of the real-time isotopy trace

For a smooth sphere isotopy with flattened endpoints, this file studies its time-preserving
real-time trace, sending (t, x) to (t, H.flattenedRealTime (t, x)).

The topological embedding follows from slice injectivity and properness of the time projection.
The main point is immersion. The derivative of the trace is injective because its first component
remembers the time velocity and its restriction to each spatial tangent space is the derivative of
a slice embedding. In finite dimension and codimension one, that derivative extends to a
continuous linear equivalence after adjoining ℝ. A localized split-derivative inverse-function
argument then supplies the required manifold immersion normal form.
-/

@[expose] public section


open Function Set
open scoped ContDiff Manifold Topology unitInterval

noncomputable section

namespace SplittingSpheres

variable {E F C : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [CompleteSpace C]

/-- A local smooth representative suffices for the split-derivative immersion criterion. -/
theorem isImmersionAtOfComplement_of_contDiffOn_hasFDerivAt_split
    (T : E → F) (L : (E × C) ≃L[ℝ] F) (a : E)
    (s : Set E) (hs : IsOpen s) (ha : a ∈ s)
    (hT : ContDiffOn ℝ ∞ T s)
    (hder : HasFDerivAt T
      ((ContinuousLinearEquiv.toContinuousLinearMap L).comp
        (ContinuousLinearMap.inl ℝ E C)) a) :
    Manifold.IsImmersionAtOfComplement C (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ F) ∞ T a := by
  obtain ⟨φ, hφsupp, -, hφsmooth, -, hφa⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hs.mem_nhds ha)
  let ψ : E → ℝ := fun z ↦ Real.smoothTransition (4 * φ z - 2)
  have hψsmooth : ContDiff ℝ ∞ ψ := by
    exact Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul hφsmooth).sub contDiff_const)
  let Text : E → F := fun z ↦ ψ z • T z
  have hText : ContDiff ℝ ∞ Text := by
    rw [contDiff_infty]
    intro n
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ s
    · exact (hψsmooth.of_le (by simp)).contDiffAt.smul
        ((hT.of_le (by simp)).contDiffAt (hs.mem_nhds hz))
    · have hzsupport : z ∉ tsupport φ := fun hz' ↦ hz (hφsupp hz')
      have hφzero : Filter.EventuallyEq (nhds z) φ 0 :=
        notMem_tsupport_iff_eventuallyEq.mp hzsupport
      have hTextzero : Filter.EventuallyEq (nhds z) Text 0 := by
        filter_upwards [hφzero] with y hy
        simp only [Text, ψ, hy, Pi.zero_apply]
        norm_num [Real.smoothTransition.zero_of_nonpos]
      exact (contDiffAt_const (x := z) (c := (0 : F))).congr_of_eventuallyEq hTextzero
  have hψone : Filter.EventuallyEq (nhds a) ψ 1 := by
    have hφgt : ∀ᶠ z in nhds a, (3 / 4 : ℝ) < φ z :=
      hφsmooth.continuous.continuousAt
        (isOpen_Ioi.mem_nhds (by norm_num [hφa]))
    filter_upwards [hφgt] with z hz
    change Real.smoothTransition (4 * φ z - 2) = 1
    exact Real.smoothTransition.one_of_one_le (by linarith)
  have hTextEq : Filter.EventuallyEq (nhds a) Text T := by
    filter_upwards [hψone] with z hz
    simp [Text, hz]
  exact (isImmersionAtOfComplement_of_contDiff_hasFDerivAt_split
    Text L a hText (hder.congr_of_eventuallyEq hTextEq) (by simp)).congr_of_eventuallyEq hTextEq

section Transport

variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
  [IsManifold (modelWithCornersSelf ℝ F) ∞ N]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [CompleteSpace C] in
theorem isImmersionAtOfComplement_of_writtenInExtChartAt
    {f : M → N} {x : M} (hf : ContinuousAt f x)
    (h : Manifold.IsImmersionAtOfComplement C
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) ∞
      (writtenInExtChartAt (modelWithCornersSelf ℝ E)
        (modelWithCornersSelf ℝ F) x f)
      ((extChartAt (modelWithCornersSelf ℝ E) x) x)) :
    Manifold.IsImmersionAtOfComplement C
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) ∞ f x := by
  let c₀ : OpenPartialHomeomorph M E := chartAt E x
  let d₀ : OpenPartialHomeomorph N F := chartAt F (f x)
  let c : OpenPartialHomeomorph M E := c₀.trans h.domChart
  let d : OpenPartialHomeomorph N F := d₀.trans h.codChart
  have hxc₀ : x ∈ c₀.source := mem_chart_source E x
  have hfxd₀ : f x ∈ d₀.source := mem_chart_source F (f x)
  have hcoordx : c₀ x = (extChartAt (modelWithCornersSelf ℝ E) x) x := by
    rfl
  have hxc : x ∈ c.source := by
    change x ∈ (c₀.trans h.domChart).source
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨hxc₀, ?_⟩
    change c₀ x ∈ h.domChart.source
    rw [hcoordx]
    exact h.mem_domChart_source
  have hfd : f x ∈ d.source := by
    change f x ∈ (d₀.trans h.codChart).source
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨hfxd₀, ?_⟩
    have : d₀ (f x) =
        writtenInExtChartAt (modelWithCornersSelf ℝ E)
          (modelWithCornersSelf ℝ F) x f
          ((extChartAt (modelWithCornersSelf ℝ E) x) x) := by
      simp only [writtenInExtChartAt, Function.comp_apply]
      rw [(extChartAt (modelWithCornersSelf ℝ E) x).left_inv]
      · rfl
      · exact mem_extChartAt_source x
    change d₀ (f x) ∈ h.codChart.source
    rw [this]
    exact h.mem_codChart_source
  have hcmax : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M := by
    apply c.mem_maximalAtlas_of_contMDiffOn
    · have h₀ : ContMDiffOn (modelWithCornersSelf ℝ E)
          (modelWithCornersSelf ℝ E) ∞ c₀ c₀.source :=
        contMDiffOn_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
      have h₁ := contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
      change ContMDiffOn (modelWithCornersSelf ℝ E)
        (modelWithCornersSelf ℝ E) ∞ (h.domChart ∘ c₀)
          (c₀.source ∩ c₀ ⁻¹' h.domChart.source)
      exact h₁.comp' h₀
    · have h₀ : ContMDiffOn (modelWithCornersSelf ℝ E)
          (modelWithCornersSelf ℝ E) ∞ c₀.symm c₀.target :=
        contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
      have h₁ := contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
      change ContMDiffOn (modelWithCornersSelf ℝ E)
        (modelWithCornersSelf ℝ E) ∞ (c₀.symm ∘ h.domChart.symm)
          (h.domChart.target ∩ h.domChart.symm ⁻¹' c₀.target)
      exact h₀.comp' h₁
  have hdmax : d ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ F) ∞ N := by
    apply d.mem_maximalAtlas_of_contMDiffOn
    · have h₀ : ContMDiffOn (modelWithCornersSelf ℝ F)
          (modelWithCornersSelf ℝ F) ∞ d₀ d₀.source :=
        contMDiffOn_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (f x))
      have h₁ := contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
      change ContMDiffOn (modelWithCornersSelf ℝ F)
        (modelWithCornersSelf ℝ F) ∞ (h.codChart ∘ d₀)
          (d₀.source ∩ d₀ ⁻¹' h.codChart.source)
      exact h₁.comp' h₀
    · have h₀ : ContMDiffOn (modelWithCornersSelf ℝ F)
          (modelWithCornersSelf ℝ F) ∞ d₀.symm d₀.target :=
        contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (f x))
      have h₁ := contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
      change ContMDiffOn (modelWithCornersSelf ℝ F)
        (modelWithCornersSelf ℝ F) ∞ (d₀.symm ∘ h.codChart.symm)
          (h.codChart.target ∩ h.codChart.symm ⁻¹' d₀.target)
      exact h₀.comp' h₁
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt hf h.equiv c d
    hxc hfd hcmax hdmax
  intro y hy
  have hyc : y ∈ c.target := by
    rw [OpenPartialHomeomorph.extend_target] at hy
    exact hy.1
  have hyh : y ∈ h.domChart.target := by
    change y ∈ h.domChart.target ∩ h.domChart.symm ⁻¹' c₀.target at hyc
    exact hyc.1
  have hyhext : y ∈ (h.domChart.extend (modelWithCornersSelf ℝ E)).target := by
    rw [OpenPartialHomeomorph.extend_target]
    exact ⟨hyh, mem_range_self y⟩
  have hw := h.writtenInCharts hyhext
  change h.codChart (d₀ (f (c₀.symm (h.domChart.symm y)))) = h.equiv (y, 0) at hw
  change h.codChart (d₀ (f (c₀.symm (h.domChart.symm y)))) = h.equiv (y, 0)
  exact hw

end Transport

section ManifoldSplit

variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
  [IsManifold (modelWithCornersSelf ℝ F) ∞ N]

/-- On finite-dimensional boundaryless manifolds, a split `mfderiv` gives an immersion. -/
theorem isImmersionAtOfComplement_of_contMDiff_mfderiv_split
    (f : M → N) (hf : ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ F) ∞ f)
    (x : M) (L : (E × C) ≃L[ℝ] F)
    (hder : mfderiv (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ F) f x =
        (ContinuousLinearEquiv.toContinuousLinearMap L).comp
          (ContinuousLinearMap.inl ℝ E C)) :
    Manifold.IsImmersionAtOfComplement C (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ F) ∞ f x := by
  let c₀ : OpenPartialHomeomorph M E := chartAt E x
  let d₀ : OpenPartialHomeomorph N F := chartAt F (f x)
  let sM : Set M := c₀.source ∩ f ⁻¹' d₀.source
  let sE : Set E := c₀ '' sM
  let T : E → F := writtenInExtChartAt (modelWithCornersSelf ℝ E)
    (modelWithCornersSelf ℝ F) x f
  have hsMopen : IsOpen sM :=
    c₀.open_source.inter (d₀.open_source.preimage hf.continuous)
  have hsMsub : sM ⊆ c₀.source := inter_subset_left
  have hsEopen : IsOpen sE := by
    exact c₀.isOpen_image_of_subset_source hsMopen hsMsub
  have hxa : c₀ x ∈ sE := by
    refine ⟨x, ⟨mem_chart_source E x, ?_⟩, rfl⟩
    exact mem_chart_source F (f x)
  have hmaps : MapsTo f sM d₀.source := fun y hy ↦ hy.2
  have hcoordM : ContMDiffOn (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ F) ∞ T sE := by
    have h := (c₀.contMDiffOn_writtenInExtend_iff
      (IsManifold.chart_mem_maximalAtlas x)
      (IsManifold.chart_mem_maximalAtlas (f x)) hsMsub hmaps).2
        (hf.contMDiffOn.mono (subset_univ sM))
    simpa only [T, sE, c₀, d₀, writtenInExtChartAt, extChartAt,
      OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_comp] using h
  have hcoord : ContDiffOn ℝ ∞ T sE :=
    contMDiffOn_iff_contDiffOn.mp hcoordM
  have hmd : MDiffAt f x := (hf x).mdifferentiableAt (by simp)
  have hcoordDer : HasFDerivAt T
      ((ContinuousLinearEquiv.toContinuousLinearMap L).comp
        (ContinuousLinearMap.inl ℝ E C))
      ((extChartAt (modelWithCornersSelf ℝ E) x) x) := by
    have h := hmd.hasMFDerivAt
    rw [hder] at h
    have h' := h.2
    rw [ModelWithCorners.range_eq_univ] at h'
    exact hasFDerivWithinAt_univ.mp h'
  have hcoordImm := isImmersionAtOfComplement_of_contDiffOn_hasFDerivAt_split T L
    ((extChartAt (modelWithCornersSelf ℝ E) x) x) sE hsEopen
    (by simpa only [c₀, extChartAt, OpenPartialHomeomorph.extend_coe,
      modelWithCornersSelf_coe, id_comp] using hxa) hcoord hcoordDer
  exact isImmersionAtOfComplement_of_writtenInExtChartAt
    hf.continuous.continuousAt hcoordImm

end ManifoldSplit

section CodimensionOne

variable {A B : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

/-- An injective linear map of codimension one extends to an equivalence after adding `ℝ`. -/
theorem exists_continuousLinearEquiv_prod_real_of_injective
    (m : A →L[ℝ] B) (hm : Function.Injective m)
    (hrank : Module.finrank ℝ A + 1 = Module.finrank ℝ B) :
    ∃ L : (A × ℝ) ≃L[ℝ] B,
      (ContinuousLinearEquiv.toContinuousLinearMap L).comp
        (ContinuousLinearMap.inl ℝ A ℝ) = m := by
  let K : Submodule ℝ B := LinearMap.range m.toLinearMap
  let eA : A ≃L[ℝ] K :=
    (LinearEquiv.ofInjective m.toLinearMap hm).toContinuousLinearEquiv
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl K
  have hQrank : Module.finrank ℝ Q = 1 := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hQ
    rw [← eA.toLinearEquiv.finrank_eq] at hsum
    omega
  let eR : ℝ ≃L[ℝ] Q :=
    ContinuousLinearEquiv.ofFinrankEq (by simpa using hQrank.symm)
  let eDec : (K × Q) ≃L[ℝ] B :=
    (K.prodEquivOfIsCompl Q hQ).toContinuousLinearEquiv
  let L : (A × ℝ) ≃L[ℝ] B := (eA.prodCongr eR).trans eDec
  refine ⟨L, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  change L (v, 0) = m v
  change ((eA v : K) : B) + ((eR 0 : Q) : B) = m v
  simp only [map_zero, Submodule.coe_zero, add_zero]
  rfl

end CodimensionOne

section ImmersionDerivative

variable {E₁ E₂ D : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [ChartedSpace E₁ M₁]
  [TopologicalSpace M₂] [ChartedSpace E₂ M₂]
  [IsManifold (modelWithCornersSelf ℝ E₁) 1 M₁]
  [IsManifold (modelWithCornersSelf ℝ E₂) 1 M₂]

omit [IsManifold (modelWithCornersSelf ℝ E₁) 1 M₁]
  [IsManifold (modelWithCornersSelf ℝ E₂) 1 M₂] in
private theorem immersion_coordinate_projection_mdifferentiable
    {f : M₁ → M₂} {x : M₁}
    (h : Manifold.IsImmersionAtOfComplement D
      (modelWithCornersSelf ℝ E₁) (modelWithCornersSelf ℝ E₂) ∞ f x) :
    MDiffAt (fun y : M₂ ↦
      (h.equiv.symm ((h.codChart.extend (modelWithCornersSelf ℝ E₂)) y)).1)
      (f x) := by
  let q : M₂ → E₁ := fun y ↦
    (h.equiv.symm ((h.codChart.extend (modelWithCornersSelf ℝ E₂)) y)).1
  have hcod : MDiffAt
      (h.codChart.extend (modelWithCornersSelf ℝ E₂)) (f x) :=
    (h.codChart.contMDiffAt_extend h.codChart_mem_maximalAtlas
      h.mem_codChart_source).mdifferentiableAt (by simp)
  have hq : MDiffAt q (f x) := by
    dsimp only [q]
    have houter : Differentiable ℝ (fun z : E₂ ↦ (h.equiv.symm z).1) := by fun_prop
    exact houter.comp_mdifferentiableAt hcod
  exact hq

omit [IsManifold (modelWithCornersSelf ℝ E₁) 1 M₁]
  [IsManifold (modelWithCornersSelf ℝ E₂) 1 M₂] in
private theorem immersion_coordinate_projection_eventuallyEq
    {f : M₁ → M₂} {x : M₁}
    (h : Manifold.IsImmersionAtOfComplement D
      (modelWithCornersSelf ℝ E₁) (modelWithCornersSelf ℝ E₂) ∞ f x) :
    Filter.EventuallyEq (nhds x)
      (fun y : M₁ ↦
        (h.equiv.symm ((h.codChart.extend (modelWithCornersSelf ℝ E₂)) (f y))).1)
      (h.domChart.extend (modelWithCornersSelf ℝ E₁)) := by
  filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source] with y hy
  have hy' : y ∈ (h.domChart.extend (modelWithCornersSelf ℝ E₁)).source := by
    rwa [h.domChart.extend_source]
  have hz : (h.domChart.extend (modelWithCornersSelf ℝ E₁)) y ∈
      (h.domChart.extend (modelWithCornersSelf ℝ E₁)).target :=
    (h.domChart.extend (modelWithCornersSelf ℝ E₁)).map_source hy'
  have hw := h.writtenInCharts hz
  simp only [Function.comp_apply,
    (h.domChart.extend (modelWithCornersSelf ℝ E₁)).left_inv hy'] at hw
  rw [hw, ContinuousLinearEquiv.symm_apply_apply]

omit [IsManifold (modelWithCornersSelf ℝ E₁) 1 M₁]
  [IsManifold (modelWithCornersSelf ℝ E₂) 1 M₂] in
private theorem immersion_domExtend_mfderiv_injective
    {f : M₁ → M₂} {x : M₁}
    (h : Manifold.IsImmersionAtOfComplement D
      (modelWithCornersSelf ℝ E₁) (modelWithCornersSelf ℝ E₂) ∞ f x) :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ E₁)
      (modelWithCornersSelf ℝ E₁)
      (h.domChart.extend (modelWithCornersSelf ℝ E₁)) x) := by
  have hc : h.domChart.MDifferentiable (modelWithCornersSelf ℝ E₁)
      (modelWithCornersSelf ℝ E₁) := ⟨
    (contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn
      (by simp),
    (contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn
      (by simp)⟩
  have hcinj : Function.Injective (mfderiv (modelWithCornersSelf ℝ E₁)
      (modelWithCornersSelf ℝ E₁) h.domChart x) :=
    hc.mfderiv_injective h.mem_domChart_source
  have hcAt : MDiffAt h.domChart x := hc.mdifferentiableAt h.mem_domChart_source
  have heq : mfderiv (modelWithCornersSelf ℝ E₁)
      (modelWithCornersSelf ℝ E₁)
      (h.domChart.extend (modelWithCornersSelf ℝ E₁)) x =
      mfderiv (modelWithCornersSelf ℝ E₁)
        (modelWithCornersSelf ℝ E₁) h.domChart x := by
    rw [show (h.domChart.extend (modelWithCornersSelf ℝ E₁) : M₁ → E₁) =
      (modelWithCornersSelf ℝ E₁) ∘ h.domChart by rfl,
      mfderiv_comp x (modelWithCornersSelf ℝ E₁).mdifferentiableAt hcAt]
    rw [(modelWithCornersSelf ℝ E₁).hasMFDerivAt.mfderiv]
    exact ContinuousLinearMap.id_comp _
  rw [heq]
  exact hcinj

omit [IsManifold (modelWithCornersSelf ℝ E₁) 1 M₁]
  [IsManifold (modelWithCornersSelf ℝ E₂) 1 M₂] in
/-- The manifold derivative of an immersion is injective. -/
theorem immersion_mfderiv_injective
    {f : M₁ → M₂} {x : M₁}
    (h : Manifold.IsImmersionAtOfComplement D
      (modelWithCornersSelf ℝ E₁) (modelWithCornersSelf ℝ E₂) ∞ f x) :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ E₁)
      (modelWithCornersSelf ℝ E₂) f x) := by
  let q : M₂ → E₁ := fun y ↦
    (h.equiv.symm ((h.codChart.extend (modelWithCornersSelf ℝ E₂)) y)).1
  have hq : MDiffAt q (f x) := immersion_coordinate_projection_mdifferentiable h
  have hf : MDiffAt f x := h.contMDiffAt.mdifferentiableAt (by simp)
  have hqf : Filter.EventuallyEq (nhds x) (q ∘ f)
      (h.domChart.extend (modelWithCornersSelf ℝ E₁)) :=
    immersion_coordinate_projection_eventuallyEq h
  have hdominj := immersion_domExtend_mfderiv_injective h
  intro v w hvw
  apply hdominj
  rw [← hqf.mfderiv_eq, mfderiv_comp x hq hf]
  exact congrArg (mfderiv (modelWithCornersSelf ℝ E₂)
    (modelWithCornersSelf ℝ E₁) q (f x)) hvw

end ImmersionDerivative

section TraceDerivative

variable {E₀ E₁ E₂ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  {M₀ M₁ M₂ : Type*}
  [TopologicalSpace M₀] [ChartedSpace E₀ M₀]
  [TopologicalSpace M₁] [ChartedSpace E₁ M₁]
  [TopologicalSpace M₂] [ChartedSpace E₂ M₂]
  [IsManifold (modelWithCornersSelf ℝ E₀) 1 M₀]
  [IsManifold (modelWithCornersSelf ℝ E₁) 1 M₁]
  [IsManifold (modelWithCornersSelf ℝ E₂) 1 M₂]

omit [IsManifold (modelWithCornersSelf ℝ E₀) 1 M₀]
  [IsManifold (modelWithCornersSelf ℝ E₁) 1 M₁]
  [IsManifold (modelWithCornersSelf ℝ E₂) 1 M₂] in
set_option backward.isDefEq.respectTransparency false in
/-- The time-preserving trace has injective derivative when every spatial slice does. -/
theorem trace_mfderiv_injective
    (Fmap : M₀ × M₁ → M₂) (p : M₀ × M₁)
    (hF : MDiffAt Fmap p)
    (hslice : Function.Injective
      (mfderiv (modelWithCornersSelf ℝ E₁)
        (modelWithCornersSelf ℝ E₂) (fun x ↦ Fmap (p.1, x)) p.2)) :
    Function.Injective
      (mfderiv ((modelWithCornersSelf ℝ E₀).prod
          (modelWithCornersSelf ℝ E₁))
        ((modelWithCornersSelf ℝ E₀).prod
          (modelWithCornersSelf ℝ E₂))
        (fun z ↦ (z.1, Fmap z)) p) := by
  have hGder := mfderiv_prodMk (x := p) mdifferentiableAt_fst hF
  intro v w hvw
  rcases v with ⟨v₀, v₁⟩
  rcases w with ⟨w₀, w₁⟩
  rw [hGder] at hvw
  simp only [mfderiv_fst, ContinuousLinearMap.fst] at hvw
  have hfirst : v₀ = w₀ := congrArg Prod.fst hvw
  have hsecond :
      (mfderiv ((modelWithCornersSelf ℝ E₀).prod
        (modelWithCornersSelf ℝ E₁)) (modelWithCornersSelf ℝ E₂) Fmap p)
          (v₀, v₁) =
      (mfderiv ((modelWithCornersSelf ℝ E₀).prod
        (modelWithCornersSelf ℝ E₁)) (modelWithCornersSelf ℝ E₂) Fmap p)
          (w₀, w₁) := congrArg Prod.snd hvw
  rw [mfderiv_prod_eq_add_apply hF, mfderiv_prod_eq_add_apply hF, hfirst] at hsecond
  have hvsecond : v₁ = w₁ := hslice (add_left_cancel hsecond)
  exact Prod.ext hfirst hvsecond

end TraceDerivative

section SphereTrace

/-- The time-preserving trace of the real-time flattened isotopy. -/
def SmoothSphereIsotopy.flattenedRealTimeTrace
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) : ℝ × Sphere 3 → ℝ × Sphere 4 :=
  fun p ↦ (p.1, H.flattenedRealTime p)

@[simp]
theorem SmoothSphereIsotopy.flattenedRealTimeTrace_apply
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) (p : ℝ × Sphere 3) :
    H.flattenedRealTimeTrace p = (p.1, H.flattenedRealTime p) := rfl

@[simp]
theorem SmoothSphereIsotopy.flattenedRealTimeTrace_fst
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) (p : ℝ × Sphere 3) :
    (H.flattenedRealTimeTrace p).1 = p.1 := rfl

@[simp]
theorem SmoothSphereIsotopy.flattenedRealTimeTrace_snd
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) (p : ℝ × Sphere 3) :
    (H.flattenedRealTimeTrace p).2 = H.flattenedRealTime p := rfl

@[simp]
theorem SmoothSphereIsotopy.flattenedRealTimeTrace_coe
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) (p : I × Sphere 3) :
    H.flattenedRealTimeTrace ((p.1 : ℝ), p.2) =
      ((p.1 : ℝ), H.flattenEndpoints.toFun p) := by
  simp only [SmoothSphereIsotopy.flattenedRealTimeTrace_apply,
    SmoothSphereIsotopy.flattenedRealTime_coe]

/-- The trace uses the original zero slice throughout the first quarter. -/
theorem SmoothSphereIsotopy.flattenedRealTimeTrace_eq_zero
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) {t : ℝ} (ht : t ≤ 1 / 4)
    (x : Sphere 3) :
    H.flattenedRealTimeTrace (t, x) = (t, H.toFun (0, x)) := by
  rw [SmoothSphereIsotopy.flattenedRealTimeTrace_apply,
    H.flattenedRealTime_eq_zero ht]

/-- The trace uses the original one slice from the last quarter onward. -/
theorem SmoothSphereIsotopy.flattenedRealTimeTrace_eq_one
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) {t : ℝ} (ht : (3 / 4 : ℝ) ≤ t)
    (x : Sphere 3) :
    H.flattenedRealTimeTrace (t, x) = (t, H.toFun (1, x)) := by
  rw [SmoothSphereIsotopy.flattenedRealTimeTrace_apply,
    H.flattenedRealTime_eq_one ht]

theorem SmoothSphereIsotopy.contMDiff_flattenedRealTimeTrace
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) :
    ContMDiff ((modelWithCornersSelf ℝ ℝ).prod
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))))
      ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))) ∞
      H.flattenedRealTimeTrace :=
  contMDiff_fst.prodMk H.contMDiff_flattenedRealTime

private theorem SmoothSphereIsotopy.isImmersionAtOfComplement_flattenedRealTimeTrace
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) (p : ℝ × Sphere 3) :
    Manifold.IsImmersionAtOfComplement ℝ ((modelWithCornersSelf ℝ ℝ).prod
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))))
      ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))) ∞
      H.flattenedRealTimeTrace p := by
  let E₃ := EuclideanSpace ℝ (Fin 3)
  let E₄ := EuclideanSpace ℝ (Fin 4)
  let : ChartedSpace (ℝ × E₃) (ℝ × Sphere 3) :=
    prodChartedSpace ℝ ℝ E₃ (Sphere 3)
  let : ChartedSpace (ℝ × E₄) (ℝ × Sphere 4) :=
    prodChartedSpace ℝ ℝ E₄ (Sphere 4)
  have : IsManifold (modelWithCornersSelf ℝ ℝ) ∞ ℝ := by
    infer_instance
  have : IsManifold (modelWithCornersSelf ℝ E₃) ∞ (Sphere 3) := by
    dsimp only [E₃]
    infer_instance
  have : IsManifold (modelWithCornersSelf ℝ E₄) ∞ (Sphere 4) := by
    dsimp only [E₄]
    infer_instance
  let : IsManifold (modelWithCornersSelf ℝ (ℝ × E₃)) ∞
      (ℝ × Sphere 3) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod ℝ (Sphere 3)
  let : IsManifold (modelWithCornersSelf ℝ (ℝ × E₄)) ∞
      (ℝ × Sphere 4) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod ℝ (Sphere 4)
  have hslice : Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun x ↦ H.flattenedRealTime (p.1, x)) := by
    simpa only [SmoothSphereIsotopy.flattenedRealTime] using
      H.isSmoothEmbedding_slice (unitInterval.endpointFlatTimeReal p.1)
  have hsliceInj : Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (fun x ↦ H.flattenedRealTime (p.1, x)) p.2) := by
    let hi := hslice.isImmersion.isImmersionAt p.2
    exact immersion_mfderiv_injective
      hi.isImmersionAtOfComplement_complement
  have hinjProd := trace_mfderiv_injective
    (E₀ := ℝ) (E₁ := E₃) (E₂ := E₄) H.flattenedRealTime p
    (H.contMDiff_flattenedRealTime.mdifferentiableAt (by simp)) hsliceInj
  have hinj : Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (ℝ × E₃))
        (modelWithCornersSelf ℝ (ℝ × E₄)) H.flattenedRealTimeTrace p) := by
    rw [modelWithCornersSelf_prod, modelWithCornersSelf_prod]
    change Function.Injective
      (mfderiv ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ E₃))
        ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ E₄))
        (fun z ↦ (z.1, H.flattenedRealTime z)) p)
    exact hinjProd
  let m : (ℝ × E₃) →L[ℝ] (ℝ × E₄) :=
    mfderiv (modelWithCornersSelf ℝ (ℝ × E₃))
      (modelWithCornersSelf ℝ (ℝ × E₄)) H.flattenedRealTimeTrace p
  have hminj : Function.Injective m := by
    exact hinj
  have hrank : Module.finrank ℝ (ℝ × E₃) + 1 =
      Module.finrank ℝ (ℝ × E₄) := by
    simp only [E₃, E₄, Module.finrank_prod,
      finrank_euclideanSpace, Fintype.card_fin]
  obtain ⟨L, hL⟩ := exists_continuousLinearEquiv_prod_real_of_injective
    (A := ℝ × E₃) (B := ℝ × E₄) m hminj hrank
  have htraceSelf : ContMDiff (modelWithCornersSelf ℝ (ℝ × E₃))
      (modelWithCornersSelf ℝ (ℝ × E₄)) ∞
      H.flattenedRealTimeTrace := by
    simpa only [E₃, E₄, modelWithCornersSelf_prod] using
      H.contMDiff_flattenedRealTimeTrace
  have himmSelf := isImmersionAtOfComplement_of_contMDiff_mfderiv_split
    H.flattenedRealTimeTrace htraceSelf p L (by
    change m = _
    exact hL.symm)
  simpa only [E₃, E₄, modelWithCornersSelf_prod] using himmSelf

/-- The real-time trace is an immersion with its fixed one-dimensional complement. -/
theorem SmoothSphereIsotopy.isImmersionOfComplement_flattenedRealTimeTrace
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) :
    Manifold.IsImmersionOfComplement ℝ ((modelWithCornersSelf ℝ ℝ).prod
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))))
      ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))) ∞
      H.flattenedRealTimeTrace :=
  H.isImmersionAtOfComplement_flattenedRealTimeTrace

/-- The real-time trace is a smooth immersion. -/
theorem SmoothSphereIsotopy.isImmersion_flattenedRealTimeTrace
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) :
    Manifold.IsImmersion ((modelWithCornersSelf ℝ ℝ).prod
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))))
      ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))) ∞
      H.flattenedRealTimeTrace :=
  H.isImmersionOfComplement_flattenedRealTimeTrace.isImmersion

/-- The real-time trace is a topological embedding. -/
theorem SmoothSphereIsotopy.isEmbedding_flattenedRealTimeTrace
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) :
    Topology.IsEmbedding H.flattenedRealTimeTrace := by
  have hcont : Continuous H.flattenedRealTimeTrace :=
    H.contMDiff_flattenedRealTimeTrace.continuous
  have hinj : Function.Injective H.flattenedRealTimeTrace := by
    rintro ⟨t, x⟩ ⟨s, y⟩ h
    have htime : t = s := congrArg Prod.fst h
    subst s
    apply Prod.ext
    · rfl
    apply (H.isSmoothEmbedding_slice
      (unitInterval.endpointFlatTimeReal t)).isEmbedding.injective
    exact congrArg Prod.snd h
  have hproperFst : IsProperMap
      (Prod.fst : ℝ × Sphere 3 → ℝ) := isProperMap_fst_of_compactSpace
  have hproper : IsProperMap H.flattenedRealTimeTrace :=
    isProperMap_of_comp_of_t2 hcont continuous_fst (by
      simpa only [Function.comp_def,
        SmoothSphereIsotopy.flattenedRealTimeTrace_fst] using hproperFst)
  exact (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    hcont hinj hproper.isClosedMap).isEmbedding

/-- The time-preserving real-time trace of a flattened sphere isotopy is a smooth embedding. -/
theorem SmoothSphereIsotopy.isSmoothEmbedding_flattenedRealTimeTrace
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) :
    Manifold.IsSmoothEmbedding ((modelWithCornersSelf ℝ ℝ).prod
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))))
      ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))) ∞
      H.flattenedRealTimeTrace :=
  Manifold.IsSmoothEmbedding.mk
    H.isImmersion_flattenedRealTimeTrace
    H.isEmbedding_flattenedRealTimeTrace

end SphereTrace

end SplittingSpheres
