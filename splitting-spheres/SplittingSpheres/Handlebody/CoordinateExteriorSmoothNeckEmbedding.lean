/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorSmoothNeckCylinder
public import SplittingSpheres.Foundations.SmoothEmbedding

/-!
# Smooth embeddings of the coordinate-unlink neck cylinder

This file proves that the explicit closed neck cylinder is a smooth embedding, including at both
boundary faces of its interval factor.  The proof first embeds the interval as the vertical
diameter of the normal disk, takes its product with the two-sphere, and passes through the polar
product diffeomorphism.  The fixed-label lifts are then smooth embeddings by reflection through
the locally diffeomorphic covering projection.

The auxiliary chart transport across unequal Euclidean model presentations is kept private.  No
claim about capping, gluing, separation, or a smooth structure on a pushout is made here.
-/

@[expose] public section

open Function Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace Manifold

universe uA uE uE' uF uH

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {A : Type uA} [NormedAddCommGroup A] [NormedSpace 𝕜 A]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type uH} [TopologicalSpace H]
  {IM : ModelWithCorners 𝕜 A H}
  {M Q R : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace Q] [ChartedSpace E Q]
  [TopologicalSpace R] [ChartedSpace E' R]
  {n : ℕ∞ω}
  {f : M → Q} {x : M}

private theorem contMDiff_linearEquiv (L : E ≃L[𝕜] E') :
    ContMDiff (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') n L :=
  contMDiff_iff_contDiff.mpr L.contDiff

private theorem contMDiff_linearEquiv_symm (L : E ≃L[𝕜] E') :
    ContMDiff (modelWithCornersSelf 𝕜 E') (modelWithCornersSelf 𝕜 E) n L.symm :=
  contMDiff_iff_contDiff.mpr L.symm.contDiff

private theorem IsImmersionAtOfComplement.postcomp_diffeomorph_selfModels
    [IsManifold IM n M]
    [IsManifold (modelWithCornersSelf 𝕜 E) n Q]
    [IsManifold (modelWithCornersSelf 𝕜 E') n R]
    (hf : IsImmersionAtOfComplement F IM
      (modelWithCornersSelf 𝕜 E) n f x)
    (e : Q ≃ₘ^n⟮modelWithCornersSelf 𝕜 E,
      modelWithCornersSelf 𝕜 E'⟯ R)
    (L : E ≃L[𝕜] E') :
    IsImmersionAtOfComplement F IM
      (modelWithCornersSelf 𝕜 E') n (e ∘ f) x := by
  let d0 : OpenPartialHomeomorph R E :=
    e.toHomeomorph.toOpenPartialHomeomorph.symm.trans hf.codChart
  let d : OpenPartialHomeomorph R E' :=
    d0.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hfxd : e (f x) ∈ d.source := by
    simp only [d, d0, OpenPartialHomeomorph.trans_source, mem_inter_iff,
      mem_preimage, Homeomorph.toOpenPartialHomeomorph_source,
      Homeomorph.toOpenPartialHomeomorph_target,
      OpenPartialHomeomorph.symm_source, univ_inter]
    simpa using hf.mem_codChart_source
  have hd_source : d.source = d0.source := by
    simp [d]
  have hd0_source : d0.source = e.symm ⁻¹' hf.codChart.source := by
    simp [d0]
  have hd_smooth : ContMDiffOn (modelWithCornersSelf 𝕜 E')
      (modelWithCornersSelf 𝕜 E') n d d.source := by
    rw [show (d : R → E') = L ∘ hf.codChart ∘ e.symm by rfl]
    have hmiddle : ContMDiffOn (modelWithCornersSelf 𝕜 E')
        (modelWithCornersSelf 𝕜 E) n
        (hf.codChart ∘ e.symm) d.source :=
      (contMDiffOn_of_mem_maximalAtlas hf.codChart_mem_maximalAtlas).comp
        e.symm.contMDiff.contMDiffOn (by
          intro z hz
          rw [hd_source, hd0_source] at hz
          exact hz)
    exact ((contMDiff_linearEquiv L).contMDiffOn (s := univ)).comp hmiddle
      (fun _ _ ↦ mem_univ _)
  have hd_target : d.target = L.symm ⁻¹' d0.target := by
    simp [d]
  have hd0_target : d0.target = hf.codChart.target := by
    simp [d0]
  have hd_symm_smooth : ContMDiffOn (modelWithCornersSelf 𝕜 E')
      (modelWithCornersSelf 𝕜 E') n d.symm d.target := by
    rw [show (d.symm : E' → R) = e ∘ hf.codChart.symm ∘ L.symm by rfl]
    have hmiddle : ContMDiffOn (modelWithCornersSelf 𝕜 E')
        (modelWithCornersSelf 𝕜 E) n
        (hf.codChart.symm ∘ L.symm) d.target :=
      (contMDiffOn_symm_of_mem_maximalAtlas hf.codChart_mem_maximalAtlas).comp
        (contMDiff_linearEquiv_symm L).contMDiffOn (by
          intro z hz
          rw [hd_target, hd0_target] at hz
          exact hz)
    exact (e.contMDiff.contMDiffOn (s := univ)).comp hmiddle
      (fun _ _ ↦ mem_univ _)
  have hd_max : d ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf 𝕜 E') n R :=
    d.mem_maximalAtlas_of_contMDiffOn hd_smooth hd_symm_smooth
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (e.continuous.continuousAt.comp hf.continuousAt)
    (hf.equiv.trans L) hf.domChart d
    hf.mem_domChart_source hfxd hf.domChart_mem_maximalAtlas hd_max
  intro y hy
  have hbase := hf.writtenInCharts hy
  rw [OpenPartialHomeomorph.extend_coe] at hbase ⊢
  change L (hf.codChart (e.symm (e (f ((hf.domChart.extend
    IM).symm y))))) = _
  rw [e.symm_apply_apply]
  exact congrArg L hbase

private theorem IsImmersionOfComplement.postcomp_diffeomorph_selfModels
    [IsManifold IM n M]
    [IsManifold (modelWithCornersSelf 𝕜 E) n Q]
    [IsManifold (modelWithCornersSelf 𝕜 E') n R]
    (hf : IsImmersionOfComplement F IM
      (modelWithCornersSelf 𝕜 E) n f)
    (e : Q ≃ₘ^n⟮modelWithCornersSelf 𝕜 E,
      modelWithCornersSelf 𝕜 E'⟯ R)
    (L : E ≃L[𝕜] E') :
    IsImmersionOfComplement F IM
      (modelWithCornersSelf 𝕜 E') n (e ∘ f) :=
  fun x ↦ (hf x).postcomp_diffeomorph_selfModels e L

private theorem IsImmersion.postcomp_diffeomorph_selfModels
    [IsManifold IM n M]
    [IsManifold (modelWithCornersSelf 𝕜 E) n Q]
    [IsManifold (modelWithCornersSelf 𝕜 E') n R]
    (hf : IsImmersion IM
      (modelWithCornersSelf 𝕜 E) n f)
    (e : Q ≃ₘ^n⟮modelWithCornersSelf 𝕜 E,
      modelWithCornersSelf 𝕜 E'⟯ R)
    (L : E ≃L[𝕜] E') :
    IsImmersion IM
      (modelWithCornersSelf 𝕜 E') n (e ∘ f) :=
  (hf.isImmersionOfComplement_complement.postcomp_diffeomorph_selfModels e L).isImmersion

private theorem IsSmoothEmbedding.postcomp_diffeomorph_selfModels
    [IsManifold IM n M]
    [IsManifold (modelWithCornersSelf 𝕜 E) n Q]
    [IsManifold (modelWithCornersSelf 𝕜 E') n R]
    (hf : IsSmoothEmbedding IM
      (modelWithCornersSelf 𝕜 E) n f)
    (e : Q ≃ₘ^n⟮modelWithCornersSelf 𝕜 E,
      modelWithCornersSelf 𝕜 E'⟯ R)
    (L : E ≃L[𝕜] E') :
    IsSmoothEmbedding IM
      (modelWithCornersSelf 𝕜 E') n (e ∘ f) where
  isImmersion := hf.isImmersion.postcomp_diffeomorph_selfModels e L
  isEmbedding := e.toHomeomorph.isEmbedding.comp hf.isEmbedding

end Manifold

namespace SplittingSpheres

open Metric

/-- The one-dimensional Euclidean source used in the interval chart normal form. -/
abbrev NeckLineSource := EuclideanSpace ℝ (Fin 1)

/-- Linear normal form for the vertical diameter: the extra real parameter is the horizontal
normal direction. -/
def neckDiskChartLinearMap :
    (NeckLineSource × ℝ) →ₗ[ℝ] SphereHandleFirst where
  toFun p := WithLp.toLp 2 ![p.2, 2 * WithLp.ofLp p.1 0]
  map_add' p q := by
    ext j
    fin_cases j <;> simp
    ring
  map_smul' c p := by
    ext j
    fin_cases j <;> simp
    ring

/-- The displayed interval normal form is injective. -/
theorem neckDiskChartLinearMap_injective :
    Function.Injective neckDiskChartLinearMap := by
  intro p q hpq
  have h0 := congrArg (fun z : SphereHandleFirst ↦ z 0) hpq
  have h1 := congrArg (fun z : SphereHandleFirst ↦ z 1) hpq
  apply Prod.ext
  · apply PiLp.ext
    intro j
    fin_cases j
    dsimp [neckDiskChartLinearMap] at h1
    exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) h1
  · simpa [neckDiskChartLinearMap] using h0

/-- The interval direction plus its chosen complement has the normal plane's dimension. -/
theorem finrank_neckDiskChart :
    Module.finrank ℝ (NeckLineSource × ℝ) =
      Module.finrank ℝ SphereHandleFirst := by
  simp [NeckLineSource, SphereHandleFirst]

/-- The continuous linear equivalence underlying the interval immersion charts. -/
def neckDiskChartLinearEquiv :
    (NeckLineSource × ℝ) ≃L[ℝ] SphereHandleFirst :=
  (neckDiskChartLinearMap.linearEquivOfInjective
    neckDiskChartLinearMap_injective finrank_neckDiskChart).toContinuousLinearEquiv

/-- Evaluation of the bundled linear equivalence agrees with its defining linear map. -/
@[simp]
theorem neckDiskChartLinearEquiv_apply (p : NeckLineSource × ℝ) :
    neckDiskChartLinearEquiv p = neckDiskChartLinearMap p := rfl

/-- The horizontal coordinate of the raw neck diameter vanishes. -/
@[simp]
theorem coordinateUnlinkExteriorSmoothNeckDiskRaw_apply_zero
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorSmoothNeckDiskRaw t 0 = 0 := by
  simp [coordinateUnlinkExteriorSmoothNeckDiskRaw,
    coordinateUnlinkExteriorPlanarNeckBaseArc,
    complexToUnlinkNormalPlane]
  norm_num

/-- The vertical coordinate of the raw neck diameter is the affine interval parameter. -/
@[simp]
theorem coordinateUnlinkExteriorSmoothNeckDiskRaw_apply_one
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorSmoothNeckDiskRaw t 1 = 2 * (t : ℝ) - 1 := by
  unfold coordinateUnlinkExteriorSmoothNeckDiskRaw
  simp only [PiLp.smul_apply]
  rw [show (complexToUnlinkNormalPlane
    (coordinateUnlinkExteriorPlanarNeckBaseArc t + (1 / 2 : ℂ))) 1 =
      sphereHandleRadius * (2 * (t : ℝ) - 1) by
    simp [complexToUnlinkNormalPlane,
      coordinateUnlinkExteriorPlanarNeckBaseArc]]
  simp only [smul_eq_mul, inv_mul_cancel_left₀ sphereHandleRadius_ne_zero]

/-- The raw closed-interval diameter is an immersion, including at both boundary points. -/
theorem isImmersionOfComplement_coordinateUnlinkExteriorSmoothNeckDiskRaw :
    Manifold.IsImmersionOfComplement ℝ
      (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf ℝ SphereHandleFirst) ∞
      coordinateUnlinkExteriorSmoothNeckDiskRaw := by
  intro t
  by_cases ht : (t : ℝ) < 1
  · let c : SphereHandleFirst :=
      coordinateUnlinkExteriorSmoothNeckDiskRaw 0
    apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
      contMDiff_coordinateUnlinkExteriorSmoothNeckDiskRaw.continuous.continuousAt
      neckDiskChartLinearEquiv
      (chartAt (EuclideanHalfSpace 1) t)
      (Homeomorph.addLeft (-c)).toOpenPartialHomeomorph
      (mem_chart_source _ t) (by simp [Homeomorph.addLeft])
      (IsManifold.chart_mem_maximalAtlas t) ?_; swap
    · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      · have : ContDiff ℝ ∞ (fun y : SphereHandleFirst ↦ -c + y) := by fun_prop
        simpa [contMDiffOn_iff_contDiffOn, contDiffOn_univ]
      · have : ContDiff ℝ ∞ (fun y : SphereHandleFirst ↦ c + y) := by fun_prop
        simpa [contMDiffOn_iff_contDiffOn, contDiffOn_univ, Homeomorph.addLeft]
    intro z hz
    obtain ⟨⟨u, rfl⟩, hu⟩ :
        (∃ y, ⇑(modelWithCornersEuclideanHalfSpace 1) y = z) ∧
          ⇑(modelWithCornersEuclideanHalfSpace 1).symm z ∈
            (IccLeftChart (0 : ℝ) 1).target := by
      simpa [ht] using! hz
    replace hu : WithLp.ofLp u.val 0 ≤ (1 : ℝ) - 0 := by
      have hu' : u ∈ (IccLeftChart (0 : ℝ) 1).target := by
        simpa [modelWithCornersEuclideanHalfSpace_symm_apply,
          max_eq_left u.property] using hu
      change WithLp.ofLp u.val 0 < (1 : ℝ) - 0 at hu'
      exact hu'.le
    ext j
    fin_cases j
    · simp [ht, c, neckDiskChartLinearEquiv, neckDiskChartLinearMap,
        modelWithCornersEuclideanHalfSpace_symm_apply, u.property,
        IccLeftChart_symm_apply_of_le (x := (0 : ℝ)) (y := 1) hu]
    · simp [ht, c, neckDiskChartLinearEquiv, neckDiskChartLinearMap,
        modelWithCornersEuclideanHalfSpace_symm_apply, u.property,
        IccLeftChart_symm_apply_of_le (x := (0 : ℝ)) (y := 1) hu]
  · let c : SphereHandleFirst :=
      coordinateUnlinkExteriorSmoothNeckDiskRaw 1
    apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
      contMDiff_coordinateUnlinkExteriorSmoothNeckDiskRaw.continuous.continuousAt
      neckDiskChartLinearEquiv
      (chartAt (EuclideanHalfSpace 1) t)
      (Homeomorph.pointReflection ((2 : ℝ)⁻¹ • c)).toOpenPartialHomeomorph
      (mem_chart_source _ t) (by simp [Homeomorph.pointReflection])
      (IsManifold.chart_mem_maximalAtlas t) ?_; swap
    · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      · have : ContDiff ℝ ∞
            ((fun v : SphereHandleFirst ↦ v + (2 : ℝ)⁻¹ • c) ∘
              fun y ↦ (2 : ℝ)⁻¹ • c - y) := by fun_prop
        simpa [contMDiffOn_iff_contDiffOn, contDiffOn_univ]
      · have : ContDiff ℝ ∞
            ((fun v : SphereHandleFirst ↦ -v + (2 : ℝ)⁻¹ • c) ∘
              fun y ↦ y - (2 : ℝ)⁻¹ • c) := by fun_prop
        simpa [contMDiffOn_iff_contDiffOn, contDiffOn_univ]
    intro z hz
    obtain ⟨⟨u, rfl⟩, hu⟩ :
        (∃ y, ⇑(modelWithCornersEuclideanHalfSpace 1) y = z) ∧
          ⇑(modelWithCornersEuclideanHalfSpace 1).symm z ∈
            (IccRightChart (0 : ℝ) 1).target := by
      simpa [ht] using! hz
    replace hu : WithLp.ofLp u.val 0 ≤ (1 : ℝ) - 0 := by
      have hu' : u ∈ (IccRightChart (0 : ℝ) 1).target := by
        simpa [modelWithCornersEuclideanHalfSpace_symm_apply,
          max_eq_left u.property] using hu
      change WithLp.ofLp u.val 0 < (1 : ℝ) - 0 at hu'
      exact hu'.le
    ext j
    fin_cases j
    · simp [ht, c, neckDiskChartLinearEquiv, neckDiskChartLinearMap,
        modelWithCornersEuclideanHalfSpace_symm_apply, u.property,
        IccRightChart_symm_apply_of_le (x := (0 : ℝ)) (y := 1) hu,
        Equiv.pointReflection_apply]
    · simp [ht, c, neckDiskChartLinearEquiv, neckDiskChartLinearMap,
        modelWithCornersEuclideanHalfSpace_symm_apply, u.property,
        IccRightChart_symm_apply_of_le (x := (0 : ℝ)) (y := 1) hu,
        Equiv.pointReflection_apply]
      linarith

/-- The affine interval diameter is injective. -/
theorem injective_coordinateUnlinkExteriorSmoothNeckDiskRaw :
    Function.Injective coordinateUnlinkExteriorSmoothNeckDiskRaw := by
  intro t u htu
  have hcoord := congrArg (fun v : SphereHandleFirst ↦ v 1) htu
  simp only [coordinateUnlinkExteriorSmoothNeckDiskRaw_apply_one] at hcoord
  apply Subtype.ext
  linarith

/-- The raw interval diameter is a topological embedding. -/
theorem isEmbedding_coordinateUnlinkExteriorSmoothNeckDiskRaw :
    IsEmbedding coordinateUnlinkExteriorSmoothNeckDiskRaw :=
  (contMDiff_coordinateUnlinkExteriorSmoothNeckDiskRaw.continuous.isClosedEmbedding
    injective_coordinateUnlinkExteriorSmoothNeckDiskRaw).isEmbedding

/-- The raw interval diameter is a smooth embedding for the closed-interval model. -/
theorem isSmoothEmbedding_coordinateUnlinkExteriorSmoothNeckDiskRaw :
    Manifold.IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf ℝ SphereHandleFirst) ∞
      coordinateUnlinkExteriorSmoothNeckDiskRaw :=
  ⟨isImmersionOfComplement_coordinateUnlinkExteriorSmoothNeckDiskRaw.isImmersion,
    isEmbedding_coordinateUnlinkExteriorSmoothNeckDiskRaw⟩

/-- Radial scaling from the unit cap disk to the actual normal-plane neck. -/
def neckNormalScaleEquiv : SphereHandleFirst ≃L[ℝ] SphereHandleFirst :=
  ContinuousLinearEquiv.smulLeft
    (Units.mk0 sphereHandleRadius sphereHandleRadius_ne_zero)

/-- The normal scaling equivalence acts by the sphere-handle radius. -/
@[simp]
theorem neckNormalScaleEquiv_apply (v : SphereHandleFirst) :
    neckNormalScaleEquiv v = sphereHandleRadius • v := rfl

/-- The actual normal-plane coordinate traced by the neck interval. -/
def coordinateUnlinkExteriorSmoothNeckNormalRaw
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) : UnlinkNormalPlane :=
  complexToUnlinkNormalPlane
    (coordinateUnlinkExteriorPlanarNeckBaseArc t + (1 / 2 : ℂ))

/-- The actual normal path is radial scaling of the raw cap-disk diameter. -/
theorem coordinateUnlinkExteriorSmoothNeckNormalRaw_eq :
    coordinateUnlinkExteriorSmoothNeckNormalRaw =
      neckNormalScaleEquiv ∘ coordinateUnlinkExteriorSmoothNeckDiskRaw := by
  funext t
  exact (sphereHandleRadius_smul_coordinateUnlinkExteriorSmoothNeckDiskRaw t).symm

/-- The actual normal-plane neck path is a smooth embedding. -/
theorem isSmoothEmbedding_coordinateUnlinkExteriorSmoothNeckNormalRaw :
    Manifold.IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf ℝ UnlinkNormalPlane) ∞
      coordinateUnlinkExteriorSmoothNeckNormalRaw := by
  rw [coordinateUnlinkExteriorSmoothNeckNormalRaw_eq]
  exact
    isSmoothEmbedding_coordinateUnlinkExteriorSmoothNeckDiskRaw.postcomp_diffeomorph_selfModels
      neckNormalScaleEquiv.toDiffeomorph neckNormalScaleEquiv

/-- The normal neck path bundled into the open unit normal disk. -/
def coordinateUnlinkExteriorSmoothNeckNormalDisk
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) : UnlinkUnitNormalDisk :=
  ⟨coordinateUnlinkExteriorSmoothNeckNormalRaw t, by
    change coordinateUnlinkExteriorSmoothNeckNormalRaw t ∈
      ball (0 : UnlinkNormalPlane) 1
    rw [mem_ball_zero_iff, coordinateUnlinkExteriorSmoothNeckNormalRaw,
      norm_complexToUnlinkNormalPlane]
    have hr : sphereHandleRadius < 1 := by
      rw [← sq_lt_sq₀ sphereHandleRadius_pos.le zero_le_one, sphereHandleRadius_sq]
      norm_num
    exact (norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_half_le t).trans_lt
      hr⟩

/-- Coercing the bundled normal-disk path recovers the raw normal coordinate. -/
@[simp]
theorem coordinateUnlinkExteriorSmoothNeckNormalDisk_val
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorSmoothNeckNormalDisk t : UnlinkNormalPlane) =
      coordinateUnlinkExteriorSmoothNeckNormalRaw t := rfl

/-- The bundled normal-disk path is continuous. -/
theorem continuous_coordinateUnlinkExteriorSmoothNeckNormalDisk :
    Continuous coordinateUnlinkExteriorSmoothNeckNormalDisk :=
  isSmoothEmbedding_coordinateUnlinkExteriorSmoothNeckNormalRaw.contMDiff.continuous.subtype_mk _

/-- Inclusion of the open unit normal disk is a local diffeomorphism. -/
theorem isLocalDiffeomorph_unlinkUnitNormalDisk_subtypeVal :
    IsLocalDiffeomorph (modelWithCornersSelf ℝ UnlinkNormalPlane)
      (modelWithCornersSelf ℝ UnlinkNormalPlane) ∞
      (Subtype.val : UnlinkUnitNormalDisk → UnlinkNormalPlane) := by
  let _ : Nonempty UnlinkUnitNormalDisk :=
    ⟨⟨0, mem_ball_self (by norm_num)⟩⟩
  let hOpen : IsOpenEmbedding
      (Subtype.val : UnlinkUnitNormalDisk → UnlinkNormalPlane) :=
    isOpen_ball.isOpenEmbedding_subtypeVal
  let oph : OpenPartialHomeomorph UnlinkUnitNormalDisk UnlinkNormalPlane :=
    hOpen.toOpenPartialHomeomorph Subtype.val
  let phi : PartialDiffeomorph
      (modelWithCornersSelf ℝ UnlinkNormalPlane)
      (modelWithCornersSelf ℝ UnlinkNormalPlane)
      UnlinkUnitNormalDisk UnlinkNormalPlane ∞ := {
    toPartialEquiv := oph.toPartialEquiv
    open_source := oph.open_source
    open_target := oph.open_target
    contMDiffOn_toFun := by
      simpa [oph, hOpen] using
        (contMDiff_subtype_val : ContMDiff
          (modelWithCornersSelf ℝ UnlinkNormalPlane)
          (modelWithCornersSelf ℝ UnlinkNormalPlane) ∞
          (Subtype.val : UnlinkUnitNormalDisk → UnlinkNormalPlane)).contMDiffOn
    contMDiffOn_invFun := by
      intro y hy
      apply (ContMDiffWithinAt.subtypeVal_comp_iff unlinkUnitNormalDisk
        oph.symm oph.target y).mp
      apply contMDiffWithinAt_id.congr
      · intro z hz
        exact oph.right_inv hz
      · exact oph.right_inv hy
  }
  intro x
  have hx : x ∈ phi.source := by
    change x ∈ oph.source
    simp [oph]
  simpa [phi, oph] using
    (phi.isLocalDiffeomorphAt
      (modelWithCornersSelf ℝ UnlinkNormalPlane)
      (modelWithCornersSelf ℝ UnlinkNormalPlane) ∞ hx)

/-- The neck interval embeds smoothly into the open unit normal disk. -/
theorem isSmoothEmbedding_coordinateUnlinkExteriorSmoothNeckNormalDisk :
    Manifold.IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf ℝ UnlinkNormalPlane) ∞
      coordinateUnlinkExteriorSmoothNeckNormalDisk := by
  apply Manifold.IsSmoothEmbedding.reflect_isLocalDiffeomorph
    isLocalDiffeomorph_unlinkUnitNormalDisk_subtypeVal
    continuous_coordinateUnlinkExteriorSmoothNeckNormalDisk
  simpa [Function.comp_def] using
    isSmoothEmbedding_coordinateUnlinkExteriorSmoothNeckNormalRaw

private def sphereOpenSubtypePartialDiffeomorph
    (s : TopologicalSpace.Opens (Sphere 4)) [Nonempty s] :
    PartialDiffeomorph
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      s (Sphere 4) ∞ := by
  let hOpen : IsOpenEmbedding (Subtype.val : s → Sphere 4) :=
    s.2.isOpenEmbedding_subtypeVal
  let oph : OpenPartialHomeomorph s (Sphere 4) :=
    hOpen.toOpenPartialHomeomorph Subtype.val
  exact {
    toPartialEquiv := oph.toPartialEquiv
    open_source := oph.open_source
    open_target := oph.open_target
    contMDiffOn_toFun := by
      simpa [oph] using
        (contMDiff_subtype_val : ContMDiff
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
          (Subtype.val : s → Sphere 4)).contMDiffOn
    contMDiffOn_invFun := by
      intro y hy
      apply (ContMDiffWithinAt.subtypeVal_comp_iff s oph.symm oph.target y).mp
      apply contMDiffWithinAt_id.congr
      · intro z hz
        exact oph.right_inv hz
      · exact oph.right_inv hy
  }

private theorem isLocalDiffeomorph_sphereOpenSubtypeVal
    (s : TopologicalSpace.Opens (Sphere 4)) :
    IsLocalDiffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (Subtype.val : s → Sphere 4) := by
  intro x
  let _ : Nonempty s := ⟨x⟩
  let phi : PartialDiffeomorph
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      s (Sphere 4) ∞ := sphereOpenSubtypePartialDiffeomorph s
  have hx : x ∈ phi.source := by
    simp [phi, sphereOpenSubtypePartialDiffeomorph]
  simpa [phi, sphereOpenSubtypePartialDiffeomorph] using
    (phi.isLocalDiffeomorphAt
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞ hx)

private theorem isSmoothEmbedding_postcomp_sphereOpenSubtypeVal
    (s : TopologicalSpace.Opens (Sphere 4))
    {f : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2 → s}
    (hf : Manifold.IsSmoothEmbedding
      coordinateUnlinkExteriorSmoothNeckCylinderModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞ f) :
    Manifold.IsSmoothEmbedding
      coordinateUnlinkExteriorSmoothNeckCylinderModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      ((Subtype.val : s → Sphere 4) ∘ f) := by
  refine ⟨?_, IsEmbedding.subtypeVal.comp hf.isEmbedding⟩
  refine (show Manifold.IsImmersionOfComplement hf.isImmersion.complement
      coordinateUnlinkExteriorSmoothNeckCylinderModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      ((Subtype.val : s → Sphere 4) ∘ f) from ?_).isImmersion
  intro x
  let _ : Nonempty s := ⟨f x⟩
  let e := sphereOpenSubtypePartialDiffeomorph s
  have he : f x ∈ e.source := by
    simp [e, sphereOpenSubtypePartialDiffeomorph]
  have hpost :=
    (hf.isImmersion.isImmersionOfComplement_complement x).postcomp_partialDiffeomorph
      e he
  simpa [e, sphereOpenSubtypePartialDiffeomorph, Function.comp_def] using hpost

/-- Crossing the normal path with `S²` and applying polar coordinates is a smooth embedding. -/
theorem isSmoothEmbedding_coordinateUnlinkExteriorSmoothNeckPolarProduct :
    Manifold.IsSmoothEmbedding coordinateUnlinkExteriorSmoothNeckCylinderModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (spherePolarDiffeomorph ∘ fun
        x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2 ↦
          (x.2, coordinateUnlinkExteriorSmoothNeckNormalDisk x.1)) := by
  let productCharted :
      ChartedSpace
      (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)))
      (Sphere 2 × UnlinkUnitNormalDisk) := inferInstance
  let _ : ChartedSpace
      (UnlinkNormalPlane × EuclideanSpace ℝ (Fin 2))
      (Sphere 2 × UnlinkUnitNormalDisk) := productCharted
  let productManifold : IsManifold
      ((modelWithCornersSelf ℝ UnlinkNormalPlane).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))) ∞
      (Sphere 2 × UnlinkUnitNormalDisk) := inferInstance
  let _ : IsManifold
      (modelWithCornersSelf ℝ
        (UnlinkNormalPlane × EuclideanSpace ℝ (Fin 2))) ∞
      (Sphere 2 × UnlinkUnitNormalDisk) := by
    rw [modelWithCornersSelf_prod]
    exact productManifold
  have hprod :=
    isSmoothEmbedding_coordinateUnlinkExteriorSmoothNeckNormalDisk.prodMap
      (Manifold.IsSmoothEmbedding.id
        (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (n := ∞) (M := Sphere 2))
  have hswap := hprod.postcomp_diffeomorph
    (Diffeomorph.prodComm
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      UnlinkUnitNormalDisk (Sphere 2) ∞)
  change Manifold.IsSmoothEmbedding
    ((modelWithCornersEuclideanHalfSpace 1).prod
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
    ((modelWithCornersSelf ℝ UnlinkNormalPlane).prod
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))) ∞
    (fun x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2 =>
      (x.2, coordinateUnlinkExteriorSmoothNeckNormalDisk x.1)) at hswap
  rw [← modelWithCornersSelf_prod] at hswap
  let ePolar :
      (Sphere 2 × UnlinkUnitNormalDisk) ≃ₘ^∞⟮
        modelWithCornersSelf ℝ
          (UnlinkNormalPlane × EuclideanSpace ℝ (Fin 2)),
        modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))⟯
        SpherePolarRegion := {
    toEquiv := spherePolarDiffeomorph.toEquiv
    contMDiff_toFun := by
      rw [modelWithCornersSelf_prod]
      exact spherePolarDiffeomorph.contMDiff
    contMDiff_invFun := by
      rw [modelWithCornersSelf_prod]
      exact spherePolarDiffeomorph.symm.contMDiff
  }
  have hfinal := hswap.postcomp_diffeomorph_selfModels
    ePolar
    (EuclideanSpace.finAddEquivProd (n := 2) (m := 2)).symm
  have hePolar (p : Sphere 2 × UnlinkUnitNormalDisk) :
      ePolar p = spherePolarDiffeomorph p := by
    rfl
  have heq :
      (fun x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2 =>
        ePolar (x.2, coordinateUnlinkExteriorSmoothNeckNormalDisk x.1)) =
      (spherePolarDiffeomorph ∘ fun x =>
        (x.2, coordinateUnlinkExteriorSmoothNeckNormalDisk x.1)) := by
    funext x
    exact hePolar _
  exact heq ▸ hfinal

/-- The polar scale along the neck agrees with the sphere-handle cap scale. -/
theorem spherePolarScale_smoothNeckNormalDisk
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    spherePolarScale (coordinateUnlinkExteriorSmoothNeckNormalDisk t).1 =
      sphereHandleScale ‖coordinateUnlinkExteriorSmoothNeckDiskRaw t‖ := by
  unfold spherePolarScale sphereHandleScale
  congr 1
  rw [coordinateUnlinkExteriorSmoothNeckNormalDisk_val,
    show coordinateUnlinkExteriorSmoothNeckNormalRaw t =
      sphereHandleRadius • coordinateUnlinkExteriorSmoothNeckDiskRaw t by
        exact (sphereHandleRadius_smul_coordinateUnlinkExteriorSmoothNeckDiskRaw t).symm,
    norm_smul, Real.norm_eq_abs, abs_of_pos sphereHandleRadius_pos]
  ring

/-- The polar-product cylinder is exactly the aligned cap-face cylinder in `S⁴`. -/
theorem spherePolarForward_smoothNeckNormalDisk
    (x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2) :
    ((spherePolarForward
      (x.2, coordinateUnlinkExteriorSmoothNeckNormalDisk x.1) :
        SpherePolarRegion) : Sphere 4) =
      unlinkAlignedCapSphereMap
        (coordinateUnlinkExteriorSmoothNeckDisk x.1, x.2) := by
  apply Subtype.ext
  apply unlinkAlignedSplitEquiv.injective
  apply Prod.ext
  · rw [unlinkAlignedSplitEquiv_fst,
      standardUnlinkNormalProjection_spherePolarForward,
      unlinkAlignedSplitEquiv_capSphereMap]
    exact (sphereHandleRadius_smul_coordinateUnlinkExteriorSmoothNeckDiskRaw x.1).symm
  · rw [unlinkAlignedSplitEquiv_snd,
      unlinkAlignedSplitEquiv_capSphereMap]
    change spherePolarSourceProjection
        (spherePolarForward (x.2,
          coordinateUnlinkExteriorSmoothNeckNormalDisk x.1)) =
      sphereHandleScale ‖coordinateUnlinkExteriorSmoothNeckDiskRaw x.1‖ • x.2.1
    rw [spherePolarSourceProjection_spherePolarForward,
      spherePolarScale_smoothNeckNormalDisk]

/-- The literal neck cylinder in the strict unlink complement is a smooth embedding. -/
theorem isSmoothEmbedding_coordinateUnlinkExteriorSmoothNeckCylinderBase :
    Manifold.IsSmoothEmbedding coordinateUnlinkExteriorSmoothNeckCylinderModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      coordinateUnlinkExteriorSmoothNeckCylinderBase := by
  have hSphere := isSmoothEmbedding_postcomp_sphereOpenSubtypeVal spherePolarRegion
    isSmoothEmbedding_coordinateUnlinkExteriorSmoothNeckPolarProduct
  have heq :
      ((Subtype.val : SpherePolarRegion → Sphere 4) ∘
        (spherePolarDiffeomorph ∘ fun
          x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2 ↦
            (x.2, coordinateUnlinkExteriorSmoothNeckNormalDisk x.1))) =
      ((Subtype.val : StandardUnlinkComplement → Sphere 4) ∘
        coordinateUnlinkExteriorSmoothNeckCylinderBase) := by
    funext x
    exact (spherePolarForward_smoothNeckNormalDisk x).trans
      (coordinateUnlinkExteriorSmoothNeckCylinderBase_coe x).symm
  have hBaseCoe : Manifold.IsSmoothEmbedding
      coordinateUnlinkExteriorSmoothNeckCylinderModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      ((Subtype.val : StandardUnlinkComplement → Sphere 4) ∘
        coordinateUnlinkExteriorSmoothNeckCylinderBase) := heq ▸ hSphere
  apply Manifold.IsSmoothEmbedding.reflect_isLocalDiffeomorph
    (isLocalDiffeomorph_sphereOpenSubtypeVal standardUnlinkComplementOpens)
    continuous_coordinateUnlinkExteriorSmoothNeckCylinderBase
  exact hBaseCoe

/-- The literal strict-complement neck cylinder as a bundled smooth embedding. -/
def coordinateUnlinkExteriorSmoothNeckCylinderBaseEmbedding :
    TauCeti.SmoothEmbedding coordinateUnlinkExteriorSmoothNeckCylinderModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2)
      StandardUnlinkComplement :=
  TauCeti.SmoothEmbedding.ofIsSmoothEmbedding
    coordinateUnlinkExteriorSmoothNeckCylinderBase
      isSmoothEmbedding_coordinateUnlinkExteriorSmoothNeckCylinderBase

/-- Exact action of the bundled base-cylinder embedding. -/
@[simp]
theorem coordinateUnlinkExteriorSmoothNeckCylinderBaseEmbedding_apply
    (x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2) :
    coordinateUnlinkExteriorSmoothNeckCylinderBaseEmbedding x =
      coordinateUnlinkExteriorSmoothNeckCylinderBase x := by
  exact TauCeti.SmoothEmbedding.ofIsSmoothEmbedding_apply _ _ x

/-- Every fixed deck-labelled lift is a smooth embedding in the pulled-back atlas. -/
theorem isSmoothEmbedding_coordinateUnlinkExteriorSmoothNeckCylinderLift
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    Manifold.IsSmoothEmbedding coordinateUnlinkExteriorSmoothNeckCylinderModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (coordinateUnlinkExteriorSmoothNeckCylinderLift m a) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  apply Manifold.IsSmoothEmbedding.reflect_isLocalDiffeomorph
    (smoothCover_standardUnlinkPowerPullbackProj m).isLocalDiffeomorph
    (continuous_coordinateUnlinkExteriorSmoothNeckCylinderLift m a)
  have heq :
      (standardUnlinkPowerPullbackProj m ∘
        coordinateUnlinkExteriorSmoothNeckCylinderLift m a) =
      coordinateUnlinkExteriorSmoothNeckCylinderBase := by
    funext x
    exact coordinateUnlinkExteriorSmoothNeckCylinderLift_proj m a x
  rw [heq]
  exact isSmoothEmbedding_coordinateUnlinkExteriorSmoothNeckCylinderBase

/-- A fixed deck-labelled lifted cylinder as a bundled smooth embedding. -/
def coordinateUnlinkExteriorSmoothNeckCylinderLiftEmbedding
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    TauCeti.SmoothEmbedding coordinateUnlinkExteriorSmoothNeckCylinderModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2)
      (StandardUnlinkPowerPullback m) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  exact TauCeti.SmoothEmbedding.ofIsSmoothEmbedding
    (coordinateUnlinkExteriorSmoothNeckCylinderLift m a)
      (isSmoothEmbedding_coordinateUnlinkExteriorSmoothNeckCylinderLift m a)

/-- Exact action of the bundled fixed-label lifted-cylinder embedding. -/
@[simp]
theorem coordinateUnlinkExteriorSmoothNeckCylinderLiftEmbedding_apply
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    coordinateUnlinkExteriorSmoothNeckCylinderLiftEmbedding m a x =
      coordinateUnlinkExteriorSmoothNeckCylinderLift m a x := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  exact TauCeti.SmoothEmbedding.ofIsSmoothEmbedding_apply _ _ x

end SplittingSpheres
