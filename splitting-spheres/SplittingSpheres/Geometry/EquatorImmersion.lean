/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import SplittingSpheres.Geometry.StandardUnlink

/-!
# The coordinate equator is a smooth immersion

This file works directly with Mathlib's local-normal-form definition of an immersion.  The
stereographic charts at corresponding antipodes intertwine the coordinate equator inclusion with
a linear inclusion of tangent hyperplanes; adjoining the missing coordinate gives the required
linear equivalence in the immersion chart.
-/

@[expose] public section

open Metric Set Topology
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace SplittingSpheres

/-- The unit coordinate normal to the equator `x₃ = 0`. -/
def equatorNormal : EuclideanSpace ℝ (Fin 5) :=
  EuclideanSpace.single 3 1

@[simp]
theorem equatorNormal_apply (i : Fin 5) :
    equatorNormal i = if i = 3 then 1 else 0 := by
  simp [equatorNormal]

@[simp]
theorem equatorNormal_apply_three : equatorNormal 3 = 1 := by
  simp

theorem inner_equatorNormal_equatorAmbientMap
    (u : EuclideanSpace ℝ (Fin 4)) :
    ⟪equatorNormal, equatorAmbientMap u⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]
  simp [equatorNormal, equatorAmbientMap]

theorem inner_equatorAmbientMap_equatorNormal
    (u : EuclideanSpace ℝ (Fin 4)) :
    ⟪equatorAmbientMap u, equatorNormal⟫_ℝ = 0 := by
  rw [real_inner_comm]
  exact inner_equatorNormal_equatorAmbientMap u

/-- Orthogonal projection to the complement of a unit vector, in an explicit form. -/
theorem coe_orthogonalProjectionOnto_span_orthogonal_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (v w : E) (hv : ‖v‖ = 1) :
    (((ℝ ∙ v)ᗮ.orthogonalProjectionOnto w : (ℝ ∙ v)ᗮ) : E) =
      w - ⟪v, w⟫_ℝ • v := by
  rw [← Submodule.starProjection_apply]
  have hsplit := (ℝ ∙ v).starProjection_add_starProjection_orthogonal w
  rw [Submodule.starProjection_unit_singleton ℝ hv w] at hsplit
  exact eq_sub_of_add_eq (by simpa [add_comm] using hsplit)

@[simp]
theorem equatorSphereMap_neg (x : Sphere 3) :
    equatorSphereMap (-x) = -(equatorSphereMap x) := by
  apply Subtype.ext
  exact map_neg equatorLinearIsometry (x : EuclideanSpace ℝ (Fin 4))

/-- Stereographic projection at corresponding antipodes commutes with coordinate insertion. -/
theorem coe_stereoToFun_equator (x z : Sphere 3) :
    ((stereoToFun
      (-((equatorSphereMap x : Sphere 4) : EuclideanSpace ℝ (Fin 5)))
      ((equatorSphereMap z : Sphere 4) : EuclideanSpace ℝ (Fin 5)) :
        (ℝ ∙ (-((equatorSphereMap x : Sphere 4) :
          EuclideanSpace ℝ (Fin 5))))ᗮ) : EuclideanSpace ℝ (Fin 5)) =
      equatorLinearIsometry
        ((stereoToFun (-(x : EuclideanSpace ℝ (Fin 4)))
          (z : EuclideanSpace ℝ (Fin 4)) :
            (ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 4))))ᗮ) :
              EuclideanSpace ℝ (Fin 4)) := by
  rw [stereoToFun_apply, stereoToFun_apply]
  change
    (2 / (1 - ⟪-((equatorSphereMap x : Sphere 4) :
      EuclideanSpace ℝ (Fin 5)),
        ((equatorSphereMap z : Sphere 4) : EuclideanSpace ℝ (Fin 5))⟫_ℝ)) •
      ((((ℝ ∙ (-((equatorSphereMap x : Sphere 4) :
        EuclideanSpace ℝ (Fin 5))))ᗮ).orthogonalProjectionOnto
          ((equatorSphereMap z : Sphere 4) : EuclideanSpace ℝ (Fin 5)) :
            (ℝ ∙ (-((equatorSphereMap x : Sphere 4) :
              EuclideanSpace ℝ (Fin 5))))ᗮ) : EuclideanSpace ℝ (Fin 5)) =
    equatorLinearIsometry
      ((2 / (1 - ⟪-(x : EuclideanSpace ℝ (Fin 4)),
        (z : EuclideanSpace ℝ (Fin 4))⟫_ℝ)) •
        ((((ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 4))))ᗮ).orthogonalProjectionOnto
          (z : EuclideanSpace ℝ (Fin 4)) :
            (ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 4))))ᗮ) :
              EuclideanSpace ℝ (Fin 4)))
  have htargetNorm :
      ‖-((equatorSphereMap x : Sphere 4) : EuclideanSpace ℝ (Fin 5))‖ = 1 := by
    simpa using norm_eq_of_mem_sphere (equatorSphereMap x)
  have hsourceNorm : ‖-(x : EuclideanSpace ℝ (Fin 4))‖ = 1 := by
    simp
  rw [coe_orthogonalProjectionOnto_span_orthogonal_apply _ _ htargetNorm,
    coe_orthogonalProjectionOnto_span_orthogonal_apply _ _ hsourceNorm]
  have hpole :
      -((equatorSphereMap x : Sphere 4) : EuclideanSpace ℝ (Fin 5)) =
        equatorLinearIsometry (-(x : EuclideanSpace ℝ (Fin 4))) := by
    simpa using (map_neg equatorLinearIsometry
      (x : EuclideanSpace ℝ (Fin 4))).symm
  have hpoint :
      ((equatorSphereMap z : Sphere 4) : EuclideanSpace ℝ (Fin 5)) =
        equatorLinearIsometry (z : EuclideanSpace ℝ (Fin 4)) := rfl
  rw [hpole, hpoint, LinearIsometry.inner_map_map]
  simp only [map_smul, map_sub]

/-- The linear map which adjoins the equatorial normal direction to the tangent hyperplane. -/
def equatorTangentSumLinearMap (x : Sphere 3) :
    ((ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 4))))ᗮ × ℝ) →ₗ[ℝ]
      (ℝ ∙ (-((equatorSphereMap x : Sphere 4) :
        EuclideanSpace ℝ (Fin 5))))ᗮ where
  toFun p := ⟨equatorLinearIsometry p.1.1 + p.2 • equatorNormal, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have hp : ⟪-(x : EuclideanSpace ℝ (Fin 4)), p.1.1⟫_ℝ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp p.1.2
    have hpole :
        -((equatorSphereMap x : Sphere 4) : EuclideanSpace ℝ (Fin 5)) =
          equatorLinearIsometry (-(x : EuclideanSpace ℝ (Fin 4))) := by
      simpa using (map_neg equatorLinearIsometry (x : EuclideanSpace ℝ (Fin 4))).symm
    rw [hpole, inner_add_right, inner_smul_right, LinearIsometry.inner_map_map, hp]
    simp [equatorLinearIsometry_apply, inner_equatorAmbientMap_equatorNormal]⟩
  map_add' p q := by
    apply Subtype.ext
    change equatorLinearIsometry (p.1.1 + q.1.1) + (p.2 + q.2) • equatorNormal =
      (equatorLinearIsometry p.1.1 + p.2 • equatorNormal) +
        (equatorLinearIsometry q.1.1 + q.2 • equatorNormal)
    rw [map_add, add_smul]
    abel
  map_smul' c p := by
    apply Subtype.ext
    change equatorLinearIsometry (c • p.1.1) + (c * p.2) • equatorNormal =
      c • (equatorLinearIsometry p.1.1 + p.2 • equatorNormal)
    rw [map_smul, smul_add, mul_smul]

theorem equatorTangentSumLinearMap_injective (x : Sphere 3) :
    Function.Injective (equatorTangentSumLinearMap x) := by
  intro p q hpq
  have hpqVal := congrArg Subtype.val hpq
  change equatorLinearIsometry p.1.1 + p.2 • equatorNormal =
    equatorLinearIsometry q.1.1 + q.2 • equatorNormal at hpqVal
  have hpqThree := congrArg (fun z : EuclideanSpace ℝ (Fin 5) ↦ z 3) hpqVal
  have hscalar : p.2 = q.2 := by
    simpa [equatorNormal] using hpqThree
  have htangentMap : equatorLinearIsometry p.1.1 = equatorLinearIsometry q.1.1 := by
    rw [hscalar] at hpqVal
    exact add_right_cancel hpqVal
  have htangent : p.1 = q.1 :=
    Subtype.ext (equatorLinearIsometry.injective htangentMap)
  exact Prod.ext htangent hscalar

theorem finrank_equatorSourceTangent (x : Sphere 3) :
    Module.finrank ℝ ((ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 4))))ᗮ) = 3 := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  exact Submodule.finrank_orthogonal_span_singleton
    (n := 3) (ne_zero_of_mem_unit_sphere (-x))

theorem finrank_equatorTargetTangent (x : Sphere 3) :
    Module.finrank ℝ
      ((ℝ ∙ (-((equatorSphereMap x : Sphere 4) :
        EuclideanSpace ℝ (Fin 5))))ᗮ) = 4 := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) := ⟨by simp⟩
  exact Submodule.finrank_orthogonal_span_singleton
    (n := 4) (ne_zero_of_mem_unit_sphere (-(equatorSphereMap x)))

theorem finrank_equatorTangentSum_eq (x : Sphere 3) :
    Module.finrank ℝ
      (((ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 4))))ᗮ) × ℝ) =
    Module.finrank ℝ
      ((ℝ ∙ (-((equatorSphereMap x : Sphere 4) :
        EuclideanSpace ℝ (Fin 5))))ᗮ) := by
  rw [Module.finrank_prod, finrank_equatorSourceTangent, finrank_equatorTargetTangent]
  norm_num

/-- The tangent-hyperplane sum map as a continuous linear equivalence. -/
def equatorTangentSumEquiv (x : Sphere 3) :
    (((ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 4))))ᗮ) × ℝ) ≃L[ℝ]
      ((ℝ ∙ (-((equatorSphereMap x : Sphere 4) :
        EuclideanSpace ℝ (Fin 5))))ᗮ) :=
  ((equatorTangentSumLinearMap x).linearEquivOfInjective
    (equatorTangentSumLinearMap_injective x)
    (finrank_equatorTangentSum_eq x)).toContinuousLinearEquiv

@[simp]
theorem equatorTangentSumEquiv_apply (x : Sphere 3)
    (p : ((ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 4))))ᗮ) × ℝ) :
    equatorTangentSumEquiv x p = equatorTangentSumLinearMap x p := rfl

/-- The orthonormal coordinates used by Mathlib's preferred chart on the source sphere. -/
def equatorSourceTangentRepr (x : Sphere 3) :
    ((ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 4))))ᗮ) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin 3) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  exact (OrthonormalBasis.fromOrthogonalSpanSingleton
    (𝕜 := ℝ) 3 (ne_zero_of_mem_unit_sphere (-x))).repr

/-- The orthonormal coordinates used by Mathlib's preferred chart on the target sphere. -/
def equatorTargetTangentRepr (x : Sphere 3) :
    ((ℝ ∙ (-((equatorSphereMap x : Sphere 4) :
      EuclideanSpace ℝ (Fin 5))))ᗮ) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin 4) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) := ⟨by simp⟩
  exact (OrthonormalBasis.fromOrthogonalSpanSingleton
    (𝕜 := ℝ) 4 (ne_zero_of_mem_unit_sphere (-(equatorSphereMap x)))).repr

/-- In preferred stereographic coordinates, the coordinate equator has a complementary normal
coordinate. -/
def equatorChartLinearEquiv (x : Sphere 3) :
    (EuclideanSpace ℝ (Fin 3) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  ((((equatorSourceTangentRepr x).symm.toContinuousLinearEquiv.prodCongr
      (ContinuousLinearEquiv.refl ℝ ℝ)).trans
    (equatorTangentSumEquiv x)).trans
    (equatorTargetTangentRepr x).toContinuousLinearEquiv)

@[simp]
theorem equatorChartLinearEquiv_apply (x : Sphere 3)
    (p : EuclideanSpace ℝ (Fin 3) × ℝ) :
    equatorChartLinearEquiv x p =
      equatorTargetTangentRepr x
        (equatorTangentSumLinearMap x
          ((equatorSourceTangentRepr x).symm p.1, p.2)) := rfl

section PreferredCharts

local instance equatorSourceFinrankFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (3 + 1))) = 3 + 1) := ⟨by simp⟩

local instance equatorTargetFinrankFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (4 + 1))) = 4 + 1) := ⟨by simp⟩

/-- In the preferred stereographic charts, the equator is exactly the zero-normal slice of
`equatorChartLinearEquiv`. -/
theorem stereographic'_equator (x z : Sphere 3) :
    stereographic' 4 (-(equatorSphereMap x)) (equatorSphereMap z) =
      equatorChartLinearEquiv x (stereographic' 3 (-x) z, 0) := by
  change
    equatorTargetTangentRepr x
      (stereoToFun
        (-((equatorSphereMap x : Sphere 4) : EuclideanSpace ℝ (Fin 5)))
        ((equatorSphereMap z : Sphere 4) : EuclideanSpace ℝ (Fin 5))) =
    equatorTargetTangentRepr x
      (equatorTangentSumLinearMap x
        ((equatorSourceTangentRepr x).symm
          (equatorSourceTangentRepr x
            (stereoToFun (-(x : EuclideanSpace ℝ (Fin 4)))
              (z : EuclideanSpace ℝ (Fin 4)))), 0))
  rw [LinearIsometryEquiv.symm_apply_apply]
  congr 1
  apply Subtype.ext
  change
    ((stereoToFun
      (-((equatorSphereMap x : Sphere 4) : EuclideanSpace ℝ (Fin 5)))
      ((equatorSphereMap z : Sphere 4) : EuclideanSpace ℝ (Fin 5)) :
        (ℝ ∙ (-((equatorSphereMap x : Sphere 4) :
          EuclideanSpace ℝ (Fin 5))))ᗮ) : EuclideanSpace ℝ (Fin 5)) =
    equatorLinearIsometry
      ((stereoToFun (-(x : EuclideanSpace ℝ (Fin 4)))
        (z : EuclideanSpace ℝ (Fin 4)) :
          (ℝ ∙ (-(x : EuclideanSpace ℝ (Fin 4))))ᗮ) :
            EuclideanSpace ℝ (Fin 4)) + (0 : ℝ) • equatorNormal
  simpa using coe_stereoToFun_equator x z

end PreferredCharts

/-- The coordinate equator is an immersion with the missing coordinate as a global
one-dimensional complement. -/
theorem isImmersionOfComplement_equatorSphereMap :
    Manifold.IsImmersionOfComplement ℝ (𝓡 3) (𝓡 4) ∞ equatorSphereMap := by
  intro x
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    contMDiff_equatorSphereMap.continuous.continuousAt (equatorChartLinearEquiv x)
    (chartAt (EuclideanSpace ℝ (Fin 3)) x)
    (chartAt (EuclideanSpace ℝ (Fin 4)) (equatorSphereMap x))
    (mem_chart_source _ x) (mem_chart_source _ (equatorSphereMap x))
    (IsManifold.chart_mem_maximalAtlas x)
    (IsManifold.chart_mem_maximalAtlas (equatorSphereMap x))
  intro u hu
  rw [OpenPartialHomeomorph.extend_target] at hu
  have huTarget :
      u ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) x).target := by
    simpa only [modelWithCornersSelf_coe_symm, preimage_id_eq, id_eq] using hu.1
  simp only [Function.comp_apply, mfld_simps]
  calc
    _ = equatorChartLinearEquiv x
        ((chartAt (EuclideanSpace ℝ (Fin 3)) x
          ((chartAt (EuclideanSpace ℝ (Fin 3)) x).symm u)), 0) :=
      stereographic'_equator x
        ((chartAt (EuclideanSpace ℝ (Fin 3)) x).symm u)
    _ = _ := by rw [(chartAt (EuclideanSpace ℝ (Fin 3)) x).right_inv huTarget]

/-- The coordinate equator is a smooth immersion, proved from the local normal-form definition. -/
theorem isImmersion_equatorSphereMap :
    Manifold.IsImmersion (𝓡 3) (𝓡 4) ∞ equatorSphereMap :=
  isImmersionOfComplement_equatorSphereMap.isImmersion

/-- The coordinate equator, bundled as a smooth embedding of `S³` in `S⁴`. -/
def standardSplittingSphere : SmoothSphereEmbedding 3 4 :=
  TauCeti.SmoothEmbedding.ofIsSmoothEmbedding equatorSphereMap
    ⟨isImmersion_equatorSphereMap, isEmbedding_equatorSphereMap⟩

@[simp]
theorem standardSplittingSphere_apply (x : Sphere 3) :
    standardSplittingSphere x = equatorSphereMap x := by
  simp [standardSplittingSphere]

/-- The bundled coordinate embedding has exactly the coordinate equator as its image. -/
theorem range_standardSplittingSphere :
    range standardSplittingSphere = coordinateEquator := by
  have hfun : (standardSplittingSphere : Sphere 3 → Sphere 4) = equatorSphereMap := by
    funext x
    exact standardSplittingSphere_apply x
  rw [hfun]
  exact range_equatorSphereMap

/-- The bundled coordinate equator separates the two standard unlink components. -/
theorem isSplittingSphere_standardSplittingSphere :
    IsSplittingSphere standardSplittingSphere := by
  rw [IsSplittingSphere, range_standardSplittingSphere]
  exact separates_coordinateEquator

end SplittingSpheres
