/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Order.IntermediateValue
public import SplittingSpheres.Statement

/-!
# The coordinate splitting sphere for the standard unlink

This file develops the elementary coordinate geometry of the equatorial `3`-sphere
`x₃ = 0` in `S⁴`.  In particular, it proves directly that this equator separates the two
round components used in `standardUnlinkComponent`.
-/

@[expose] public section

open Metric Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-- Insert a zero as coordinate `3` of a vector in `ℝ⁴`. -/
def equatorAmbientMap (x : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 ![x 0, x 1, x 2, 0, x 3]

@[simp]
theorem equatorAmbientMap_apply_zero (x : EuclideanSpace ℝ (Fin 4)) :
    equatorAmbientMap x 0 = x 0 := rfl

@[simp]
theorem equatorAmbientMap_apply_one (x : EuclideanSpace ℝ (Fin 4)) :
    equatorAmbientMap x 1 = x 1 := rfl

@[simp]
theorem equatorAmbientMap_apply_two (x : EuclideanSpace ℝ (Fin 4)) :
    equatorAmbientMap x 2 = x 2 := rfl

@[simp]
theorem equatorAmbientMap_apply_three (x : EuclideanSpace ℝ (Fin 4)) :
    equatorAmbientMap x 3 = 0 := rfl

@[simp]
theorem equatorAmbientMap_apply_four (x : EuclideanSpace ℝ (Fin 4)) :
    equatorAmbientMap x 4 = x 3 := rfl

theorem norm_equatorAmbientMap (x : EuclideanSpace ℝ (Fin 4)) :
    ‖equatorAmbientMap x‖ = ‖x‖ := by
  have hsq : ‖equatorAmbientMap x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, equatorAmbientMap, Fin.sum_univ_succ]
  nlinarith [norm_nonneg (equatorAmbientMap x), norm_nonneg x]

/-- The coordinate insertion as a linear isometry. -/
def equatorLinearIsometry :
    EuclideanSpace ℝ (Fin 4) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 5) where
  toFun := equatorAmbientMap
  map_add' x y := by
    ext i
    fin_cases i <;> simp [equatorAmbientMap]
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [equatorAmbientMap]
  norm_map' := norm_equatorAmbientMap

@[simp]
theorem equatorLinearIsometry_apply (x : EuclideanSpace ℝ (Fin 4)) :
    equatorLinearIsometry x = equatorAmbientMap x := rfl

/-- The raw coordinate parametrization of the equator `x₃ = 0` in `S⁴`. -/
def equatorSphereMap (x : Sphere 3) : Sphere 4 :=
  ⟨equatorAmbientMap x.1, by
    simpa [mem_sphere_zero_iff_norm, norm_equatorAmbientMap] using x.2⟩

@[simp]
theorem equatorSphereMap_coe (x : Sphere 3) :
    (equatorSphereMap x).1 = equatorAmbientMap x.1 := rfl

theorem isometry_equatorSphereMap : Isometry equatorSphereMap := by
  intro x y
  change edist (equatorLinearIsometry x.1) (equatorLinearIsometry y.1) = edist x.1 y.1
  exact equatorLinearIsometry.isometry.edist_eq x.1 y.1

theorem isEmbedding_equatorSphereMap : IsEmbedding equatorSphereMap :=
  isometry_equatorSphereMap.isEmbedding

theorem contMDiff_equatorSphereMap :
    ContMDiff (𝓡 3) (𝓡 4) ∞ equatorSphereMap := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) := ⟨by simp⟩
  have h : ContMDiff (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5))) ∞
      (fun x : Sphere 3 ↦ equatorLinearIsometry (x : EuclideanSpace ℝ (Fin 4))) :=
    equatorLinearIsometry.contDiff.comp_contMDiff contMDiff_coe_sphere
  exact (h.codRestrict_sphere (n := 4) fun x ↦ (equatorSphereMap x).2).congr fun _ ↦ rfl

/-- Delete coordinate `3` from a vector in `ℝ⁵`. -/
def equatorAmbientProjection (y : EuclideanSpace ℝ (Fin 5)) :
    EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![y 0, y 1, y 2, y 4]

@[simp]
theorem equatorAmbientProjection_apply_zero (y : EuclideanSpace ℝ (Fin 5)) :
    equatorAmbientProjection y 0 = y 0 := rfl

@[simp]
theorem equatorAmbientProjection_apply_one (y : EuclideanSpace ℝ (Fin 5)) :
    equatorAmbientProjection y 1 = y 1 := rfl

@[simp]
theorem equatorAmbientProjection_apply_two (y : EuclideanSpace ℝ (Fin 5)) :
    equatorAmbientProjection y 2 = y 2 := rfl

@[simp]
theorem equatorAmbientProjection_apply_three (y : EuclideanSpace ℝ (Fin 5)) :
    equatorAmbientProjection y 3 = y 4 := rfl

theorem norm_equatorAmbientProjection_of_coord_three_eq_zero
    (y : EuclideanSpace ℝ (Fin 5)) (hy : y 3 = 0) :
    ‖equatorAmbientProjection y‖ = ‖y‖ := by
  have hsq : ‖equatorAmbientProjection y‖ ^ 2 = ‖y‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, equatorAmbientProjection, Fin.sum_univ_succ, hy]
  nlinarith [norm_nonneg (equatorAmbientProjection y), norm_nonneg y]

/-- The coordinate equator in the ambient `4`-sphere. -/
def coordinateEquator : Set (Sphere 4) :=
  {x | x.1 3 = 0}

theorem range_equatorSphereMap :
    range equatorSphereMap = coordinateEquator := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact equatorAmbientMap_apply_three x.1
  · intro hy
    change y.1 3 = 0 at hy
    have hnorm : ‖equatorAmbientProjection y.1‖ = 1 := by
      rw [norm_equatorAmbientProjection_of_coord_three_eq_zero y.1 hy]
      simpa [mem_sphere_zero_iff_norm] using y.2
    let x : Sphere 3 := ⟨equatorAmbientProjection y.1, by
      simpa [mem_sphere_zero_iff_norm] using hnorm⟩
    refine ⟨x, Subtype.ext ?_⟩
    ext i
    fin_cases i <;> simp [x, equatorSphereMap, equatorAmbientMap, equatorAmbientProjection, hy]

/-- The sign of the open cap containing component `i` of the standard unlink. -/
def capSign (i : Fin 2) : ℝ :=
  if i = 0 then -1 else 1

@[simp]
theorem capSign_zero : capSign 0 = -1 := by simp [capSign]

@[simp]
theorem capSign_one : capSign 1 = 1 := by simp [capSign]

@[simp]
theorem capSign_sq (i : Fin 2) : capSign i ^ 2 = 1 := by
  fin_cases i <;> simp

/-- The two open coordinate hemispheres complementary to `coordinateEquator`. -/
def coordinateOpenCap (i : Fin 2) : Set (Sphere 4) :=
  if i = 0 then {x | x.1 3 < 0} else {x | 0 < x.1 3}

@[simp]
theorem mem_coordinateOpenCap_zero {x : Sphere 4} :
    x ∈ coordinateOpenCap 0 ↔ x.1 3 < 0 := by
  simp [coordinateOpenCap]

@[simp]
theorem mem_coordinateOpenCap_one {x : Sphere 4} :
    x ∈ coordinateOpenCap 1 ↔ 0 < x.1 3 := by
  simp [coordinateOpenCap]

/-- Parametrize a coordinate open cap by the open unit ball in `ℝ⁴`. -/
def capAmbientMap (i : Fin 2) (u : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2
    ![u 0, u 1, u 2, capSign i * √(1 - ‖u‖ ^ 2), u 3]

@[simp]
theorem capAmbientMap_apply_zero (i : Fin 2) (u : EuclideanSpace ℝ (Fin 4)) :
    capAmbientMap i u 0 = u 0 := rfl

@[simp]
theorem capAmbientMap_apply_one (i : Fin 2) (u : EuclideanSpace ℝ (Fin 4)) :
    capAmbientMap i u 1 = u 1 := rfl

@[simp]
theorem capAmbientMap_apply_two (i : Fin 2) (u : EuclideanSpace ℝ (Fin 4)) :
    capAmbientMap i u 2 = u 2 := rfl

@[simp]
theorem capAmbientMap_apply_three (i : Fin 2) (u : EuclideanSpace ℝ (Fin 4)) :
    capAmbientMap i u 3 = capSign i * √(1 - ‖u‖ ^ 2) := rfl

@[simp]
theorem capAmbientMap_apply_four (i : Fin 2) (u : EuclideanSpace ℝ (Fin 4)) :
    capAmbientMap i u 4 = u 3 := rfl

theorem norm_capAmbientMap_of_mem_ball (i : Fin 2)
    {u : EuclideanSpace ℝ (Fin 4)} (hu : u ∈ ball 0 1) :
    ‖capAmbientMap i u‖ = 1 := by
  have hu_lt : ‖u‖ < 1 := mem_ball_zero_iff.1 hu
  have hrad : 0 ≤ 1 - ‖u‖ ^ 2 := by
    nlinarith [norm_nonneg u]
  have hu_sq :
      u 0 ^ 2 + (u 1 ^ 2 + (u 2 ^ 2 + u 3 ^ 2)) = ‖u‖ ^ 2 := by
    simpa [Fin.sum_univ_succ] using (EuclideanSpace.real_norm_sq_eq u).symm
  have hsq : ‖capAmbientMap i u‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change u 0 ^ 2 + (u 1 ^ 2 + (u 2 ^ 2 +
      ((capSign i * √(1 - ‖u‖ ^ 2)) ^ 2 + u 3 ^ 2))) = 1
    rw [mul_pow, capSign_sq, one_mul, Real.sq_sqrt hrad]
    nlinarith
  nlinarith [norm_nonneg (capAmbientMap i u)]

/-- The ball parametrization, corestricted to the ambient unit sphere. -/
def capSphereMap (i : Fin 2) (u : ball (0 : EuclideanSpace ℝ (Fin 4)) 1) : Sphere 4 :=
  ⟨capAmbientMap i u.1, by
    simpa [mem_sphere_zero_iff_norm] using norm_capAmbientMap_of_mem_ball i u.2⟩

@[simp]
theorem capSphereMap_coe (i : Fin 2)
    (u : ball (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    (capSphereMap i u).1 = capAmbientMap i u.1 := rfl

theorem continuous_capSphereMap (i : Fin 2) : Continuous (capSphereMap i) := by
  apply continuous_induced_rng.2
  change Continuous fun u : ball (0 : EuclideanSpace ℝ (Fin 4)) 1 ↦
    capAmbientMap i u.1
  unfold capAmbientMap
  fun_prop

theorem norm_equatorAmbientProjection_sq_add_coord_three
    (y : EuclideanSpace ℝ (Fin 5)) :
    ‖equatorAmbientProjection y‖ ^ 2 + y 3 ^ 2 = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [equatorAmbientProjection, Fin.sum_univ_succ]
  ring

theorem range_capSphereMap (i : Fin 2) :
    range (capSphereMap i) = coordinateOpenCap i := by
  fin_cases i
  · ext y
    constructor
    · rintro ⟨u, rfl⟩
      change capSign 0 * √(1 - ‖u.1‖ ^ 2) < 0
      have hu_lt : ‖u.1‖ < 1 := mem_ball_zero_iff.1 u.2
      have hrad : 0 < 1 - ‖u.1‖ ^ 2 := by
        nlinarith [norm_nonneg u.1]
      simp [Real.sqrt_pos.2 hrad]
    · intro hy
      change y.1 3 < 0 at hy
      have hynorm : ‖y.1‖ = 1 := by
        simpa [mem_sphere_zero_iff_norm] using y.2
      have hproj_sq :
          ‖equatorAmbientProjection y.1‖ ^ 2 + y.1 3 ^ 2 = 1 := by
        simpa [hynorm] using norm_equatorAmbientProjection_sq_add_coord_three y.1
      have hproj_lt : ‖equatorAmbientProjection y.1‖ < 1 := by
        nlinarith [norm_nonneg (equatorAmbientProjection y.1), sq_pos_of_neg hy]
      let u : ball (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
        ⟨equatorAmbientProjection y.1, mem_ball_zero_iff.2 hproj_lt⟩
      have hrad : 1 - ‖u.1‖ ^ 2 = y.1 3 ^ 2 := by
        dsimp [u]
        nlinarith
      have hcoord : capSign 0 * √(1 - ‖u.1‖ ^ 2) = y.1 3 := by
        rw [hrad, Real.sqrt_sq_eq_abs, abs_of_neg hy]
        simp
      have hcoord' :
          capSign 0 * √(1 - ‖equatorAmbientProjection y.1‖ ^ 2) = y.1 3 := by
        simpa [u] using hcoord
      have hcoord'' :
          -√(1 - ‖equatorAmbientProjection y.1‖ ^ 2) = y.1 3 := by
        simpa using hcoord'
      refine ⟨u, Subtype.ext ?_⟩
      ext j
      fin_cases j <;>
        simp [u, capSphereMap, capAmbientMap, hcoord'']

  · ext y
    constructor
    · rintro ⟨u, rfl⟩
      change 0 < capSign 1 * √(1 - ‖u.1‖ ^ 2)
      have hu_lt : ‖u.1‖ < 1 := mem_ball_zero_iff.1 u.2
      have hrad : 0 < 1 - ‖u.1‖ ^ 2 := by
        nlinarith [norm_nonneg u.1]
      simpa using Real.sqrt_pos.2 hrad
    · intro hy
      change 0 < y.1 3 at hy
      have hynorm : ‖y.1‖ = 1 := by
        simpa [mem_sphere_zero_iff_norm] using y.2
      have hproj_sq :
          ‖equatorAmbientProjection y.1‖ ^ 2 + y.1 3 ^ 2 = 1 := by
        simpa [hynorm] using norm_equatorAmbientProjection_sq_add_coord_three y.1
      have hproj_lt : ‖equatorAmbientProjection y.1‖ < 1 := by
        nlinarith [norm_nonneg (equatorAmbientProjection y.1), sq_pos_of_pos hy]
      let u : ball (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
        ⟨equatorAmbientProjection y.1, mem_ball_zero_iff.2 hproj_lt⟩
      have hrad : 1 - ‖u.1‖ ^ 2 = y.1 3 ^ 2 := by
        dsimp [u]
        nlinarith
      have hcoord : capSign 1 * √(1 - ‖u.1‖ ^ 2) = y.1 3 := by
        rw [hrad, Real.sqrt_sq_eq_abs, abs_of_pos hy]
        simp
      have hcoord' :
          capSign 1 * √(1 - ‖equatorAmbientProjection y.1‖ ^ 2) = y.1 3 := by
        simpa [u] using hcoord
      have hcoord'' :
          √(1 - ‖equatorAmbientProjection y.1‖ ^ 2) = y.1 3 := by
        simpa using hcoord'
      refine ⟨u, Subtype.ext ?_⟩
      ext j
      fin_cases j <;>
        simp [u, capSphereMap, capAmbientMap, hcoord'']

theorem isPreconnected_coordinateOpenCap (i : Fin 2) :
    IsPreconnected (coordinateOpenCap i) := by
  letI : PreconnectedSpace (ball (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    Subtype.preconnectedSpace (convex_ball (0 : EuclideanSpace ℝ (Fin 4)) 1).isPreconnected
  rw [← range_capSphereMap i]
  exact isPreconnected_range (continuous_capSphereMap i)

theorem coordinateOpenCap_subset_compl_coordinateEquator (i : Fin 2) :
    coordinateOpenCap i ⊆ coordinateEquatorᶜ := by
  fin_cases i
  · intro x hx hxEquator
    change x.1 3 < 0 at hx
    change x.1 3 = 0 at hxEquator
    linarith
  · intro x hx hxEquator
    change 0 < x.1 3 at hx
    change x.1 3 = 0 at hxEquator
    linarith

theorem standardUnlinkComponent_subset_coordinateOpenCap (i : Fin 2) :
    standardUnlinkComponent i ⊆ coordinateOpenCap i := by
  fin_cases i
  · intro x hx
    change x.1 3 = -(1 / 2 : ℝ) ∧ x.1 4 = 0 at hx
    change x.1 3 < 0
    rw [hx.1]
    norm_num
  · intro x hx
    change x.1 3 = (1 / 2 : ℝ) ∧ x.1 4 = 0 at hx
    change 0 < x.1 3
    rw [hx.1]
    norm_num

/-- A concrete point on each round component of the standard unlink. -/
def standardUnlinkPoint (i : Fin 2) : Sphere 4 :=
  ⟨WithLp.toLp 2
      ![(1 / 2 : ℝ), 1 / 2, 1 / 2,
        (if i = 0 then -(1 / 2 : ℝ) else 1 / 2), 0], by
    rw [mem_sphere_zero_iff_norm]
    have hsq : ‖WithLp.toLp 2
        ![(1 / 2 : ℝ), 1 / 2, 1 / 2,
          (if i = 0 then -(1 / 2 : ℝ) else 1 / 2), 0]‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      fin_cases i <;> norm_num [Fin.sum_univ_succ]
    nlinarith [norm_nonneg (WithLp.toLp 2
      ![(1 / 2 : ℝ), 1 / 2, 1 / 2,
        (if i = 0 then -(1 / 2 : ℝ) else 1 / 2), 0])]⟩

@[simp]
theorem standardUnlinkPoint_coord_three (i : Fin 2) :
    (standardUnlinkPoint i).1 3 =
      (if i = 0 then -(1 / 2 : ℝ) else 1 / 2) := rfl

@[simp]
theorem standardUnlinkPoint_coord_four (i : Fin 2) :
    (standardUnlinkPoint i).1 4 = 0 := rfl

theorem standardUnlinkPoint_mem_component (i : Fin 2) :
    standardUnlinkPoint i ∈ standardUnlinkComponent i := by
  exact ⟨standardUnlinkPoint_coord_three i, standardUnlinkPoint_coord_four i⟩

theorem standardUnlinkComponent_nonempty (i : Fin 2) :
    (standardUnlinkComponent i).Nonempty :=
  ⟨standardUnlinkPoint i, standardUnlinkPoint_mem_component i⟩

theorem standardUnlinkPoint_mem_coordinateOpenCap (i : Fin 2) :
    standardUnlinkPoint i ∈ coordinateOpenCap i :=
  standardUnlinkComponent_subset_coordinateOpenCap i
    (standardUnlinkPoint_mem_component i)

theorem standardUnlinkComponent_subset_connectedComponentIn (i : Fin 2) :
    standardUnlinkComponent i ⊆
      connectedComponentIn coordinateEquatorᶜ (standardUnlinkPoint i) := by
  exact (standardUnlinkComponent_subset_coordinateOpenCap i).trans
    ((isPreconnected_coordinateOpenCap i).subset_connectedComponentIn
      (standardUnlinkPoint_mem_coordinateOpenCap i)
      (coordinateOpenCap_subset_compl_coordinateEquator i))

theorem connectedComponentIn_standardUnlinkPoints_ne :
    connectedComponentIn coordinateEquatorᶜ (standardUnlinkPoint 0) ≠
      connectedComponentIn coordinateEquatorᶜ (standardUnlinkPoint 1) := by
  intro hEq
  have hp0F : standardUnlinkPoint 0 ∈ coordinateEquatorᶜ :=
    coordinateOpenCap_subset_compl_coordinateEquator 0
      (standardUnlinkPoint_mem_coordinateOpenCap 0)
  have hp1F : standardUnlinkPoint 1 ∈ coordinateEquatorᶜ :=
    coordinateOpenCap_subset_compl_coordinateEquator 1
      (standardUnlinkPoint_mem_coordinateOpenCap 1)
  have hp0mem : standardUnlinkPoint 0 ∈
      connectedComponentIn coordinateEquatorᶜ (standardUnlinkPoint 0) :=
    mem_connectedComponentIn hp0F
  have hp1mem : standardUnlinkPoint 1 ∈
      connectedComponentIn coordinateEquatorᶜ (standardUnlinkPoint 0) := by
    rw [hEq]
    exact mem_connectedComponentIn hp1F
  let coord : Sphere 4 → ℝ := fun x ↦ x.1 3
  have hcoordContinuous : Continuous coord := by
    fun_prop
  have hzeroIcc : (0 : ℝ) ∈ Icc (coord (standardUnlinkPoint 0))
      (coord (standardUnlinkPoint 1)) := by
    simp [coord]
  have hzeroImage : (0 : ℝ) ∈ coord ''
      connectedComponentIn coordinateEquatorᶜ (standardUnlinkPoint 0) :=
    (isPreconnected_connectedComponentIn.intermediate_value hp0mem hp1mem
      hcoordContinuous.continuousOn) hzeroIcc
  rcases hzeroImage with ⟨z, hzComponent, hzCoord⟩
  have hzCompl : z ∈ coordinateEquatorᶜ :=
    connectedComponentIn_subset coordinateEquatorᶜ (standardUnlinkPoint 0) hzComponent
  apply hzCompl
  change z.1 3 = 0
  exact hzCoord

theorem compl_coordinateEquator_eq_union_openCaps :
    coordinateEquatorᶜ = coordinateOpenCap 0 ∪ coordinateOpenCap 1 := by
  ext x
  constructor
  · intro hx
    change x.1 3 ≠ 0 at hx
    rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · exact Or.inl hxneg
    · exact Or.inr hxpos
  · rintro (hxneg | hxpos) hxEquator
    · change x.1 3 < 0 at hxneg
      change x.1 3 = 0 at hxEquator
      linarith
    · change 0 < x.1 3 at hxpos
      change x.1 3 = 0 at hxEquator
      linarith

/-- The two coordinate caps are exactly the two connected components of the equator complement. -/
theorem connectedComponentIn_standardUnlinkPoint_eq_coordinateOpenCap (i : Fin 2) :
    connectedComponentIn coordinateEquatorᶜ (standardUnlinkPoint i) =
      coordinateOpenCap i := by
  fin_cases i
  · apply Subset.antisymm
    · intro z hz
      have hzCompl : z ∈ coordinateEquatorᶜ :=
        connectedComponentIn_subset coordinateEquatorᶜ (standardUnlinkPoint 0) hz
      have hzNe : z.1 3 ≠ 0 := by
        intro hzZero
        apply hzCompl
        exact hzZero
      change z.1 3 < 0
      by_contra hzNotNeg
      have hzPos : 0 < z.1 3 := lt_of_le_of_ne (le_of_not_gt hzNotNeg) hzNe.symm
      have hzCapOne : z ∈ coordinateOpenCap 1 := hzPos
      have hzComponentOne : z ∈
          connectedComponentIn coordinateEquatorᶜ (standardUnlinkPoint 1) :=
        (isPreconnected_coordinateOpenCap 1).subset_connectedComponentIn
          (standardUnlinkPoint_mem_coordinateOpenCap 1)
          (coordinateOpenCap_subset_compl_coordinateEquator 1) hzCapOne
      apply connectedComponentIn_standardUnlinkPoints_ne
      exact (connectedComponentIn_eq hz).trans (connectedComponentIn_eq hzComponentOne).symm
    · exact (isPreconnected_coordinateOpenCap 0).subset_connectedComponentIn
        (standardUnlinkPoint_mem_coordinateOpenCap 0)
        (coordinateOpenCap_subset_compl_coordinateEquator 0)
  · apply Subset.antisymm
    · intro z hz
      have hzCompl : z ∈ coordinateEquatorᶜ :=
        connectedComponentIn_subset coordinateEquatorᶜ (standardUnlinkPoint 1) hz
      have hzNe : z.1 3 ≠ 0 := by
        intro hzZero
        apply hzCompl
        exact hzZero
      change 0 < z.1 3
      by_contra hzNotPos
      have hzNeg : z.1 3 < 0 := lt_of_le_of_ne (le_of_not_gt hzNotPos) hzNe
      have hzCapZero : z ∈ coordinateOpenCap 0 := hzNeg
      have hzComponentZero : z ∈
          connectedComponentIn coordinateEquatorᶜ (standardUnlinkPoint 0) :=
        (isPreconnected_coordinateOpenCap 0).subset_connectedComponentIn
          (standardUnlinkPoint_mem_coordinateOpenCap 0)
          (coordinateOpenCap_subset_compl_coordinateEquator 0) hzCapZero
      apply connectedComponentIn_standardUnlinkPoints_ne
      exact (connectedComponentIn_eq hzComponentZero).trans (connectedComponentIn_eq hz).symm
    · exact (isPreconnected_coordinateOpenCap 1).subset_connectedComponentIn
        (standardUnlinkPoint_mem_coordinateOpenCap 1)
        (coordinateOpenCap_subset_compl_coordinateEquator 1)

theorem disjoint_coordinateEquator_standardUnlinkCarrier :
    Disjoint coordinateEquator standardUnlinkCarrier := by
  rw [Set.disjoint_left]
  intro x hxEquator hxCarrier
  change x.1 3 = 0 at hxEquator
  rcases hxCarrier with hx0 | hx1
  · change x.1 3 = -(1 / 2 : ℝ) ∧ x.1 4 = 0 at hx0
    linarith [hx0.1]
  · change x.1 3 = (1 / 2 : ℝ) ∧ x.1 4 = 0 at hx1
    linarith [hx1.1]

/-- The coordinate equator separates the two explicit round unlink components. -/
theorem separates_coordinateEquator :
    Separates coordinateEquator
      (standardUnlinkComponent 0) (standardUnlinkComponent 1) := by
  refine ⟨?_, standardUnlinkPoint 0, standardUnlinkPoint_mem_component 0,
    standardUnlinkPoint 1, standardUnlinkPoint_mem_component 1,
    standardUnlinkComponent_subset_connectedComponentIn 0,
    standardUnlinkComponent_subset_connectedComponentIn 1,
    connectedComponentIn_standardUnlinkPoints_ne⟩
  simpa [standardUnlinkCarrier] using disjoint_coordinateEquator_standardUnlinkCarrier

theorem separates_range_equatorSphereMap :
    Separates (range equatorSphereMap)
      (standardUnlinkComponent 0) (standardUnlinkComponent 1) := by
  rw [range_equatorSphereMap]
  exact separates_coordinateEquator

/-- The equatorial parametrization already has the smoothness and topological-embedding parts
of the bundled smooth-embedding structure. -/
theorem equatorSphereMap_contMDiff_and_isEmbedding :
    ContMDiff (𝓡 3) (𝓡 4) ∞ equatorSphereMap ∧
      IsEmbedding equatorSphereMap :=
  ⟨contMDiff_equatorSphereMap, isEmbedding_equatorSphereMap⟩

end SplittingSpheres
