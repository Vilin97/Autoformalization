/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import SplittingSpheres.Foundations.SmoothCoverPullbackAtlas
public import SplittingSpheres.Foundations.TopologicalCoverPullback
public import SplittingSpheres.Geometry.UnlinkComplement

/-!
# A power-map pullback over the coordinate unlink complement

The final two coordinates identify the normal plane of the coordinate unlink with the complex
plane.  Displacement from the center of component `1` is nonzero throughout the strict unlink
complement, so one may pull the `m`-th power map on `ℂ \ {0}` back along this displacement map.
For `m ≠ 0`, this file proves that the projection is a topological and smooth covering and that
every fiber has exactly `m` points.

No cyclic deck action or meridian-winding calculation is asserted here.  Those geometric facts
require additional constructions beyond the raw power-map pullback.
-/

@[expose] public section

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold

namespace SplittingSpheres

/-- Identify a normal-plane displacement with a complex number. -/
def unlinkNormalPlaneToComplex (v : UnlinkNormalPlane) : ℂ :=
  Complex.equivRealProdCLM.symm (v 0, v 1)

theorem continuous_unlinkNormalPlaneToComplex :
    Continuous unlinkNormalPlaneToComplex := by
  unfold unlinkNormalPlaneToComplex
  fun_prop

/-- Complex normal displacement from the center of component `1`. -/
def standardUnlinkRightDisplacementComplex (x : Sphere 4) : ℂ :=
  unlinkNormalPlaneToComplex
    (standardUnlinkNormalProjection x - standardUnlinkNormalCenter 1)

theorem continuous_standardUnlinkRightDisplacementComplex :
    Continuous standardUnlinkRightDisplacementComplex := by
  exact continuous_unlinkNormalPlaneToComplex.comp
    (continuous_standardUnlinkNormalProjection.sub continuous_const)

/-- The right normal displacement vanishes exactly on component `1`; hence it is nonzero on the
strict complement of the whole unlink. -/
theorem standardUnlinkRightDisplacementComplex_ne_zero
    (x : StandardUnlinkComplement) :
    standardUnlinkRightDisplacementComplex x.1 ≠ 0 := by
  intro hz
  let v := standardUnlinkNormalProjection x.1 - standardUnlinkNormalCenter 1
  have hpair : (v 0, v 1) = (0, 0) := by
    apply Complex.equivRealProdCLM.symm.injective
    change Complex.equivRealProdCLM.symm (v 0, v 1) =
      Complex.equivRealProdCLM.symm (0 : ℝ × ℝ)
    exact (show Complex.equivRealProdCLM.symm (v 0, v 1) = 0 by
      simpa only [standardUnlinkRightDisplacementComplex,
        unlinkNormalPlaneToComplex, v] using hz).trans
          (map_zero Complex.equivRealProdCLM.symm).symm
  have hv : v = 0 := by
    ext j
    fin_cases j
    · exact congrArg Prod.fst hpair
    · exact congrArg Prod.snd hpair
  have hprojection :
      standardUnlinkNormalProjection x.1 = standardUnlinkNormalCenter 1 :=
    sub_eq_zero.mp hv
  have hcomponent : x.1 ∈ standardUnlinkComponent 1 := by
    rw [← preimage_singleton_standardUnlinkNormalCenter 1]
    exact hprojection
  exact x.2 (Or.inr hcomponent)

/-- The right-normal displacement as a continuous map to the punctured complex plane. -/
def standardUnlinkRightNormalMap :
    StandardUnlinkComplement → {z : ℂ // z ≠ 0} :=
  fun x ↦ ⟨standardUnlinkRightDisplacementComplex x.1,
    standardUnlinkRightDisplacementComplex_ne_zero x⟩

@[simp]
theorem standardUnlinkRightNormalMap_coe (x : StandardUnlinkComplement) :
    (standardUnlinkRightNormalMap x : ℂ) =
      standardUnlinkRightDisplacementComplex x.1 :=
  rfl

theorem continuous_standardUnlinkRightNormalMap :
    Continuous standardUnlinkRightNormalMap :=
  Continuous.subtype_mk
    (continuous_standardUnlinkRightDisplacementComplex.comp continuous_subtype_val) _

/-- The power map on the punctured complex plane. -/
def nonzeroComplexPow (m : ℕ) : {z : ℂ // z ≠ 0} → {z : ℂ // z ≠ 0} :=
  fun z ↦ ⟨z.1 ^ m, pow_ne_zero m z.2⟩

@[simp]
theorem nonzeroComplexPow_coe (m : ℕ) (z : {z : ℂ // z ≠ 0}) :
    (nonzeroComplexPow m z : ℂ) = z.1 ^ m :=
  rfl

/-- For positive degree, the punctured-complex power map is a covering map. -/
theorem isCoveringMap_nonzeroComplexPow (m : ℕ) [NeZero m] :
    IsCoveringMap (nonzeroComplexPow m) := by
  change IsCoveringMap (fun z : {z : ℂ // z ≠ 0} ↦
    (⟨z.1 ^ m, pow_ne_zero m z.2⟩ : {z : ℂ // z ≠ 0}))
  exact isCoveringMap_npow m (𝕜 := ℂ) (by simp [NeZero.ne m])

/-- Taking a nonzero complex number to the corresponding unit does not change its underlying
complex value. -/
theorem unitsHomeomorphNeZero_symm_val (z : {z : ℂ // z ≠ 0}) :
    ((((unitsHomeomorphNeZero (G₀ := ℂ)).symm z : ℂˣ) : ℂ)) = z.1 := by
  exact congrArg Subtype.val ((unitsHomeomorphNeZero (G₀ := ℂ)).apply_symm_apply z)

/-- Sending a complex unit to the nonzero subtype does not change its underlying value. -/
theorem unitsHomeomorphNeZero_apply_val (z : ℂˣ) :
    ((unitsHomeomorphNeZero (G₀ := ℂ) z : {z : ℂ // z ≠ 0}) : ℂ) = (z : ℂ) := by
  calc
    ((unitsHomeomorphNeZero (G₀ := ℂ) z : {z : ℂ // z ≠ 0}) : ℂ) =
        (((unitsHomeomorphNeZero (G₀ := ℂ)).symm
          (unitsHomeomorphNeZero (G₀ := ℂ) z) : ℂˣ) : ℂ) :=
      (unitsHomeomorphNeZero_symm_val
        (unitsHomeomorphNeZero (G₀ := ℂ) z)).symm
    _ = (z : ℂ) := congrArg Units.val
      ((unitsHomeomorphNeZero (G₀ := ℂ)).symm_apply_apply z)

/-- Conjugating by `unitsHomeomorphNeZero` identifies the fiber of the power map on punctured
complex numbers with the corresponding fiber of the power map on complex units. -/
def nonzeroComplexPowFiberEquivUnitsPow (m : ℕ) (w : {z : ℂ // z ≠ 0}) :
    (nonzeroComplexPow m ⁻¹' {w}) ≃
      ((fun z : ℂˣ ↦ z ^ m) ⁻¹' {(unitsHomeomorphNeZero (G₀ := ℂ)).symm w}) where
  toFun z := ⟨(unitsHomeomorphNeZero (G₀ := ℂ)).symm z.1, by
    have hz : nonzeroComplexPow m z.1 = w := z.2
    apply Units.ext
    change ((((unitsHomeomorphNeZero (G₀ := ℂ)).symm z.1 : ℂˣ) : ℂ) ^ m) =
      (((unitsHomeomorphNeZero (G₀ := ℂ)).symm w : ℂˣ) : ℂ)
    rw [unitsHomeomorphNeZero_symm_val, unitsHomeomorphNeZero_symm_val]
    exact congrArg Subtype.val hz⟩
  invFun z := ⟨unitsHomeomorphNeZero (G₀ := ℂ) z.1, by
    have hz : z.1 ^ m = (unitsHomeomorphNeZero (G₀ := ℂ)).symm w := z.2
    apply Subtype.ext
    change ((unitsHomeomorphNeZero (G₀ := ℂ) z.1 : {z : ℂ // z ≠ 0}) : ℂ) ^ m = w.1
    rw [unitsHomeomorphNeZero_apply_val, ← unitsHomeomorphNeZero_symm_val w]
    exact congrArg Units.val hz⟩
  left_inv z := by
    apply Subtype.ext
    exact (unitsHomeomorphNeZero (G₀ := ℂ)).apply_symm_apply z.1
  right_inv z := by
    apply Subtype.ext
    exact (unitsHomeomorphNeZero (G₀ := ℂ)).symm_apply_apply z.1

/-- Every fiber of the power map on complex units has exactly `m` points. -/
theorem natCard_unitsPow_fiber (m : ℕ) [NeZero m] (w : ℂˣ) :
    Nat.card ((fun z : ℂˣ ↦ z ^ m) ⁻¹' {w}) = m := by
  let hq := Complex.isQuotientCoveringMap_npow m
  obtain ⟨z, hz⟩ := hq.surjective w
  calc
    Nat.card ((fun z : ℂˣ ↦ z ^ m) ⁻¹' {w}) =
        Nat.card ((powMonoidHom (α := ℂˣ) m).ker) :=
      Nat.card_congr (hq.fiberEquivGroup ⟨z, hz⟩)
    _ = Nat.card (rootsOfUnity m ℂ) := by rw [rootsOfUnity_eq_ker]
    _ = m := Complex.card_rootsOfUnity m

/-- Every fiber of the punctured-complex power covering has exactly `m` points. -/
theorem natCard_nonzeroComplexPow_fiber (m : ℕ) [NeZero m]
    (w : {z : ℂ // z ≠ 0}) :
    Nat.card (nonzeroComplexPow m ⁻¹' {w}) = m := by
  calc
    Nat.card (nonzeroComplexPow m ⁻¹' {w}) =
        Nat.card ((fun z : ℂˣ ↦ z ^ m) ⁻¹'
          {(unitsHomeomorphNeZero (G₀ := ℂ)).symm w}) :=
      Nat.card_congr (nonzeroComplexPowFiberEquivUnitsPow m w)
    _ = m := natCard_unitsPow_fiber m _

/-- The raw power-map pullback over the strict coordinate-unlink complement.  For `m = 0` this
type is still a well-defined fiber product, but its projection is not claimed to be a cover. -/
abbrev StandardUnlinkPowerPullback (m : ℕ) :=
  TopologicalCoverPullback (nonzeroComplexPow m) standardUnlinkRightNormalMap

/-- Projection of the raw power-map pullback to the strict unlink complement. -/
def standardUnlinkPowerPullbackProj (m : ℕ) :
    StandardUnlinkPowerPullback m → StandardUnlinkComplement :=
  topologicalCoverPullbackProj (nonzeroComplexPow m) standardUnlinkRightNormalMap

@[simp]
theorem standardUnlinkPowerPullbackProj_apply (m : ℕ)
    (z : StandardUnlinkPowerPullback m) :
    standardUnlinkPowerPullbackProj m z = z.1.1 :=
  rfl

/-- For `m ≠ 0`, the power-pullback projection is a topological covering map. -/
theorem isCoveringMap_standardUnlinkPowerPullbackProj (m : ℕ) [NeZero m] :
    IsCoveringMap (standardUnlinkPowerPullbackProj m) :=
  SplittingSpheres.IsCoveringMap.pullback
    (isCoveringMap_nonzeroComplexPow m) continuous_standardUnlinkRightNormalMap

/-- For `m ≠ 0`, every fiber of the power-pullback projection has exactly `m` points. -/
theorem natCard_standardUnlinkPowerPullbackProj_fiber (m : ℕ) [NeZero m]
    (x : StandardUnlinkComplement) :
    Nat.card (standardUnlinkPowerPullbackProj m ⁻¹' {x}) = m := by
  calc
    Nat.card (standardUnlinkPowerPullbackProj m ⁻¹' {x}) =
        Nat.card (nonzeroComplexPow m ⁻¹' {standardUnlinkRightNormalMap x}) :=
      Nat.card_congr (topologicalCoverPullbackFiberEquiv
        (nonzeroComplexPow m) standardUnlinkRightNormalMap x)
    _ = m := natCard_nonzeroComplexPow_fiber m _

/-- The charted-space structure on the nonzero-degree power pullback, pulled back from the smooth
strict complement.  It is kept explicit because it depends on `m` and on the projection. -/
abbrev standardUnlinkPowerPullbackChartedSpace (m : ℕ) [NeZero m] :
    ChartedSpace (EuclideanSpace ℝ (Fin 4)) (StandardUnlinkPowerPullback m) :=
  SplittingSpheres.IsCoveringMap.pullbackChartedSpace
    (isCoveringMap_standardUnlinkPowerPullbackProj m)

/-- The pulled-back atlas is a smooth four-manifold atlas. -/
theorem isManifold_standardUnlinkPowerPullback (m : ℕ) [NeZero m] :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4)) (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  exact SplittingSpheres.IsCoveringMap.isManifold_pullbackChartedSpace
    (𝓡 4) ∞ (isCoveringMap_standardUnlinkPowerPullbackProj m)

/-- With its explicit pulled-back atlas, the nonzero-degree power-pullback projection is smooth. -/
theorem smoothCover_standardUnlinkPowerPullbackProj (m : ℕ) [NeZero m] :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    SmoothCover (𝓡 4) (𝓡 4) ∞ (standardUnlinkPowerPullbackProj m) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4)) (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  exact SplittingSpheres.IsCoveringMap.smoothCover_pullbackChartedSpace
    (𝓡 4) ∞ (isCoveringMap_standardUnlinkPowerPullbackProj m)

end SplittingSpheres
