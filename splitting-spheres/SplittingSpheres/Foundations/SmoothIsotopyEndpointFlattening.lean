/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothIsotopyConcat

/-!
# Flattening a smooth sphere isotopy near its time endpoints

The standard smooth transition function gives a time change which is identically zero on the
first quarter of the unit interval and identically one on the last quarter.  Precomposing an
isotopy with this time change preserves its endpoint maps and all of its embedded slices, while
making the family literally constant on neighborhoods of both time-boundary faces.

This is a source reparametrization, not an ambient isotopy-extension theorem.
-/

@[expose] public section

open Function Set
open scoped ContDiff Manifold unitInterval

noncomputable section

namespace unitInterval

/-- A smooth time change which is constant near both endpoints of the unit interval. -/
def endpointFlatTime (t : I) : I :=
  ⟨Real.smoothTransition (2 * (t : ℝ) - 1 / 2),
    Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The endpoint-flattening time change is smooth as a map of manifolds with boundary. -/
theorem contMDiff_endpointFlatTime :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ endpointFlatTime := by
  let L : ℝ →L[ℝ] ℝ := (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  have hsub : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun t : I ↦ (t : ℝ)) :=
    contMDiff_subtypeVal_Icc
  have hmul : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun t : I ↦ 2 * (t : ℝ)) := by
    convert L.contMDiff.comp hsub using 1
    funext t
    simp [L]
  have harg : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞
      (fun t : I ↦ 2 * (t : ℝ) - 1 / 2) :=
    hmul.sub contMDiff_const
  have hval : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞
      (fun t : I ↦ Real.smoothTransition (2 * (t : ℝ) - 1 / 2)) :=
    Real.smoothTransition.contDiff.contMDiff.comp harg
  rw [contMDiff_iff_comp_subtypeVal_Icc]
  exact ⟨hval.continuous.subtype_mk _, hval⟩

@[simp]
theorem endpointFlatTime_zero : endpointFlatTime 0 = 0 := by
  apply Subtype.ext
  norm_num [endpointFlatTime, Real.smoothTransition.zero_of_nonpos]

@[simp]
theorem endpointFlatTime_one : endpointFlatTime 1 = 1 := by
  apply Subtype.ext
  norm_num [endpointFlatTime, Real.smoothTransition.one_of_one_le]

/-- The flattened time is exactly zero throughout the first quarter. -/
theorem endpointFlatTime_eq_zero {t : I} (ht : (t : ℝ) ≤ 1 / 4) :
    endpointFlatTime t = 0 := by
  apply Subtype.ext
  change Real.smoothTransition (2 * (t : ℝ) - 1 / 2) = 0
  apply Real.smoothTransition.zero_of_nonpos
  linarith

/-- The flattened time is exactly one throughout the last quarter. -/
theorem endpointFlatTime_eq_one {t : I} (ht : (3 / 4 : ℝ) ≤ t) :
    endpointFlatTime t = 1 := by
  apply Subtype.ext
  change Real.smoothTransition (2 * (t : ℝ) - 1 / 2) = 1
  apply Real.smoothTransition.one_of_one_le
  linarith

end unitInterval

namespace SplittingSpheres

/-- Reparametrize a smooth sphere isotopy so that it is constant near both time endpoints. -/
def SmoothSphereIsotopy.flattenEndpoints
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) : SmoothSphereIsotopy S₀ S₁ where
  toFun := fun p ↦ H.toFun (unitInterval.endpointFlatTime p.1, p.2)
  contMDiff_toFun := H.contMDiff_toFun.comp
    ((unitInterval.contMDiff_endpointFlatTime.comp contMDiff_fst).prodMk contMDiff_snd)
  isSmoothEmbedding_slice := fun t ↦ H.isSmoothEmbedding_slice
    (unitInterval.endpointFlatTime t)
  range_zero := by
    simpa only [unitInterval.endpointFlatTime_zero] using H.range_zero
  range_one := by
    simpa only [unitInterval.endpointFlatTime_one] using H.range_one

@[simp]
theorem SmoothSphereIsotopy.flattenEndpoints_toFun
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) (p : I × Sphere 3) :
    H.flattenEndpoints.toFun p =
      H.toFun (unitInterval.endpointFlatTime p.1, p.2) :=
  rfl

/-- The flattened isotopy is literally its time-zero slice throughout the first quarter. -/
theorem SmoothSphereIsotopy.flattenEndpoints_eq_zero
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) {t : I} (ht : (t : ℝ) ≤ 1 / 4)
    (x : Sphere 3) :
    H.flattenEndpoints.toFun (t, x) = H.toFun (0, x) := by
  rw [SmoothSphereIsotopy.flattenEndpoints_toFun,
    unitInterval.endpointFlatTime_eq_zero ht]

/-- The flattened isotopy is literally its time-one slice throughout the last quarter. -/
theorem SmoothSphereIsotopy.flattenEndpoints_eq_one
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) {t : I} (ht : (3 / 4 : ℝ) ≤ t)
    (x : Sphere 3) :
    H.flattenEndpoints.toFun (t, x) = H.toFun (1, x) := by
  rw [SmoothSphereIsotopy.flattenEndpoints_toFun,
    unitInterval.endpointFlatTime_eq_one ht]

/-- Endpoint flattening preserves pointwise avoidance of the frozen standard unlink. -/
theorem SmoothSphereIsotopy.flattenEndpoints_avoids
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁)
    (hH : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    ∀ p, H.flattenEndpoints.toFun p ∉ standardUnlinkCarrier := by
  rintro ⟨t, x⟩
  exact hH (unitInterval.endpointFlatTime t, x)

end SplittingSpheres
