/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import SplittingSpheres.Foundations.SmoothIsotopyEndpointFlattening

/-!
# Real-time extension and velocity of a flattened isotopy

The endpoint-flattening formula makes sense for every real time and still lands in the unit
interval.  It therefore extends a flattened sphere isotopy to a globally smooth real-time family,
constant before its first-quarter transition and after its last-quarter transition.

The second part of the file records a generic parameterized-calculus fact.  For a smooth map
`F : ℝ × M → E` into a normed space, its ordinary real-time Fréchet derivative, evaluated on `1`,
is a smooth function of both time and the manifold parameter.  This is an analytic prerequisite
for constructing the spacetime vector field of an isotopy; no extension off the trace is asserted.
-/

@[expose] public section

open Function Set
open scoped ContDiff Manifold Topology unitInterval

noncomputable section

namespace unitInterval

/-- The endpoint-flattening time change, extended smoothly to every real input. -/
def endpointFlatTimeReal (t : ℝ) : I :=
  ⟨Real.smoothTransition (2 * t - 1 / 2),
    Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The real-time endpoint-flattening map is smooth into the interval with boundary. -/
theorem contMDiff_endpointFlatTimeReal :
    ContMDiff 𝓘(ℝ) (𝓡∂ 1) ∞ endpointFlatTimeReal := by
  let L : ℝ →L[ℝ] ℝ := (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  have hmul : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ ↦ 2 * t) := by
    convert L.contMDiff using 1
    funext t
    simp [L]
  have harg : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ ↦ 2 * t - 1 / 2) :=
    hmul.sub contMDiff_const
  have hval : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞
      (fun t : ℝ ↦ Real.smoothTransition (2 * t - 1 / 2)) :=
    Real.smoothTransition.contDiff.contMDiff.comp harg
  rw [contMDiff_iff_comp_subtypeVal_Icc]
  exact ⟨hval.continuous.subtype_mk _, hval⟩

/-- Restricting the real-time formula to the unit interval recovers `endpointFlatTime`. -/
@[simp]
theorem endpointFlatTimeReal_coe (t : I) :
    endpointFlatTimeReal (t : ℝ) = endpointFlatTime t :=
  rfl

/-- The real-time extension is exactly zero before and throughout the first quarter. -/
theorem endpointFlatTimeReal_eq_zero {t : ℝ} (ht : t ≤ 1 / 4) :
    endpointFlatTimeReal t = 0 := by
  apply Subtype.ext
  change Real.smoothTransition (2 * t - 1 / 2) = 0
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

/-- The real-time extension is exactly one from the last quarter onward. -/
theorem endpointFlatTimeReal_eq_one {t : ℝ} (ht : (3 / 4 : ℝ) ≤ t) :
    endpointFlatTimeReal t = 1 := by
  apply Subtype.ext
  change Real.smoothTransition (2 * t - 1 / 2) = 1
  exact Real.smoothTransition.one_of_one_le (by linarith)

end unitInterval

namespace SplittingSpheres

/-- Extend the endpoint-flattened formula of a sphere isotopy to every real time. -/
def SmoothSphereIsotopy.flattenedRealTime
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) : ℝ × Sphere 3 → Sphere 4 :=
  fun p ↦ H.toFun (unitInterval.endpointFlatTimeReal p.1, p.2)

/-- The real-time extension of a flattened sphere isotopy is jointly smooth. -/
theorem SmoothSphereIsotopy.contMDiff_flattenedRealTime
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) :
    ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 4) ∞ H.flattenedRealTime := by
  exact H.contMDiff_toFun.comp
    ((unitInterval.contMDiff_endpointFlatTimeReal.comp contMDiff_fst).prodMk contMDiff_snd)

/-- On interval inputs, the real-time extension is the bundled endpoint-flattened isotopy. -/
@[simp]
theorem SmoothSphereIsotopy.flattenedRealTime_coe
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) (p : I × Sphere 3) :
    H.flattenedRealTime ((p.1 : ℝ), p.2) = H.flattenEndpoints.toFun p :=
  rfl

/-- The real-time extension is the original zero slice throughout the first quarter. -/
theorem SmoothSphereIsotopy.flattenedRealTime_eq_zero
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) {t : ℝ} (ht : t ≤ 1 / 4)
    (x : Sphere 3) :
    H.flattenedRealTime (t, x) = H.toFun (0, x) := by
  rw [SmoothSphereIsotopy.flattenedRealTime,
    unitInterval.endpointFlatTimeReal_eq_zero ht]

/-- The real-time extension is the original one slice from the last quarter onward. -/
theorem SmoothSphereIsotopy.flattenedRealTime_eq_one
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) {t : ℝ} (ht : (3 / 4 : ℝ) ≤ t)
    (x : Sphere 3) :
    H.flattenedRealTime (t, x) = H.toFun (1, x) := by
  rw [SmoothSphereIsotopy.flattenedRealTime,
    unitInterval.endpointFlatTimeReal_eq_one ht]

section RealTimeVelocity

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H]
  {J : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold J 1 M]

/-- The ordinary real-time derivative of a manifold-parameterized normed-space-valued map. -/
def realTimeVelocity (f : ℝ × M → E) (p : ℝ × M) : E :=
  fderiv ℝ (fun t : ℝ ↦ f (t, p.2)) p.1 1

omit [TopologicalSpace M] in
/-- A family which is locally constant in time has zero real-time velocity at that point. -/
theorem realTimeVelocity_eq_zero_of_eventuallyEq_const
    (f : ℝ × M → E) (p : ℝ × M) (c : E)
    (h : (fun t : ℝ ↦ f (t, p.2)) =ᶠ[𝓝 p.1] fun _ ↦ c) :
    realTimeVelocity f p = 0 := by
  rw [realTimeVelocity, h.fderiv_eq]
  simp

/-- The real-time velocity of a jointly smooth family is jointly smooth in time and parameter. -/
theorem contMDiff_realTimeVelocity
    (f : ℝ × M → E)
    (hf : ContMDiff (𝓘(ℝ).prod J) 𝓘(ℝ, E) ∞ f) :
    ContMDiff (𝓘(ℝ).prod J) 𝓘(ℝ, E) ∞ (realTimeVelocity f) := by
  intro p
  let f' : (ℝ × M) → ℝ → E := fun q t ↦ f (t, q.2)
  let g : (ℝ × M) → ℝ := Prod.fst
  have hf' : ContMDiff ((𝓘(ℝ).prod J).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞
      (Function.uncurry f') := by
    exact hf.comp (contMDiff_snd.prodMk (contMDiff_snd.comp contMDiff_fst))
  have hg : ContMDiff (𝓘(ℝ).prod J) 𝓘(ℝ) ∞ g := contMDiff_fst
  have h := ContMDiffAt.mfderiv_apply
    (m := (∞ : WithTop ℕ∞)) (n := (∞ : WithTop ℕ∞))
    f' g id (fun _ : ℝ × M ↦ (1 : ℝ))
    (hf' (p, p.1)) (hg p) contMDiffAt_id contMDiffAt_const (by simp)
  change ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, E) ∞
    (fun q ↦ fderiv ℝ (fun t : ℝ ↦ f (t, q.2)) q.1 1) p
  simpa only [inTangentCoordinates_model_space, f', g, id_eq, mfderiv_eq_fderiv] using h

end RealTimeVelocity

end SplittingSpheres
