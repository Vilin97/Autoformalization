/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Topology.Homotopy.Covering

/-!
# Smooth covering maps

This file combines the topological covering-map API with the local smooth structure needed by
the splitting-spheres argument.  Its main elementary observation is that a continuous lift of a
smooth map through a smooth local diffeomorphism is smooth: locally, the lift is the composite
with a smooth local inverse.
-/

@[expose] public section

open scoped ContDiff Manifold Topology

noncomputable section

namespace SplittingSpheres

universe uE uX uA uHE uHX uHA

variable {EE EX EA : Type*}
  [NormedAddCommGroup EE] [NormedSpace ℝ EE]
  [NormedAddCommGroup EX] [NormedSpace ℝ EX]
  [NormedAddCommGroup EA] [NormedSpace ℝ EA]
variable {HE : Type uHE} [TopologicalSpace HE]
  {HX : Type uHX} [TopologicalSpace HX]
  {HA : Type uHA} [TopologicalSpace HA]
variable {IE : ModelWithCorners ℝ EE HE} {IX : ModelWithCorners ℝ EX HX}
  {IA : ModelWithCorners ℝ EA HA}
variable {E : Type uE} [TopologicalSpace E] [ChartedSpace HE E]
  {X : Type uX} [TopologicalSpace X] [ChartedSpace HX X]
  {A : Type uA} [TopologicalSpace A] [ChartedSpace HA A]
variable {n : ℕ∞ω} {p : E → X}

/-- A smooth covering map is simultaneously a topological covering map and a smooth local
diffeomorphism.  The two fields deliberately retain both APIs: the first controls global lifting
and monodromy, while the second controls regularity of the lifts. -/
structure SmoothCover (IE : ModelWithCorners ℝ EE HE) (IX : ModelWithCorners ℝ EX HX)
    (n : ℕ∞ω) (p : E → X) : Prop where
  /-- The projection is a covering map in the topological sense. -/
  isCoveringMap : IsCoveringMap p
  /-- The projection is a local diffeomorphism in the smooth sense. -/
  isLocalDiffeomorph : IsLocalDiffeomorph IE IX n p

namespace SmoothCover

/-- On a compact Hausdorff total space, a smooth local diffeomorphism is automatically a smooth
cover. -/
theorem of_isLocalDiffeomorph [T2Space E] [T2Space X] [CompactSpace E]
    (hp : IsLocalDiffeomorph IE IX n p) : SmoothCover IE IX n p :=
  ⟨isLocalHomeomorph_iff_isCoveringMap.mp hp.isLocalHomeomorph, hp⟩

/-- A smooth covering projection is continuous. -/
protected theorem continuous (hp : SmoothCover IE IX n p) : Continuous p :=
  hp.1.continuous

/-- A smooth covering projection is smooth. -/
protected theorem contMDiff (hp : SmoothCover IE IX n p) : ContMDiff IE IX n p :=
  hp.2.contMDiff

/-- A continuous lift through a smooth covering projection is smooth whenever the map downstairs
is smooth. -/
theorem contMDiff_lift (hp : SmoothCover IE IX n p) {f : A → X} {F : A → E}
    (hf : ContMDiff IA IX n f) (hF : Continuous F) (hlift : p ∘ F = f) :
    ContMDiff IA IE n F := by
  intro a
  let hpa : IsLocalDiffeomorphAt IE IX n p (F a) := hp.2 (F a)
  have htarget : ∀ᶠ a' in 𝓝 a, F a' ∈ hpa.localInverse.target :=
    hF.continuousAt
      (hpa.localInverse.open_target.mem_nhds hpa.localInverse_mem_target)
  have heq : F =ᶠ[𝓝 a] hpa.localInverse ∘ f := by
    filter_upwards [htarget] with a' ha'
    have hinv := (hpa.localInverse_left_inv ha').symm
    simpa only [Function.comp_apply, ← congrFun hlift a'] using hinv
  have hfa : f a = p (F a) := (congrFun hlift a).symm
  exact (hpa.localInverse_contMDiffAt.comp_of_eq (hf a) hfa).congr_of_eventuallyEq heq

/-- Along a continuous lift, smoothness upstairs is equivalent to smoothness downstairs. -/
theorem contMDiff_lift_iff (hp : SmoothCover IE IX n p) {f : A → X} {F : A → E}
    (hF : Continuous F) (hlift : p ∘ F = f) :
    ContMDiff IA IE n F ↔ ContMDiff IA IX n f := by
  refine ⟨?_, fun hf ↦ hp.contMDiff_lift hf hF hlift⟩
  intro h
  rw [← hlift]
  exact hp.contMDiff.comp h

/-- The fundamental-group lifting criterion for a smooth cover, with the resulting lift promoted
from continuous to smooth.  Uniqueness is stated among smooth maps, but follows from the stronger
uniqueness among continuous maps supplied by the covering-space theorem. -/
theorem existsUnique_contMDiff_lift_of_range_le (hp : SmoothCover IE IX n p)
    [PathConnectedSpace A] [LocallyPathConnectedSpace A]
    {f : A → X} (hf : ContMDiff IA IX n f) {a₀ : A} {e₀ : E}
    (he : p e₀ = f a₀)
    (hle : (_root_.FundamentalGroup.map ⟨f, hf.continuous⟩ a₀).range ≤
      (_root_.FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range) :
    ∃! F : A → E,
      ContMDiff IA IE n F ∧ F a₀ = e₀ ∧ p ∘ F = f := by
  let fC : C(A, X) := ⟨f, hf.continuous⟩
  obtain ⟨F, hF, hunique⟩ :=
    hp.1.existsUnique_continuousMap_lifts_of_range_le (f := fC) he hle
  have hproj : p ∘ (F : A → E) = f := by
    funext a
    change p (F a) = f a
    exact congrFun hF.2 a
  refine ⟨F, ⟨hp.contMDiff_lift hf F.continuous hproj, hF.1, hproj⟩, ?_⟩
  intro G hG
  let GC : C(A, E) := ⟨G, hG.1.continuous⟩
  have hGC : GC a₀ = e₀ ∧ p ∘ GC = fC := by
    refine ⟨hG.2.1, ?_⟩
    funext a
    change p (G a) = f a
    exact congrFun hG.2.2 a
  have hEq : GC = F := hunique GC hGC
  funext a
  exact congrArg (fun Q : C(A, E) ↦ Q a) hEq

end SmoothCover

end SplittingSpheres
