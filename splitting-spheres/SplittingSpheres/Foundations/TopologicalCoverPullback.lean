/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Covering.Basic

/-!
# Pulling back topological covering maps

For maps `p : E → X` and `f : Y → X`, the pullback total space consists of pairs `(y,e)` with
`f y = p e`.  If `p` is a covering map and `f` is continuous, projection to `Y` is again a
covering map.  The proof pulls an evenly covered neighborhood of `f y` back along `f` and keeps
the same discrete fiber.

This is point-set topology only.  A smooth structure on a pulled-back total space is supplied
separately by `SmoothCoverPullbackAtlas` once the base is a manifold.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

universe uE uX uY

variable {E : Type uE} {X : Type uX} {Y : Type uY}
variable [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]

/-- The point-set pullback of `p : E → X` along `f : Y → X`. -/
abbrev TopologicalCoverPullback (p : E → X) (f : Y → X) :=
  {z : Y × E // f z.1 = p z.2}

/-- Projection from a point-set pullback to its new base. -/
def topologicalCoverPullbackProj (p : E → X) (f : Y → X) :
    TopologicalCoverPullback p f → Y :=
  fun z ↦ z.1.1

omit [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y] in
@[simp]
theorem topologicalCoverPullbackProj_apply (p : E → X) (f : Y → X)
    (z : TopologicalCoverPullback p f) :
    topologicalCoverPullbackProj p f z = z.1.1 :=
  rfl

/-- The selected point of the old total space lies over the image of the selected new-base
point exactly when it determines a point of the pullback. -/
def topologicalCoverPullbackMk (p : E → X) (f : Y → X) (y : Y) (e : E)
    (h : f y = p e) : TopologicalCoverPullback p f :=
  ⟨(y, e), h⟩

omit [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y] in
@[simp]
theorem topologicalCoverPullbackProj_mk (p : E → X) (f : Y → X)
    (y : Y) (e : E) (h : f y = p e) :
    topologicalCoverPullbackProj p f (topologicalCoverPullbackMk p f y e h) = y :=
  rfl

omit [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y] in
/-- The literal fiber of a pullback projection over `y` is equivalent to the old fiber over
`f y`.  This point-set equivalence is useful for transporting sheet cardinalities without making
any connectedness or surjectivity assumption on the covering map. -/
def topologicalCoverPullbackFiberEquiv (p : E → X) (f : Y → X) (y : Y) :
    (topologicalCoverPullbackProj p f ⁻¹' {y}) ≃ (p ⁻¹' {f y}) where
  toFun z := ⟨z.1.1.2, by
    change p z.1.1.2 = f y
    rw [← z.1.2]
    congr 1
    have hy : topologicalCoverPullbackProj p f z.1 = y := z.2
    exact hy⟩
  invFun e := ⟨⟨(y, e.1), by
    have he : p e.1 = f y := e.2
    exact he.symm⟩, by
      change y = y
      rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have hy : topologicalCoverPullbackProj p f z.1 = y := z.2
      exact hy.symm
    · rfl
  right_inv e := by
    apply Subtype.ext
    rfl

omit [TopologicalSpace X] in
/-- Projection from the pullback is continuous. -/
theorem continuous_topologicalCoverPullbackProj (p : E → X) (f : Y → X) :
    Continuous (topologicalCoverPullbackProj p f) :=
  continuous_fst.comp continuous_subtype_val

namespace IsEvenlyCovered

/-- Pull an evenly covered neighborhood back along a continuous map.  The discrete fiber is the
old fiber over `f y`; `to_isEvenlyCovered_preimage` can subsequently retag it as the literal
fiber of the pullback projection. -/
theorem pullback {p : E → X} {f : Y → X} (hf : Continuous f) (y : Y)
    (h : IsEvenlyCovered p (f y) (p ⁻¹' {f y})) :
    IsEvenlyCovered (topologicalCoverPullbackProj p f) y (p ⁻¹' {f y}) := by
  rcases h with ⟨hdiscrete, U, hfyU, hU, hpU, H, hH⟩
  let V : Set Y := f ⁻¹' U
  have hV : IsOpen V := hU.preimage hf
  have hprojV : IsOpen (topologicalCoverPullbackProj p f ⁻¹' V) :=
    hV.preimage (continuous_topologicalCoverPullbackProj p f)
  let forward :
      topologicalCoverPullbackProj p f ⁻¹' V → V × (p ⁻¹' {f y}) :=
    fun z ↦
      (⟨z.1.1.1, z.2⟩,
        (H ⟨z.1.1.2, by
          change p z.1.1.2 ∈ U
          rw [← z.1.2]
          exact z.2⟩).2)
  let inverse :
      V × (p ⁻¹' {f y}) → topologicalCoverPullbackProj p f ⁻¹' V :=
    fun yi ↦ by
      let e := H.symm (⟨f yi.1.1, yi.1.2⟩, yi.2)
      have he : p e.1 = f yi.1.1 := by
        have happ := H.apply_symm_apply (⟨f yi.1.1, yi.1.2⟩, yi.2)
        have hfirst := congrArg (fun z ↦ z.1.1) happ
        exact (hH e).symm.trans hfirst
      exact ⟨⟨(yi.1.1, e.1), he.symm⟩, yi.1.2⟩
  have hleft : LeftInverse inverse forward := by
    intro z
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (H.symm (⟨f z.1.1.1, z.2⟩,
          (H ⟨z.1.1.2, _⟩).2)).1 = z.1.1.2
      have hbase : (H ⟨z.1.1.2, by
          change p z.1.1.2 ∈ U
          rw [← z.1.2]
          exact z.2⟩).1 = ⟨f z.1.1.1, z.2⟩ := by
        apply Subtype.ext
        exact (hH _).trans z.1.2.symm
      rw [← hbase, H.symm_apply_apply]
  have hright : RightInverse inverse forward := by
    intro yi
    apply Prod.ext
    · rfl
    · change (H (H.symm (⟨f yi.1.1, yi.1.2⟩, yi.2))).2 = yi.2
      rw [H.apply_symm_apply]
  refine ⟨hdiscrete, V, hfyU, hV, hprojV, ?_, ?_⟩
  · exact
      { toFun := forward
        invFun := inverse
        left_inv := hleft
        right_inv := hright
        continuous_toFun := by
          dsimp only [forward]
          fun_prop
        continuous_invFun := by
          dsimp only [inverse]
          fun_prop }
  · intro z
    rfl

end IsEvenlyCovered

/-- Covering maps are stable under arbitrary continuous base change. -/
theorem IsCoveringMap.pullback {p : E → X} (hp : IsCoveringMap p)
    {f : Y → X} (hf : Continuous f) :
    IsCoveringMap (topologicalCoverPullbackProj p f) := by
  intro y
  exact (IsEvenlyCovered.pullback hf y (hp (f y))).to_isEvenlyCovered_preimage

end SplittingSpheres
