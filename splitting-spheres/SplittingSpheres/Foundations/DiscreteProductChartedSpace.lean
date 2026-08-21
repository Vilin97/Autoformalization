/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.LocalHomeomorphChartedSpace

/-!
# Charted spaces with a discrete product factor

Projection from `D × P` to `P` is a local homeomorphism when `D` is discrete.  Pulling an
atlas on `P` back through this projection gives every component of `D × P` the same model
space and the same manifold dimension as `P`.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace SplittingSpheres

/-- The sheet of `D × P` over a fixed point of a discrete factor, identified with `P`. -/
def discreteProdSndChart
    {D P : Type*} [TopologicalSpace D] [DiscreteTopology D]
    [TopologicalSpace P] (d : D) : OpenPartialHomeomorph (D × P) P where
  toFun := Prod.snd
  invFun := fun p ↦ (d, p)
  source := {q | q.1 = d}
  target := univ
  map_source' _ _ := mem_univ _
  map_target' _ _ := rfl
  left_inv' q hq := Prod.ext hq.symm rfl
  right_inv' _ _ := rfl
  open_source := by
    change IsOpen (Prod.fst ⁻¹' {d})
    exact (isOpen_discrete {d}).preimage continuous_fst
  open_target := isOpen_univ
  continuousOn_toFun := continuous_snd.continuousOn
  continuousOn_invFun := (continuous_const.prodMk continuous_id).continuousOn

/-- Projection to the second factor is a local homeomorphism when the first factor is
discrete. -/
theorem isLocalHomeomorph_discreteProdSnd
    {D P : Type*} [TopologicalSpace D] [DiscreteTopology D]
    [TopologicalSpace P] :
    IsLocalHomeomorph (Prod.snd : D × P → P) := by
  apply IsLocalHomeomorph.mk
  intro x
  refine ⟨discreteProdSndChart x.1, ?_, ?_⟩
  · rfl
  · intro _ _
    rfl

/-- Pull an `H`-modeled atlas on `P` back componentwise to `D × P`, without adding the
discrete factor to the model space. -/
@[instance_reducible]
def discreteProductChartedSpace
    (H D P : Type*) [TopologicalSpace H]
    [TopologicalSpace D] [DiscreteTopology D]
    [TopologicalSpace P] [ChartedSpace H P] :
    ChartedSpace H (D × P) :=
  SplittingSpheres.IsLocalHomeomorph.pullbackChartedSpace
    (isLocalHomeomorph_discreteProdSnd (D := D) (P := P))

/-- The componentwise pulled-back atlas on `D × P` is an `I`-manifold whenever `P` is. -/
theorem isManifold_discreteProductChartedSpace
    {K V H : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup V] [NormedSpace K V]
    [TopologicalSpace H]
    (I : ModelWithCorners K V H) (n : ℕ∞ω)
    (D P : Type*) [TopologicalSpace D] [DiscreteTopology D]
    [TopologicalSpace P] [ChartedSpace H P] [IsManifold I n P] :
    letI := discreteProductChartedSpace H D P
    IsManifold I n (D × P) :=
  SplittingSpheres.IsLocalHomeomorph.isManifold_pullbackChartedSpace
    I n (isLocalHomeomorph_discreteProdSnd (D := D) (P := P))

end SplittingSpheres
