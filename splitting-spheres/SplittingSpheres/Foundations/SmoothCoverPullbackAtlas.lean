/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.LocalHomeomorphChartedSpace
public import SplittingSpheres.Foundations.SmoothCover

/-!
# The smooth structure pulled back along a covering projection

A topological covering projection is a local homeomorphism.  Pulling the base atlas back through
its local sheets therefore equips the total space with a manifold structure for which the
projection is a local diffeomorphism, hence a smooth covering map.

The source is assumed to have only its topology.  The charted-space and manifold instances in
the statements below are deliberately introduced by dependent `letI` binders: there is no
pre-existing source atlas or hidden source-smoothness hypothesis.
-/

@[expose] public section

noncomputable section

open ChartedSpace IsManifold
open scoped ContDiff Manifold

namespace SplittingSpheres

universe uE uX uH

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [TopologicalSpace E]
variable {X : Type uX} [TopologicalSpace X] [ChartedSpace H X]
variable (I : ModelWithCorners ℝ V H) (n : ℕ∞ω)

namespace IsCoveringMap

/-- The charted-space structure on the total space obtained by pulling back the base atlas along
the local sheets of a covering projection.

This is not installed globally: its value depends on the chosen projection and covering proof.
Use it locally with
`letI := SplittingSpheres.IsCoveringMap.pullbackChartedSpace hp`. -/
abbrev pullbackChartedSpace {p : E → X} (hp : IsCoveringMap p) : ChartedSpace H E :=
  SplittingSpheres.IsLocalHomeomorph.pullbackChartedSpace hp.isLocalHomeomorph

/-- The preferred chart of the covering-pullback atlas is the local sheet followed by the
preferred chart downstairs. -/
@[simp]
theorem pullbackChartedSpace_chartAt {p : E → X} (hp : IsCoveringMap p) (x : E) :
    @chartAt H _ E _
        (SplittingSpheres.IsCoveringMap.pullbackChartedSpace hp) x =
      SplittingSpheres.IsLocalHomeomorph.pullbackChart hp.isLocalHomeomorph x :=
  rfl

/-- The pullback atlas makes the total space a manifold of the same regularity and model as the
base. -/
theorem isManifold_pullbackChartedSpace
    {p : E → X} (hp : IsCoveringMap p) [IsManifold I n X] :
    letI : ChartedSpace H E :=
      SplittingSpheres.IsCoveringMap.pullbackChartedSpace (H := H) hp
    IsManifold I n E := by
  let _ : ChartedSpace H E :=
    SplittingSpheres.IsCoveringMap.pullbackChartedSpace (H := H) hp
  exact SplittingSpheres.IsLocalHomeomorph.isManifold_pullbackChartedSpace
    I n hp.isLocalHomeomorph

/-- With the pulled-back atlas and induced manifold structure selected, the covering projection
is a local diffeomorphism. -/
theorem isLocalDiffeomorph_pullbackChartedSpace
    {p : E → X} (hp : IsCoveringMap p) [IsManifold I n X] :
    letI : ChartedSpace H E :=
      SplittingSpheres.IsCoveringMap.pullbackChartedSpace (H := H) hp
    letI : IsManifold I n E :=
      SplittingSpheres.IsCoveringMap.isManifold_pullbackChartedSpace I n hp
    IsLocalDiffeomorph I I n p := by
  let _ : ChartedSpace H E :=
    SplittingSpheres.IsCoveringMap.pullbackChartedSpace (H := H) hp
  let _ : IsManifold I n E :=
    SplittingSpheres.IsCoveringMap.isManifold_pullbackChartedSpace I n hp
  exact SplittingSpheres.IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
    I n hp.isLocalHomeomorph

/-- A covering projection is smooth for the atlas pulled back from its base. -/
theorem contMDiff_pullbackChartedSpace
    {p : E → X} (hp : IsCoveringMap p) [IsManifold I n X] :
    letI : ChartedSpace H E :=
      SplittingSpheres.IsCoveringMap.pullbackChartedSpace (H := H) hp
    letI : IsManifold I n E :=
      SplittingSpheres.IsCoveringMap.isManifold_pullbackChartedSpace I n hp
    ContMDiff I I n p := by
  let _ : ChartedSpace H E :=
    SplittingSpheres.IsCoveringMap.pullbackChartedSpace (H := H) hp
  let _ : IsManifold I n E :=
    SplittingSpheres.IsCoveringMap.isManifold_pullbackChartedSpace I n hp
  exact
    (SplittingSpheres.IsCoveringMap.isLocalDiffeomorph_pullbackChartedSpace I n hp).contMDiff

/-- Every topological covering projection over a manifold becomes a `SmoothCover` after selecting
the pulled-back atlas and its induced manifold structure on the total space. -/
theorem smoothCover_pullbackChartedSpace
    {p : E → X} (hp : IsCoveringMap p) [IsManifold I n X] :
    letI : ChartedSpace H E :=
      SplittingSpheres.IsCoveringMap.pullbackChartedSpace (H := H) hp
    letI : IsManifold I n E :=
      SplittingSpheres.IsCoveringMap.isManifold_pullbackChartedSpace I n hp
    SmoothCover I I n p := by
  let _ : ChartedSpace H E :=
    SplittingSpheres.IsCoveringMap.pullbackChartedSpace (H := H) hp
  let _ : IsManifold I n E :=
    SplittingSpheres.IsCoveringMap.isManifold_pullbackChartedSpace I n hp
  exact ⟨hp,
    SplittingSpheres.IsCoveringMap.isLocalDiffeomorph_pullbackChartedSpace I n hp⟩

end IsCoveringMap

end SplittingSpheres
