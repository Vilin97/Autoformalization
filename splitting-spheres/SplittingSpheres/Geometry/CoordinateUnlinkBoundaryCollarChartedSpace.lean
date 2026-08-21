/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Instances.ZMod
public import SplittingSpheres.Foundations.DiscreteProductChartedSpace
public import SplittingSpheres.Geometry.CoordinateUnlinkBoundaryCollarModel
public import SplittingSpheres.Geometry.EuclideanFourBallSmoothCollar

/-!
# The boundary-collar atlas in coordinate-unlink exterior coordinates

The natural radial four-ball collar is modeled on `(𝓡 3).prod (𝓡∂ 1)`.  This file
postcomposes each of its preferred charts with the explicit carrier homeomorphism to the
coordinate-unlink exterior model space.  The resulting transitions are exactly the conjugates
whose smoothness was established by `coordinateUnlinkBoundaryCollarConjugate_mem_contDiffGroupoid`.

The construction is also pulled back componentwise to a finite family indexed by the discrete
space `ZMod m`.  No atlas on the four-ball target, cut side, or glued space is asserted here.
-/

@[expose] public section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-- A natural collar chart, with its target postcomposed by the explicit carrier
homeomorphism to the coordinate-unlink exterior model space. -/
def coordinateUnlinkExteriorRechartedFourBallCollarChart
    (p : EuclideanFourBallCollarDomain) :
    OpenPartialHomeomorph EuclideanFourBallCollarDomain
      CoordinateUnlinkExteriorModelSpace :=
  (chartAt CoordinateUnlinkBoundaryCollarModelSpace p).trans
    coordinateUnlinkBoundaryCollarModelHomeomorph.toOpenPartialHomeomorph

@[simp]
theorem mem_coordinateUnlinkExteriorRechartedFourBallCollarChart_source
    (p : EuclideanFourBallCollarDomain) :
    p ∈ (coordinateUnlinkExteriorRechartedFourBallCollarChart p).source := by
  simp [coordinateUnlinkExteriorRechartedFourBallCollarChart]

/-- The natural smooth collar atlas, explicitly recharted into the literal carrier
used by the coordinate-unlink exterior model. -/
@[instance_reducible]
def coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      EuclideanFourBallCollarDomain where
  atlas := range coordinateUnlinkExteriorRechartedFourBallCollarChart
  chartAt := coordinateUnlinkExteriorRechartedFourBallCollarChart
  mem_chart_source :=
    mem_coordinateUnlinkExteriorRechartedFourBallCollarChart_source
  chart_mem_atlas p := ⟨p, rfl⟩

@[simp]
theorem coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace_chartAt
    (p : EuclideanFourBallCollarDomain) :
    @chartAt CoordinateUnlinkExteriorModelSpace _
        EuclideanFourBallCollarDomain _
        coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace p =
      coordinateUnlinkExteriorRechartedFourBallCollarChart p :=
  rfl

theorem mem_coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace_atlas_iff
    (e : OpenPartialHomeomorph EuclideanFourBallCollarDomain
      CoordinateUnlinkExteriorModelSpace) :
    e ∈ @atlas CoordinateUnlinkExteriorModelSpace _
        EuclideanFourBallCollarDomain _
        coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace ↔
      ∃ p, e = coordinateUnlinkExteriorRechartedFourBallCollarChart p := by
  change e ∈ range coordinateUnlinkExteriorRechartedFourBallCollarChart ↔ _
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, rfl⟩

/-- The explicitly recharted radial-collar atlas is smooth in the coordinate-unlink
exterior model. -/
theorem isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  refine { compatible := ?_ }
  intro e e' he he'
  rw [mem_coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace_atlas_iff]
    at he he'
  obtain ⟨p, rfl⟩ := he
  obtain ⟨q, rfl⟩ := he'
  have hold := (contDiffGroupoid ∞ coordinateUnlinkBoundaryCollarModel).compatible
    (chart_mem_atlas CoordinateUnlinkBoundaryCollarModelSpace p)
    (chart_mem_atlas CoordinateUnlinkBoundaryCollarModelSpace q)
  have hnew :=
    coordinateUnlinkBoundaryCollarConjugate_mem_contDiffGroupoid
      ((chartAt CoordinateUnlinkBoundaryCollarModelSpace p).symm.trans
        (chartAt CoordinateUnlinkBoundaryCollarModelSpace q)) hold
  simpa only [coordinateUnlinkExteriorRechartedFourBallCollarChart,
    coordinateUnlinkBoundaryCollarConjugate,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc,
    Homeomorph.symm_toOpenPartialHomeomorph,
    OpenPartialHomeomorph.symm_symm] using hnew

/-- Componentwise pullback of the recharted collar atlas to the full finite family. -/
@[instance_reducible]
def coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace
    (m : ℕ) :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m × EuclideanFourBallCollarDomain) :=
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) EuclideanFourBallCollarDomain

/-- The full discrete family of explicitly recharted radial collars is a smooth
manifold in the coordinate-unlink exterior model. -/
theorem isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily
    (m : ℕ) :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  exact isManifold_discreteProductChartedSpace
    coordinateUnlinkExteriorModel ∞ (ZMod m) EuclideanFourBallCollarDomain

end SplittingSpheres
