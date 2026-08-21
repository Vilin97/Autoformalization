/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkEquatorPowerCollar
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckEquatorComparison

/-!
# A global smooth collar of the transported planar neck image

The global collar of the equatorial lift is reindexed by the old transported-neck label.  The
required label is exactly `a - coordinateUnlinkExteriorPlanarSmoothNeckShift m`.  Its zero section
therefore has exactly the ambient range of
`coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m a`.

This does not assert that the old transported-neck parametrization is smooth.  The smooth map is
the zero section of the collar constructed here; only its exact point-set image is identified with
the range of the old parametrization.
-/

@[expose] public section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-- The explicit smooth collar image indexed by the old transported-neck label. -/
def coordinateUnlinkExteriorPlanarTransportedNeckCollarImage
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Opens (StandardUnlinkPowerPullback m) :=
  equatorUnlinkPowerCollarImage m
    (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m)

abbrev CoordinateUnlinkExteriorPlanarTransportedNeckCollarImage
    (m : ℕ) [NeZero m] (a : ZMod m) :=
  coordinateUnlinkExteriorPlanarTransportedNeckCollarImage m a

/-- A global smooth collar whose zero section has exactly the range of the transported old neck.

The old source parametrization is not asserted smooth; only its exact point-set image is used. -/
def coordinateUnlinkExteriorPlanarTransportedNeckCollarDiffeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    (Sphere 3 × EquatorCollarInterval) ≃ₘ^∞⟮
        ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ)), (𝓡 4)⟯
      CoordinateUnlinkExteriorPlanarTransportedNeckCollarImage m a :=
  equatorUnlinkPowerCollarDiffeomorph m
    (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m)

@[simp]
theorem coordinateUnlinkExteriorPlanarTransportedNeckCollarDiffeomorph_apply_coe
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    ((coordinateUnlinkExteriorPlanarTransportedNeckCollarDiffeomorph
      m a p : CoordinateUnlinkExteriorPlanarTransportedNeckCollarImage m a) :
        StandardUnlinkPowerPullback m) =
      equatorUnlinkPowerCollarLift m
        (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) p := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  exact equatorUnlinkPowerCollarDiffeomorph_apply_coe m _ p

def coordinateUnlinkExteriorPlanarTransportedNeckCollarZero
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    CoordinateUnlinkExteriorPlanarTransportedNeckCollarImage m a :=
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  coordinateUnlinkExteriorPlanarTransportedNeckCollarDiffeomorph m a
    (x, ⟨0, by norm_num [equatorCollarIntervalOpens]⟩)

@[simp]
theorem coordinateUnlinkExteriorPlanarTransportedNeckCollarZero_coe
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    (coordinateUnlinkExteriorPlanarTransportedNeckCollarZero m a x :
      StandardUnlinkPowerPullback m) =
      equatorUnlinkPowerLift m
        (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) x := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  exact equatorUnlinkPowerCollarDiffeomorph_zero_coe m _ x

/-- The zero section of the smooth collar is exactly the transported point-set neck range. -/
theorem range_coordinateUnlinkExteriorPlanarTransportedNeckCollarZero
    (m : ℕ) [NeZero m] (a : ZMod m) :
    range (fun x : Sphere 3 ↦
      (coordinateUnlinkExteriorPlanarTransportedNeckCollarZero m a x :
        StandardUnlinkPowerPullback m)) =
      range (coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m a) := by
  rw [range_transportedNeckSphereMap_eq_equatorPowerLift_sub_shift]
  congr 1
  funext x
  exact coordinateUnlinkExteriorPlanarTransportedNeckCollarZero_coe m a x

/-- The exact transported old-neck range lies in the displayed open smooth collar image. -/
theorem range_coordinateUnlinkExteriorPlanarTransportedNeckSphereMap_subset_collarImage
    (m : ℕ) [NeZero m] (a : ZMod m) :
    range (coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m a) ⊆
      coordinateUnlinkExteriorPlanarTransportedNeckCollarImage m a := by
  rw [← range_coordinateUnlinkExteriorPlanarTransportedNeckCollarZero]
  rintro y ⟨x, rfl⟩
  exact (coordinateUnlinkExteriorPlanarTransportedNeckCollarZero m a x).property

end SplittingSpheres

end
