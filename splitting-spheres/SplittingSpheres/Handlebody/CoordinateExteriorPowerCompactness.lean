/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalCoverPullbackCompact
public import SplittingSpheres.Geometry.UnlinkPowerProper
public import SplittingSpheres.Handlebody.CoordinateExteriorPowerPushout

/-!
# Compactness of the coordinate-exterior power pullbacks

For nonzero degree, the punctured-complex power map is proper.  Every base occurring in the
coordinate-exterior pushout decomposition is compact, so the generic proper-pullback theorem
gives compactness of the global, piece, boundary, and glued total spaces.

The nonzero-degree hypothesis is essential: for degree zero, a nonempty fiber of the raw power
map is the whole punctured complex plane.
-/

@[expose] public section

noncomputable section

open Function Topology

namespace SplittingSpheres

/-- The nonzero-degree power pullback over the literal closed exterior is compact. -/
theorem compactSpace_coordinateUnlinkExteriorEighthPowerPullback
    (m : ℕ) [NeZero m] :
    CompactSpace (CoordinateUnlinkExteriorEighthPowerPullback m) := by
  let _ : CompactSpace ↑(coordinateUnlinkExterior (1 / 8 : ℝ)) :=
    isCompact_iff_compactSpace.mp
      (isOpen_standardUnlinkOpenTubes (1 / 8 : ℝ)).isClosed_compl.isCompact
  exact topologicalCoverPullbackCompactSpace (nonzeroComplexPow m)
    coordinateUnlinkExteriorEighthRightNormalMap
    (isProperMap_nonzeroComplexPow m)
    continuous_coordinateUnlinkExteriorEighthRightNormalMap

/-- The nonzero-degree power pullback over the exterior pushout is compact. -/
theorem compactSpace_coordinateUnlinkExteriorPushoutPowerPullback
    (m : ℕ) [NeZero m] :
    CompactSpace (CoordinateUnlinkExteriorPushoutPowerPullback m) :=
  topologicalCoverPullbackCompactSpace (nonzeroComplexPow m)
    coordinateUnlinkExteriorPushoutRightNormalMap
    (isProperMap_nonzeroComplexPow m)
    continuous_coordinateUnlinkExteriorPushoutRightNormalMap

/-- The nonzero-degree one-handle restricted pullback is compact. -/
theorem compactSpace_coordinateUnlinkExteriorOneHandlePowerPullback
    (m : ℕ) [NeZero m] :
    CompactSpace (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
  topologicalCoverPullbackCompactSpace (nonzeroComplexPow m)
    (coordinateUnlinkExteriorPushoutRightNormalMap ∘
      coordinateUnlinkExteriorPushoutOneHandleInclusion)
    (isProperMap_nonzeroComplexPow m)
    (continuous_coordinateUnlinkExteriorPushoutRightNormalMap.comp
      coordinateUnlinkExteriorPushoutOneHandleInclusion.continuous)

/-- The nonzero-degree punctured-cap restricted pullback is compact. -/
theorem compactSpace_coordinateUnlinkExteriorPuncturedCapPowerPullback
    (m : ℕ) [NeZero m] :
    CompactSpace (CoordinateUnlinkExteriorPuncturedCapPowerPullback m) :=
  topologicalCoverPullbackCompactSpace (nonzeroComplexPow m)
    (coordinateUnlinkExteriorPushoutRightNormalMap ∘
      coordinateUnlinkExteriorPushoutPuncturedCapInclusion)
    (isProperMap_nonzeroComplexPow m)
    (continuous_coordinateUnlinkExteriorPushoutRightNormalMap.comp
      coordinateUnlinkExteriorPushoutPuncturedCapInclusion.continuous)

/-- The nonzero-degree attaching-boundary pullback is compact. -/
theorem compactSpace_coordinateUnlinkExteriorBoundaryPowerPullback
    (m : ℕ) [NeZero m] :
    CompactSpace (CoordinateUnlinkExteriorBoundaryPowerPullback m) :=
  topologicalCoverPullbackCompactSpace (nonzeroComplexPow m)
    ((coordinateUnlinkExteriorPushoutRightNormalMap ∘
      coordinateUnlinkExteriorPushoutOneHandleInclusion) ∘
        oneHandleBoundaryInclusion)
    (isProperMap_nonzeroComplexPow m)
    ((continuous_coordinateUnlinkExteriorPushoutRightNormalMap.comp
      coordinateUnlinkExteriorPushoutOneHandleInclusion.continuous).comp
        oneHandleBoundaryInclusion.continuous)

/-- Gluing the two compact restricted total spaces along their common boundary pullback gives a
compact topological pushout. -/
theorem compactSpace_coordinateUnlinkExteriorPowerPullbackPushout
    (m : ℕ) [NeZero m] :
    CompactSpace (CoordinateUnlinkExteriorPowerPullbackPushout m) := by
  let _ := compactSpace_coordinateUnlinkExteriorOneHandlePowerPullback m
  let _ := compactSpace_coordinateUnlinkExteriorPuncturedCapPowerPullback m
  infer_instance

end SplittingSpheres
