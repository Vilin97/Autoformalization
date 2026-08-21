/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.DiscreteHomeomorphFamily
public import SplittingSpheres.Foundations.RadialSphereHomeomorphExtension
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckEquatorComparison
public import SplittingSpheres.Handlebody.ProductFourBallEuclideanHomeomorph

/-!
# Extending the neck-source reparametrizations over the cap balls

The old neck maps and the smooth equatorial collar use the same embedded spheres with different
source parametrizations.  For each label, the established sphere homeomorphism is extended
radially over the Euclidean four-ball.  After the point-set comparison from the old product cap
to the Euclidean ball, this gives a labelled cap-family homeomorphism whose boundary action is
exactly the required neck reparametrization.

This radial extension is topological.  No smoothness of the old source reparametrization or of
the resulting ball homeomorphism is asserted.
-/

@[expose] public section

open Function Metric Set Topology
open scoped Topology

noncomputable section

namespace SplittingSpheres

/-- Assemble the label-dependent old-to-smooth neck source reparametrizations. -/
def coordinateUnlinkExteriorPlanarNeckEquatorFamilyHomeomorph
    (m : ℕ) [NeZero m] :
    ZMod m × Sphere 3 ≃ₜ ZMod m × Sphere 3 :=
  discreteFamilyHomeomorph
    (coordinateUnlinkExteriorPlanarNeckEquatorHomeomorph m)

/-- The labelled sphere reparametrization preserves the label and applies the selected source
homeomorphism. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckEquatorFamilyHomeomorph_apply
    (m : ℕ) [NeZero m] (p : ZMod m × Sphere 3) :
    coordinateUnlinkExteriorPlanarNeckEquatorFamilyHomeomorph m p =
      (p.1, coordinateUnlinkExteriorPlanarNeckEquatorHomeomorph m p.1 p.2) :=
  rfl

/-- Extend every labelled neck source reparametrization radially across its Euclidean cap. -/
def coordinateUnlinkExteriorPlanarNeckEquatorRadialBallFamilyHomeomorph
    (m : ℕ) [NeZero m] :
    ZMod m × EuclideanFourBall ≃ₜ ZMod m × EuclideanFourBall :=
  discreteFamilyHomeomorph (fun a ↦
    radialSphereExtensionBallHomeomorph
      (coordinateUnlinkExteriorPlanarNeckEquatorHomeomorph m a))

/-- Compare the old labelled product caps with Euclidean caps and then apply the radial neck
reparametrization. -/
def coordinateUnlinkExteriorPlanarNeckReparametrizedProductCapFamilyHomeomorph
    (m : ℕ) [NeZero m] :
    ZMod m × ProductFourBall ≃ₜ ZMod m × EuclideanFourBall :=
  (productFourBallFamilyHomeomorphEuclideanFourBall m).trans
    (coordinateUnlinkExteriorPlanarNeckEquatorRadialBallFamilyHomeomorph m)

/-- On the Euclidean boundary, the radial family comparison applies exactly the labelled neck
source reparametrization. -/
theorem coordinateUnlinkExteriorPlanarNeckEquatorRadialBallFamilyHomeomorph_boundary_inclusion
    (m : ℕ) [NeZero m] (p : ZMod m × Sphere 3) :
    coordinateUnlinkExteriorPlanarNeckEquatorRadialBallFamilyHomeomorph m
        (p.1, (euclideanFourBallBoundaryHomeomorphSphereThree.symm p.2).1) =
      (p.1, (euclideanFourBallBoundaryHomeomorphSphereThree.symm
        (coordinateUnlinkExteriorPlanarNeckEquatorHomeomorph m p.1 p.2)).1) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change radialSphereExtensionMap
        (coordinateUnlinkExteriorPlanarNeckEquatorHomeomorph m p.1)
        ((euclideanFourBallBoundaryHomeomorphSphereThree.symm p.2).1 :
          EuclideanSpace ℝ (Fin 4)) = _
    have hs :
        (((euclideanFourBallBoundaryHomeomorphSphereThree.symm p.2).1 :
          EuclideanFourBall) : EuclideanSpace ℝ (Fin 4)) = p.2 := by
      change (((closedUnitBallBoundaryHomeomorph
        (EuclideanSpace ℝ (Fin 4))).symm p.2).1.1 :
          EuclideanSpace ℝ (Fin 4)) = p.2
      exact closedUnitBallBoundaryHomeomorph_symm_apply_val
        (EuclideanSpace ℝ (Fin 4)) p.2
    rw [hs, radialSphereExtensionMap_of_mem_sphere]
    symm
    exact closedUnitBallBoundaryHomeomorph_symm_apply_val
      (EuclideanSpace ℝ (Fin 4))
      (coordinateUnlinkExteriorPlanarNeckEquatorHomeomorph m p.1 p.2)

/-- The product-to-Euclidean cap comparison has the exact reparametrized attaching action needed
for diagram congruence. -/
theorem
    coordinateUnlinkExteriorPlanarNeckReparametrizedProductCapFamilyHomeomorph_boundary_inclusion
    (m : ℕ) [NeZero m] (p : ZMod m × Sphere 3) :
    coordinateUnlinkExteriorPlanarNeckReparametrizedProductCapFamilyHomeomorph m
        (p.1, productFourSphereBoundaryInclusion p.2) =
      (p.1, (euclideanFourBallBoundaryHomeomorphSphereThree.symm
        (coordinateUnlinkExteriorPlanarNeckEquatorHomeomorph m p.1 p.2)).1) := by
  rw [coordinateUnlinkExteriorPlanarNeckReparametrizedProductCapFamilyHomeomorph,
    Homeomorph.trans_apply,
    productFourBallFamilyHomeomorphEuclideanFourBall_boundary_inclusion,
    coordinateUnlinkExteriorPlanarNeckEquatorRadialBallFamilyHomeomorph_boundary_inclusion]

end SplittingSpheres

end
