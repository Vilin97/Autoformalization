/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.ClosedBallMaps
public import SplittingSpheres.Handlebody.CoreExtensionDiffeomorph
public import SplittingSpheres.Handlebody.SphereHandleInterior

/-!
# Smooth core-supported one-handle extensions

The explicit product coordinates on the open one-handle region show that the direct spherical
extension of every boundary-relative one-handle diffeomorphism is smooth on the inner band.  A
core-support condition supplies identity on the complementary outer band, so the locality layer
can bundle the extension as a genuine smooth diffeomorphism of the literal four-sphere.

No smooth gluing theorem is assumed here: smoothness on the inner region is proved through the
explicit interior diffeomorphism, while smoothness near the seam follows from literal identity on
an open neighborhood.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open TopologicalSpace
open scoped ContDiff Manifold Topology

namespace SplittingSpheres

/-- The inner band used by the locality argument is exactly the open one-handle region used by
the explicit interior product coordinates. -/
theorem sphereHandleInnerBand_eq_oneRegion :
    sphereHandleInnerBand = sphereHandleOneRegion := by
  ext q
  rfl

/-- The inclusion of the open Euclidean three-ball into the convex closed-ball model is smooth. -/
theorem contMDiff_sphereHandleOpenBallToClosedBall :
    ContMDiff (modelWithCornersSelf ℝ SphereHandleSecond)
      (euclideanClosedBallModel 3) ∞ sphereHandleOpenBallToClosedBall := by
  apply contMDiff_euclideanClosedBall_of_contMDiff_val
  exact contMDiff_subtype_val

/-- Include the open interior product into the compact one-handle piece. -/
def sphereHandleInteriorProductInclusion
    (p : Sphere 1 × SphereHandleOpenUnitBall) : OneHandlePiece :=
  (p.1, sphereHandleOpenBallToClosedBall p.2)

@[simp]
theorem sphereHandleInteriorProductInclusion_apply
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    sphereHandleInteriorProductInclusion p =
      (p.1, sphereHandleOpenBallToClosedBall p.2) :=
  rfl

/-- The product inclusion into the compact one-handle is smooth for the literal product and
convex closed-ball models. -/
theorem contMDiff_sphereHandleInteriorProductInclusion :
    ContMDiff sphereHandleInteriorProductModel oneHandlePieceModel ∞
      sphereHandleInteriorProductInclusion :=
  contMDiff_fst.prodMk
    (contMDiff_sphereHandleOpenBallToClosedBall.comp contMDiff_snd)

/-- Exact action of a direct extension in the explicit open one-handle coordinates. -/
@[simp]
theorem directCappedOneHandleExtensionSphere_interiorDiffeomorph
    (f : OneHandleBoundaryRelativeDiff)
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    directCappedOneHandleExtensionSphere f
        ((sphereHandleInteriorDiffeomorph p : SphereHandleOneRegion) : Sphere 4) =
      oneHandleSphereMap (f.1 (sphereHandleInteriorProductInclusion p)) := by
  rw [sphereHandleInteriorDiffeomorph_apply_coe,
    sphereHandleInteriorProductInclusion_apply,
    directCappedOneHandleExtensionSphere_oneHandle]

/-- The direct extension of an arbitrary boundary-relative one-handle diffeomorphism is smooth
after restricting its source to the explicit open one-handle region. -/
theorem contMDiff_directCappedOneHandleExtensionSphere_restrict_oneRegion
    (f : OneHandleBoundaryRelativeDiff) :
    ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun q : SphereHandleOneRegion ↦
        directCappedOneHandleExtensionSphere f q.1) := by
  have hformula : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun q : SphereHandleOneRegion ↦
        oneHandleSphereMap
          (f.1 (sphereHandleInteriorProductInclusion
            (sphereHandleInteriorDiffeomorph.symm q)))) :=
    contMDiff_oneHandleSphereMap.comp <|
      f.1.contMDiff.comp <|
        contMDiff_sphereHandleInteriorProductInclusion.comp
          sphereHandleInteriorDiffeomorph.symm.contMDiff
  apply hformula.congr
  intro q
  have hq : q.1 = oneHandleSphereMap
      (sphereHandleInteriorProductInclusion
        (sphereHandleInteriorDiffeomorph.symm q)) := by
    symm
    rw [sphereHandleInteriorProductInclusion_apply,
      ← sphereHandleInteriorDiffeomorph_apply_coe]
    exact congr_arg Subtype.val (sphereHandleInteriorDiffeomorph.apply_symm_apply q)
  rw [hq, directCappedOneHandleExtensionSphere_oneHandle]

/-- Equivalent inner-band form of the restricted smoothness theorem. -/
theorem contMDiff_directCappedOneHandleExtensionSphere_restrict_innerBand
    (f : OneHandleBoundaryRelativeDiff) :
    ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun q : sphereHandleInnerBand ↦
        directCappedOneHandleExtensionSphere f q.1) := by
  rw [sphereHandleInnerBand_eq_oneRegion]
  exact contMDiff_directCappedOneHandleExtensionSphere_restrict_oneRegion f

/-- Every boundary-relative one-handle diffeomorphism has a smooth direct extension on the inner
band.  No support hypothesis is needed for this local statement. -/
theorem contMDiffOn_directCappedOneHandleExtensionSphere_innerBand
    (f : OneHandleBoundaryRelativeDiff) :
    ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (directCappedOneHandleExtensionSphere f) sphereHandleInnerBand := by
  apply (contMDiffOn_sphereHandleInnerBand_iff_restrict _).mpr
  exact contMDiff_directCappedOneHandleExtensionSphere_restrict_innerBand f

/-- The unconditional smooth extension of a core-supported boundary-relative one-handle
diffeomorphism to the literal four-sphere. -/
def smoothOneHandleCoreExtensionDiffeomorph
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho) :
    TauCeti.Diff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (Sphere 4) ∞ :=
  oneHandleCoreExtensionDiffeomorph hrho f
    (contMDiffOn_directCappedOneHandleExtensionSphere_innerBand f.1)
    (contMDiffOn_directCappedOneHandleExtensionSphere_innerBand (f⁻¹).1)

@[simp]
theorem smoothOneHandleCoreExtensionDiffeomorph_apply
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho) (q : Sphere 4) :
    smoothOneHandleCoreExtensionDiffeomorph hrho f q =
      directCappedOneHandleExtensionSphere f.1 q :=
  rfl

/-- Exact action of the smooth core extension in the explicit open one-handle coordinates. -/
@[simp]
theorem smoothOneHandleCoreExtensionDiffeomorph_interiorDiffeomorph
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho)
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    smoothOneHandleCoreExtensionDiffeomorph hrho f
        ((sphereHandleInteriorDiffeomorph p : SphereHandleOneRegion) : Sphere 4) =
      oneHandleSphereMap (f.1.1 (sphereHandleInteriorProductInclusion p)) := by
  rw [smoothOneHandleCoreExtensionDiffeomorph_apply,
    directCappedOneHandleExtensionSphere_interiorDiffeomorph]

/-- The inverse smooth extension is exactly the direct extension of the inverse core-supported
diffeomorphism. -/
@[simp]
theorem smoothOneHandleCoreExtensionDiffeomorph_symm_apply
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho) (q : Sphere 4) :
    (smoothOneHandleCoreExtensionDiffeomorph hrho f).symm q =
      directCappedOneHandleExtensionSphere (f⁻¹).1 q :=
  oneHandleCoreExtensionDiffeomorph_symm_apply _ _ _ _ _

/-- Forgetting smoothness recovers the previously constructed direct extension homeomorphism. -/
@[simp]
theorem smoothOneHandleCoreExtensionDiffeomorph_toHomeomorph
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho) :
    (smoothOneHandleCoreExtensionDiffeomorph hrho f).toHomeomorph =
      directCappedOneHandleExtensionSphere f.1 :=
  oneHandleCoreExtensionDiffeomorph_toHomeomorph _ _ _ _

/-- The smooth extension is pointwise the identity on the outer band. -/
theorem smoothOneHandleCoreExtensionDiffeomorph_eq_on_outerBand
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho)
    (q : sphereHandleOuterBand rho) :
    smoothOneHandleCoreExtensionDiffeomorph hrho f q.1 = q.1 :=
  oneHandleCoreExtensionDiffeomorph_eq_on_outerBand _ _ _ _ _

/-- The inverse smooth extension is also pointwise the identity on the outer band. -/
theorem smoothOneHandleCoreExtensionDiffeomorph_symm_eq_on_outerBand
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho)
    (q : sphereHandleOuterBand rho) :
    (smoothOneHandleCoreExtensionDiffeomorph hrho f).symm q.1 = q.1 :=
  oneHandleCoreExtensionDiffeomorph_symm_eq_on_outerBand _ _ _ _ _

/-- Smooth core extension is functorial under composition. -/
def smoothOneHandleCoreExtensionHom
    {rho : ℝ} (hrho : rho < 1) :
    OneHandleCoreSupportedRelativeDiff rho →*
      TauCeti.Diff
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (Sphere 4) ∞ where
  toFun := smoothOneHandleCoreExtensionDiffeomorph hrho
  map_one' := by
    apply Diffeomorph.ext
    intro q
    rw [smoothOneHandleCoreExtensionDiffeomorph_apply]
    change directCappedOneHandleExtensionSphere
      (1 : OneHandleBoundaryRelativeDiff) q = q
    rw [directCappedOneHandleExtensionSphere_one]
    rfl
  map_mul' f g := by
    apply Diffeomorph.ext
    intro q
    rw [smoothOneHandleCoreExtensionDiffeomorph_apply,
      TauCeti.Diffeomorph.mul_apply,
      smoothOneHandleCoreExtensionDiffeomorph_apply,
      smoothOneHandleCoreExtensionDiffeomorph_apply]
    change directCappedOneHandleExtensionSphere (f.1 * g.1) q = _
    rw [directCappedOneHandleExtensionSphere_mul, Homeomorph.mul_apply]

@[simp]
theorem smoothOneHandleCoreExtensionHom_apply
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho) (q : Sphere 4) :
    smoothOneHandleCoreExtensionHom hrho f q =
      directCappedOneHandleExtensionSphere f.1 q :=
  rfl

/-- The smooth core-extension homomorphism is faithful. -/
theorem smoothOneHandleCoreExtensionHom_injective
    {rho : ℝ} (hrho : rho < 1) :
    Injective (smoothOneHandleCoreExtensionHom hrho) := by
  intro f g h
  apply oneHandleCoreExtensionSphereHom_injective rho
  change directCappedOneHandleExtensionSphere f.1 =
    directCappedOneHandleExtensionSphere g.1
  have hh := congrArg Diffeomorph.toHomeomorph h
  change (smoothOneHandleCoreExtensionDiffeomorph hrho f).toHomeomorph =
    (smoothOneHandleCoreExtensionDiffeomorph hrho g).toHomeomorph at hh
  simpa only [smoothOneHandleCoreExtensionDiffeomorph_toHomeomorph] using hh

/-- The same faithful extension homomorphism, viewed as fixing the empty subset pointwise. -/
def smoothOneHandleCoreExtensionRelativeHom
    {rho : ℝ} (hrho : rho < 1) :
    OneHandleCoreSupportedRelativeDiff rho →*
      TauCeti.RelativeDiff
        (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (Sphere 4) ∞ (∅ : Set (Sphere 4)) :=
  (smoothOneHandleCoreExtensionHom hrho).codRestrict
    (TauCeti.Diffeomorph.fixingSubgroup (∅ : Set (Sphere 4))) (by
      intro f
      apply TauCeti.Diffeomorph.mem_fixingSubgroup_of_forall
      intro q hq
      exact hq.elim)

@[simp]
theorem smoothOneHandleCoreExtensionRelativeHom_coe
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho) :
    (smoothOneHandleCoreExtensionRelativeHom hrho f).1 =
      smoothOneHandleCoreExtensionDiffeomorph hrho f :=
  rfl

@[simp]
theorem smoothOneHandleCoreExtensionRelativeHom_apply
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho) (q : Sphere 4) :
    (smoothOneHandleCoreExtensionRelativeHom hrho f).1 q =
      directCappedOneHandleExtensionSphere f.1 q :=
  rfl

/-- Viewing the smooth extension as relative to the empty set preserves faithfulness. -/
theorem smoothOneHandleCoreExtensionRelativeHom_injective
    {rho : ℝ} (hrho : rho < 1) :
    Injective (smoothOneHandleCoreExtensionRelativeHom hrho) := by
  intro f g h
  apply smoothOneHandleCoreExtensionHom_injective hrho
  exact congrArg Subtype.val h

end SplittingSpheres
