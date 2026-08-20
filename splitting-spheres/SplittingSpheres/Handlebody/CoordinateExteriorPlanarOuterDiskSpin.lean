/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.RadialSphereHomeomorphExtension
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarAllFilling
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarOuterBoundary
public import SplittingSpheres.Handlebody.PartialSphereSpinDisk

/-!
# The completely filled planar factor and its partial sphere spin

The lifted outer boundary of the planar power pullback is identified with the literal boundary
of the polynomial outer disk.  We then correct the radial disk parameterization by the radial
extension of its boundary reparameterization.  The resulting disk homeomorphism preserves the
displayed outer-circle parameter exactly.  Therefore the partial `S²`-spin of the filled outer
disk is the standard capped one-handle, hence is homeomorphic to `S⁴`.

All claims are point-set topological.  No smooth compatibility or four-manifold gluing theorem
is asserted.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-! ## The polynomial outer boundary as the exact lifted outer carrier -/

theorem sphereHandleRadius_sub_half_gt_oneEighth :
    (1 / 8 : ℝ) < sphereHandleRadius - 1 / 2 := by
  linarith [fiveEighth_lt_sphereHandleRadius]

/-- A point of the polynomial outer boundary satisfies both inner lower bounds. -/
def coordinateUnlinkExteriorPlanarOuterBoundaryToFlower
    (m : ℕ) [NeZero m]
    (z : ↑(coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m)) :
    CoordinateUnlinkExteriorPlanarFlower m := by
  have houter : ‖z.1 ^ m + (1 / 2 : ℂ)‖ = sphereHandleRadius := z.2
  have hright : (1 / 8 : ℝ) ≤ ‖z.1 ^ m‖ := by
    have htri := norm_add_le (z.1 ^ m) (1 / 2 : ℂ)
    rw [houter] at htri
    norm_num at htri ⊢
    linarith [sphereHandleRadius_sub_half_gt_oneEighth]
  have hleft : (1 / 8 : ℝ) ≤ ‖z.1 ^ m + 1‖ := by
    have hreverse := norm_sub_norm_le
      (z.1 ^ m + (1 / 2 : ℂ)) (-1 / 2 : ℂ)
    have hsub : (z.1 ^ m + (1 / 2 : ℂ)) - (-1 / 2 : ℂ) = z.1 ^ m + 1 := by
      ring
    rw [hsub, houter] at hreverse
    norm_num at hreverse ⊢
    linarith [sphereHandleRadius_sub_half_gt_oneEighth]
  refine ⟨⟨z.1, ?_⟩, houter.le, hright, hleft⟩
  intro hzero
  rw [hzero, zero_pow (NeZero.ne m), norm_zero] at hright
  norm_num at hright

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterBoundaryToFlower_val
    (m : ℕ) [NeZero m]
    (z : ↑(coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m)) :
    (coordinateUnlinkExteriorPlanarOuterBoundaryToFlower m z).1.1 = z.1 :=
  by
    change z.1 = z.1
    rfl

theorem continuous_coordinateUnlinkExteriorPlanarOuterBoundaryToFlower
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarOuterBoundaryToFlower m) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.subtype_mk _

/-- Turn a polynomial outer-boundary point into the corresponding point of the exact outer
carrier in the planar pullback. -/
def coordinateUnlinkExteriorPlanarPolynomialBoundaryToOuterCarrier
    (m : ℕ) [NeZero m]
    (z : ↑(coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m)) :
    coordinateUnlinkExteriorPlanarOuterBoundaryCarrier m := by
  let f : CoordinateUnlinkExteriorPlanarFlower m :=
    coordinateUnlinkExteriorPlanarOuterBoundaryToFlower m z
  let q : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m :=
    (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m).symm f
  have hnorm : ‖q.1.1.1.1‖ = 1 := by
    change ‖coordinateUnlinkExteriorPlanarFlowerBaseRaw m f.1‖ = 1
    rw [coordinateUnlinkExteriorPlanarFlowerBaseRaw, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr sphereHandleRadius_pos),
      norm_complexToUnlinkNormalPlane]
    change sphereHandleRadius⁻¹ * ‖z.1 ^ m + (1 / 2 : ℂ)‖ = 1
    rw [z.2, inv_mul_cancel₀ sphereHandleRadius_ne_zero]
  let u : Sphere 1 := ⟨q.1.1.1.1, mem_sphere_zero_iff_norm.mpr hnorm⟩
  refine ⟨q, ⟨u, ?_⟩⟩
  apply Subtype.ext
  apply Subtype.ext
  rfl

theorem continuous_coordinateUnlinkExteriorPlanarPolynomialBoundaryToOuterCarrier
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarPolynomialBoundaryToOuterCarrier m) := by
  apply Continuous.subtype_mk
  exact (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m).symm
    |>.continuous.comp
      (continuous_coordinateUnlinkExteriorPlanarOuterBoundaryToFlower m)

/-- Forget the carrier proof and retain the planar power coordinate, bundled in the exact
polynomial boundary. -/
def coordinateUnlinkExteriorPlanarOuterCarrierToPolynomialBoundary
    (m : ℕ) [NeZero m]
    (z : coordinateUnlinkExteriorPlanarOuterBoundaryCarrier m) :
    ↑(coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m) := by
  refine ⟨z.1.1.2.1, ?_⟩
  rcases z.2 with ⟨u, hu⟩
  have hpow :=
    coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph_apply_pow
      m z.1
  have hubase : z.1.1.1 =
      coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary u := hu.symm
  rw [hubase, coordinateUnlinkExteriorPuncturedNormalDiskCharacter_outerBoundary] at hpow
  change z.1.1.2.1 ^ m =
    (sphereHandleRadius : ℂ) * unlinkUnitCircleComplex u - (1 / 2 : ℂ) at hpow
  change ‖z.1.1.2.1 ^ m + (1 / 2 : ℂ)‖ = sphereHandleRadius
  rw [hpow]
  have hadd :
      (sphereHandleRadius : ℂ) * unlinkUnitCircleComplex u - (1 / 2 : ℂ) +
          (1 / 2 : ℂ) =
        (sphereHandleRadius : ℂ) * unlinkUnitCircleComplex u := by ring
  rw [hadd, norm_mul, norm_unlinkUnitCircleComplex]
  norm_num [abs_of_pos sphereHandleRadius_pos]

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterCarrierToPolynomialBoundary_coe
    (m : ℕ) [NeZero m]
    (z : coordinateUnlinkExteriorPlanarOuterBoundaryCarrier m) :
    (coordinateUnlinkExteriorPlanarOuterCarrierToPolynomialBoundary m z : ℂ) =
      z.1.1.2.1 :=
  rfl

theorem continuous_coordinateUnlinkExteriorPlanarOuterCarrierToPolynomialBoundary
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarOuterCarrierToPolynomialBoundary m) := by
  apply Continuous.subtype_mk
  fun_prop

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterCarrierToPolynomialBoundary_inverse
    (m : ℕ) [NeZero m]
    (z : ↑(coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m)) :
    coordinateUnlinkExteriorPlanarOuterCarrierToPolynomialBoundary m
        (coordinateUnlinkExteriorPlanarPolynomialBoundaryToOuterCarrier m z) = z := by
  apply Subtype.ext
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarPolynomialBoundaryToOuterCarrier_inverse
    (m : ℕ) [NeZero m]
    (z : coordinateUnlinkExteriorPlanarOuterBoundaryCarrier m) :
    coordinateUnlinkExteriorPlanarPolynomialBoundaryToOuterCarrier m
        (coordinateUnlinkExteriorPlanarOuterCarrierToPolynomialBoundary m z) = z := by
  apply Subtype.ext
  change (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m).symm
      (coordinateUnlinkExteriorPlanarOuterBoundaryToFlower m
        (coordinateUnlinkExteriorPlanarOuterCarrierToPolynomialBoundary m z)) = z.1
  apply (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m).injective
  apply Subtype.ext
  rfl

/-- The exact outer carrier is the polynomial outer boundary, with the power coordinate as its
literal planar coordinate. -/
def coordinateUnlinkExteriorPlanarOuterCarrierPolynomialBoundaryHomeomorph
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarOuterBoundaryCarrier m ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m) where
  toFun := coordinateUnlinkExteriorPlanarOuterCarrierToPolynomialBoundary m
  invFun := coordinateUnlinkExteriorPlanarPolynomialBoundaryToOuterCarrier m
  left_inv := coordinateUnlinkExteriorPlanarPolynomialBoundaryToOuterCarrier_inverse m
  right_inv := coordinateUnlinkExteriorPlanarOuterCarrierToPolynomialBoundary_inverse m
  continuous_toFun :=
    continuous_coordinateUnlinkExteriorPlanarOuterCarrierToPolynomialBoundary m
  continuous_invFun :=
    continuous_coordinateUnlinkExteriorPlanarPolynomialBoundaryToOuterCarrier m

/-- The original lifted outer circle, now as a homeomorphism onto the polynomial boundary. -/
def coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph
    (m : ℕ) [NeZero m] :
    Sphere 1 ≃ₜ ↑(coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m) :=
  (coordinateUnlinkExteriorPlanarOuterBoundaryHomeomorph m).trans
    (coordinateUnlinkExteriorPlanarOuterCarrierPolynomialBoundaryHomeomorph m)

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph_coe
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    (coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m u : ℂ) =
      (coordinateUnlinkExteriorPlanarOuterLift m u).1.2.1 := by
  rfl

/-! ## Correcting the disk parameterization on its boundary -/

/-- The project's Euclidean unit circle is the complex unit circle. -/
def unlinkUnitCircleHomeomorph :
    Sphere 1 ≃ₜ sphere (0 : ℂ) 1 where
  toFun u := ⟨unlinkUnitCircleComplex u, by
    rw [mem_sphere_zero_iff_norm, norm_unlinkUnitCircleComplex]⟩
  invFun z := ⟨complexToUnlinkNormalPlane z.1, by
    rw [mem_sphere_zero_iff_norm, norm_complexToUnlinkNormalPlane]
    exact mem_sphere_zero_iff_norm.mp z.2⟩
  left_inv u := by
    apply Subtype.ext
    exact complexToUnlinkNormalPlane_unlinkUnitCircleComplex u
  right_inv z := by
    apply Subtype.ext
    exact unlinkNormalPlaneToComplex_complexToUnlinkNormalPlane z.1
  continuous_toFun := by
    exact continuous_unlinkUnitCircleComplex.subtype_mk _
  continuous_invFun := by
    exact continuous_complexToUnlinkNormalPlane.comp continuous_subtype_val |>.subtype_mk _

@[simp]
theorem unlinkUnitCircleHomeomorph_coe (u : Sphere 1) :
    (unlinkUnitCircleHomeomorph u : ℂ) = unlinkUnitCircleComplex u :=
  rfl

/-- The corresponding coordinate homeomorphism of closed unit disks. -/
def unlinkUnitDiskHomeomorph :
    EuclideanClosedBall 2 ≃ₜ closedBall (0 : ℂ) 1 where
  toFun x := ⟨unlinkNormalPlaneToComplex x.1, by
    rw [mem_closedBall_zero_iff, norm_unlinkNormalPlaneToComplex]
    exact mem_closedBall_zero_iff.mp x.2⟩
  invFun z := ⟨complexToUnlinkNormalPlane z.1, by
    rw [mem_closedBall_zero_iff, norm_complexToUnlinkNormalPlane]
    exact mem_closedBall_zero_iff.mp z.2⟩
  left_inv x := by
    apply Subtype.ext
    exact complexToUnlinkNormalPlane_unlinkNormalPlaneToComplex x.1
  right_inv z := by
    apply Subtype.ext
    exact unlinkNormalPlaneToComplex_complexToUnlinkNormalPlane z.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold unlinkNormalPlaneToComplex
    fun_prop
  continuous_invFun := by
    exact continuous_complexToUnlinkNormalPlane.comp continuous_subtype_val |>.subtype_mk _

@[simp]
theorem unlinkUnitDiskHomeomorph_coe (x : EuclideanClosedBall 2) :
    (unlinkUnitDiskHomeomorph x : ℂ) = unlinkNormalPlaneToComplex x.1 :=
  rfl

/-- The self-homeomorphism of the complex unit circle which changes the radial disk
parameterization to the parameterization inherited from the lifted one-handle boundary. -/
def coordinateUnlinkExteriorPlanarOuterBoundaryReparam
    (m : ℕ) [NeZero m] :
    sphere (0 : ℂ) 1 ≃ₜ sphere (0 : ℂ) 1 :=
  unlinkUnitCircleHomeomorph.symm.trans <|
    (coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m).trans
      (planarOuterDiskBoundaryHomeomorph m).symm

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterBoundaryReparam_unitCircle
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    coordinateUnlinkExteriorPlanarOuterBoundaryReparam m
        (unlinkUnitCircleHomeomorph u) =
      (planarOuterDiskBoundaryHomeomorph m).symm
        (coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m u) := by
  simp [coordinateUnlinkExteriorPlanarOuterBoundaryReparam]

/-- The radial body and boundary homeomorphisms use the same underlying ambient map. -/
def coordinateUnlinkExteriorPlanarOuterBoundaryToDisk
    (m : ℕ) :
    C(↑(coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m),
      ↑(coordinateUnlinkExteriorPlanarOuterDiskSet m)) where
  toFun z := ⟨z.1, z.2.le⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterBoundaryToDisk_coe
    (m : ℕ)
    (z : ↑(coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m)) :
    (coordinateUnlinkExteriorPlanarOuterBoundaryToDisk m z : ℂ) = z.1 :=
  rfl

/-- The radial body and boundary homeomorphisms use the same underlying ambient map. -/
theorem planarOuterDiskHomeomorph_on_boundary
    (m : ℕ) [NeZero m] (u : sphere (0 : ℂ) 1) :
    planarOuterDiskHomeomorph m ⟨u.1, sphere_subset_closedBall u.2⟩ =
      coordinateUnlinkExteriorPlanarOuterBoundaryToDisk m
        (planarOuterDiskBoundaryHomeomorph m u) := by
  apply Subtype.ext
  rfl

/-- A disk parameterization of the polynomial outer disk whose boundary action is exactly the
lifted outer-circle parameterization. -/
def coordinateUnlinkExteriorPlanarOuterDiskParamHomeomorph
    (m : ℕ) [NeZero m] :
    EuclideanClosedBall 2 ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarOuterDiskSet m) :=
  unlinkUnitDiskHomeomorph.trans <|
    (radialSphereExtensionBallHomeomorph
      (coordinateUnlinkExteriorPlanarOuterBoundaryReparam m)).trans <|
        planarOuterDiskHomeomorph m

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterDiskParamHomeomorph_boundary
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    coordinateUnlinkExteriorPlanarOuterDiskParamHomeomorph m
        (partialSphereSpinDiskOuter u) =
      coordinateUnlinkExteriorPlanarOuterBoundaryToDisk m
        (coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m u) := by
  let uc : sphere (0 : ℂ) 1 := unlinkUnitCircleHomeomorph u
  let ucBall : closedBall (0 : ℂ) 1 :=
    ⟨uc.1, sphere_subset_closedBall uc.2⟩
  have hfirst : unlinkUnitDiskHomeomorph (partialSphereSpinDiskOuter u) = ucBall := by
    apply Subtype.ext
    rfl
  let v : sphere (0 : ℂ) 1 :=
    coordinateUnlinkExteriorPlanarOuterBoundaryReparam m uc
  let vBall : closedBall (0 : ℂ) 1 :=
    ⟨v.1, sphere_subset_closedBall v.2⟩
  have hradial :
      radialSphereExtensionBallHomeomorph
          (coordinateUnlinkExteriorPlanarOuterBoundaryReparam m) ucBall = vBall := by
    apply Subtype.ext
    rw [radialSphereExtensionBallHomeomorph_apply_val,
      radialSphereExtensionMap_of_mem_sphere]
  change planarOuterDiskHomeomorph m
      (radialSphereExtensionBallHomeomorph
        (coordinateUnlinkExteriorPlanarOuterBoundaryReparam m)
        (unlinkUnitDiskHomeomorph (partialSphereSpinDiskOuter u))) = _
  rw [hfirst, hradial, planarOuterDiskHomeomorph_on_boundary]
  apply Subtype.ext
  change ((planarOuterDiskBoundaryHomeomorph m
      (coordinateUnlinkExteriorPlanarOuterBoundaryReparam m
        (unlinkUnitCircleHomeomorph u)) :
      ↑(coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m)) : ℂ) = _
  rw [coordinateUnlinkExteriorPlanarOuterBoundaryReparam_unitCircle,
    (planarOuterDiskBoundaryHomeomorph m).apply_symm_apply]
  rfl

/-! ## The completely filled partial spin is a four-sphere -/

/-- The lifted outer circle, now regarded as a continuous map into the filled polynomial disk. -/
def coordinateUnlinkExteriorPlanarOuterDiskOuter
    (m : ℕ) [NeZero m] :
    C(Sphere 1, ↑(coordinateUnlinkExteriorPlanarOuterDiskSet m)) where
  toFun u := coordinateUnlinkExteriorPlanarOuterBoundaryToDisk m
    (coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m u)
  continuous_toFun :=
    (coordinateUnlinkExteriorPlanarOuterBoundaryToDisk m).continuous.comp
      (coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m).continuous

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterDiskOuter_apply
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    coordinateUnlinkExteriorPlanarOuterDiskOuter m u =
      coordinateUnlinkExteriorPlanarOuterBoundaryToDisk m
        (coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m u) :=
  rfl

/-- The partial spin of the completely filled planar factor is the standard disk partial spin. -/
def coordinateUnlinkExteriorPlanarOuterDiskPartialSpinHomeomorphDisk :
    ∀ (m : ℕ) [NeZero m],
      PartialSphereSpin (coordinateUnlinkExteriorPlanarOuterDiskOuter m) ≃ₜ
        DiskPartialSphereSpin := fun m _ ↦
  partialSphereSpinCongr
    (coordinateUnlinkExteriorPlanarOuterDiskOuter m)
    partialSphereSpinDiskOuter
    (coordinateUnlinkExteriorPlanarOuterDiskParamHomeomorph m).symm
    (fun u ↦ by
      change (coordinateUnlinkExteriorPlanarOuterDiskParamHomeomorph m).symm
          (coordinateUnlinkExteriorPlanarOuterBoundaryToDisk m
            (coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m u)) =
        partialSphereSpinDiskOuter u
      rw [← coordinateUnlinkExteriorPlanarOuterDiskParamHomeomorph_boundary,
        (coordinateUnlinkExteriorPlanarOuterDiskParamHomeomorph m).symm_apply_apply])

/-- Consequently the completely filled partial spin is homeomorphic to the standard
four-sphere. -/
def coordinateUnlinkExteriorPlanarOuterDiskPartialSpinHomeomorphSphere
    (m : ℕ) [NeZero m] :
    PartialSphereSpin (coordinateUnlinkExteriorPlanarOuterDiskOuter m) ≃ₜ Sphere 4 :=
  (coordinateUnlinkExteriorPlanarOuterDiskPartialSpinHomeomorphDisk m).trans
    diskPartialSphereSpinHomeomorphSphere

end SplittingSpheres
