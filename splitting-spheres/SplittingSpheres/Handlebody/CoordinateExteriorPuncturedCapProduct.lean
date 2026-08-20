/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPowerPieceCover

/-!
# Product reduction of the punctured-cap power pullback

The punctured-cap face of the radius-`1/8` coordinate exterior is literally a punctured closed
normal disk times `S²`.  The right-normal character depends only on the disk coordinate.  This
file packages those two facts as homeomorphisms and identifies the restricted power pullback
with the product of a planar power pullback and the unchanged `S²` factor.

Everything here is point-set topology.  No surface classification, smooth structure, or graph
thickening is asserted.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

/-! ## The punctured cap as an exact product -/

/-- The planar normal-disk factor of the radius-`1/8` punctured cap. -/
abbrev CoordinateUnlinkExteriorPuncturedNormalDisk : Type :=
  ↑(unlinkPuncturedNormalDiskSet (1 / 8 : ℝ))

/-- The proved set equality for the punctured cap, bundled as a homeomorphism to the product of
its planar factor with the entire sphere factor. -/
def coordinateUnlinkExteriorPuncturedCapProductHomeomorph :
    UnlinkPuncturedCap (1 / 8 : ℝ) ≃ₜ
      CoordinateUnlinkExteriorPuncturedNormalDisk × Sphere 2 :=
  (Homeomorph.setCongr (unlinkPuncturedCapSet_eq_prod (1 / 8 : ℝ))).trans
    ((Homeomorph.Set.prod (unlinkPuncturedNormalDiskSet (1 / 8 : ℝ))
      (univ : Set (Sphere 2))).trans
        ((Homeomorph.refl CoordinateUnlinkExteriorPuncturedNormalDisk).prodCongr
          (Homeomorph.Set.univ (Sphere 2))))

@[simp]
theorem coordinateUnlinkExteriorPuncturedCapProductHomeomorph_fst_val
    (x : UnlinkPuncturedCap (1 / 8 : ℝ)) :
    (coordinateUnlinkExteriorPuncturedCapProductHomeomorph x).1.1 = x.1.1 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPuncturedCapProductHomeomorph_snd
    (x : UnlinkPuncturedCap (1 / 8 : ℝ)) :
    (coordinateUnlinkExteriorPuncturedCapProductHomeomorph x).2 = x.1.2 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPuncturedCapProductHomeomorph_symm_fst_val
    (a : CoordinateUnlinkExteriorPuncturedNormalDisk) (x : Sphere 2) :
    (coordinateUnlinkExteriorPuncturedCapProductHomeomorph.symm (a, x)).1.1 = a.1 := by
  have h := coordinateUnlinkExteriorPuncturedCapProductHomeomorph.apply_symm_apply (a, x)
  exact congrArg (fun y ↦ y.1.1) h

@[simp]
theorem coordinateUnlinkExteriorPuncturedCapProductHomeomorph_symm_snd
    (a : CoordinateUnlinkExteriorPuncturedNormalDisk) (x : Sphere 2) :
    (coordinateUnlinkExteriorPuncturedCapProductHomeomorph.symm (a, x)).1.2 = x := by
  have h := coordinateUnlinkExteriorPuncturedCapProductHomeomorph.apply_symm_apply (a, x)
  exact congrArg Prod.snd h

/-! ## The planar character -/

/-- The displayed planar formula never vanishes on the punctured normal-disk factor. -/
theorem coordinateUnlinkExteriorPuncturedNormalDiskCharacter_ne_zero
    (a : CoordinateUnlinkExteriorPuncturedNormalDisk) :
    unlinkNormalPlaneToComplex
        (sphereHandleRadius • a.1.1 - standardUnlinkNormalCenter 1) ≠ 0 := by
  let x : Sphere 2 := Classical.choice <| by
    obtain ⟨x⟩ :=
      (NormedSpace.sphere_nonempty
        (E := EuclideanSpace ℝ (Fin 3)) (x := 0) (r := 1) |>.mpr zero_le_one).to_subtype
    exact ⟨x⟩
  let y : UnlinkPuncturedCap (1 / 8 : ℝ) :=
    coordinateUnlinkExteriorPuncturedCapProductHomeomorph.symm (a, x)
  have hne := (coordinateUnlinkExteriorPushoutRightNormalMap
    (coordinateUnlinkExteriorPushoutPuncturedCapInclusion y)).2
  rw [coordinateUnlinkExteriorPushoutRightNormalMap_puncturedCap] at hne
  simpa [y] using hne

/-- The right-normal character on the punctured normal disk alone. -/
def coordinateUnlinkExteriorPuncturedNormalDiskCharacter
    (a : CoordinateUnlinkExteriorPuncturedNormalDisk) : {z : ℂ // z ≠ 0} :=
  ⟨unlinkNormalPlaneToComplex
      (sphereHandleRadius • a.1.1 - standardUnlinkNormalCenter 1),
    coordinateUnlinkExteriorPuncturedNormalDiskCharacter_ne_zero a⟩

@[simp]
theorem coordinateUnlinkExteriorPuncturedNormalDiskCharacter_coe
    (a : CoordinateUnlinkExteriorPuncturedNormalDisk) :
    (coordinateUnlinkExteriorPuncturedNormalDiskCharacter a : ℂ) =
      unlinkNormalPlaneToComplex
        (sphereHandleRadius • a.1.1 - standardUnlinkNormalCenter 1) :=
  rfl

theorem continuous_coordinateUnlinkExteriorPuncturedNormalDiskCharacter :
    Continuous coordinateUnlinkExteriorPuncturedNormalDiskCharacter := by
  have hval : Continuous (fun a : CoordinateUnlinkExteriorPuncturedNormalDisk ↦
      (a.1.1 : SphereHandleFirst)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hdisplacement : Continuous
      (fun a : CoordinateUnlinkExteriorPuncturedNormalDisk ↦
        sphereHandleRadius • a.1.1 - standardUnlinkNormalCenter 1) :=
    by fun_prop
  apply Continuous.subtype_mk
  exact continuous_unlinkNormalPlaneToComplex.comp hdisplacement

/-- The cap character is exactly the planar character of the first product coordinate. -/
@[simp]
theorem coordinateUnlinkExteriorPushoutRightNormalMap_puncturedCap_eq_planar
    (x : UnlinkPuncturedCap (1 / 8 : ℝ)) :
    coordinateUnlinkExteriorPushoutRightNormalMap
        (coordinateUnlinkExteriorPushoutPuncturedCapInclusion x) =
      coordinateUnlinkExteriorPuncturedNormalDiskCharacter
        (coordinateUnlinkExteriorPuncturedCapProductHomeomorph x).1 := by
  apply Subtype.ext
  rw [coordinateUnlinkExteriorPushoutRightNormalMap_puncturedCap,
    coordinateUnlinkExteriorPuncturedNormalDiskCharacter_coe,
    coordinateUnlinkExteriorPuncturedCapProductHomeomorph_fst_val]

/-- Function-level factorization of the cap character through the product projection. -/
theorem coordinateUnlinkExteriorPushoutRightNormalMap_puncturedCap_factorization :
    coordinateUnlinkExteriorPushoutRightNormalMap ∘
        coordinateUnlinkExteriorPushoutPuncturedCapInclusion =
      coordinateUnlinkExteriorPuncturedNormalDiskCharacter ∘
        Prod.fst ∘ coordinateUnlinkExteriorPuncturedCapProductHomeomorph := by
  funext x
  exact coordinateUnlinkExteriorPushoutRightNormalMap_puncturedCap_eq_planar x

/-! ## Product decomposition of the restricted power pullback -/

/-- The planar power pullback defined by the punctured-disk character. -/
abbrev CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback (m : ℕ) : Type :=
  TopologicalCoverPullback (nonzeroComplexPow m)
    coordinateUnlinkExteriorPuncturedNormalDiskCharacter

/-- Projection of the planar power pullback to its punctured-disk base. -/
def coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj (m : ℕ) :
    CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m →
      CoordinateUnlinkExteriorPuncturedNormalDisk :=
  topologicalCoverPullbackProj (nonzeroComplexPow m)
    coordinateUnlinkExteriorPuncturedNormalDiskCharacter

@[simp]
theorem coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj_apply
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :
    coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj m z = z.1.1 :=
  rfl

/-- Split a cap-pullback point into its planar pullback coordinate and its unchanged `S²`
coordinate. -/
def coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph (m : ℕ) :
    CoordinateUnlinkExteriorPuncturedCapPowerPullback m ≃ₜ
      CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m × Sphere 2 where
  toFun z :=
    (⟨((coordinateUnlinkExteriorPuncturedCapProductHomeomorph z.1.1).1, z.1.2),
      (coordinateUnlinkExteriorPushoutRightNormalMap_puncturedCap_eq_planar z.1.1).symm.trans
        z.2⟩,
      (coordinateUnlinkExteriorPuncturedCapProductHomeomorph z.1.1).2)
  invFun z :=
    ⟨(coordinateUnlinkExteriorPuncturedCapProductHomeomorph.symm (z.1.1.1, z.2),
        z.1.1.2), by
      have hfactor := coordinateUnlinkExteriorPushoutRightNormalMap_puncturedCap_eq_planar
        (coordinateUnlinkExteriorPuncturedCapProductHomeomorph.symm (z.1.1.1, z.2))
      rw [coordinateUnlinkExteriorPuncturedCapProductHomeomorph.apply_symm_apply] at hfactor
      exact hfactor.trans z.1.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact coordinateUnlinkExteriorPuncturedCapProductHomeomorph.symm_apply_apply z.1.1
    · rfl
  right_inv z := by
    have hprod := coordinateUnlinkExteriorPuncturedCapProductHomeomorph.apply_symm_apply
      (z.1.1.1, z.2)
    have hbase :
        (coordinateUnlinkExteriorPuncturedCapProductHomeomorph
          (coordinateUnlinkExteriorPuncturedCapProductHomeomorph.symm
            (z.1.1.1, z.2))).1 = z.1.1.1 :=
      congrArg (fun q : CoordinateUnlinkExteriorPuncturedNormalDisk × Sphere 2 ↦ q.1) hprod
    have hsphere :
        (coordinateUnlinkExteriorPuncturedCapProductHomeomorph
          (coordinateUnlinkExteriorPuncturedCapProductHomeomorph.symm
            (z.1.1.1, z.2))).2 = z.2 :=
      congrArg (fun q : CoordinateUnlinkExteriorPuncturedNormalDisk × Sphere 2 ↦ q.2) hprod
    exact Prod.ext
      (Subtype.ext (Prod.ext hbase rfl)) hsphere
  continuous_toFun := by
    have hbase : Continuous (fun z : CoordinateUnlinkExteriorPuncturedCapPowerPullback m ↦
        coordinateUnlinkExteriorPuncturedCapProductHomeomorph z.1.1) :=
      coordinateUnlinkExteriorPuncturedCapProductHomeomorph.continuous.comp
        (continuous_fst.comp continuous_subtype_val)
    have hfiber : Continuous
        (fun z : CoordinateUnlinkExteriorPuncturedCapPowerPullback m ↦ z.1.2) :=
      continuous_snd.comp continuous_subtype_val
    exact (Continuous.subtype_mk ((continuous_fst.comp hbase).prodMk hfiber) _).prodMk
      (continuous_snd.comp hbase)
  continuous_invFun := by
    have hpair : Continuous
        (fun z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m × Sphere 2 ↦
          (z.1.1.1, z.2)) :=
      (continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
    have hbase : Continuous
        (fun z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m × Sphere 2 ↦
          coordinateUnlinkExteriorPuncturedCapProductHomeomorph.symm (z.1.1.1, z.2)) :=
      coordinateUnlinkExteriorPuncturedCapProductHomeomorph.symm.continuous.comp hpair
    have hfiber : Continuous
        (fun z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m × Sphere 2 ↦
          z.1.1.2) :=
      continuous_snd.comp (continuous_subtype_val.comp continuous_fst)
    exact Continuous.subtype_mk (hbase.prodMk hfiber) _

@[simp]
theorem coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph_planarBase
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedCapPowerPullback m) :
    (coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m z).1.1.1 =
      (coordinateUnlinkExteriorPuncturedCapProductHomeomorph
        (coordinateUnlinkExteriorPuncturedCapPowerPullbackProj m z)).1 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph_fiberCoordinate
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedCapPowerPullback m) :
    (coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m z).1.1.2 =
      z.1.2 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph_sphereCoordinate
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedCapPowerPullback m) :
    (coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m z).2 =
      (coordinateUnlinkExteriorPuncturedCapProductHomeomorph
        (coordinateUnlinkExteriorPuncturedCapPowerPullbackProj m z)).2 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph_proj
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedCapPowerPullback m) :
    coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj m
        (coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m z).1 =
      (coordinateUnlinkExteriorPuncturedCapProductHomeomorph
        (coordinateUnlinkExteriorPuncturedCapPowerPullbackProj m z)).1 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph_symm_fiberCoordinate
    (m : ℕ)
    (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m × Sphere 2) :
    ((coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m).symm z).1.2 =
      z.1.1.2 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph_symm_proj
    (m : ℕ)
    (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m × Sphere 2) :
    coordinateUnlinkExteriorPuncturedCapProductHomeomorph
        (coordinateUnlinkExteriorPuncturedCapPowerPullbackProj m
          ((coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m).symm z)) =
      (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj m z.1, z.2) := by
  change coordinateUnlinkExteriorPuncturedCapProductHomeomorph
      (coordinateUnlinkExteriorPuncturedCapProductHomeomorph.symm (z.1.1.1, z.2)) =
    (z.1.1.1, z.2)
  exact coordinateUnlinkExteriorPuncturedCapProductHomeomorph.apply_symm_apply _

/-! ## Planar covering consequences -/

theorem isCoveringMap_coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj
    (m : ℕ) [NeZero m] :
    IsCoveringMap (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj m) :=
  SplittingSpheres.IsCoveringMap.pullback (isCoveringMap_nonzeroComplexPow m)
    continuous_coordinateUnlinkExteriorPuncturedNormalDiskCharacter

theorem natCard_coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj_fiber
    (m : ℕ) [NeZero m] (a : CoordinateUnlinkExteriorPuncturedNormalDisk) :
    Nat.card
        (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj m ⁻¹' {a}) = m := by
  calc
    Nat.card
        (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj m ⁻¹' {a}) =
        Nat.card (nonzeroComplexPow m ⁻¹'
          {coordinateUnlinkExteriorPuncturedNormalDiskCharacter a}) :=
      Nat.card_congr (topologicalCoverPullbackFiberEquiv
        (nonzeroComplexPow m)
        coordinateUnlinkExteriorPuncturedNormalDiskCharacter a)
    _ = m := natCard_nonzeroComplexPow_fiber m _

end SplittingSpheres
