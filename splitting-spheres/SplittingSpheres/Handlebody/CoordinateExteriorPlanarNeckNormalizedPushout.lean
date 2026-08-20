/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutCongr
public import SplittingSpheres.Foundations.TopologicalPushoutProduct
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarLeftHalfTrivialization

/-!
# Annulus-normalized neck pushout

The two closed polynomial halves of the planar flower have already been identified with,
respectively, `ZMod m` labelled copies of the standard annulus and one standard annulus.  This
file conjugates the two lifted-neck attaching maps through those homeomorphisms and transports
the proved planar neck pushout to the resulting normalized diagram.

The normalized left attaching map retains its `ZMod m` label literally.  Both normalized maps
are exact conjugates of the original attaching maps, so their compatibility with the original
closed-half inclusions is recorded without any new geometric gluing argument.

The final section distributes a product with `Sphere 2` over this normalized pushout.  No
boundary-sector order, separation, surface classification, or smoothness statement is made.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

/-! ## Normalized pieces -/

/-- The left normalized piece: one standard closed annulus for every `ZMod m` label. -/
abbrev CoordinateUnlinkExteriorPlanarNormalizedLeftHalf (m : ℕ) : Type :=
  ZMod m × PartialSphereSpinAnnulus

/-- The right normalized piece is one standard closed annulus. -/
abbrev CoordinateUnlinkExteriorPlanarNormalizedRightHalf : Type :=
  PartialSphereSpinAnnulus

/-- Identify the labelled left annuli with the actual closed left flower half. -/
def coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNormalizedLeftHalf m ≃ₜ
      CoordinateUnlinkExteriorPlanarFlowerLeftHalf m :=
  ((Homeomorph.refl (ZMod m)).prodCongr
      coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph).trans
    (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m)

@[simp]
theorem coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph_apply
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNormalizedLeftHalf m) :
    coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m x =
      coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m
        (x.1, coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph x.2) :=
  rfl

/-- Identify the normalized right annulus with the actual closed right flower half. -/
abbrev coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNormalizedRightHalf ≃ₜ
      CoordinateUnlinkExteriorPlanarFlowerRightHalf m :=
  coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m

/-! ## Conjugated seam maps -/

/-- The normalized left seam map, defined as the exact inverse conjugate of the original one. -/
def coordinateUnlinkExteriorPlanarNormalizedLeftSeam
    (m : ℕ) [NeZero m] :
    C(ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval,
      CoordinateUnlinkExteriorPlanarNormalizedLeftHalf m) where
  toFun x := (coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m).symm
    (coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m x)
  continuous_toFun :=
    (coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m).symm.continuous.comp
      (coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m).continuous

@[simp]
theorem coordinateUnlinkExteriorPlanarNormalizedLeftSeam_apply
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarNormalizedLeftSeam m x =
      (x.1, coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.symm
        (coordinateUnlinkExteriorPlanarNeckBaseArcToBaseLeftHalf x.2)) := by
  apply (coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m).injective
  change coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m
      ((coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m).symm
        (coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m x)) = _
  rw [(coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m).apply_symm_apply]
  change coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m x =
    coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m
      (x.1, coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph
        (coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.symm
          (coordinateUnlinkExteriorPlanarNeckBaseArcToBaseLeftHalf x.2)))
  rw [coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.apply_symm_apply]
  exact (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization_neckArc m x.1 x.2).symm

@[simp]
theorem coordinateUnlinkExteriorPlanarNormalizedLeftSeam_fst
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m x).1 = x.1 := by
  rw [coordinateUnlinkExteriorPlanarNormalizedLeftSeam_apply]

/-- The normalized right seam map, defined as the exact inverse conjugate of the original one. -/
def coordinateUnlinkExteriorPlanarNormalizedRightSeam
    (m : ℕ) [NeZero m] :
    C(ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval,
      CoordinateUnlinkExteriorPlanarNormalizedRightHalf) where
  toFun x := (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m).symm
    (coordinateUnlinkExteriorPlanarNeckArcToRightHalf m x)
  continuous_toFun :=
    (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m).symm.continuous.comp
      (coordinateUnlinkExteriorPlanarNeckArcToRightHalf m).continuous

@[simp]
theorem coordinateUnlinkExteriorPlanarNormalizedRightSeam_apply
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarNormalizedRightSeam m x =
      (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m).symm
        (coordinateUnlinkExteriorPlanarNeckArcToRightHalf m x) :=
  rfl

theorem coordinateUnlinkExteriorPlanarNormalizedLeftSeam_conjugacy
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m
        (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m x) =
      coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m x :=
  (coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m).apply_symm_apply _

theorem coordinateUnlinkExteriorPlanarNormalizedRightSeam_conjugacy
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m
        (coordinateUnlinkExteriorPlanarNormalizedRightSeam m x) =
      coordinateUnlinkExteriorPlanarNeckArcToRightHalf m x :=
  (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m).apply_symm_apply _

theorem injective_coordinateUnlinkExteriorPlanarNormalizedLeftSeam
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m) := by
  intro x y hxy
  apply injective_coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m
  rw [← coordinateUnlinkExteriorPlanarNormalizedLeftSeam_conjugacy m x,
    ← coordinateUnlinkExteriorPlanarNormalizedLeftSeam_conjugacy m y, hxy]

theorem injective_coordinateUnlinkExteriorPlanarNormalizedRightSeam
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNormalizedRightSeam m) := by
  intro x y hxy
  apply injective_coordinateUnlinkExteriorPlanarNeckArcToRightHalf m
  rw [← coordinateUnlinkExteriorPlanarNormalizedRightSeam_conjugacy m x,
    ← coordinateUnlinkExteriorPlanarNormalizedRightSeam_conjugacy m y, hxy]

/-! ## The normalized planar pushout -/

/-- The pushout of the `m` labelled left annuli and the single right annulus along the
conjugated lifted-neck maps. -/
abbrev CoordinateUnlinkExteriorPlanarNormalizedNeckPushout
    (m : ℕ) [NeZero m] : Type :=
  TopologicalPushout
    (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m)
    (coordinateUnlinkExteriorPlanarNormalizedRightSeam m)

/-- Congruence from the annulus-normalized diagram to the original closed-half diagram. -/
def coordinateUnlinkExteriorPlanarNormalizedNeckPushoutCongr
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNormalizedNeckPushout m ≃ₜ
      TopologicalPushout
        (coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m)
        (coordinateUnlinkExteriorPlanarNeckArcToRightHalf m) :=
  topologicalPushoutCongr
    (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m)
    (coordinateUnlinkExteriorPlanarNormalizedRightSeam m)
    (coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m)
    (coordinateUnlinkExteriorPlanarNeckArcToRightHalf m)
    (Homeomorph.refl
      (ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval))
    (coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m)
    (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m)
    (fun x ↦ by
      simpa using coordinateUnlinkExteriorPlanarNormalizedLeftSeam_conjugacy m x)
    (fun x ↦ by
      exact coordinateUnlinkExteriorPlanarNormalizedRightSeam_conjugacy m x)

@[simp]
theorem coordinateUnlinkExteriorPlanarNormalizedNeckPushoutCongr_inl
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNormalizedLeftHalf m) :
    coordinateUnlinkExteriorPlanarNormalizedNeckPushoutCongr m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m)
          (coordinateUnlinkExteriorPlanarNormalizedRightSeam m) x) =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m)
        (coordinateUnlinkExteriorPlanarNeckArcToRightHalf m)
        (coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m x) := by
  apply topologicalPushoutCongr_inl

@[simp]
theorem coordinateUnlinkExteriorPlanarNormalizedNeckPushoutCongr_inr
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNormalizedRightHalf) :
    coordinateUnlinkExteriorPlanarNormalizedNeckPushoutCongr m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m)
          (coordinateUnlinkExteriorPlanarNormalizedRightSeam m) x) =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckArcToLeftHalf m)
        (coordinateUnlinkExteriorPlanarNeckArcToRightHalf m)
        (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m x) := by
  apply topologicalPushoutCongr_inr

/-- The normalized annulus pushout is the literal planar flower. -/
def coordinateUnlinkExteriorPlanarNormalizedNeckPushoutHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNormalizedNeckPushout m ≃ₜ
      CoordinateUnlinkExteriorPlanarFlower m :=
  (coordinateUnlinkExteriorPlanarNormalizedNeckPushoutCongr m).trans
    (coordinateUnlinkExteriorPlanarFlowerNeckPushoutHomeomorph m)

@[simp]
theorem coordinateUnlinkExteriorPlanarNormalizedNeckPushoutHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNormalizedLeftHalf m) :
    coordinateUnlinkExteriorPlanarNormalizedNeckPushoutHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m)
          (coordinateUnlinkExteriorPlanarNormalizedRightSeam m) x) =
      coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion m
        (coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m x) := by
  rw [coordinateUnlinkExteriorPlanarNormalizedNeckPushoutHomeomorph,
    Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarNormalizedNeckPushoutCongr_inl,
    coordinateUnlinkExteriorPlanarFlowerNeckPushoutHomeomorph_inl]
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNormalizedNeckPushoutHomeomorph_inr
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNormalizedRightHalf) :
    coordinateUnlinkExteriorPlanarNormalizedNeckPushoutHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m)
          (coordinateUnlinkExteriorPlanarNormalizedRightSeam m) x) =
      coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion m
        (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m x) := by
  rw [coordinateUnlinkExteriorPlanarNormalizedNeckPushoutHomeomorph,
    Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarNormalizedNeckPushoutCongr_inr,
    coordinateUnlinkExteriorPlanarFlowerNeckPushoutHomeomorph_inr]
  rfl

/-! ## Product with the spun `Sphere 2` factor -/

/-- The product-seam pushout obtained by crossing every normalized piece with `Sphere 2`. -/
abbrev CoordinateUnlinkExteriorPlanarNormalizedNeckSphereTwoPushout
    (m : ℕ) [NeZero m] : Type :=
  TopologicalPushout
    ((coordinateUnlinkExteriorPlanarNormalizedLeftSeam m).prodMap
      (ContinuousMap.id (Sphere 2)))
    ((coordinateUnlinkExteriorPlanarNormalizedRightSeam m).prodMap
      (ContinuousMap.id (Sphere 2)))

/-- Crossing the normalized neck pushout with `Sphere 2` gives the planar flower times
`Sphere 2`. -/
def coordinateUnlinkExteriorPlanarNormalizedNeckSphereTwoPushoutHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNormalizedNeckSphereTwoPushout m ≃ₜ
      CoordinateUnlinkExteriorPlanarFlower m × Sphere 2 := by
  let _ : T2Space (CoordinateUnlinkExteriorPlanarNormalizedNeckPushout m) :=
    (coordinateUnlinkExteriorPlanarNormalizedNeckPushoutHomeomorph m).symm.t2Space
  exact
    (topologicalPushoutProductHomeomorph
      (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m)
      (coordinateUnlinkExteriorPlanarNormalizedRightSeam m)
      (Sphere 2)
      (injective_coordinateUnlinkExteriorPlanarNormalizedLeftSeam m)
      (injective_coordinateUnlinkExteriorPlanarNormalizedRightSeam m)).trans
      ((coordinateUnlinkExteriorPlanarNormalizedNeckPushoutHomeomorph m).prodCongr
        (Homeomorph.refl (Sphere 2)))

@[simp]
theorem coordinateUnlinkExteriorPlanarNormalizedNeckSphereTwoPushoutHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNormalizedLeftHalf m)
    (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNormalizedNeckSphereTwoPushoutHomeomorph m
        (topologicalPushoutInl
          ((coordinateUnlinkExteriorPlanarNormalizedLeftSeam m).prodMap
            (ContinuousMap.id (Sphere 2)))
          ((coordinateUnlinkExteriorPlanarNormalizedRightSeam m).prodMap
            (ContinuousMap.id (Sphere 2))) (x, s)) =
      (coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion m
        (coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m x), s) := by
  rw [coordinateUnlinkExteriorPlanarNormalizedNeckSphereTwoPushoutHomeomorph,
    Homeomorph.trans_apply, topologicalPushoutProductHomeomorph_inl]
  exact Prod.ext
    (coordinateUnlinkExteriorPlanarNormalizedNeckPushoutHomeomorph_inl m x) rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNormalizedNeckSphereTwoPushoutHomeomorph_inr
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNormalizedRightHalf)
    (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNormalizedNeckSphereTwoPushoutHomeomorph m
        (topologicalPushoutInr
          ((coordinateUnlinkExteriorPlanarNormalizedLeftSeam m).prodMap
            (ContinuousMap.id (Sphere 2)))
          ((coordinateUnlinkExteriorPlanarNormalizedRightSeam m).prodMap
            (ContinuousMap.id (Sphere 2))) (x, s)) =
      (coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion m
        (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m x), s) := by
  rw [coordinateUnlinkExteriorPlanarNormalizedNeckSphereTwoPushoutHomeomorph,
    Homeomorph.trans_apply, topologicalPushoutProductHomeomorph_inr]
  exact Prod.ext
    (coordinateUnlinkExteriorPlanarNormalizedNeckPushoutHomeomorph_inr m x) rfl

end SplittingSpheres
