/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckCompactCutSide
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckFullCoverRange

/-!
# The full planar neck family over the coordinate equator

The union of the labelled equatorial lifts in the standard unlink power pullback is exactly
the inverse image of the coordinate equator.  Transporting this entire family through the
canonical strict coordinate-exterior map gives the transported planar neck family, and hence
the global seam of the strict planar neck star is the same coordinate-equator inverse image.

The global left and right off-seam sets are recorded only as point-set pullbacks from the
literal neck star.  They are disjoint and cover the complement of the global seam.  This file
does not identify those two sides with the two coordinate open caps, orient a collar, or make
any smoothness assertion about the normalized planar annuli.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

/-! ## The full equatorial carrier -/

/-- The union of all labelled equatorial lifts in the standard unlink power pullback. -/
def coordinateUnlinkExteriorPlanarFullEquatorCarrier
    (m : ℕ) [NeZero m] : Set (StandardUnlinkPowerPullback m) :=
  ⋃ a : ZMod m, range (equatorUnlinkPowerLift m a)

/-- A point lies on one of the labelled equatorial lifts exactly when its projected base lies
on the coordinate equator. -/
theorem mem_coordinateUnlinkExteriorPlanarFullEquatorCarrier_iff
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    z ∈ coordinateUnlinkExteriorPlanarFullEquatorCarrier m ↔
      (standardUnlinkPowerPullbackProj m z : Sphere 4) ∈ coordinateEquator := by
  constructor
  · intro hz
    rw [coordinateUnlinkExteriorPlanarFullEquatorCarrier] at hz
    obtain ⟨a, ha⟩ := mem_iUnion.mp hz
    obtain ⟨x, rfl⟩ := ha
    rw [equatorUnlinkPowerLift_proj]
    change equatorSphereMap x ∈ coordinateEquator
    rw [← range_equatorSphereMap]
    exact mem_range_self x
  · intro hz
    rw [coordinateUnlinkExteriorPlanarFullEquatorCarrier]
    rw [← range_equatorSphereMap] at hz
    obtain ⟨x, hx⟩ := hz
    have hbase :
        standardUnlinkPowerPullbackProj m (equatorUnlinkPowerLift m 0 x) =
          standardUnlinkPowerPullbackProj m z := by
      rw [equatorUnlinkPowerLift_proj]
      apply Subtype.ext
      exact hx
    obtain ⟨a, ha, _haUnique⟩ :=
      existsUnique_standardUnlinkPowerDeckZMod_eq m
        (equatorUnlinkPowerLift m 0 x) z hbase
    refine mem_iUnion.mpr ⟨a, ⟨x, ?_⟩⟩
    rw [← ha, standardUnlinkPowerDeckZModHom_equatorUnlinkPowerLift_add]
    simp

/-! ## The global strict star sides and seam -/

/-- The global left off-seam set in the strict full cover, pulled back from the literal neck
star. -/
def coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam
    (m : ℕ) [NeZero m] : Set (StandardUnlinkPowerPullback m) :=
  coordinateUnlinkExteriorPlanarFullCoverToNeckStar m ⁻¹'
    coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam m

/-- The global right off-seam set in the strict full cover, pulled back from the literal neck
star. -/
def coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam
    (m : ℕ) [NeZero m] : Set (StandardUnlinkPowerPullback m) :=
  coordinateUnlinkExteriorPlanarFullCoverToNeckStar m ⁻¹'
    coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m

/-- The full labelled seam in the strict full cover, pulled back from the literal neck star. -/
def coordinateUnlinkExteriorPlanarFullCoverGlobalSeam
    (m : ℕ) [NeZero m] : Set (StandardUnlinkPowerPullback m) :=
  coordinateUnlinkExteriorPlanarFullCoverToNeckStar m ⁻¹'
    coordinateUnlinkExteriorPlanarNeckStarSeam m

/-- The two global strict off-seam sets are disjoint. -/
theorem disjoint_coordinateUnlinkExteriorPlanarFullCoverGlobalOffSeam
    (m : ℕ) [NeZero m] :
    Disjoint (coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam m)
      (coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam m) :=
  (disjoint_coordinateUnlinkExteriorPlanarNeckStarOffSeam m).preimage _

/-- The two global strict off-seam sets cover exactly the complement of the full seam. -/
theorem union_coordinateUnlinkExteriorPlanarFullCoverGlobalOffSeam
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam m ∪
        coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam m =
      (coordinateUnlinkExteriorPlanarFullCoverGlobalSeam m)ᶜ := by
  rw [coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam,
    coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam,
    coordinateUnlinkExteriorPlanarFullCoverGlobalSeam, ← preimage_union,
    ← preimage_compl, union_coordinateUnlinkExteriorPlanarNeckStarOffSeam]

/-! ## Comparison of the full transported family -/

private theorem
    coordinateUnlinkExteriorEighthPowerPullbackToComplement_fullTransport_equator
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    coordinateUnlinkExteriorEighthPowerPullbackToComplement m
        (standardUnlinkPowerPullbackToCoordinateExteriorStrict m
          (equatorUnlinkPowerLift m a x)) =
      equatorUnlinkPowerLift m a x := by
  rw [standardUnlinkPowerPullbackToCoordinateExteriorStrict_equatorUnlinkPowerLift]
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    exact equatorUnlinkClosedTubeExteriorPowerLift_powerCoordinate m a x

private theorem range_coordinateUnlinkExteriorPlanarTransportedNeckSphereMap_eq_image_equator
    (m : ℕ) [NeZero m] (a : ZMod m) :
    range (fun s : Sphere 3 ↦
        coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (coordinateUnlinkExteriorPlanarNeckSphereMap m
            (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) s)) =
      standardUnlinkPowerPullbackToCoordinateExteriorStrict m ''
        range (equatorUnlinkPowerLift m a) := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    have hs : coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m
          (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) s ∈
        range (equatorUnlinkPowerLift m a) := by
      rw [← range_transportedNeckSphereMap_eq_equatorPowerLift m a]
      exact mem_range_self s
    obtain ⟨x, hx⟩ := hs
    refine ⟨equatorUnlinkPowerLift m a x, ⟨x, rfl⟩, ?_⟩
    apply coordinateUnlinkExteriorEighthPowerPullbackToComplement_injective m
    calc
      coordinateUnlinkExteriorEighthPowerPullbackToComplement m
          (standardUnlinkPowerPullbackToCoordinateExteriorStrict m
            (equatorUnlinkPowerLift m a x)) =
          equatorUnlinkPowerLift m a x :=
        coordinateUnlinkExteriorEighthPowerPullbackToComplement_fullTransport_equator m a x
      _ = coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m
          (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) s := hx
      _ = coordinateUnlinkExteriorEighthPowerPullbackToComplement m
          (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (coordinateUnlinkExteriorPlanarNeckSphereMap m
              (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) s)) := rfl
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    have hx : equatorUnlinkPowerLift m a x ∈
        range (coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m
          (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)) := by
      rw [range_transportedNeckSphereMap_eq_equatorPowerLift m a]
      exact mem_range_self x
    obtain ⟨s, hs⟩ := hx
    refine ⟨s, ?_⟩
    apply coordinateUnlinkExteriorEighthPowerPullbackToComplement_injective m
    calc
      coordinateUnlinkExteriorEighthPowerPullbackToComplement m
          (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (coordinateUnlinkExteriorPlanarNeckSphereMap m
              (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) s)) =
          coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m
            (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) s := rfl
      _ = equatorUnlinkPowerLift m a x := hs
      _ = coordinateUnlinkExteriorEighthPowerPullbackToComplement m
          (standardUnlinkPowerPullbackToCoordinateExteriorStrict m
            (equatorUnlinkPowerLift m a x)) :=
        (coordinateUnlinkExteriorEighthPowerPullbackToComplement_fullTransport_equator
          m a x).symm

/-- The entire transported neck family is exactly the image of the full equatorial carrier
under the canonical strict full-cover map. -/
theorem
    range_coordinateUnlinkExteriorPlanarTransportedNeckSphereFamily_eq_image_fullEquatorCarrier
    (m : ℕ) [NeZero m] :
    range (fun x : ZMod m × Sphere 3 ↦
        coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (coordinateUnlinkExteriorPlanarNeckSphereFamily m x)) =
      standardUnlinkPowerPullbackToCoordinateExteriorStrict m ''
        coordinateUnlinkExteriorPlanarFullEquatorCarrier m := by
  ext z
  constructor
  · rintro ⟨⟨b, s⟩, rfl⟩
    let a := b - coordinateUnlinkExteriorPlanarSmoothNeckShift m
    have hz : coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (coordinateUnlinkExteriorPlanarNeckSphereMap m b s) ∈
        range (fun x : Sphere 3 ↦
          coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (coordinateUnlinkExteriorPlanarNeckSphereMap m
              (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) x)) := by
      refine ⟨s, ?_⟩
      simp [a]
    rw [range_coordinateUnlinkExteriorPlanarTransportedNeckSphereMap_eq_image_equator
      m a] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    refine ⟨w, ?_, hwz⟩
    exact mem_iUnion.mpr ⟨a, hw⟩
  · rintro ⟨w, hw, rfl⟩
    rw [coordinateUnlinkExteriorPlanarFullEquatorCarrier] at hw
    obtain ⟨a, ha⟩ := mem_iUnion.mp hw
    have hz : standardUnlinkPowerPullbackToCoordinateExteriorStrict m w ∈
        standardUnlinkPowerPullbackToCoordinateExteriorStrict m ''
          range (equatorUnlinkPowerLift m a) := ⟨w, ha, rfl⟩
    rw [←
      range_coordinateUnlinkExteriorPlanarTransportedNeckSphereMap_eq_image_equator
        m a] at hz
    obtain ⟨s, hs⟩ := hz
    refine ⟨(a + coordinateUnlinkExteriorPlanarSmoothNeckShift m, s), ?_⟩
    simpa only [coordinateUnlinkExteriorPlanarNeckSphereFamily_apply] using hs

private theorem coordinateUnlinkExteriorPlanarFullCoverGlobalSeam_eq_fullEquatorCarrier
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarFullCoverGlobalSeam m =
      coordinateUnlinkExteriorPlanarFullEquatorCarrier m := by
  change standardUnlinkPowerPullbackToCoordinateExteriorStrict m ⁻¹'
      coordinateUnlinkExteriorPlanarCompactNeckStarSeam m = _
  rw [coordinateUnlinkExteriorPlanarCompactNeckStarSeam_eq_range_transport_family,
    range_coordinateUnlinkExteriorPlanarTransportedNeckSphereFamily_eq_image_fullEquatorCarrier]
  apply preimage_image_eq
  intro x y hxy
  apply (standardUnlinkPowerPullbackCoordinateExteriorStrictHomeomorph m).injective
  exact Subtype.ext hxy

/-- The global strict planar-neck seam is exactly the inverse image of the coordinate equator
under the standard unlink power-cover projection. -/
theorem coordinateUnlinkExteriorPlanarFullCoverGlobalSeam_eq_preimage_coordinateEquator
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarFullCoverGlobalSeam m =
      (fun z : StandardUnlinkPowerPullback m ↦
        (standardUnlinkPowerPullbackProj m z : Sphere 4)) ⁻¹'
          coordinateEquator := by
  rw [coordinateUnlinkExteriorPlanarFullCoverGlobalSeam_eq_fullEquatorCarrier]
  ext z
  exact mem_coordinateUnlinkExteriorPlanarFullEquatorCarrier_iff m z

end SplittingSpheres

end
