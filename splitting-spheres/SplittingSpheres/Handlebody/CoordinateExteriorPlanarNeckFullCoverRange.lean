/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckFullCoverSeparation

/-!
# The exact strict-core range in the planar neck star

This file upgrades the full-cover map to the planar neck star to an open embedding.  Its range is
identified with the explicit image of the strict coordinate exterior under the inverse neck
transport and the flower-to-star homeomorphism.

Restricting the embedding gives honest homeomorphisms from the two full-cover equator sides onto
their exact images: the intersections of the strict-core range with the corresponding labelled
star sides.  These intersections are not asserted to be the whole compact left leaf or remainder.
No connectedness, component count, manifold structure, or smoothness assertion is made.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open Set.Notation

namespace SplittingSpheres

/-! ## The transported strict core -/

/-- The full-cover map into the neck star is a topological embedding. -/
theorem isEmbedding_coordinateUnlinkExteriorPlanarFullCoverToNeckStar
    (m : ℕ) [NeZero m] :
    IsEmbedding (coordinateUnlinkExteriorPlanarFullCoverToNeckStar m) := by
  exact
    (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar
      m).isEmbedding.comp <|
      (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm.isEmbedding.comp <|
        IsEmbedding.subtypeVal.comp
          (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).isEmbedding

/-- The explicit neck-star subset obtained by transporting the strict open coordinate exterior. -/
def coordinateUnlinkExteriorPlanarNeckStarStrictCore
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorPlanarNeckStar m) :=
  coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m ''
    ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm ''
      coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m)

/-- The transported strict core is open in the compact neck star. -/
theorem isOpen_coordinateUnlinkExteriorPlanarNeckStarStrictCore
    (m : ℕ) [NeZero m] :
    IsOpen (coordinateUnlinkExteriorPlanarNeckStarStrictCore m) := by
  exact
    (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar
      m).isOpenMap _ <|
      (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm.isOpenMap _
        (coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m).2

/-- The range of the full-cover map is exactly the transported strict core. -/
theorem range_coordinateUnlinkExteriorPlanarFullCoverToNeckStar
    (m : ℕ) [NeZero m] :
    range (coordinateUnlinkExteriorPlanarFullCoverToNeckStar m) =
      coordinateUnlinkExteriorPlanarNeckStarStrictCore m := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm
      (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m z).1, ?_, rfl⟩
    exact ⟨(coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m z).1,
      (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m z).2, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    let zs : CoordinateUnlinkExteriorEighthPowerPullbackStrict m := ⟨z, hz⟩
    refine ⟨(coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).symm zs, ?_⟩
    change coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
        ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm
          ((coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m
            ((coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).symm zs)).1)) =
      coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
        ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm z)
    rw [(coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).apply_symm_apply]

/-- The full-cover map is, more strongly, an open embedding into the neck star. -/
theorem isOpenEmbedding_coordinateUnlinkExteriorPlanarFullCoverToNeckStar
    (m : ℕ) [NeZero m] :
    IsOpenEmbedding (coordinateUnlinkExteriorPlanarFullCoverToNeckStar m) := by
  refine ⟨isEmbedding_coordinateUnlinkExteriorPlanarFullCoverToNeckStar m, ?_⟩
  rw [range_coordinateUnlinkExteriorPlanarFullCoverToNeckStar]
  exact isOpen_coordinateUnlinkExteriorPlanarNeckStarStrictCore m

/-- The full cover is homeomorphic to the exact set-theoretic range of its neck-star map. -/
def coordinateUnlinkExteriorPlanarFullCoverNeckStarRangeHomeomorph
    (m : ℕ) [NeZero m] :
    StandardUnlinkPowerPullback m ≃ₜ
      ↑(range (coordinateUnlinkExteriorPlanarFullCoverToNeckStar m)) :=
  (isEmbedding_coordinateUnlinkExteriorPlanarFullCoverToNeckStar m).toHomeomorph

/-- The range homeomorphism has the original neck-star map as its underlying function. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarFullCoverNeckStarRangeHomeomorph_apply_coe
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    (coordinateUnlinkExteriorPlanarFullCoverNeckStarRangeHomeomorph m z).1 =
      coordinateUnlinkExteriorPlanarFullCoverToNeckStar m z :=
  rfl

/-- The inverse of the range homeomorphism sends its canonical range point back to its source. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarFullCoverNeckStarRangeHomeomorph_symm_apply_mk
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    (coordinateUnlinkExteriorPlanarFullCoverNeckStarRangeHomeomorph m).symm
        ⟨coordinateUnlinkExteriorPlanarFullCoverToNeckStar m z, ⟨z, rfl⟩⟩ = z :=
  (isEmbedding_coordinateUnlinkExteriorPlanarFullCoverToNeckStar m).toHomeomorph_symm_apply z

/-- The same homeomorphism with the exact range rewritten as the transported strict core. -/
def coordinateUnlinkExteriorPlanarFullCoverNeckStarStrictCoreHomeomorph
    (m : ℕ) [NeZero m] :
    StandardUnlinkPowerPullback m ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarNeckStarStrictCore m) :=
  (coordinateUnlinkExteriorPlanarFullCoverNeckStarRangeHomeomorph m).trans
    (Homeomorph.setCongr
      (range_coordinateUnlinkExteriorPlanarFullCoverToNeckStar m))

/-- The strict-core homeomorphism also has the neck-star map as its underlying function. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarFullCoverNeckStarStrictCoreHomeomorph_apply_coe
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    (coordinateUnlinkExteriorPlanarFullCoverNeckStarStrictCoreHomeomorph m z).1 =
      coordinateUnlinkExteriorPlanarFullCoverToNeckStar m z :=
  rfl

/-! ## Exact restrictions to subsets of the range -/

/-- Restrict the full-cover embedding to the preimage of any neck-star set. -/
def coordinateUnlinkExteriorPlanarFullCoverPreimageHomeomorphRangeInter
    (m : ℕ) [NeZero m]
    (L : Set (CoordinateUnlinkExteriorPlanarNeckStar m)) :
    ↑(coordinateUnlinkExteriorPlanarFullCoverToNeckStar m ⁻¹' L) ≃ₜ
      ↑(range (coordinateUnlinkExteriorPlanarFullCoverToNeckStar m) ∩ L) :=
  (isEmbedding_coordinateUnlinkExteriorPlanarFullCoverToNeckStar m).homeomorphImage
      (coordinateUnlinkExteriorPlanarFullCoverToNeckStar m ⁻¹' L) |>.trans
    (Homeomorph.setCongr image_preimage_eq_range_inter)

/-- The general restricted homeomorphism is induced by the original neck-star map. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarFullCoverPreimageHomeomorphRangeInter_apply_coe
    (m : ℕ) [NeZero m]
    (L : Set (CoordinateUnlinkExteriorPlanarNeckStar m))
    (z : ↑(coordinateUnlinkExteriorPlanarFullCoverToNeckStar m ⁻¹' L)) :
    (coordinateUnlinkExteriorPlanarFullCoverPreimageHomeomorphRangeInter m L z).1 =
      coordinateUnlinkExteriorPlanarFullCoverToNeckStar m z.1 :=
  rfl

/-! ## The two labelled side images -/

/-- The exact image of the selected full-cover left side inside the neck star. -/
def coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorLeftSideImage
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Set (CoordinateUnlinkExteriorPlanarNeckStar m) :=
  range (coordinateUnlinkExteriorPlanarFullCoverToNeckStar m) ∩
    coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)

/-- The exact image of the selected full-cover remainder side inside the neck star. -/
def coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorRestSideImage
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Set (CoordinateUnlinkExteriorPlanarNeckStar m) :=
  range (coordinateUnlinkExteriorPlanarFullCoverToNeckStar m) ∩
    coordinateUnlinkExteriorPlanarNeckStarFiberRest m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)

/-- The selected left image is the strict core intersected with the matching labelled leaf. -/
theorem coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorLeftSideImage_eq_strictCore_inter
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorLeftSideImage m a =
      coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m
          (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) := by
  rw [coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorLeftSideImage,
    range_coordinateUnlinkExteriorPlanarFullCoverToNeckStar]

/-- The selected remainder image is the strict core intersected with the matching star rest. -/
theorem coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorRestSideImage_eq_strictCore_inter
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorRestSideImage m a =
      coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m
          (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m) := by
  rw [coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorRestSideImage,
    range_coordinateUnlinkExteriorPlanarFullCoverToNeckStar]

/-- The exact neck-star image of the full-cover left side. -/
theorem image_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFullCoverToNeckStar m ''
        coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a =
      coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorLeftSideImage m a := by
  exact image_preimage_eq_range_inter

/-- The exact neck-star image of the full-cover remainder side. -/
theorem image_coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFullCoverToNeckStar m ''
        coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a =
      coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorRestSideImage m a := by
  exact image_preimage_eq_range_inter

/-- The selected full-cover left side is homeomorphic to its exact strict-core leaf image. -/
def coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSideHomeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) :
    ↑(coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a) ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorLeftSideImage m a) :=
  coordinateUnlinkExteriorPlanarFullCoverPreimageHomeomorphRangeInter m
    (coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m))

/-- The selected full-cover rest side is homeomorphic to its exact strict-core rest image. -/
def coordinateUnlinkExteriorPlanarFullCoverEquatorRestSideHomeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) :
    ↑(coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a) ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorRestSideImage m a) :=
  coordinateUnlinkExteriorPlanarFullCoverPreimageHomeomorphRangeInter m
    (coordinateUnlinkExteriorPlanarNeckStarFiberRest m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m))

/-- The left-side homeomorphism is induced by the original neck-star map. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSideHomeomorph_apply_coe
    (m : ℕ) [NeZero m] (a : ZMod m)
    (z : ↑(coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a)) :
    (coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSideHomeomorph m a z).1 =
      coordinateUnlinkExteriorPlanarFullCoverToNeckStar m z.1 :=
  rfl

/-- The rest-side homeomorphism is induced by the original neck-star map. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarFullCoverEquatorRestSideHomeomorph_apply_coe
    (m : ℕ) [NeZero m] (a : ZMod m)
    (z : ↑(coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a)) :
    (coordinateUnlinkExteriorPlanarFullCoverEquatorRestSideHomeomorph m a z).1 =
      coordinateUnlinkExteriorPlanarFullCoverToNeckStar m z.1 :=
  rfl

/-- The restricted left-side map has precisely the named strict-core leaf image. -/
theorem range_coordinateUnlinkExteriorPlanarFullCoverToNeckStar_restrict_leftSide
    (m : ℕ) [NeZero m] (a : ZMod m) :
    range (fun z : ↑(coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a) ↦
        coordinateUnlinkExteriorPlanarFullCoverToNeckStar m z.1) =
      coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorLeftSideImage m a := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨⟨z.1, rfl⟩, z.2⟩
  · rintro ⟨⟨z, hz⟩, hside⟩
    refine ⟨⟨z, ?_⟩, hz⟩
    change coordinateUnlinkExteriorPlanarFullCoverToNeckStar m z ∈
      coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m
        (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)
    rw [hz]
    exact hside

/-- The restricted rest-side map has precisely the named strict-core rest image. -/
theorem range_coordinateUnlinkExteriorPlanarFullCoverToNeckStar_restrict_restSide
    (m : ℕ) [NeZero m] (a : ZMod m) :
    range (fun z : ↑(coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a) ↦
        coordinateUnlinkExteriorPlanarFullCoverToNeckStar m z.1) =
      coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorRestSideImage m a := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨⟨z.1, rfl⟩, z.2⟩
  · rintro ⟨⟨z, hz⟩, hside⟩
    refine ⟨⟨z, ?_⟩, hz⟩
    change coordinateUnlinkExteriorPlanarFullCoverToNeckStar m z ∈
      coordinateUnlinkExteriorPlanarNeckStarFiberRest m
        (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)
    rw [hz]
    exact hside

/-- The selected left-side image is open in the neck star. -/
theorem isOpen_coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorLeftSideImage
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsOpen (coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorLeftSideImage m a) := by
  rw [
    coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorLeftSideImage_eq_strictCore_inter]
  exact (isOpen_coordinateUnlinkExteriorPlanarNeckStarStrictCore m).inter
    (isOpen_coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m))

/-- The selected remainder-side image is open in the neck star. -/
theorem isOpen_coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorRestSideImage
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsOpen (coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorRestSideImage m a) := by
  rw [
    coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorRestSideImage_eq_strictCore_inter]
  exact (isOpen_coordinateUnlinkExteriorPlanarNeckStarStrictCore m).inter
    (isOpen_coordinateUnlinkExteriorPlanarNeckStarFiberRest m
      (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m))

/-! ## Deck covariance of the explicit equators -/

/-- Applying deck label `b` to the equator labelled `a` produces the equator labelled `b + a`. -/
theorem standardUnlinkPowerDeckZModHom_equatorUnlinkPowerLift_add
    (m : ℕ) [NeZero m] (b a : ZMod m) (x : Sphere 3) :
    standardUnlinkPowerDeckZModHom m (Multiplicative.ofAdd b)
        (equatorUnlinkPowerLift m a x) =
      equatorUnlinkPowerLift m (b + a) x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change
      (((standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd b)).1 : ℂˣ) : ℂ) *
          ((((standardRootsOfUnityZModMulEquiv m
            (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) *
            equatorUnlinkPowerRoot m x) =
        (((standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd (b + a))).1 : ℂˣ) : ℂ) *
          equatorUnlinkPowerRoot m x
    rw [← mul_assoc]
    congr 1
    simpa using congrArg (fun u : rootsOfUnity m ℂ ↦ ((u.1 : ℂˣ) : ℂ))
      ((standardRootsOfUnityZModMulEquiv m).map_mul
        (Multiplicative.ofAdd b) (Multiplicative.ofAdd a)).symm

/-- The deck action carries the entire equator range at `a` onto the range at `b + a`. -/
theorem image_standardUnlinkPowerDeckZModHom_range_equatorUnlinkPowerLift
    (m : ℕ) [NeZero m] (b a : ZMod m) :
    standardUnlinkPowerDeckZModHom m (Multiplicative.ofAdd b) ''
        range (equatorUnlinkPowerLift m a) =
      range (equatorUnlinkPowerLift m (b + a)) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (standardUnlinkPowerDeckZModHom_equatorUnlinkPowerLift_add
      m b a x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨equatorUnlinkPowerLift m a x, ⟨x, rfl⟩,
      standardUnlinkPowerDeckZModHom_equatorUnlinkPowerLift_add m b a x⟩

/-- The same deck action carries the complement of equator `a` onto that of equator `b + a`. -/
theorem image_standardUnlinkPowerDeckZModHom_equatorComplement
    (m : ℕ) [NeZero m] (b a : ZMod m) :
    standardUnlinkPowerDeckZModHom m (Multiplicative.ofAdd b) ''
        (range (equatorUnlinkPowerLift m a))ᶜ =
      (range (equatorUnlinkPowerLift m (b + a)))ᶜ := by
  rw [(standardUnlinkPowerDeckZModHom m
      (Multiplicative.ofAdd b)).image_compl,
    image_standardUnlinkPowerDeckZModHom_range_equatorUnlinkPowerLift]

end SplittingSpheres

end
