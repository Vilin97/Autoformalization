/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckStrictCorePieces

/-!
# Interior annulus access in the strict planar neck core

This file locates the normalized open annuli in the two exact strict-core sides.  A normalized
left point with label `a` and time strictly below `1` lies off the attaching seam in the
`a`-labelled leaf.  A normalized right point with time strictly below `1` lies in the remainder
of every selected labelled leaf.  Combining these facts with the exact strict-core criterion
shows that time in `(0, 1)` gives honest carriers in the corresponding strict sides.

The two carriers are continuous images of `S¹ × (0, 1) × S²`, hence path connected, and any
two of their points are joined inside the relevant strict side.  No assertion is made that a
carrier exhausts its side.  In particular, this file does not assert connectivity of a
one-handle with any cap carrier removed, connectivity of either complete side, or an exact
component count.
-/

@[expose] public section

noncomputable section

open Function Set Topology
open Set.Notation

namespace SplittingSpheres

/-! ## Normalized annular points in the star -/

/-- A normalized labelled left-annulus point transported to the literal neck star. -/
def coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) :
    CoordinateUnlinkExteriorPlanarNeckStar m :=
  coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
    (partialSphereSpinInr
      (coordinateUnlinkExteriorPlanarFlowerOuter m)
      (coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint m a u t, s))

/-- A normalized right-annulus point transported to the literal neck star. -/
def coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint
    (m : ℕ) [NeZero m] (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) :
    CoordinateUnlinkExteriorPlanarNeckStar m :=
  coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
    (partialSphereSpinInr
      (coordinateUnlinkExteriorPlanarFlowerOuter m)
      (coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint m u t, s))

/-- Exact location of a normalized left point in the bottom-left grid chart of the star. -/
theorem coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_eq_grid
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m a u t s =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)
        (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
          (topologicalPushoutInr
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
            ((a, (u, t)), s))) := by
  rw [coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint,
    coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint,
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar,
    Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarNeckGridRegrouping_bottomLeft_apply]
  exact coordinateUnlinkExteriorPlanarNeckGridColumnFirstHomeomorphStar_inl m _

/-- Exact location of a normalized right point in the bottom-right grid chart of the star. -/
theorem coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint_eq_grid
    (m : ℕ) [NeZero m] (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint m u t s =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)
        (coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m
          (topologicalPushoutInr
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight
            ((u, t), s))) := by
  rw [coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint,
    coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint,
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar,
    Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarNeckGridRegrouping_bottomRight_apply]
  exact coordinateUnlinkExteriorPlanarNeckGridColumnFirstHomeomorphStar_inr m _

/-! ## Avoiding the attaching range below time one -/

private theorem injective_coordinateUnlinkExteriorPlanarNeckGrid_leftToTopLeft
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft := by
  intro x y hxy
  apply Prod.ext
  · exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridHL m => z.1) hxy
  · apply Subtype.ext
    exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridHL m => z.2.1) hxy

/-- A bottom-left grid point at time below `1` is not in the vertical attaching range. -/
theorem coordinateUnlinkExteriorPlanarNeckGrid_bottomLeft_not_mem_verticalCenterRange
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) (ht : (t : ℝ) < 1) :
    topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
        ((a, (u, t)), s) ∉
      range (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  rintro ⟨q, hq⟩
  rcases topologicalPushout_jointly_surjective D.centerToTop D.centerToBottom q with
    ⟨e, rfl⟩ | ⟨x, rfl⟩
  · rw [TopologicalPushoutGridDiagram.verticalCenterToLeft_inl] at hq
    obtain ⟨b, _hbTop, hbBottom⟩ :=
      (topologicalPushoutInl_eq_inr_iff D.leftToTopLeft D.leftToBottomLeft
        (injective_coordinateUnlinkExteriorPlanarNeckGrid_leftToTopLeft m)
        (D.topToTopLeft e) ((a, (u, t)), s)).mp hq
    have htime := congrArg
      (fun z : CoordinateUnlinkExteriorPlanarNeckGridFL m => z.1.2.2) hbBottom
    rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_leftToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridLeftToBottomLeft_apply] at htime
    change (1 : Set.Icc (0 : ℝ) 1) = t at htime
    exact (ne_of_gt ht) (congrArg Subtype.val htime)
  · rw [TopologicalPushoutGridDiagram.verticalCenterToLeft_inr] at hq
    have hbottom := topologicalPushoutInr_injective
      D.leftToTopLeft D.leftToBottomLeft
      (injective_coordinateUnlinkExteriorPlanarNeckGrid_leftToTopLeft m) hq
    have htime := congrArg
      (fun z : CoordinateUnlinkExteriorPlanarNeckGridFL m => z.1.2.2) hbottom
    rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_bottomToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridBottomToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNormalizedLeftSeam_time] at htime
    exact (ne_of_gt ht) (congrArg Subtype.val htime)

/-- The complement coordinate of a bottom-left grid point retains its literal label. -/
theorem coordinateUnlinkExteriorPlanarNeckGrid_bottomLeft_complement_label
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckStarLeftLabel m
        (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
          (topologicalPushoutInr
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
            ((a, (u, t)), s))) = a := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  let x : CoordinateUnlinkExteriorPlanarNeckGridFL m := ((a, (u, t)), s)
  have hsymm :
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal m).symm
          (topologicalPushoutInr D.leftToTopLeft D.leftToBottomLeft x) =
        topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
            m).leftToTopLeft
          (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
            m).leftToBottomLeft
          x := by
    apply
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal
        m).injective
    rw [(coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal
      m).apply_symm_apply]
    exact (simLeftVerticalLeftOriginal_inr m x).symm
  rw [coordinateUnlinkExteriorPlanarNeckStarLeftLabel_apply,
    coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement,
    Homeomorph.trans_apply, hsymm,
    coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphComplementOneHandles_apply_coe]
  change
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle m
      ((coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
        m).columnFirstBottomLeft x)).1 = a
  rw [coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle_bottomLeft]

/-- Below time `1`, a bottom-left point avoids the left star attaching map. -/
theorem coordinateUnlinkExteriorPlanarNeckGrid_bottomLeft_complement_not_mem_range
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) (ht : (t : ℝ) < 1) :
    coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
          ((a, (u, t)), s)) ∉
      range (coordinateUnlinkExteriorPlanarNeckStarToLeft m) := by
  rintro ⟨x, hx⟩
  apply
    coordinateUnlinkExteriorPlanarNeckGrid_bottomLeft_not_mem_verticalCenterRange
      m a u t s ht
  refine
    ⟨(coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm x,
      ?_⟩
  apply
    (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement
      m).injective
  exact hx

/-- Every normalized left point below time `1` lies in its labelled off-seam star leaf. -/
theorem coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_mem_leaf
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) (ht : (t : ℝ) < 1) :
    coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m a u t s ∈
      coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a := by
  rw [coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_eq_grid]
  refine ⟨_, ⟨?_, ?_⟩, rfl⟩
  · exact coordinateUnlinkExteriorPlanarNeckGrid_bottomLeft_complement_label
      m a u t s
  · exact
      coordinateUnlinkExteriorPlanarNeckGrid_bottomLeft_complement_not_mem_range
        m a u t s ht

private theorem injective_coordinateUnlinkExteriorPlanarNeckGrid_rightToTopRight
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight := by
  intro x y hxy
  apply Prod.ext
  · exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridHR m => z.1) hxy
  · apply Subtype.ext
    exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridHR m => z.2.1) hxy

/-- A bottom-right grid point at time below `1` is not in the vertical attaching range. -/
theorem coordinateUnlinkExteriorPlanarNeckGrid_bottomRight_not_mem_verticalCenterRange
    (m : ℕ) [NeZero m] (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) (ht : (t : ℝ) < 1) :
    topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight
        ((u, t), s) ∉
      range (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  rintro ⟨q, hq⟩
  rcases topologicalPushout_jointly_surjective D.centerToTop D.centerToBottom q with
    ⟨e, rfl⟩ | ⟨x, rfl⟩
  · rw [TopologicalPushoutGridDiagram.verticalCenterToRight_inl] at hq
    obtain ⟨b, _hbTop, hbBottom⟩ :=
      (topologicalPushoutInl_eq_inr_iff D.rightToTopRight D.rightToBottomRight
        (injective_coordinateUnlinkExteriorPlanarNeckGrid_rightToTopRight m)
        (D.topToTopRight e) ((u, t), s)).mp hq
    have htime := congrArg
      (fun z : CoordinateUnlinkExteriorPlanarNeckGridFR => z.1.2) hbBottom
    rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_rightToBottomRight_apply,
      coordinateUnlinkExteriorPlanarNeckGridRightToBottomRight_apply] at htime
    change (1 : Set.Icc (0 : ℝ) 1) = t at htime
    exact (ne_of_gt ht) (congrArg Subtype.val htime)
  · rw [TopologicalPushoutGridDiagram.verticalCenterToRight_inr] at hq
    have hbottom := topologicalPushoutInr_injective
      D.rightToTopRight D.rightToBottomRight
      (injective_coordinateUnlinkExteriorPlanarNeckGrid_rightToTopRight m) hq
    have htime := congrArg
      (fun z : CoordinateUnlinkExteriorPlanarNeckGridFR => z.1.2) hbottom
    rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_bottomToBottomRight_apply,
      coordinateUnlinkExteriorPlanarNeckGridBottomToBottomRight_apply,
      coordinateUnlinkExteriorPlanarNormalizedRightSeam_time] at htime
    exact (ne_of_gt ht) (congrArg Subtype.val htime)

/-- Below time `1`, a bottom-right point avoids the right star attaching map. -/
theorem coordinateUnlinkExteriorPlanarNeckGrid_bottomRight_complement_not_mem_range
    (m : ℕ) [NeZero m] (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) (ht : (t : ℝ) < 1) :
    coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight
          ((u, t), s)) ∉
      range (coordinateUnlinkExteriorPlanarNeckStarToRight m) := by
  rintro ⟨x, hx⟩
  apply
    coordinateUnlinkExteriorPlanarNeckGrid_bottomRight_not_mem_verticalCenterRange
      m u t s ht
  refine
    ⟨(coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm x,
      ?_⟩
  apply
    (coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement
      m).injective
  exact hx

/-- Every normalized right point below time `1` belongs to the remainder of any selected
labelled star leaf. -/
theorem coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint_mem_rest
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) (ht : (t : ℝ) < 1) :
    coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint m u t s ∈
      coordinateUnlinkExteriorPlanarNeckStarFiberRest m a := by
  let f := coordinateUnlinkExteriorPlanarNeckStarToLeft m
  let g := coordinateUnlinkExteriorPlanarNeckStarToRight m
  let y :=
    coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m
      (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight
        ((u, t), s))
  have hy : y ∉ range g :=
    coordinateUnlinkExteriorPlanarNeckGrid_bottomRight_complement_not_mem_range
      m u t s ht
  rw [coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint_eq_grid]
  change topologicalPushoutInr f g y ∈
    (topologicalPushoutFiberSeam f g a)ᶜ \
      topologicalPushoutInlFiberOffSeam f g
        (coordinateUnlinkExteriorPlanarNeckStarLeftLabel m) a
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨z, _hzf, hzg⟩ :=
      (topologicalPushoutInl_eq_inr_iff f g
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft
          m).injective
        (f (a, q)) y).mp hq
    exact hy ⟨z, hzg⟩
  · rintro ⟨x, _hx, hxy⟩
    obtain ⟨z, _hzf, hzg⟩ :=
      (topologicalPushoutInl_eq_inr_iff f g
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft
          m).injective
        x y).mp hxy
    exact hy ⟨z, hzg⟩

/-! ## Exact strict-side membership in the open annuli -/

/-- Below the attaching time, exact membership in the strict left side is positive time. -/
theorem coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_mem_strictSide_iff
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) (ht : (t : ℝ) < 1) :
    coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m a u t s ∈
        coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
          coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a ↔
      0 < (t : ℝ) := by
  constructor
  · intro h
    exact
      (coordinateUnlinkExteriorPlanarNeckStar_normalizedLeft_mem_strictCore_iff
        m a u t s).mp h.1
  · intro h
    exact
      ⟨(coordinateUnlinkExteriorPlanarNeckStar_normalizedLeft_mem_strictCore_iff
          m a u t s).mpr h,
        coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_mem_leaf
          m a u t s ht⟩

/-- Below the attaching time, exact membership in the strict remainder is positive time. -/
theorem coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint_mem_strictRest_iff
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) (ht : (t : ℝ) < 1) :
    coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint m u t s ∈
        coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
          coordinateUnlinkExteriorPlanarNeckStarFiberRest m a ↔
      0 < (t : ℝ) := by
  constructor
  · intro h
    exact
      (coordinateUnlinkExteriorPlanarNeckStar_normalizedRight_mem_strictCore_iff
        m u t s).mp h.1
  · intro h
    exact
      ⟨(coordinateUnlinkExteriorPlanarNeckStar_normalizedRight_mem_strictCore_iff
          m u t s).mpr h,
        coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint_mem_rest
          m a u t s ht⟩

/-! ## Path-connected open-annulus carriers -/

/-- Include an open unit-interval time in the closed normalized annulus time. -/
def coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed
    (t : Set.Ioo (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨t.1, t.2.1.le, t.2.2.le⟩

theorem continuous_coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed :
    Continuous coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed := by
  exact continuous_subtype_val.subtype_mk _

/-- The complete normalized open left annulus, spun by `S²`, inside the neck star. -/
def coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier
    (m : ℕ) [NeZero m] (a : ZMod m) :
    C(Sphere 1 × (Set.Ioo (0 : ℝ) 1 × Sphere 2),
      CoordinateUnlinkExteriorPlanarNeckStar m) where
  toFun x :=
    coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m a x.1
      (coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed x.2.1) x.2.2
  continuous_toFun := by
    have ht : Continuous
        (fun x : Sphere 1 × (Set.Ioo (0 : ℝ) 1 × Sphere 2) =>
          coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed x.2.1) :=
      continuous_coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed.comp
        (continuous_fst.comp continuous_snd)
    have hx : Continuous
        (fun x : Sphere 1 × (Set.Ioo (0 : ℝ) 1 × Sphere 2) =>
          ((a, (x.1,
            coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed x.2.1)),
              x.2.2)) :=
      (continuous_const.prodMk (continuous_fst.prodMk ht)).prodMk
        (continuous_snd.comp continuous_snd)
    have hp :=
      (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
        (coordinateUnlinkExteriorPlanarNeckGridDiagram
          m).leftToBottomLeft).continuous.comp hx
    have hh :=
      (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement
        m).continuous.comp hp
    have hs :=
      (topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)).continuous.comp hh
    exact hs.congr fun x =>
      (coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_eq_grid
        m a x.1 (coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed x.2.1)
          x.2.2).symm

/-- The complete normalized open right annulus, spun by `S²`, inside the neck star. -/
def coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier
    (m : ℕ) [NeZero m] :
    C(Sphere 1 × (Set.Ioo (0 : ℝ) 1 × Sphere 2),
      CoordinateUnlinkExteriorPlanarNeckStar m) where
  toFun x :=
    coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint m x.1
      (coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed x.2.1) x.2.2
  continuous_toFun := by
    have ht : Continuous
        (fun x : Sphere 1 × (Set.Ioo (0 : ℝ) 1 × Sphere 2) =>
          coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed x.2.1) :=
      continuous_coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed.comp
        (continuous_fst.comp continuous_snd)
    have hx : Continuous
        (fun x : Sphere 1 × (Set.Ioo (0 : ℝ) 1 × Sphere 2) =>
          ((x.1, coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed x.2.1),
            x.2.2)) :=
      (continuous_fst.prodMk ht).prodMk
        (continuous_snd.comp continuous_snd)
    have hp :=
      (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
        (coordinateUnlinkExteriorPlanarNeckGridDiagram
          m).rightToBottomRight).continuous.comp hx
    have hh :=
      (coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement
        m).continuous.comp hp
    have hs :=
      (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)).continuous.comp hh
    exact hs.congr fun x =>
      (coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint_eq_grid
        m x.1 (coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed x.2.1)
          x.2.2).symm

/-- The open left-annulus carrier lies in the exact strict selected leaf side. -/
theorem range_coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier_subset
    (m : ℕ) [NeZero m] (a : ZMod m) :
    range (coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier m a) ⊆
      coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a := by
  rintro _ ⟨x, rfl⟩
  exact
    (coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_mem_strictSide_iff
      m a x.1 (coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed x.2.1)
        x.2.2 x.2.1.2.2).mpr x.2.1.2.1

/-- The open right-annulus carrier lies in the exact strict remainder of every selected
labelled leaf. -/
theorem range_coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier_subset
    (m : ℕ) [NeZero m] (a : ZMod m) :
    range (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m) ⊆
      coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a := by
  rintro _ ⟨x, rfl⟩
  exact
    (coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint_mem_strictRest_iff
      m a x.1 (coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed x.2.1)
        x.2.2 x.2.1.2.2).mpr x.2.1.2.1

/-- The normalized open left-annulus carrier is path connected. -/
theorem isPathConnected_range_coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsPathConnected
      (range (coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier m a)) := by
  let _ : PathConnectedSpace (Sphere 1) :=
    pathConnectedSpace_iff_univ.mpr isPathConnected_sphereOne
  let _ : PathConnectedSpace (Set.Ioo (0 : ℝ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp <|
      (convex_Ioo (0 : ℝ) 1).isPathConnected ⟨1 / 2, by norm_num⟩
  let _ : PathConnectedSpace (Sphere 2) :=
    pathConnectedSpace_iff_univ.mpr isPathConnected_sphereTwo
  exact isPathConnected_range
    (coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier m a).continuous

/-- The normalized open right-annulus carrier is path connected. -/
theorem isPathConnected_range_coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier
    (m : ℕ) [NeZero m] :
    IsPathConnected
      (range (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m)) := by
  let _ : PathConnectedSpace (Sphere 1) :=
    pathConnectedSpace_iff_univ.mpr isPathConnected_sphereOne
  let _ : PathConnectedSpace (Set.Ioo (0 : ℝ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp <|
      (convex_Ioo (0 : ℝ) 1).isPathConnected ⟨1 / 2, by norm_num⟩
  let _ : PathConnectedSpace (Sphere 2) :=
    pathConnectedSpace_iff_univ.mpr isPathConnected_sphereTwo
  exact isPathConnected_range
    (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m).continuous

/-- Any two normalized open left-annulus points are joined inside the exact strict leaf side. -/
theorem coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier_joinedIn
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x y : Sphere 1 × (Set.Ioo (0 : ℝ) 1 × Sphere 2)) :
    JoinedIn
      (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a)
      (coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier m a x)
      (coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier m a y) := by
  exact
    (isPathConnected_range_coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier
      m a).joinedIn _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ |>.mono
        (range_coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier_subset
          m a)

/-- Any two normalized open right-annulus points are joined inside the exact strict remainder. -/
theorem coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier_joinedIn
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x y : Sphere 1 × (Set.Ioo (0 : ℝ) 1 × Sphere 2)) :
    JoinedIn
      (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a)
      (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m x)
      (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m y) := by
  exact
    (isPathConnected_range_coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier
      m).joinedIn _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ |>.mono
        (range_coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier_subset
          m a)

end SplittingSpheres
