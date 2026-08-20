/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckStrictCoreInteriorAccess

/-!
# Paths from the strict central right node to its open annulus

This file treats only points represented by the right coprojection of the literal neck star.
It joins every such point in the exact strict remainder of a selected seam to the normalized
open right-annulus carrier.  The proof works in the right column of the neck grid: annular
points move to time `1 / 2`, while one-handle points first move through the three-ball to its
sphere boundary and then cross the pushout into the annulus.

At a retained-sector endpoint, the whole three-ball belongs to one attaching sphere.  The
selected-seam avoidance hypothesis is therefore transported along the ball coordinate; the
upper-endpoint label twist remains the one built into the grid.  No statement about other left
leaves, connectivity of the complete remainder, or an exact component count is made.
-/

@[expose] public section

noncomputable section

open Function Set Topology
open Set.Notation
open scoped unitInterval

namespace SplittingSpheres

/-! ## Right-column points and their two coprojections -/

/-- Send a point of the right grid column through the right coprojection of the neck star. -/
def coordinateUnlinkExteriorPlanarNeckStarRightGridPoint
    (m : ℕ) [NeZero m]
    (q : (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalRight) :
    CoordinateUnlinkExteriorPlanarNeckStar m :=
  topologicalPushoutInr
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m q)

/-- A point in the one-handle (`HR`) coprojection of the right grid column. -/
def coordinateUnlinkExteriorPlanarNeckStarRightTopPoint
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridRightOuter m)
    (b : EuclideanClosedBall 3) : CoordinateUnlinkExteriorPlanarNeckStar m :=
  coordinateUnlinkExteriorPlanarNeckStarRightGridPoint m <|
    topologicalPushoutInl
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight
      (x, b)

/-- A point in the normalized right-annulus (`FR`) coprojection of the right grid column. -/
def coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint
    (m : ℕ) [NeZero m] (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) :
    CoordinateUnlinkExteriorPlanarNeckStar m :=
  coordinateUnlinkExteriorPlanarNeckStarRightGridPoint m <|
    topologicalPushoutInr
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight
      ((u, t), s)

/-- The bottom right-column point is the normalized right-annulus point from the strict-core
interior carrier. -/
theorem coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint_eq_normalized
    (m : ℕ) [NeZero m] (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint m u t s =
      coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint m u t s := by
  exact
    (coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint_eq_grid
      m u t s).symm

/-- Every one-handle point of the right grid column lies in the exact strict core. -/
theorem coordinateUnlinkExteriorPlanarNeckStarRightTopPoint_mem_strictCore
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridRightOuter m)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarNeckStarRightTopPoint m x b ∈
      coordinateUnlinkExteriorPlanarNeckStarStrictCore m := by
  let p : OneHandlePiece :=
    (coordinateUnlinkExteriorPlanarRightOuterSectorParameter m x.1 x.2, b)
  have hp := coordinateUnlinkExteriorPlanarNeckStar_oneHandle_mem_strictCore m p
  rw [coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar,
    Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarNeckGridRegrouping_topRight_apply] at hp
  unfold TopologicalPushoutGridDiagram.columnFirstTopRight at hp
  rw [ContinuousMap.comp_apply,
    coordinateUnlinkExteriorPlanarNeckGridColumnFirstHomeomorphStar_inr] at hp
  exact hp

/-- Positive annulus time is exactly what is needed for a bottom right-column point to belong
to the strict core. -/
theorem coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint_mem_strictCore_iff
    (m : ℕ) [NeZero m] (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint m u t s ∈
        coordinateUnlinkExteriorPlanarNeckStarStrictCore m ↔
      0 < (t : ℝ) := by
  rw [coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint_eq_normalized]
  exact coordinateUnlinkExteriorPlanarNeckStar_normalizedRight_mem_strictCore_iff
    m u t s

/-! ## Selected-seam avoidance in right coordinates -/

/-- A point represented by the right star coprojection belongs to the selected remainder
exactly when its right-coordinate representative avoids the selected attaching sphere. -/
theorem coordinateUnlinkExteriorPlanarNeckStar_inr_mem_fiberRest_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (y : CoordinateUnlinkExteriorPlanarNeckRightComplement m) :
    topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m) y ∈
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a ↔
      y ∉ range (fun s : Sphere 3 =>
        coordinateUnlinkExteriorPlanarNeckStarToRight m (a, s)) := by
  let f := coordinateUnlinkExteriorPlanarNeckStarToLeft m
  let g := coordinateUnlinkExteriorPlanarNeckStarToRight m
  let label := coordinateUnlinkExteriorPlanarNeckStarLeftLabel m
  change topologicalPushoutInr f g y ∈
      topologicalPushoutFiberRest f g label a ↔
    y ∉ range (fun s : Sphere 3 => g (a, s))
  constructor
  · rintro ⟨hseam, _hoff⟩ ⟨s, hs⟩
    apply hseam
    refine ⟨s, ?_⟩
    rw [← hs]
    exact topologicalPushout_condition f g (a, s)
  · intro hy
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨z, hzf, hzg⟩ :=
        (topologicalPushoutInl_eq_inr_iff f g
          (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft
            m).injective
          (f (a, s)) y).mp hs
      have hz : z = (a, s) :=
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft
          m).injective hzf
      subst z
      exact hy ⟨s, hzg⟩
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨z, hzf, _hzg⟩ :=
        (topologicalPushoutInl_eq_inr_iff f g
          (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft
            m).injective x y).mp hxy
      exact hx.2 ⟨z, hzf⟩

/-- The right-grid formulation of selected-seam avoidance. -/
theorem coordinateUnlinkExteriorPlanarNeckStarRightGridPoint_mem_fiberRest_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (q : (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalRight) :
    coordinateUnlinkExteriorPlanarNeckStarRightGridPoint m q ∈
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a ↔
      coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m q ∉
        range (fun s : Sphere 3 =>
          coordinateUnlinkExteriorPlanarNeckStarToRight m (a, s)) :=
  coordinateUnlinkExteriorPlanarNeckStar_inr_mem_fiberRest_iff m a _

private theorem injective_coordinateUnlinkExteriorPlanarNeckGridRightToTopRight_paths
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight := by
  intro x y hxy
  apply Prod.ext
  · exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridHR m => z.1) hxy
  · apply Subtype.ext
    exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridHR m => z.2.1) hxy

private theorem injective_coordinateUnlinkExteriorPlanarNeckGridRightToBottomRight_paths
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight := by
  intro x y hxy
  apply Prod.ext
  · apply injective_coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m
    exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridFR => z.1.1) hxy
  · exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridFR => z.2) hxy

/-- Membership of an `HR` point in a selected attaching sphere depends only on the retained
sector endpoint and its incident (possibly shifted) seam label, not on the three-ball
coordinate. -/
theorem coordinateUnlinkExteriorPlanarNeckStarRightTopPoint_mem_attachingRange_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarNeckGridRightOuter m)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight
          (x, b)) ∈
        range (fun s : Sphere 3 =>
          coordinateUnlinkExteriorPlanarNeckStarToRight m (a, s)) ↔
      ∃ e : CoordinateUnlinkExteriorPlanarRightNodeEndpoint m,
        coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m e = x ∧
          (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m e).1 = a := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  let H := coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m
  let V := coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m
  constructor
  · rintro ⟨s, hs⟩
    let q := V.symm (a, s)
    have hV : V q = (a, s) := V.apply_symm_apply (a, s)
    have hq :
        topologicalPushoutInl D.rightToTopRight D.rightToBottomRight (x, b) =
          D.verticalCenterToRight q := by
      apply H.injective
      exact hs.symm
    rcases topologicalPushout_jointly_surjective D.centerToTop D.centerToBottom q with
      ⟨z, hz⟩ | ⟨z, hz⟩
    · rw [← hz] at hq hV
      rw [TopologicalPushoutGridDiagram.verticalCenterToRight_inl,
        coordinateUnlinkExteriorPlanarNeckGridDiagram_topToTopRight_apply,
        coordinateUnlinkExteriorPlanarNeckGridTopToTopRight_apply] at hq
      have hz := topologicalPushoutInl_injective
        D.rightToTopRight D.rightToBottomRight
        (injective_coordinateUnlinkExteriorPlanarNeckGridRightToBottomRight_paths m) hq
      have hx : coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m z.1 = x :=
        (congrArg (fun w : CoordinateUnlinkExteriorPlanarNeckGridHR m => w.1) hz).symm
      rw [coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_inl] at hV
      have ha :
          (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m z.1).1 = a :=
        congrArg Prod.fst hV
      exact ⟨z.1, hx, ha⟩
    · rw [← hz] at hq hV
      rw [TopologicalPushoutGridDiagram.verticalCenterToRight_inr] at hq
      obtain ⟨c, hcTop, hcBottom⟩ :=
        (topologicalPushoutInl_eq_inr_iff
          D.rightToTopRight D.rightToBottomRight
          (injective_coordinateUnlinkExteriorPlanarNeckGridRightToTopRight_paths m)
          (x, b) (D.bottomToBottomRight z)).mp hq
      have hcx : c.1 = x := by
        rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_rightToTopRight_apply,
          coordinateUnlinkExteriorPlanarNeckGridRightToTopRight_apply] at hcTop
        exact congrArg (fun w : CoordinateUnlinkExteriorPlanarNeckGridHR m => w.1) hcTop
      have hcircle :
          coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle m z.1 =
            coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m c.1 := by
        rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_rightToBottomRight_apply,
          coordinateUnlinkExteriorPlanarNeckGridRightToBottomRight_apply,
          coordinateUnlinkExteriorPlanarNeckGridDiagram_bottomToBottomRight_apply,
          coordinateUnlinkExteriorPlanarNeckGridBottomToBottomRight_apply] at hcBottom
        exact (congrArg
          (fun w : CoordinateUnlinkExteriorPlanarNeckGridFR => w.1.1) hcBottom).symm
      obtain ⟨e, heSeam, heOuter⟩ :=
        coordinateUnlinkExteriorPlanarRightNodeBoundary_cross m z.1 c.1 hcircle
      rw [coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_inr] at hV
      have ha : z.1.1 = a := congrArg Prod.fst hV
      exact ⟨e, heOuter.trans hcx, congrArg Prod.fst heSeam |>.trans ha⟩
  · rintro ⟨e, heOuter, heLabel⟩
    let q : D.verticalCenter :=
      topologicalPushoutInl D.centerToTop D.centerToBottom (e, b)
    let vs : ZMod m × Sphere 3 := V q
    have hvsLabel : vs.1 = a := by
      change (V (topologicalPushoutInl D.centerToTop D.centerToBottom (e, b))).1 = a
      rw [coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_inl]
      exact heLabel
    refine ⟨vs.2, ?_⟩
    change H (D.verticalCenterToRight (V.symm (a, vs.2))) =
      H (topologicalPushoutInl D.rightToTopRight D.rightToBottomRight (x, b))
    congr 1
    have havs : (a, vs.2) = vs := Prod.ext hvsLabel.symm rfl
    rw [havs]
    change D.verticalCenterToRight (V.symm (V q)) = _
    rw [V.symm_apply_apply]
    change D.verticalCenterToRight
        (topologicalPushoutInl D.centerToTop D.centerToBottom (e, b)) = _
    rw [TopologicalPushoutGridDiagram.verticalCenterToRight_inl,
      coordinateUnlinkExteriorPlanarNeckGridDiagram_topToTopRight_apply,
      coordinateUnlinkExteriorPlanarNeckGridTopToTopRight_apply, heOuter]

/-- Along a fixed retained sector, membership in the selected remainder is independent of the
three-ball coordinate. -/
theorem coordinateUnlinkExteriorPlanarNeckStarRightTopPoint_mem_fiberRest_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarNeckGridRightOuter m)
    (b c : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarNeckStarRightTopPoint m x b ∈
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a ↔
      coordinateUnlinkExteriorPlanarNeckStarRightTopPoint m x c ∈
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a := by
  simp only [coordinateUnlinkExteriorPlanarNeckStarRightTopPoint]
  rw [coordinateUnlinkExteriorPlanarNeckStarRightGridPoint_mem_fiberRest_iff,
    coordinateUnlinkExteriorPlanarNeckStarRightGridPoint_mem_fiberRest_iff]
  constructor
  · intro hb hc
    apply hb
    rw [coordinateUnlinkExteriorPlanarNeckStarRightTopPoint_mem_attachingRange_iff]
      at hc ⊢
    exact hc
  · intro hc hb
    apply hc
    rw [coordinateUnlinkExteriorPlanarNeckStarRightTopPoint_mem_attachingRange_iff]
      at hb ⊢
    exact hb

/-- On the sphere boundary of the three-ball, the `HR` and `FR` descriptions agree in the
right-column pushout. -/
theorem coordinateUnlinkExteriorPlanarNeckStarRightTopPoint_sphere_eq_bottom_one
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridRightOuter m) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckStarRightTopPoint m x
        (coordinateUnlinkExteriorPlanarNeckGridSphereToBall s) =
      coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint m
        (coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m x) 1 s := by
  apply congrArg (coordinateUnlinkExteriorPlanarNeckStarRightGridPoint m)
  simpa only [coordinateUnlinkExteriorPlanarNeckGridDiagram_rightToTopRight_apply,
    coordinateUnlinkExteriorPlanarNeckGridRightToTopRight_apply,
    coordinateUnlinkExteriorPlanarNeckGridDiagram_rightToBottomRight_apply,
    coordinateUnlinkExteriorPlanarNeckGridRightToBottomRight_apply,
    coordinateUnlinkExteriorPlanarNeckGridRightOuterToNormalizedRight_apply,
    partialSphereSpinAnnulusOne_apply] using
      (topologicalPushout_condition
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight (x, s))

/-! ## Descent through the normalized right annulus -/

private def coordinateUnlinkExteriorPlanarNeckRightHalfTime :
    Set.Icc (0 : ℝ) 1 :=
  ⟨1 / 2, by norm_num, by norm_num⟩

private def coordinateUnlinkExteriorPlanarNeckRightOpenHalfTime :
    Set.Ioo (0 : ℝ) 1 :=
  ⟨1 / 2, by norm_num, by norm_num⟩

/-- Linearly move a closed annulus time toward `1 / 2`. -/
private def coordinateUnlinkExteriorPlanarNeckRightTimeDescent
    (t : Set.Icc (0 : ℝ) 1) (r : I) : Set.Icc (0 : ℝ) 1 :=
  ⟨(1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) * (1 / 2), by
      have hfirst : 0 ≤ (1 - (r : ℝ)) * (t : ℝ) :=
        mul_nonneg (sub_nonneg.mpr r.2.2) t.2.1
      have hsecond : 0 ≤ (r : ℝ) * (1 / 2) :=
        mul_nonneg r.2.1 (by norm_num)
      exact add_nonneg hfirst hsecond,
    by
      have hfirst : (1 - (r : ℝ)) * (t : ℝ) ≤ 1 - (r : ℝ) :=
        by simpa using
          mul_le_mul_of_nonneg_left t.2.2 (sub_nonneg.mpr r.2.2)
      have hsecond : (r : ℝ) * (1 / 2) ≤ (r : ℝ) :=
        mul_le_of_le_one_right r.2.1 (by norm_num)
      linarith⟩

private theorem continuous_coordinateUnlinkExteriorPlanarNeckRightTimeDescent
    (t : Set.Icc (0 : ℝ) 1) :
    Continuous (coordinateUnlinkExteriorPlanarNeckRightTimeDescent t) := by
  apply Continuous.subtype_mk
  fun_prop

@[simp]
private theorem coordinateUnlinkExteriorPlanarNeckRightTimeDescent_zero
    (t : Set.Icc (0 : ℝ) 1) :
    coordinateUnlinkExteriorPlanarNeckRightTimeDescent t 0 = t := by
  apply Subtype.ext
  simp [coordinateUnlinkExteriorPlanarNeckRightTimeDescent]

@[simp]
private theorem coordinateUnlinkExteriorPlanarNeckRightTimeDescent_one
    (t : Set.Icc (0 : ℝ) 1) :
    coordinateUnlinkExteriorPlanarNeckRightTimeDescent t 1 =
      coordinateUnlinkExteriorPlanarNeckRightHalfTime := by
  apply Subtype.ext
  norm_num [coordinateUnlinkExteriorPlanarNeckRightTimeDescent,
    coordinateUnlinkExteriorPlanarNeckRightHalfTime]

private theorem coordinateUnlinkExteriorPlanarNeckRightTimeDescent_pos
    (t : Set.Icc (0 : ℝ) 1) (ht : 0 < (t : ℝ)) (r : I) :
    0 < (coordinateUnlinkExteriorPlanarNeckRightTimeDescent t r : ℝ) := by
  change 0 < (1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) * (1 / 2)
  have hfirst : 0 ≤ (1 - (r : ℝ)) * (t : ℝ) :=
    mul_nonneg (sub_nonneg.mpr r.2.2) (le_of_lt ht)
  have hsecond : 0 ≤ (r : ℝ) * (1 / 2) :=
    mul_nonneg r.2.1 (by norm_num)
  by_cases hr : (r : ℝ) = 0
  · rw [hr]
    simpa using ht
  · have hrpos : 0 < (r : ℝ) := lt_of_le_of_ne r.2.1 (Ne.symm hr)
    have hsecondpos : 0 < (r : ℝ) * (1 / 2) :=
      mul_pos hrpos (by norm_num)
    exact add_pos_of_nonneg_of_pos hfirst hsecondpos

private theorem coordinateUnlinkExteriorPlanarNeckRightTimeDescent_lt_one_of_ne_zero
    (t : Set.Icc (0 : ℝ) 1) (r : I) (hr : r ≠ 0) :
    (coordinateUnlinkExteriorPlanarNeckRightTimeDescent t r : ℝ) < 1 := by
  change (1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) * (1 / 2) < 1
  have hrval : (r : ℝ) ≠ 0 := by
    intro h
    apply hr
    exact Subtype.ext h
  have hrpos : 0 < (r : ℝ) := lt_of_le_of_ne r.2.1 (Ne.symm hrval)
  have hfirst : (1 - (r : ℝ)) * (t : ℝ) ≤ 1 - (r : ℝ) :=
    by simpa using
      mul_le_mul_of_nonneg_left t.2.2 (sub_nonneg.mpr r.2.2)
  nlinarith

private def coordinateUnlinkExteriorPlanarNeckRightTimePath
    (t : Set.Icc (0 : ℝ) 1) :
    Path t coordinateUnlinkExteriorPlanarNeckRightHalfTime where
  toFun := coordinateUnlinkExteriorPlanarNeckRightTimeDescent t
  continuous_toFun :=
    continuous_coordinateUnlinkExteriorPlanarNeckRightTimeDescent t
  source' := coordinateUnlinkExteriorPlanarNeckRightTimeDescent_zero t
  target' := coordinateUnlinkExteriorPlanarNeckRightTimeDescent_one t

/-- Vary only the closed normalized annulus time in the right-column star point. -/
private def coordinateUnlinkExteriorPlanarNeckStarRightClosedAnnulusCurve
    (m : ℕ) [NeZero m] (u : Sphere 1) (s : Sphere 2) :
    C(Set.Icc (0 : ℝ) 1, CoordinateUnlinkExteriorPlanarNeckStar m) where
  toFun t := coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint m u t s
  continuous_toFun := by
    have hx : Continuous
        (fun t : Set.Icc (0 : ℝ) 1 => ((u, t), s)) :=
      (continuous_const.prodMk continuous_id).prodMk continuous_const
    have hp :=
      (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
        (coordinateUnlinkExteriorPlanarNeckGridDiagram
          m).rightToBottomRight).continuous.comp hx
    have hh :=
      (coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement
        m).continuous.comp hp
    exact
      (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)).continuous.comp hh

/-- Every positive-time right-annulus point already in the selected strict remainder is joined
there to the open right-annulus carrier.  This includes the outer time `1`, provided its seam
label is not the selected one. -/
theorem coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint_joinedIn_interiorCarrier
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) (ht : 0 < (t : ℝ))
    (hy : coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint m u t s ∈
      coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a) :
    ∃ z ∈ range (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m),
      JoinedIn
        (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
          coordinateUnlinkExteriorPlanarNeckStarFiberRest m a)
        (coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint m u t s) z := by
  let P := coordinateUnlinkExteriorPlanarNeckRightTimePath t
  let C := coordinateUnlinkExteriorPlanarNeckStarRightClosedAnnulusCurve m u s
  have htime : JoinedIn (range (P : I → Set.Icc (0 : ℝ) 1)) t
      coordinateUnlinkExteriorPlanarNeckRightHalfTime :=
    ⟨P, fun r => ⟨r, rfl⟩⟩
  have hmapped := htime.map C.continuous
  have hsubset :
      C '' range (P : I → Set.Icc (0 : ℝ) 1) ⊆
        coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
          coordinateUnlinkExteriorPlanarNeckStarFiberRest m a := by
    rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
    constructor
    · apply
        (coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint_mem_strictCore_iff
          m u (coordinateUnlinkExteriorPlanarNeckRightTimeDescent t r) s).mpr
      exact coordinateUnlinkExteriorPlanarNeckRightTimeDescent_pos t ht r
    · change coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint m u
        (coordinateUnlinkExteriorPlanarNeckRightTimeDescent t r) s ∈
          coordinateUnlinkExteriorPlanarNeckStarFiberRest m a
      by_cases hr : r = 0
      · subst r
        simpa using hy.2
      · rw [coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint_eq_normalized]
        exact
          coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint_mem_rest
            m a u (coordinateUnlinkExteriorPlanarNeckRightTimeDescent t r) s
              (coordinateUnlinkExteriorPlanarNeckRightTimeDescent_lt_one_of_ne_zero
                t r hr)
  have hjoined := hmapped.mono hsubset
  refine ⟨C coordinateUnlinkExteriorPlanarNeckRightHalfTime, ?_, hjoined⟩
  refine ⟨(u, (coordinateUnlinkExteriorPlanarNeckRightOpenHalfTime, s)), ?_⟩
  change coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint m u
      (coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed
        coordinateUnlinkExteriorPlanarNeckRightOpenHalfTime) s =
    coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint m u
      coordinateUnlinkExteriorPlanarNeckRightHalfTime s
  rw [coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint_eq_normalized]
  congr 1

/-! ## Crossing from the one-handle sector into the annulus -/

/-- Vary only the three-ball coordinate in a fixed retained one-handle sector. -/
private def coordinateUnlinkExteriorPlanarNeckStarRightTopBallCurve
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridRightOuter m) :
    C(EuclideanClosedBall 3, CoordinateUnlinkExteriorPlanarNeckStar m) where
  toFun b := coordinateUnlinkExteriorPlanarNeckStarRightTopPoint m x b
  continuous_toFun := by
    have hx : Continuous
        (fun b : EuclideanClosedBall 3 => (x, b)) :=
      continuous_const.prodMk continuous_id
    have hp :=
      (topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
        (coordinateUnlinkExteriorPlanarNeckGridDiagram
          m).rightToBottomRight).continuous.comp hx
    have hh :=
      (coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement
        m).continuous.comp hp
    exact
      (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)).continuous.comp hh

/-- An `HR` point in the exact strict remainder can move through its three-ball, cross the
right-column quotient at time `1`, and enter the open right-annulus carrier. -/
theorem coordinateUnlinkExteriorPlanarNeckStarRightTopPoint_joinedIn_interiorCarrier
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarNeckGridRightOuter m)
    (b : EuclideanClosedBall 3) (s : Sphere 2)
    (hy : coordinateUnlinkExteriorPlanarNeckStarRightTopPoint m x b ∈
      coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a) :
    ∃ z ∈ range (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m),
      JoinedIn
        (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
          coordinateUnlinkExteriorPlanarNeckStarFiberRest m a)
        (coordinateUnlinkExteriorPlanarNeckStarRightTopPoint m x b) z := by
  let C := coordinateUnlinkExteriorPlanarNeckStarRightTopBallCurve m x
  have hball : JoinedIn (univ : Set (EuclideanClosedBall 3)) b
      (coordinateUnlinkExteriorPlanarNeckGridSphereToBall s) :=
    (isPathConnected_euclideanClosedBall 3).joinedIn _ (mem_univ _) _ (mem_univ _)
  have hmapped := hball.map C.continuous
  have hsubset : C '' (univ : Set (EuclideanClosedBall 3)) ⊆
      coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a := by
    rintro _ ⟨c, _hc, rfl⟩
    constructor
    · exact coordinateUnlinkExteriorPlanarNeckStarRightTopPoint_mem_strictCore m x c
    · exact
        (coordinateUnlinkExteriorPlanarNeckStarRightTopPoint_mem_fiberRest_iff
          m a x b c).mp hy.2
  have htoBoundary := hmapped.mono hsubset
  change JoinedIn
      (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a)
      (coordinateUnlinkExteriorPlanarNeckStarRightTopPoint m x b)
      (coordinateUnlinkExteriorPlanarNeckStarRightTopPoint m x
        (coordinateUnlinkExteriorPlanarNeckGridSphereToBall s)) at htoBoundary
  rw [coordinateUnlinkExteriorPlanarNeckStarRightTopPoint_sphere_eq_bottom_one]
    at htoBoundary
  obtain ⟨z, hz, hfromBoundary⟩ :=
    coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint_joinedIn_interiorCarrier
      m a (coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m x) 1 s
        (by norm_num) htoBoundary.target_mem
  exact ⟨z, hz, htoBoundary.trans hfromBoundary⟩

/-! ## Access from the complete central right column -/

/-- Every right-column grid point in the exact strict remainder is joined there to the open
right-annulus carrier. -/
theorem coordinateUnlinkExteriorPlanarNeckStarRightGridPoint_joinedIn_interiorCarrier
    (m : ℕ) [NeZero m] (a : ZMod m)
    (q : (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalRight)
    (hq : coordinateUnlinkExteriorPlanarNeckStarRightGridPoint m q ∈
      coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a) :
    ∃ z ∈ range (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m),
      JoinedIn
        (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
          coordinateUnlinkExteriorPlanarNeckStarFiberRest m a)
        (coordinateUnlinkExteriorPlanarNeckStarRightGridPoint m q) z := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  rcases topologicalPushout_jointly_surjective
      D.rightToTopRight D.rightToBottomRight q with
    ⟨x, hx⟩ | ⟨x, hx⟩
  · rw [← hx] at hq ⊢
    obtain ⟨s, _hs⟩ := isPathConnected_sphereTwo.nonempty
    exact
      coordinateUnlinkExteriorPlanarNeckStarRightTopPoint_joinedIn_interiorCarrier
        m a x.1 x.2 s hq
  · rw [← hx] at hq ⊢
    have ht : 0 < (x.1.2 : ℝ) :=
      (coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint_mem_strictCore_iff
        m x.1.1 x.1.2 x.2).mp hq.1
    exact
      coordinateUnlinkExteriorPlanarNeckStarRightBottomPoint_joinedIn_interiorCarrier
        m a x.1.1 x.1.2 x.2 ht hq

/-- Every point represented through the right coprojection of the neck star, if it lies in the
exact strict selected remainder, is joined inside that same set to a point of the open
right-annulus carrier. -/
theorem coordinateUnlinkExteriorPlanarNeckStarRightCoprojection_joinedIn_interiorCarrier
    (m : ℕ) [NeZero m] (a : ZMod m)
    (y : CoordinateUnlinkExteriorPlanarNeckRightComplement m)
    (hy : topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m) y ∈
      coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a) :
    ∃ z ∈ range (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m),
      JoinedIn
        (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
          coordinateUnlinkExteriorPlanarNeckStarFiberRest m a)
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
          (coordinateUnlinkExteriorPlanarNeckStarToRight m) y) z := by
  let H := coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m
  let q := H.symm y
  have hpoint : coordinateUnlinkExteriorPlanarNeckStarRightGridPoint m q =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m) y := by
    change topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m) (H q) = _
    rw [H.apply_symm_apply]
  have hq : coordinateUnlinkExteriorPlanarNeckStarRightGridPoint m q ∈
      coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a := by
    rw [hpoint]
    exact hy
  obtain ⟨z, hz, hj⟩ :=
    coordinateUnlinkExteriorPlanarNeckStarRightGridPoint_joinedIn_interiorCarrier
      m a q hq
  exact ⟨z, hz, hpoint ▸ hj⟩

end SplittingSpheres
