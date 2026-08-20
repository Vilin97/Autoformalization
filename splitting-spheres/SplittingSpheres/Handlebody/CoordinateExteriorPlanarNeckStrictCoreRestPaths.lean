/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckStrictCoreLeftPaths
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckStrictCoreRightPaths

/-!
# Paths in the strict remainder of a selected planar-neck seam

This file proves path connectedness of the exact strict remainder of one selected labelled
seam in the literal neck star.  A nonselected left open-annulus carrier is joined to the
right open-annulus carrier by moving a chosen seam-circle point from normalized time `1 / 2`
to time `1`, crossing the star pushout, and using right-column access.

For an arbitrary remainder point, pushout coverage reduces to a right representative or a
left representative.  A left representative in the attaching range is changed directly to
a right representative.  Otherwise its literal label differs from the selected label, so
left-side access and the preceding bridge apply.

The conclusions concern only `StrictCore ∩ FiberRest`.  No assertion is made about the whole
compact pullback, an exact number of components, or any smooth or manifold structure.
-/

@[expose] public section

noncomputable section

open Function Set Topology
open Set.Notation

namespace SplittingSpheres

/-! ## Left representatives of the selected remainder -/

/-- A point represented by the left star coprojection belongs to the selected remainder
exactly when its literal left label is not the selected label. -/
theorem coordinateUnlinkExteriorPlanarNeckStar_inl_mem_fiberRest_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarNeckLeftComplement m) :
    topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m) x ∈
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a ↔
      coordinateUnlinkExteriorPlanarNeckStarLeftLabel m x ≠ a := by
  let f := coordinateUnlinkExteriorPlanarNeckStarToLeft m
  let g := coordinateUnlinkExteriorPlanarNeckStarToRight m
  let label := coordinateUnlinkExteriorPlanarNeckStarLeftLabel m
  change topologicalPushoutInl f g x ∈
      topologicalPushoutFiberRest f g label a ↔ label x ≠ a
  constructor
  · rintro ⟨hxSeam, hxOff⟩ hxa
    by_cases hxf : x ∈ range f
    · obtain ⟨⟨b, s⟩, hbs⟩ := hxf
      have hba : b = a := by
        rw [← hxa, ← hbs]
        exact (coordinateUnlinkExteriorPlanarNeckStarLeftLabel_toLeft m (b, s)).symm
      subst b
      apply hxSeam
      exact ⟨s, congrArg (topologicalPushoutInl f g) hbs⟩
    · apply hxOff
      exact ⟨x, ⟨hxa, hxf⟩, rfl⟩
  · intro hxa
    constructor
    · rintro ⟨s, hs⟩
      have hfx : f (a, s) = x :=
        topologicalPushoutInl_injective f g
          (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToRight
            m).injective hs
      apply hxa
      calc
        label x = label (f (a, s)) := by rw [hfx]
        _ = a := coordinateUnlinkExteriorPlanarNeckStarLeftLabel_toLeft m (a, s)
    · rintro ⟨y, hy, hxy⟩
      have hyx : y = x :=
        topologicalPushoutInl_injective f g
          (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToRight
            m).injective hxy
      apply hxa
      calc
        label x = label y := by rw [hyx]
        _ = a := hy.1

/-- A strict nonselected left side is contained in the exact strict selected remainder. -/
theorem coordinateUnlinkExteriorPlanarNeckStarStrictLeftSide_subset_strictFiberRest_of_ne
    (m : ℕ) [NeZero m] (a b : ZMod m) (hba : b ≠ a) :
    coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m b ⊆
      coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a := by
  rintro _ ⟨hstrict, y, hy, rfl⟩
  refine ⟨hstrict,
    (coordinateUnlinkExteriorPlanarNeckStar_inl_mem_fiberRest_iff m a y).mpr ?_⟩
  intro hya
  exact hba (hy.1.symm.trans hya)

/-! ## Crossing a nonselected left open annulus to the right carrier -/

private def coordinateUnlinkExteriorPlanarNeckRestBridgeHalfOpen :
    Set.Ioo (0 : ℝ) 1 :=
  ⟨1 / 2, by norm_num, by norm_num⟩

private def coordinateUnlinkExteriorPlanarNeckRestBridgeOneClosed :
    Set.Icc (0 : ℝ) 1 :=
  ⟨1, by norm_num, by norm_num⟩

private def coordinateUnlinkExteriorPlanarNeckStarLeftClosedTimeCurve
    (m : ℕ) [NeZero m] (b : ZMod m) (u : Sphere 1) (s : Sphere 2) :
    C(Set.Icc (0 : ℝ) 1, CoordinateUnlinkExteriorPlanarNeckStar m) where
  toFun t :=
    coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m b u t s
  continuous_toFun := by
    have hx : Continuous
        (fun t : Set.Icc (0 : ℝ) 1 => ((b, (u, t)), s)) :=
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)).prodMk
        continuous_const
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
    exact hs.congr fun t =>
      (coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_eq_grid
        m b u t s).symm

private def coordinateUnlinkExteriorPlanarNeckRestBridgeTimeInclusion :
    C(Set.Icc (1 / 2 : ℝ) 1, Set.Icc (0 : ℝ) 1) where
  toFun t := ⟨t.1, by linarith [t.2.1], t.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private theorem coordinateUnlinkExteriorPlanarNeckStar_leftSeamOne_eq_rightCoprojection
    (m : ℕ) [NeZero m] (b : ZMod m)
    (v : CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    ∃ y : CoordinateUnlinkExteriorPlanarNeckRightComplement m,
      coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m b
          (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m b v)
          coordinateUnlinkExteriorPlanarNeckRestBridgeOneClosed s =
        topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
          (coordinateUnlinkExteriorPlanarNeckStarToRight m) y := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  let V := coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m
  let q := topologicalPushoutInr D.centerToTop D.centerToBottom ((b, v), s)
  let c := V q
  refine ⟨coordinateUnlinkExteriorPlanarNeckStarToRight m c, ?_⟩
  rw [coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_eq_grid]
  have hleft :
      topologicalPushoutInr D.leftToTopLeft D.leftToBottomLeft
          ((b, (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m b v,
            coordinateUnlinkExteriorPlanarNeckRestBridgeOneClosed)), s) =
        D.verticalCenterToLeft q := by
    rw [show D.verticalCenterToLeft q =
        topologicalPushoutInr D.leftToTopLeft D.leftToBottomLeft
          (D.bottomToBottomLeft ((b, v), s)) by
      change D.verticalCenterToLeft
          (topologicalPushoutInr D.centerToTop D.centerToBottom ((b, v), s)) = _
      rw [TopologicalPushoutGridDiagram.verticalCenterToLeft_inr]]
    apply congrArg (topologicalPushoutInr D.leftToTopLeft D.leftToBottomLeft)
    rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_bottomToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridBottomToBottomLeft_apply]
    apply Prod.ext
    · rw [← coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap_normalized m b v]
      rfl
    · rfl
  rw [hleft]
  calc
    topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
          (coordinateUnlinkExteriorPlanarNeckStarToRight m)
          (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
            (D.verticalCenterToLeft q)) =
        topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
          (coordinateUnlinkExteriorPlanarNeckStarToRight m)
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m c) := by
      congr 1
      rw [coordinateUnlinkExteriorPlanarNeckStarToLeft_apply]
      change coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
          (D.verticalCenterToLeft q) =
        coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
          (D.verticalCenterToLeft (V.symm (V q)))
      rw [V.symm_apply_apply]
    _ = topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
          (coordinateUnlinkExteriorPlanarNeckStarToRight m)
          (coordinateUnlinkExteriorPlanarNeckStarToRight m c) :=
      topologicalPushout_condition
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m) c

private theorem coordinateUnlinkExteriorPlanarNeckStar_leftSeamHalf_joinedIn_rightCarrier
    (m : ℕ) [NeZero m] (a b : ZMod m) (hba : b ≠ a)
    (v : CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    ∃ z ∈ range (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m),
      JoinedIn
        (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
          coordinateUnlinkExteriorPlanarNeckStarFiberRest m a)
        (coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier m b
          (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m b v,
            (coordinateUnlinkExteriorPlanarNeckRestBridgeHalfOpen, s))) z := by
  let P :=
    (coordinateUnlinkExteriorPlanarNeckStarLeftClosedTimeCurve m b
      (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m b v) s).comp
        coordinateUnlinkExteriorPlanarNeckRestBridgeTimeInclusion
  let lo : Set.Icc (1 / 2 : ℝ) 1 := ⟨1 / 2, le_rfl, by norm_num⟩
  let hi : Set.Icc (1 / 2 : ℝ) 1 := ⟨1, by norm_num, le_rfl⟩
  let _ : PathConnectedSpace (Set.Icc (1 / 2 : ℝ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp <|
      (convex_Icc (1 / 2 : ℝ) 1).isPathConnected
        ⟨1 / 2, le_rfl, by norm_num⟩
  have hsubset : range P ⊆
      coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a := by
    rintro _ ⟨t, rfl⟩
    let tc := coordinateUnlinkExteriorPlanarNeckRestBridgeTimeInclusion t
    let x :=
      coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
          ((b, (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m b v, tc)), s))
    have hpoint : P t = topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m) x := by
      exact coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_eq_grid
        m b (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m b v) tc s
    rw [hpoint]
    constructor
    · rw [← hpoint]
      apply
        (coordinateUnlinkExteriorPlanarNeckStar_normalizedLeft_mem_strictCore_iff
          m b (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m b v) tc s).mpr
      change 0 < (t : ℝ)
      linarith [t.2.1]
    · apply
        (coordinateUnlinkExteriorPlanarNeckStar_inl_mem_fiberRest_iff m a x).mpr
      rw [coordinateUnlinkExteriorPlanarNeckGrid_bottomLeft_complement_label]
      exact hba
  have hpath : JoinedIn
      (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a)
      (P lo) (P hi) :=
    (isPathConnected_range P.continuous).joinedIn
      _ ⟨lo, rfl⟩ _ ⟨hi, rfl⟩ |>.mono hsubset
  have hlo : P lo =
      coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier m b
        (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m b v,
          (coordinateUnlinkExteriorPlanarNeckRestBridgeHalfOpen, s)) := by
    change coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m b
        (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m b v)
        (coordinateUnlinkExteriorPlanarNeckRestBridgeTimeInclusion lo) s =
      coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m b
        (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m b v)
        (coordinateUnlinkExteriorPlanarNeckOpenTimeToClosed
          coordinateUnlinkExteriorPlanarNeckRestBridgeHalfOpen) s
    congr 1
  have hhi : P hi =
      coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m b
        (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m b v)
        coordinateUnlinkExteriorPlanarNeckRestBridgeOneClosed s := by
    change coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m b
        (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m b v)
        (coordinateUnlinkExteriorPlanarNeckRestBridgeTimeInclusion hi) s = _
    congr 1
  obtain ⟨y, hy⟩ :=
    coordinateUnlinkExteriorPlanarNeckStar_leftSeamOne_eq_rightCoprojection
      m b v s
  have hyMem : topologicalPushoutInr
      (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
      (coordinateUnlinkExteriorPlanarNeckStarToRight m) y ∈
        coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
          coordinateUnlinkExteriorPlanarNeckStarFiberRest m a := by
    rw [← hy, ← hhi]
    exact hpath.target_mem
  obtain ⟨z, hz, hyz⟩ :=
    coordinateUnlinkExteriorPlanarNeckStarRightCoprojection_joinedIn_interiorCarrier
      m a y hyMem
  refine ⟨z, hz, ?_⟩
  rw [hlo] at hpath
  rw [hhi, hy] at hpath
  exact hpath.trans hyz

/-- Every point of a nonselected normalized left open-annulus carrier is joined inside the
exact strict selected remainder to the normalized right open-annulus carrier. -/
theorem coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier_joinedIn_rightCarrier
    (m : ℕ) [NeZero m] (a b : ZMod m) (hba : b ≠ a)
    (x : Sphere 1 × (Set.Ioo (0 : ℝ) 1 × Sphere 2)) :
    ∃ z ∈ range (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m),
      JoinedIn
        (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
          coordinateUnlinkExteriorPlanarNeckStarFiberRest m a)
        (coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier m b x) z := by
  let v : CoordinateUnlinkExteriorPlanarNeckInterval := 0
  let s : Sphere 2 := coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint
  let y : Sphere 1 × (Set.Ioo (0 : ℝ) 1 × Sphere 2) :=
    (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m b v,
      (coordinateUnlinkExteriorPlanarNeckRestBridgeHalfOpen, s))
  have hleft :=
    coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier_joinedIn m b x y
  have hleft' : JoinedIn
      (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a)
      (coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier m b x)
      (coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier m b y) :=
    hleft.mono <|
      coordinateUnlinkExteriorPlanarNeckStarStrictLeftSide_subset_strictFiberRest_of_ne
        m a b hba
  obtain ⟨z, hz, hyz⟩ :=
    coordinateUnlinkExteriorPlanarNeckStar_leftSeamHalf_joinedIn_rightCarrier
      m a b hba v s
  exact ⟨z, hz, hleft'.trans hyz⟩

/-! ## Access and path connectedness of the complete strict remainder -/

/-- Every point of the exact strict selected remainder is joined inside that remainder to
the normalized right open-annulus carrier. -/
theorem coordinateUnlinkExteriorPlanarNeckStarStrictFiberRest_accesses_rightCarrier
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarNeckStar m)
    (hx : x ∈ coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
      coordinateUnlinkExteriorPlanarNeckStarFiberRest m a) :
    ∃ z ∈ range (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m),
      JoinedIn
        (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
          coordinateUnlinkExteriorPlanarNeckStarFiberRest m a) x z := by
  let f := coordinateUnlinkExteriorPlanarNeckStarToLeft m
  let g := coordinateUnlinkExteriorPlanarNeckStarToRight m
  rcases topologicalPushout_jointly_surjective f g x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · by_cases hy : y ∈ range f
    · obtain ⟨c, hc⟩ := hy
      have hcross : topologicalPushoutInl f g y =
          topologicalPushoutInr f g (g c) := by
        rw [← hc]
        exact topologicalPushout_condition f g c
      have hright : topologicalPushoutInr f g (g c) ∈
          coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
            coordinateUnlinkExteriorPlanarNeckStarFiberRest m a := by
        rw [← hcross]
        exact hx
      obtain ⟨z, hz, hj⟩ :=
        coordinateUnlinkExteriorPlanarNeckStarRightCoprojection_joinedIn_interiorCarrier
          m a (g c) hright
      rw [← hcross] at hj
      exact ⟨z, hz, hj⟩
    · let b := coordinateUnlinkExteriorPlanarNeckStarLeftLabel m y
      have hba : b ≠ a :=
        (coordinateUnlinkExteriorPlanarNeckStar_inl_mem_fiberRest_iff m a y).mp hx.2
      have hleft : topologicalPushoutInl f g y ∈
          coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
            coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m b := by
        refine ⟨hx.1, ?_⟩
        exact ⟨y, ⟨rfl, hy⟩, rfl⟩
      obtain ⟨u, hu⟩ :=
        coordinateUnlinkExteriorPlanarNeckStarStrictLeftSide_accesses_interiorCarrier
          m b (topologicalPushoutInl f g y) hleft
      have hu' : JoinedIn
          (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
            coordinateUnlinkExteriorPlanarNeckStarFiberRest m a)
          (topologicalPushoutInl f g y)
          (coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier m b u) :=
        hu.mono <|
          coordinateUnlinkExteriorPlanarNeckStarStrictLeftSide_subset_strictFiberRest_of_ne
            m a b hba
      obtain ⟨z, hz, huz⟩ :=
        coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier_joinedIn_rightCarrier
          m a b hba u
      exact ⟨z, hz, hu'.trans huz⟩
  · exact
      coordinateUnlinkExteriorPlanarNeckStarRightCoprojection_joinedIn_interiorCarrier
        m a y hx

/-- The exact strict remainder of a selected labelled seam is path connected. -/
theorem isPathConnected_coordinateUnlinkExteriorPlanarNeckStarStrictFiberRest
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsPathConnected
      (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a) := by
  obtain ⟨x, hx⟩ :=
    (isPathConnected_range_coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier
      m).nonempty
  rcases hx with ⟨u, rfl⟩
  refine
    ⟨coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier m u,
      range_coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier_subset
        m a ⟨u, rfl⟩, ?_⟩
  intro y hy
  obtain ⟨z, ⟨v, rfl⟩, hyz⟩ :=
    coordinateUnlinkExteriorPlanarNeckStarStrictFiberRest_accesses_rightCarrier
      m a y hy
  exact
    (coordinateUnlinkExteriorPlanarNeckStarRightInteriorCarrier_joinedIn
      m a u v).trans hyz.symm

/-- The exact strict remainder of a selected labelled seam is preconnected. -/
theorem isPreconnected_coordinateUnlinkExteriorPlanarNeckStarStrictFiberRest
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsPreconnected
      (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a) :=
  (isPathConnected_coordinateUnlinkExteriorPlanarNeckStarStrictFiberRest
    m a).isConnected.isPreconnected

end SplittingSpheres
