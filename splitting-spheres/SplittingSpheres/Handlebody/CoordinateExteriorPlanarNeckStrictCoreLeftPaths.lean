/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckStrictCoreInteriorAccess

/-!
# Paths in a selected strict left side of the planar neck star

This file proves that the intersection of the strict neck core with one selected left leaf
off the attaching seam is path connected.  The proof uses the exact left-column grid
presentation.  A bottom-annulus point has positive time by the strict-core criterion and can
therefore move into the normalized open-annulus carrier.  A top one-handle point first moves
in its fixed outer-arc three-ball fiber to the boundary, crosses the pushout at annulus time
`1`, and then enters the open annulus.

The endpoint calculation also shows that keeping the top outer-arc coordinate fixed while
changing the ball coordinate preserves both its leaf label and avoidance of the central
attaching range.  Thus the ball path is taken in a complete fiber already known to be off the
seam; no connectivity statement about a ball complement is used.  The result concerns only
the selected left side and makes no component-count or ambient-complement claim.
-/

@[expose] public section

open Function Set Topology
open Set.Notation

noncomputable section

namespace SplittingSpheres

private theorem injective_neckGrid_leftToTopLeft
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft := by
  intro x y hxy
  apply Prod.ext
  · exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridHL m => z.1) hxy
  · apply Subtype.ext
    exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridHL m => z.2.1) hxy

private theorem injective_neckGrid_leftToBottomLeft
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft := by
  intro x y hxy
  rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_leftToBottomLeft_apply,
    coordinateUnlinkExteriorPlanarNeckGridLeftToBottomLeft_apply] at hxy
  apply Prod.ext
  · apply Prod.ext
    · exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridFL m => z.1.1) hxy
    · apply injective_coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap
      exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridFL m => z.1.2.1) hxy
  · exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridFL m => z.2) hxy

private theorem neckGridVerticalLeftHomeomorphComplement_not_range_iff
    (m : ℕ) [NeZero m]
    (q : (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalLeft) :
    coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m q ∉
        range (coordinateUnlinkExteriorPlanarNeckStarToLeft m) ↔
      q ∉ range
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  let H := coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
  let V := coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m
  constructor
  · intro hq ⟨c, hc⟩
    apply hq
    refine ⟨V c, ?_⟩
    rw [coordinateUnlinkExteriorPlanarNeckStarToLeft_apply, V.symm_apply_apply]
    exact congrArg H hc
  · intro hq ⟨z, hz⟩
    apply hq
    refine ⟨V.symm z, ?_⟩
    apply H.injective
    rw [coordinateUnlinkExteriorPlanarNeckStarToLeft_apply] at hz
    exact hz

/-- Exact label of a top-left grid point after passage to the literal left complement. -/
theorem coordinateUnlinkExteriorPlanarNeckGrid_topLeft_complement_label
    (m : ℕ) [NeZero m]
    (w : CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarNeckStarLeftLabel m
        (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
          (topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
            (w, b))) = w.1 := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  let x : CoordinateUnlinkExteriorPlanarNeckGridHL m := (w, b)
  have hsymm :
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal m).symm
          (topologicalPushoutInl D.leftToTopLeft D.leftToBottomLeft x) =
        topologicalPushoutInl
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
    exact (simLeftVerticalLeftOriginal_inl m x).symm
  rw [coordinateUnlinkExteriorPlanarNeckStarLeftLabel_apply,
    coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement,
    Homeomorph.trans_apply, hsymm,
    coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphComplementOneHandles_apply_coe]
  change
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle m
      ((coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
        m).columnFirstTopLeft x)).1 = w.1
  rw [coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle_topLeft]

private theorem neckGrid_topLeft_mem_verticalCenterRange_of_endpoint
    (m : ℕ) [NeZero m]
    (w : CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m)
    (b : EuclideanClosedBall 3)
    (hw : w ∈ range
      (coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter m)) :
    topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
        (w, b) ∈
      range
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  obtain ⟨e, rfl⟩ := hw
  refine ⟨topologicalPushoutInl D.centerToTop D.centerToBottom (e, b), ?_⟩
  rw [TopologicalPushoutGridDiagram.verticalCenterToLeft_inl,
    coordinateUnlinkExteriorPlanarNeckGridDiagram_topToTopLeft_apply,
    coordinateUnlinkExteriorPlanarNeckGridTopToTopLeft_apply]

private theorem neckGrid_endpoint_of_topLeft_mem_verticalCenterRange
    (m : ℕ) [NeZero m]
    (w : CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m)
    (b : EuclideanClosedBall 3)
    (hmem :
      topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
          (w, b) ∈
        range
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft) :
    w ∈ range
      (coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter m) := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  obtain ⟨q, hq⟩ := hmem
  rcases topologicalPushout_jointly_surjective D.centerToTop D.centerToBottom q with
    ⟨e, rfl⟩ | ⟨x, rfl⟩
  · rw [TopologicalPushoutGridDiagram.verticalCenterToLeft_inl] at hq
    have htop := topologicalPushoutInl_injective
      D.leftToTopLeft D.leftToBottomLeft
      (injective_neckGrid_leftToBottomLeft m) hq
    rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_topToTopLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridTopToTopLeft_apply] at htop
    exact ⟨e.1, congrArg Prod.fst htop⟩
  · rw [TopologicalPushoutGridDiagram.verticalCenterToLeft_inr] at hq
    obtain ⟨v, hvTop, hvBottom⟩ :=
      (topologicalPushoutInl_eq_inr_iff D.leftToTopLeft D.leftToBottomLeft
        (injective_neckGrid_leftToTopLeft m) (w, b)
        (D.bottomToBottomLeft x)).mp hq.symm
    rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_leftToTopLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridLeftToTopLeft_apply] at hvTop
    have hvw : v.1 = w := congrArg Prod.fst hvTop
    rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_leftToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridLeftToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridDiagram_bottomToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridBottomToBottomLeft_apply] at hvBottom
    have hcircle := congrArg
      (fun z : CoordinateUnlinkExteriorPlanarNeckGridFL m => z.1.2.1) hvBottom
    have hcircle' :
        coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap v.1.2 =
          coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m x.1.1 x.1.2 := by
      exact hcircle
    obtain ⟨e, heOuter, _heSeam⟩ :=
      coordinateUnlinkExteriorPlanarLeftLeafBoundary_cross
        m x.1.1 v.1.2 x.1.2 hcircle'
    let e' :=
      (coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m).symm
        (w.1, e)
    have he' :=
      (coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m).apply_symm_apply
        (w.1, e)
    rw [coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph_apply] at he'
    change
      (((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m e').1, e'.2) :
          CoordinateUnlinkExteriorPlanarNeckGridEndpoint m) = (w.1, e) at he'
    have heLabel :
        (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m e').1 = w.1 :=
      congrArg
        (fun z : CoordinateUnlinkExteriorPlanarNeckGridEndpoint m => z.1) he'
    have heEnd : e'.2 = e :=
      congrArg
        (fun z : CoordinateUnlinkExteriorPlanarNeckGridEndpoint m => z.2) he'
    refine ⟨e', ?_⟩
    rw [coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter_apply]
    apply Prod.ext
    · exact heLabel
    · rw [← (congrArg Prod.snd hvw), ← heOuter]
      exact congrArg coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc
        heEnd

/-- Once a top-left point avoids the vertical center, varying only its ball coordinate
continues to avoid the vertical center. -/
theorem coordinateUnlinkExteriorPlanarNeckGrid_topLeft_not_mem_verticalCenterRange
    (m : ℕ) [NeZero m]
    (w : CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m)
    (b₀ b : EuclideanClosedBall 3)
    (h₀ :
      topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
          (w, b₀) ∉
        range
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft) :
    topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
        (w, b) ∉
      range
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft := by
  intro hb
  exact h₀ <|
    neckGrid_topLeft_mem_verticalCenterRange_of_endpoint m w b₀ <|
      neckGrid_endpoint_of_topLeft_mem_verticalCenterRange m w b hb

private def coordinateUnlinkExteriorPlanarNeckStarLeftClosedTimeMap
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1) (s : Sphere 2) :
    C(Set.Icc (0 : ℝ) 1, CoordinateUnlinkExteriorPlanarNeckStar m) where
  toFun t :=
    coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m a u t s
  continuous_toFun := by
    have hx : Continuous
        (fun t : Set.Icc (0 : ℝ) 1 => ((a, (u, t)), s)) :=
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
        m a u t s).symm

private def coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint
    (m : ℕ) [NeZero m]
    (w : CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m)
    (b : EuclideanClosedBall 3) :
    CoordinateUnlinkExteriorPlanarNeckStar m :=
  topologicalPushoutInl
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
      (topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
        (w, b)))

private def coordinateUnlinkExteriorPlanarNeckStarTopLeftBallMap
    (m : ℕ) [NeZero m]
    (w : CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m) :
    C(EuclideanClosedBall 3, CoordinateUnlinkExteriorPlanarNeckStar m) where
  toFun b := coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint m w b
  continuous_toFun := by
    exact
      (topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)).continuous.comp <|
      (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement
        m).continuous.comp <|
      (topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
        (coordinateUnlinkExteriorPlanarNeckGridDiagram
          m).leftToBottomLeft).continuous.comp <|
      continuous_const.prodMk continuous_id

private theorem coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint_eq_oneHandle
    (m : ℕ) [NeZero m]
    (w : CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint m w b =
      coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
        (partialSphereSpinInl
          (coordinateUnlinkExteriorPlanarFlowerOuter m)
          (coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m w, b)) := by
  rw [coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint,
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar,
    Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarNeckGridRegrouping_topLeft_apply]
  unfold TopologicalPushoutGridDiagram.columnFirstTopLeft
  rw [ContinuousMap.comp_apply,
    coordinateUnlinkExteriorPlanarNeckGridColumnFirstHomeomorphStar_inl]

private theorem coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint_mem_strictCore
    (m : ℕ) [NeZero m]
    (w : CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint m w b ∈
      coordinateUnlinkExteriorPlanarNeckStarStrictCore m := by
  rw [coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint_eq_oneHandle]
  exact coordinateUnlinkExteriorPlanarNeckStar_oneHandle_mem_strictCore m
    (coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m w, b)

private theorem coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint_boundary
    (m : ℕ) [NeZero m]
    (w : CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m)
    (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint m w
        (coordinateUnlinkExteriorPlanarNeckGridSphereToBall s) =
      coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m w.1
        (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap w.2) 1 s := by
  rw [coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint,
    coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_eq_grid]
  apply congrArg
    (fun q : (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalLeft =>
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)
        (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m q))
  simpa only [
    coordinateUnlinkExteriorPlanarNeckGridDiagram_leftToTopLeft_apply,
    coordinateUnlinkExteriorPlanarNeckGridLeftToTopLeft_apply,
    coordinateUnlinkExteriorPlanarNeckGridDiagram_leftToBottomLeft_apply,
    coordinateUnlinkExteriorPlanarNeckGridLeftToBottomLeft_apply,
    coordinateUnlinkExteriorPlanarNeckGridLeftOuterToNormalizedLeft_apply,
    partialSphereSpinAnnulusOne_apply] using
      topologicalPushout_condition
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
        (w, s)

/-- Every positive-time normalized left point that is still off the selected seam can be
joined inside the strict selected side to the open-annulus carrier. -/
theorem coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_accesses_interiorCarrier
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2)
    (ht : 0 < (t : ℝ))
    (hleaf : coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m a u t s ∈
      coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a) :
    ∃ y : Sphere 1 × (Set.Ioo (0 : ℝ) 1 × Sphere 2),
      JoinedIn
        (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
          coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a)
        (coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m a u t s)
        (coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier m a y) := by
  have hhalfPos : 0 < (t : ℝ) / 2 := by linarith
  have hhalfLe : (t : ℝ) / 2 ≤ (t : ℝ) := by linarith
  have hhalfLtOne : (t : ℝ) / 2 < 1 := by linarith [t.2.2]
  let thalf : Set.Ioo (0 : ℝ) 1 := ⟨(t : ℝ) / 2, hhalfPos, hhalfLtOne⟩
  let toClosed :
      C(Set.Icc ((t : ℝ) / 2) (t : ℝ), Set.Icc (0 : ℝ) 1) :=
    { toFun := fun r => ⟨r.1, le_trans (le_of_lt hhalfPos) r.2.1,
        le_trans r.2.2 t.2.2⟩
      continuous_toFun := continuous_subtype_val.subtype_mk _ }
  let lineMap :
      C(Set.Icc ((t : ℝ) / 2) (t : ℝ),
        CoordinateUnlinkExteriorPlanarNeckStar m) :=
    (coordinateUnlinkExteriorPlanarNeckStarLeftClosedTimeMap m a u s).comp toClosed
  let _ : PathConnectedSpace (Set.Icc ((t : ℝ) / 2) (t : ℝ)) :=
    isPathConnected_iff_pathConnectedSpace.mp <|
      (convex_Icc ((t : ℝ) / 2) (t : ℝ)).isPathConnected
        ⟨(t : ℝ) / 2, le_rfl, hhalfLe⟩
  have hrange : range lineMap ⊆
      coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a := by
    rintro _ ⟨r, rfl⟩
    have hrPos : 0 < (toClosed r : ℝ) :=
      hhalfPos.trans_le r.2.1
    constructor
    · exact
        (coordinateUnlinkExteriorPlanarNeckStar_normalizedLeft_mem_strictCore_iff
          m a u (toClosed r) s).mpr hrPos
    · by_cases hrLt : (toClosed r : ℝ) < 1
      · exact coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_mem_leaf
          m a u (toClosed r) s hrLt
      · have hrOne : (toClosed r : ℝ) = 1 :=
          le_antisymm (toClosed r).2.2 (le_of_not_gt hrLt)
        change (r : ℝ) = 1 at hrOne
        have htOne : (t : ℝ) = 1 :=
          le_antisymm t.2.2 <| by linarith [r.2.2]
        have hrt : toClosed r = t := by
          apply Subtype.ext
          exact hrOne.trans htOne.symm
        change coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint
          m a u (toClosed r) s ∈
            coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a
        rw [hrt]
        exact hleaf
  let lo : Set.Icc ((t : ℝ) / 2) (t : ℝ) :=
    ⟨(t : ℝ) / 2, le_rfl, hhalfLe⟩
  let hi : Set.Icc ((t : ℝ) / 2) (t : ℝ) :=
    ⟨(t : ℝ), hhalfLe, le_rfl⟩
  have hjoin : JoinedIn
      (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a)
      (lineMap hi) (lineMap lo) :=
    (isPathConnected_range lineMap.continuous).joinedIn
        _ ⟨hi, rfl⟩ _ ⟨lo, rfl⟩ |>.mono hrange
  have hhi : lineMap hi =
      coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m a u t s := by
    apply congrArg
      (coordinateUnlinkExteriorPlanarNeckStarLeftClosedTimeMap m a u s)
    apply Subtype.ext
    rfl
  have hlo : lineMap lo =
      coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier m a
        (u, (thalf, s)) := by
    apply congrArg
      (coordinateUnlinkExteriorPlanarNeckStarLeftClosedTimeMap m a u s)
    apply Subtype.ext
    rfl
  exact ⟨(u, (thalf, s)), hhi ▸ hlo ▸ hjoin⟩

private theorem coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint_joinedIn_boundary
    (m : ℕ) [NeZero m] (a : ZMod m)
    (w : CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m)
    (b : EuclideanClosedBall 3) (s : Sphere 2)
    (hlabel :
      coordinateUnlinkExteriorPlanarNeckStarLeftLabel m
        (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
          (topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
            (w, b))) = a)
    (hnot :
      coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
          (topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
            (w, b)) ∉
        range (coordinateUnlinkExteriorPlanarNeckStarToLeft m)) :
    JoinedIn
      (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a)
      (coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint m w b)
      (coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint m w
        (coordinateUnlinkExteriorPlanarNeckGridSphereToBall s)) := by
  have hwLabel : w.1 = a := by
    rw [coordinateUnlinkExteriorPlanarNeckGrid_topLeft_complement_label] at hlabel
    exact hlabel
  let _ : PathConnectedSpace (EuclideanClosedBall 3) :=
    pathConnectedSpace_iff_univ.mpr (isPathConnected_euclideanClosedBall 3)
  have hpath :=
    (isPathConnected_range
      (coordinateUnlinkExteriorPlanarNeckStarTopLeftBallMap m w).continuous).joinedIn
        _ ⟨b, rfl⟩ _
        ⟨coordinateUnlinkExteriorPlanarNeckGridSphereToBall s, rfl⟩
  refine hpath.mono ?_
  rintro _ ⟨b', rfl⟩
  constructor
  · exact coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint_mem_strictCore m w b'
  · change topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)
        (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
          (topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
            (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
            (w, b'))) ∈
      topologicalPushoutInlFiberOffSeam
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)
        (coordinateUnlinkExteriorPlanarNeckStarLeftLabel m) a
    refine ⟨_, ⟨?_, ?_⟩, rfl⟩
    · rw [coordinateUnlinkExteriorPlanarNeckGrid_topLeft_complement_label,
        hwLabel]
    · apply
        (neckGridVerticalLeftHomeomorphComplement_not_range_iff m _).mpr
      apply coordinateUnlinkExteriorPlanarNeckGrid_topLeft_not_mem_verticalCenterRange
        m w b b'
      exact (neckGridVerticalLeftHomeomorphComplement_not_range_iff m _).mp hnot

/-- Every point of the exact strict selected left side can be joined inside that side to a
point of the normalized open-annulus carrier. -/
theorem coordinateUnlinkExteriorPlanarNeckStarStrictLeftSide_accesses_interiorCarrier
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarNeckStar m)
    (hx : x ∈ coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
      coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a) :
    ∃ y : Sphere 1 × (Set.Ioo (0 : ℝ) 1 × Sphere 2),
      JoinedIn
        (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
          coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a)
        x (coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier m a y) := by
  rcases hx with ⟨hstrict, ⟨z, hz, rfl⟩⟩
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  let H := coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
  rcases topologicalPushout_jointly_surjective D.leftToTopLeft D.leftToBottomLeft
      (H.symm z) with ⟨p, hp⟩ | ⟨p, hp⟩
  · rcases p with ⟨w, b⟩
    have hgrid : H
        (topologicalPushoutInl D.leftToTopLeft D.leftToBottomLeft (w, b)) = z := by
      rw [hp, H.apply_symm_apply]
    subst z
    dsimp only [D, H] at hz hstrict
    let s₀ : Sphere 2 := coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint
    have htop :=
      coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint_joinedIn_boundary
        m a w b s₀ hz.1 hz.2
    have hwLabel : w.1 = a := by
      have h := hz.1
      rw [coordinateUnlinkExteriorPlanarNeckGrid_topLeft_complement_label] at h
      exact h
    rw [coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint_boundary,
      hwLabel] at htop
    obtain ⟨y, hy⟩ :=
      coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_accesses_interiorCarrier
        m a (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap w.2) 1 s₀
          (by norm_num) htop.target_mem.2
    refine ⟨y, ?_⟩
    simpa [coordinateUnlinkExteriorPlanarNeckStarTopLeftPoint] using htop.trans hy
  · rcases p with ⟨⟨b, ⟨u, t⟩⟩, s⟩
    have hgrid : H
        (topologicalPushoutInr D.leftToTopLeft D.leftToBottomLeft
          ((b, (u, t)), s)) = z := by
      rw [hp, H.apply_symm_apply]
    subst z
    dsimp only [D, H] at hz hstrict
    have hpoint :=
      coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_eq_grid
        m b u t s
    have hb : b = a := by
      have h := hz.1
      rw [coordinateUnlinkExteriorPlanarNeckGrid_bottomLeft_complement_label] at h
      exact h
    subst b
    have hstrict' := hstrict
    rw [← hpoint] at hstrict'
    have ht : 0 < (t : ℝ) :=
      (coordinateUnlinkExteriorPlanarNeckStar_normalizedLeft_mem_strictCore_iff
        m a u t s).mp hstrict'
    have hleaf :
        coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m a u t s ∈
          coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a := by
      rw [hpoint]
      exact ⟨_, hz, rfl⟩
    obtain ⟨y, hy⟩ :=
      coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_accesses_interiorCarrier
        m a u t s ht hleaf
    refine ⟨y, ?_⟩
    rw [hpoint] at hy
    exact hy

/-- The exact strict selected left side is path connected. -/
theorem isPathConnected_coordinateUnlinkExteriorPlanarNeckStarStrictLeftSide
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsPathConnected
      (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a) := by
  obtain ⟨x, hx⟩ :=
    (isPathConnected_range_coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier
      m a).nonempty
  rcases hx with ⟨u, rfl⟩
  refine
    ⟨coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier m a u,
      range_coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier_subset
        m a ⟨u, rfl⟩, ?_⟩
  intro y hy
  obtain ⟨v, hv⟩ :=
    coordinateUnlinkExteriorPlanarNeckStarStrictLeftSide_accesses_interiorCarrier
      m a y hy
  exact
    (coordinateUnlinkExteriorPlanarNeckStarLeftInteriorCarrier_joinedIn
      m a u v).trans hv.symm

/-- The exact strict selected left side is preconnected. -/
theorem isPreconnected_coordinateUnlinkExteriorPlanarNeckStarStrictLeftSide
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsPreconnected
      (coordinateUnlinkExteriorPlanarNeckStarStrictCore m ∩
        coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a) :=
  (isPathConnected_coordinateUnlinkExteriorPlanarNeckStarStrictLeftSide
    m a).isConnected.isPreconnected

end SplittingSpheres
