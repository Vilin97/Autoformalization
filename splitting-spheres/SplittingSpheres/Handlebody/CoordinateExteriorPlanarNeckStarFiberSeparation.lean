/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutFiberSeparation
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckStarSeparation

/-!
# Separation by one labelled sphere in the neck star

The left target of the literal neck star is a subtype of
`ZMod m × OneHandlePiece`.  Its first coordinate is therefore a continuous label map.
This file proves that the left attaching map preserves that literal label and specializes
the generic fiber-separation API to one selected `Sphere 3`.

The resulting statements are point-set separation statements.  In particular, the two
displayed sides are open, disjoint, and cover the complement of the selected sphere, and
points on opposite sides lie in distinct relative connected components.  No assertion that
either displayed side is itself connected is made.
-/

@[expose] public section

noncomputable section

open Function Set Topology
open Set.Notation

namespace SplittingSpheres

/-! ## The literal left label -/

/-- The label of a point of the displayed left complement is its literal first coordinate
in `ZMod m × OneHandlePiece`. -/
def coordinateUnlinkExteriorPlanarNeckStarLeftLabel
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckLeftComplement m, ZMod m) where
  toFun x := x.1.1
  continuous_toFun := continuous_fst.comp continuous_subtype_val

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckStarLeftLabel_apply
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckLeftComplement m) :
    coordinateUnlinkExteriorPlanarNeckStarLeftLabel m x = x.1.1 :=
  rfl

private def neckGridTopLeftLabel
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckGridHL m, ZMod m) :=
  ⟨fun x => x.1.1, continuous_fst.comp continuous_fst⟩

private def neckGridBottomLeftLabel
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckGridFL m, ZMod m) :=
  ⟨fun x => x.1.1, continuous_fst.comp continuous_fst⟩

private def neckGridVerticalLeftLabel
    (m : ℕ) [NeZero m] :
    C((coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalLeft, ZMod m) :=
  topologicalPushoutDesc
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
    (neckGridTopLeftLabel m) (neckGridBottomLeftLabel m) (fun _ => rfl)

@[simp]
private theorem neckGridVerticalLeftLabel_inl
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridHL m) :
    neckGridVerticalLeftLabel m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft x) =
      x.1.1 :=
  topologicalPushoutDesc_inl _ _ _ _ _ x

@[simp]
private theorem neckGridVerticalLeftLabel_inr
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridFL m) :
    neckGridVerticalLeftLabel m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft x) =
      x.1.1 :=
  topologicalPushoutDesc_inr _ _ _ _ _ x

private theorem neckGridVerticalLeftLabel_toLeft
    (m : ℕ) [NeZero m]
    (q : (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenter) :
    neckGridVerticalLeftLabel m
        ((coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft q) =
      (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m q).1 := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  rcases topologicalPushout_jointly_surjective D.centerToTop D.centerToBottom q with
    ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [TopologicalPushoutGridDiagram.verticalCenterToLeft_inl,
      coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_inl,
      neckGridVerticalLeftLabel_inl,
      coordinateUnlinkExteriorPlanarNeckGridDiagram_topToTopLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridTopToTopLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter_apply]
  · rw [TopologicalPushoutGridDiagram.verticalCenterToLeft_inr,
      coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_inr,
      neckGridVerticalLeftLabel_inr,
      coordinateUnlinkExteriorPlanarNeckGridDiagram_bottomToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridBottomToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNormalizedLeftSeam_fst]

private theorem neckGridVerticalLeftHomeomorphComplement_fst
    (m : ℕ) [NeZero m]
    (x : (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalLeft) :
    (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m x).1.1 =
      neckGridVerticalLeftLabel m x := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  rcases topologicalPushout_jointly_surjective D.leftToTopLeft D.leftToBottomLeft x with
    ⟨x, rfl⟩ | ⟨x, rfl⟩
  · have hsymm :
        (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal m).symm
            (topologicalPushoutInl D.leftToTopLeft D.leftToBottomLeft x) =
          topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
              m).leftToTopLeft
            (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
              m).leftToBottomLeft x := by
      apply (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal
        m).injective
      rw [(coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal
          m).apply_symm_apply]
      exact (simLeftVerticalLeftOriginal_inl m x).symm
    rw [coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement,
      Homeomorph.trans_apply, hsymm,
      coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphComplementOneHandles_apply_coe,
      neckGridVerticalLeftLabel_inl]
    change
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle m
        ((coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
          m).columnFirstTopLeft x)).1 = x.1.1
    rw [coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle_topLeft]
  · have hsymm :
        (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal m).symm
            (topologicalPushoutInr D.leftToTopLeft D.leftToBottomLeft x) =
          topologicalPushoutInr
            (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
              m).leftToTopLeft
            (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
              m).leftToBottomLeft x := by
      apply (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal
        m).injective
      rw [(coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal
          m).apply_symm_apply]
      exact (simLeftVerticalLeftOriginal_inr m x).symm
    rw [coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement,
      Homeomorph.trans_apply, hsymm,
      coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphComplementOneHandles_apply_coe,
      neckGridVerticalLeftLabel_inr]
    change
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle m
        ((coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
          m).columnFirstBottomLeft x)).1 = x.1.1
    rw [coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle_bottomLeft]

/-- The left neck-star attaching map preserves the literal `ZMod m` label. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckStarLeftLabel_toLeft
    (m : ℕ) [NeZero m] (x : ZMod m × Sphere 3) :
    coordinateUnlinkExteriorPlanarNeckStarLeftLabel m
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m x) = x.1 := by
  rw [coordinateUnlinkExteriorPlanarNeckStarLeftLabel_apply,
    coordinateUnlinkExteriorPlanarNeckStarToLeft_apply,
    neckGridVerticalLeftHomeomorphComplement_fst,
    neckGridVerticalLeftLabel_toLeft,
    (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph
      m).apply_symm_apply]

/-! ## One-fiber separation -/

/-- The image in the neck star of the selected labelled attaching `Sphere 3`. -/
def coordinateUnlinkExteriorPlanarNeckStarFiberSeam
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Set (CoordinateUnlinkExteriorPlanarNeckStar m) :=
  topologicalPushoutFiberSeam
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m) a

/-- The `a`-labelled left leaf away from the full attaching locus. -/
def coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Set (CoordinateUnlinkExteriorPlanarNeckStar m) :=
  topologicalPushoutInlFiberOffSeam
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (coordinateUnlinkExteriorPlanarNeckStarLeftLabel m) a

/-- The complement of the selected sphere after removing its labelled left off-seam leaf. -/
def coordinateUnlinkExteriorPlanarNeckStarFiberRest
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Set (CoordinateUnlinkExteriorPlanarNeckStar m) :=
  topologicalPushoutFiberRest
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (coordinateUnlinkExteriorPlanarNeckStarLeftLabel m) a

/-- The selected sphere has the literal expected range formula. -/
theorem coordinateUnlinkExteriorPlanarNeckStarFiberSeam_eq_range
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a =
      range (fun s : Sphere 3 ↦
        topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
          (coordinateUnlinkExteriorPlanarNeckStarToRight m)
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m (a, s))) :=
  rfl

/-- The selected labelled left leaf is open in the neck star. -/
theorem isOpen_coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsOpen (coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a) :=
  isOpen_topologicalPushoutInlFiberOffSeam
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (coordinateUnlinkExteriorPlanarNeckStarLeftLabel m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToRight m) a

/-- The remainder after removing the selected sphere is open in the neck star. -/
theorem isOpen_coordinateUnlinkExteriorPlanarNeckStarFiberRest
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsOpen (coordinateUnlinkExteriorPlanarNeckStarFiberRest m a) :=
  isOpen_topologicalPushoutFiberRest
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (coordinateUnlinkExteriorPlanarNeckStarLeftLabel m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (coordinateUnlinkExteriorPlanarNeckStarLeftLabel_toLeft m) a

/-- The two displayed sides are disjoint. -/
theorem disjoint_coordinateUnlinkExteriorPlanarNeckStarFiberSides
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Disjoint (coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a)
      (coordinateUnlinkExteriorPlanarNeckStarFiberRest m a) :=
  disjoint_topologicalPushoutFiberSides
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (coordinateUnlinkExteriorPlanarNeckStarLeftLabel m) a

/-- The two displayed sides cover exactly the complement of the selected sphere. -/
theorem union_coordinateUnlinkExteriorPlanarNeckStarFiberSides
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a ∪
        coordinateUnlinkExteriorPlanarNeckStarFiberRest m a =
      (coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a)ᶜ :=
  union_topologicalPushoutFiberSides
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (coordinateUnlinkExteriorPlanarNeckStarLeftLabel m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToRight m) a

/-- The selected labelled left side is clopen in the complement of its attaching sphere. -/
theorem isClopen_coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam_restrict
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsClopen (((coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a)ᶜ) ↓∩
      coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a) :=
  isClopen_topologicalPushoutInlFiberOffSeam_restrict
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (coordinateUnlinkExteriorPlanarNeckStarLeftLabel m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (coordinateUnlinkExteriorPlanarNeckStarLeftLabel_toLeft m) a

/-- Points on the selected left side and on the remainder lie in distinct relative connected
components after the selected attaching sphere is removed. -/
theorem connectedComponentIn_ne_of_mem_coordinateUnlinkExteriorPlanarNeckStarFiberSides
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x y : CoordinateUnlinkExteriorPlanarNeckStar m)
    (hxSeam : x ∉ coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a)
    (hySeam : y ∉ coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a)
    (hx : x ∈ coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a)
    (hy : y ∈ coordinateUnlinkExteriorPlanarNeckStarFiberRest m a) :
    connectedComponentIn
        (coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a)ᶜ x ≠
      connectedComponentIn
        (coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a)ᶜ y :=
  connectedComponentIn_ne_of_mem_topologicalPushoutFiberSides
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (coordinateUnlinkExteriorPlanarNeckStarLeftLabel m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (coordinateUnlinkExteriorPlanarNeckStarLeftLabel_toLeft m) a
    x y hxSeam hySeam hx hy

/-- The selected attaching sphere is closed in the neck star. -/
theorem isClosed_coordinateUnlinkExteriorPlanarNeckStarFiberSeam
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsClosed (coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a) := by
  rw [← isOpen_compl_iff,
    ← union_coordinateUnlinkExteriorPlanarNeckStarFiberSides]
  exact (isOpen_coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a).union
    (isOpen_coordinateUnlinkExteriorPlanarNeckStarFiberRest m a)

/-! ## Explicit witnesses on both sides -/

private def neckStarSeparationCirclePoint : Sphere 1 :=
  unlinkMeridianCirclePoint 0

private def neckStarSeparationSpherePoint : Sphere 2 :=
  coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint

private def neckGridLeftOffBoundaryPoint
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalLeft :=
  topologicalPushoutInr
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
    ((a, (neckStarSeparationCirclePoint, 0)), neckStarSeparationSpherePoint)

private theorem injective_neckGridLeftToTopLeft
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft := by
  intro x y hxy
  apply Prod.ext
  · exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridHL m => z.1) hxy
  · apply Subtype.ext
    exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridHL m => z.2.1) hxy

private theorem neckGridLeftOffBoundaryPoint_not_range
    (m : ℕ) [NeZero m] (a : ZMod m) :
    neckGridLeftOffBoundaryPoint m a ∉
      range (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  rintro ⟨q, hq⟩
  rcases topologicalPushout_jointly_surjective D.centerToTop D.centerToBottom q with
    ⟨e, rfl⟩ | ⟨x, rfl⟩
  · rw [TopologicalPushoutGridDiagram.verticalCenterToLeft_inl] at hq
    obtain ⟨b, _hbTop, hbBottom⟩ :=
      (topologicalPushoutInl_eq_inr_iff D.leftToTopLeft D.leftToBottomLeft
        (injective_neckGridLeftToTopLeft m) (D.topToTopLeft e)
        ((a, (neckStarSeparationCirclePoint, 0)),
          neckStarSeparationSpherePoint)).mp hq
    have htime := congrArg
      (fun z : CoordinateUnlinkExteriorPlanarNeckGridFL m => z.1.2.2) hbBottom
    rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_leftToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridLeftToBottomLeft_apply] at htime
    exact zero_ne_one htime.symm
  · rw [TopologicalPushoutGridDiagram.verticalCenterToLeft_inr] at hq
    have hbottom := topologicalPushoutInr_injective
      D.leftToTopLeft D.leftToBottomLeft
      (injective_neckGridLeftToTopLeft m) hq
    have htime := congrArg
      (fun z : CoordinateUnlinkExteriorPlanarNeckGridFL m => z.1.2.2) hbottom
    rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_bottomToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridBottomToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNormalizedLeftSeam_time] at htime
    exact one_ne_zero htime

private def neckStarLeftOffBoundaryPoint
    (m : ℕ) [NeZero m] (a : ZMod m) :
    CoordinateUnlinkExteriorPlanarNeckLeftComplement m :=
  coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
    (neckGridLeftOffBoundaryPoint m a)

private theorem neckStarLeftOffBoundaryPoint_label
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarNeckStarLeftLabel m
        (neckStarLeftOffBoundaryPoint m a) = a := by
  rw [coordinateUnlinkExteriorPlanarNeckStarLeftLabel_apply,
    neckStarLeftOffBoundaryPoint,
    neckGridVerticalLeftHomeomorphComplement_fst,
    neckGridLeftOffBoundaryPoint, neckGridVerticalLeftLabel_inr]

private theorem neckStarLeftOffBoundaryPoint_not_range
    (m : ℕ) [NeZero m] (a : ZMod m) :
    neckStarLeftOffBoundaryPoint m a ∉
      range (coordinateUnlinkExteriorPlanarNeckStarToLeft m) := by
  rintro ⟨x, hx⟩
  apply neckGridLeftOffBoundaryPoint_not_range m a
  refine ⟨
    (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm x,
    ?_⟩
  apply (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement
    m).injective
  exact hx

/-- Every selected labelled left side is nonempty.  The witness is the `t = 0` point in
the normalized left annulus, whereas the attaching boundary lies at `t = 1`. -/
theorem coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam_nonempty
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a).Nonempty := by
  let x := neckStarLeftOffBoundaryPoint m a
  refine ⟨topologicalPushoutInl
      (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
      (coordinateUnlinkExteriorPlanarNeckStarToRight m) x, ?_⟩
  exact ⟨x, ⟨neckStarLeftOffBoundaryPoint_label m a,
    neckStarLeftOffBoundaryPoint_not_range m a⟩, rfl⟩

private def neckGridRightOffBoundaryPoint
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalRight :=
  topologicalPushoutInr
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight
    ((neckStarSeparationCirclePoint, 0), neckStarSeparationSpherePoint)

private theorem injective_neckGridRightToTopRight
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight := by
  intro x y hxy
  apply Prod.ext
  · exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridHR m => z.1) hxy
  · apply Subtype.ext
    exact congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckGridHR m => z.2.1) hxy

private theorem neckGridRightOffBoundaryPoint_not_range
    (m : ℕ) [NeZero m] :
    neckGridRightOffBoundaryPoint m ∉
      range (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight := by
  let D := coordinateUnlinkExteriorPlanarNeckGridDiagram m
  rintro ⟨q, hq⟩
  rcases topologicalPushout_jointly_surjective D.centerToTop D.centerToBottom q with
    ⟨e, rfl⟩ | ⟨x, rfl⟩
  · rw [TopologicalPushoutGridDiagram.verticalCenterToRight_inl] at hq
    obtain ⟨b, _hbTop, hbBottom⟩ :=
      (topologicalPushoutInl_eq_inr_iff D.rightToTopRight D.rightToBottomRight
        (injective_neckGridRightToTopRight m) (D.topToTopRight e)
        ((neckStarSeparationCirclePoint, 0), neckStarSeparationSpherePoint)).mp hq
    have htime := congrArg
      (fun z : CoordinateUnlinkExteriorPlanarNeckGridFR => z.1.2) hbBottom
    rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_rightToBottomRight_apply,
      coordinateUnlinkExteriorPlanarNeckGridRightToBottomRight_apply] at htime
    exact zero_ne_one htime.symm
  · rw [TopologicalPushoutGridDiagram.verticalCenterToRight_inr] at hq
    have hbottom := topologicalPushoutInr_injective
      D.rightToTopRight D.rightToBottomRight
      (injective_neckGridRightToTopRight m) hq
    have htime := congrArg
      (fun z : CoordinateUnlinkExteriorPlanarNeckGridFR => z.1.2) hbottom
    rw [coordinateUnlinkExteriorPlanarNeckGridDiagram_bottomToBottomRight_apply,
      coordinateUnlinkExteriorPlanarNeckGridBottomToBottomRight_apply,
      coordinateUnlinkExteriorPlanarNormalizedRightSeam_time] at htime
    exact one_ne_zero htime

private def neckStarRightOffBoundaryPoint
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNeckRightComplement m :=
  coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m
    (neckGridRightOffBoundaryPoint m)

private theorem neckStarRightOffBoundaryPoint_not_range
    (m : ℕ) [NeZero m] :
    neckStarRightOffBoundaryPoint m ∉
      range (coordinateUnlinkExteriorPlanarNeckStarToRight m) := by
  rintro ⟨x, hx⟩
  apply neckGridRightOffBoundaryPoint_not_range m
  refine ⟨
    (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm x,
    ?_⟩
  apply (coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement
    m).injective
  exact hx

/-- The remainder after removing any selected labelled sphere is nonempty.  The witness is
a `t = 0` point in the right normalized annulus, away from the full attaching range. -/
theorem coordinateUnlinkExteriorPlanarNeckStarFiberRest_nonempty
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (coordinateUnlinkExteriorPlanarNeckStarFiberRest m a).Nonempty := by
  let f := coordinateUnlinkExteriorPlanarNeckStarToLeft m
  let g := coordinateUnlinkExteriorPlanarNeckStarToRight m
  let y := neckStarRightOffBoundaryPoint m
  let p : CoordinateUnlinkExteriorPlanarNeckStar m :=
    topologicalPushoutInr f g y
  refine ⟨p, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    obtain ⟨z, hzf, hzg⟩ :=
      (topologicalPushoutInl_eq_inr_iff f g
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m).injective
        (f (a, s)) y).mp hs
    have hz : z = (a, s) :=
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m).injective hzf
    exact neckStarRightOffBoundaryPoint_not_range m ⟨z, hz ▸ hzg⟩
  · rintro ⟨x, hx, hxp⟩
    obtain ⟨z, hzf, _hzg⟩ :=
      (topologicalPushoutInl_eq_inr_iff f g
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckStarToLeft m).injective
        x y).mp hxp
    exact hx.2 ⟨z, hzf⟩

/-- Removing one selected labelled attaching sphere genuinely disconnects the neck star.
This does not identify either displayed side with a single connected component. -/
theorem not_preconnectedSpace_coordinateUnlinkExteriorPlanarNeckStarFiberComplement
    (m : ℕ) [NeZero m] (a : ZMod m) :
    ¬ PreconnectedSpace
      (↑(coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a)ᶜ) := by
  intro hpre
  let _ : PreconnectedSpace
      (↑(coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a)ᶜ) := hpre
  let leftRestricted :=
    (((coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a)ᶜ) ↓∩
      coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam m a)
  have hleftClopen : IsClopen leftRestricted :=
    isClopen_coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam_restrict m a
  rcases isClopen_iff.mp hleftClopen with hleftEmpty | hleftUniv
  · obtain ⟨x, hx⟩ :=
      coordinateUnlinkExteriorPlanarNeckStarLeftLeafOffSeam_nonempty m a
    have hxComplement :
        x ∈ (coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a)ᶜ := by
      rw [← union_coordinateUnlinkExteriorPlanarNeckStarFiberSides]
      exact Or.inl hx
    let xs : ↑(coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a)ᶜ :=
      ⟨x, hxComplement⟩
    have hxs : xs ∈ leftRestricted := hx
    rw [hleftEmpty] at hxs
    exact hxs
  · obtain ⟨y, hy⟩ :=
      coordinateUnlinkExteriorPlanarNeckStarFiberRest_nonempty m a
    have hyComplement :
        y ∈ (coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a)ᶜ := by
      rw [← union_coordinateUnlinkExteriorPlanarNeckStarFiberSides]
      exact Or.inr hy
    let ys : ↑(coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a)ᶜ :=
      ⟨y, hyComplement⟩
    have hys : ys ∈ leftRestricted := hleftUniv.symm ▸ mem_univ ys
    exact Set.disjoint_left.1
      (disjoint_coordinateUnlinkExteriorPlanarNeckStarFiberSides m a) hys hy

end SplittingSpheres
