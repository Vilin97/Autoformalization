/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarOuterParameterSplit
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarOuterSector
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckNormalizedPushout
public import SplittingSpheres.Handlebody.PartialSphereSpinAnnulusReverse

/-!
# The boundary circle of a normalized left leaf

For a fixed sheet label, the outer boundary of the corresponding normalized left annulus is
the union of two closed arcs.  One is the retained round outer arc; the other is the lifted
vertical neck seam.  They meet exactly at the two points `S⁰` and together cover the literal
`t = 1` boundary circle of `PartialSphereSpinAnnulus`.

This file recognizes that circle as the corresponding topological pushout.  It also distributes
the construction over the product with the literal closed three-ball, giving an exact split of
`OneHandlePiece = S¹ × B³`.  All maps are tied back to the existing normalized left-half and
labelled-sector maps.  No order, separation, manifold, smoothness, or connected-sum assertion is
made.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped Topology

namespace SplittingSpheres

/-! ## The two arcs in the literal `t = 1` circle -/

/-- Extract the circle coordinate of the retained round outer arc under the literal-annulus
normal form of the downstairs left half. -/
def coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap :
    C(CoordinateUnlinkExteriorPlanarBaseLeftOuterArc, Sphere 1) where
  toFun w :=
    (coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.symm w.1).1
  continuous_toFun :=
    ((coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.symm.continuous.comp
      continuous_subtype_val).fst)

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap_apply
    (w : CoordinateUnlinkExteriorPlanarBaseLeftOuterArc) :
    coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap w =
      (coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.symm w.1).1 :=
  rfl

/-- Extract the circle coordinate of the fixed-label normalized neck seam. -/
def coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    C(CoordinateUnlinkExteriorPlanarNeckInterval, Sphere 1) where
  toFun t := (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m (a, t)).2.1
  continuous_toFun := by
    have ha : Continuous (fun _ : CoordinateUnlinkExteriorPlanarNeckInterval ↦ a) :=
      continuous_const
    have ht : Continuous (fun t : CoordinateUnlinkExteriorPlanarNeckInterval ↦ t) :=
      continuous_id
    have h := (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m).continuous.comp
      (ha.prodMk ht)
    exact h.snd.fst

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap_apply
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m a t =
      (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m (a, t)).2.1 :=
  rfl

/-- The retained outer-arc coordinate really lies on the literal `t = 1` annulus boundary. -/
theorem coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap_annulus
    (w : CoordinateUnlinkExteriorPlanarBaseLeftOuterArc) :
    partialSphereSpinAnnulusOne
        (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap w) =
      coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.symm w.1 := by
  have hw : w.1 ∈ coordinateUnlinkExteriorPlanarBaseLeftHalfOuterEndpointSet :=
    Or.inr w.2
  rw [← range_coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_one] at hw
  obtain ⟨u, hu⟩ := hw
  have hinv :
      coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.symm w.1 =
        (u, 1) := by
    rw [← hu,
      coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.symm_apply_apply]
  apply Prod.ext
  · rfl
  · exact (congrArg Prod.snd hinv).symm

/-- The normalized seam coordinate really lies on the same literal `t = 1` annulus boundary. -/
theorem coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap_annulus
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    partialSphereSpinAnnulusOne
        (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m a t) =
      (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m (a, t)).2 := by
  apply Prod.ext
  · rfl
  · exact (coordinateUnlinkExteriorPlanarNormalizedLeftSeam_time m (a, t)).symm

/-- In normalized left-half coordinates, the retained outer arc is literally the selected
labelled sector. -/
theorem coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap_sector
    (m : ℕ) [NeZero m] (a : ZMod m)
    (w : CoordinateUnlinkExteriorPlanarBaseLeftOuterArc) :
    (coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m
      (a, partialSphereSpinAnnulusOne
        (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap w))).1 =
      coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap m a w := by
  rw [coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap_annulus,
    coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph_apply,
    coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.apply_symm_apply]
  rfl

/-- The fixed-label seam, after re-bundling at `t = 1`, is exactly the existing normalized
left seam. -/
theorem coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap_normalized
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (a, partialSphereSpinAnnulusOne
        (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m a t)) =
      coordinateUnlinkExteriorPlanarNormalizedLeftSeam m (a, t) := by
  apply Prod.ext
  · exact (coordinateUnlinkExteriorPlanarNormalizedLeftSeam_fst m (a, t)).symm
  · exact coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap_annulus m a t

/-! ## The common `S⁰` endpoint family -/

/-- Send a product-four-ball end to the corresponding endpoint of the retained outer arc. -/
def coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc :
    C(sphere (0 : EuclideanSpace ℝ (Fin 1)) 1,
      CoordinateUnlinkExteriorPlanarBaseLeftOuterArc) where
  toFun e :=
    ⟨coordinateUnlinkExteriorPlanarNeckBaseArcToBaseLeftHalf
      (productFourEndUnitInterval e), by
        change ‖coordinateUnlinkExteriorPlanarNeckBaseArc
            (productFourEndUnitInterval e) + (1 / 2 : ℂ)‖ = sphereHandleRadius
        rcases productFourEndUnitInterval_eq_zero_or_one e with h | h
        · rw [h, norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_half]
          norm_num
        · rw [h, norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_half]
          norm_num⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_coordinateUnlinkExteriorPlanarNeckBaseArc.comp
      continuous_productFourEndUnitInterval

/-- Send a product-four-ball end to the corresponding endpoint of the neck interval. -/
def coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam :
    C(sphere (0 : EuclideanSpace ℝ (Fin 1)) 1,
      CoordinateUnlinkExteriorPlanarNeckInterval) where
  toFun := productFourEndUnitInterval
  continuous_toFun := continuous_productFourEndUnitInterval

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc_apply
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    (coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc e).1 =
      coordinateUnlinkExteriorPlanarNeckBaseArcToBaseLeftHalf
        (productFourEndUnitInterval e) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam_apply
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam e =
      productFourEndUnitInterval e :=
  rfl

/-- The retained-outer and neck-seam circle coordinates agree at both endpoints. -/
theorem coordinateUnlinkExteriorPlanarLeftLeafBoundary_compatibility
    (m : ℕ) [NeZero m] (a : ZMod m)
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap
        (coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc e) =
      coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m a
        (coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam e) := by
  rw [coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap_apply,
    coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap_apply,
    coordinateUnlinkExteriorPlanarNormalizedLeftSeam_apply]
  rfl

theorem injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam :
    Injective coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam := by
  intro e f hef
  have hball :
      (⟨e.1, sphere_subset_closedBall e.2⟩ : EuclideanClosedBall 1) =
        ⟨f.1, sphere_subset_closedBall f.2⟩ :=
    euclideanClosedBallOneHomeomorphUnitInterval.injective hef
  apply Subtype.ext
  exact congrArg (fun x : EuclideanClosedBall 1 ↦ x.1) hball

theorem injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc :
    Injective coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc := by
  intro e f hef
  apply injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam
  apply injective_coordinateUnlinkExteriorPlanarNeckBaseArc
  exact congrArg (fun w : CoordinateUnlinkExteriorPlanarBaseLeftOuterArc ↦ (w.1 : ℂ)) hef

theorem injective_coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap :
    Injective coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap := by
  intro w v hwv
  apply Subtype.ext
  apply coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.symm.injective
  rw [← coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap_annulus w,
    ← coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap_annulus v, hwv]

theorem injective_coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Injective (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m a) := by
  intro t s hts
  have hnormalized :
      coordinateUnlinkExteriorPlanarNormalizedLeftSeam m (a, t) =
        coordinateUnlinkExteriorPlanarNormalizedLeftSeam m (a, s) := by
    rw [← coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap_normalized m a t,
      ← coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap_normalized m a s, hts]
  exact congrArg Prod.snd
    (injective_coordinateUnlinkExteriorPlanarNormalizedLeftSeam m hnormalized)

/-! ## Exact overlap and coverage -/

/-- A neck parameter on the retained round outer arc is necessarily one of the two endpoints. -/
theorem coordinateUnlinkExteriorPlanarLeftLeafSeam_parameter_eq_endpoint
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval)
    (houter : coordinateUnlinkExteriorPlanarNeckBaseArcToBaseLeftHalf t ∈
      coordinateUnlinkExteriorPlanarBaseLeftOuterArcSet) :
    t = 0 ∨ t = 1 := by
  apply coordinateUnlinkExteriorPlanarNeckArcTranslate_parameter_eq_endpoint_of_outerNorm
    m a t
  rw [coordinateUnlinkExteriorPlanarNeckArcTranslate_pow]
  exact houter

/-- A cross equality between the retained outer arc and the seam comes from one common `S⁰`
endpoint. -/
theorem coordinateUnlinkExteriorPlanarLeftLeafBoundary_cross
    (m : ℕ) [NeZero m] (a : ZMod m)
    (w : CoordinateUnlinkExteriorPlanarBaseLeftOuterArc)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval)
    (hwt : coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap w =
      coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m a t) :
    ∃ e,
      coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc e = w ∧
        coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam e = t := by
  have hannulus :
      coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.symm w.1 =
        (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m (a, t)).2 := by
    rw [← coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap_annulus w,
      ← coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap_annulus m a t, hwt]
  have hbase : w.1 = coordinateUnlinkExteriorPlanarNeckBaseArcToBaseLeftHalf t := by
    rw [coordinateUnlinkExteriorPlanarNormalizedLeftSeam_apply] at hannulus
    exact coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.symm.injective hannulus
  have ht := coordinateUnlinkExteriorPlanarLeftLeafSeam_parameter_eq_endpoint
    m a t (hbase ▸ w.2)
  rcases ht with ht | ht
  · refine ⟨coordinateUnlinkExteriorPlanarNeckLowerEnd, ?_, ?_⟩
    · apply Subtype.ext
      rw [coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc_apply,
        productFourEndUnitInterval_neckLowerEnd, ← ht]
      exact hbase.symm
    · rw [coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam_apply,
        productFourEndUnitInterval_neckLowerEnd, ht]
  · refine ⟨coordinateUnlinkExteriorPlanarNeckUpperEnd, ?_, ?_⟩
    · apply Subtype.ext
      rw [coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc_apply,
        productFourEndUnitInterval_neckUpperEnd, ← ht]
      exact hbase.symm
    · rw [coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam_apply,
        productFourEndUnitInterval_neckUpperEnd, ht]

/-- The retained outer arc and fixed-label seam exhaust the literal annulus boundary circle. -/
theorem coordinateUnlinkExteriorPlanarLeftLeafBoundary_cover
    (m : ℕ) [NeZero m] (a : ZMod m) :
    range coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap ∪
        range (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m a) = univ := by
  apply Set.eq_univ_of_forall
  intro u
  let w : CoordinateUnlinkExteriorPlanarBaseLeftHalf :=
    coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph (u, 1)
  have hwEndpoint : w ∈ coordinateUnlinkExteriorPlanarBaseLeftHalfOuterEndpointSet := by
    rw [← range_coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_one]
    exact ⟨u, rfl⟩
  rcases hwEndpoint with hwSeam | hwOuter
  · right
    let z : CoordinateUnlinkExteriorPlanarFlower m :=
      (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m (a, w)).1
    have hzpow : z.1.1 ^ m = (w : ℂ) := by
      change coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw m (a, w) ^ m =
        (w : ℂ)
      exact coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw_pow m (a, w)
    have hzre : (z.1.1 ^ m).re = -1 / 2 := by
      rw [hzpow]
      exact hwSeam
    let t := coordinateUnlinkExteriorPlanarNeckParameter m z hzre
    refine ⟨t, ?_⟩
    have hbase : coordinateUnlinkExteriorPlanarNeckBaseArc t = (w : ℂ) := by
      rw [coordinateUnlinkExteriorPlanarNeckBaseArc_parameter m z hzre,
        hzpow]
    have hannulus :
        partialSphereSpinAnnulusOne
            (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m a t) =
          (u, 1) := by
      rw [coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap_annulus]
      rw [coordinateUnlinkExteriorPlanarNormalizedLeftSeam_apply]
      apply coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.injective
      rw [coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.apply_symm_apply]
      apply Subtype.ext
      exact hbase
    exact congrArg Prod.fst hannulus
  · left
    let wo : CoordinateUnlinkExteriorPlanarBaseLeftOuterArc := ⟨w, hwOuter⟩
    refine ⟨wo, ?_⟩
    have hannulus :
        partialSphereSpinAnnulusOne
            (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap wo) =
          (u, 1) := by
      rw [coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap_annulus]
      change coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.symm w = (u, 1)
      exact coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.symm_apply_apply _
    exact congrArg Prod.fst hannulus

/-! ## Pushout recognition and the product with `B³` -/

noncomputable instance compactSpace_coordinateUnlinkExteriorPlanarBaseLeftOuterArc :
    CompactSpace CoordinateUnlinkExteriorPlanarBaseLeftOuterArc := by
  let _ : CompactSpace CoordinateUnlinkExteriorPlanarBaseLeftHalf :=
    coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.compactSpace
  exact isCompact_iff_compactSpace.mp
    isClosed_coordinateUnlinkExteriorPlanarBaseLeftOuterArcSet.isCompact

/-- The abstract boundary pushout for one normalized left leaf. -/
abbrev CoordinateUnlinkExteriorPlanarLeftLeafBoundaryPushout : Type :=
  TopologicalPushout
    coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc
    coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam

/-- The two exact closed arcs recover the literal annulus boundary circle. -/
def coordinateUnlinkExteriorPlanarLeftLeafBoundaryPushoutHomeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) :
    CoordinateUnlinkExteriorPlanarLeftLeafBoundaryPushout ≃ₜ Sphere 1 :=
  topologicalPushoutHomeomorph
    coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc
    coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam
    coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap
    (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m a)
    (coordinateUnlinkExteriorPlanarLeftLeafBoundary_compatibility m a)
    injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc
    injective_coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap
    (injective_coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m a)
    (coordinateUnlinkExteriorPlanarLeftLeafBoundary_cross m a)
    (coordinateUnlinkExteriorPlanarLeftLeafBoundary_cover m a)

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafBoundaryPushoutHomeomorph_inl
    (m : ℕ) [NeZero m] (a : ZMod m)
    (w : CoordinateUnlinkExteriorPlanarBaseLeftOuterArc) :
    coordinateUnlinkExteriorPlanarLeftLeafBoundaryPushoutHomeomorph m a
        (topologicalPushoutInl
          coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc
          coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam w) =
      coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap w :=
  topologicalPushoutHomeomorph_inl _ _ _ _ _ _ _ _ _ _ w

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafBoundaryPushoutHomeomorph_inr
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarLeftLeafBoundaryPushoutHomeomorph m a
        (topologicalPushoutInr
          coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc
          coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam t) =
      coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m a t :=
  topologicalPushoutHomeomorph_inr _ _ _ _ _ _ _ _ _ _ t

/-- Product of the left-leaf boundary pushout with the literal closed three-ball. -/
abbrev CoordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushout : Type :=
  TopologicalPushout
    (coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc.prodMap
      (ContinuousMap.id (EuclideanClosedBall 3)))
    (coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam.prodMap
      (ContinuousMap.id (EuclideanClosedBall 3)))

/-- The product boundary split is exactly the compact one-handle `S¹ × B³`. -/
def coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) :
    CoordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushout ≃ₜ
      OneHandlePiece := by
  let _ : T2Space CoordinateUnlinkExteriorPlanarLeftLeafBoundaryPushout :=
    (coordinateUnlinkExteriorPlanarLeftLeafBoundaryPushoutHomeomorph m a).symm.t2Space
  exact
    (topologicalPushoutProductHomeomorph
      coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc
      coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam
      (EuclideanClosedBall 3)
      injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc
      injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam).trans
      ((coordinateUnlinkExteriorPlanarLeftLeafBoundaryPushoutHomeomorph m a).prodCongr
        (Homeomorph.refl (EuclideanClosedBall 3)))

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph_inl
    (m : ℕ) [NeZero m] (a : ZMod m)
    (w : CoordinateUnlinkExteriorPlanarBaseLeftOuterArc)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph m a
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc.prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          (coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam.prodMap
            (ContinuousMap.id (EuclideanClosedBall 3))) (w, b)) =
      (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap w, b) := by
  rw [coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph,
    Homeomorph.trans_apply, topologicalPushoutProductHomeomorph_inl]
  exact Prod.ext
    (coordinateUnlinkExteriorPlanarLeftLeafBoundaryPushoutHomeomorph_inl m a w) rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph_inr
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph m a
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc.prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          (coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam.prodMap
            (ContinuousMap.id (EuclideanClosedBall 3))) (t, b)) =
      (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m a t, b) := by
  rw [coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph,
    Homeomorph.trans_apply, topologicalPushoutProductHomeomorph_inr]
  exact Prod.ext
    (coordinateUnlinkExteriorPlanarLeftLeafBoundaryPushoutHomeomorph_inr m a t) rfl

end SplittingSpheres
