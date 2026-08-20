/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarLeftHalfTrivialization
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckSphere

/-!
# Labelled left sectors of the retained planar outer circle

The retained outer circle of the planar flower is the exact polynomial outer-boundary locus.
Over its closed left polynomial half, the existing sheet trivialization separates this locus
into one closed sector for every `ZMod m` label.  This file packages each sector as a genuine
homeomorphic image of the downstairs left outer arc, proves that the labelled sectors are
pairwise disjoint and exhaust precisely the left part of the retained circle, and identifies
their endpoints with the already constructed labelled neck endpoints.

This is deliberately not a cyclic-order theorem.  The polynomial-outer part of the right
annulus still has to be split into its labelled arc components and its endpoint adjacency has
to be proved before one may claim a labelled sectorization of the whole retained circle.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-! ## The retained outer locus and its left base arc -/

/-- The polynomial outer-boundary arc in the closed left base half. -/
def coordinateUnlinkExteriorPlanarBaseLeftOuterArcSet :
    Set CoordinateUnlinkExteriorPlanarBaseLeftHalf :=
  {w | ‖(w : ℂ) + (1 / 2 : ℂ)‖ = sphereHandleRadius}

/-- The literal downstairs left outer arc. -/
abbrev CoordinateUnlinkExteriorPlanarBaseLeftOuterArc : Type :=
  ↑coordinateUnlinkExteriorPlanarBaseLeftOuterArcSet

/-- The retained polynomial outer-boundary locus in the whole flower. -/
def coordinateUnlinkExteriorPlanarRetainedOuterSet
    (m : ℕ) : Set (CoordinateUnlinkExteriorPlanarFlower m) :=
  {z | ‖z.1.1 ^ m + (1 / 2 : ℂ)‖ = sphereHandleRadius}

/-- The part of the retained outer locus lying over the closed left polynomial half. -/
def coordinateUnlinkExteriorPlanarRetainedOuterLeftSet
    (m : ℕ) : Set (CoordinateUnlinkExteriorPlanarFlower m) :=
  coordinateUnlinkExteriorPlanarRetainedOuterSet m ∩
    coordinateUnlinkExteriorPlanarFlowerLeftHalfSet m

/-- The previously constructed retained outer-circle parametrization has exactly the expected
polynomial outer-boundary range. -/
theorem range_coordinateUnlinkExteriorPlanarFlowerOuter
    (m : ℕ) [NeZero m] :
    range (coordinateUnlinkExteriorPlanarFlowerOuter m) =
      coordinateUnlinkExteriorPlanarRetainedOuterSet m := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    have hu :=
      (coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m u).2
    change ‖(coordinateUnlinkExteriorPlanarOuterLift m u).1.2.1 ^ m +
        (1 / 2 : ℂ)‖ = sphereHandleRadius at hu
    change ‖(coordinateUnlinkExteriorPlanarFlowerOuter m u).1.1 ^ m +
        (1 / 2 : ℂ)‖ = sphereHandleRadius
    rw [coordinateUnlinkExteriorPlanarFlowerOuter_val]
    exact hu
  · intro hz
    let w : ↑(coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m) :=
      ⟨z.1.1, hz⟩
    let u :=
      (coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m).symm w
    refine ⟨u, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hu := congrArg Subtype.val <|
      (coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m).apply_symm_apply w
    rw [coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph_coe] at hu
    rw [coordinateUnlinkExteriorPlanarFlowerOuter_val]
    exact hu

/-! ## The labelled sector maps -/

/-- The fixed-label lift of the downstairs left outer arc into the whole flower. -/
def coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    C(CoordinateUnlinkExteriorPlanarBaseLeftOuterArc,
      CoordinateUnlinkExteriorPlanarFlower m) where
  toFun w :=
    (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m (a, w.1)).1
  continuous_toFun :=
    continuous_subtype_val.comp <|
      (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m).continuous.comp
        (continuous_const.prodMk continuous_subtype_val)

/-- The range of the fixed-label left outer sector. -/
def coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorSet
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Set (CoordinateUnlinkExteriorPlanarFlower m) :=
  range (coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap m a)

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap_pow
    (m : ℕ) [NeZero m] (a : ZMod m)
    (w : CoordinateUnlinkExteriorPlanarBaseLeftOuterArc) :
    (coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap m a w).1.1 ^ m =
      (w.1 : ℂ) := by
  change coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw m
    (a, w.1) ^ m = _
  exact coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw_pow m (a, w.1)

theorem injective_coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Injective (coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap m a) := by
  intro w v h
  have hleft :
      coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m (a, w.1) =
        coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m (a, v.1) := by
    apply Subtype.ext
    exact h
  have hp :=
    (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m).injective hleft
  apply Subtype.ext
  exact congrArg Prod.snd hp

theorem isClosed_coordinateUnlinkExteriorPlanarBaseLeftOuterArcSet :
    IsClosed coordinateUnlinkExteriorPlanarBaseLeftOuterArcSet := by
  exact isClosed_eq (by fun_prop) continuous_const

/-- Every labelled left sector is genuinely homeomorphic to the downstairs left outer arc. -/
def coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorHomeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) :
    CoordinateUnlinkExteriorPlanarBaseLeftOuterArc ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorSet m a) := by
  let _ : CompactSpace CoordinateUnlinkExteriorPlanarBaseLeftHalf :=
    coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.compactSpace
  let _ : CompactSpace CoordinateUnlinkExteriorPlanarBaseLeftOuterArc :=
    isCompact_iff_compactSpace.mp
      isClosed_coordinateUnlinkExteriorPlanarBaseLeftOuterArcSet.isCompact
  exact
    ((coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap m a).continuous.isClosedEmbedding
      (injective_coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap m a)).isEmbedding
        |>.toHomeomorph

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorHomeomorph_apply_coe
    (m : ℕ) [NeZero m] (a : ZMod m)
    (w : CoordinateUnlinkExteriorPlanarBaseLeftOuterArc) :
    (coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorHomeomorph m a w :
        CoordinateUnlinkExteriorPlanarFlower m) =
      coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap m a w :=
  rfl

/-! ## Disjointness and exact left-side coverage -/

/-- Distinct sheet labels give disjoint closed left sectors, including their endpoints. -/
theorem pairwise_disjoint_coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorSet
    (m : ℕ) [NeZero m] :
    Pairwise fun a b : ZMod m ↦
      Disjoint (coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorSet m a)
        (coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorSet m b) := by
  intro a b hab
  rw [Set.disjoint_left]
  rintro z ⟨w, rfl⟩ ⟨v, hv⟩
  apply hab
  have hleft :
      coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m (a, w.1) =
        coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m (b, v.1) := by
    apply Subtype.ext
    exact hv.symm
  exact congrArg Prod.fst <|
    (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m).injective hleft

/-- The labelled left sectors exhaust exactly the left part of the retained outer circle. -/
theorem iUnion_coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorSet
    (m : ℕ) [NeZero m] :
    (⋃ a : ZMod m, coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorSet m a) =
      coordinateUnlinkExteriorPlanarRetainedOuterLeftSet m := by
  ext z
  constructor
  · intro hz
    rw [mem_iUnion] at hz
    obtain ⟨a, w, hw⟩ := hz
    subst z
    constructor
    · change ‖(coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap m a w).1.1 ^ m +
          (1 / 2 : ℂ)‖ = sphereHandleRadius
      rw [coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap_pow]
      exact w.2
    · exact
        (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m (a, w.1)).2
  · rintro ⟨hzouter, hzleft⟩
    let zl : CoordinateUnlinkExteriorPlanarFlowerLeftHalf m := ⟨z, hzleft⟩
    let x := (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m).symm zl
    have hx : coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m x = zl :=
      (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m).apply_symm_apply zl
    have hxpow : (x.2 : ℂ) = z.1.1 ^ m := by
      rw [← coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw_pow m x]
      exact congrArg
        (fun q : CoordinateUnlinkExteriorPlanarFlowerLeftHalf m ↦ q.1.1.1 ^ m) hx
    let w : CoordinateUnlinkExteriorPlanarBaseLeftOuterArc := ⟨x.2, by
      change ‖(x.2 : ℂ) + (1 / 2 : ℂ)‖ = sphereHandleRadius
      rw [hxpow]
      exact hzouter⟩
    rw [mem_iUnion]
    refine ⟨x.1, w, ?_⟩
    change
      (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m
          (x.1, w.1)).1 = z
    have hxpair : (x.1, w.1) = x := Prod.ext rfl rfl
    rw [hxpair, hx]

/-! ## Literal neck endpoints -/

/-- The lower endpoint of the downstairs left outer arc. -/
def coordinateUnlinkExteriorPlanarBaseLeftOuterArcLower :
    CoordinateUnlinkExteriorPlanarBaseLeftOuterArc :=
  ⟨coordinateUnlinkExteriorPlanarNeckBaseArcToBaseLeftHalf 0, by
    change ‖coordinateUnlinkExteriorPlanarNeckBaseArc 0 + (1 / 2 : ℂ)‖ =
      sphereHandleRadius
    rw [norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_half]
    norm_num⟩

/-- The upper endpoint of the downstairs left outer arc. -/
def coordinateUnlinkExteriorPlanarBaseLeftOuterArcUpper :
    CoordinateUnlinkExteriorPlanarBaseLeftOuterArc :=
  ⟨coordinateUnlinkExteriorPlanarNeckBaseArcToBaseLeftHalf 1, by
    change ‖coordinateUnlinkExteriorPlanarNeckBaseArc 1 + (1 / 2 : ℂ)‖ =
      sphereHandleRadius
    rw [norm_coordinateUnlinkExteriorPlanarNeckBaseArc_add_half]
    norm_num⟩

/-- The lower endpoint of a labelled left sector is the lower endpoint of the corresponding
labelled neck arc. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap_lower
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap m a
        coordinateUnlinkExteriorPlanarBaseLeftOuterArcLower =
      coordinateUnlinkExteriorPlanarNeckArcTranslate m a 0 := by
  have h := congrArg Subtype.val <|
    coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization_neckArc m a 0
  change
    (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m
      (a, coordinateUnlinkExteriorPlanarNeckBaseArcToBaseLeftHalf 0)).1 = _
  simpa only [coordinateUnlinkExteriorPlanarNeckArcToLeftHalf_val,
    coordinateUnlinkExteriorPlanarNeckArcFamily_apply] using h

/-- The upper endpoint of a labelled left sector is the upper endpoint of the corresponding
labelled neck arc. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap_upper
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap m a
        coordinateUnlinkExteriorPlanarBaseLeftOuterArcUpper =
      coordinateUnlinkExteriorPlanarNeckArcTranslate m a 1 := by
  have h := congrArg Subtype.val <|
    coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization_neckArc m a 1
  change
    (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m
      (a, coordinateUnlinkExteriorPlanarNeckBaseArcToBaseLeftHalf 1)).1 = _
  simpa only [coordinateUnlinkExteriorPlanarNeckArcToLeftHalf_val,
    coordinateUnlinkExteriorPlanarNeckArcFamily_apply] using h

/-! ## Low-degree elaboration checks -/

example :
    (⋃ a : ZMod 1, coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorSet 1 a) =
      coordinateUnlinkExteriorPlanarRetainedOuterLeftSet 1 :=
  iUnion_coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorSet 1

example :
    Disjoint (coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorSet 2 0)
      (coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorSet 2 1) :=
  pairwise_disjoint_coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorSet 2 (by norm_num)

end SplittingSpheres
