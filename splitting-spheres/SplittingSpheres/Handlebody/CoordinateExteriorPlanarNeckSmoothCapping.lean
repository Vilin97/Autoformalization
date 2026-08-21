/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.CollaredTopologicalPushoutManifold
public import SplittingSpheres.Geometry.CoordinateUnlinkSignedSeamSmoothHalves
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Direct smooth capping of the compact planar neck cut

This file glues each compact neck cut side directly to the labelled family
`ZMod m × EuclideanFourBall` along `ZMod m × Sphere 3`.  The pushout atlas is generated
from the direct collared-cut atlas, the direct common-model four-ball atlas, and the signed seam
atlas.  No transported `ProductFourBall` atlas or comparison homeomorphism is used.
-/

@[expose] public section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-- The labelled three-spheres along which a compact cut side is capped. -/
abbrev CoordinateUnlinkExteriorPlanarNeckSmoothCappingAttachingDomain
    (m : ℕ) :=
  ZMod m × Sphere 3

/-- The signed collar used as the seam chart for smooth capping. -/
abbrev CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar
    (m : ℕ) :=
  ZMod m × (Sphere 3 × EquatorCollarInterval)

/-- The radial collar on the labelled direct common-model four-ball family. -/
def coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar
    (m : ℕ) :
    ZMod m × EuclideanFourBallCollarDomain →
      ZMod m × EuclideanFourBall :=
  fun p ↦
    (p.1, coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar p.2)

/-- Attach the labelled direct common-model four-balls at radial collar time zero. -/
def coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap
    (m : ℕ) :
    C(CoordinateUnlinkExteriorPlanarNeckSmoothCappingAttachingDomain m,
      ZMod m × EuclideanFourBall) where
  toFun p := coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m
    (p.1, (p.2, euclideanFourBallCollarZero))
  continuous_toFun := by
    have h := (Topology.IsOpenEmbedding.id :
        IsOpenEmbedding (id : ZMod m → ZMod m)).prodMap
      isOpenEmbedding_euclideanFourBallSmoothCollar
    have hcollar : IsOpenEmbedding
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m) := by
      convert h using 1
      funext p
      apply Prod.ext rfl
      exact
        coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar_apply p.2
    apply hcollar.continuous.comp
    fun_prop

variable (m : ℕ) [NeZero m]

/-- The direct inward collar of the compact left cut side. -/
def coordinateUnlinkExteriorPlanarNeckLeftCutCollar :
    ZMod m × EuclideanFourBallCollarDomain → CompactNeckLeftCut m :=
  collaredCutSideHalfCollarMap
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
    (compactNeckLeftBoundaryCollarMap m)
    (compactNeckLeftBoundaryCollarMap_range_subset m)

/-- Attach the compact left cut side at inward collar time zero. -/
def coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap :
    C(CoordinateUnlinkExteriorPlanarNeckSmoothCappingAttachingDomain m,
      CompactNeckLeftCut m) where
  toFun p := coordinateUnlinkExteriorPlanarNeckLeftCutCollar m
    (p.1, (p.2, euclideanFourBallCollarZero))
  continuous_toFun := by
    apply (isOpenEmbedding_compactNeckLeftBoundaryCollarMap_toCut m).continuous.comp
    fun_prop

/-- The direct inward collar of the compact right cut side. -/
def coordinateUnlinkExteriorPlanarNeckRightCutCollar :
    ZMod m × EuclideanFourBallCollarDomain → CompactNeckRightCut m :=
  collaredCutSideHalfCollarMap
    (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
    (compactNeckRightBoundaryCollarMap m)
    (compactNeckRightBoundaryCollarMap_range_subset m)

/-- Attach the compact right cut side at inward collar time zero. -/
def coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap :
    C(CoordinateUnlinkExteriorPlanarNeckSmoothCappingAttachingDomain m,
      CompactNeckRightCut m) where
  toFun p := coordinateUnlinkExteriorPlanarNeckRightCutCollar m
    (p.1, (p.2, euclideanFourBallCollarZero))
  continuous_toFun := by
    apply (isOpenEmbedding_compactNeckRightBoundaryCollarMap_toCut m).continuous.comp
    fun_prop

/-- The compact left cut capped by a labelled family of direct Euclidean four-balls. -/
abbrev CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping :=
  TopologicalPushout
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)

/-- The compact right cut capped by a labelled family of direct Euclidean four-balls. -/
abbrev CoordinateUnlinkExteriorPlanarNeckRightSmoothCapping :=
  TopologicalPushout
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)

section PointSetCore

variable {X : Type*} [TopologicalSpace X]

private def smoothCappingAttachingMapOfCollar
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : Continuous c) :
    C(CoordinateUnlinkExteriorPlanarNeckSmoothCappingAttachingDomain m, X) where
  toFun p := c (p.1, (p.2, euclideanFourBallCollarZero))
  continuous_toFun := hc.comp (by fun_prop)

private def smoothCappingBranchOfCollar
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) : X :=
  c (signedSeamHalfReparam m p)

omit [NeZero m] in
private theorem injective_smoothCappingAttachingMapOfCollar
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsEmbedding c) :
    Injective (smoothCappingAttachingMapOfCollar m c hc.continuous) := by
  intro p q hpq
  have h := hc.injective hpq
  apply Prod.ext
  · exact congrArg
      (fun z : ZMod m × EuclideanFourBallCollarDomain ↦ z.1) h
  · exact congrArg
      (fun z : ZMod m × EuclideanFourBallCollarDomain ↦ z.2.1) h

private theorem isClosedEmbedding_smoothCappingAttachingMapOfCollar
    [T2Space X]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsEmbedding c) :
    IsClosedEmbedding (smoothCappingAttachingMapOfCollar m c hc.continuous) :=
  (smoothCappingAttachingMapOfCollar m c hc.continuous).continuous.isClosedEmbedding
    (injective_smoothCappingAttachingMapOfCollar m c hc)

omit [NeZero m] in
private theorem smoothCappingBranch_mem_attachingRange_iff
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsEmbedding c)
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :
    smoothCappingBranchOfCollar m c p ∈
        range (smoothCappingAttachingMapOfCollar m c hc.continuous) ↔
      signedSeamTime m p = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    have h := hc.injective hq
    have ht := congrArg
      (fun z : ZMod m × EuclideanFourBallCollarDomain ↦
        (z.2.2.1.1 : ℝ)) h
    change (0 : ℝ) = |(p.2.2.1 : ℝ)| at ht
    exact abs_eq_zero.mp ht.symm
  · intro hp
    refine ⟨(p.1, p.2.1), ?_⟩
    apply congrArg c
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        apply Subtype.ext
        change (0 : ℝ) = |(p.2.2.1 : ℝ)|
        change (p.2.2.1 : ℝ) = 0 at hp
        rw [hp, abs_zero]

omit [NeZero m] in
private theorem smoothCapping_zero_match
    {Y : Type*} [TopologicalSpace Y]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : Continuous c)
    (d : ZMod m × EuclideanFourBallCollarDomain → Y)
    (hd : Continuous d)
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : signedSeamTime m p = 0) :
    ∃ a,
      smoothCappingAttachingMapOfCollar m c hc a =
        smoothCappingBranchOfCollar m c p ∧
      smoothCappingAttachingMapOfCollar m d hd a =
        smoothCappingBranchOfCollar m d p := by
  have hparam : signedSeamHalfReparam m p =
      (p.1, (p.2.1, euclideanFourBallCollarZero)) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        apply Subtype.ext
        change |(p.2.2.1 : ℝ)| = 0
        change (p.2.2.1 : ℝ) = 0 at hp
        rw [hp, abs_zero]
  refine ⟨(p.1, p.2.1), ?_, ?_⟩
  · exact congrArg c hparam.symm
  · exact congrArg d hparam.symm

end PointSetCore

omit [NeZero m] in
/-- The labelled four-ball family collar is an open embedding. -/
theorem isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar :
    IsOpenEmbedding
      (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m) := by
  have h := (Topology.IsOpenEmbedding.id :
      IsOpenEmbedding (id : ZMod m → ZMod m)).prodMap
    isOpenEmbedding_euclideanFourBallSmoothCollar
  convert h using 1
  funext p
  apply Prod.ext rfl
  exact coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar_apply p.2

/-- The compact left cut collar is an open embedding. -/
theorem isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutCollar :
    IsOpenEmbedding (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m) :=
  isOpenEmbedding_compactNeckLeftBoundaryCollarMap_toCut m

/-- The compact right cut collar is an open embedding. -/
theorem isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutCollar :
    IsOpenEmbedding (coordinateUnlinkExteriorPlanarNeckRightCutCollar m) :=
  isOpenEmbedding_compactNeckRightBoundaryCollarMap_toCut m

/-- The left attaching map is a closed embedding. -/
theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m) := by
  change IsClosedEmbedding
    (fun p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingAttachingDomain m ↦
      coordinateUnlinkExteriorPlanarNeckLeftCutCollar m
        (p.1, (p.2, euclideanFourBallCollarZero)))
  exact isClosedEmbedding_smoothCappingAttachingMapOfCollar m
    (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutCollar m).isEmbedding

/-- The right attaching map is a closed embedding. -/
theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m) := by
  change IsClosedEmbedding
    (fun p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingAttachingDomain m ↦
      coordinateUnlinkExteriorPlanarNeckRightCutCollar m
        (p.1, (p.2, euclideanFourBallCollarZero)))
  exact isClosedEmbedding_smoothCappingAttachingMapOfCollar m
    (coordinateUnlinkExteriorPlanarNeckRightCutCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutCollar m).isEmbedding

/-- The labelled four-ball attaching map is a closed embedding. -/
theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) := by
  change IsClosedEmbedding
    (fun p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingAttachingDomain m ↦
      coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m
        (p.1, (p.2, euclideanFourBallCollarZero)))
  exact isClosedEmbedding_smoothCappingAttachingMapOfCollar m
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m).isEmbedding

private abbrev SmoothCappingNonpositiveHalf (m : ℕ) :=
  {p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m //
    signedSeamTime m p ≤ 0}

private abbrev SmoothCappingNonnegativeHalf (m : ℕ) :=
  {p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m //
    0 ≤ signedSeamTime m p}

private def smoothCappingSignedSeamZero : EquatorCollarInterval :=
  ⟨0, by norm_num [equatorCollarIntervalOpens]⟩

private def smoothCappingInwardToSignedNegative
    (q : ZMod m × EuclideanFourBallCollarDomain) :
    CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m :=
  (q.1, (q.2.1, ⟨-(q.2.2.1.1 : ℝ), by
    constructor
    · have ht : (q.2.2.1.1 : ℝ) < 1 / 2 :=
        (euclideanFourBallCollarInterval_mem_iff q.2.2.1).mp q.2.2.2
      simpa using neg_lt_neg ht
    · linarith [q.2.2.1.2.1]⟩))

private def smoothCappingInwardToSignedPositive
    (q : ZMod m × EuclideanFourBallCollarDomain) :
    CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m :=
  (q.1, (q.2.1, ⟨(q.2.2.1.1 : ℝ), by
    constructor
    · linarith [q.2.2.1.2.1]
    · exact q.2.2.2⟩))

omit [NeZero m] in
private theorem signedSeamHalfReparam_inwardToSignedNegative
    (q : ZMod m × EuclideanFourBallCollarDomain) :
    signedSeamHalfReparam m (smoothCappingInwardToSignedNegative m q) = q := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Subtype.ext
      change |-((q.2.2.1.1 : ℝ))| = (q.2.2.1.1 : ℝ)
      rw [abs_neg, abs_of_nonneg q.2.2.1.2.1]

omit [NeZero m] in
private theorem signedSeamHalfReparam_inwardToSignedPositive
    (q : ZMod m × EuclideanFourBallCollarDomain) :
    signedSeamHalfReparam m (smoothCappingInwardToSignedPositive m q) = q := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Subtype.ext
      change |(q.2.2.1.1 : ℝ)| = (q.2.2.1.1 : ℝ)
      rw [abs_of_nonneg q.2.2.1.2.1]

private def smoothCappingNonpositiveHalfHomeomorph :
    SmoothCappingNonpositiveHalf m ≃ₜ
      (ZMod m × EuclideanFourBallCollarDomain) where
  toFun p := signedSeamHalfReparam m p.1
  invFun q := ⟨smoothCappingInwardToSignedNegative m q,
    neg_nonpos.mpr q.2.2.1.2.1⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        change -|(p.1.2.2.1 : ℝ)| = (p.1.2.2.1 : ℝ)
        have hp : (p.1.2.2.1 : ℝ) ≤ 0 := p.2
        rw [abs_of_nonpos hp, neg_neg]
  right_inv q := signedSeamHalfReparam_inwardToSignedNegative m q
  continuous_toFun :=
    (continuous_signedSeamHalfReparam m).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    unfold smoothCappingInwardToSignedNegative
    fun_prop

private def smoothCappingNonnegativeHalfHomeomorph :
    SmoothCappingNonnegativeHalf m ≃ₜ
      (ZMod m × EuclideanFourBallCollarDomain) where
  toFun p := signedSeamHalfReparam m p.1
  invFun q := ⟨smoothCappingInwardToSignedPositive m q, q.2.2.1.2.1⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        change |(p.1.2.2.1 : ℝ)| = (p.1.2.2.1 : ℝ)
        have hp : 0 ≤ (p.1.2.2.1 : ℝ) := p.2
        rw [abs_of_nonneg hp]
  right_inv q := signedSeamHalfReparam_inwardToSignedPositive m q
  continuous_toFun :=
    (continuous_signedSeamHalfReparam m).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    unfold smoothCappingInwardToSignedPositive
    fun_prop

private def smoothCappingNonpositiveBranch
    {X : Type*}
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (p : SmoothCappingNonpositiveHalf m) : X :=
  smoothCappingBranchOfCollar m c p.1

private def smoothCappingNonnegativeBranch
    {X : Type*}
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (p : SmoothCappingNonnegativeHalf m) : X :=
  smoothCappingBranchOfCollar m c p.1

omit [NeZero m] in
private theorem isOpenEmbedding_smoothCappingNonpositiveBranch
    {X : Type*} [TopologicalSpace X]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c) :
    IsOpenEmbedding (smoothCappingNonpositiveBranch m c) := by
  have h := hc.comp (smoothCappingNonpositiveHalfHomeomorph m).isOpenEmbedding
  exact h

omit [NeZero m] in
private theorem isOpenEmbedding_smoothCappingNonnegativeBranch
    {X : Type*} [TopologicalSpace X]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c) :
    IsOpenEmbedding (smoothCappingNonnegativeBranch m c) := by
  have h := hc.comp (smoothCappingNonnegativeHalfHomeomorph m).isOpenEmbedding
  exact h

private def smoothCappingSeamMapOfCollars
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c)
    (d : ZMod m × EuclideanFourBallCollarDomain → Y)
    (hd : IsOpenEmbedding d) :
    CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m →
      TopologicalPushout
        (smoothCappingAttachingMapOfCollar m c hc.continuous)
        (smoothCappingAttachingMapOfCollar m d hd.continuous) :=
  topologicalPushoutSeamMap
    (smoothCappingAttachingMapOfCollar m c hc.continuous)
    (smoothCappingAttachingMapOfCollar m d hd.continuous)
    (signedSeamTime m)
    (smoothCappingBranchOfCollar m c)
    (smoothCappingBranchOfCollar m d)

omit [NeZero m] in
private theorem continuous_smoothCappingSeamMapOfCollars
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c)
    (d : ZMod m × EuclideanFourBallCollarDomain → Y)
    (hd : IsOpenEmbedding d) :
    Continuous (smoothCappingSeamMapOfCollars m c hc d hd) := by
  apply continuous_topologicalPushoutSeamMap
    (smoothCappingAttachingMapOfCollar m c hc.continuous)
    (smoothCappingAttachingMapOfCollar m d hd.continuous)
    (signedSeamTime m)
    (smoothCappingBranchOfCollar m c)
    (smoothCappingBranchOfCollar m d)
  · unfold signedSeamTime
    fun_prop
  · exact hc.continuous.comp (continuous_signedSeamHalfReparam m)
  · exact hd.continuous.comp (continuous_signedSeamHalfReparam m)
  · intro p hp
    obtain ⟨a, hleft, hright⟩ :=
      smoothCapping_zero_match m c hc.continuous d hd.continuous p hp
    rw [← hleft, ← hright]
    exact topologicalPushout_condition
      (smoothCappingAttachingMapOfCollar m c hc.continuous)
      (smoothCappingAttachingMapOfCollar m d hd.continuous) a

omit [NeZero m] in
private theorem injective_smoothCappingBranch_nonpositive
    {X : Type*} [TopologicalSpace X]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c)
    {p q : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m}
    (hp : signedSeamTime m p ≤ 0) (hq : signedSeamTime m q ≤ 0)
    (hpq : smoothCappingBranchOfCollar m c p =
      smoothCappingBranchOfCollar m c q) : p = q := by
  let p' : SmoothCappingNonpositiveHalf m := ⟨p, hp⟩
  let q' : SmoothCappingNonpositiveHalf m := ⟨q, hq⟩
  have hpq' : smoothCappingNonpositiveBranch m c p' =
      smoothCappingNonpositiveBranch m c q' := hpq
  exact congrArg Subtype.val
    ((isOpenEmbedding_smoothCappingNonpositiveBranch m c hc).injective hpq')

omit [NeZero m] in
private theorem injective_smoothCappingBranch_positive
    {X : Type*} [TopologicalSpace X]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c)
    {p q : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m}
    (hp : 0 < signedSeamTime m p) (hq : 0 < signedSeamTime m q)
    (hpq : smoothCappingBranchOfCollar m c p =
      smoothCappingBranchOfCollar m c q) : p = q := by
  let p' : SmoothCappingNonnegativeHalf m := ⟨p, hp.le⟩
  let q' : SmoothCappingNonnegativeHalf m := ⟨q, hq.le⟩
  have hpq' : smoothCappingNonnegativeBranch m c p' =
      smoothCappingNonnegativeBranch m c q' := hpq
  exact congrArg Subtype.val
    ((isOpenEmbedding_smoothCappingNonnegativeBranch m c hc).injective hpq')

omit [NeZero m] in
private theorem injective_smoothCappingSeamMapOfCollars
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c)
    (d : ZMod m × EuclideanFourBallCollarDomain → Y)
    (hd : IsOpenEmbedding d) :
    Injective (smoothCappingSeamMapOfCollars m c hc d hd) := by
  apply injective_topologicalPushoutSeamMap
    (smoothCappingAttachingMapOfCollar m c hc.continuous)
    (smoothCappingAttachingMapOfCollar m d hd.continuous)
    (signedSeamTime m)
    (smoothCappingBranchOfCollar m c)
    (smoothCappingBranchOfCollar m d)
    (injective_smoothCappingAttachingMapOfCollar m c hc.isEmbedding)
    (injective_smoothCappingAttachingMapOfCollar m d hd.isEmbedding)
  · intro p q hp hq hpq
    exact injective_smoothCappingBranch_nonpositive m c hc hp hq hpq
  · intro p q hp hq hpq
    exact injective_smoothCappingBranch_positive m d hd hp hq hpq
  · intro p hp
    exact (smoothCappingBranch_mem_attachingRange_iff
      m d hd.isEmbedding p).mp hp

private theorem preimage_inl_image_smoothCappingSeamMapOfCollars
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c)
    (d : ZMod m × EuclideanFourBallCollarDomain → Y)
    (hd : IsOpenEmbedding d)
    (U : Set (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)) :
    (topologicalPushoutInl
        (smoothCappingAttachingMapOfCollar m c hc.continuous)
        (smoothCappingAttachingMapOfCollar m d hd.continuous)) ⁻¹'
        (smoothCappingSeamMapOfCollars m c hc d hd '' U) =
      smoothCappingNonpositiveBranch m c ''
        {p : SmoothCappingNonpositiveHalf m | p.1 ∈ U} := by
  let f := smoothCappingAttachingMapOfCollar m c hc.continuous
  let g := smoothCappingAttachingMapOfCollar m d hd.continuous
  ext x
  constructor
  · intro hx
    change topologicalPushoutInl f g x ∈
      smoothCappingSeamMapOfCollars m c hc d hd '' U at hx
    obtain ⟨p, hpU, hp⟩ := hx
    by_cases hpt : signedSeamTime m p ≤ 0
    · refine ⟨⟨p, hpt⟩, hpU, ?_⟩
      apply topologicalPushoutInl_injective f g
        (isClosedEmbedding_smoothCappingAttachingMapOfCollar
          m d hd.isEmbedding).injective
      simpa [f, g, smoothCappingNonpositiveBranch,
        smoothCappingSeamMapOfCollars, topologicalPushoutSeamMap, hpt] using hp
    · have hpos : 0 < signedSeamTime m p := lt_of_not_ge hpt
      have hcross :
          topologicalPushoutInl f g x =
            topologicalPushoutInr f g (smoothCappingBranchOfCollar m d p) := by
        simpa [f, g, smoothCappingSeamMapOfCollars,
          topologicalPushoutSeamMap, hpt] using hp.symm
      obtain ⟨a, _ha, hga⟩ :=
        (topologicalPushoutInl_eq_inr_iff f g
          (isClosedEmbedding_smoothCappingAttachingMapOfCollar
            m c hc.isEmbedding).injective x
          (smoothCappingBranchOfCollar m d p)).mp hcross
      exact False.elim <| (ne_of_gt hpos)
        ((smoothCappingBranch_mem_attachingRange_iff
          m d hd.isEmbedding p).mp ⟨a, hga⟩)
  · rintro ⟨p, hpU, rfl⟩
    change topologicalPushoutInl f g
        (smoothCappingNonpositiveBranch m c p) ∈
      smoothCappingSeamMapOfCollars m c hc d hd '' U
    refine ⟨p.1, hpU, ?_⟩
    simp [f, g, smoothCappingNonpositiveBranch,
      smoothCappingSeamMapOfCollars, topologicalPushoutSeamMap, p.2]

private theorem preimage_inr_image_smoothCappingSeamMapOfCollars
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c)
    (d : ZMod m × EuclideanFourBallCollarDomain → Y)
    (hd : IsOpenEmbedding d)
    (U : Set (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)) :
    (topologicalPushoutInr
        (smoothCappingAttachingMapOfCollar m c hc.continuous)
        (smoothCappingAttachingMapOfCollar m d hd.continuous)) ⁻¹'
        (smoothCappingSeamMapOfCollars m c hc d hd '' U) =
      smoothCappingNonnegativeBranch m d ''
        {p : SmoothCappingNonnegativeHalf m | p.1 ∈ U} := by
  let f := smoothCappingAttachingMapOfCollar m c hc.continuous
  let g := smoothCappingAttachingMapOfCollar m d hd.continuous
  ext y
  constructor
  · intro hy
    change topologicalPushoutInr f g y ∈
      smoothCappingSeamMapOfCollars m c hc d hd '' U at hy
    obtain ⟨p, hpU, hp⟩ := hy
    by_cases hpt : signedSeamTime m p ≤ 0
    · have hcross :
          topologicalPushoutInl f g (smoothCappingBranchOfCollar m c p) =
            topologicalPushoutInr f g y := by
        simpa [f, g, smoothCappingSeamMapOfCollars,
          topologicalPushoutSeamMap, hpt] using hp
      obtain ⟨a, hfa, hga⟩ :=
        (topologicalPushoutInl_eq_inr_iff f g
          (isClosedEmbedding_smoothCappingAttachingMapOfCollar
            m c hc.isEmbedding).injective
          (smoothCappingBranchOfCollar m c p) y).mp hcross
      have htzero : signedSeamTime m p = 0 :=
        (smoothCappingBranch_mem_attachingRange_iff
          m c hc.isEmbedding p).mp ⟨a, hfa⟩
      obtain ⟨b, hfb, hgb⟩ := smoothCapping_zero_match
        m c hc.continuous d hd.continuous p htzero
      refine ⟨⟨p, htzero.ge⟩, hpU, ?_⟩
      change smoothCappingBranchOfCollar m d p = y
      have hab : a = b :=
        (isClosedEmbedding_smoothCappingAttachingMapOfCollar
          m c hc.isEmbedding).injective (hfa.trans hfb.symm)
      rw [← hgb, ← hga, hab]
    · have hpos : 0 < signedSeamTime m p := lt_of_not_ge hpt
      refine ⟨⟨p, hpos.le⟩, hpU, ?_⟩
      apply topologicalPushoutInr_injective f g
        (isClosedEmbedding_smoothCappingAttachingMapOfCollar
          m c hc.isEmbedding).injective
      simpa [f, g, smoothCappingNonnegativeBranch,
        smoothCappingSeamMapOfCollars, topologicalPushoutSeamMap, hpt] using hp
  · rintro ⟨p, hpU, rfl⟩
    change topologicalPushoutInr f g
        (smoothCappingNonnegativeBranch m d p) ∈
      smoothCappingSeamMapOfCollars m c hc d hd '' U
    refine ⟨p.1, hpU, ?_⟩
    rcases p.2.eq_or_lt with hzero | hpos
    · have htzero : signedSeamTime m p.1 = 0 := hzero.symm
      obtain ⟨a, hleft, hright⟩ := smoothCapping_zero_match
        m c hc.continuous d hd.continuous p.1 htzero
      change smoothCappingSeamMapOfCollars m c hc d hd p.1 =
        topologicalPushoutInr f g (smoothCappingBranchOfCollar m d p.1)
      rw [show smoothCappingSeamMapOfCollars m c hc d hd p.1 =
          topologicalPushoutInl f g (smoothCappingBranchOfCollar m c p.1) by
        simp [f, g, smoothCappingSeamMapOfCollars,
          topologicalPushoutSeamMap, htzero]]
      rw [← hleft, ← hright]
      exact topologicalPushout_condition f g a
    · simp [f, g, smoothCappingNonnegativeBranch,
        smoothCappingSeamMapOfCollars, topologicalPushoutSeamMap,
        not_le_of_gt hpos]

private theorem isOpenMap_smoothCappingSeamMapOfCollars
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c)
    (d : ZMod m × EuclideanFourBallCollarDomain → Y)
    (hd : IsOpenEmbedding d) :
    IsOpenMap (smoothCappingSeamMapOfCollars m c hc d hd) := by
  intro U hU
  rw [isOpen_topologicalPushout_iff]
  constructor
  · rw [preimage_inl_image_smoothCappingSeamMapOfCollars m c hc d hd U]
    apply (isOpenEmbedding_smoothCappingNonpositiveBranch m c hc).isOpenMap
    exact hU.preimage continuous_subtype_val
  · rw [preimage_inr_image_smoothCappingSeamMapOfCollars m c hc d hd U]
    apply (isOpenEmbedding_smoothCappingNonnegativeBranch m d hd).isOpenMap
    exact hU.preimage continuous_subtype_val

private theorem isOpenEmbedding_smoothCappingSeamMapOfCollars
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c)
    (d : ZMod m × EuclideanFourBallCollarDomain → Y)
    (hd : IsOpenEmbedding d) :
    IsOpenEmbedding (smoothCappingSeamMapOfCollars m c hc d hd) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_smoothCappingSeamMapOfCollars m c hc d hd
  · exact injective_smoothCappingSeamMapOfCollars m c hc d hd
  · exact isOpenMap_smoothCappingSeamMapOfCollars m c hc d hd

private theorem smoothCappingSeamMap_mem_inlOffSeam_iff
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c)
    (d : ZMod m × EuclideanFourBallCollarDomain → Y)
    (hd : IsOpenEmbedding d)
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :
    smoothCappingSeamMapOfCollars m c hc d hd p ∈
        topologicalPushoutInlOffSeam
          (smoothCappingAttachingMapOfCollar m c hc.continuous)
          (smoothCappingAttachingMapOfCollar m d hd.continuous) ↔
      signedSeamTime m p < 0 := by
  let f := smoothCappingAttachingMapOfCollar m c hc.continuous
  let g := smoothCappingAttachingMapOfCollar m d hd.continuous
  constructor
  · rintro ⟨x, hx, hxp⟩
    by_cases hpt : signedSeamTime m p ≤ 0
    · have heq : x = smoothCappingBranchOfCollar m c p := by
        apply topologicalPushoutInl_injective f g
          (isClosedEmbedding_smoothCappingAttachingMapOfCollar
            m d hd.isEmbedding).injective
        simpa [f, g, smoothCappingSeamMapOfCollars,
          topologicalPushoutSeamMap, hpt] using hxp
      have hne : signedSeamTime m p ≠ 0 := by
        intro ht
        apply hx
        rw [heq]
        exact (smoothCappingBranch_mem_attachingRange_iff
          m c hc.isEmbedding p).mpr ht
      exact lt_of_le_of_ne hpt hne
    · have hpos : 0 < signedSeamTime m p := lt_of_not_ge hpt
      have hcross :
          topologicalPushoutInl f g x =
            topologicalPushoutInr f g (smoothCappingBranchOfCollar m d p) := by
        simpa [f, g, smoothCappingSeamMapOfCollars,
          topologicalPushoutSeamMap, hpt] using hxp
      obtain ⟨a, _ha, hga⟩ :=
        (topologicalPushoutInl_eq_inr_iff f g
          (isClosedEmbedding_smoothCappingAttachingMapOfCollar
            m c hc.isEmbedding).injective x
          (smoothCappingBranchOfCollar m d p)).mp hcross
      exact False.elim <| (ne_of_gt hpos)
        ((smoothCappingBranch_mem_attachingRange_iff
          m d hd.isEmbedding p).mp ⟨a, hga⟩)
  · intro hp
    refine ⟨smoothCappingBranchOfCollar m c p, ?_, ?_⟩
    · intro hrange
      exact hp.ne ((smoothCappingBranch_mem_attachingRange_iff
        m c hc.isEmbedding p).mp hrange)
    · simp [smoothCappingSeamMapOfCollars,
        topologicalPushoutSeamMap, hp.le]

private theorem smoothCappingSeamMap_mem_inrOffSeam_iff
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c)
    (d : ZMod m × EuclideanFourBallCollarDomain → Y)
    (hd : IsOpenEmbedding d)
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :
    smoothCappingSeamMapOfCollars m c hc d hd p ∈
        topologicalPushoutInrOffSeam
          (smoothCappingAttachingMapOfCollar m c hc.continuous)
          (smoothCappingAttachingMapOfCollar m d hd.continuous) ↔
      0 < signedSeamTime m p := by
  let f := smoothCappingAttachingMapOfCollar m c hc.continuous
  let g := smoothCappingAttachingMapOfCollar m d hd.continuous
  constructor
  · rintro ⟨y, hy, hyp⟩
    by_cases hpt : signedSeamTime m p ≤ 0
    · have hcross :
          topologicalPushoutInl f g (smoothCappingBranchOfCollar m c p) =
            topologicalPushoutInr f g y := by
        simpa [f, g, smoothCappingSeamMapOfCollars,
          topologicalPushoutSeamMap, hpt] using hyp.symm
      obtain ⟨a, hfa, hga⟩ :=
        (topologicalPushoutInl_eq_inr_iff f g
          (isClosedEmbedding_smoothCappingAttachingMapOfCollar
            m c hc.isEmbedding).injective
          (smoothCappingBranchOfCollar m c p) y).mp hcross
      have htzero : signedSeamTime m p = 0 :=
        (smoothCappingBranch_mem_attachingRange_iff
          m c hc.isEmbedding p).mp ⟨a, hfa⟩
      obtain ⟨b, hfb, _hgb⟩ := smoothCapping_zero_match
        m c hc.continuous d hd.continuous p htzero
      have hab : a = b :=
        (isClosedEmbedding_smoothCappingAttachingMapOfCollar
          m c hc.isEmbedding).injective (hfa.trans hfb.symm)
      apply False.elim
      apply hy
      refine ⟨b, ?_⟩
      subst b
      exact hga
    · exact lt_of_not_ge hpt
  · intro hp
    refine ⟨smoothCappingBranchOfCollar m d p, ?_, ?_⟩
    · intro hrange
      exact hp.ne' ((smoothCappingBranch_mem_attachingRange_iff
        m d hd.isEmbedding p).mp hrange)
    · simp [smoothCappingSeamMapOfCollars,
        topologicalPushoutSeamMap, not_le_of_gt hp]

omit [NeZero m] in
private theorem smoothCappingSeamMap_attaching_coverage
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c)
    (d : ZMod m × EuclideanFourBallCollarDomain → Y)
    (hd : IsOpenEmbedding d)
    (a : CoordinateUnlinkExteriorPlanarNeckSmoothCappingAttachingDomain m) :
    ∃ q, smoothCappingSeamMapOfCollars m c hc d hd q =
      topologicalPushoutInl
        (smoothCappingAttachingMapOfCollar m c hc.continuous)
        (smoothCappingAttachingMapOfCollar m d hd.continuous)
        (smoothCappingAttachingMapOfCollar m c hc.continuous a) := by
  let q : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m :=
    (a.1, (a.2, smoothCappingSignedSeamZero))
  refine ⟨q, ?_⟩
  have hzero : signedSeamTime m q = 0 := rfl
  have hleft : smoothCappingBranchOfCollar m c q =
      smoothCappingAttachingMapOfCollar m c hc.continuous a := by
    apply congrArg c
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        apply Subtype.ext
        change |(smoothCappingSignedSeamZero.1 : ℝ)| = 0
        simp [smoothCappingSignedSeamZero]
  simp only [smoothCappingSeamMapOfCollars, topologicalPushoutSeamMap,
    hzero, le_refl, ↓reduceIte]
  rw [hleft]

/-- The left-cut branch of the signed smooth-capping seam. -/
def coordinateUnlinkExteriorPlanarNeckLeftCutSeamBranch
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :
    CompactNeckLeftCut m :=
  coordinateUnlinkExteriorPlanarNeckLeftCutCollar m
    (signedSeamHalfReparam m p)

/-- The right-cut branch of the signed smooth-capping seam. -/
def coordinateUnlinkExteriorPlanarNeckRightCutSeamBranch
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :
    CompactNeckRightCut m :=
  coordinateUnlinkExteriorPlanarNeckRightCutCollar m
    (signedSeamHalfReparam m p)

/-- The four-ball branch common to the left and right smooth-capping seams. -/
def coordinateUnlinkExteriorPlanarNeckEuclideanFourBallSeamBranch
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :
    ZMod m × EuclideanFourBall :=
  coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m
    (signedSeamHalfReparam m p)

/-- The signed seam map generating the direct smooth atlas on the capped left cut. -/
def coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap :
    CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m →
      CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m :=
  topologicalPushoutSeamMap
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (signedSeamTime m)
    (coordinateUnlinkExteriorPlanarNeckLeftCutSeamBranch m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallSeamBranch m)

/-- The signed seam map generating the direct smooth atlas on the capped right cut. -/
def coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap :
    CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m →
      CoordinateUnlinkExteriorPlanarNeckRightSmoothCapping m :=
  topologicalPushoutSeamMap
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (signedSeamTime m)
    (coordinateUnlinkExteriorPlanarNeckRightCutSeamBranch m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallSeamBranch m)

/-- The left signed seam map is an open embedding. -/
theorem isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap :
    IsOpenEmbedding
      (coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m) := by
  exact isOpenEmbedding_smoothCappingSeamMapOfCollars m
    (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m)

/-- The right signed seam map is an open embedding. -/
theorem isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap :
    IsOpenEmbedding
      (coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap m) := by
  exact isOpenEmbedding_smoothCappingSeamMapOfCollars m
    (coordinateUnlinkExteriorPlanarNeckRightCutCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutCollar m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m)

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap_of_nonpositive
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : signedSeamTime m p ≤ 0) :
    coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m p =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckLeftCutSeamBranch m p) := by
  simp [coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap,
    topologicalPushoutSeamMap, hp]

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap_of_positive
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : 0 < signedSeamTime m p) :
    coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m p =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallSeamBranch m p) := by
  simp [coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap,
    topologicalPushoutSeamMap, not_le_of_gt hp]

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap_of_nonpositive
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : signedSeamTime m p ≤ 0) :
    coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap m p =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckRightCutSeamBranch m p) := by
  simp [coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap,
    topologicalPushoutSeamMap, hp]

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap_of_positive
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : 0 < signedSeamTime m p) :
    coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap m p =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallSeamBranch m p) := by
  simp [coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap,
    topologicalPushoutSeamMap, not_le_of_gt hp]

/-- Every left attaching point is covered by the left signed seam chart. -/
theorem coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap_attaching_coverage
    (a : CoordinateUnlinkExteriorPlanarNeckSmoothCappingAttachingDomain m) :
    ∃ q, coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m q =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m a) := by
  exact smoothCappingSeamMap_attaching_coverage m
    (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m) a

/-- Every right attaching point is covered by the right signed seam chart. -/
theorem coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap_attaching_coverage
    (a : CoordinateUnlinkExteriorPlanarNeckSmoothCappingAttachingDomain m) :
    ∃ q, coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap m q =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m a) := by
  exact smoothCappingSeamMap_attaching_coverage m
    (coordinateUnlinkExteriorPlanarNeckRightCutCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutCollar m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m) a

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckLeftSmoothCapping_coprojection_attaching
    (a : CoordinateUnlinkExteriorPlanarNeckSmoothCappingAttachingDomain m) :
    topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m a) =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m a) :=
  topologicalPushout_condition
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) a

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckRightSmoothCapping_coprojection_attaching
    (a : CoordinateUnlinkExteriorPlanarNeckSmoothCappingAttachingDomain m) :
    topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m a) =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m a) :=
  topologicalPushout_condition
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) a

private theorem isLocalDiffeomorph_coordinateUnlinkExteriorPlanarNeckLeftCutCollar :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckLeftCutChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m) := by
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  have hcompat := collaredCutSideAtlasChart_compatible_of_localDiffeomorphOn
    coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckLeftCut_offBoundary m)
    (compactNeckLeftBoundaryCollarMap m)
    (compactNeckLeftBoundaryCollarMap_range_subset m)
    (isOpenEmbedding_compactNeckLeftBoundaryCollarMap_toCut m)
    (isLocalDiffeomorphOn_compactNeckLeftBoundaryCollarMap m)
  exact isLocalDiffeomorph_collaredCutSideHalfCollarMap
    coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckLeftCut_offBoundary m)
    (compactNeckLeftBoundaryCollarMap m)
    (compactNeckLeftBoundaryCollarMap_range_subset m)
    (isOpenEmbedding_compactNeckLeftBoundaryCollarMap_toCut m)
    (compactNeckLeftCut_collarCoverage m) hcompat

private theorem isLocalDiffeomorph_coordinateUnlinkExteriorPlanarNeckRightCutCollar :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckRightCutChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarNeckRightCutCollar m) := by
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  have hcompat := collaredCutSideAtlasChart_compatible_of_localDiffeomorphOn
    coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckRightCut_offBoundary m)
    (compactNeckRightBoundaryCollarMap m)
    (compactNeckRightBoundaryCollarMap_range_subset m)
    (isOpenEmbedding_compactNeckRightBoundaryCollarMap_toCut m)
    (isLocalDiffeomorphOn_compactNeckRightBoundaryCollarMap m)
  exact isLocalDiffeomorph_collaredCutSideHalfCollarMap
    coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckRightCut_offBoundary m)
    (compactNeckRightBoundaryCollarMap m)
    (compactNeckRightBoundaryCollarMap_range_subset m)
    (isOpenEmbedding_compactNeckRightBoundaryCollarMap_toCut m)
    (compactNeckRightCut_collarCoverage m) hcompat

private theorem isLocalDiffeomorphAt_congr_of_eqOn_open
    {E F H K M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace K]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K)
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N]
    {f g : M → N} {x : M} (hg : IsLocalDiffeomorphAt I J ∞ g x)
    (W : Set M) (hW : IsOpen W) (hxW : x ∈ W)
    (heq : EqOn f g W) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  let Ψ := Classical.choose hg
  let q := Ψ.toOpenPartialHomeomorph.restrOpen W hW
  let Φ : PartialDiffeomorph I J M N ∞ :=
    { toPartialEquiv := q.toPartialEquiv
      open_source := q.open_source
      open_target := q.open_target
      contMDiffOn_toFun := by
        apply Ψ.contMDiffOn_toFun.mono
        intro y hy
        change y ∈ Ψ.source ∩ W at hy
        exact hy.1
      contMDiffOn_invFun := by
        apply Ψ.contMDiffOn_invFun.mono
        intro y hy
        change y ∈ Ψ.target ∩ Ψ.symm ⁻¹' W at hy
        exact hy.1 }
  refine ⟨Φ, ?_, ?_⟩
  · change x ∈ Ψ.source ∩ W
    exact ⟨(Classical.choose_spec hg).1, hxW⟩
  · intro y hy
    change y ∈ Ψ.source ∩ W at hy
    exact (heq hy.2).trans ((Classical.choose_spec hg).2 hy.1)

private theorem isLocalDiffeomorphAt_congr_of_eventuallyEq
    {E F H K M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace K]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K)
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N]
    {f g : M → N} {x : M} (hg : IsLocalDiffeomorphAt I J ∞ g x)
    (heq : f =ᶠ[nhds x] g) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp heq
  exact isLocalDiffeomorphAt_congr_of_eqOn_open I J hg W hWopen hxW
    (fun y hy ↦ hWsub hy)

omit [NeZero m] in
private theorem
    isLocalDiffeomorph_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ EuclideanFourBall :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBall
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBall) :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBallFamily m
  have hsndSource : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × EuclideanFourBallCollarDomain →
        EuclideanFourBallCollarDomain) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := EuclideanFourBallCollarDomain))
  have hsndTarget : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × EuclideanFourBall → EuclideanFourBall) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := EuclideanFourBall))
  intro x
  let c := coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar
  let u : ZMod m × EuclideanFourBallCollarDomain → EuclideanFourBall :=
    fun z ↦ c z.2
  have hbase : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ c x.2 :=
    isLocalDiffeomorph_coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar x.2
  have hu : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ u x := by
    simpa [u, Function.comp_def] using
      (hsndSource x).comp coordinateUnlinkExteriorModel EuclideanFourBall hbase
  let targetPoint : ZMod m × EuclideanFourBall := (x.1, c x.2)
  let htarget := hsndTarget targetPoint
  let g : ZMod m × EuclideanFourBallCollarDomain →
      ZMod m × EuclideanFourBall :=
    fun z ↦ htarget.localInverse (u z)
  have hg : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ g x := by
    have hcomp := hu.comp coordinateUnlinkExteriorModel
      (ZMod m × EuclideanFourBall)
      htarget.localInverse_isLocalDiffeomorphAt
    simpa [g, Function.comp_def] using hcomp
  apply isLocalDiffeomorphAt_congr_of_eventuallyEq
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel hg
  have huCont : ContinuousAt u x := hu.contMDiffAt.continuousAt
  have hinvValue : htarget.localInverse (u x) = targetPoint :=
    htarget.localInverse_left_inv htarget.localInverse_mem_target
  have hsource : ∀ᶠ z in nhds x, u z ∈ htarget.localInverse.source :=
    huCont (htarget.localInverse.open_source.mem_nhds
      htarget.localInverse_mem_source)
  have hinvLabelAt :
      {z : ZMod m × EuclideanFourBall | z.1 = x.1} ∈
        nhds (htarget.localInverse (u x)) := by
    rw [hinvValue]
    exact ((isOpen_discrete ({x.1} : Set (ZMod m))).preimage continuous_fst).mem_nhds
      (by simp [targetPoint])
  have hinvLabel : ∀ᶠ z in nhds x,
      (htarget.localInverse (u z)).1 = x.1 :=
    huCont (htarget.localInverse_contMDiffAt.continuousAt hinvLabelAt)
  have hsourceLabel : ∀ᶠ z in nhds x, z.1 = x.1 :=
    ((isOpen_discrete ({x.1} : Set (ZMod m))).preimage continuous_fst).mem_nhds
      (by simp)
  filter_upwards [hsource, hinvLabel, hsourceLabel] with z hzSource hzInvLabel hzLabel
  apply Prod.ext
  · exact hzLabel.trans hzInvLabel.symm
  · exact (htarget.localInverse_right_inv hzSource).symm

private def smoothCappingSphereThreePoint : Sphere 3 :=
  ⟨Classical.choose
      (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin 4))
        (x := 0) (r := 1) |>.2 (by norm_num)),
    Classical.choose_spec
      (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin 4))
        (x := 0) (r := 1) |>.2 (by norm_num))⟩

private def smoothCappingSignedNegativeQuarter : EquatorCollarInterval :=
  ⟨-(1 / 4 : ℝ), by norm_num [equatorCollarIntervalOpens]⟩

private def smoothCappingSignedPositiveQuarter : EquatorCollarInterval :=
  ⟨(1 / 4 : ℝ), by norm_num [equatorCollarIntervalOpens]⟩

omit [NeZero m] in
private theorem nonempty_smoothCappingSignedCollar :
    Nonempty (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
  ⟨(0, (smoothCappingSphereThreePoint, smoothCappingSignedSeamZero))⟩

private theorem nonempty_smoothCappingInlOffSeam
    {X : Type} [TopologicalSpace X] [T2Space X]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c) :
    Nonempty ↑(topologicalPushoutInlOffSeamOpens
      (smoothCappingAttachingMapOfCollar m c hc.continuous)
      (isClosedEmbedding_smoothCappingAttachingMapOfCollar
        m c hc.isEmbedding)) := by
  let p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m :=
    (0, (smoothCappingSphereThreePoint, smoothCappingSignedNegativeQuarter))
  refine ⟨⟨smoothCappingBranchOfCollar m c p, ?_⟩⟩
  intro hp
  have ht := (smoothCappingBranch_mem_attachingRange_iff
    m c hc.isEmbedding p).mp hp
  norm_num [p, signedSeamTime, smoothCappingSignedNegativeQuarter] at ht

private theorem nonempty_smoothCappingInrOffSeam
    {Y : Type} [TopologicalSpace Y] [T2Space Y]
    (d : ZMod m × EuclideanFourBallCollarDomain → Y)
    (hd : IsOpenEmbedding d) :
    Nonempty ↑(topologicalPushoutInrOffSeamOpens
      (smoothCappingAttachingMapOfCollar m d hd.continuous)
      (isClosedEmbedding_smoothCappingAttachingMapOfCollar
        m d hd.isEmbedding)) := by
  let p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m :=
    (0, (smoothCappingSphereThreePoint, smoothCappingSignedPositiveQuarter))
  refine ⟨⟨smoothCappingBranchOfCollar m d p, ?_⟩⟩
  intro hp
  have ht := (smoothCappingBranch_mem_attachingRange_iff
    m d hd.isEmbedding p).mp hp
  norm_num [p, signedSeamTime, smoothCappingSignedPositiveQuarter] at ht

private theorem smoothCappingSeamInlOverlap_source
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c)
    (d : ZMod m × EuclideanFourBallCollarDomain → Y)
    (hd : IsOpenEmbedding d)
    [Nonempty (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)]
    [Nonempty ↑(topologicalPushoutInlOffSeamOpens
      (smoothCappingAttachingMapOfCollar m c hc.continuous)
      (isClosedEmbedding_smoothCappingAttachingMapOfCollar
        m c hc.isEmbedding))] :
    (topologicalPushoutSeamInlOffSeamOverlap
      (smoothCappingAttachingMapOfCollar m c hc.continuous)
      (smoothCappingAttachingMapOfCollar m d hd.continuous)
      (isClosedEmbedding_smoothCappingAttachingMapOfCollar
        m c hc.isEmbedding)
      (isClosedEmbedding_smoothCappingAttachingMapOfCollar
        m d hd.isEmbedding)
      (smoothCappingSeamMapOfCollars m c hc d hd)
      (isOpenEmbedding_smoothCappingSeamMapOfCollars m c hc d hd)).source =
        {p | signedSeamTime m p < 0} := by
  rw [topologicalPushoutSeamInlOffSeamOverlap_source]
  ext p
  exact smoothCappingSeamMap_mem_inlOffSeam_iff m c hc d hd p

private theorem smoothCappingSeamInrOverlap_source
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c)
    (d : ZMod m × EuclideanFourBallCollarDomain → Y)
    (hd : IsOpenEmbedding d)
    [Nonempty (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)]
    [Nonempty ↑(topologicalPushoutInrOffSeamOpens
      (smoothCappingAttachingMapOfCollar m d hd.continuous)
      (isClosedEmbedding_smoothCappingAttachingMapOfCollar
        m d hd.isEmbedding))] :
    (topologicalPushoutSeamInrOffSeamOverlap
      (smoothCappingAttachingMapOfCollar m c hc.continuous)
      (smoothCappingAttachingMapOfCollar m d hd.continuous)
      (isClosedEmbedding_smoothCappingAttachingMapOfCollar
        m c hc.isEmbedding)
      (isClosedEmbedding_smoothCappingAttachingMapOfCollar
        m d hd.isEmbedding)
      (smoothCappingSeamMapOfCollars m c hc d hd)
      (isOpenEmbedding_smoothCappingSeamMapOfCollars m c hc d hd)).source =
        {p | 0 < signedSeamTime m p} := by
  rw [topologicalPushoutSeamInrOffSeamOverlap_source]
  ext p
  exact smoothCappingSeamMap_mem_inrOffSeam_iff m c hc d hd p

private theorem isManifold_smoothCappingPushoutOfCollars
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [ChartedSpace CoordinateUnlinkExteriorModelSpace X]
    [ChartedSpace CoordinateUnlinkExteriorModelSpace Y]
    [IsManifold coordinateUnlinkExteriorModel ∞ X]
    [IsManifold coordinateUnlinkExteriorModel ∞ Y]
    (c : ZMod m × EuclideanFourBallCollarDomain → X)
    (hc : IsOpenEmbedding c)
    (hcLocal :
      letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
      IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞ c)
    (d : ZMod m × EuclideanFourBallCollarDomain → Y)
    (hd : IsOpenEmbedding d)
    (hdLocal :
      letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
      IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞ d) :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI := topologicalPushoutChartedSpace
      (H := CoordinateUnlinkExteriorModelSpace)
      (smoothCappingAttachingMapOfCollar m c hc.continuous)
      (smoothCappingAttachingMapOfCollar m d hd.continuous)
      (isClosedEmbedding_smoothCappingAttachingMapOfCollar
        m c hc.isEmbedding)
      (isClosedEmbedding_smoothCappingAttachingMapOfCollar
        m d hd.isEmbedding)
      (smoothCappingSeamMapOfCollars m c hc d hd)
      (isOpenEmbedding_smoothCappingSeamMapOfCollars m c hc d hd)
      (smoothCappingSeamMap_attaching_coverage m c hc d hd)
    IsManifold coordinateUnlinkExteriorModel ∞
      (TopologicalPushout
        (smoothCappingAttachingMapOfCollar m c hc.continuous)
        (smoothCappingAttachingMapOfCollar m d hd.continuous)) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    isManifold_signedSeamFamilyCommonModel m
  let _ : Nonempty
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    nonempty_smoothCappingSignedCollar m
  let _ : Nonempty ↑(topologicalPushoutInlOffSeamOpens
      (smoothCappingAttachingMapOfCollar m c hc.continuous)
      (isClosedEmbedding_smoothCappingAttachingMapOfCollar
        m c hc.isEmbedding)) :=
    nonempty_smoothCappingInlOffSeam m c hc
  let _ : Nonempty ↑(topologicalPushoutInrOffSeamOpens
      (smoothCappingAttachingMapOfCollar m d hd.continuous)
      (isClosedEmbedding_smoothCappingAttachingMapOfCollar
        m d hd.isEmbedding)) :=
    nonempty_smoothCappingInrOffSeam m d hd
  have hleftLocal : IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (smoothCappingBranchOfCollar m c)
      (topologicalPushoutSeamInlOffSeamOverlap
        (smoothCappingAttachingMapOfCollar m c hc.continuous)
        (smoothCappingAttachingMapOfCollar m d hd.continuous)
        (isClosedEmbedding_smoothCappingAttachingMapOfCollar
          m c hc.isEmbedding)
        (isClosedEmbedding_smoothCappingAttachingMapOfCollar
          m d hd.isEmbedding)
        (smoothCappingSeamMapOfCollars m c hc d hd)
        (isOpenEmbedding_smoothCappingSeamMapOfCollars m c hc d hd)).source := by
    rw [smoothCappingSeamInlOverlap_source m c hc d hd]
    intro p
    have hcomp :=
      (isLocalDiffeomorphOn_signedSeamHalfReparam_negative m p).comp
        coordinateUnlinkExteriorModel X
        (hcLocal (signedSeamHalfReparam m p.1))
    change IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (fun x : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m ↦
        c (signedSeamHalfReparam m x)) p.1
    exact hcomp
  have hrightLocal : IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (smoothCappingBranchOfCollar m d)
      (topologicalPushoutSeamInrOffSeamOverlap
        (smoothCappingAttachingMapOfCollar m c hc.continuous)
        (smoothCappingAttachingMapOfCollar m d hd.continuous)
        (isClosedEmbedding_smoothCappingAttachingMapOfCollar
          m c hc.isEmbedding)
        (isClosedEmbedding_smoothCappingAttachingMapOfCollar
          m d hd.isEmbedding)
        (smoothCappingSeamMapOfCollars m c hc d hd)
        (isOpenEmbedding_smoothCappingSeamMapOfCollars m c hc d hd)).source := by
    rw [smoothCappingSeamInrOverlap_source m c hc d hd]
    intro p
    have hcomp :=
      (isLocalDiffeomorphOn_signedSeamHalfReparam_positive m p).comp
        coordinateUnlinkExteriorModel Y
        (hdLocal (signedSeamHalfReparam m p.1))
    change IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (fun x : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m ↦
        d (signedSeamHalfReparam m x)) p.1
    exact hcomp
  exact isManifold_topologicalPushoutChartedSpace_of_signed_localDiffeomorphOn
    (smoothCappingAttachingMapOfCollar m c hc.continuous)
    (smoothCappingAttachingMapOfCollar m d hd.continuous)
    coordinateUnlinkExteriorModel ∞
    (isClosedEmbedding_smoothCappingAttachingMapOfCollar
      m c hc.isEmbedding)
    (isClosedEmbedding_smoothCappingAttachingMapOfCollar
      m d hd.isEmbedding)
    (signedSeamTime m)
    (smoothCappingBranchOfCollar m c)
    (smoothCappingBranchOfCollar m d)
    (isOpenEmbedding_smoothCappingSeamMapOfCollars m c hc d hd)
    (smoothCappingSeamMap_attaching_coverage m c hc d hd)
    (smoothCapping_zero_match m c hc.continuous d hd.continuous)
    (fun p hp ↦ (smoothCappingBranch_mem_attachingRange_iff
      m c hc.isEmbedding p).mp hp)
    (fun p hp ↦ (smoothCappingBranch_mem_attachingRange_iff
      m d hd.isEmbedding p).mp hp)
    hleftLocal hrightLocal

/-- The direct charted-space structure generated on the capped compact left cut. -/
@[instance_reducible]
noncomputable def coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m) := by
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ := compactNeckLeftCutChartedSpace m
  let _ :=
    coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  exact topologicalPushoutChartedSpace
    (H := CoordinateUnlinkExteriorModelSpace)
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m)
    (coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap_attaching_coverage m)

/-- The direct charted-space structure generated on the capped compact right cut. -/
@[instance_reducible]
noncomputable def coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorPlanarNeckRightSmoothCapping m) := by
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ := compactNeckRightCutChartedSpace m
  let _ :=
    coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  exact topologicalPushoutChartedSpace
    (H := CoordinateUnlinkExteriorModelSpace)
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap m)
    (coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap_attaching_coverage m)

/-- The capped compact left cut is a smooth four-manifold in the direct generated atlas. -/
theorem isManifold_coordinateUnlinkExteriorPlanarNeckLeftSmoothCapping :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m) := by
  let _ := compactNeckLeftCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckLeftCut m) :=
    isManifold_compactNeckLeftCut m
  let _ :=
    coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBall) :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBallFamily m
  exact isManifold_smoothCappingPushoutOfCollars m
    (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
    (isLocalDiffeomorph_coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m)
    (isLocalDiffeomorph_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m)

/-- The capped compact right cut is a smooth four-manifold in the direct generated atlas. -/
theorem isManifold_coordinateUnlinkExteriorPlanarNeckRightSmoothCapping :
    letI := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
    IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarNeckRightSmoothCapping m) := by
  let _ := compactNeckRightCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckRightCut m) :=
    isManifold_compactNeckRightCut m
  let _ :=
    coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBall) :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBallFamily m
  exact isManifold_smoothCappingPushoutOfCollars m
    (coordinateUnlinkExteriorPlanarNeckRightCutCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutCollar m)
    (isLocalDiffeomorph_coordinateUnlinkExteriorPlanarNeckRightCutCollar m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m)
    (isLocalDiffeomorph_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallFamilyCollar m)

end SplittingSpheres

end
