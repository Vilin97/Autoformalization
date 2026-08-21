/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.CollaredCutSideBoundary
public import SplittingSpheres.Geometry.CoordinateUnlinkBoundaryCollarDiffeomorph
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckCompactCutSide
import SplittingSpheres.Foundations.DiscreteProductChartedSpace
import SplittingSpheres.Foundations.SmoothEmbedding
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth compact neck cut sides

This file equips the two closed sides of the oriented compact neck-star cut with their direct
smooth collared-cut atlases.  The collar maps retain the cyclic label and use the symbolically
oriented neck collar, so no choice of a globally fixed forward orientation is made.

The collar maps are smooth everywhere and local diffeomorphisms exactly over the native
open stratum, equivalently at positive collar time.  The resulting model boundary is the
subtype preimage of the old ambient radial boundary together with the full cutting seam.
-/

@[expose] public section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace SplittingSpheres

noncomputable section


/-- Parameterize the nonpositive half of the compact neck collar by inward collar time. -/
def compactNeckLeftHalfParameter
    (p : EuclideanFourBallCollarDomain) :
    Sphere 3 × EquatorCollarInterval :=
  (p.1, ⟨-(p.2.1.1 : ℝ), by
    constructor
    · exact neg_lt_neg p.2.2
    · linarith [p.2.1.2.1]⟩)

/-- Parameterize the nonnegative half of the compact neck collar by inward collar time. -/
def compactNeckRightHalfParameter
    (p : EuclideanFourBallCollarDomain) :
    Sphere 3 × EquatorCollarInterval :=
  (p.1, ⟨(p.2.1.1 : ℝ), by
    constructor
    · have hp0 : 0 ≤ (p.2.1.1 : ℝ) := p.2.1.2.1
      linarith
    · exact p.2.2⟩)

@[simp] private theorem compactNeckLeftHalfParameter_time
    (p : EuclideanFourBallCollarDomain) :
    (compactNeckLeftHalfParameter p).2.1 = -(p.2.1.1 : ℝ) := rfl

@[simp] private theorem compactNeckRightHalfParameter_time
    (p : EuclideanFourBallCollarDomain) :
    (compactNeckRightHalfParameter p).2.1 = (p.2.1.1 : ℝ) := rfl

private theorem injective_compactNeckLeftHalfParameter :
    Injective compactNeckLeftHalfParameter := by
  intro p q hpq
  apply Prod.ext
  · exact congrArg (fun z : Sphere 3 × EquatorCollarInterval ↦ z.1) hpq
  · apply Subtype.ext
    apply Subtype.ext
    have ht := congrArg (fun z : Sphere 3 × EquatorCollarInterval ↦ z.2.1) hpq
    simpa using congrArg Neg.neg ht

private theorem injective_compactNeckRightHalfParameter :
    Injective compactNeckRightHalfParameter := by
  intro p q hpq
  apply Prod.ext
  · exact congrArg (fun z : Sphere 3 × EquatorCollarInterval ↦ z.1) hpq
  · apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Sphere 3 × EquatorCollarInterval ↦ z.2.1) hpq

private theorem range_compactNeckLeftHalfParameter :
    range compactNeckLeftHalfParameter =
      {p : Sphere 3 × EquatorCollarInterval | p.2.1 ≤ 0} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact neg_nonpos.mpr q.2.1.2.1
  · intro hp
    have hp0 : 0 ≤ -p.2.1 := neg_nonneg.mpr hp
    have hpt : -p.2.1 ≤ 1 / 2 := by
      have := p.2.2.1
      linarith
    have hplt : -p.2.1 < 1 / 2 := by
      have := p.2.2.1
      linarith
    let t : EuclideanFourBallCollarInterval :=
      ⟨⟨-p.2.1, hp0, hpt⟩, hplt⟩
    refine ⟨(p.1, t), ?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change -(-p.2.1) = p.2.1
      simp

private theorem range_compactNeckRightHalfParameter :
    range compactNeckRightHalfParameter =
      {p : Sphere 3 × EquatorCollarInterval | 0 ≤ p.2.1} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact q.2.1.2.1
  · intro hp
    have hpt : p.2.1 ≤ 1 / 2 := p.2.2.2.le
    let t : EuclideanFourBallCollarInterval :=
      ⟨⟨p.2.1, hp, hpt⟩, p.2.2.2⟩
    refine ⟨(p.1, t), ?_⟩
    apply Prod.ext rfl
    rfl

private def compactNeckLeftHalfHomeomorph :
    EuclideanFourBallCollarDomain ≃ₜ
      CoordinateUnlinkExteriorPlanarCompactCollarNonpositiveHalf where
  toFun p := ⟨compactNeckLeftHalfParameter p,
    neg_nonpos.mpr p.2.1.2.1⟩
  invFun p :=
    (p.1.1, ⟨⟨-p.1.2.1, neg_nonneg.mpr p.2, by
      have h := neg_lt_neg p.1.2.2.1
      simpa using h.le⟩,
      by
        have h := neg_lt_neg p.1.2.2.1
        simpa using h⟩)
  left_inv p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Subtype.ext
      simp [compactNeckLeftHalfParameter]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [compactNeckLeftHalfParameter]
  continuous_toFun := by
    unfold compactNeckLeftHalfParameter
    fun_prop
  continuous_invFun := by
    fun_prop

private def compactNeckRightHalfHomeomorph :
    EuclideanFourBallCollarDomain ≃ₜ
      CoordinateUnlinkExteriorPlanarCompactCollarNonnegativeHalf where
  toFun p := ⟨compactNeckRightHalfParameter p, p.2.1.2.1⟩
  invFun p :=
    (p.1.1, ⟨⟨p.1.2.1, p.2, p.1.2.2.2.le⟩, p.1.2.2.2⟩)
  left_inv p := by
    apply Prod.ext
    · rfl
    · rfl
  right_inv p := by
    rfl
  continuous_toFun := by
    unfold compactNeckRightHalfParameter
    fun_prop
  continuous_invFun := by
    fun_prop

private theorem isEmbedding_compactNeckLeftHalfParameter :
    IsEmbedding compactNeckLeftHalfParameter := by
  have h := Topology.IsEmbedding.subtypeVal.comp
    compactNeckLeftHalfHomeomorph.isEmbedding
  exact h

private theorem isEmbedding_compactNeckRightHalfParameter :
    IsEmbedding compactNeckRightHalfParameter := by
  have h := Topology.IsEmbedding.subtypeVal.comp
    compactNeckRightHalfHomeomorph.isEmbedding
  exact h

private def compactNeckEquatorCollarIntervalNegDiffeomorph :
    EquatorCollarInterval ≃ₘ^∞⟮
      (modelWithCornersSelf ℝ ℝ), (modelWithCornersSelf ℝ ℝ)⟯
      EquatorCollarInterval where
  toEquiv :=
    coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph.toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff equatorCollarIntervalOpens _).mp
    have h : ContDiff ℝ ∞ (fun t : ℝ ↦ -t) := by fun_prop
    simpa [coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph,
      Function.comp_def] using h.comp_contMDiff contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff equatorCollarIntervalOpens _).mp
    have h : ContDiff ℝ ∞ (fun t : ℝ ↦ -t) := by fun_prop
    simpa [coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph,
      Function.comp_def] using h.comp_contMDiff contMDiff_subtype_val

private def compactNeckCollarFlipDiffeomorph :
    (Sphere 3 × EquatorCollarInterval) ≃ₘ^∞⟮
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real)),
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real))⟯
      (Sphere 3 × EquatorCollarInterval) :=
  (Diffeomorph.refl
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 3)))
      (Sphere 3) ∞).prodCongr
    compactNeckEquatorCollarIntervalNegDiffeomorph

@[simp] private theorem compactNeckCollarFlipDiffeomorph_apply
    (p : Sphere 3 × EquatorCollarInterval) :
    compactNeckCollarFlipDiffeomorph p =
      coordinateUnlinkExteriorPlanarCompactCollarFlipHomeomorph p :=
  rfl

private theorem contMDiff_compactNeckLeftHalfParameter :
    ContMDiff euclideanFourBallCollarModel
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real)) ∞
      compactNeckLeftHalfParameter := by
  have ht : ContMDiff (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf Real Real) ∞
      (fun t : EuclideanFourBallCollarInterval ↦ -(t.1.1 : Real)) := by
    have hval : ContMDiff (modelWithCornersEuclideanHalfSpace 1)
        (modelWithCornersSelf Real Real) ∞
        (fun t : EuclideanFourBallCollarInterval ↦ (t.1.1 : Real)) :=
      (contMDiff_subtypeVal_Icc (x := (0 : Real)) (y := (1 / 2 : Real))).comp
        contMDiff_subtype_val
    have hneg : ContDiff Real ∞ (fun t : Real ↦ -t) := by fun_prop
    exact hneg.comp_contMDiff hval
  apply ContMDiff.prodMk contMDiff_fst
  apply (ContMDiff.subtypeVal_comp_iff equatorCollarIntervalOpens _).mp
  exact ht.comp contMDiff_snd

private theorem contMDiff_compactNeckRightHalfParameter :
    ContMDiff euclideanFourBallCollarModel
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real)) ∞
      compactNeckRightHalfParameter := by
  have ht : ContMDiff (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf Real Real) ∞
      (fun t : EuclideanFourBallCollarInterval ↦ (t.1.1 : Real)) :=
    (contMDiff_subtypeVal_Icc (x := (0 : Real)) (y := (1 / 2 : Real))).comp
      contMDiff_subtype_val
  apply ContMDiff.prodMk contMDiff_fst
  apply (ContMDiff.subtypeVal_comp_iff equatorCollarIntervalOpens _).mp
  exact ht.comp contMDiff_snd

section Compact

variable (m : ℕ) [NeZero m]

/-- The closed left side of the oriented compact neck-star cut. -/
abbrev CompactNeckLeftCut : Type :=
  CollaredCutSide
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)

/-- The closed right side of the oriented compact neck-star cut. -/
abbrev CompactNeckRightCut : Type :=
  CollaredCutSide
    (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)

local instance standardPowerChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
  standardUnlinkPowerPullbackChartedSpace m

local instance compactExteriorPowerChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
  coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m

local instance compactNeckBoundaryCollarFamilyChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m × EuclideanFourBallCollarDomain) :=
  coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m

local instance compactNeckBoundaryCollarFamilyIsManifold :
    IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
  isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m

private noncomputable def compactNeckOrientedSourceDiffeomorph (a : ZMod m) :
    (Sphere 3 × EquatorCollarInterval) ≃ₘ^∞⟮
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real)),
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real))⟯
      (Sphere 3 × EquatorCollarInterval) := by
  classical
  exact if coordinateUnlinkExteriorPlanarCompactCollarRawForward m a then
    Diffeomorph.refl _ _ ∞
  else compactNeckCollarFlipDiffeomorph

@[simp] private theorem compactNeckOrientedSourceDiffeomorph_apply
    (a : ZMod m) (p : Sphere 3 × EquatorCollarInterval) :
    compactNeckOrientedSourceDiffeomorph m a p =
      coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph m a p := by
  classical
  by_cases h : coordinateUnlinkExteriorPlanarCompactCollarRawForward m a
  · simp [compactNeckOrientedSourceDiffeomorph,
      coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph, h]
  · simp [compactNeckOrientedSourceDiffeomorph,
      coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph, h]

private theorem contMDiff_compactNeckOrientedCollarMap (a : ZMod m) :
    letI : IsManifold
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      isManifold_coordinateUnlinkExteriorEighthPowerPullback m
    ContMDiff
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real))
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a) := by
  let _ : IsManifold
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  have h :=
    (contMDiff_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a).comp
      (compactNeckOrientedSourceDiffeomorph m a).contMDiff
  exact h.congr fun p ↦ by
    simp [coordinateUnlinkExteriorPlanarOrientedCompactCollarMap]

private theorem isLocalDiffeomorph_compactNeckOrientedCollarMap (a : ZMod m) :
    letI : IsManifold
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      isManifold_coordinateUnlinkExteriorEighthPowerPullback m
    IsLocalDiffeomorph
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real))
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a) := by
  let _ : IsManifold
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  intro p
  have h := (compactNeckOrientedSourceDiffeomorph m a).isLocalDiffeomorph p
  have hcomp := h.comp coordinateUnlinkExteriorModel
    (CoordinateUnlinkExteriorEighthPowerPullback m)
    (isLocalDiffeomorph_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap
      m a (compactNeckOrientedSourceDiffeomorph m a p))
  obtain ⟨phi, hp, hphi⟩ := hcomp
  refine ⟨phi, hp, ?_⟩
  intro q hq
  rw [show coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a q =
      coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a
        (compactNeckOrientedSourceDiffeomorph m a q) by
    simp [coordinateUnlinkExteriorPlanarOrientedCompactCollarMap]]
  exact hphi hq

private theorem compactNeckOrientedCollarMap_not_mem_ambientBoundary
    (a : ZMod m) (p : Sphere 3 × EquatorCollarInterval) :
    letI : IsManifold
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      isManifold_coordinateUnlinkExteriorEighthPowerPullback m
    coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a p ∉
      coordinateUnlinkExteriorModel.boundary
        (CoordinateUnlinkExteriorEighthPowerPullback m) := by
  let _ : IsManifold
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  intro hpBoundary
  have hsource :
      (((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real))).IsBoundaryPoint p :=
    ((isLocalDiffeomorph_compactNeckOrientedCollarMap m a p).isBoundaryPoint_iff
      (by simp)).mpr hpBoundary
  have hempty :
      (((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real))).boundary
          (Sphere 3 × EquatorCollarInterval) = ∅ :=
    ModelWithCorners.Boundaryless.boundary_eq_empty
  change p ∈ (((modelWithCornersSelf Real
      (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real))).boundary
          (Sphere 3 × EquatorCollarInterval) at hsource
  rw [hempty] at hsource
  exact hsource

/-- The all-label half-collar map for the left compact neck cut. -/
noncomputable def compactNeckLeftBoundaryCollarMap :
    ZMod m × EuclideanFourBallCollarDomain →
      CoordinateUnlinkExteriorEighthPowerPullback m :=
  fun p ↦ coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m p.1
    (compactNeckLeftHalfParameter p.2)

/-- The all-label half-collar map for the right compact neck cut. -/
noncomputable def compactNeckRightBoundaryCollarMap :
    ZMod m × EuclideanFourBallCollarDomain →
      CoordinateUnlinkExteriorEighthPowerPullback m :=
  fun p ↦ coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m p.1
    (compactNeckRightHalfParameter p.2)

private theorem range_compactNeckLeftBoundaryCollarMap_component (a : ZMod m) :
    range (fun p : EuclideanFourBallCollarDomain ↦
      compactNeckLeftBoundaryCollarMap m (a, p)) =
      (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a :
        Set (CoordinateUnlinkExteriorEighthPowerPullback m)) ∩
        coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m := by
  rw [← range_coordinateUnlinkExteriorPlanarOrientedCompactCollarLeftHalfMap m a]
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨compactNeckLeftHalfHomeomorph p, rfl⟩
  · rintro ⟨p, rfl⟩
    refine ⟨compactNeckLeftHalfHomeomorph.symm p, ?_⟩
    have hp := congrArg Subtype.val
      (compactNeckLeftHalfHomeomorph.apply_symm_apply p)
    exact congrArg
      (coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a) hp

private theorem range_compactNeckRightBoundaryCollarMap_component (a : ZMod m) :
    range (fun p : EuclideanFourBallCollarDomain ↦
      compactNeckRightBoundaryCollarMap m (a, p)) =
      (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a :
        Set (CoordinateUnlinkExteriorEighthPowerPullback m)) ∩
        coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m := by
  rw [← range_coordinateUnlinkExteriorPlanarOrientedCompactCollarRightHalfMap m a]
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨compactNeckRightHalfHomeomorph p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨compactNeckRightHalfHomeomorph.symm p, rfl⟩

/-- The union of the pairwise-disjoint compact collar images over all cyclic labels. -/
def compactNeckCollarFamilyImage :
    Set (CoordinateUnlinkExteriorEighthPowerPullback m) :=
  ⋃ a : ZMod m,
    (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a :
      Set (CoordinateUnlinkExteriorEighthPowerPullback m))

/-- The all-label compact collar image is open in the ambient exterior cover. -/
theorem isOpen_compactNeckCollarFamilyImage :
    IsOpen (compactNeckCollarFamilyImage m) := by
  apply isOpen_iUnion
  intro a
  exact (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a).2

/-- The left half-collar has exactly the part of the collar family lying in the left cut. -/
theorem range_compactNeckLeftBoundaryCollarMap :
    range (compactNeckLeftBoundaryCollarMap m) =
      compactNeckCollarFamilyImage m ∩
        coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m := by
  ext z
  constructor
  · rintro ⟨⟨a, p⟩, rfl⟩
    have hz : compactNeckLeftBoundaryCollarMap m (a, p) ∈
        range (fun q : EuclideanFourBallCollarDomain ↦
          compactNeckLeftBoundaryCollarMap m (a, q)) :=
      mem_range_self p
    rw [range_compactNeckLeftBoundaryCollarMap_component m a] at hz
    exact ⟨mem_iUnion.mpr ⟨a, hz.1⟩, hz.2⟩
  · rintro ⟨hzV, hzC⟩
    obtain ⟨a, hza⟩ := mem_iUnion.mp hzV
    have hz : z ∈ range (fun p : EuclideanFourBallCollarDomain ↦
        compactNeckLeftBoundaryCollarMap m (a, p)) := by
      rw [range_compactNeckLeftBoundaryCollarMap_component m a]
      exact ⟨hza, hzC⟩
    obtain ⟨p, hp⟩ := hz
    exact ⟨(a, p), hp⟩

/-- The right half-collar has exactly the part of the collar family lying in the right cut. -/
theorem range_compactNeckRightBoundaryCollarMap :
    range (compactNeckRightBoundaryCollarMap m) =
      compactNeckCollarFamilyImage m ∩
        coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m := by
  ext z
  constructor
  · rintro ⟨⟨a, p⟩, rfl⟩
    have hz : compactNeckRightBoundaryCollarMap m (a, p) ∈
        range (fun q : EuclideanFourBallCollarDomain ↦
          compactNeckRightBoundaryCollarMap m (a, q)) :=
      mem_range_self p
    rw [range_compactNeckRightBoundaryCollarMap_component m a] at hz
    exact ⟨mem_iUnion.mpr ⟨a, hz.1⟩, hz.2⟩
  · rintro ⟨hzV, hzC⟩
    obtain ⟨a, hza⟩ := mem_iUnion.mp hzV
    have hz : z ∈ range (fun p : EuclideanFourBallCollarDomain ↦
        compactNeckRightBoundaryCollarMap m (a, p)) := by
      rw [range_compactNeckRightBoundaryCollarMap_component m a]
      exact ⟨hza, hzC⟩
    obtain ⟨p, hp⟩ := hz
    exact ⟨(a, p), hp⟩

private theorem isEmbedding_compactNeckLeftBoundaryCollarMap_component
    (a : ZMod m) :
    IsEmbedding (fun p : EuclideanFourBallCollarDomain ↦
      compactNeckLeftBoundaryCollarMap m (a, p)) :=
  (isOpenEmbedding_coordinateUnlinkExteriorPlanarOrientedCompactCollarMap
      m a).isEmbedding.comp isEmbedding_compactNeckLeftHalfParameter

private theorem isEmbedding_compactNeckRightBoundaryCollarMap_component
    (a : ZMod m) :
    IsEmbedding (fun p : EuclideanFourBallCollarDomain ↦
      compactNeckRightBoundaryCollarMap m (a, p)) :=
  (isOpenEmbedding_coordinateUnlinkExteriorPlanarOrientedCompactCollarMap
      m a).isEmbedding.comp isEmbedding_compactNeckRightHalfParameter

private theorem injective_compactNeckLeftBoundaryCollarMap :
    Injective (compactNeckLeftBoundaryCollarMap m) := by
  rintro ⟨a, p⟩ ⟨b, q⟩ hpq
  by_cases hab : a = b
  · subst b
    exact Prod.ext rfl
      ((isEmbedding_compactNeckLeftBoundaryCollarMap_component m a).injective hpq)
  · have hpa : compactNeckLeftBoundaryCollarMap m (a, p) ∈
        coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a := by
      have hp : compactNeckLeftBoundaryCollarMap m (a, p) ∈
          range (fun r : EuclideanFourBallCollarDomain ↦
            compactNeckLeftBoundaryCollarMap m (a, r)) := mem_range_self p
      rw [range_compactNeckLeftBoundaryCollarMap_component m a] at hp
      exact hp.1
    have hqb : compactNeckLeftBoundaryCollarMap m (b, q) ∈
        coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m b := by
      have hq : compactNeckLeftBoundaryCollarMap m (b, q) ∈
          range (fun r : EuclideanFourBallCollarDomain ↦
            compactNeckLeftBoundaryCollarMap m (b, r)) := mem_range_self q
      rw [range_compactNeckLeftBoundaryCollarMap_component m b] at hq
      exact hq.1
    exact False.elim <|
      Set.disjoint_left.mp
        (pairwise_disjoint_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage
          m hab) hpa (hpq ▸ hqb)

private theorem injective_compactNeckRightBoundaryCollarMap :
    Injective (compactNeckRightBoundaryCollarMap m) := by
  rintro ⟨a, p⟩ ⟨b, q⟩ hpq
  by_cases hab : a = b
  · subst b
    exact Prod.ext rfl
      ((isEmbedding_compactNeckRightBoundaryCollarMap_component m a).injective hpq)
  · have hpa : compactNeckRightBoundaryCollarMap m (a, p) ∈
        coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a := by
      have hp : compactNeckRightBoundaryCollarMap m (a, p) ∈
          range (fun r : EuclideanFourBallCollarDomain ↦
            compactNeckRightBoundaryCollarMap m (a, r)) := mem_range_self p
      rw [range_compactNeckRightBoundaryCollarMap_component m a] at hp
      exact hp.1
    have hqb : compactNeckRightBoundaryCollarMap m (b, q) ∈
        coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m b := by
      have hq : compactNeckRightBoundaryCollarMap m (b, q) ∈
          range (fun r : EuclideanFourBallCollarDomain ↦
            compactNeckRightBoundaryCollarMap m (b, r)) := mem_range_self q
      rw [range_compactNeckRightBoundaryCollarMap_component m b] at hq
      exact hq.1
    exact False.elim <|
      Set.disjoint_left.mp
        (pairwise_disjoint_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage
          m hab) hpa (hpq ▸ hqb)

private def prodSigmaHomeomorph
    (D P : Type*) [TopologicalSpace D] [DiscreteTopology D]
    [TopologicalSpace P] :
    D × P ≃ₜ (Σ _ : D, P) where
  toFun p := ⟨p.1, p.2⟩
  invFun p := (p.1, p.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    rw [continuous_prod_of_discrete_left]
    intro d
    change Continuous (fun p : P ↦ (⟨d, p⟩ : Σ _ : D, P))
    exact continuous_sigmaMk (σ := fun _ : D ↦ P)
  continuous_invFun := by
    apply continuous_sigma
    intro d
    exact continuous_const.prodMk continuous_id

private theorem isInducing_compactNeckLeftBoundaryCollarMap :
    IsInducing (compactNeckLeftBoundaryCollarMap m) := by
  let g : (Σ _ : ZMod m, EuclideanFourBallCollarDomain) →
      CoordinateUnlinkExteriorEighthPowerPullback m :=
    fun p ↦ compactNeckLeftBoundaryCollarMap m (p.1, p.2)
  have hg : IsInducing g := by
    rw [inducing_sigma]
    constructor
    · intro a
      exact (isEmbedding_compactNeckLeftBoundaryCollarMap_component m a).isInducing
    · intro a
      refine ⟨coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a,
        (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a).2, ?_⟩
      rintro ⟨b, p⟩
      constructor
      · intro hp
        by_contra hba
        have hown : compactNeckLeftBoundaryCollarMap m (b, p) ∈
            coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m b := by
          have hmem : compactNeckLeftBoundaryCollarMap m (b, p) ∈
              range (fun r : EuclideanFourBallCollarDomain ↦
                compactNeckLeftBoundaryCollarMap m (b, r)) := mem_range_self p
          rw [range_compactNeckLeftBoundaryCollarMap_component m b] at hmem
          exact hmem.1
        exact Set.disjoint_left.mp
          (pairwise_disjoint_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage
            m hba) hown hp
      · intro hba
        change b = a at hba
        subst b
        have hmem : compactNeckLeftBoundaryCollarMap m (a, p) ∈
            range (fun r : EuclideanFourBallCollarDomain ↦
              compactNeckLeftBoundaryCollarMap m (a, r)) := mem_range_self p
        rw [range_compactNeckLeftBoundaryCollarMap_component m a] at hmem
        exact hmem.1
  have hcomp := hg.comp (prodSigmaHomeomorph (ZMod m)
    EuclideanFourBallCollarDomain).isInducing
  exact hcomp

/-- The all-label left half-collar is an embedding in the ambient exterior cover. -/
theorem isEmbedding_compactNeckLeftBoundaryCollarMap :
    IsEmbedding (compactNeckLeftBoundaryCollarMap m) :=
  ⟨isInducing_compactNeckLeftBoundaryCollarMap m,
    injective_compactNeckLeftBoundaryCollarMap m⟩

private theorem isInducing_compactNeckRightBoundaryCollarMap :
    IsInducing (compactNeckRightBoundaryCollarMap m) := by
  let g : (Σ _ : ZMod m, EuclideanFourBallCollarDomain) →
      CoordinateUnlinkExteriorEighthPowerPullback m :=
    fun p ↦ compactNeckRightBoundaryCollarMap m (p.1, p.2)
  have hg : IsInducing g := by
    rw [inducing_sigma]
    constructor
    · intro a
      exact (isEmbedding_compactNeckRightBoundaryCollarMap_component m a).isInducing
    · intro a
      refine ⟨coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a,
        (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a).2, ?_⟩
      rintro ⟨b, p⟩
      constructor
      · intro hp
        by_contra hba
        have hown : compactNeckRightBoundaryCollarMap m (b, p) ∈
            coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m b := by
          have hmem : compactNeckRightBoundaryCollarMap m (b, p) ∈
              range (fun r : EuclideanFourBallCollarDomain ↦
                compactNeckRightBoundaryCollarMap m (b, r)) := mem_range_self p
          rw [range_compactNeckRightBoundaryCollarMap_component m b] at hmem
          exact hmem.1
        exact Set.disjoint_left.mp
          (pairwise_disjoint_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage
            m hba) hown hp
      · intro hba
        change b = a at hba
        subst b
        have hmem : compactNeckRightBoundaryCollarMap m (a, p) ∈
            range (fun r : EuclideanFourBallCollarDomain ↦
              compactNeckRightBoundaryCollarMap m (a, r)) := mem_range_self p
        rw [range_compactNeckRightBoundaryCollarMap_component m a] at hmem
        exact hmem.1
  have hcomp := hg.comp (prodSigmaHomeomorph (ZMod m)
    EuclideanFourBallCollarDomain).isInducing
  exact hcomp

/-- The all-label right half-collar is an embedding in the ambient exterior cover. -/
theorem isEmbedding_compactNeckRightBoundaryCollarMap :
    IsEmbedding (compactNeckRightBoundaryCollarMap m) :=
  ⟨isInducing_compactNeckRightBoundaryCollarMap m,
    injective_compactNeckRightBoundaryCollarMap m⟩

private theorem disjoint_compactNeckStarLeftOffSeam_seam :
    Disjoint
      (coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) := by
  rw [Set.disjoint_left]
  intro z hzLeft hzSeam
  have hzComp : z ∈
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)ᶜ := by
    rw [← union_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam]
    exact Or.inl hzLeft
  exact hzComp hzSeam

private theorem disjoint_compactNeckStarRightOffSeam_seam :
    Disjoint
      (coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) := by
  rw [Set.disjoint_left]
  intro z hzRight hzSeam
  have hzComp : z ∈
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)ᶜ := by
    rw [← union_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam]
    exact Or.inr hzRight
  exact hzComp hzSeam

private theorem compactNeckLeftCut_offBoundary :
    collaredCutSideOffBoundary
        (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
        (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) =
      coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m := by
  rw [coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier_eq]
  ext z
  constructor
  · rintro ⟨hzLeft | hzSeam, hzNotSeam⟩
    · exact hzLeft
    · exact False.elim (hzNotSeam hzSeam)
  · intro hzLeft
    refine ⟨Or.inl hzLeft, ?_⟩
    exact Set.disjoint_left.mp
      (disjoint_compactNeckStarLeftOffSeam_seam m) hzLeft

private theorem compactNeckRightCut_offBoundary :
    collaredCutSideOffBoundary
        (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
        (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) =
      coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m := by
  rw [coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier_eq]
  ext z
  constructor
  · rintro ⟨hzRight | hzSeam, hzNotSeam⟩
    · exact hzRight
    · exact False.elim (hzNotSeam hzSeam)
  · intro hzRight
    refine ⟨Or.inl hzRight, ?_⟩
    exact Set.disjoint_left.mp
      (disjoint_compactNeckStarRightOffSeam_seam m) hzRight

/-- The left half-collar meets the native off-seam stratum exactly at positive collar time. -/
theorem compactNeckLeftBoundaryCollarMap_mem_offBoundary_iff
    (p : ZMod m × EuclideanFourBallCollarDomain) :
    compactNeckLeftBoundaryCollarMap m p ∈
        collaredCutSideOffBoundary
          (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
          (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) ↔
      0 < (p.2.2.1.1 : Real) := by
  rw [compactNeckLeftCut_offBoundary m]
  change coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m p.1
      (compactNeckLeftHalfParameter p.2) ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ↔ _
  rw [coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_left_iff]
  simp only [compactNeckLeftHalfParameter_time]
  exact neg_lt_zero

/-- The right half-collar meets the native off-seam stratum exactly at positive collar time. -/
theorem compactNeckRightBoundaryCollarMap_mem_offBoundary_iff
    (p : ZMod m × EuclideanFourBallCollarDomain) :
    compactNeckRightBoundaryCollarMap m p ∈
        collaredCutSideOffBoundary
          (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
          (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) ↔
      0 < (p.2.2.1.1 : Real) := by
  rw [compactNeckRightCut_offBoundary m]
  change coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m p.1
      (compactNeckRightHalfParameter p.2) ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m ↔ _
  rw [coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_right_iff]
  rfl

/-- The left half-collar pulls the ambient radial boundary and seam back to zero collar time. -/
theorem preimage_compactNeckLeftBoundaryCollarMap_ambientBoundary_union_seam :
    compactNeckLeftBoundaryCollarMap m ⁻¹'
        (coordinateUnlinkExteriorModel.boundary
            (CoordinateUnlinkExteriorEighthPowerPullback m) ∪
          coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) =
      Prod.snd ⁻¹' ((univ : Set (Sphere 3)) ×ˢ
        {euclideanFourBallCollarZero}) := by
  ext p
  simp only [mem_preimage, mem_union, mem_prod, mem_univ, true_and,
    mem_singleton_iff]
  change
    (coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m p.1
        (compactNeckLeftHalfParameter p.2) ∈
        coordinateUnlinkExteriorModel.boundary
          (CoordinateUnlinkExteriorEighthPowerPullback m) ∨
      coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m p.1
        (compactNeckLeftHalfParameter p.2) ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) ↔
      p.2.2 = euclideanFourBallCollarZero
  rw [or_iff_right (compactNeckOrientedCollarMap_not_mem_ambientBoundary
    m p.1 (compactNeckLeftHalfParameter p.2))]
  rw [coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_seam_iff]
  change (-(p.2.2.1.1 : Real) = 0) ↔
    p.2.2 = euclideanFourBallCollarZero
  constructor
  · intro hp
    apply Subtype.ext
    apply Subtype.ext
    exact neg_eq_zero.mp hp
  · intro hp
    simp [hp]

/-- The right half-collar pulls the ambient radial boundary and seam back to zero collar time. -/
theorem preimage_compactNeckRightBoundaryCollarMap_ambientBoundary_union_seam :
    compactNeckRightBoundaryCollarMap m ⁻¹'
        (coordinateUnlinkExteriorModel.boundary
            (CoordinateUnlinkExteriorEighthPowerPullback m) ∪
          coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) =
      Prod.snd ⁻¹' ((univ : Set (Sphere 3)) ×ˢ
        {euclideanFourBallCollarZero}) := by
  ext p
  simp only [mem_preimage, mem_union, mem_prod, mem_univ, true_and,
    mem_singleton_iff]
  change
    (coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m p.1
        (compactNeckRightHalfParameter p.2) ∈
        coordinateUnlinkExteriorModel.boundary
          (CoordinateUnlinkExteriorEighthPowerPullback m) ∨
      coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m p.1
        (compactNeckRightHalfParameter p.2) ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) ↔
      p.2.2 = euclideanFourBallCollarZero
  rw [or_iff_right (compactNeckOrientedCollarMap_not_mem_ambientBoundary
    m p.1 (compactNeckRightHalfParameter p.2))]
  rw [coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_seam_iff]
  change ((p.2.2.1.1 : Real) = 0) ↔
    p.2.2 = euclideanFourBallCollarZero
  constructor
  · intro hp
    apply Subtype.ext
    apply Subtype.ext
    exact hp
  · intro hp
    simp [hp]

/-- The native off-seam part of the left cut is open in the ambient exterior cover. -/
theorem isOpen_compactNeckLeftCut_offBoundary :
    IsOpen (collaredCutSideOffBoundary
      (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)) := by
  rw [compactNeckLeftCut_offBoundary m]
  exact isOpen_coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m

/-- The native off-seam part of the right cut is open in the ambient exterior cover. -/
theorem isOpen_compactNeckRightCut_offBoundary :
    IsOpen (collaredCutSideOffBoundary
      (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)) := by
  rw [compactNeckRightCut_offBoundary m]
  exact isOpen_coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m

/-- The left half-collar takes values in the left cut carrier. -/
theorem compactNeckLeftBoundaryCollarMap_range_subset :
    range (compactNeckLeftBoundaryCollarMap m) ⊆
      coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m := by
  rw [range_compactNeckLeftBoundaryCollarMap m]
  exact inter_subset_right

/-- The right half-collar takes values in the right cut carrier. -/
theorem compactNeckRightBoundaryCollarMap_range_subset :
    range (compactNeckRightBoundaryCollarMap m) ⊆
      coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m := by
  rw [range_compactNeckRightBoundaryCollarMap m]
  exact inter_subset_right

/-- The left half-collar, corestricted to the cut, is an open embedding. -/
theorem isOpenEmbedding_compactNeckLeftBoundaryCollarMap_toCut :
    IsOpenEmbedding
      (collaredCutSideHalfCollarMap
        (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
        (compactNeckLeftBoundaryCollarMap m)
        (compactNeckLeftBoundaryCollarMap_range_subset m)) := by
  apply isOpenEmbedding_collaredCutSideHalfCollarMap
    (V := compactNeckCollarFamilyImage m)
  · exact isEmbedding_compactNeckLeftBoundaryCollarMap m
  · exact isOpen_compactNeckCollarFamilyImage m
  · exact range_compactNeckLeftBoundaryCollarMap m

/-- The right half-collar, corestricted to the cut, is an open embedding. -/
theorem isOpenEmbedding_compactNeckRightBoundaryCollarMap_toCut :
    IsOpenEmbedding
      (collaredCutSideHalfCollarMap
        (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
        (compactNeckRightBoundaryCollarMap m)
        (compactNeckRightBoundaryCollarMap_range_subset m)) := by
  apply isOpenEmbedding_collaredCutSideHalfCollarMap
    (V := compactNeckCollarFamilyImage m)
  · exact isEmbedding_compactNeckRightBoundaryCollarMap m
  · exact isOpen_compactNeckCollarFamilyImage m
  · exact range_compactNeckRightBoundaryCollarMap m

private theorem compactNeckStarSeam_subset_collarFamilyImage :
    coordinateUnlinkExteriorPlanarCompactNeckStarSeam m ⊆
      compactNeckCollarFamilyImage m := by
  intro z hz
  rw [coordinateUnlinkExteriorPlanarCompactNeckStarSeam_eq_range_transport_family] at hz
  obtain ⟨⟨a, s⟩, hs⟩ := hz
  have hzZero : z ∈
      range (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m a) := by
    rw [range_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero]
    refine ⟨s, ?_⟩
    simpa only [coordinateUnlinkExteriorPlanarNeckSphereFamily_apply] using hs
  obtain ⟨x, rfl⟩ := hzZero
  apply mem_iUnion.mpr
  refine ⟨a, ?_⟩
  exact ⟨(x, ⟨0, by norm_num [equatorCollarIntervalOpens]⟩), rfl⟩

/-- Every point of the left cut lies in a native chart or a half-collar chart. -/
theorem compactNeckLeftCut_collarCoverage
    (z : CompactNeckLeftCut m) :
    z.1 ∈ collaredCutSideOffBoundary
        (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
        (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) ∨
      z.1 ∈ range (compactNeckLeftBoundaryCollarMap m) := by
  rw [compactNeckLeftCut_offBoundary m]
  have hzC : (z.1 : CoordinateUnlinkExteriorEighthPowerPullback m) ∈
      coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m := z.2
  have hzUnion : (z.1 : CoordinateUnlinkExteriorEighthPowerPullback m) ∈
      coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ∪
        coordinateUnlinkExteriorPlanarCompactNeckStarSeam m :=
    (congrArg
      (fun S : Set (CoordinateUnlinkExteriorEighthPowerPullback m) ↦ z.1 ∈ S)
      (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier_eq m)).mp hzC
  rcases hzUnion with hzLeft | hzSeam
  · exact Or.inl hzLeft
  · right
    rw [range_compactNeckLeftBoundaryCollarMap m]
    exact ⟨compactNeckStarSeam_subset_collarFamilyImage m hzSeam,
      hzC⟩

/-- Every point of the right cut lies in a native chart or a half-collar chart. -/
theorem compactNeckRightCut_collarCoverage
    (z : CompactNeckRightCut m) :
    z.1 ∈ collaredCutSideOffBoundary
        (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
        (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) ∨
      z.1 ∈ range (compactNeckRightBoundaryCollarMap m) := by
  rw [compactNeckRightCut_offBoundary m]
  have hzC : (z.1 : CoordinateUnlinkExteriorEighthPowerPullback m) ∈
      coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m := z.2
  have hzUnion : (z.1 : CoordinateUnlinkExteriorEighthPowerPullback m) ∈
      coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m ∪
        coordinateUnlinkExteriorPlanarCompactNeckStarSeam m :=
    (congrArg
      (fun S : Set (CoordinateUnlinkExteriorEighthPowerPullback m) ↦ z.1 ∈ S)
      (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier_eq m)).mp hzC
  rcases hzUnion with hzRight | hzSeam
  · exact Or.inl hzRight
  · right
    rw [range_compactNeckRightBoundaryCollarMap m]
    exact ⟨compactNeckStarSeam_subset_collarFamilyImage m hzSeam,
      hzC⟩

/-- The explicit direct collared-cut atlas on the left compact neck cut. -/
@[instance_reducible]
noncomputable def compactNeckLeftCutChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CompactNeckLeftCut m) :=
  collaredCutSideChartedSpace
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckLeftCut_offBoundary m)
    (compactNeckLeftBoundaryCollarMap m)
    (compactNeckLeftBoundaryCollarMap_range_subset m)
    (isOpenEmbedding_compactNeckLeftBoundaryCollarMap_toCut m)
    (compactNeckLeftCut_collarCoverage m)

/-- The explicit direct collared-cut atlas on the right compact neck cut. -/
@[instance_reducible]
noncomputable def compactNeckRightCutChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CompactNeckRightCut m) :=
  collaredCutSideChartedSpace
    (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckRightCut_offBoundary m)
    (compactNeckRightBoundaryCollarMap m)
    (compactNeckRightBoundaryCollarMap_range_subset m)
    (isOpenEmbedding_compactNeckRightBoundaryCollarMap_toCut m)
    (compactNeckRightCut_collarCoverage m)

end Compact
variable {E' H' Q : Type*}
  [NormedAddCommGroup E'] [NormedSpace Real E']
  [TopologicalSpace H'] [TopologicalSpace Q] [ChartedSpace H' Q]

private theorem contMDiff_recharted_of_contMDiff
    (J : ModelWithCorners Real E' H')
    (f : EuclideanFourBallCollarDomain → Q)
    (hf : ContMDiff euclideanFourBallCollarModel J ∞ f) :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    ContMDiff coordinateUnlinkExteriorModel J ∞ f := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  intro p
  rw [contMDiffAt_iff_source_of_mem_source
    (mem_chart_source CoordinateUnlinkExteriorModelSpace p)]
  have hnat := hf p
  rw [contMDiffAt_iff_source_of_mem_source
    (mem_chart_source CoordinateUnlinkBoundaryCollarModelSpace p)] at hnat
  have hbase : coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm
        (extChartAt coordinateUnlinkExteriorModel p p) =
      extChartAt euclideanFourBallCollarModel p p := by
    change coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm
        (coordinateUnlinkExteriorModel
          (coordinateUnlinkBoundaryCollarModelHomeomorph
            (chartAt CoordinateUnlinkBoundaryCollarModelSpace p p))) =
      euclideanFourBallCollarModel
        (chartAt CoordinateUnlinkBoundaryCollarModelSpace p p)
    rw [coordinateUnlinkBoundaryCollarModel_coordinate_eq]
    simp
  have hmap : MapsTo coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm
      (range coordinateUnlinkExteriorModel)
      (range euclideanFourBallCollarModel) := by
    rintro _ ⟨q, rfl⟩
    refine ⟨coordinateUnlinkBoundaryCollarModelHomeomorph.symm q, ?_⟩
    exact coordinateUnlinkBoundaryCollarModel_coordinate_symm_eq q
  rw [← hbase] at hnat
  have hlin : ContMDiff (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4)))
      (modelWithCornersSelf Real CoordinateUnlinkBoundaryCollarModelVector) ∞
      coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm :=
    coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm.contDiff.contMDiff
  have hcomp := hnat.comp (extChartAt coordinateUnlinkExteriorModel p p)
    (hlin (extChartAt coordinateUnlinkExteriorModel p p)).contMDiffWithinAt
    hmap
  have hinv (z : EuclideanSpace Real (Fin 4))
      (hz : z ∈ range coordinateUnlinkExteriorModel) :
      (extChartAt coordinateUnlinkExteriorModel p).symm z =
        (extChartAt euclideanFourBallCollarModel p).symm
          (coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm z) := by
    have hmodelInv :
        euclideanFourBallCollarModel.symm
            (coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm z) =
          coordinateUnlinkBoundaryCollarModelHomeomorph.symm
            (coordinateUnlinkExteriorModel.symm z) := by
      have hvec : coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm z =
          euclideanFourBallCollarModel
            (coordinateUnlinkBoundaryCollarModelHomeomorph.symm
              (coordinateUnlinkExteriorModel.symm z)) := by
        rw [coordinateUnlinkBoundaryCollarModel_coordinate_symm_eq,
          coordinateUnlinkExteriorModel.right_inv hz]
      rw [hvec, euclideanFourBallCollarModel.left_inv]
    change
      (coordinateUnlinkExteriorRechartedFourBallCollarChart p).symm
          (coordinateUnlinkExteriorModel.symm z) =
        (chartAt CoordinateUnlinkBoundaryCollarModelSpace p).symm
          (euclideanFourBallCollarModel.symm
            (coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm z))
    change
      (chartAt CoordinateUnlinkBoundaryCollarModelSpace p).symm
          (coordinateUnlinkBoundaryCollarModelHomeomorph.symm
            (coordinateUnlinkExteriorModel.symm z)) =
        (chartAt CoordinateUnlinkBoundaryCollarModelSpace p).symm
          (euclideanFourBallCollarModel.symm
            (coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm z))
    rw [hmodelInv]
  apply hcomp.congr
  · intro z hz
    change f
        ((extChartAt coordinateUnlinkExteriorModel p).symm z) =
      f
        ((extChartAt euclideanFourBallCollarModel p).symm
          (coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm z))
    rw [hinv z hz]
  · change f
        ((extChartAt coordinateUnlinkExteriorModel p).symm
          (extChartAt coordinateUnlinkExteriorModel p p)) =
      f
        ((extChartAt euclideanFourBallCollarModel p).symm
          (coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm
            (extChartAt coordinateUnlinkExteriorModel p p)))
    rw [hinv (extChartAt coordinateUnlinkExteriorModel p p)]
    exact ⟨_, rfl⟩

private theorem contMDiff_to_recharted_of_contMDiff
    (J : ModelWithCorners Real E' H')
    (f : Q → EuclideanFourBallCollarDomain)
    (hf : ContMDiff J euclideanFourBallCollarModel ∞ f) :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    ContMDiff J coordinateUnlinkExteriorModel ∞ f := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  intro x
  rw [contMDiffAt_iff_target_of_mem_source
    (mem_chart_source CoordinateUnlinkExteriorModelSpace (f x))]
  have hnat := hf x
  rw [contMDiffAt_iff_target_of_mem_source
    (mem_chart_source CoordinateUnlinkBoundaryCollarModelSpace (f x))] at hnat
  refine ⟨hnat.1, ?_⟩
  have hlin : ContMDiff
      (modelWithCornersSelf Real CoordinateUnlinkBoundaryCollarModelVector)
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
      coordinateUnlinkBoundaryCollarVectorLinearEquiv :=
    coordinateUnlinkBoundaryCollarVectorLinearEquiv.contDiff.contMDiff
  have hcomp := (hlin
    (extChartAt euclideanFourBallCollarModel (f x) (f x))).comp x hnat.2
  exact hcomp.congr_of_eventuallyEq <|
    Filter.Eventually.of_forall fun y ↦ by
      change coordinateUnlinkExteriorModel
          (coordinateUnlinkBoundaryCollarModelHomeomorph
            (chartAt CoordinateUnlinkBoundaryCollarModelSpace (f x) (f y))) =
        coordinateUnlinkBoundaryCollarVectorLinearEquiv
          (euclideanFourBallCollarModel
            (chartAt CoordinateUnlinkBoundaryCollarModelSpace (f x) (f y)))
      exact coordinateUnlinkBoundaryCollarModel_coordinate_eq _

private theorem contMDiff_recharted_leftHalf :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    ContMDiff coordinateUnlinkExteriorModel
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real)) ∞
      compactNeckLeftHalfParameter :=
  contMDiff_recharted_of_contMDiff _ _
    contMDiff_compactNeckLeftHalfParameter

private theorem contMDiff_recharted_rightHalf :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    ContMDiff coordinateUnlinkExteriorModel
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real)) ∞
      compactNeckRightHalfParameter :=
  contMDiff_recharted_of_contMDiff _ _
    contMDiff_compactNeckRightHalfParameter

private def compactNeckPositiveHalfDomainOpens :
    Opens EuclideanFourBallCollarDomain :=
  ⟨{p | 0 < (p.2.1.1 : Real)}, by
    apply isOpen_lt continuous_const
    fun_prop⟩

private def compactNeckNegativeFullCollarOpens :
    Opens (Sphere 3 × EquatorCollarInterval) :=
  ⟨{p | (p.2.1 : Real) < 0}, by
    apply isOpen_lt
    · fun_prop
    · fun_prop⟩

private def compactNeckPositiveFullCollarOpens :
    Opens (Sphere 3 × EquatorCollarInterval) :=
  ⟨{p | 0 < (p.2.1 : Real)}, by
    apply isOpen_lt continuous_const
    fun_prop⟩

private def compactNeckLeftInteriorInverse
    (q : compactNeckNegativeFullCollarOpens) :
    EuclideanFourBallCollarDomain :=
  (q.1.1, ⟨⟨-(q.1.2.1 : Real), by
    constructor
    · exact neg_nonneg.mpr q.2.le
    · have h := q.1.2.2.1
      linarith⟩, by
        have h := q.1.2.2.1
        have h' := neg_lt_neg h
        change -(q.1.2.1 : Real) < 1 / 2
        simpa only [neg_neg] using h'⟩)

private def compactNeckRightInteriorInverse
    (q : compactNeckPositiveFullCollarOpens) :
    EuclideanFourBallCollarDomain :=
  (q.1.1, ⟨⟨(q.1.2.1 : Real), q.2.le, q.1.2.2.2.le⟩,
    q.1.2.2.2⟩)

private theorem contMDiff_compactNeckLeftInteriorInverse_natural :
    ContMDiff
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real))
      euclideanFourBallCollarModel ∞
      compactNeckLeftInteriorInverse := by
  unfold compactNeckLeftInteriorInverse
  have hval : ContMDiff
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real))
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real)) ∞
      (Subtype.val : compactNeckNegativeFullCollarOpens →
        Sphere 3 × EquatorCollarInterval) :=
    contMDiff_subtype_val
  have hfst : ContMDiff
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))) ∞
      (fun q : compactNeckNegativeFullCollarOpens ↦ q.1.1) :=
    contMDiff_fst.comp hval
  apply ContMDiff.prodMk hfst
  rw [← ContMDiff.subtypeVal_comp_iff euclideanFourBallCollarIntervalOpens]
  apply contMDiff_iff_comp_subtypeVal_Icc.mpr
  constructor
  · fun_prop
  · have ht : ContMDiff
        ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
          (modelWithCornersSelf Real Real))
        (modelWithCornersSelf Real Real) ∞
        (fun q : compactNeckNegativeFullCollarOpens ↦
          -(q.1.2.1 : Real)) := by
      have hsnd : ContMDiff
          ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
            (modelWithCornersSelf Real Real))
          (modelWithCornersSelf Real Real) ∞
          (fun q : compactNeckNegativeFullCollarOpens ↦ q.1.2) :=
        contMDiff_snd.comp hval
      have hreal : ContMDiff
          ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
            (modelWithCornersSelf Real Real))
          (modelWithCornersSelf Real Real) ∞
          (fun q : compactNeckNegativeFullCollarOpens ↦
            (q.1.2.1 : Real)) :=
        contMDiff_subtype_val.comp hsnd
      exact hreal.neg
    exact ht.congr fun _ ↦ rfl

private theorem contMDiff_compactNeckRightInteriorInverse_natural :
    ContMDiff
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real))
      euclideanFourBallCollarModel ∞
      compactNeckRightInteriorInverse := by
  unfold compactNeckRightInteriorInverse
  have hval : ContMDiff
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real))
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real)) ∞
      (Subtype.val : compactNeckPositiveFullCollarOpens →
        Sphere 3 × EquatorCollarInterval) :=
    contMDiff_subtype_val
  have hfst : ContMDiff
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))) ∞
      (fun q : compactNeckPositiveFullCollarOpens ↦ q.1.1) :=
    contMDiff_fst.comp hval
  apply ContMDiff.prodMk hfst
  rw [← ContMDiff.subtypeVal_comp_iff euclideanFourBallCollarIntervalOpens]
  apply contMDiff_iff_comp_subtypeVal_Icc.mpr
  constructor
  · fun_prop
  · have ht : ContMDiff
        ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
          (modelWithCornersSelf Real Real))
        (modelWithCornersSelf Real Real) ∞
        (fun q : compactNeckPositiveFullCollarOpens ↦
          (q.1.2.1 : Real)) := by
      have hsnd : ContMDiff
          ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
            (modelWithCornersSelf Real Real))
          (modelWithCornersSelf Real Real) ∞
          (fun q : compactNeckPositiveFullCollarOpens ↦ q.1.2) :=
        contMDiff_snd.comp hval
      exact contMDiff_subtype_val.comp hsnd
    exact ht.congr fun _ ↦ rfl

private def compactNeckLeftInteriorEquiv :
    compactNeckPositiveHalfDomainOpens ≃
      compactNeckNegativeFullCollarOpens where
  toFun p := ⟨compactNeckLeftHalfParameter p.1, by
    change -(p.1.2.1.1 : Real) < 0
    exact neg_lt_zero.mpr p.2⟩
  invFun q := ⟨compactNeckLeftInteriorInverse q, by
    change 0 < -(q.1.2.1 : Real)
    exact neg_pos.mpr q.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Subtype.ext
      simp [compactNeckLeftInteriorInverse, compactNeckLeftHalfParameter]
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [compactNeckLeftInteriorInverse, compactNeckLeftHalfParameter]

private def compactNeckRightInteriorEquiv :
    compactNeckPositiveHalfDomainOpens ≃
      compactNeckPositiveFullCollarOpens where
  toFun p := ⟨compactNeckRightHalfParameter p.1, p.2⟩
  invFun q := ⟨compactNeckRightInteriorInverse q, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def compactNeckLeftInteriorDiffeomorph :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    compactNeckPositiveHalfDomainOpens ≃ₘ^∞⟮
      coordinateUnlinkExteriorModel,
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real))⟯
      compactNeckNegativeFullCollarOpens := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  refine
    { toEquiv := compactNeckLeftInteriorEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · rw [← ContMDiff.subtypeVal_comp_iff compactNeckNegativeFullCollarOpens]
    exact (contMDiff_recharted_leftHalf.comp contMDiff_subtype_val).congr
      fun _ ↦ rfl
  · rw [← ContMDiff.subtypeVal_comp_iff compactNeckPositiveHalfDomainOpens]
    exact (contMDiff_to_recharted_of_contMDiff _ _
      contMDiff_compactNeckLeftInteriorInverse_natural).congr fun _ ↦ rfl

private noncomputable def compactNeckRightInteriorDiffeomorph :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    compactNeckPositiveHalfDomainOpens ≃ₘ^∞⟮
      coordinateUnlinkExteriorModel,
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real))⟯
      compactNeckPositiveFullCollarOpens := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  refine
    { toEquiv := compactNeckRightInteriorEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · rw [← ContMDiff.subtypeVal_comp_iff compactNeckPositiveFullCollarOpens]
    exact (contMDiff_recharted_rightHalf.comp contMDiff_subtype_val).congr
      fun _ ↦ rfl
  · rw [← ContMDiff.subtypeVal_comp_iff compactNeckPositiveHalfDomainOpens]
    exact (contMDiff_to_recharted_of_contMDiff _ _
      contMDiff_compactNeckRightInteriorInverse_natural).congr fun _ ↦ rfl

universe uM uN uH uK uE uF

private theorem isLocalDiffeomorphAt_of_open_diffeomorph
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace Real F]
    {H : Type uH} [TopologicalSpace H]
    {K : Type uK} [TopologicalSpace K]
    (I : ModelWithCorners Real E H) (J : ModelWithCorners Real F K)
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    {N : Type uN} [TopologicalSpace N] [ChartedSpace K N]
    (U : Opens M) (V : Opens N) (f : M → N)
    (e : U ≃ₘ^∞⟮I, J⟯ V)
    (heq : ∀ p : U, (e p).1 = f p.1)
    (x : M) (hx : x ∈ U) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  let u : U := ⟨x, hx⟩
  let hU : IsLocalDiffeomorphAt I I ∞
      (Subtype.val : U → M) u :=
    isLocalDiffeomorph_opensSubtypeVal I U u
  let hV : IsLocalDiffeomorphAt J J ∞
      (Subtype.val : V → N) (e u) :=
    isLocalDiffeomorph_opensSubtypeVal J V (e u)
  let Φ0 : PartialDiffeomorph I J M V ∞ :=
    hU.localInverse.trans e.toPartialDiffeomorph
  let Φ : PartialDiffeomorph I J M N ∞ :=
    Φ0.trans (Classical.choose hV)
  refine ⟨Φ, ?_, ?_⟩
  · change x ∈ Φ0.source ∩ Φ0 ⁻¹' (Classical.choose hV).source
    refine ⟨?_, ?_⟩
    · change x ∈ hU.localInverse.source ∩
        hU.localInverse ⁻¹' e.toPartialDiffeomorph.source
      refine ⟨hU.localInverse_mem_source, ?_⟩
      change hU.localInverse x ∈ (Set.univ : Set U)
      trivial
    · change e (hU.localInverse x) ∈ (Classical.choose hV).source
      rw [hU.localInverse_left_inv hU.localInverse_mem_target]
      exact (Classical.choose_spec hV).1
  · intro y hy
    have hyInv : y ∈ hU.localInverse.source := hy.1.1
    have hyV : Φ0 y ∈ (Classical.choose hV).source := hy.2
    calc
      f y = f (hU.localInverse y : M) :=
        congrArg f (hU.localInverse_right_inv hyInv).symm
      _ = (e (hU.localInverse y) : N) := (heq _).symm
      _ = (Φ0 y : V) := rfl
      _ = (Classical.choose hV) (Φ0 y) :=
        (Classical.choose_spec hV).2 hyV
      _ = Φ y := rfl

private theorem isLocalDiffeomorphOn_compactNeckLeftHalfParameter :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real)) ∞
      compactNeckLeftHalfParameter compactNeckPositiveHalfDomainOpens := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  intro p
  exact isLocalDiffeomorphAt_of_open_diffeomorph
    coordinateUnlinkExteriorModel
    ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
      (modelWithCornersSelf Real Real))
    compactNeckPositiveHalfDomainOpens compactNeckNegativeFullCollarOpens
    compactNeckLeftHalfParameter compactNeckLeftInteriorDiffeomorph
    (fun _ ↦ rfl) p.1 p.2

private theorem isLocalDiffeomorphOn_compactNeckRightHalfParameter :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
        (modelWithCornersSelf Real Real)) ∞
      compactNeckRightHalfParameter compactNeckPositiveHalfDomainOpens := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  intro p
  exact isLocalDiffeomorphAt_of_open_diffeomorph
    coordinateUnlinkExteriorModel
    ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))).prod
      (modelWithCornersSelf Real Real))
    compactNeckPositiveHalfDomainOpens compactNeckPositiveFullCollarOpens
    compactNeckRightHalfParameter compactNeckRightInteriorDiffeomorph
    (fun _ ↦ rfl) p.1 p.2

private theorem isLocalDiffeomorphAt_congr_of_eqOn_open
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace Real F]
    {H : Type uH} [TopologicalSpace H]
    {K : Type uK} [TopologicalSpace K]
    (I : ModelWithCorners Real E H) (J : ModelWithCorners Real F K)
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    {N : Type uN} [TopologicalSpace N] [ChartedSpace K N]
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

section Compact

variable (m : ℕ) [NeZero m]

local instance smoothStandardPowerChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
  standardUnlinkPowerPullbackChartedSpace m

local instance smoothCompactExteriorPowerChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
  coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m

/-- The all-label left half-collar is smooth for the recharted collar-family atlas. -/
theorem contMDiff_compactNeckLeftBoundaryCollarMap :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      isManifold_coordinateUnlinkExteriorEighthPowerPullback m
    ContMDiff coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
      (compactNeckLeftBoundaryCollarMap m) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  let _ : IsManifold
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  have hsnd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × EuclideanFourBallCollarDomain →
        EuclideanFourBallCollarDomain) := by
    exact SplittingSpheres.IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
        (isLocalHomeomorph_discreteProdSnd
          (D := ZMod m) (P := EuclideanFourBallCollarDomain))
  have hcomponent (a : ZMod m) :
      ContMDiff coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
        (fun p : EuclideanFourBallCollarDomain ↦
          compactNeckLeftBoundaryCollarMap m (a, p)) := by
    have h := (contMDiff_compactNeckOrientedCollarMap m a).comp
      contMDiff_recharted_leftHalf
    exact h.congr fun _ ↦ rfl
  intro x
  have hx := ((hcomponent x.1).comp hsnd.contMDiff) x
  apply hx.congr_of_eventuallyEq
  filter_upwards [
    ((isOpen_discrete ({x.1} : Set (ZMod m))).preimage continuous_fst).mem_nhds
      (by simp)] with y hy
  change compactNeckLeftBoundaryCollarMap m y =
    compactNeckLeftBoundaryCollarMap m (x.1, y.2)
  simp only [mem_preimage, mem_singleton_iff] at hy
  rcases y with ⟨b, q⟩
  change b = x.1 at hy
  subst b
  rfl

/-- The all-label right half-collar is smooth for the recharted collar-family atlas. -/
theorem contMDiff_compactNeckRightBoundaryCollarMap :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      isManifold_coordinateUnlinkExteriorEighthPowerPullback m
    ContMDiff coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
      (compactNeckRightBoundaryCollarMap m) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  let _ : IsManifold
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  have hsnd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × EuclideanFourBallCollarDomain →
        EuclideanFourBallCollarDomain) := by
    exact SplittingSpheres.IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
        (isLocalHomeomorph_discreteProdSnd
          (D := ZMod m) (P := EuclideanFourBallCollarDomain))
  have hcomponent (a : ZMod m) :
      ContMDiff coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
        (fun p : EuclideanFourBallCollarDomain ↦
          compactNeckRightBoundaryCollarMap m (a, p)) := by
    have h := (contMDiff_compactNeckOrientedCollarMap m a).comp
      contMDiff_recharted_rightHalf
    exact h.congr fun _ ↦ rfl
  intro x
  have hx := ((hcomponent x.1).comp hsnd.contMDiff) x
  apply hx.congr_of_eventuallyEq
  filter_upwards [
    ((isOpen_discrete ({x.1} : Set (ZMod m))).preimage continuous_fst).mem_nhds
      (by simp)] with y hy
  change compactNeckRightBoundaryCollarMap m y =
    compactNeckRightBoundaryCollarMap m (x.1, y.2)
  simp only [mem_preimage, mem_singleton_iff] at hy
  rcases y with ⟨b, q⟩
  change b = x.1 at hy
  subst b
  rfl

private theorem isLocalDiffeomorphOn_compactNeckLeftBoundaryCollarComponent
    (a : ZMod m) :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        EuclideanFourBallCollarDomain :=
      isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
    letI : IsManifold
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      isManifold_coordinateUnlinkExteriorEighthPowerPullback m
    IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (fun p : EuclideanFourBallCollarDomain ↦
        compactNeckLeftBoundaryCollarMap m (a, p))
      compactNeckPositiveHalfDomainOpens := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  let _ : IsManifold
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  intro p
  have hhalf := isLocalDiffeomorphOn_compactNeckLeftHalfParameter p
  have horiented :=
    isLocalDiffeomorph_compactNeckOrientedCollarMap m a
      (compactNeckLeftHalfParameter p.1)
  have hcomp := hhalf.comp coordinateUnlinkExteriorModel
    (CoordinateUnlinkExteriorEighthPowerPullback m) horiented
  simpa [compactNeckLeftBoundaryCollarMap, Function.comp_def] using hcomp

private theorem isLocalDiffeomorphOn_compactNeckRightBoundaryCollarComponent
    (a : ZMod m) :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        EuclideanFourBallCollarDomain :=
      isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
    letI : IsManifold
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      isManifold_coordinateUnlinkExteriorEighthPowerPullback m
    IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (fun p : EuclideanFourBallCollarDomain ↦
        compactNeckRightBoundaryCollarMap m (a, p))
      compactNeckPositiveHalfDomainOpens := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  let _ : IsManifold
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  intro p
  have hhalf := isLocalDiffeomorphOn_compactNeckRightHalfParameter p
  have horiented :=
    isLocalDiffeomorph_compactNeckOrientedCollarMap m a
      (compactNeckRightHalfParameter p.1)
  have hcomp := hhalf.comp coordinateUnlinkExteriorModel
    (CoordinateUnlinkExteriorEighthPowerPullback m) horiented
  simpa [compactNeckRightBoundaryCollarMap, Function.comp_def] using hcomp

/-- The left half-collar is a local diffeomorphism exactly over the native off-seam overlap. -/
theorem isLocalDiffeomorphOn_compactNeckLeftBoundaryCollarMap :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      isManifold_coordinateUnlinkExteriorEighthPowerPullback m
    IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (compactNeckLeftBoundaryCollarMap m)
      ((compactNeckLeftBoundaryCollarMap m) ⁻¹'
        collaredCutSideOffBoundary
          (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
          (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  let _ : IsManifold
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  have hsnd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × EuclideanFourBallCollarDomain →
        EuclideanFourBallCollarDomain) := by
    exact SplittingSpheres.IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
        (isLocalHomeomorph_discreteProdSnd
          (D := ZMod m) (P := EuclideanFourBallCollarDomain))
  intro x
  have hxpos : x.1.2 ∈ compactNeckPositiveHalfDomainOpens :=
    (compactNeckLeftBoundaryCollarMap_mem_offBoundary_iff m x.1).mp x.2
  have hcomponent :=
    isLocalDiffeomorphOn_compactNeckLeftBoundaryCollarComponent
      m x.1.1 ⟨x.1.2, hxpos⟩
  have hfixed : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (fun y : ZMod m × EuclideanFourBallCollarDomain ↦
        compactNeckLeftBoundaryCollarMap m (x.1.1, y.2)) x.1 := by
    simpa [Function.comp_def] using
      (hsnd x.1).comp coordinateUnlinkExteriorModel
        (CoordinateUnlinkExteriorEighthPowerPullback m) hcomponent
  let W : Set (ZMod m × EuclideanFourBallCollarDomain) :=
    (Prod.fst : ZMod m × EuclideanFourBallCollarDomain → ZMod m) ⁻¹'
      ({x.1.1} : Set (ZMod m))
  refine isLocalDiffeomorphAt_congr_of_eqOn_open
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel hfixed W
      ((isOpen_discrete ({x.1.1} : Set (ZMod m))).preimage continuous_fst)
      (by simp [W]) ?_
  intro y hy
  change y.1 ∈ ({x.1.1} : Set (ZMod m)) at hy
  simp only [mem_singleton_iff] at hy
  rcases y with ⟨b, q⟩
  change b = x.1.1 at hy
  subst b
  rfl

/-- The right half-collar is a local diffeomorphism exactly over the native off-seam overlap. -/
theorem isLocalDiffeomorphOn_compactNeckRightBoundaryCollarMap :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      isManifold_coordinateUnlinkExteriorEighthPowerPullback m
    IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (compactNeckRightBoundaryCollarMap m)
      ((compactNeckRightBoundaryCollarMap m) ⁻¹'
        collaredCutSideOffBoundary
          (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
          (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  let _ : IsManifold
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  have hsnd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × EuclideanFourBallCollarDomain →
        EuclideanFourBallCollarDomain) := by
    exact SplittingSpheres.IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
        (isLocalHomeomorph_discreteProdSnd
          (D := ZMod m) (P := EuclideanFourBallCollarDomain))
  intro x
  have hxpos : x.1.2 ∈ compactNeckPositiveHalfDomainOpens :=
    (compactNeckRightBoundaryCollarMap_mem_offBoundary_iff m x.1).mp x.2
  have hcomponent :=
    isLocalDiffeomorphOn_compactNeckRightBoundaryCollarComponent
      m x.1.1 ⟨x.1.2, hxpos⟩
  have hfixed : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (fun y : ZMod m × EuclideanFourBallCollarDomain ↦
        compactNeckRightBoundaryCollarMap m (x.1.1, y.2)) x.1 := by
    simpa [Function.comp_def] using
      (hsnd x.1).comp coordinateUnlinkExteriorModel
        (CoordinateUnlinkExteriorEighthPowerPullback m) hcomponent
  let W : Set (ZMod m × EuclideanFourBallCollarDomain) :=
    (Prod.fst : ZMod m × EuclideanFourBallCollarDomain → ZMod m) ⁻¹'
      ({x.1.1} : Set (ZMod m))
  refine isLocalDiffeomorphAt_congr_of_eqOn_open
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel hfixed W
      ((isOpen_discrete ({x.1.1} : Set (ZMod m))).preimage continuous_fst)
      (by simp [W]) ?_
  intro y hy
  change y.1 ∈ ({x.1.1} : Set (ZMod m)) at hy
  simp only [mem_singleton_iff] at hy
  rcases y with ⟨b, q⟩
  change b = x.1.1 at hy
  subst b
  rfl

end Compact

section Compact

variable (m : ℕ) [NeZero m]

local instance compactExteriorPowerChartedSpaceForCut :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
  coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m

local instance compactExteriorPowerIsManifoldForCut :
    IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
  isManifold_coordinateUnlinkExteriorEighthPowerPullback m

local instance compactNeckBoundaryCollarFamilyChartedSpaceForCut :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m × EuclideanFourBallCollarDomain) :=
  coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m

local instance compactNeckBoundaryCollarFamilyIsManifoldForCut :
    IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
  isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m

/-- The direct left cut atlas makes the left compact neck cut a smooth manifold with boundary. -/
theorem isManifold_compactNeckLeftCut :
    letI := compactNeckLeftCutChartedSpace m
    IsManifold coordinateUnlinkExteriorModel ∞
      (CompactNeckLeftCut m) :=
  isManifold_collaredCutSideChartedSpace_of_localDiffeomorphOn
    coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckLeftCut_offBoundary m)
    (compactNeckLeftBoundaryCollarMap m)
    (compactNeckLeftBoundaryCollarMap_range_subset m)
    (isOpenEmbedding_compactNeckLeftBoundaryCollarMap_toCut m)
    (compactNeckLeftCut_collarCoverage m)
    (isLocalDiffeomorphOn_compactNeckLeftBoundaryCollarMap m)

/-- The direct right cut atlas makes the right compact neck cut a smooth manifold with boundary. -/
theorem isManifold_compactNeckRightCut :
    letI := compactNeckRightCutChartedSpace m
    IsManifold coordinateUnlinkExteriorModel ∞
      (CompactNeckRightCut m) :=
  isManifold_collaredCutSideChartedSpace_of_localDiffeomorphOn
    coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckRightCut_offBoundary m)
    (compactNeckRightBoundaryCollarMap m)
    (compactNeckRightBoundaryCollarMap_range_subset m)
    (isOpenEmbedding_compactNeckRightBoundaryCollarMap_toCut m)
    (compactNeckRightCut_collarCoverage m)
    (isLocalDiffeomorphOn_compactNeckRightBoundaryCollarMap m)

/-- The left cut inclusion into the ambient exterior cover is smooth. -/
theorem contMDiff_compactNeckLeftCut_subtypeVal :
    letI := compactNeckLeftCutChartedSpace m
    ContMDiff coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
      (Subtype.val : CompactNeckLeftCut m →
          CoordinateUnlinkExteriorEighthPowerPullback m) :=
  contMDiff_collaredCutSideSubtypeVal_of_localDiffeomorphOn
    coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckLeftCut_offBoundary m)
    (compactNeckLeftBoundaryCollarMap m)
    (compactNeckLeftBoundaryCollarMap_range_subset m)
    (isOpenEmbedding_compactNeckLeftBoundaryCollarMap_toCut m)
    (compactNeckLeftCut_collarCoverage m)
    (isLocalDiffeomorphOn_compactNeckLeftBoundaryCollarMap m)
    (contMDiff_compactNeckLeftBoundaryCollarMap m)

/-- The right cut inclusion into the ambient exterior cover is smooth. -/
theorem contMDiff_compactNeckRightCut_subtypeVal :
    letI := compactNeckRightCutChartedSpace m
    ContMDiff coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
      (Subtype.val : CompactNeckRightCut m →
          CoordinateUnlinkExteriorEighthPowerPullback m) :=
  contMDiff_collaredCutSideSubtypeVal_of_localDiffeomorphOn
    coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckRightCut_offBoundary m)
    (compactNeckRightBoundaryCollarMap m)
    (compactNeckRightBoundaryCollarMap_range_subset m)
    (isOpenEmbedding_compactNeckRightBoundaryCollarMap_toCut m)
    (compactNeckRightCut_collarCoverage m)
    (isLocalDiffeomorphOn_compactNeckRightBoundaryCollarMap m)
    (contMDiff_compactNeckRightBoundaryCollarMap m)

private theorem compactNeckLeftBoundaryPreimage :
    compactNeckLeftBoundaryCollarMap m ⁻¹'
        (coordinateUnlinkExteriorModel.boundary
            (CoordinateUnlinkExteriorEighthPowerPullback m) ∪
          coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) =
      coordinateUnlinkExteriorModel.boundary
        (ZMod m × EuclideanFourBallCollarDomain) :=
  (preimage_compactNeckLeftBoundaryCollarMap_ambientBoundary_union_seam m).trans
    (coordinateUnlinkExteriorRechartedFourBallCollarFamily_boundary m).symm

private theorem compactNeckRightBoundaryPreimage :
    compactNeckRightBoundaryCollarMap m ⁻¹'
        (coordinateUnlinkExteriorModel.boundary
            (CoordinateUnlinkExteriorEighthPowerPullback m) ∪
          coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) =
      coordinateUnlinkExteriorModel.boundary
        (ZMod m × EuclideanFourBallCollarDomain) :=
  (preimage_compactNeckRightBoundaryCollarMap_ambientBoundary_union_seam m).trans
    (coordinateUnlinkExteriorRechartedFourBallCollarFamily_boundary m).symm

/-- The left cut boundary is the old ambient radial boundary together with the full seam. -/
theorem boundary_compactNeckLeftCut :
    letI := compactNeckLeftCutChartedSpace m
    coordinateUnlinkExteriorModel.boundary
        (CompactNeckLeftCut m) =
      (Subtype.val : CompactNeckLeftCut m →
          CoordinateUnlinkExteriorEighthPowerPullback m) ⁻¹'
        (coordinateUnlinkExteriorModel.boundary
            (CoordinateUnlinkExteriorEighthPowerPullback m) ∪
          coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) :=
  boundary_collaredCutSideChartedSpace_of_localDiffeomorphOn
    coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckLeftCut_offBoundary m)
    (compactNeckLeftBoundaryCollarMap m)
    (compactNeckLeftBoundaryCollarMap_range_subset m)
    (isOpenEmbedding_compactNeckLeftBoundaryCollarMap_toCut m)
    (compactNeckLeftCut_collarCoverage m)
    (isLocalDiffeomorphOn_compactNeckLeftBoundaryCollarMap m)
    (by simp) (compactNeckLeftBoundaryPreimage m)

/-- The right cut boundary is the old ambient radial boundary together with the full seam. -/
theorem boundary_compactNeckRightCut :
    letI := compactNeckRightCutChartedSpace m
    coordinateUnlinkExteriorModel.boundary
        (CompactNeckRightCut m) =
      (Subtype.val : CompactNeckRightCut m →
          CoordinateUnlinkExteriorEighthPowerPullback m) ⁻¹'
        (coordinateUnlinkExteriorModel.boundary
            (CoordinateUnlinkExteriorEighthPowerPullback m) ∪
          coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) :=
  boundary_collaredCutSideChartedSpace_of_localDiffeomorphOn
    coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckRightCut_offBoundary m)
    (compactNeckRightBoundaryCollarMap m)
    (compactNeckRightBoundaryCollarMap_range_subset m)
    (isOpenEmbedding_compactNeckRightBoundaryCollarMap_toCut m)
    (compactNeckRightCut_collarCoverage m)
    (isLocalDiffeomorphOn_compactNeckRightBoundaryCollarMap m)
    (by simp) (compactNeckRightBoundaryPreimage m)

end Compact

end

end SplittingSpheres
