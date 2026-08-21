/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.CoordinateUnlinkExteriorCommonModelFourBall
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckCompactCutSmooth

/-!
# Direct common-model atlas for the signed seam

This file equips the signed collar `Sphere 3 × EquatorCollarInterval` with a direct atlas in the
common coordinate-unlink exterior model. The interval is charted into the strict interior of the
one-dimensional Euclidean half-space, the product atlas is recharted through the existing
boundary-collar model carrier equivalence, and the construction is pulled back componentwise to
a discrete `ZMod m` family.

The resulting family is a boundaryless smooth manifold for every natural number `m`, with no
`NeZero m` assumption. Its signed-time coordinate is smooth. Forgetting the sign gives the
continuous labelled half-collar reparametrization used by the two seam branches; it is not claimed
to be smooth across time zero. On the two strict halves, explicit homeomorphisms record the two
linear reparametrizations.

No attaching, pushout, capping, or strict-half smoothness statement is asserted here.
-/

@[expose] public section

open Function Set Topology TopologicalSpace WithLp
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-- The midpoint witnesses that the signed collar interval is nonempty. -/
instance signedSeamIntervalNonempty : Nonempty EquatorCollarInterval :=
  ⟨⟨0, by norm_num [equatorCollarIntervalOpens]⟩⟩

/-- The closed interval used only to reuse its native half-space chart. -/
instance signedSeamClosedIntervalFact :
    Fact ((-(1 / 2 : ℝ)) < (1 / 2 : ℝ)) := ⟨by norm_num⟩

/-- The ordinary open interval as the interior open subspace of the matching
closed interval. -/
def signedSeamClosedIntervalInteriorOpens :
    Opens (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
  ⟨{t | -(1 / 2 : ℝ) < t.1 ∧ t.1 < 1 / 2}, by
    exact (isOpen_lt continuous_const continuous_subtype_val).inter
      (isOpen_lt continuous_subtype_val continuous_const)⟩

instance signedSeamClosedIntervalInteriorNonempty :
    Nonempty signedSeamClosedIntervalInteriorOpens :=
  ⟨⟨⟨0, by norm_num⟩, by norm_num [signedSeamClosedIntervalInteriorOpens]⟩⟩

/-- The identity on real values identifies the two presentations of the open
signed interval. -/
def signedSeamIntervalClosedInteriorHomeomorph :
    EquatorCollarInterval ≃ₜ signedSeamClosedIntervalInteriorOpens where
  toFun t := ⟨⟨t.1, t.2.1.le, t.2.2.le⟩, t.2⟩
  invFun t := ⟨t.1.1, t.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Shift the open equator-collar interval into the strict interior of the
one-dimensional Euclidean half-space, using the native left chart on the
matching closed interval. -/
def signedSeamIntervalHalfSpaceChart :
    OpenPartialHomeomorph EquatorCollarInterval (EuclideanHalfSpace 1) :=
  signedSeamIntervalClosedInteriorHomeomorph.toOpenPartialHomeomorph.trans
    ((IccLeftChart (-(1 / 2 : ℝ)) (1 / 2 : ℝ)).subtypeRestr
      signedSeamClosedIntervalInteriorNonempty)

@[simp]
theorem signedSeamIntervalHalfSpaceChart_apply
    (t : EquatorCollarInterval) :
    (signedSeamIntervalHalfSpaceChart t).val 0 = (t.1 : ℝ) + 1 / 2 := by
  simp [signedSeamIntervalHalfSpaceChart,
    signedSeamIntervalClosedInteriorHomeomorph,
    OpenPartialHomeomorph.subtypeRestr_coe, IccLeftChart_apply]

theorem signedSeamIntervalHalfSpaceChart_source :
    signedSeamIntervalHalfSpaceChart.source = univ := by
  ext t
  simp only [signedSeamIntervalHalfSpaceChart,
    OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, mem_inter_iff, mem_univ,
    true_and, mem_preimage,
    OpenPartialHomeomorph.subtypeRestr_source]
  change ((t.1 : ℝ) < 1 / 2) ↔ True
  exact ⟨fun _ ↦ trivial, fun _ ↦ t.2.2⟩

theorem isOpenEmbedding_signedSeamIntervalHalfSpaceChart :
    IsOpenEmbedding signedSeamIntervalHalfSpaceChart :=
  signedSeamIntervalHalfSpaceChart.isOpenEmbedding
    signedSeamIntervalHalfSpaceChart_source

/-- The singleton half-space atlas on the signed interval. -/
@[instance_reducible]
def signedSeamIntervalChartedSpace :
    ChartedSpace (EuclideanHalfSpace 1) EquatorCollarInterval :=
  isOpenEmbedding_signedSeamIntervalHalfSpaceChart.singletonChartedSpace

theorem isManifold_signedSeamInterval :
    letI := signedSeamIntervalChartedSpace
    IsManifold (modelWithCornersEuclideanHalfSpace 1) ∞
      EquatorCollarInterval :=
  isOpenEmbedding_signedSeamIntervalHalfSpaceChart.isManifold_singleton

theorem signedSeamInterval_boundary :
    letI := signedSeamIntervalChartedSpace
    (modelWithCornersEuclideanHalfSpace 1).boundary
        EquatorCollarInterval = ∅ := by
  let _ := signedSeamIntervalChartedSpace
  let _ : IsManifold (modelWithCornersEuclideanHalfSpace 1) ∞
      EquatorCollarInterval := isManifold_signedSeamInterval
  ext t
  change (modelWithCornersEuclideanHalfSpace 1).IsBoundaryPoint t ↔ False
  rw [ModelWithCorners.isBoundaryPoint_iff]
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  rw [extChartAt_coe]
  rw [isOpenEmbedding_signedSeamIntervalHalfSpaceChart.singletonChartedSpace_chartAt_eq]
  simp only [comp_apply, mem_ofPred_eq,
    modelWithCornersEuclideanHalfSpace_apply,
    signedSeamIntervalHalfSpaceChart_apply]
  change (0 : ℝ) = (t.1 : ℝ) + 1 / 2 ↔ False
  constructor
  · intro ht
    linarith [t.2.1]
  · exact False.elim

theorem contMDiff_signedSeamInterval_value :
    letI := signedSeamIntervalChartedSpace
    ContMDiff (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun t : EquatorCollarInterval ↦ (t.1 : ℝ)) := by
  let _ := signedSeamIntervalChartedSpace
  let _ : IsManifold (modelWithCornersEuclideanHalfSpace 1) ∞
      EquatorCollarInterval := isManifold_signedSeamInterval
  have hchart : ContMDiff (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersEuclideanHalfSpace 1) ∞
      signedSeamIntervalHalfSpaceChart :=
    contMDiff_isOpenEmbedding isOpenEmbedding_signedSeamIntervalHalfSpaceChart
  have hmodel : ContMDiff (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ∞
      (fun z : EuclideanHalfSpace 1 ↦ z.val) :=
    (modelWithCornersEuclideanHalfSpace 1).contMDiff.congr fun _ ↦ rfl
  have heval : ContDiff ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin 1) ↦ z 0) := by fun_prop
  have hcoord : ContMDiff (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : EuclideanHalfSpace 1 ↦ z.val 0 - 1 / 2) :=
    (heval.comp_contMDiff hmodel).sub contMDiff_const
  exact (hcoord.comp hchart).congr fun t ↦ by
    change (t.1 : ℝ) =
      (signedSeamIntervalHalfSpaceChart t).val 0 - 1 / 2
    rw [signedSeamIntervalHalfSpaceChart_apply]
    ring

/-- The product atlas on the unlabelled signed collar in the boundary-collar model. -/
@[instance_reducible]
def signedSeamCollarBoundaryChartedSpace :
    ChartedSpace CoordinateUnlinkBoundaryCollarModelSpace
      (Sphere 3 × EquatorCollarInterval) :=
  let _ := signedSeamIntervalChartedSpace
  inferInstance

theorem isManifold_signedSeamCollarBoundary :
    letI := signedSeamCollarBoundaryChartedSpace
    IsManifold coordinateUnlinkBoundaryCollarModel ∞
      (Sphere 3 × EquatorCollarInterval) := by
  let _ := signedSeamIntervalChartedSpace
  let _ : IsManifold (modelWithCornersEuclideanHalfSpace 1) ∞
      EquatorCollarInterval := isManifold_signedSeamInterval
  exact inferInstance

theorem signedSeamCollarBoundary_boundary :
    letI := signedSeamCollarBoundaryChartedSpace
    coordinateUnlinkBoundaryCollarModel.boundary
        (Sphere 3 × EquatorCollarInterval) = ∅ := by
  let _ := signedSeamIntervalChartedSpace
  let _ : IsManifold (modelWithCornersEuclideanHalfSpace 1) ∞
      EquatorCollarInterval := isManifold_signedSeamInterval
  let _ := signedSeamCollarBoundaryChartedSpace
  let _ : IsManifold coordinateUnlinkBoundaryCollarModel ∞
      (Sphere 3 × EquatorCollarInterval) :=
    isManifold_signedSeamCollarBoundary
  rw [ModelWithCorners.boundary_prod,
    signedSeamInterval_boundary,
    ModelWithCorners.Boundaryless.boundary_eq_empty
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (M := Sphere 3)]
  ext x
  constructor
  · rintro (hx | hx)
    · exact hx.2
    · exact hx.1
  · exact False.elim

/-- Rechart a signed-collar chart directly into the common coordinate-exterior
model carrier. -/
def signedSeamCommonModelChart
    (p : Sphere 3 × EquatorCollarInterval) :
    OpenPartialHomeomorph (Sphere 3 × EquatorCollarInterval)
      CoordinateUnlinkExteriorModelSpace :=
  let _ := signedSeamCollarBoundaryChartedSpace
  (chartAt CoordinateUnlinkBoundaryCollarModelSpace p).trans
    coordinateUnlinkBoundaryCollarModelHomeomorph.toOpenPartialHomeomorph

@[simp]
theorem mem_signedSeamCommonModelChart_source
    (p : Sphere 3 × EquatorCollarInterval) :
    p ∈ (signedSeamCommonModelChart p).source := by
  simp [signedSeamCommonModelChart]

/-- The direct common-model rechart of the unlabelled signed-collar atlas. -/
@[instance_reducible]
def signedSeamCommonModelChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (Sphere 3 × EquatorCollarInterval) where
  atlas := range signedSeamCommonModelChart
  chartAt := signedSeamCommonModelChart
  mem_chart_source := mem_signedSeamCommonModelChart_source
  chart_mem_atlas p := ⟨p, rfl⟩

theorem mem_signedSeamCommonModelChartedSpace_atlas_iff
    (e : OpenPartialHomeomorph (Sphere 3 × EquatorCollarInterval)
      CoordinateUnlinkExteriorModelSpace) :
    e ∈ @atlas CoordinateUnlinkExteriorModelSpace _
        (Sphere 3 × EquatorCollarInterval) _
        signedSeamCommonModelChartedSpace ↔
      ∃ p, e = signedSeamCommonModelChart p := by
  change e ∈ range signedSeamCommonModelChart ↔ _
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, rfl⟩

theorem isManifold_signedSeamCommonModel :
    letI := signedSeamCommonModelChartedSpace
    IsManifold coordinateUnlinkExteriorModel ∞
      (Sphere 3 × EquatorCollarInterval) := by
  let _ := signedSeamCollarBoundaryChartedSpace
  let _ : IsManifold coordinateUnlinkBoundaryCollarModel ∞
      (Sphere 3 × EquatorCollarInterval) :=
    isManifold_signedSeamCollarBoundary
  let _ := signedSeamCommonModelChartedSpace
  refine { compatible := ?_ }
  intro e e' he he'
  rw [mem_signedSeamCommonModelChartedSpace_atlas_iff] at he he'
  obtain ⟨p, rfl⟩ := he
  obtain ⟨q, rfl⟩ := he'
  have hold := (contDiffGroupoid ∞ coordinateUnlinkBoundaryCollarModel).compatible
    (chart_mem_atlas CoordinateUnlinkBoundaryCollarModelSpace p)
    (chart_mem_atlas CoordinateUnlinkBoundaryCollarModelSpace q)
  have hnew :=
    coordinateUnlinkBoundaryCollarConjugate_mem_contDiffGroupoid
      ((chartAt CoordinateUnlinkBoundaryCollarModelSpace p).symm.trans
        (chartAt CoordinateUnlinkBoundaryCollarModelSpace q)) hold
  simpa only [signedSeamCommonModelChart,
    coordinateUnlinkBoundaryCollarConjugate,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc,
    Homeomorph.symm_toOpenPartialHomeomorph,
    OpenPartialHomeomorph.symm_symm] using hnew

variable {E' H' Q : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] [TopologicalSpace Q] [ChartedSpace H' Q]

/-- Any naturally smooth map out of the signed collar remains smooth after
the direct common-model rechart. -/
theorem contMDiff_signedSeamCommonModel_of_boundaryModel
    (J : ModelWithCorners ℝ E' H')
    (f : Sphere 3 × EquatorCollarInterval → Q)
    (hf : letI := signedSeamCollarBoundaryChartedSpace
      ContMDiff coordinateUnlinkBoundaryCollarModel J ∞ f) :
    letI := signedSeamCommonModelChartedSpace
    ContMDiff coordinateUnlinkExteriorModel J ∞ f := by
  let _ := signedSeamCollarBoundaryChartedSpace
  let _ : IsManifold coordinateUnlinkBoundaryCollarModel ∞
      (Sphere 3 × EquatorCollarInterval) :=
    isManifold_signedSeamCollarBoundary
  let _ := signedSeamCommonModelChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (Sphere 3 × EquatorCollarInterval) :=
    isManifold_signedSeamCommonModel
  intro p
  rw [contMDiffAt_iff_source_of_mem_source
    (mem_chart_source CoordinateUnlinkExteriorModelSpace p)]
  have hnat := hf p
  rw [contMDiffAt_iff_source_of_mem_source
    (mem_chart_source CoordinateUnlinkBoundaryCollarModelSpace p)] at hnat
  have hbase : coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm
        (extChartAt coordinateUnlinkExteriorModel p p) =
      extChartAt coordinateUnlinkBoundaryCollarModel p p := by
    change coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm
        (coordinateUnlinkExteriorModel
          (coordinateUnlinkBoundaryCollarModelHomeomorph
            (chartAt CoordinateUnlinkBoundaryCollarModelSpace p p))) =
      coordinateUnlinkBoundaryCollarModel
        (chartAt CoordinateUnlinkBoundaryCollarModelSpace p p)
    rw [coordinateUnlinkBoundaryCollarModel_coordinate_eq]
    simp
  have hmap : MapsTo coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm
      (range coordinateUnlinkExteriorModel)
      (range coordinateUnlinkBoundaryCollarModel) := by
    rintro _ ⟨q, rfl⟩
    refine ⟨coordinateUnlinkBoundaryCollarModelHomeomorph.symm q, ?_⟩
    exact coordinateUnlinkBoundaryCollarModel_coordinate_symm_eq q
  rw [← hbase] at hnat
  have hlin : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ CoordinateUnlinkBoundaryCollarModelVector) ∞
      coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm :=
    coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm.contDiff.contMDiff
  have hcomp := hnat.comp (extChartAt coordinateUnlinkExteriorModel p p)
    (hlin (extChartAt coordinateUnlinkExteriorModel p p)).contMDiffWithinAt
    hmap
  have hinv (z : EuclideanSpace ℝ (Fin 4))
      (hz : z ∈ range coordinateUnlinkExteriorModel) :
      (extChartAt coordinateUnlinkExteriorModel p).symm z =
        (extChartAt coordinateUnlinkBoundaryCollarModel p).symm
          (coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm z) := by
    have hmodelInv :
        coordinateUnlinkBoundaryCollarModel.symm
            (coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm z) =
          coordinateUnlinkBoundaryCollarModelHomeomorph.symm
            (coordinateUnlinkExteriorModel.symm z) := by
      have hvec : coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm z =
          coordinateUnlinkBoundaryCollarModel
            (coordinateUnlinkBoundaryCollarModelHomeomorph.symm
              (coordinateUnlinkExteriorModel.symm z)) := by
        rw [coordinateUnlinkBoundaryCollarModel_coordinate_symm_eq,
          coordinateUnlinkExteriorModel.right_inv hz]
      rw [hvec, coordinateUnlinkBoundaryCollarModel.left_inv]
    change
      (signedSeamCommonModelChart p).symm
          (coordinateUnlinkExteriorModel.symm z) =
        (chartAt CoordinateUnlinkBoundaryCollarModelSpace p).symm
          (coordinateUnlinkBoundaryCollarModel.symm
            (coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm z))
    change
      (chartAt CoordinateUnlinkBoundaryCollarModelSpace p).symm
          (coordinateUnlinkBoundaryCollarModelHomeomorph.symm
            (coordinateUnlinkExteriorModel.symm z)) =
        (chartAt CoordinateUnlinkBoundaryCollarModelSpace p).symm
          (coordinateUnlinkBoundaryCollarModel.symm
            (coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm z))
    rw [hmodelInv]
  apply hcomp.congr
  · intro z hz
    change f ((extChartAt coordinateUnlinkExteriorModel p).symm z) =
      f ((extChartAt coordinateUnlinkBoundaryCollarModel p).symm
        (coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm z))
    rw [hinv z hz]
  · change f
        ((extChartAt coordinateUnlinkExteriorModel p).symm
          (extChartAt coordinateUnlinkExteriorModel p p)) =
      f ((extChartAt coordinateUnlinkBoundaryCollarModel p).symm
        (coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm
          (extChartAt coordinateUnlinkExteriorModel p p)))
    rw [hinv (extChartAt coordinateUnlinkExteriorModel p p)]
    exact ⟨_, rfl⟩

/-- Any map naturally smooth into the signed collar remains smooth when its
target is given the direct common-model rechart. -/
theorem contMDiff_to_signedSeamCommonModel_of_boundaryModel
    (J : ModelWithCorners ℝ E' H')
    (f : Q → Sphere 3 × EquatorCollarInterval)
    (hf : letI := signedSeamCollarBoundaryChartedSpace
      ContMDiff J coordinateUnlinkBoundaryCollarModel ∞ f) :
    letI := signedSeamCommonModelChartedSpace
    ContMDiff J coordinateUnlinkExteriorModel ∞ f := by
  let _ := signedSeamCollarBoundaryChartedSpace
  let _ : IsManifold coordinateUnlinkBoundaryCollarModel ∞
      (Sphere 3 × EquatorCollarInterval) :=
    isManifold_signedSeamCollarBoundary
  let _ := signedSeamCommonModelChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (Sphere 3 × EquatorCollarInterval) :=
    isManifold_signedSeamCommonModel
  intro x
  rw [contMDiffAt_iff_target_of_mem_source
    (mem_chart_source CoordinateUnlinkExteriorModelSpace (f x))]
  have hnat := hf x
  rw [contMDiffAt_iff_target_of_mem_source
    (mem_chart_source CoordinateUnlinkBoundaryCollarModelSpace (f x))] at hnat
  refine ⟨hnat.1, ?_⟩
  have hlin : ContMDiff
      (modelWithCornersSelf ℝ CoordinateUnlinkBoundaryCollarModelVector)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      coordinateUnlinkBoundaryCollarVectorLinearEquiv :=
    coordinateUnlinkBoundaryCollarVectorLinearEquiv.contDiff.contMDiff
  have hcomp := (hlin
    (extChartAt coordinateUnlinkBoundaryCollarModel (f x) (f x))).comp x hnat.2
  exact hcomp.congr_of_eventuallyEq <|
    Filter.Eventually.of_forall fun y ↦ by
      change coordinateUnlinkExteriorModel
          (coordinateUnlinkBoundaryCollarModelHomeomorph
            (chartAt CoordinateUnlinkBoundaryCollarModelSpace (f x) (f y))) =
        coordinateUnlinkBoundaryCollarVectorLinearEquiv
          (coordinateUnlinkBoundaryCollarModel
            (chartAt CoordinateUnlinkBoundaryCollarModelSpace (f x) (f y)))
      exact coordinateUnlinkBoundaryCollarModel_coordinate_eq _

/-- The direct rechart is diffeomorphic to the natural signed-collar atlas by
the literal identity. -/
def signedSeamCommonBoundaryIdentityDiffeomorph :
    letI := signedSeamCollarBoundaryChartedSpace
    letI := signedSeamCommonModelChartedSpace
    (Sphere 3 × EquatorCollarInterval) ≃ₘ^∞⟮
      coordinateUnlinkExteriorModel,
      coordinateUnlinkBoundaryCollarModel⟯
      (Sphere 3 × EquatorCollarInterval) := by
  let _ := signedSeamCollarBoundaryChartedSpace
  let _ := signedSeamCommonModelChartedSpace
  exact
    { toEquiv := Equiv.refl _
      contMDiff_toFun :=
        contMDiff_signedSeamCommonModel_of_boundaryModel
          coordinateUnlinkBoundaryCollarModel id contMDiff_id
      contMDiff_invFun :=
        contMDiff_to_signedSeamCommonModel_of_boundaryModel
          coordinateUnlinkBoundaryCollarModel id contMDiff_id }

@[simp]
theorem signedSeamCommonBoundaryIdentityDiffeomorph_apply
    (p : Sphere 3 × EquatorCollarInterval) :
    letI := signedSeamCollarBoundaryChartedSpace
    letI := signedSeamCommonModelChartedSpace
    signedSeamCommonBoundaryIdentityDiffeomorph p = p := by
  change (Equiv.refl (Sphere 3 × EquatorCollarInterval)) p = p
  rfl

theorem contMDiff_signedSeamTime :
    letI := signedSeamCommonModelChartedSpace
    ContMDiff coordinateUnlinkExteriorModel
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ (p.2.1 : ℝ)) := by
  let _ := signedSeamIntervalChartedSpace
  let _ : IsManifold (modelWithCornersEuclideanHalfSpace 1) ∞
      EquatorCollarInterval := isManifold_signedSeamInterval
  let _ := signedSeamCollarBoundaryChartedSpace
  have hnat : ContMDiff coordinateUnlinkBoundaryCollarModel
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ (p.2.1 : ℝ)) :=
    contMDiff_signedSeamInterval_value.comp contMDiff_snd
  exact contMDiff_signedSeamCommonModel_of_boundaryModel _ _ hnat

theorem signedSeamCommonModel_boundary :
    letI := signedSeamCommonModelChartedSpace
    coordinateUnlinkExteriorModel.boundary
        (Sphere 3 × EquatorCollarInterval) = ∅ := by
  let _ := signedSeamCollarBoundaryChartedSpace
  let _ : IsManifold coordinateUnlinkBoundaryCollarModel ∞
      (Sphere 3 × EquatorCollarInterval) :=
    isManifold_signedSeamCollarBoundary
  let _ := signedSeamCommonModelChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (Sphere 3 × EquatorCollarInterval) :=
    isManifold_signedSeamCommonModel
  ext p
  change coordinateUnlinkExteriorModel.IsBoundaryPoint p ↔ False
  let q := (chartAt CoordinateUnlinkBoundaryCollarModelSpace p) p
  have hcarrier :=
    (coordinateUnlinkBoundaryCollarCarrierDiffeomorph.isLocalDiffeomorph q).isBoundaryPoint_iff
      (by simp)
  have hcarrier' :
      coordinateUnlinkBoundaryCollarModel.IsBoundaryPoint q ↔
        coordinateUnlinkExteriorModel.IsBoundaryPoint
          (coordinateUnlinkBoundaryCollarModelHomeomorph q) := by
    simpa only [coordinateUnlinkBoundaryCollarCarrierDiffeomorph_apply] using hcarrier
  change coordinateUnlinkExteriorModel.IsBoundaryPoint
      (coordinateUnlinkBoundaryCollarModelHomeomorph q) ↔ False
  rw [← hcarrier']
  change coordinateUnlinkBoundaryCollarModel.IsBoundaryPoint p ↔ False
  have hp : p ∉ coordinateUnlinkBoundaryCollarModel.boundary
      (Sphere 3 × EquatorCollarInterval) := by
    rw [signedSeamCollarBoundary_boundary]
    simp
  exact ⟨fun h ↦ hp h, False.elim⟩

/-- The componentwise common-model atlas on the labelled signed-collar family. -/
@[instance_reducible]
def signedSeamFamilyCommonModelChartedSpace (m : ℕ) :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m × (Sphere 3 × EquatorCollarInterval)) :=
  let _ := signedSeamCommonModelChartedSpace
  discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) (Sphere 3 × EquatorCollarInterval)

theorem isManifold_signedSeamFamilyCommonModel (m : ℕ) :
    letI := signedSeamFamilyCommonModelChartedSpace m
    IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × (Sphere 3 × EquatorCollarInterval)) := by
  let _ := signedSeamCommonModelChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (Sphere 3 × EquatorCollarInterval) :=
    isManifold_signedSeamCommonModel
  exact isManifold_discreteProductChartedSpace
    coordinateUnlinkExteriorModel ∞ (ZMod m)
      (Sphere 3 × EquatorCollarInterval)

/-- The signed seam coordinate, with the association fixed as
`ZMod m × (Sphere 3 × EquatorCollarInterval)`. -/
def signedSeamTime (m : ℕ)
    (p : ZMod m × (Sphere 3 × EquatorCollarInterval)) : ℝ :=
  p.2.2.1

theorem contMDiff_signedSeamFamilyTime (m : ℕ) :
    letI := signedSeamFamilyCommonModelChartedSpace m
    ContMDiff coordinateUnlinkExteriorModel
      (modelWithCornersSelf ℝ ℝ) ∞ (signedSeamTime m) := by
  let _ := signedSeamCommonModelChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (Sphere 3 × EquatorCollarInterval) :=
    isManifold_signedSeamCommonModel
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × (Sphere 3 × EquatorCollarInterval)) :=
    isManifold_signedSeamFamilyCommonModel m
  have hsnd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × (Sphere 3 × EquatorCollarInterval) →
        Sphere 3 × EquatorCollarInterval) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd (D := ZMod m)
        (P := Sphere 3 × EquatorCollarInterval))
  exact (contMDiff_signedSeamTime.comp hsnd.contMDiff).congr fun _ ↦ rfl

theorem signedSeamFamilyCommonModel_boundary (m : ℕ) :
    letI := signedSeamFamilyCommonModelChartedSpace m
    coordinateUnlinkExteriorModel.boundary
        (ZMod m × (Sphere 3 × EquatorCollarInterval)) = ∅ := by
  let _ := signedSeamCommonModelChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (Sphere 3 × EquatorCollarInterval) :=
    isManifold_signedSeamCommonModel
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × (Sphere 3 × EquatorCollarInterval)) :=
    isManifold_signedSeamFamilyCommonModel m
  have hsnd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × (Sphere 3 × EquatorCollarInterval) →
        Sphere 3 × EquatorCollarInterval) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd (D := ZMod m)
        (P := Sphere 3 × EquatorCollarInterval))
  rw [← hsnd.preimage_boundary (by simp), signedSeamCommonModel_boundary]
  simp

/-- Forget the sign of a full collar time and regard its magnitude as an
inward half-collar time. -/
def signedSeamUnsignedCollarInterval
    (t : EquatorCollarInterval) : EuclideanFourBallCollarInterval :=
  ⟨⟨|t.1|, abs_nonneg _, (abs_lt.2 t.2).le⟩, abs_lt.2 t.2⟩

@[simp]
theorem signedSeamUnsignedCollarInterval_value
    (t : EquatorCollarInterval) :
    ((signedSeamUnsignedCollarInterval t).1.1 : ℝ) = |t.1| := rfl

/-- The one total, continuous half-reparametrization needed by both branches
of the signed pushout seam.  It is smooth only off the zero slice. -/
def signedSeamHalfReparam (m : ℕ) :
    ZMod m × (Sphere 3 × EquatorCollarInterval) →
      ZMod m × EuclideanFourBallCollarDomain :=
  fun p ↦ (p.1, (p.2.1, signedSeamUnsignedCollarInterval p.2.2))

theorem continuous_signedSeamHalfReparam (m : ℕ) :
    Continuous (signedSeamHalfReparam m) := by
  unfold signedSeamHalfReparam signedSeamUnsignedCollarInterval
  fun_prop

@[simp]
theorem signedSeamHalfReparam_fst (m : ℕ)
    (p : ZMod m × (Sphere 3 × EquatorCollarInterval)) :
    (signedSeamHalfReparam m p).1 = p.1 := rfl

@[simp]
theorem signedSeamHalfReparam_sphere (m : ℕ)
    (p : ZMod m × (Sphere 3 × EquatorCollarInterval)) :
    (signedSeamHalfReparam m p).2.1 = p.2.1 := rfl

theorem compactNeckLeftHalfParameter_signedSeamHalfReparam
    (m : ℕ)
    (p : ZMod m × (Sphere 3 × EquatorCollarInterval))
    (hp : signedSeamTime m p ≤ 0) :
    compactNeckLeftHalfParameter (signedSeamHalfReparam m p).2 = p.2 := by
  change (p.2.2.1 : ℝ) ≤ 0 at hp
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change -|p.2.2.1| = p.2.2.1
    rw [abs_of_nonpos hp]
    simp

theorem compactNeckRightHalfParameter_signedSeamHalfReparam
    (m : ℕ)
    (p : ZMod m × (Sphere 3 × EquatorCollarInterval))
    (hp : 0 ≤ signedSeamTime m p) :
    compactNeckRightHalfParameter (signedSeamHalfReparam m p).2 = p.2 := by
  change 0 ≤ (p.2.2.1 : ℝ) at hp
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change |p.2.2.1| = p.2.2.1
    exact abs_of_nonneg hp

/-- Strict negative half of the unlabelled signed collar. -/
def signedSeamNegativeBaseOpens :
    Opens (Sphere 3 × EquatorCollarInterval) :=
  ⟨{p | (p.2.1 : ℝ) < 0}, isOpen_lt (by fun_prop) continuous_const⟩

/-- Strict positive half of the unlabelled signed collar. -/
def signedSeamPositiveBaseOpens :
    Opens (Sphere 3 × EquatorCollarInterval) :=
  ⟨{p | 0 < (p.2.1 : ℝ)}, isOpen_lt continuous_const (by fun_prop)⟩

/-- Positive-time interior of the one-sided four-ball collar domain. -/
def signedSeamPositiveCollarOpens : Opens EuclideanFourBallCollarDomain :=
  ⟨{p | 0 < (p.2.1.1 : ℝ)}, isOpen_lt continuous_const (by fun_prop)⟩

/-- On the negative signed half, inward time is `-t`. -/
def signedSeamNegativeHalfReparamOpen :
    signedSeamNegativeBaseOpens → signedSeamPositiveCollarOpens :=
  fun p ↦ by
    have hpneg : (p.1.2.1 : ℝ) < 0 := p.2
    have hlower : -(1 / 2 : ℝ) < (p.1.2.1 : ℝ) := p.1.2.2.1
    have hupper : -(p.1.2.1 : ℝ) < 1 / 2 := by linarith
    let t : EuclideanFourBallCollarInterval :=
      ⟨⟨-(p.1.2.1 : ℝ), (neg_pos.mpr hpneg).le, hupper.le⟩, hupper⟩
    exact ⟨(p.1.1, t), neg_pos.mpr hpneg⟩

/-- On the positive signed half, inward time is `t`. -/
def signedSeamPositiveHalfReparamOpen :
    signedSeamPositiveBaseOpens → signedSeamPositiveCollarOpens :=
  fun p ↦ ⟨(p.1.1, ⟨⟨(p.1.2.1 : ℝ), p.2.le,
      p.1.2.2.2.le⟩, p.1.2.2.2⟩), p.2⟩

/-- Recover negative signed time from positive inward collar time. -/
def signedSeamNegativeHalfReparamOpenInv :
    signedSeamPositiveCollarOpens → signedSeamNegativeBaseOpens :=
  fun p ↦ by
    have hp : 0 < (p.1.2.1.1 : ℝ) := p.2
    exact ⟨compactNeckLeftHalfParameter p.1, neg_neg_of_pos hp⟩

/-- Recover positive signed time from positive inward collar time. -/
def signedSeamPositiveHalfReparamOpenInv :
    signedSeamPositiveCollarOpens → signedSeamPositiveBaseOpens :=
  fun p ↦ ⟨compactNeckRightHalfParameter p.1, p.2⟩

/-- The strict negative signed half is equivalent to the positive one-sided collar interior. -/
def signedSeamNegativeHalfReparamOpenEquiv :
    signedSeamNegativeBaseOpens ≃ signedSeamPositiveCollarOpens where
  toFun := signedSeamNegativeHalfReparamOpen
  invFun := signedSeamNegativeHalfReparamOpenInv
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [signedSeamNegativeHalfReparamOpen,
        signedSeamNegativeHalfReparamOpenInv,
        compactNeckLeftHalfParameter]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Subtype.ext
      simp [signedSeamNegativeHalfReparamOpen,
        signedSeamNegativeHalfReparamOpenInv,
        compactNeckLeftHalfParameter]

/-- The strict positive signed half is equivalent to the positive one-sided collar interior. -/
def signedSeamPositiveHalfReparamOpenEquiv :
    signedSeamPositiveBaseOpens ≃ signedSeamPositiveCollarOpens where
  toFun := signedSeamPositiveHalfReparamOpen
  invFun := signedSeamPositiveHalfReparamOpenInv
  left_inv p := by rfl
  right_inv p := by rfl

/-- The strict negative half-reparametrization as a homeomorphism. -/
def signedSeamNegativeHalfReparamOpenHomeomorph :
    signedSeamNegativeBaseOpens ≃ₜ signedSeamPositiveCollarOpens where
  toEquiv := signedSeamNegativeHalfReparamOpenEquiv
  continuous_toFun := by
    change Continuous signedSeamNegativeHalfReparamOpen
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact (continuous_fst.comp continuous_subtype_val)
    · apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val)).neg
  continuous_invFun := by
    change Continuous signedSeamNegativeHalfReparamOpenInv
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp
        (continuous_subtype_val.comp
          (continuous_snd.comp continuous_subtype_val))).neg

/-- The strict positive half-reparametrization as a homeomorphism. -/
def signedSeamPositiveHalfReparamOpenHomeomorph :
    signedSeamPositiveBaseOpens ≃ₜ signedSeamPositiveCollarOpens where
  toEquiv := signedSeamPositiveHalfReparamOpenEquiv
  continuous_toFun := by
    change Continuous signedSeamPositiveHalfReparamOpen
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := by
    change Continuous signedSeamPositiveHalfReparamOpenInv
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · apply Continuous.subtype_mk
      exact continuous_subtype_val.comp
        (continuous_subtype_val.comp
          (continuous_snd.comp continuous_subtype_val))

end SplittingSpheres
