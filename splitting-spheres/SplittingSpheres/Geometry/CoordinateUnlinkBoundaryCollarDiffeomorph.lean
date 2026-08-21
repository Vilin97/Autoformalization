/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.CoordinateUnlinkBoundaryCollarChartedSpace

/-!
# Smooth comparison of the natural and recharted boundary collars

The explicit homeomorphism between the natural four-ball boundary-collar model and the
coordinate-unlink exterior model is a diffeomorphism.  It identifies the recharted atlas on
`EuclideanFourBallCollarDomain` with its natural collar atlas: the underlying comparison map
is literally the identity in both directions.

As a consequence, the model boundary of the recharted collar is the familiar zero-time face.
The same description pulls back componentwise to a finite family indexed by `ZMod m`.
-/

@[expose] public section

open Function Set Topology TopologicalSpace IsManifold
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-- The explicit carrier homeomorphism from the natural boundary-collar model to the
coordinate-unlink exterior model is smooth in both directions. -/
def coordinateUnlinkBoundaryCollarCarrierDiffeomorph :
    CoordinateUnlinkBoundaryCollarModelSpace ≃ₘ^∞⟮
      coordinateUnlinkBoundaryCollarModel,
      coordinateUnlinkExteriorModel⟯
      CoordinateUnlinkExteriorModelSpace where
  toEquiv := coordinateUnlinkBoundaryCollarModelHomeomorph.toEquiv
  contMDiff_toFun := by
    have hcoord : ContMDiff coordinateUnlinkBoundaryCollarModel
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (coordinateUnlinkBoundaryCollarVectorLinearEquiv ∘
          coordinateUnlinkBoundaryCollarModel) :=
      coordinateUnlinkBoundaryCollarVectorLinearEquiv.contDiff.comp_contMDiff
        coordinateUnlinkBoundaryCollarModel.contMDiff
    have hrange : MapsTo
        (coordinateUnlinkBoundaryCollarVectorLinearEquiv ∘
          coordinateUnlinkBoundaryCollarModel)
        univ (range coordinateUnlinkExteriorModel) := by
      intro p _
      exact ⟨coordinateUnlinkBoundaryCollarModelHomeomorph p,
        (coordinateUnlinkBoundaryCollarModel_coordinate_eq p).symm⟩
    have hsmooth := coordinateUnlinkExteriorModel.contMDiffOn_symm.comp
      hcoord.contMDiffOn hrange
    exact (contMDiffOn_univ.mp hsmooth).congr fun p ↦ by
      simp only [comp_apply]
      rw [← coordinateUnlinkBoundaryCollarModel_coordinate_eq]
      exact (coordinateUnlinkExteriorModel.left_inv _).symm
  contMDiff_invFun := by
    have hcoord : ContMDiff coordinateUnlinkExteriorModel
        (modelWithCornersSelf ℝ CoordinateUnlinkBoundaryCollarModelVector) ∞
        (coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm ∘
          coordinateUnlinkExteriorModel) :=
      coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm.contDiff.comp_contMDiff
        coordinateUnlinkExteriorModel.contMDiff
    have hrange : MapsTo
        (coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm ∘
          coordinateUnlinkExteriorModel)
        univ (range coordinateUnlinkBoundaryCollarModel) := by
      intro p _
      exact ⟨coordinateUnlinkBoundaryCollarModelHomeomorph.symm p,
        coordinateUnlinkBoundaryCollarModel_coordinate_symm_eq p⟩
    have hsmooth := coordinateUnlinkBoundaryCollarModel.contMDiffOn_symm.comp
      hcoord.contMDiffOn hrange
    exact (contMDiffOn_univ.mp hsmooth).congr fun p ↦ by
      simp only [comp_apply]
      rw [← coordinateUnlinkBoundaryCollarModel_coordinate_symm_eq]
      exact (coordinateUnlinkBoundaryCollarModel.left_inv _).symm

/-- Forgetting smoothness recovers exactly the carrier homeomorphism used to define the
recharted collar atlas. -/
@[simp]
theorem coordinateUnlinkBoundaryCollarCarrierDiffeomorph_toHomeomorph :
    coordinateUnlinkBoundaryCollarCarrierDiffeomorph.toHomeomorph =
      coordinateUnlinkBoundaryCollarModelHomeomorph :=
  rfl

/-- The forward carrier diffeomorphism is the explicit carrier homeomorphism. -/
@[simp]
theorem coordinateUnlinkBoundaryCollarCarrierDiffeomorph_apply
    (p : CoordinateUnlinkBoundaryCollarModelSpace) :
    coordinateUnlinkBoundaryCollarCarrierDiffeomorph p =
      coordinateUnlinkBoundaryCollarModelHomeomorph p :=
  rfl

/-- The inverse carrier diffeomorphism is the inverse explicit carrier homeomorphism. -/
@[simp]
theorem coordinateUnlinkBoundaryCollarCarrierDiffeomorph_symm_apply
    (p : CoordinateUnlinkExteriorModelSpace) :
    coordinateUnlinkBoundaryCollarCarrierDiffeomorph.symm p =
      coordinateUnlinkBoundaryCollarModelHomeomorph.symm p :=
  rfl

/-- The identity of the four-ball collar domain is smooth from the recharted atlas to the
natural atlas and from the natural atlas back to the recharted atlas. -/
theorem coordinateUnlinkExteriorRechartedFourBallCollarIdentity_contMDiff :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    ContMDiff coordinateUnlinkExteriorModel
      euclideanFourBallCollarModel ∞
      (id : EuclideanFourBallCollarDomain →
        EuclideanFourBallCollarDomain) ∧
      ContMDiff euclideanFourBallCollarModel
        coordinateUnlinkExteriorModel ∞
        (id : EuclideanFourBallCollarDomain →
          EuclideanFourBallCollarDomain) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  let sourceChart (p : EuclideanFourBallCollarDomain) :
      PartialDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel EuclideanFourBallCollarDomain
      CoordinateUnlinkExteriorModelSpace ∞ :=
    { toPartialEquiv :=
        (chartAt CoordinateUnlinkExteriorModelSpace p).toPartialEquiv
      open_source := (chartAt CoordinateUnlinkExteriorModelSpace p).open_source
      open_target := (chartAt CoordinateUnlinkExteriorModelSpace p).open_target
      contMDiffOn_toFun :=
        contMDiffOn_of_mem_maximalAtlas (chart_mem_maximalAtlas p)
      contMDiffOn_invFun :=
        contMDiffOn_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas p) }
  let targetChart (p : EuclideanFourBallCollarDomain) :
      PartialDiffeomorph euclideanFourBallCollarModel
      euclideanFourBallCollarModel EuclideanFourBallCollarDomain
      CoordinateUnlinkBoundaryCollarModelSpace ∞ :=
    { toPartialEquiv :=
        (chartAt CoordinateUnlinkBoundaryCollarModelSpace p).toPartialEquiv
      open_source := (chartAt CoordinateUnlinkBoundaryCollarModelSpace p).open_source
      open_target := (chartAt CoordinateUnlinkBoundaryCollarModelSpace p).open_target
      contMDiffOn_toFun :=
        contMDiffOn_of_mem_maximalAtlas (chart_mem_maximalAtlas p)
      contMDiffOn_invFun :=
        contMDiffOn_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas p) }
  let carrierChart : PartialDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkBoundaryCollarModel CoordinateUnlinkExteriorModelSpace
      CoordinateUnlinkBoundaryCollarModelSpace ∞ :=
    { toPartialEquiv :=
        coordinateUnlinkBoundaryCollarModelHomeomorph.symm.toPartialEquiv
      open_source := isOpen_univ
      open_target := isOpen_univ
      contMDiffOn_toFun :=
        coordinateUnlinkBoundaryCollarCarrierDiffeomorph.symm.contMDiff.contMDiffOn
      contMDiffOn_invFun :=
        coordinateUnlinkBoundaryCollarCarrierDiffeomorph.contMDiff.contMDiffOn }
  let phi (p : EuclideanFourBallCollarDomain) :=
    ((sourceChart p).trans carrierChart).trans
        (targetChart p).symm
  have hmem (p : EuclideanFourBallCollarDomain) : p ∈ (phi p).source := by
    dsimp only [phi]
    rw [PartialDiffeomorph.trans_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv, PartialEquiv.trans_source]
    change p ∈
      ((sourceChart p).trans
          carrierChart).source ∩
        (fun z ↦ ((sourceChart p).trans
          carrierChart) z) ⁻¹'
          (targetChart p).symm.source
    rw [PartialDiffeomorph.trans_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv, PartialEquiv.trans_source]
    simp only [PartialDiffeomorph.toOpenPartialHomeomorph]
    change p ∈ (sourceChart p).source ∩
      sourceChart p ⁻¹' carrierChart.source ∩
        (fun z ↦ coordinateUnlinkBoundaryCollarModelHomeomorph.symm
          (sourceChart p z)) ⁻¹' (targetChart p).symm.source
    refine ⟨⟨mem_chart_source _ p, mem_univ _⟩, ?_⟩
    change coordinateUnlinkBoundaryCollarModelHomeomorph.symm
        (coordinateUnlinkExteriorRechartedFourBallCollarChart p p) ∈
      (chartAt CoordinateUnlinkBoundaryCollarModelSpace p).target
    change (chartAt CoordinateUnlinkBoundaryCollarModelSpace p) p ∈
      (chartAt CoordinateUnlinkBoundaryCollarModelSpace p).target
    exact (chartAt CoordinateUnlinkBoundaryCollarModelSpace p).map_source
      (mem_chart_source _ p)
  have heq (p : EuclideanFourBallCollarDomain) :
      EqOn id (phi p) (phi p).source := by
    intro y hy
    dsimp only [phi]
    rw [PartialDiffeomorph.trans_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv, PartialEquiv.trans_apply]
    simp only [PartialDiffeomorph.toOpenPartialHomeomorph]
    change id y = (targetChart p).symm
      (((sourceChart p).trans
        carrierChart) y)
    rw [PartialDiffeomorph.trans_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv, PartialEquiv.trans_apply]
    change id y = (targetChart p).symm
      (coordinateUnlinkBoundaryCollarModelHomeomorph.symm (sourceChart p y))
    change y = (chartAt CoordinateUnlinkBoundaryCollarModelSpace p).symm
      (coordinateUnlinkBoundaryCollarModelHomeomorph.symm
        (coordinateUnlinkExteriorRechartedFourBallCollarChart p y))
    have hyNew : y ∈
        (coordinateUnlinkExteriorRechartedFourBallCollarChart p).source := hy.1.1
    have hyNatural : y ∈
        (chartAt CoordinateUnlinkBoundaryCollarModelSpace p).source := by
      simpa only [coordinateUnlinkExteriorRechartedFourBallCollarChart,
        OpenPartialHomeomorph.trans_source,
        Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
        using hyNew
    have hleft :=
      ((chartAt CoordinateUnlinkBoundaryCollarModelSpace p).left_inv hyNatural).symm
    change y = (chartAt CoordinateUnlinkBoundaryCollarModelSpace p).symm
      (coordinateUnlinkBoundaryCollarModelHomeomorph.symm
        (coordinateUnlinkBoundaryCollarModelHomeomorph
          ((chartAt CoordinateUnlinkBoundaryCollarModelSpace p) y)))
    rw [coordinateUnlinkBoundaryCollarModelHomeomorph.symm_apply_apply]
    exact hleft
  constructor
  · intro p
    exact ((phi p).contMDiffOn_toFun.congr (heq p)).contMDiffAt
      ((phi p).open_source.mem_nhds (hmem p))
  · intro p
    have hpTarget : p ∈ (phi p).target := by
      have hpoint : p = phi p p := by
        simpa only [id_eq] using (heq p) (hmem p)
      have hmap : phi p p ∈ (phi p).target :=
        (phi p).map_source (hmem p)
      rw [← hpoint] at hmap
      exact hmap
    have hinv : EqOn id (phi p).symm (phi p).target := by
      intro y hy
      have hySource : (phi p).symm y ∈ (phi p).source :=
        (phi p).symm.map_source hy
      have hEq := (heq p) hySource
      have hRight := (phi p).right_inv hy
      simp only [id_eq] at hEq ⊢
      exact hRight.symm.trans hEq.symm
    exact ((phi p).symm.contMDiffOn_toFun.congr hinv).contMDiffAt
      ((phi p).symm.open_source.mem_nhds hpTarget)

/-- The recharted exterior-model collar and the natural four-ball collar are diffeomorphic by
the literal identity map.  Its forward direction is recharted to natural. -/
def coordinateUnlinkExteriorRechartedFourBallCollarIdentityDiffeomorph :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    EuclideanFourBallCollarDomain ≃ₘ^∞⟮
      coordinateUnlinkExteriorModel,
      euclideanFourBallCollarModel⟯ EuclideanFourBallCollarDomain := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  exact
    { toEquiv := Equiv.refl _
      contMDiff_toFun :=
        coordinateUnlinkExteriorRechartedFourBallCollarIdentity_contMDiff.1
      contMDiff_invFun :=
        coordinateUnlinkExteriorRechartedFourBallCollarIdentity_contMDiff.2 }

/-- The forward recharted-to-natural collar diffeomorphism is literally the identity. -/
@[simp]
theorem coordinateUnlinkExteriorRechartedFourBallCollarIdentityDiffeomorph_apply
    (p : EuclideanFourBallCollarDomain) :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    coordinateUnlinkExteriorRechartedFourBallCollarIdentityDiffeomorph p = p := by
  change (Equiv.refl EuclideanFourBallCollarDomain) p = p
  rfl

/-- The inverse natural-to-recharted collar diffeomorphism is literally the identity. -/
@[simp]
theorem coordinateUnlinkExteriorRechartedFourBallCollarIdentityDiffeomorph_symm_apply
    (p : EuclideanFourBallCollarDomain) :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    coordinateUnlinkExteriorRechartedFourBallCollarIdentityDiffeomorph.symm p = p := by
  change (Equiv.refl EuclideanFourBallCollarDomain).symm p = p
  rfl

/-- The recharted-to-natural identity diffeomorphism is, in particular, a local
diffeomorphism at every point. -/
theorem isLocalDiffeomorph_coordinateUnlinkExteriorRechartedFourBallCollarIdentity :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      euclideanFourBallCollarModel ∞
      (id : EuclideanFourBallCollarDomain →
        EuclideanFourBallCollarDomain) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  have hfun :
      (⇑coordinateUnlinkExteriorRechartedFourBallCollarIdentityDiffeomorph :
        EuclideanFourBallCollarDomain → EuclideanFourBallCollarDomain) = id := by
    funext p
    exact coordinateUnlinkExteriorRechartedFourBallCollarIdentityDiffeomorph_apply p
  rw [← hfun]
  exact coordinateUnlinkExteriorRechartedFourBallCollarIdentityDiffeomorph.isLocalDiffeomorph

/-- Recharting the four-ball collar in exterior coordinates does not change its model
boundary. -/
theorem coordinateUnlinkExteriorRechartedFourBallCollar_boundary :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    coordinateUnlinkExteriorModel.boundary EuclideanFourBallCollarDomain =
      euclideanFourBallCollarModel.boundary EuclideanFourBallCollarDomain := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  have h :=
    coordinateUnlinkExteriorRechartedFourBallCollarIdentityDiffeomorph.preimage_boundary
      (by simp)
  have hfun :
      (⇑coordinateUnlinkExteriorRechartedFourBallCollarIdentityDiffeomorph :
        EuclideanFourBallCollarDomain → EuclideanFourBallCollarDomain) = id := by
    funext p
    exact coordinateUnlinkExteriorRechartedFourBallCollarIdentityDiffeomorph_apply p
  rw [hfun, preimage_id] at h
  exact h.symm

/-- The boundary of the recharted finite collar family is exactly the inverse image under the
second projection of the natural zero-time face. -/
theorem coordinateUnlinkExteriorRechartedFourBallCollarFamily_boundary
    (m : ℕ) :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    coordinateUnlinkExteriorModel.boundary
        (ZMod m × EuclideanFourBallCollarDomain) =
      Prod.snd ⁻¹' ((univ : Set (Sphere 3)) ×ˢ
        {euclideanFourBallCollarZero}) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  have hlocal : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × EuclideanFourBallCollarDomain →
        EuclideanFourBallCollarDomain) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
        (isLocalHomeomorph_discreteProdSnd (D := ZMod m)
          (P := EuclideanFourBallCollarDomain))
  have hboundary := hlocal.preimage_boundary (by simp)
  calc
    coordinateUnlinkExteriorModel.boundary
        (ZMod m × EuclideanFourBallCollarDomain) =
        Prod.snd ⁻¹' coordinateUnlinkExteriorModel.boundary
          EuclideanFourBallCollarDomain := hboundary.symm
    _ = Prod.snd ⁻¹' euclideanFourBallCollarModel.boundary
          EuclideanFourBallCollarDomain := by
      rw [coordinateUnlinkExteriorRechartedFourBallCollar_boundary]
    _ = Prod.snd ⁻¹' ((univ : Set (Sphere 3)) ×ˢ
          {euclideanFourBallCollarZero}) := by
      rw [euclideanFourBallCollarModel_boundary]

end SplittingSpheres
