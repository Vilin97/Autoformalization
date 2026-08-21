/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.CoordinateUnlinkExteriorSmoothAtlas

/-!
# The natural boundary-collar model for the coordinate unlink exterior

The natural four-dimensional half-space model `(𝓡 3).prod (𝓡∂ 1)` has carrier
`EuclideanSpace ℝ (Fin 3) × EuclideanHalfSpace 1`.  This file gives an explicit product
homeomorphism from that carrier to the coordinate-unlink exterior model carrier and the
corresponding continuous linear equivalence of ambient vector spaces.

The exact coordinate identities let smooth changes of coordinates in the natural collar model
be conjugated into the exterior atlas model.  No atlas on a ball or cut side, and no gluing
statement, is constructed here.
-/

@[expose] public section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-- The ambient vector space of the natural three-dimensional-boundary collar model. -/
abbrev CoordinateUnlinkBoundaryCollarModelVector :=
  EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1)

/-- The carrier `ℝ³ × ℝ_{≥0}` of the natural four-dimensional boundary-collar model. -/
abbrev CoordinateUnlinkBoundaryCollarModelSpace :=
  ModelProd (EuclideanSpace ℝ (Fin 3)) (EuclideanHalfSpace 1)

/-- The natural four-dimensional half-space model for a three-dimensional boundary collar. -/
abbrev coordinateUnlinkBoundaryCollarModel :
    ModelWithCorners ℝ CoordinateUnlinkBoundaryCollarModelVector
      CoordinateUnlinkBoundaryCollarModelSpace :=
  (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
    (modelWithCornersEuclideanHalfSpace 1)

/-- A continuous linear identification `ℝ³ ≃ ℝ² × ℝ` used to associate the
natural collar carrier with the coordinate exterior carrier. -/
def coordinateUnlinkBoundaryTangentialLinearEquiv :
    EuclideanSpace ℝ (Fin 3) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

/-- The product homeomorphism from the natural boundary-collar carrier to the literal carrier
used by the coordinate-unlink exterior atlas. -/
def coordinateUnlinkBoundaryCollarModelHomeomorph :
    CoordinateUnlinkBoundaryCollarModelSpace ≃ₜ
      CoordinateUnlinkExteriorModelSpace :=
  ((coordinateUnlinkBoundaryTangentialLinearEquiv.toHomeomorph).prodCongr
      (Homeomorph.refl (EuclideanHalfSpace 1))).trans
    (Homeomorph.prodAssoc
      (EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace ℝ (Fin 1))
      (EuclideanHalfSpace 1))

/-- The corresponding continuous linear equivalence between the natural collar vector model
and the exterior atlas's Euclidean four-space. -/
def coordinateUnlinkBoundaryCollarVectorLinearEquiv :
    CoordinateUnlinkBoundaryCollarModelVector ≃L[ℝ]
      EuclideanSpace ℝ (Fin 4) :=
  ((coordinateUnlinkBoundaryTangentialLinearEquiv.prodCongr
      (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 1)))).trans
    (ContinuousLinearEquiv.prodAssoc ℝ
      (EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace ℝ (Fin 1))
      (EuclideanSpace ℝ (Fin 1)))).trans
    coordinateUnlinkExteriorModelLinearEquiv

/-- In forward coordinates, the carrier homeomorphism agrees exactly with the vector-space
continuous linear equivalence. -/
theorem coordinateUnlinkBoundaryCollarModel_coordinate_eq
    (p : CoordinateUnlinkBoundaryCollarModelSpace) :
    coordinateUnlinkExteriorModel
        (coordinateUnlinkBoundaryCollarModelHomeomorph p) =
      coordinateUnlinkBoundaryCollarVectorLinearEquiv
        (coordinateUnlinkBoundaryCollarModel p) := by
  rfl

/-- In inverse coordinates, the carrier homeomorphism agrees exactly with the inverse
vector-space continuous linear equivalence. -/
theorem coordinateUnlinkBoundaryCollarModel_coordinate_symm_eq
    (p : CoordinateUnlinkExteriorModelSpace) :
    coordinateUnlinkBoundaryCollarModel
        (coordinateUnlinkBoundaryCollarModelHomeomorph.symm p) =
      coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm
        (coordinateUnlinkExteriorModel p) := by
  apply coordinateUnlinkBoundaryCollarVectorLinearEquiv.injective
  rw [coordinateUnlinkBoundaryCollarVectorLinearEquiv.apply_symm_apply]
  rw [← coordinateUnlinkBoundaryCollarModel_coordinate_eq
    (coordinateUnlinkBoundaryCollarModelHomeomorph.symm p)]
  rw [coordinateUnlinkBoundaryCollarModelHomeomorph.apply_symm_apply]

/-- Conjugate a coordinate change in the natural collar carrier into the exterior model
carrier. -/
def coordinateUnlinkBoundaryCollarConjugate
    (e : OpenPartialHomeomorph CoordinateUnlinkBoundaryCollarModelSpace
      CoordinateUnlinkBoundaryCollarModelSpace) :
    OpenPartialHomeomorph CoordinateUnlinkExteriorModelSpace
      CoordinateUnlinkExteriorModelSpace :=
  coordinateUnlinkBoundaryCollarModelHomeomorph.symm.toOpenPartialHomeomorph.trans
    (e.trans coordinateUnlinkBoundaryCollarModelHomeomorph.toOpenPartialHomeomorph)

/-- The source of the conjugated coordinate change is the corresponding carrier-homeomorphism
image of the original source. -/
@[simp]
theorem coordinateUnlinkBoundaryCollarConjugate_source
    (e : OpenPartialHomeomorph CoordinateUnlinkBoundaryCollarModelSpace
      CoordinateUnlinkBoundaryCollarModelSpace) :
    (coordinateUnlinkBoundaryCollarConjugate e).source =
      coordinateUnlinkBoundaryCollarModelHomeomorph.symm ⁻¹' e.source := by
  simp [coordinateUnlinkBoundaryCollarConjugate]

/-- Pointwise evaluation of a conjugated coordinate change. -/
@[simp]
theorem coordinateUnlinkBoundaryCollarConjugate_apply
    (e : OpenPartialHomeomorph CoordinateUnlinkBoundaryCollarModelSpace
      CoordinateUnlinkBoundaryCollarModelSpace)
    (q : CoordinateUnlinkExteriorModelSpace) :
    coordinateUnlinkBoundaryCollarConjugate e q =
      coordinateUnlinkBoundaryCollarModelHomeomorph
        (e (coordinateUnlinkBoundaryCollarModelHomeomorph.symm q)) :=
  rfl

/-- Conjugation commutes with inversion of open partial homeomorphisms. -/
@[simp]
theorem coordinateUnlinkBoundaryCollarConjugate_symm
    (e : OpenPartialHomeomorph CoordinateUnlinkBoundaryCollarModelSpace
      CoordinateUnlinkBoundaryCollarModelSpace) :
    (coordinateUnlinkBoundaryCollarConjugate e).symm =
      coordinateUnlinkBoundaryCollarConjugate e.symm := by
  unfold coordinateUnlinkBoundaryCollarConjugate
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  simp only [Homeomorph.symm_toOpenPartialHomeomorph,
    OpenPartialHomeomorph.symm_symm]
  rw [OpenPartialHomeomorph.trans_assoc]

private theorem coordinateUnlinkBoundaryCollarModel_symm_vector
    (z : EuclideanSpace ℝ (Fin 4))
    (hz : z ∈ range coordinateUnlinkExteriorModel) :
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

private theorem coordinateUnlinkBoundaryCollarConjugate_coordinate
    (e : OpenPartialHomeomorph CoordinateUnlinkBoundaryCollarModelSpace
      CoordinateUnlinkBoundaryCollarModelSpace)
    (z : EuclideanSpace ℝ (Fin 4))
    (hz : z ∈ range coordinateUnlinkExteriorModel) :
    coordinateUnlinkExteriorModel
        (coordinateUnlinkBoundaryCollarConjugate e
          (coordinateUnlinkExteriorModel.symm z)) =
      coordinateUnlinkBoundaryCollarVectorLinearEquiv
        (coordinateUnlinkBoundaryCollarModel
          (e (coordinateUnlinkBoundaryCollarModel.symm
            (coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm z)))) := by
  rw [coordinateUnlinkBoundaryCollarConjugate_apply,
    coordinateUnlinkBoundaryCollarModel_coordinate_eq,
    coordinateUnlinkBoundaryCollarModel_symm_vector z hz]

private theorem coordinateUnlinkBoundaryCollarConjugate_maps_coordinateDomain
    (e : OpenPartialHomeomorph CoordinateUnlinkBoundaryCollarModelSpace
      CoordinateUnlinkBoundaryCollarModelSpace)
    {z : EuclideanSpace ℝ (Fin 4)}
    (hz : z ∈ coordinateUnlinkExteriorModel.symm ⁻¹'
        (coordinateUnlinkBoundaryCollarConjugate e).source ∩
      range coordinateUnlinkExteriorModel) :
    coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm z ∈
      coordinateUnlinkBoundaryCollarModel.symm ⁻¹' e.source ∩
        range coordinateUnlinkBoundaryCollarModel := by
  have hzrange : z ∈ range coordinateUnlinkExteriorModel := hz.2
  have hsymm := coordinateUnlinkBoundaryCollarModel_symm_vector z hzrange
  constructor
  · rw [mem_preimage, hsymm]
    rw [coordinateUnlinkBoundaryCollarConjugate_source] at hz
    exact hz.1
  · refine ⟨coordinateUnlinkBoundaryCollarModelHomeomorph.symm
        (coordinateUnlinkExteriorModel.symm z), ?_⟩
    exact (coordinateUnlinkBoundaryCollarModel_coordinate_symm_eq
      (coordinateUnlinkExteriorModel.symm z)).trans (by
        rw [coordinateUnlinkExteriorModel.right_inv hzrange])

private theorem coordinateUnlinkBoundaryCollarConjugate_mem_pregroupoid
    {n : ℕ∞ω}
    (e : OpenPartialHomeomorph CoordinateUnlinkBoundaryCollarModelSpace
      CoordinateUnlinkBoundaryCollarModelSpace)
    (he : (contDiffPregroupoid n coordinateUnlinkBoundaryCollarModel).property
      e e.source) :
    (contDiffPregroupoid n coordinateUnlinkExteriorModel).property
      (coordinateUnlinkBoundaryCollarConjugate e)
        (coordinateUnlinkBoundaryCollarConjugate e).source := by
  rw [contDiffPregroupoid] at he ⊢
  let D := coordinateUnlinkExteriorModel.symm ⁻¹'
      (coordinateUnlinkBoundaryCollarConjugate e).source ∩
    range coordinateUnlinkExteriorModel
  have hpre : ContDiffOn ℝ n
      ((coordinateUnlinkBoundaryCollarModel ∘ e ∘
        coordinateUnlinkBoundaryCollarModel.symm) ∘
          coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm) D :=
    he.comp coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm.contDiff.contDiffOn
      (fun _ hz ↦
        coordinateUnlinkBoundaryCollarConjugate_maps_coordinateDomain e hz)
  have hpost : ContDiffOn ℝ n
      (coordinateUnlinkBoundaryCollarVectorLinearEquiv ∘
        ((coordinateUnlinkBoundaryCollarModel ∘ e ∘
          coordinateUnlinkBoundaryCollarModel.symm) ∘
            coordinateUnlinkBoundaryCollarVectorLinearEquiv.symm)) D :=
    coordinateUnlinkBoundaryCollarVectorLinearEquiv.contDiff.comp_contDiffOn hpre
  exact hpost.congr fun z hz ↦
    (coordinateUnlinkBoundaryCollarConjugate_coordinate e z hz.2).symm

/-- Conjugation carries a smooth collar-model coordinate change into the smooth groupoid of the
coordinate-unlink exterior model. -/
theorem coordinateUnlinkBoundaryCollarConjugate_mem_contDiffGroupoid
    {n : ℕ∞ω}
    (e : OpenPartialHomeomorph CoordinateUnlinkBoundaryCollarModelSpace
      CoordinateUnlinkBoundaryCollarModelSpace)
    (he : e ∈ contDiffGroupoid n coordinateUnlinkBoundaryCollarModel) :
    coordinateUnlinkBoundaryCollarConjugate e ∈
      contDiffGroupoid n coordinateUnlinkExteriorModel := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at he ⊢
  constructor
  · exact coordinateUnlinkBoundaryCollarConjugate_mem_pregroupoid e he.1
  · change (contDiffPregroupoid n coordinateUnlinkExteriorModel).property
      (coordinateUnlinkBoundaryCollarConjugate e).symm
        (coordinateUnlinkBoundaryCollarConjugate e).symm.source
    rw [coordinateUnlinkBoundaryCollarConjugate_symm]
    exact coordinateUnlinkBoundaryCollarConjugate_mem_pregroupoid e.symm he.2

end SplittingSpheres
