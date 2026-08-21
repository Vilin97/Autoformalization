/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkExteriorCollar

/-!
# A smooth atlas on the literal coordinate-unlink exterior

The closed radius-`1/8` exterior of the coordinate unlink is covered by its strict ambient
interior and two explicit radial collars.  This file puts those charts in one four-dimensional
model with corners and checks every transition: ambient--ambient, collar--collar, and the mixed
transitions.  The mixed inverse is the actual punctured-tube polar coordinate map, not a
transported topological atlas.

The resulting charted space is a smooth four-manifold with boundary.  Its model boundary is
exactly the two radial faces where one normal distance equals `1/8`.

No atlas is transported through a flower, cap, pushout, or other point-set decomposition, and no
claim about compatibility with those constructions is made here.
-/

@[expose] public section

open Function Metric Set Topology
open TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-- A product presentation of the four-dimensional vector model used for the exterior atlas. -/
abbrev CoordinateUnlinkExteriorModelVector :=
  EuclideanSpace ℝ (Fin 2) ×
    (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))

/-- The product model space `ℝ² × (ℝ × ℝ_{≥0})` for the exterior atlas. -/
abbrev CoordinateUnlinkExteriorModelSpace :=
  ModelProd (EuclideanSpace ℝ (Fin 2))
    (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1))

/-- A fixed continuous linear identification of the product vector model with `ℝ⁴`. -/
def coordinateUnlinkExteriorModelLinearEquiv :
    CoordinateUnlinkExteriorModelVector ≃L[ℝ]
      EuclideanSpace ℝ (Fin 4) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [CoordinateUnlinkExteriorModelVector])

/-- The common four-dimensional model with corners used by both ambient and collar charts. -/
abbrev coordinateUnlinkExteriorModel :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 4))
      CoordinateUnlinkExteriorModelSpace :=
  standardUnlinkExteriorCollarModel.transContinuousLinearEquiv
    coordinateUnlinkExteriorModelLinearEquiv

/-- The common exterior model has nonempty vector-space interior. -/
theorem coordinateUnlinkExteriorModel_nonemptyInterior :
    (interior (range coordinateUnlinkExteriorModel)).Nonempty :=
  coordinateUnlinkExteriorModel.nonempty_interior

/-- The part of the common model space mapped into the vector-space interior. -/
def coordinateUnlinkExteriorModelInteriorOpens :
    Opens CoordinateUnlinkExteriorModelSpace :=
  ⟨coordinateUnlinkExteriorModel ⁻¹'
      interior (range coordinateUnlinkExteriorModel),
    isOpen_interior.preimage coordinateUnlinkExteriorModel.continuous⟩

/-- The model-interior open subspace. -/
abbrev CoordinateUnlinkExteriorModelInterior :=
  coordinateUnlinkExteriorModelInteriorOpens

/-- The model-interior open subspace is nonempty. -/
theorem nonempty_coordinateUnlinkExteriorModelInterior :
    Nonempty CoordinateUnlinkExteriorModelInterior := by
  obtain ⟨y, hy⟩ := coordinateUnlinkExteriorModel_nonemptyInterior
  refine ⟨⟨coordinateUnlinkExteriorModel.symm y, ?_⟩⟩
  change coordinateUnlinkExteriorModel
      (coordinateUnlinkExteriorModel.symm y) ∈
    interior (range coordinateUnlinkExteriorModel)
  rwa [coordinateUnlinkExteriorModel.right_inv (interior_subset hy)]

/-- The canonical nonemptiness instance for the model-interior open subspace. -/
instance instNonemptyCoordinateUnlinkExteriorModelInterior :
    Nonempty CoordinateUnlinkExteriorModelInterior :=
  nonempty_coordinateUnlinkExteriorModelInterior

/-- Include the model-interior open subspace into the common Euclidean vector model. -/
def coordinateUnlinkExteriorModelInteriorInclusion
    (x : CoordinateUnlinkExteriorModelInterior) :
    EuclideanSpace ℝ (Fin 4) :=
  coordinateUnlinkExteriorModel x.1

/-- The model-interior inclusion has image exactly the interior of the model range. -/
theorem range_coordinateUnlinkExteriorModelInteriorInclusion :
    range coordinateUnlinkExteriorModelInteriorInclusion =
      interior (range coordinateUnlinkExteriorModel) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hy
    refine ⟨⟨coordinateUnlinkExteriorModel.symm y, ?_⟩, ?_⟩
    · change coordinateUnlinkExteriorModel
          (coordinateUnlinkExteriorModel.symm y) ∈
        interior (range coordinateUnlinkExteriorModel)
      rw [coordinateUnlinkExteriorModel.right_inv (interior_subset hy)]
      exact hy
    · exact coordinateUnlinkExteriorModel.right_inv (interior_subset hy)

/-- The model-interior inclusion is an open embedding. -/
theorem isOpenEmbedding_coordinateUnlinkExteriorModelInteriorInclusion :
    IsOpenEmbedding coordinateUnlinkExteriorModelInteriorInclusion := by
  refine ⟨?_, ?_⟩
  · exact coordinateUnlinkExteriorModel.isClosedEmbedding.isEmbedding.comp
      IsEmbedding.subtypeVal
  · rw [range_coordinateUnlinkExteriorModelInteriorInclusion]
    exact isOpen_interior

/-- The inverse model map as an open partial homeomorphism from the vector-space interior. -/
def coordinateUnlinkExteriorModelInteriorOpenPartialHomeomorph :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 4))
      CoordinateUnlinkExteriorModelSpace where
  toFun := coordinateUnlinkExteriorModel.symm
  invFun := coordinateUnlinkExteriorModel
  source := interior (range coordinateUnlinkExteriorModel)
  target := coordinateUnlinkExteriorModel ⁻¹'
    interior (range coordinateUnlinkExteriorModel)
  map_source' y hy := by
    change coordinateUnlinkExteriorModel
        (coordinateUnlinkExteriorModel.symm y) ∈
      interior (range coordinateUnlinkExteriorModel)
    rwa [coordinateUnlinkExteriorModel.right_inv (interior_subset hy)]
  map_target' x hx := hx
  left_inv' y hy :=
    coordinateUnlinkExteriorModel.right_inv (interior_subset hy)
  right_inv' x _ := coordinateUnlinkExteriorModel.left_inv x
  open_source := isOpen_interior
  open_target := isOpen_interior.preimage
    coordinateUnlinkExteriorModel.continuous
  continuousOn_toFun :=
    coordinateUnlinkExteriorModel.continuous_symm.continuousOn
  continuousOn_invFun :=
    coordinateUnlinkExteriorModel.continuous.continuousOn

/-- A fixed base point in the vector-space interior of the common model. -/
def coordinateUnlinkExteriorModelInteriorBasePoint :
    EuclideanSpace ℝ (Fin 4) :=
  coordinateUnlinkExteriorModel_nonemptyInterior.choose

/-- The fixed model base point belongs to the vector-space interior. -/
theorem coordinateUnlinkExteriorModelInteriorBasePoint_mem :
    coordinateUnlinkExteriorModelInteriorBasePoint ∈
      interior (range coordinateUnlinkExteriorModel) :=
  coordinateUnlinkExteriorModel_nonemptyInterior.choose_spec


/-- The literal closed radius-`1/8` exterior of the coordinate unlink. -/
abbrev CoordinateUnlinkExteriorEighth :=
  CoordinateUnlinkExteriorSubtype (1 / 8 : ℝ)

/-- The strict part of the closed exterior, away from both radial boundary faces. -/
def coordinateUnlinkExteriorEighthInteriorOpens :
    Opens CoordinateUnlinkExteriorEighth :=
  ⟨{q | q.1 ∈ (standardUnlinkClosedTubes (1 / 8 : ℝ))ᶜ},
    (isClosed_standardUnlinkClosedTubes (1 / 8 : ℝ)).isOpen_compl.preimage
      continuous_subtype_val⟩

/-- The strict exterior as an open subspace of the closed exterior. -/
abbrev CoordinateUnlinkExteriorEighthInterior :=
  coordinateUnlinkExteriorEighthInteriorOpens

/-- Include the strict part of the exterior into the ambient four-sphere. -/
def coordinateUnlinkExteriorEighthInteriorToSphere
    (q : CoordinateUnlinkExteriorEighthInterior) : Sphere 4 :=
  q.1.1

/-- The strict-interior inclusion has image the complement of the two closed tubes. -/
theorem range_coordinateUnlinkExteriorEighthInteriorToSphere :
    range coordinateUnlinkExteriorEighthInteriorToSphere =
      (standardUnlinkClosedTubes (1 / 8 : ℝ))ᶜ := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hq
    have hext : q ∈ coordinateUnlinkExterior (1 / 8 : ℝ) := by
      exact compl_subset_compl.mpr
        (standardUnlinkOpenTubes_subset_closedTubes (1 / 8 : ℝ)) hq
    exact ⟨⟨⟨q, hext⟩, hq⟩, rfl⟩

/-- The strict-interior inclusion into the four-sphere is an open embedding. -/
theorem isOpenEmbedding_coordinateUnlinkExteriorEighthInteriorToSphere :
    IsOpenEmbedding coordinateUnlinkExteriorEighthInteriorToSphere := by
  refine ⟨?_, ?_⟩
  · exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  · rw [range_coordinateUnlinkExteriorEighthInteriorToSphere]
    exact (isClosed_standardUnlinkClosedTubes (1 / 8 : ℝ)).isOpen_compl

/-- An ambient `S⁴` chart on the strict interior, shifted into the common model interior. -/
def coordinateUnlinkExteriorEighthAmbientChartOnInterior
    (x : CoordinateUnlinkExteriorEighthInterior) :
    OpenPartialHomeomorph CoordinateUnlinkExteriorEighthInterior
      CoordinateUnlinkExteriorModelSpace := by
  letI : Nonempty CoordinateUnlinkExteriorEighthInterior := ⟨x⟩
  let inclusionChart : OpenPartialHomeomorph
      CoordinateUnlinkExteriorEighthInterior (Sphere 4) :=
    isOpenEmbedding_coordinateUnlinkExteriorEighthInteriorToSphere
      |>.toOpenPartialHomeomorph
        coordinateUnlinkExteriorEighthInteriorToSphere
  let shift : EuclideanSpace ℝ (Fin 4) :=
    coordinateUnlinkExteriorModelInteriorBasePoint -
      chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1 x.1.1
  let localChart :=
    (((inclusionChart.trans
      (chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1)).trans
        (Homeomorph.addRight shift).toOpenPartialHomeomorph).trans
      coordinateUnlinkExteriorModelInteriorOpenPartialHomeomorph)
  exact localChart

/-- Extend a strict-interior ambient chart to the literal closed exterior along its open
embedding. -/
def coordinateUnlinkExteriorEighthAmbientChart
    (x : CoordinateUnlinkExteriorEighthInterior) :
    OpenPartialHomeomorph CoordinateUnlinkExteriorEighth
      CoordinateUnlinkExteriorModelSpace :=
  (coordinateUnlinkExteriorEighthAmbientChartOnInterior x).lift_openEmbedding
    coordinateUnlinkExteriorEighthInteriorOpens.2.isOpenEmbedding_subtypeVal

/-- The center of a strict-interior ambient chart belongs to its source. -/
theorem mem_coordinateUnlinkExteriorEighthAmbientChart_source
    (x : CoordinateUnlinkExteriorEighthInterior) :
    x.1 ∈ (coordinateUnlinkExteriorEighthAmbientChart x).source := by
  simp only [coordinateUnlinkExteriorEighthAmbientChart, Opens.carrier_eq_coe,
    coordinateUnlinkExteriorEighthAmbientChartOnInterior, Nat.reduceAdd,
    coordinateUnlinkExteriorModelInteriorOpenPartialHomeomorph,
    ModelWithCorners.coe_transContinuousLinearEquiv_symm,
    modelWithCorners_prod_coe_symm, modelWithCornersSelf_coe_symm,
    ModelWithCorners.coe_transContinuousLinearEquiv, modelWithCorners_prod_coe,
    modelWithCornersSelf_coe, OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.trans_toPartialEquiv, PartialEquiv.trans_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_source, PartialHomeomorph.toFun_eq_coe,
    OpenPartialHomeomorph.coe_toPartialHomeomorph,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply, univ_inter, PartialEquiv.coe_trans,
    Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ,
    Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.coe_addRight, mem_image,
    mem_inter_iff, mem_preimage, comp_apply, SetLike.coe_eq_coe, exists_eq_right]
  refine ⟨ChartedSpace.mem_chart_source x.1.1, ?_⟩
  change chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1 x.1.1 +
      (coordinateUnlinkExteriorModelInteriorBasePoint -
        chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1 x.1.1) ∈
    interior (range coordinateUnlinkExteriorModel)
  have heq : chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1 x.1.1 +
      (coordinateUnlinkExteriorModelInteriorBasePoint -
        chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1 x.1.1) =
      coordinateUnlinkExteriorModelInteriorBasePoint := by abel
  rw [heq]
  exact coordinateUnlinkExteriorModelInteriorBasePoint_mem

/-- The common collar-coordinate domain `S² × S¹ × [1/8,1/4)`. -/
abbrev CoordinateUnlinkExteriorEighthCollarDomain :=
  Sphere 2 × (Sphere 1 × CoordinateUnlinkExteriorEighthCollarRadius)

/-- Include either explicit radial collar into the literal closed exterior. -/
def coordinateUnlinkExteriorEighthCollarToExterior
    (i : Fin 2) (p : CoordinateUnlinkExteriorEighthCollarDomain) :
    CoordinateUnlinkExteriorEighth :=
  (standardUnlinkExteriorCollarOpenHomeomorph i
    (r := (1 / 8 : ℝ)) (R := (1 / 4 : ℝ)) (by norm_num) (by norm_num) p).1

/-- Either collar inclusion is an open embedding into the literal exterior. -/
theorem isOpenEmbedding_coordinateUnlinkExteriorEighthCollarToExterior
    (i : Fin 2) :
    IsOpenEmbedding (coordinateUnlinkExteriorEighthCollarToExterior i) := by
  exact standardUnlinkExteriorCollarOpens i (1 / 8 : ℝ) (1 / 4 : ℝ)
    |>.2.isOpenEmbedding_subtypeVal.comp
      (standardUnlinkExteriorCollarOpenHomeomorph i
        (r := (1 / 8 : ℝ)) (R := (1 / 4 : ℝ))
        (by norm_num) (by norm_num)).isOpenEmbedding

/-- A native product collar chart, lifted along the actual collar inclusion. -/
def coordinateUnlinkExteriorEighthCollarChart
    (i : Fin 2) (p : CoordinateUnlinkExteriorEighthCollarDomain) :
    OpenPartialHomeomorph CoordinateUnlinkExteriorEighth
      CoordinateUnlinkExteriorModelSpace :=
  (chartAt CoordinateUnlinkExteriorModelSpace p).lift_openEmbedding
    (isOpenEmbedding_coordinateUnlinkExteriorEighthCollarToExterior i)

/-- The image of a collar-chart center belongs to the lifted chart source. -/
theorem mem_coordinateUnlinkExteriorEighthCollarChart_source
    (i : Fin 2) (p : CoordinateUnlinkExteriorEighthCollarDomain) :
    coordinateUnlinkExteriorEighthCollarToExterior i p ∈
      (coordinateUnlinkExteriorEighthCollarChart i p).source := by
  rw [coordinateUnlinkExteriorEighthCollarChart,
    OpenPartialHomeomorph.lift_openEmbedding_source]
  exact ⟨p, ChartedSpace.mem_chart_source p, rfl⟩

/-- Every point of the literal exterior lies either in its strict part or in one of the two
explicit radius-`1/8` collars. -/
theorem coordinateUnlinkExteriorEighth_interior_or_collar
    (q : CoordinateUnlinkExteriorEighth) :
    q ∈ coordinateUnlinkExteriorEighthInteriorOpens ∨
      ∃ i : Fin 2, ∃ p : CoordinateUnlinkExteriorEighthCollarDomain,
        coordinateUnlinkExteriorEighthCollarToExterior i p = q := by
  by_cases hstrict : q.1 ∈ (standardUnlinkClosedTubes (1 / 8 : ℝ))ᶜ
  · exact Or.inl hstrict
  · right
    have hclosed : q.1 ∈ standardUnlinkClosedTubes (1 / 8 : ℝ) := by
      simpa only [mem_compl_iff, not_not] using hstrict
    have build (i : Fin 2)
        (hi : q.1 ∈ standardUnlinkClosedTube i (1 / 8 : ℝ)) :
        ∃ p : CoordinateUnlinkExteriorEighthCollarDomain,
          coordinateUnlinkExteriorEighthCollarToExterior i p = q := by
      have hiQuarter : q.1 ∈ standardUnlinkOpenTube i (1 / 4 : ℝ) := by
        change standardUnlinkNormalProjection q.1 ∈
          ball (standardUnlinkNormalCenter i) (1 / 4 : ℝ)
        change standardUnlinkNormalProjection q.1 ∈
          closedBall (standardUnlinkNormalCenter i) (1 / 8 : ℝ) at hi
        exact closedBall_subset_ball (by norm_num) hi
      let z : StandardUnlinkExteriorCollar i (1 / 8 : ℝ) (1 / 4 : ℝ) :=
        ⟨q.1, q.2, hiQuarter⟩
      let p : CoordinateUnlinkExteriorEighthCollarDomain :=
        (standardUnlinkExteriorEighthCollarHomeomorph i).symm z
      refine ⟨p, ?_⟩
      apply Subtype.ext
      change (standardUnlinkExteriorEighthCollarHomeomorph i p).1 = q.1
      simpa only [p, z] using congrArg Subtype.val
        ((standardUnlinkExteriorEighthCollarHomeomorph i).apply_symm_apply z)
    rcases hclosed with hzero | hone
    · exact ⟨0, build 0 hzero⟩
    · exact ⟨1, build 1 hone⟩

/-- The two radial faces where one normal distance is exactly `1/8`. -/
def coordinateUnlinkExteriorEighthRadialBoundary :
    Set CoordinateUnlinkExteriorEighth :=
  {q | ∃ i : Fin 2,
    ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter i‖ =
      (1 / 8 : ℝ)}

/-- Strict-exterior membership is equivalent to both normal distances being greater than `1/8`. -/
theorem mem_coordinateUnlinkExteriorEighthInteriorOpens_iff
    (q : CoordinateUnlinkExteriorEighth) :
    q ∈ coordinateUnlinkExteriorEighthInteriorOpens ↔
      ∀ i : Fin 2,
        (1 / 8 : ℝ) <
          ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter i‖ := by
  change q.1 ∉ standardUnlinkClosedTubes (1 / 8 : ℝ) ↔ _
  simp only [standardUnlinkClosedTubes, standardUnlinkClosedTube,
    mem_union, mem_preimage, mem_closedBall, dist_eq_norm, not_or, not_le]
  constructor
  · rintro ⟨hzero, hone⟩ i
    fin_cases i
    · exact hzero
    · exact hone
  · intro h
    exact ⟨h 0, h 1⟩

/-- The radial faces are exactly the complement of the strict part of the exterior. -/
theorem coordinateUnlinkExteriorEighthRadialBoundary_eq_compl_interior :
    coordinateUnlinkExteriorEighthRadialBoundary =
      (coordinateUnlinkExteriorEighthInteriorOpens :
        Set CoordinateUnlinkExteriorEighth)ᶜ := by
  ext q
  rw [mem_compl_iff,
    show q ∈ (coordinateUnlinkExteriorEighthInteriorOpens :
        Set CoordinateUnlinkExteriorEighth) ↔
        ∀ i : Fin 2, (1 / 8 : ℝ) <
          ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter i‖ from
      mem_coordinateUnlinkExteriorEighthInteriorOpens_iff q]
  constructor
  · rintro ⟨i, hi⟩ hall
    exact (ne_of_gt (hall i)) hi
  · intro hnot
    push Not at hnot
    obtain ⟨i, hi⟩ := hnot
    refine ⟨i, le_antisymm hi ?_⟩
    apply le_of_not_gt
    intro hlt
    have htube : q.1 ∈ standardUnlinkOpenTube i (1 / 8 : ℝ) := by
      change standardUnlinkNormalProjection q.1 ∈
        ball (standardUnlinkNormalCenter i) (1 / 8 : ℝ)
      simpa only [mem_ball, dist_eq_norm] using hlt
    have htubes : q.1 ∈ standardUnlinkOpenTubes (1 / 8 : ℝ) := by
      fin_cases i
      · exact Or.inl htube
      · exact Or.inr htube
    exact q.2 htubes

/-- At each exterior point, choose an ambient chart in the strict part and a collar chart on a
radial face. -/
def coordinateUnlinkExteriorEighthPreferredChart
    (q : CoordinateUnlinkExteriorEighth) :
    OpenPartialHomeomorph CoordinateUnlinkExteriorEighth
      CoordinateUnlinkExteriorModelSpace := by
  classical
  by_cases hq : q ∈ coordinateUnlinkExteriorEighthInteriorOpens
  · exact coordinateUnlinkExteriorEighthAmbientChart ⟨q, hq⟩
  · have hcollar :=
      (coordinateUnlinkExteriorEighth_interior_or_collar q).resolve_left hq
    exact coordinateUnlinkExteriorEighthCollarChart hcollar.choose
      hcollar.choose_spec.choose

/-- Every exterior point belongs to the source of its preferred chart. -/
theorem mem_coordinateUnlinkExteriorEighthPreferredChart_source
    (q : CoordinateUnlinkExteriorEighth) :
    q ∈ (coordinateUnlinkExteriorEighthPreferredChart q).source := by
  classical
  rw [coordinateUnlinkExteriorEighthPreferredChart]
  split_ifs with hq
  · exact mem_coordinateUnlinkExteriorEighthAmbientChart_source ⟨q, hq⟩
  · let hcollar :=
      (coordinateUnlinkExteriorEighth_interior_or_collar q).resolve_left hq
    let i := hcollar.choose
    let p := hcollar.choose_spec.choose
    have hp := mem_coordinateUnlinkExteriorEighthCollarChart_source i p
    rw [hcollar.choose_spec.choose_spec] at hp
    exact hp


/-- The atlas combining ambient `S⁴` charts on the strict part with the two radial collars. -/
@[instance_reducible]
def coordinateUnlinkExteriorEighthChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      CoordinateUnlinkExteriorEighth where
  atlas :=
    {e | (∃ x : CoordinateUnlinkExteriorEighthInterior,
        e = coordinateUnlinkExteriorEighthAmbientChart x) ∨
      ∃ i : Fin 2, ∃ p : CoordinateUnlinkExteriorEighthCollarDomain,
        e = coordinateUnlinkExteriorEighthCollarChart i p}
  chartAt := coordinateUnlinkExteriorEighthPreferredChart
  mem_chart_source :=
    mem_coordinateUnlinkExteriorEighthPreferredChart_source
  chart_mem_atlas := by
    intro q
    classical
    rw [coordinateUnlinkExteriorEighthPreferredChart]
    split_ifs with hq
    · exact Or.inl ⟨⟨q, hq⟩, rfl⟩
    · let hcollar :=
        (coordinateUnlinkExteriorEighth_interior_or_collar q).resolve_left hq
      exact Or.inr ⟨hcollar.choose, hcollar.choose_spec.choose, rfl⟩


private theorem ModelWithCorners.boundary_transContinuousLinearEquiv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M]
    (I : ModelWithCorners 𝕜 E₁ H) (L : E₁ ≃L[𝕜] E₂) :
    (I.transContinuousLinearEquiv L).boundary M = I.boundary M := by
  ext x
  change L (extChartAt I x x) ∈
      frontier (range (I.transContinuousLinearEquiv L)) ↔
    extChartAt I x x ∈ frontier (range I)
  rw [I.transContinuousLinearEquiv_range]
  have hfront := L.toHomeomorph.image_frontier (range I)
  change L '' frontier (range I) = frontier (L '' range I) at hfront
  rw [← hfront]
  exact L.injective.mem_set_image

private theorem coordinateUnlinkExteriorModel_boundary_collarDomain :
    coordinateUnlinkExteriorModel.boundary
        CoordinateUnlinkExteriorEighthCollarDomain =
      (univ : Set (Sphere 2)) ×ˢ
        ((univ : Set (Sphere 1)) ×ˢ
          {unlinkExteriorCollarInnerRadius (1 / 8 : ℝ) (1 / 4 : ℝ)}) := by
  rw [ModelWithCorners.boundary_transContinuousLinearEquiv]
  exact standardUnlinkExteriorCollarModel_boundary
    (1 / 8 : ℝ) (1 / 4 : ℝ)

private def coordinateUnlinkExteriorEighthPuncturedTubeOverlapOpens
    (i : Fin 2) : Opens (StandardUnlinkPuncturedTube i (1 / 4 : ℝ)) :=
  ⟨{q | (1 / 8 : ℝ) <
      (standardUnlinkPuncturedTubePolarCoordinates i (by norm_num) q).2.2},
    isOpen_lt continuous_const
      ((contMDiff_standardUnlinkPuncturedTubePolarCoordinates i (by norm_num)).continuous
        |>.snd.snd)⟩

private abbrev CoordinateUnlinkExteriorEighthPuncturedTubeOverlap (i : Fin 2) :=
  coordinateUnlinkExteriorEighthPuncturedTubeOverlapOpens i

private def coordinateUnlinkExteriorEighthPuncturedTubePolarCollarCoordinates
    (i : Fin 2)
    (q : CoordinateUnlinkExteriorEighthPuncturedTubeOverlap i) :
    CoordinateUnlinkExteriorEighthCollarDomain := by
  let polar := standardUnlinkPuncturedTubePolarCoordinates i (by norm_num) q.1
  have hlower : (1 / 8 : ℝ) < polar.2.2 := q.2
  have hupper : polar.2.2 < (1 / 4 : ℝ) := by
    rw [standardUnlinkPuncturedTubePolarCoordinates_radius]
    have hmem := q.1.1.2
    change standardUnlinkNormalProjection q.1.1.1 ∈
      ball (standardUnlinkNormalCenter i) (1 / 4 : ℝ) at hmem
    simpa only [mem_ball, dist_eq_norm] using hmem
  exact (polar.1, (polar.2.1,
    ⟨⟨polar.2.2, hlower.le, hupper.le⟩, hupper⟩))

private theorem contMDiff_coordinateUnlinkExteriorEighthPuncturedTubePolarCollarCoordinates
    (i : Fin 2) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      standardUnlinkExteriorCollarModel ∞
      (coordinateUnlinkExteriorEighthPuncturedTubePolarCollarCoordinates i) := by
  have hraw :=
    (contMDiff_standardUnlinkPuncturedTubePolarCoordinates i (by norm_num)).comp
      (contMDiff_subtype_val : ContMDiff
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (Subtype.val : CoordinateUnlinkExteriorEighthPuncturedTubeOverlap i →
          StandardUnlinkPuncturedTube i (1 / 4 : ℝ)))
  have hbase := contMDiff_fst.comp hraw
  have hdirection := contMDiff_fst.comp (contMDiff_snd.comp hraw)
  have hradiusReal := contMDiff_snd.comp (contMDiff_snd.comp hraw)
  have hradius : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersEuclideanHalfSpace 1) ∞
      (fun q : CoordinateUnlinkExteriorEighthPuncturedTubeOverlap i ↦
        (coordinateUnlinkExteriorEighthPuncturedTubePolarCollarCoordinates i q).2.2) := by
    apply (ContMDiff.subtypeVal_comp_iff
      (unlinkExteriorCollarRadius (1 / 8 : ℝ) (1 / 4 : ℝ)) _).mp
    rw [contMDiff_iff_comp_subtypeVal_Icc]
    constructor
    · apply Continuous.subtype_mk
      exact hradiusReal.continuous.congr fun _ ↦ rfl
    · exact hradiusReal.congr fun _ ↦ rfl
  exact (hbase.prodMk (hdirection.prodMk hradius)).congr fun _ ↦ rfl

private theorem probe_ambient_transition_forward
    (x y : CoordinateUnlinkExteriorEighthInterior) :
    ContDiffOn ℝ ∞
      (coordinateUnlinkExteriorModel ∘
        (coordinateUnlinkExteriorEighthAmbientChartOnInterior x).symm.trans
          (coordinateUnlinkExteriorEighthAmbientChartOnInterior y) ∘
        coordinateUnlinkExteriorModel.symm)
      (coordinateUnlinkExteriorModel.symm ⁻¹'
          ((coordinateUnlinkExteriorEighthAmbientChartOnInterior x).symm.trans
            (coordinateUnlinkExteriorEighthAmbientChartOnInterior y)).source ∩
        range coordinateUnlinkExteriorModel) := by
    let cx := chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1
    let cy := chartAt (EuclideanSpace ℝ (Fin 4)) y.1.1
    have hbase := (contDiffGroupoid ∞
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))).compatible
        (chart_mem_atlas (EuclideanSpace ℝ (Fin 4)) x.1.1)
        (chart_mem_atlas (EuclideanSpace ℝ (Fin 4)) y.1.1)
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hbase
    have hg : ContDiffOn ℝ ∞ ((cy : Sphere 4 →
          EuclideanSpace ℝ (Fin 4)) ∘ cx.symm)
        (cx.symm.trans cy).source := by
      simpa only [contDiffPregroupoid, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, id_comp, comp_id,
        OpenPartialHomeomorph.coe_trans, cx, cy, preimage_id, range_id,
        inter_univ] using hbase.1
    let sx := coordinateUnlinkExteriorModelInteriorBasePoint - cx x.1.1
    let sy := coordinateUnlinkExteriorModelInteriorBasePoint - cy y.1.1
    let _ : Nonempty CoordinateUnlinkExteriorEighthInterior := ⟨x⟩
    let j : OpenPartialHomeomorph CoordinateUnlinkExteriorEighthInterior
        (Sphere 4) :=
      isOpenEmbedding_coordinateUnlinkExteriorEighthInteriorToSphere
        |>.toOpenPartialHomeomorph
          coordinateUnlinkExteriorEighthInteriorToSphere
    let tx := (Homeomorph.addRight sx).toOpenPartialHomeomorph
    let ty := (Homeomorph.addRight sy).toOpenPartialHomeomorph
    let D := coordinateUnlinkExteriorModelInteriorOpenPartialHomeomorph
    let bx := (j.trans cx).trans tx
    let bY := (j.trans cy).trans ty
    have hsubset :
        coordinateUnlinkExteriorModel.symm ⁻¹'
            ((coordinateUnlinkExteriorEighthAmbientChartOnInterior x).symm.trans
              (coordinateUnlinkExteriorEighthAmbientChartOnInterior y)).source ∩
            range coordinateUnlinkExteriorModel ⊆
          (fun z ↦ z - sx) ⁻¹' (cx.symm.trans cy).source := by
      intro z hz
      rcases hz.2 with ⟨w, rfl⟩
      have hz' : w ∈ ((bx.trans D).symm.trans (bY.trans D)).source := by
        have hz0 := hz.1
        change coordinateUnlinkExteriorModel.symm
            (coordinateUnlinkExteriorModel w) ∈
          ((coordinateUnlinkExteriorEighthAmbientChartOnInterior x).symm.trans
            (coordinateUnlinkExteriorEighthAmbientChartOnInterior y)).source at hz0
        rw [coordinateUnlinkExteriorModel.left_inv] at hz0
        change w ∈ ((bx.trans D).symm.trans (bY.trans D)).source at hz0
        exact hz0
      rw [OpenPartialHomeomorph.trans_source] at hz'
      have hwtarget := hz'.1
      rw [OpenPartialHomeomorph.symm_source,
        OpenPartialHomeomorph.trans_target] at hwtarget
      have hbx := hwtarget.2
      rw [OpenPartialHomeomorph.trans_target] at hbx
      have hjcx := hbx.2
      rw [OpenPartialHomeomorph.trans_target] at hjcx
      have hcxTarget := hjcx.1
      have hqjTarget := hjcx.2
      have hpby := hz'.2
      rw [OpenPartialHomeomorph.trans_source] at hpby
      have hpjcy := hpby.1
      rw [OpenPartialHomeomorph.trans_source] at hpjcy
      have hpj := hpjcy.1
      rw [OpenPartialHomeomorph.trans_source] at hpj
      have hjp := hpj.2
      have hp_eq :
          j ((bx.trans D).symm w) =
            cx.symm (tx.symm (D.symm w)) := by
        change j (j.symm (cx.symm (tx.symm (D.symm w)))) = _
        exact j.right_inv hqjTarget
      change j ((bx.trans D).symm w) ∈ cy.source at hjp
      rw [hp_eq] at hjp
      have htx : tx.symm (coordinateUnlinkExteriorModel w) =
          coordinateUnlinkExteriorModel w - sx := by
        rw [eq_sub_iff_add_eq]
        exact (Homeomorph.addRight sx).apply_symm_apply
          (coordinateUnlinkExteriorModel w)
      rw [OpenPartialHomeomorph.trans_source]
      constructor
      · change tx.symm (coordinateUnlinkExteriorModel w) ∈
          cx.target at hcxTarget
        rwa [htx] at hcxTarget
      · change cx.symm (tx.symm (coordinateUnlinkExteriorModel w)) ∈
          cy.source at hjp
        rwa [htx] at hjp
    have hshift : ContDiff ℝ ∞
        (fun z : EuclideanSpace ℝ (Fin 4) ↦ z - sx) :=
      contDiff_id.sub contDiff_const
    have hcomp : ContDiffOn ℝ ∞
        (fun z ↦ cy (cx.symm (z - sx)))
        ((fun z ↦ z - sx) ⁻¹' (cx.symm.trans cy).source) := by
      refine (hg.comp hshift.contDiffOn (mapsTo_preimage _ _)).congr ?_
      intro z _
      rfl
    have hfull : ContDiffOn ℝ ∞
        (fun z ↦ cy (cx.symm (z - sx)) + sy)
        ((fun z ↦ z - sx) ⁻¹' (cx.symm.trans cy).source) :=
      hcomp.add contDiff_const.contDiffOn
    refine (hfull.mono hsubset).congr ?_
    intro z hz
    rcases hz.2 with ⟨w, rfl⟩
    have hz0 := hz.1
    change coordinateUnlinkExteriorModel.symm
        (coordinateUnlinkExteriorModel w) ∈
      ((coordinateUnlinkExteriorEighthAmbientChartOnInterior x).symm.trans
        (coordinateUnlinkExteriorEighthAmbientChartOnInterior y)).source at hz0
    rw [coordinateUnlinkExteriorModel.left_inv] at hz0
    have hz' : w ∈ ((bx.trans D).symm.trans (bY.trans D)).source := by
      change w ∈
        ((coordinateUnlinkExteriorEighthAmbientChartOnInterior x).symm.trans
          (coordinateUnlinkExteriorEighthAmbientChartOnInterior y)).source
      exact hz0
    rw [OpenPartialHomeomorph.trans_source] at hz'
    have hwtarget := hz'.1
    rw [OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.trans_target] at hwtarget
    have hbx := hwtarget.2
    rw [OpenPartialHomeomorph.trans_target] at hbx
    have hjcx := hbx.2
    rw [OpenPartialHomeomorph.trans_target] at hjcx
    have hqjTarget := hjcx.2
    have hpby := hz'.2
    rw [OpenPartialHomeomorph.trans_source] at hpby
    have hDsource := hpby.2
    have hp_eq :
        j ((bx.trans D).symm w) =
          cx.symm (tx.symm (D.symm w)) := by
      change j (j.symm (cx.symm (tx.symm (D.symm w)))) = _
      exact j.right_inv hqjTarget
    have htx : tx.symm (coordinateUnlinkExteriorModel w) =
        coordinateUnlinkExteriorModel w - sx := by
      rw [eq_sub_iff_add_eq]
      exact (Homeomorph.addRight sx).apply_symm_apply
        (coordinateUnlinkExteriorModel w)
    have hvecRange :
        ty (cy (j ((bx.trans D).symm w))) ∈
          range coordinateUnlinkExteriorModel := by
      apply interior_subset
      change (bY ((bx.trans D).symm w)) ∈ D.source at hDsource
      exact hDsource
    simp only [comp_apply, OpenPartialHomeomorph.trans_apply]
    rw [coordinateUnlinkExteriorModel.left_inv]
    change coordinateUnlinkExteriorModel
        (D (ty (cy (j ((bx.trans D).symm w))))) =
      cy (cx.symm (coordinateUnlinkExteriorModel w - sx)) + sy
    change coordinateUnlinkExteriorModel
        (coordinateUnlinkExteriorModel.symm
          (ty (cy (j ((bx.trans D).symm w))))) = _
    rw [coordinateUnlinkExteriorModel.right_inv hvecRange, hp_eq]
    change ty (cy (cx.symm (tx.symm
      (coordinateUnlinkExteriorModel w)))) = _
    rw [htx]
    rfl
private theorem probe_ambient_transition
    (x y : CoordinateUnlinkExteriorEighthInterior) :
    (coordinateUnlinkExteriorEighthAmbientChart x).symm.trans
        (coordinateUnlinkExteriorEighthAmbientChart y) ∈
      contDiffGroupoid ∞ coordinateUnlinkExteriorModel := by
  rw [coordinateUnlinkExteriorEighthAmbientChart,
    coordinateUnlinkExteriorEighthAmbientChart,
    OpenPartialHomeomorph.lift_openEmbedding_trans]
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · exact probe_ambient_transition_forward x y
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
    exact probe_ambient_transition_forward y x

private theorem probe_collar_transition_same
    (i : Fin 2) (p q : CoordinateUnlinkExteriorEighthCollarDomain) :
    (coordinateUnlinkExteriorEighthCollarChart i p).symm.trans
        (coordinateUnlinkExteriorEighthCollarChart i q) ∈
      contDiffGroupoid ∞ coordinateUnlinkExteriorModel := by
  rw [coordinateUnlinkExteriorEighthCollarChart,
    coordinateUnlinkExteriorEighthCollarChart,
    OpenPartialHomeomorph.lift_openEmbedding_trans]
  exact (contDiffGroupoid ∞ coordinateUnlinkExteriorModel).compatible
    (chart_mem_atlas CoordinateUnlinkExteriorModelSpace p)
    (chart_mem_atlas CoordinateUnlinkExteriorModelSpace q)

private theorem probe_range_collarToExterior_disjoint :
    Disjoint (range (coordinateUnlinkExteriorEighthCollarToExterior 0))
      (range (coordinateUnlinkExteriorEighthCollarToExterior 1)) := by
  rw [Set.disjoint_left]
  rintro q ⟨p0, rfl⟩ ⟨p1, hp1⟩
  have h0 :
      (coordinateUnlinkExteriorEighthCollarToExterior 0 p0).1 ∈
        standardUnlinkExteriorCollarSet 0 (1 / 8 : ℝ) (1 / 4 : ℝ) := by
    exact (standardUnlinkExteriorEighthCollarHomeomorph 0 p0).2
  have h1 :
      (coordinateUnlinkExteriorEighthCollarToExterior 0 p0).1 ∈
        standardUnlinkExteriorCollarSet 1 (1 / 8 : ℝ) (1 / 4 : ℝ) := by
    rw [← hp1]
    exact (standardUnlinkExteriorEighthCollarHomeomorph 1 p1).2
  exact Set.disjoint_left.mp
    (disjoint_standardUnlinkExteriorCollarSet_zero_one
      (1 / 8 : ℝ) (by norm_num)) h0 h1

private theorem probe_collar_transition_distinct
    {i j : Fin 2} (hij : i ≠ j)
    (p q : CoordinateUnlinkExteriorEighthCollarDomain) :
    (coordinateUnlinkExteriorEighthCollarChart i p).symm.trans
        (coordinateUnlinkExteriorEighthCollarChart j q) ∈
      contDiffGroupoid ∞ coordinateUnlinkExteriorModel := by
  apply ContDiffGroupoid.mem_of_source_eq_empty
  ext z
  constructor
  · intro hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    let w := (coordinateUnlinkExteriorEighthCollarChart i p).symm z
    have hwi : w ∈ (coordinateUnlinkExteriorEighthCollarChart i p).source :=
      (coordinateUnlinkExteriorEighthCollarChart i p).symm.map_source hz.1
    have hwj : w ∈ (coordinateUnlinkExteriorEighthCollarChart j q).source := hz.2
    rw [coordinateUnlinkExteriorEighthCollarChart,
      OpenPartialHomeomorph.lift_openEmbedding_source] at hwi hwj
    have hi : w ∈ range (coordinateUnlinkExteriorEighthCollarToExterior i) :=
      ⟨hwi.choose, hwi.choose_spec.2⟩
    have hj : w ∈ range (coordinateUnlinkExteriorEighthCollarToExterior j) :=
      ⟨hwj.choose, hwj.choose_spec.2⟩
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact Set.disjoint_left.mp probe_range_collarToExterior_disjoint hi hj
    · exact Set.disjoint_left.mp probe_range_collarToExterior_disjoint.symm hi hj
    · exact (hij rfl).elim
  · intro hz
    exact hz.elim

private theorem probe_contMDiff_collarForward_common (i : Fin 2) :
    ContMDiff coordinateUnlinkExteriorModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun p : CoordinateUnlinkExteriorEighthCollarDomain ↦
        (standardUnlinkExteriorEighthCollarHomeomorph i p : Sphere 4)) := by
  rw [ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left]
  exact contMDiff_standardUnlinkExteriorEighthCollarHomeomorph_ambient i

private theorem probe_contMDiff_polarCollarCoordinates_common (i : Fin 2) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorEighthPuncturedTubePolarCollarCoordinates i) := by
  rw [ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_right]
  exact contMDiff_coordinateUnlinkExteriorEighthPuncturedTubePolarCollarCoordinates i

private def coordinateUnlinkExteriorEighthPuncturedTubeOverlapToSphere
    (i : Fin 2)
    (q : CoordinateUnlinkExteriorEighthPuncturedTubeOverlap i) : Sphere 4 :=
  q.1.1.1

private theorem isOpenEmbedding_coordinateUnlinkExteriorEighthPuncturedTubeOverlapToSphere
    (i : Fin 2) :
    IsOpenEmbedding
      (coordinateUnlinkExteriorEighthPuncturedTubeOverlapToSphere i) := by
  exact (standardUnlinkOpenTubeOpens i (1 / 4 : ℝ)).2
    |>.isOpenEmbedding_subtypeVal.comp
      ((standardUnlinkPuncturedTubeOpens i (1 / 4 : ℝ)).2
        |>.isOpenEmbedding_subtypeVal.comp
          ((coordinateUnlinkExteriorEighthPuncturedTubeOverlapOpens i).2
            |>.isOpenEmbedding_subtypeVal))

private theorem contMDiff_coordinateUnlinkExteriorEighthPuncturedTubeOverlapToSphere
    (i : Fin 2) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (coordinateUnlinkExteriorEighthPuncturedTubeOverlapToSphere i) := by
  exact contMDiff_subtype_val.comp
    (contMDiff_subtype_val.comp contMDiff_subtype_val)

private def coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph
    (i : Fin 2)
    [Nonempty (CoordinateUnlinkExteriorEighthPuncturedTubeOverlap i)] :
    PartialDiffeomorph
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (CoordinateUnlinkExteriorEighthPuncturedTubeOverlap i) (Sphere 4) ∞ := by
  let hOpen :=
    isOpenEmbedding_coordinateUnlinkExteriorEighthPuncturedTubeOverlapToSphere i
  let oph := hOpen.toOpenPartialHomeomorph
    (coordinateUnlinkExteriorEighthPuncturedTubeOverlapToSphere i)
  exact {
    toPartialEquiv := oph.toPartialEquiv
    open_source := oph.open_source
    open_target := oph.open_target
    contMDiffOn_toFun := by
      simpa [oph, hOpen] using
        (contMDiff_coordinateUnlinkExteriorEighthPuncturedTubeOverlapToSphere i).contMDiffOn
    contMDiffOn_invFun := by
      intro y hy
      apply (ContMDiffWithinAt.subtypeVal_comp_iff
        (coordinateUnlinkExteriorEighthPuncturedTubeOverlapOpens i)
        oph.symm oph.target y).mp
      apply (ContMDiffWithinAt.subtypeVal_comp_iff
        (standardUnlinkPuncturedTubeOpens i (1 / 4 : ℝ))
        (Subtype.val ∘ oph.symm) oph.target y).mp
      apply (ContMDiffWithinAt.subtypeVal_comp_iff
        (standardUnlinkOpenTubeOpens i (1 / 4 : ℝ))
        (Subtype.val ∘ Subtype.val ∘ oph.symm) oph.target y).mp
      apply contMDiffWithinAt_id.congr
      · intro z hz
        exact oph.right_inv hz
      · exact oph.right_inv hy
  }

@[simp]
private theorem coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph_source
    (i : Fin 2)
    [Nonempty (CoordinateUnlinkExteriorEighthPuncturedTubeOverlap i)] :
    (coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph i).source =
      univ := by
  simp [coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph]

@[simp]
private theorem coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph_target
    (i : Fin 2)
    [Nonempty (CoordinateUnlinkExteriorEighthPuncturedTubeOverlap i)] :
    (coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph i).target =
      range (coordinateUnlinkExteriorEighthPuncturedTubeOverlapToSphere i) := by
  simp [coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph]

@[simp]
private theorem coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph_apply
    (i : Fin 2)
    [Nonempty (CoordinateUnlinkExteriorEighthPuncturedTubeOverlap i)]
    (q : CoordinateUnlinkExteriorEighthPuncturedTubeOverlap i) :
    coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph i q =
      coordinateUnlinkExteriorEighthPuncturedTubeOverlapToSphere i q := by
  simp [coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph]

private def coordinateUnlinkExteriorEighthCollarStrictOverlapPoint
    (i : Fin 2) (p : CoordinateUnlinkExteriorEighthCollarDomain)
    (hp : coordinateUnlinkExteriorEighthCollarToExterior i p ∈
      coordinateUnlinkExteriorEighthInteriorOpens) :
    CoordinateUnlinkExteriorEighthPuncturedTubeOverlap i := by
  let q : StandardUnlinkPuncturedTube i (1 / 4 : ℝ) :=
    standardUnlinkExteriorCollarToPuncturedTube i (by norm_num) (by norm_num)
      (standardUnlinkExteriorEighthCollarHomeomorph i p)
  refine ⟨q, ?_⟩
  change (1 / 8 : ℝ) <
    (standardUnlinkPuncturedTubePolarCoordinates i (by norm_num) q).2.2
  rw [standardUnlinkPuncturedTubePolarCoordinates_radius]
  have hi :=
    (mem_coordinateUnlinkExteriorEighthInteriorOpens_iff
      (coordinateUnlinkExteriorEighthCollarToExterior i p)).mp hp i
  exact hi

@[simp]
private theorem coordinateUnlinkExteriorEighthCollarStrictOverlapPoint_toSphere
    (i : Fin 2) (p : CoordinateUnlinkExteriorEighthCollarDomain)
    (hp : coordinateUnlinkExteriorEighthCollarToExterior i p ∈
      coordinateUnlinkExteriorEighthInteriorOpens) :
    coordinateUnlinkExteriorEighthPuncturedTubeOverlapToSphere i
        (coordinateUnlinkExteriorEighthCollarStrictOverlapPoint i p hp) =
      (coordinateUnlinkExteriorEighthCollarToExterior i p).1 :=
  rfl

@[simp]
private theorem coordinateUnlinkExteriorEighthPuncturedTubePolarCollarCoordinates_strictOverlapPoint
    (i : Fin 2) (p : CoordinateUnlinkExteriorEighthCollarDomain)
    (hp : coordinateUnlinkExteriorEighthCollarToExterior i p ∈
      coordinateUnlinkExteriorEighthInteriorOpens) :
    coordinateUnlinkExteriorEighthPuncturedTubePolarCollarCoordinates i
        (coordinateUnlinkExteriorEighthCollarStrictOverlapPoint i p hp) = p := by
  have hpolar :=
    standardUnlinkPuncturedTubePolarCoordinates_exteriorCollar i
      (by norm_num) (by norm_num) p
  apply Prod.ext
  · change
      (standardUnlinkPuncturedTubePolarCoordinates i (by norm_num)
        (standardUnlinkExteriorCollarToPuncturedTube i (by norm_num) (by norm_num)
          (standardUnlinkExteriorEighthCollarHomeomorph i p))).1 = p.1
    exact congrArg Prod.fst hpolar
  · apply Prod.ext
    · change
        (standardUnlinkPuncturedTubePolarCoordinates i (by norm_num)
          (standardUnlinkExteriorCollarToPuncturedTube i (by norm_num) (by norm_num)
            (standardUnlinkExteriorEighthCollarHomeomorph i p))).2.1 = p.2.1
      exact congrArg (fun q ↦ q.2.1) hpolar
    · apply Subtype.ext
      apply Subtype.ext
      change
        (standardUnlinkPuncturedTubePolarCoordinates i (by norm_num)
          (standardUnlinkExteriorCollarToPuncturedTube i (by norm_num) (by norm_num)
            (standardUnlinkExteriorEighthCollarHomeomorph i p))).2.2 =
          unlinkExteriorCollarRadiusValue p.2.2
      exact congrArg (fun q ↦ q.2.2) hpolar

private theorem probe_mixed_forward
    (i : Fin 2) (p : CoordinateUnlinkExteriorEighthCollarDomain)
    (x : CoordinateUnlinkExteriorEighthInterior) :
    ContDiffOn ℝ ∞
      (coordinateUnlinkExteriorModel ∘
        (coordinateUnlinkExteriorEighthCollarChart i p).symm.trans
          (coordinateUnlinkExteriorEighthAmbientChart x) ∘
        coordinateUnlinkExteriorModel.symm)
      (coordinateUnlinkExteriorModel.symm ⁻¹'
          ((coordinateUnlinkExteriorEighthCollarChart i p).symm.trans
            (coordinateUnlinkExteriorEighthAmbientChart x)).source ∩
        range coordinateUnlinkExteriorModel) := by
  let cp := chartAt CoordinateUnlinkExteriorModelSpace p
  let cx := chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1
  let f := fun q : CoordinateUnlinkExteriorEighthCollarDomain ↦
    (standardUnlinkExteriorEighthCollarHomeomorph i q : Sphere 4)
  have hf : ContMDiff coordinateUnlinkExteriorModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞ f :=
    probe_contMDiff_collarForward_common i
  have hcp : ContMDiffOn coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ cp.symm cp.target := by
    exact contMDiffOn_chart_symm
  have hcx : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      cx cx.source := by
    exact contMDiffOn_chart
  have hfOn : ContMDiffOn coordinateUnlinkExteriorModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞ f univ :=
    hf.contMDiffOn
  have hfc : ContMDiffOn coordinateUnlinkExteriorModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (f ∘ cp.symm) (cp.target ∩ cp.symm ⁻¹' univ) :=
    hfOn.comp' hcp
  have hgH : ContMDiffOn coordinateUnlinkExteriorModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (cx ∘ (f ∘ cp.symm))
      ((cp.target ∩ cp.symm ⁻¹' univ) ∩
        (f ∘ cp.symm) ⁻¹' cx.source) :=
    hcx.comp' hfc
  have hgE : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      ((cx ∘ (f ∘ cp.symm)) ∘ coordinateUnlinkExteriorModel.symm)
      (range coordinateUnlinkExteriorModel ∩
        coordinateUnlinkExteriorModel.symm ⁻¹'
          ((cp.target ∩ cp.symm ⁻¹' univ) ∩
            (f ∘ cp.symm) ⁻¹' cx.source)) :=
    hgH.comp' (coordinateUnlinkExteriorModel.contMDiffOn_symm (n := ∞))
  have hg := hgE.contDiffOn
  let sx := coordinateUnlinkExteriorModelInteriorBasePoint - cx x.1.1
  let _ : Nonempty CoordinateUnlinkExteriorEighthInterior := ⟨x⟩
  let j : OpenPartialHomeomorph CoordinateUnlinkExteriorEighthInterior
      (Sphere 4) :=
    isOpenEmbedding_coordinateUnlinkExteriorEighthInteriorToSphere
      |>.toOpenPartialHomeomorph
        coordinateUnlinkExteriorEighthInteriorToSphere
  let tx := (Homeomorph.addRight sx).toOpenPartialHomeomorph
  let D := coordinateUnlinkExteriorModelInteriorOpenPartialHomeomorph
  have hga : ContDiffOn ℝ ∞
      (fun z ↦ (((cx : Sphere 4 → EuclideanSpace ℝ (Fin 4)) ∘
        (f ∘ cp.symm)) ∘ coordinateUnlinkExteriorModel.symm) z + sx)
      (range coordinateUnlinkExteriorModel ∩
        coordinateUnlinkExteriorModel.symm ⁻¹'
          ((cp.target ∩ cp.symm ⁻¹' univ) ∩
            (f ∘ cp.symm) ⁻¹' cx.source)) :=
    hg.add contDiff_const.contDiffOn
  have hsubset :
      coordinateUnlinkExteriorModel.symm ⁻¹'
          ((coordinateUnlinkExteriorEighthCollarChart i p).symm.trans
            (coordinateUnlinkExteriorEighthAmbientChart x)).source ∩
        range coordinateUnlinkExteriorModel ⊆
      range coordinateUnlinkExteriorModel ∩
        coordinateUnlinkExteriorModel.symm ⁻¹'
          ((cp.target ∩ cp.symm ⁻¹' univ) ∩
            (f ∘ cp.symm) ⁻¹' cx.source) := by
    intro z hz
    refine ⟨hz.2, ?_⟩
    have hT := hz.1
    rw [OpenPartialHomeomorph.trans_source] at hT
    have hcpTarget := hT.1
    rw [coordinateUnlinkExteriorEighthCollarChart,
      OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.lift_openEmbedding_target] at hcpTarget
    refine ⟨⟨hcpTarget, mem_univ _⟩, ?_⟩
    have hA := hT.2
    rw [coordinateUnlinkExteriorEighthAmbientChart,
      OpenPartialHomeomorph.lift_openEmbedding_source] at hA
    rcases hA with ⟨u, hu, hueq⟩
    rw [coordinateUnlinkExteriorEighthAmbientChartOnInterior,
      OpenPartialHomeomorph.trans_source] at hu
    have hu' := hu.1
    rw [OpenPartialHomeomorph.trans_source] at hu'
    have hu'' := hu'.1
    rw [OpenPartialHomeomorph.trans_source] at hu''
    have hcxSource := hu''.2
    change coordinateUnlinkExteriorEighthInteriorToSphere u ∈ cx.source at hcxSource
    change f (cp.symm (coordinateUnlinkExteriorModel.symm z)) ∈ cx.source
    have hueq' := congrArg Subtype.val hueq
    change coordinateUnlinkExteriorEighthInteriorToSphere u =
      f (cp.symm (coordinateUnlinkExteriorModel.symm z)) at hueq'
    rwa [← hueq']
  refine (hga.mono hsubset).congr ?_
  intro z hz
  have hT := hz.1
  rw [OpenPartialHomeomorph.trans_source] at hT
  have hA := hT.2
  rw [coordinateUnlinkExteriorEighthAmbientChart,
    OpenPartialHomeomorph.lift_openEmbedding_source] at hA
  rcases hA with ⟨u, hu, hueq⟩
  have huD := hu
  change u ∈ (((j.trans cx).trans tx).trans D).source at huD
  rw [OpenPartialHomeomorph.trans_source] at huD
  have hDsource := huD.2
  have hueq' := congrArg Subtype.val hueq
  change coordinateUnlinkExteriorEighthInteriorToSphere u =
    f (cp.symm (coordinateUnlinkExteriorModel.symm z)) at hueq'
  have hvecRange : tx (cx (j u)) ∈
      range coordinateUnlinkExteriorModel := by
    apply interior_subset
    change tx (cx (j u)) ∈ D.source at hDsource
    exact hDsource
  simp only [comp_apply, OpenPartialHomeomorph.trans_apply]
  have heC :
      (coordinateUnlinkExteriorEighthCollarChart i p).symm
          (coordinateUnlinkExteriorModel.symm z) = u.1 := by
    exact hueq.symm
  rw [heC]
  rw [coordinateUnlinkExteriorEighthAmbientChart,
    OpenPartialHomeomorph.lift_openEmbedding_apply]
  change coordinateUnlinkExteriorModel (D (tx (cx (j u)))) =
    cx (f (cp.symm (coordinateUnlinkExteriorModel.symm z))) + sx
  change coordinateUnlinkExteriorModel
      (coordinateUnlinkExteriorModel.symm (tx (cx (j u)))) = _
  rw [coordinateUnlinkExteriorModel.right_inv hvecRange, ← hueq']
  rfl

private theorem coordinateUnlinkExteriorEighthMixedReverseSourceData
    (i : Fin 2) (p : CoordinateUnlinkExteriorEighthCollarDomain)
    (x : CoordinateUnlinkExteriorEighthInterior)
    {z : CoordinateUnlinkExteriorModelSpace}
    (hz : z ∈
      ((coordinateUnlinkExteriorEighthAmbientChart x).symm.trans
        (coordinateUnlinkExteriorEighthCollarChart i p)).source) :
    ∃ p' : CoordinateUnlinkExteriorEighthCollarDomain,
      p' ∈ (chartAt CoordinateUnlinkExteriorModelSpace p).source ∧
      coordinateUnlinkExteriorEighthCollarToExterior i p' =
        (coordinateUnlinkExteriorEighthAmbientChart x).symm z ∧
      coordinateUnlinkExteriorEighthCollarToExterior i p' ∈
        coordinateUnlinkExteriorEighthInteriorOpens := by
  rw [OpenPartialHomeomorph.trans_source] at hz
  have hAmbientSource :
      (coordinateUnlinkExteriorEighthAmbientChart x).symm z ∈
        (coordinateUnlinkExteriorEighthAmbientChart x).source :=
    (coordinateUnlinkExteriorEighthAmbientChart x).symm.map_source hz.1
  have hCollarSource := hz.2
  rw [coordinateUnlinkExteriorEighthCollarChart,
    OpenPartialHomeomorph.lift_openEmbedding_source] at hCollarSource
  rcases hCollarSource with ⟨p', hp'source, hp'eq⟩
  rw [coordinateUnlinkExteriorEighthAmbientChart,
    OpenPartialHomeomorph.lift_openEmbedding_source] at hAmbientSource
  rcases hAmbientSource with ⟨u, hu, hueq⟩
  refine ⟨p', hp'source, hp'eq, ?_⟩
  rw [hp'eq]
  change u.1 = (coordinateUnlinkExteriorEighthAmbientChart x).symm z at hueq
  rw [← hueq]
  exact u.2

private theorem coordinateUnlinkExteriorEighthAmbientChartSymmSphere
    (x : CoordinateUnlinkExteriorEighthInterior)
    {z : EuclideanSpace ℝ (Fin 4)}
    (hzrange : z ∈ range coordinateUnlinkExteriorModel)
    (hzTarget : coordinateUnlinkExteriorModel.symm z ∈
      (coordinateUnlinkExteriorEighthAmbientChart x).target) :
    (((coordinateUnlinkExteriorEighthAmbientChart x).symm
            (coordinateUnlinkExteriorModel.symm z)).1 =
          (chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1).symm
            (z - (coordinateUnlinkExteriorModelInteriorBasePoint -
              chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1 x.1.1)) ∧
      z - (coordinateUnlinkExteriorModelInteriorBasePoint -
          chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1 x.1.1) ∈
        (chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1).target) := by
  let cx := chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1
  let sx := coordinateUnlinkExteriorModelInteriorBasePoint - cx x.1.1
  let _ : Nonempty CoordinateUnlinkExteriorEighthInterior := ⟨x⟩
  let j : OpenPartialHomeomorph CoordinateUnlinkExteriorEighthInterior
      (Sphere 4) :=
    isOpenEmbedding_coordinateUnlinkExteriorEighthInteriorToSphere
      |>.toOpenPartialHomeomorph
        coordinateUnlinkExteriorEighthInteriorToSphere
  let tx := (Homeomorph.addRight sx).toOpenPartialHomeomorph
  let D := coordinateUnlinkExteriorModelInteriorOpenPartialHomeomorph
  let b := ((j.trans cx).trans tx).trans D
  have hzTarget' := hzTarget
  rw [coordinateUnlinkExteriorEighthAmbientChart,
    OpenPartialHomeomorph.lift_openEmbedding_target] at hzTarget'
  change coordinateUnlinkExteriorModel.symm z ∈ b.target at hzTarget'
  rw [OpenPartialHomeomorph.trans_target] at hzTarget'
  have hbTarget := hzTarget'.2
  rw [OpenPartialHomeomorph.trans_target] at hbTarget
  have hjcxTarget := hbTarget.2
  rw [OpenPartialHomeomorph.trans_target] at hjcxTarget
  have hjTarget := hjcxTarget.2
  have hcxTarget := hjcxTarget.1
  have hIz : coordinateUnlinkExteriorModel
      (coordinateUnlinkExteriorModel.symm z) = z :=
    coordinateUnlinkExteriorModel.right_inv hzrange
  have htx : tx.symm
      (D.symm (coordinateUnlinkExteriorModel.symm z)) = z - sx := by
    change (Homeomorph.addRight sx).symm
      (coordinateUnlinkExteriorModel
        (coordinateUnlinkExteriorModel.symm z)) = z - sx
    rw [hIz]
    rw [eq_sub_iff_add_eq]
    exact (Homeomorph.addRight sx).apply_symm_apply z
  have hcxTarget' : z - sx ∈ cx.target := by
    change tx.symm (D.symm
      (coordinateUnlinkExteriorModel.symm z)) ∈ cx.target at hcxTarget
    rwa [htx] at hcxTarget
  have hbSphere : j (b.symm (coordinateUnlinkExteriorModel.symm z)) =
      cx.symm (tx.symm
        (D.symm (coordinateUnlinkExteriorModel.symm z))) := by
    change j (j.symm (cx.symm (tx.symm
      (D.symm (coordinateUnlinkExteriorModel.symm z))))) = _
    exact j.right_inv hjTarget
  constructor
  · change j (b.symm (coordinateUnlinkExteriorModel.symm z)) =
      cx.symm (z - sx)
    rw [hbSphere, htx]
  · exact hcxTarget'

private theorem probe_mixed_reverse
    (i : Fin 2) (p : CoordinateUnlinkExteriorEighthCollarDomain)
    (x : CoordinateUnlinkExteriorEighthInterior) :
    ContDiffOn ℝ ∞
      (coordinateUnlinkExteriorModel ∘
        (coordinateUnlinkExteriorEighthAmbientChart x).symm.trans
          (coordinateUnlinkExteriorEighthCollarChart i p) ∘
        coordinateUnlinkExteriorModel.symm)
      (coordinateUnlinkExteriorModel.symm ⁻¹'
          ((coordinateUnlinkExteriorEighthAmbientChart x).symm.trans
            (coordinateUnlinkExteriorEighthCollarChart i p)).source ∩
        range coordinateUnlinkExteriorModel) := by
  classical
  let T := (coordinateUnlinkExteriorEighthAmbientChart x).symm.trans
    (coordinateUnlinkExteriorEighthCollarChart i p)
  change ContDiffOn ℝ ∞
    (coordinateUnlinkExteriorModel ∘ T ∘
      coordinateUnlinkExteriorModel.symm)
    (coordinateUnlinkExteriorModel.symm ⁻¹' T.source ∩
      range coordinateUnlinkExteriorModel)
  by_cases hTempty : T.source = ∅
  · rw [hTempty]
    simp
  have hTnonempty : T.source.Nonempty := nonempty_iff_ne_empty.mpr hTempty
  obtain ⟨z₀, hz₀⟩ := hTnonempty
  have hz₀' : z₀ ∈
      ((coordinateUnlinkExteriorEighthAmbientChart x).symm.trans
        (coordinateUnlinkExteriorEighthCollarChart i p)).source := by
    exact hz₀
  obtain ⟨p₀, hp₀source, hp₀eq, hp₀strict⟩ :=
    coordinateUnlinkExteriorEighthMixedReverseSourceData i p x hz₀'
  let _ : Nonempty (CoordinateUnlinkExteriorEighthPuncturedTubeOverlap i) :=
    ⟨coordinateUnlinkExteriorEighthCollarStrictOverlapPoint i p₀ hp₀strict⟩
  let cp := chartAt CoordinateUnlinkExteriorModelSpace p
  let cx := chartAt (EuclideanSpace ℝ (Fin 4)) x.1.1
  let φ :=
    coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph i
  let k := coordinateUnlinkExteriorEighthPuncturedTubePolarCollarCoordinates i
  let sx := coordinateUnlinkExteriorModelInteriorBasePoint - cx x.1.1
  let shift := fun z : EuclideanSpace ℝ (Fin 4) ↦ z - sx
  have hshift : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞ shift := by
    exact contMDiff_id.sub contMDiff_const
  have hcx : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      cx.symm cx.target := by
    exact contMDiffOn_chart_symm
  have hφ : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      φ.symm φ.target := by
    exact φ.contMDiffOn_invFun
  have hk : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      coordinateUnlinkExteriorModel ∞ k := by
    exact probe_contMDiff_polarCollarCoordinates_common i
  have hcp : ContMDiffOn coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ cp cp.source := by
    exact contMDiffOn_chart
  have hI : ContMDiff coordinateUnlinkExteriorModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      coordinateUnlinkExteriorModel :=
    coordinateUnlinkExteriorModel.contMDiff
  let f₁ := (cx.symm : EuclideanSpace ℝ (Fin 4) → Sphere 4) ∘ shift
  let s₁ : Set (EuclideanSpace ℝ (Fin 4)) :=
    univ ∩ shift ⁻¹' cx.target
  have h₁ : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      f₁ s₁ := by
    exact hcx.comp' (hshift.contMDiffOn (s := univ))
  let f₂ := (φ.symm : Sphere 4 →
    CoordinateUnlinkExteriorEighthPuncturedTubeOverlap i) ∘ f₁
  let s₂ : Set (EuclideanSpace ℝ (Fin 4)) := s₁ ∩ f₁ ⁻¹' φ.target
  have h₂ : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      f₂ s₂ := by
    exact hφ.comp' h₁
  let f₃ := k ∘ f₂
  let s₃ : Set (EuclideanSpace ℝ (Fin 4)) := s₂ ∩ f₂ ⁻¹' univ
  have h₃ : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      coordinateUnlinkExteriorModel ∞ f₃ s₃ := by
    exact (hk.contMDiffOn (s := univ)).comp' h₂
  let f₄ := (cp : CoordinateUnlinkExteriorEighthCollarDomain →
    CoordinateUnlinkExteriorModelSpace) ∘ f₃
  let s₄ : Set (EuclideanSpace ℝ (Fin 4)) := s₃ ∩ f₃ ⁻¹' cp.source
  have h₄ : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      coordinateUnlinkExteriorModel ∞ f₄ s₄ := by
    exact hcp.comp' h₃
  let f₅ := coordinateUnlinkExteriorModel ∘ f₄
  let s₅ : Set (EuclideanSpace ℝ (Fin 4)) := s₄ ∩ f₄ ⁻¹' univ
  have h₅ : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      f₅ s₅ := by
    exact (hI.contMDiffOn (s := univ)).comp' h₄
  refine (h₅.contDiffOn.mono ?_).congr ?_
  · intro z hz
    have hzT : coordinateUnlinkExteriorModel.symm z ∈
        ((coordinateUnlinkExteriorEighthAmbientChart x).symm.trans
          (coordinateUnlinkExteriorEighthCollarChart i p)).source := by
      exact hz.1
    have hzTparts := hzT
    rw [OpenPartialHomeomorph.trans_source] at hzTparts
    have hAmbient := coordinateUnlinkExteriorEighthAmbientChartSymmSphere x
      hz.2 hzTparts.1
    obtain ⟨p', hp'source, hp'eq, hp'strict⟩ :=
      coordinateUnlinkExteriorEighthMixedReverseSourceData i p x hzT
    let q' :=
      coordinateUnlinkExteriorEighthCollarStrictOverlapPoint i p' hp'strict
    have hqSphere :
        coordinateUnlinkExteriorEighthPuncturedTubeOverlapToSphere i q' =
          f₁ z := by
      change
        coordinateUnlinkExteriorEighthPuncturedTubeOverlapToSphere i q' =
          cx.symm (z - sx)
      dsimp only [q']
      rw [coordinateUnlinkExteriorEighthCollarStrictOverlapPoint_toSphere]
      exact (congrArg Subtype.val hp'eq).trans hAmbient.1
    have hf₁target : f₁ z ∈ φ.target := by
      change f₁ z ∈
        (coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph i).target
      rw [coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph_target]
      exact ⟨q', hqSphere⟩
    have hqSource : q' ∈ φ.source := by
      change q' ∈
        (coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph i).source
      rw [coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph_source]
      exact mem_univ q'
    have hφApply : φ q' = f₁ z := by
      change
        coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph i q' =
          f₁ z
      rw [coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph_apply]
      exact hqSphere
    have hf₂ : f₂ z = q' := by
      change φ.symm (f₁ z) = q'
      rw [← hφApply]
      exact φ.left_inv hqSource
    have hf₃ : f₃ z = p' := by
      change k (f₂ z) = p'
      rw [hf₂]
      exact
        coordinateUnlinkExteriorEighthPuncturedTubePolarCollarCoordinates_strictOverlapPoint
          i p' hp'strict
    change z ∈ s₅
    refine ⟨?_, mem_univ _⟩
    refine ⟨?_, ?_⟩
    · refine ⟨?_, mem_univ _⟩
      refine ⟨?_, hf₁target⟩
      exact ⟨mem_univ _, hAmbient.2⟩
    · change f₃ z ∈ cp.source
      rwa [hf₃]
  · intro z hz
    have hzT : coordinateUnlinkExteriorModel.symm z ∈
        ((coordinateUnlinkExteriorEighthAmbientChart x).symm.trans
          (coordinateUnlinkExteriorEighthCollarChart i p)).source := by
      exact hz.1
    have hzTparts := hzT
    rw [OpenPartialHomeomorph.trans_source] at hzTparts
    have hAmbient := coordinateUnlinkExteriorEighthAmbientChartSymmSphere x
      hz.2 hzTparts.1
    obtain ⟨p', hp'source, hp'eq, hp'strict⟩ :=
      coordinateUnlinkExteriorEighthMixedReverseSourceData i p x hzT
    let q' :=
      coordinateUnlinkExteriorEighthCollarStrictOverlapPoint i p' hp'strict
    have hqSphere :
        coordinateUnlinkExteriorEighthPuncturedTubeOverlapToSphere i q' =
          f₁ z := by
      change
        coordinateUnlinkExteriorEighthPuncturedTubeOverlapToSphere i q' =
          cx.symm (z - sx)
      dsimp only [q']
      rw [coordinateUnlinkExteriorEighthCollarStrictOverlapPoint_toSphere]
      exact (congrArg Subtype.val hp'eq).trans hAmbient.1
    have hqSource : q' ∈ φ.source := by
      change q' ∈
        (coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph i).source
      rw [coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph_source]
      exact mem_univ q'
    have hφApply : φ q' = f₁ z := by
      change
        coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph i q' =
          f₁ z
      rw [coordinateUnlinkExteriorEighthPuncturedTubeOverlapPartialDiffeomorph_apply]
      exact hqSphere
    have hf₂ : f₂ z = q' := by
      change φ.symm (f₁ z) = q'
      rw [← hφApply]
      exact φ.left_inv hqSource
    have hf₃ : f₃ z = p' := by
      change k (f₂ z) = p'
      rw [hf₂]
      exact
        coordinateUnlinkExteriorEighthPuncturedTubePolarCollarCoordinates_strictOverlapPoint
          i p' hp'strict
    have hCollarApply :
        coordinateUnlinkExteriorEighthCollarChart i p
            ((coordinateUnlinkExteriorEighthAmbientChart x).symm
              (coordinateUnlinkExteriorModel.symm z)) =
          cp p' := by
      rw [← hp'eq, coordinateUnlinkExteriorEighthCollarChart,
        OpenPartialHomeomorph.lift_openEmbedding_apply]
    simp only [comp_apply]
    change coordinateUnlinkExteriorModel
        (coordinateUnlinkExteriorEighthCollarChart i p
          ((coordinateUnlinkExteriorEighthAmbientChart x).symm
            (coordinateUnlinkExteriorModel.symm z))) =
      coordinateUnlinkExteriorModel (cp (f₃ z))
    rw [hCollarApply, hf₃]

private theorem coordinateUnlinkExteriorEighthMixedTransition
    (i : Fin 2) (p : CoordinateUnlinkExteriorEighthCollarDomain)
    (x : CoordinateUnlinkExteriorEighthInterior) :
    (coordinateUnlinkExteriorEighthCollarChart i p).symm.trans
        (coordinateUnlinkExteriorEighthAmbientChart x) ∈
      contDiffGroupoid ∞ coordinateUnlinkExteriorModel := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · exact probe_mixed_forward i p x
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
    exact probe_mixed_reverse i p x


/-- The combined atlas makes the literal coordinate-unlink exterior a smooth four-manifold with
boundary. -/
theorem coordinateUnlinkExteriorEighth_isManifold :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  exact {
    compatible := by
      intro e e' he he'
      rcases he with ⟨x, rfl⟩ | ⟨i, p, rfl⟩
      · rcases he' with ⟨y, rfl⟩ | ⟨j, q, rfl⟩
        · exact probe_ambient_transition x y
        · have hmixed := coordinateUnlinkExteriorEighthMixedTransition j q x
          have hinverse :=
            (contDiffGroupoid ∞ coordinateUnlinkExteriorModel).symm hmixed
          simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
            OpenPartialHomeomorph.symm_symm] using hinverse
      · rcases he' with ⟨y, rfl⟩ | ⟨j, q, rfl⟩
        · exact coordinateUnlinkExteriorEighthMixedTransition i p y
        · by_cases hij : i = j
          · subst j
            exact probe_collar_transition_same i p q
          · exact probe_collar_transition_distinct hij p q
  }


private theorem coordinateUnlinkExteriorEighthAmbientChart_model_mem_interior
    (x : CoordinateUnlinkExteriorEighthInterior)
    {q : CoordinateUnlinkExteriorEighth}
    (hq : q ∈ (coordinateUnlinkExteriorEighthAmbientChart x).source) :
    coordinateUnlinkExteriorModel
        (coordinateUnlinkExteriorEighthAmbientChart x q) ∈
      interior (range coordinateUnlinkExteriorModel) := by
  have htarget :=
    (coordinateUnlinkExteriorEighthAmbientChart x).map_source hq
  rw [coordinateUnlinkExteriorEighthAmbientChart,
    OpenPartialHomeomorph.lift_openEmbedding_target,
    coordinateUnlinkExteriorEighthAmbientChartOnInterior,
    OpenPartialHomeomorph.trans_target] at htarget
  exact htarget.1

private theorem coordinateUnlinkExteriorEighthCollarToExterior_radial
    (i : Fin 2) (p : CoordinateUnlinkExteriorEighthCollarDomain) :
    ‖standardUnlinkNormalProjection
          (coordinateUnlinkExteriorEighthCollarToExterior i p).1 -
        standardUnlinkNormalCenter i‖ =
      unlinkExteriorCollarRadiusValue p.2.2 := by
  have hpolar :=
    standardUnlinkPuncturedTubePolarCoordinates_exteriorCollar i
      (by norm_num) (by norm_num) p
  have hradius := congrArg (fun q ↦ q.2.2) hpolar
  rw [standardUnlinkPuncturedTubePolarCoordinates_radius,
    standardUnlinkExteriorCollarToPuncturedTube_coe] at hradius
  exact hradius

private theorem coordinateUnlinkExteriorEighth_isBoundaryPoint_collarToExterior_iff
    (i : Fin 2) (p : CoordinateUnlinkExteriorEighthCollarDomain) :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    coordinateUnlinkExteriorModel.IsBoundaryPoint
        (coordinateUnlinkExteriorEighthCollarToExterior i p) ↔
      coordinateUnlinkExteriorModel.IsBoundaryPoint p := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let cp := chartAt CoordinateUnlinkExteriorModelSpace p
  let C := coordinateUnlinkExteriorEighthCollarChart i p
  have hCsource : coordinateUnlinkExteriorEighthCollarToExterior i p ∈ C.source :=
    mem_coordinateUnlinkExteriorEighthCollarChart_source i p
  have hCatlas : C ∈ atlas CoordinateUnlinkExteriorModelSpace
      CoordinateUnlinkExteriorEighth :=
    Or.inr ⟨i, p, rfl⟩
  rw [coordinateUnlinkExteriorModel.isBoundaryPoint_iff_of_mem_atlas
      (n := ∞) (by simp) hCatlas hCsource,
    coordinateUnlinkExteriorModel.isBoundaryPoint_iff_of_mem_atlas
      (n := ∞) (by simp) (chart_mem_atlas CoordinateUnlinkExteriorModelSpace p)
        (ChartedSpace.mem_chart_source p)]
  have hvalue :
      C.extend coordinateUnlinkExteriorModel
          (coordinateUnlinkExteriorEighthCollarToExterior i p) =
        cp.extend coordinateUnlinkExteriorModel p := by
    change coordinateUnlinkExteriorModel
        (C (coordinateUnlinkExteriorEighthCollarToExterior i p)) =
      coordinateUnlinkExteriorModel (cp p)
    dsimp only [C]
    rw [coordinateUnlinkExteriorEighthCollarChart,
      OpenPartialHomeomorph.lift_openEmbedding_apply]
  have htarget :
      (C.extend coordinateUnlinkExteriorModel).target =
        (cp.extend coordinateUnlinkExteriorModel).target := by
    rw [OpenPartialHomeomorph.extend_target',
      OpenPartialHomeomorph.extend_target']
    dsimp only [C]
    rw [
      coordinateUnlinkExteriorEighthCollarChart,
      OpenPartialHomeomorph.lift_openEmbedding_target]
  rw [hvalue, htarget]

private theorem coordinateUnlinkExteriorEighthCollarDomain_isBoundaryPoint_iff
    (p : CoordinateUnlinkExteriorEighthCollarDomain) :
    coordinateUnlinkExteriorModel.IsBoundaryPoint p ↔
      p.2.2 = unlinkExteriorCollarInnerRadius (1 / 8 : ℝ) (1 / 4 : ℝ) := by
  change p ∈ coordinateUnlinkExteriorModel.boundary
      CoordinateUnlinkExteriorEighthCollarDomain ↔ _
  rw [coordinateUnlinkExteriorModel_boundary_collarDomain]
  simp

private theorem coordinateUnlinkExteriorEighthCollar_radius_eq_inner_of_not_interior
    (i : Fin 2) (p : CoordinateUnlinkExteriorEighthCollarDomain)
    (hnot : coordinateUnlinkExteriorEighthCollarToExterior i p ∉
      coordinateUnlinkExteriorEighthInteriorOpens) :
    p.2.2 =
      unlinkExteriorCollarInnerRadius (1 / 8 : ℝ) (1 / 4 : ℝ) := by
  let q := coordinateUnlinkExteriorEighthCollarToExterior i p
  have hradial : q ∈ coordinateUnlinkExteriorEighthRadialBoundary := by
    rw [coordinateUnlinkExteriorEighthRadialBoundary_eq_compl_interior]
    exact hnot
  rcases hradial with ⟨j, hj⟩
  have hiCollar : q.1 ∈
      standardUnlinkExteriorCollarSet i (1 / 8 : ℝ) (1 / 4 : ℝ) := by
    exact (standardUnlinkExteriorEighthCollarHomeomorph i p).2
  have hjCollar : q.1 ∈
      standardUnlinkExteriorCollarSet j (1 / 8 : ℝ) (1 / 4 : ℝ) := by
    apply (mem_standardUnlinkExteriorCollarSet_iff j
      (by norm_num) (by norm_num) q.1).2
    constructor
    · rw [hj]
    · rw [hj]
      norm_num
  have hji : j = i := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact (Set.disjoint_left.mp
        (disjoint_standardUnlinkExteriorCollarSet_zero_one
          (1 / 8 : ℝ) (by norm_num)) hiCollar hjCollar).elim
    · exact (Set.disjoint_left.mp
        (disjoint_standardUnlinkExteriorCollarSet_zero_one
          (1 / 8 : ℝ) (by norm_num)).symm hiCollar hjCollar).elim
    · rfl
  subst j
  have hvalue : unlinkExteriorCollarRadiusValue p.2.2 = (1 / 8 : ℝ) := by
    rw [← coordinateUnlinkExteriorEighthCollarToExterior_radial i p]
    exact hj
  apply Subtype.ext
  apply Subtype.ext
  exact hvalue

private theorem coordinateUnlinkExteriorEighth_isInteriorPoint_of_mem_interior
    (q : CoordinateUnlinkExteriorEighth)
    (hq : q ∈ coordinateUnlinkExteriorEighthInteriorOpens) :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    coordinateUnlinkExteriorModel.IsInteriorPoint q := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let x : CoordinateUnlinkExteriorEighthInterior := ⟨q, hq⟩
  let e := coordinateUnlinkExteriorEighthAmbientChart x
  have hsource : q ∈ e.source :=
    mem_coordinateUnlinkExteriorEighthAmbientChart_source x
  have heatlas : e ∈ atlas CoordinateUnlinkExteriorModelSpace
      CoordinateUnlinkExteriorEighth :=
    Or.inl ⟨x, rfl⟩
  apply (coordinateUnlinkExteriorModel.isInteriorPoint_iff_of_mem_atlas
    (n := ∞) (by simp) heatlas hsource).2
  exact e.mem_interior_extend_target (e.map_source hsource)
    (coordinateUnlinkExteriorEighthAmbientChart_model_mem_interior x hsource)

private theorem coordinateUnlinkExteriorEighth_isBoundaryPoint_iff_not_interior
    (q : CoordinateUnlinkExteriorEighth) :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    coordinateUnlinkExteriorModel.IsBoundaryPoint q ↔
      q ∉ coordinateUnlinkExteriorEighthInteriorOpens := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  constructor
  · intro hboundary hstrict
    have hinterior :=
      coordinateUnlinkExteriorEighth_isInteriorPoint_of_mem_interior q hstrict
    exact (coordinateUnlinkExteriorModel.isInteriorPoint_iff_not_isBoundaryPoint q).1
      hinterior hboundary
  · intro hnot
    have hcollar :=
      (coordinateUnlinkExteriorEighth_interior_or_collar q).resolve_left hnot
    let i := hcollar.choose
    let p := hcollar.choose_spec.choose
    have hpq : coordinateUnlinkExteriorEighthCollarToExterior i p = q :=
      hcollar.choose_spec.choose_spec
    have hpnot : coordinateUnlinkExteriorEighthCollarToExterior i p ∉
        coordinateUnlinkExteriorEighthInteriorOpens := by
      rwa [hpq]
    have hpradius :=
      coordinateUnlinkExteriorEighthCollar_radius_eq_inner_of_not_interior
        i p hpnot
    have hpboundary : coordinateUnlinkExteriorModel.IsBoundaryPoint p :=
      (coordinateUnlinkExteriorEighthCollarDomain_isBoundaryPoint_iff p).2 hpradius
    have hqboundary : coordinateUnlinkExteriorModel.IsBoundaryPoint
        (coordinateUnlinkExteriorEighthCollarToExterior i p) :=
      (coordinateUnlinkExteriorEighth_isBoundaryPoint_collarToExterior_iff i p).2
        hpboundary
    rwa [hpq] at hqboundary


/-- In the combined atlas, the model boundary is exactly the two radius-`1/8` radial faces. -/
theorem coordinateUnlinkExteriorEighth_boundary :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    coordinateUnlinkExteriorModel.boundary CoordinateUnlinkExteriorEighth =
      coordinateUnlinkExteriorEighthRadialBoundary := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  rw [coordinateUnlinkExteriorEighthRadialBoundary_eq_compl_interior]
  ext q
  exact coordinateUnlinkExteriorEighth_isBoundaryPoint_iff_not_interior q


end SplittingSpheres
