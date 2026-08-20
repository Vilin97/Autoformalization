/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutHomeomorph
public import SplittingSpheres.Handlebody.AlignedSphereHandleDecomposition

/-!
# A topological decomposition of a coordinate unlink exterior

After the coordinate alignment of `AlignedSphereHandleDecomposition.lean`, the cap disk is the
normal disk of the standard unlink.  Removing the two ambient coordinate tubes therefore removes
two open disks from that cap factor, with the exact rescaled radius
`r / sphereHandleRadius`.  For radii below
`sphereHandleRadius - 1 / 2`, the entire `S¹ × B³` face misses both tubes.  This file glues that
whole face to the punctured cap and recognizes the resulting topological pushout as the literal
coordinate unlink exterior.

The sharper radius bound is essential for this particular whole-face decomposition: points of
the one-handle face can have normal norm exactly `sphereHandleRadius`, while the unlink centers
have norm `1 / 2`.  No smooth structure, smooth gluing, or topological handlebody theorem is
asserted here.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped Topology

namespace SplittingSpheres

/-- Scaling the aligned cap disk converts its distance from a cap-coordinate center by exactly
the seam radius. -/
theorem dist_sphereHandleRadius_smul_unlinkCapCoordinateCenter
    (i : Fin 2) (a : SphereHandleFirst) :
    dist (sphereHandleRadius • a) (standardUnlinkNormalCenter i) =
      sphereHandleRadius * dist a (unlinkCapCoordinateCenter i) := by
  rw [← sphereHandleRadius_smul_unlinkCapCoordinateCenter i, dist_smul₀,
    Real.norm_eq_abs, abs_of_pos sphereHandleRadius_pos]

/-- Exact conversion between an ambient tube radius and its radius in the aligned cap disk. -/
theorem unlinkAlignedCapSphereMap_mem_standardUnlinkOpenTube_iff
    (i : Fin 2) {r : ℝ} (x : CapPiece) :
    unlinkAlignedCapSphereMap x ∈ standardUnlinkOpenTube i r ↔
      dist x.1.1 (unlinkCapCoordinateCenter i) < r / sphereHandleRadius := by
  rw [standardUnlinkOpenTube, mem_preimage, mem_ball,
    standardUnlinkNormalProjection_unlinkAlignedCapSphereMap,
    dist_sphereHandleRadius_smul_unlinkCapCoordinateCenter]
  constructor
  · intro h
    exact (lt_div_iff₀ sphereHandleRadius_pos).2 (by simpa [mul_comm] using h)
  · intro h
    simpa [mul_comm] using (lt_div_iff₀ sphereHandleRadius_pos).1 h

/-- The aligned cap with the two open normal-coordinate disks removed. -/
def unlinkPuncturedCapSet (r : ℝ) : Set CapPiece :=
  unlinkAlignedCapSphereMap ⁻¹' coordinateUnlinkExterior r

/-- The closed unit normal disk with the two rescaled open coordinate disks removed. -/
def unlinkPuncturedNormalDiskSet (r : ℝ) : Set (EuclideanClosedBall 2) :=
  {a |
    r / sphereHandleRadius ≤ dist a.1 (unlinkCapCoordinateCenter 0) ∧
      r / sphereHandleRadius ≤ dist a.1 (unlinkCapCoordinateCenter 1)}

/-- The compact punctured-cap piece used in the exterior pushout. -/
abbrev UnlinkPuncturedCap (r : ℝ) : Type := ↥(unlinkPuncturedCapSet r)

/-- Membership in the punctured cap is exactly avoidance of the two rescaled open disks. -/
theorem mem_unlinkPuncturedCapSet_iff (r : ℝ) (x : CapPiece) :
    x ∈ unlinkPuncturedCapSet r ↔
      r / sphereHandleRadius ≤ dist x.1.1 (unlinkCapCoordinateCenter 0) ∧
        r / sphereHandleRadius ≤ dist x.1.1 (unlinkCapCoordinateCenter 1) := by
  rw [unlinkPuncturedCapSet, mem_preimage, coordinateUnlinkExterior, mem_compl_iff,
    standardUnlinkOpenTubes, mem_union, not_or,
    unlinkAlignedCapSphereMap_mem_standardUnlinkOpenTube_iff,
    unlinkAlignedCapSphereMap_mem_standardUnlinkOpenTube_iff, not_lt, not_lt]

/-- The punctured cap is literally the punctured normal disk crossed with the entire sphere
factor. -/
theorem unlinkPuncturedCapSet_eq_prod (r : ℝ) :
    unlinkPuncturedCapSet r =
      unlinkPuncturedNormalDiskSet r ×ˢ (univ : Set (Sphere 2)) := by
  ext x
  simp only [mem_unlinkPuncturedCapSet_iff, mem_prod, unlinkPuncturedNormalDiskSet,
    mem_ofPred_eq, mem_univ, and_true]

/-- Under the whole-face radius bound, each deleted cap-coordinate disk lies strictly inside the
ambient unit disk. -/
theorem unlinkCapCoordinateBall_subset_unitBall
    {r : ℝ} (hr : r < sphereHandleRadius - 1 / 2) (i : Fin 2) :
    ball (unlinkCapCoordinateCenter i) (r / sphereHandleRadius) ⊆
      ball (0 : SphereHandleFirst) 1 := by
  have hrad : r / sphereHandleRadius < 1 - sphereHandleRadius := by
    rw [div_lt_iff₀ sphereHandleRadius_pos]
    nlinarith [sphereHandleRadius_sq]
  intro a ha
  have ha' : dist a (unlinkCapCoordinateCenter i) < r / sphereHandleRadius :=
    mem_ball.mp ha
  have htri := dist_triangle a (unlinkCapCoordinateCenter i) 0
  have hcenter : dist (unlinkCapCoordinateCenter i) 0 = sphereHandleRadius := by
    rw [dist_zero_right, norm_unlinkCapCoordinateCenter]
  apply mem_ball.mpr
  rw [dist_zero_right]
  rw [hcenter] at htri
  rw [dist_zero_right] at htri
  linarith

/-- The two deleted cap-coordinate disks are disjoint under the same radius bound. -/
theorem disjoint_unlinkCapCoordinateBalls
    {r : ℝ} (hr : r < sphereHandleRadius - 1 / 2) :
    Disjoint
      (ball (unlinkCapCoordinateCenter 0) (r / sphereHandleRadius))
      (ball (unlinkCapCoordinateCenter 1) (r / sphereHandleRadius)) := by
  apply Metric.ball_disjoint_ball
  apply le_of_mul_le_mul_left _ sphereHandleRadius_pos
  have hdist :=
    dist_sphereHandleRadius_smul_unlinkCapCoordinateCenter
      (1 : Fin 2) (unlinkCapCoordinateCenter 0)
  rw [sphereHandleRadius_smul_unlinkCapCoordinateCenter,
    dist_standardUnlinkNormalCenter_zero_one] at hdist
  calc
    sphereHandleRadius *
        (r / sphereHandleRadius + r / sphereHandleRadius) = r + r := by
      field_simp [sphereHandleRadius_ne_zero]
    _ ≤ 1 := by linarith [sphereHandleRadius_le_one]
    _ = sphereHandleRadius *
        dist (unlinkCapCoordinateCenter 0) (unlinkCapCoordinateCenter 1) := hdist

/-- The punctured cap is a closed subset of the compact cap piece. -/
theorem isClosed_unlinkPuncturedCapSet (r : ℝ) : IsClosed (unlinkPuncturedCapSet r) := by
  exact (isOpen_standardUnlinkOpenTubes r).isClosed_compl.preimage
    unlinkAlignedCapSphereMap.continuous

instance unlinkPuncturedCapCompactSpace (r : ℝ) : CompactSpace (UnlinkPuncturedCap r) :=
  isCompact_iff_compactSpace.mp (isClosed_unlinkPuncturedCapSet r).isCompact

/-- On the unit interval, the complementary scale is at least the seam radius. -/
theorem sphereHandleRadius_le_scale_on_unit {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sphereHandleRadius ≤ sphereHandleScale t := by
  apply (sq_le_sq₀ sphereHandleRadius_pos.le (sphereHandleScale_nonneg _)).mp
  rw [sphereHandleRadius_sq, sphereHandleScale_sq ht0 ht1]
  have ht2 : t ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ ht0 zero_le_one).2 ht1
  rw [sphereHandleRadius_sq]
  nlinarith

/-- The normal coordinate on the aligned one-handle face has norm equal to its complementary
scale. -/
@[simp]
theorem norm_standardUnlinkNormalProjection_unlinkAlignedOneHandleSphereMap
    (x : OneHandlePiece) :
    ‖standardUnlinkNormalProjection (unlinkAlignedOneHandleSphereMap x)‖ =
      sphereHandleScale ‖x.2.1‖ := by
  rw [standardUnlinkNormalProjection_unlinkAlignedOneHandleSphereMap, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (sphereHandleScale_nonneg _),
    mem_sphere_zero_iff_norm.mp x.1.2, mul_one]

/-- Every normal coordinate on the aligned one-handle face stays at least
`sphereHandleRadius - 1 / 2` from either unlink center. -/
theorem sphereHandleRadius_sub_half_le_dist_oneHandle_normalCenter
    (i : Fin 2) (x : OneHandlePiece) :
    sphereHandleRadius - 1 / 2 ≤
      dist (standardUnlinkNormalProjection (unlinkAlignedOneHandleSphereMap x))
        (standardUnlinkNormalCenter i) := by
  have hnorm : ‖x.2.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2.2
  have hscale : sphereHandleRadius ≤ sphereHandleScale ‖x.2.1‖ :=
    sphereHandleRadius_le_scale_on_unit (norm_nonneg _) hnorm
  calc
    sphereHandleRadius - 1 / 2 ≤ sphereHandleScale ‖x.2.1‖ - 1 / 2 :=
      sub_le_sub_right hscale _
    _ = ‖standardUnlinkNormalProjection (unlinkAlignedOneHandleSphereMap x)‖ -
        ‖standardUnlinkNormalCenter i‖ := by
      rw [norm_standardUnlinkNormalProjection_unlinkAlignedOneHandleSphereMap,
        norm_standardUnlinkNormalCenter]
    _ ≤ ‖standardUnlinkNormalProjection (unlinkAlignedOneHandleSphereMap x) -
        standardUnlinkNormalCenter i‖ := norm_sub_norm_le _ _
    _ = dist (standardUnlinkNormalProjection (unlinkAlignedOneHandleSphereMap x))
        (standardUnlinkNormalCenter i) := by rw [dist_eq_norm]

/-- Below the sharp whole-face threshold, the aligned one-handle face misses each open unlink
tube. -/
theorem unlinkAlignedOneHandleSphereMap_not_mem_standardUnlinkOpenTube
    {r : ℝ} (hr : r < sphereHandleRadius - 1 / 2)
    (i : Fin 2) (x : OneHandlePiece) :
    unlinkAlignedOneHandleSphereMap x ∉ standardUnlinkOpenTube i r := by
  intro hx
  have hdist :
      dist (standardUnlinkNormalProjection (unlinkAlignedOneHandleSphereMap x))
          (standardUnlinkNormalCenter i) < r := by
    exact hx
  have hlower := sphereHandleRadius_sub_half_le_dist_oneHandle_normalCenter i x
  linarith

/-- Below the sharp whole-face threshold, the entire aligned `S¹ × B³` face belongs to the
coordinate unlink exterior. -/
theorem unlinkAlignedOneHandleSphereMap_mem_coordinateUnlinkExterior
    {r : ℝ} (hr : r < sphereHandleRadius - 1 / 2) (x : OneHandlePiece) :
    unlinkAlignedOneHandleSphereMap x ∈ coordinateUnlinkExterior r := by
  rw [coordinateUnlinkExterior, mem_compl_iff, standardUnlinkOpenTubes, mem_union, not_or]
  exact ⟨unlinkAlignedOneHandleSphereMap_not_mem_standardUnlinkOpenTube hr 0 x,
    unlinkAlignedOneHandleSphereMap_not_mem_standardUnlinkOpenTube hr 1 x⟩

/-- The common outer boundary, included into the punctured cap.  The radius hypothesis is exactly
what guarantees that no point of the attaching boundary was deleted. -/
def unlinkPuncturedCapBoundaryInclusion
    {r : ℝ} (hr : r < sphereHandleRadius - 1 / 2) :
    C(OneHandleCapBoundary, UnlinkPuncturedCap r) where
  toFun z := ⟨capBoundaryInclusion z, by
    change unlinkAlignedCapSphereMap (capBoundaryInclusion z) ∈ coordinateUnlinkExterior r
    rw [← unlinkAlignedSphereMap_boundary_agreement]
    exact unlinkAlignedOneHandleSphereMap_mem_coordinateUnlinkExterior hr _⟩
  continuous_toFun := capBoundaryInclusion.continuous.subtype_mk _

@[simp]
theorem unlinkPuncturedCapBoundaryInclusion_coe
    {r : ℝ} (hr : r < sphereHandleRadius - 1 / 2) (z : OneHandleCapBoundary) :
    (unlinkPuncturedCapBoundaryInclusion hr z : CapPiece) = capBoundaryInclusion z :=
  rfl

theorem unlinkPuncturedCapBoundaryInclusion_injective
    {r : ℝ} (hr : r < sphereHandleRadius - 1 / 2) :
    Injective (unlinkPuncturedCapBoundaryInclusion hr) := by
  intro x y h
  apply capBoundaryInclusion_injective
  exact congrArg Subtype.val h

/-- The literal unlink exterior, regarded as a topological subtype. -/
abbrev CoordinateUnlinkExteriorSpace (r : ℝ) : Type := ↥(coordinateUnlinkExterior r)

/-- The aligned one-handle face, with codomain restricted to the unlink exterior. -/
def unlinkAlignedOneHandleExteriorMap
    {r : ℝ} (hr : r < sphereHandleRadius - 1 / 2) :
    C(OneHandlePiece, CoordinateUnlinkExteriorSpace r) where
  toFun x := ⟨unlinkAlignedOneHandleSphereMap x,
    unlinkAlignedOneHandleSphereMap_mem_coordinateUnlinkExterior hr x⟩
  continuous_toFun := unlinkAlignedOneHandleSphereMap.continuous.subtype_mk _

/-- The aligned cap map restricted from the punctured cap to the unlink exterior. -/
def unlinkAlignedPuncturedCapExteriorMap (r : ℝ) :
    C(UnlinkPuncturedCap r, CoordinateUnlinkExteriorSpace r) where
  toFun x := ⟨unlinkAlignedCapSphereMap x.1, x.2⟩
  continuous_toFun :=
    (unlinkAlignedCapSphereMap.continuous.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem unlinkAlignedOneHandleExteriorMap_coe
    {r : ℝ} (hr : r < sphereHandleRadius - 1 / 2) (x : OneHandlePiece) :
    (unlinkAlignedOneHandleExteriorMap hr x : Sphere 4) =
      unlinkAlignedOneHandleSphereMap x :=
  rfl

@[simp]
theorem unlinkAlignedPuncturedCapExteriorMap_coe
    (r : ℝ) (x : UnlinkPuncturedCap r) :
    (unlinkAlignedPuncturedCapExteriorMap r x : Sphere 4) =
      unlinkAlignedCapSphereMap x.1 :=
  rfl

/-- The two exterior face maps agree along their retained common boundary. -/
theorem unlinkExteriorFaceMaps_boundary_agreement
    {r : ℝ} (hr : r < sphereHandleRadius - 1 / 2) (z : OneHandleCapBoundary) :
    unlinkAlignedOneHandleExteriorMap hr (oneHandleBoundaryInclusion z) =
      unlinkAlignedPuncturedCapExteriorMap r
        (unlinkPuncturedCapBoundaryInclusion hr z) := by
  apply Subtype.ext
  exact unlinkAlignedSphereMap_boundary_agreement z

theorem unlinkAlignedOneHandleExteriorMap_injective
    {r : ℝ} (hr : r < sphereHandleRadius - 1 / 2) :
    Injective (unlinkAlignedOneHandleExteriorMap hr) := by
  intro x y h
  apply unlinkAlignedOneHandleSphereMap_injective
  exact congrArg Subtype.val h

theorem unlinkAlignedPuncturedCapExteriorMap_injective (r : ℝ) :
    Injective (unlinkAlignedPuncturedCapExteriorMap r) := by
  intro x y h
  apply Subtype.ext
  apply unlinkAlignedCapSphereMap_injective
  exact congrArg Subtype.val h

/-- A cross-face equality in the exterior still comes from the retained common boundary. -/
theorem unlinkExteriorFaceMaps_cross
    {r : ℝ} (hr : r < sphereHandleRadius - 1 / 2)
    (x : OneHandlePiece) (y : UnlinkPuncturedCap r)
    (hxy : unlinkAlignedOneHandleExteriorMap hr x =
      unlinkAlignedPuncturedCapExteriorMap r y) :
    ∃ z : OneHandleCapBoundary,
      oneHandleBoundaryInclusion z = x ∧
        unlinkPuncturedCapBoundaryInclusion hr z = y := by
  have hambient : unlinkAlignedOneHandleSphereMap x = unlinkAlignedCapSphereMap y.1 :=
    congrArg Subtype.val hxy
  obtain ⟨z, hzx, hzy⟩ :=
    (unlinkAlignedOneHandleSphereMap_eq_capSphereMap_iff x y.1).mp hambient
  exact ⟨z, hzx, Subtype.ext hzy⟩

/-- The restricted face images cover the literal coordinate unlink exterior. -/
theorem range_unlinkExteriorFaceMaps
    {r : ℝ} (hr : r < sphereHandleRadius - 1 / 2) :
    range (unlinkAlignedOneHandleExteriorMap hr) ∪
        range (unlinkAlignedPuncturedCapExteriorMap r) = univ := by
  ext q
  constructor
  · exact fun _ ↦ mem_univ q
  · intro _
    rcases exists_unlinkAlignedOneHandleSphereMap_or_capSphereMap q.1 with
      ⟨x, hx⟩ | ⟨y, hy⟩
    · exact Or.inl ⟨x, Subtype.ext hx⟩
    · have hyPunctured : y ∈ unlinkPuncturedCapSet r := by
        change unlinkAlignedCapSphereMap y ∈ coordinateUnlinkExterior r
        rw [hy]
        exact q.2
      exact Or.inr ⟨⟨y, hyPunctured⟩, Subtype.ext hy⟩

/-- The adjunction of the whole one-handle face to the punctured cap along their common outer
boundary. -/
abbrev CoordinateUnlinkExteriorPushout
    {r : ℝ} (hr : r < sphereHandleRadius - 1 / 2) : TopCat :=
  TopologicalPushout oneHandleBoundaryInclusion
    (unlinkPuncturedCapBoundaryInclusion hr)

/-- The punctured-cap pushout is homeomorphic to the literal coordinate unlink exterior.

This theorem is purely topological.  Its `_hrpos` argument records the intended positive tube
radius; the recognition construction itself only needs the sharper upper bound `hr`. -/
def coordinateUnlinkExteriorPushoutHomeomorph
    {r : ℝ} (_hrpos : 0 < r) (hr : r < sphereHandleRadius - 1 / 2) :
    CoordinateUnlinkExteriorPushout hr ≃ₜ CoordinateUnlinkExteriorSpace r :=
  topologicalPushoutHomeomorph oneHandleBoundaryInclusion
    (unlinkPuncturedCapBoundaryInclusion hr)
    (unlinkAlignedOneHandleExteriorMap hr)
    (unlinkAlignedPuncturedCapExteriorMap r)
    (unlinkExteriorFaceMaps_boundary_agreement hr)
    oneHandleBoundaryInclusion_injective
    (unlinkAlignedOneHandleExteriorMap_injective hr)
    (unlinkAlignedPuncturedCapExteriorMap_injective r)
    (unlinkExteriorFaceMaps_cross hr)
    (range_unlinkExteriorFaceMaps hr)

@[simp]
theorem coordinateUnlinkExteriorPushoutHomeomorph_inl
    {r : ℝ} (hrpos : 0 < r) (hr : r < sphereHandleRadius - 1 / 2)
    (x : OneHandlePiece) :
    coordinateUnlinkExteriorPushoutHomeomorph hrpos hr
        (topologicalPushoutInl oneHandleBoundaryInclusion
          (unlinkPuncturedCapBoundaryInclusion hr) x) =
      unlinkAlignedOneHandleExteriorMap hr x :=
  topologicalPushoutHomeomorph_inl _ _ _ _ _ _ _ _ _ _ x

@[simp]
theorem coordinateUnlinkExteriorPushoutHomeomorph_inr
    {r : ℝ} (hrpos : 0 < r) (hr : r < sphereHandleRadius - 1 / 2)
    (x : UnlinkPuncturedCap r) :
    coordinateUnlinkExteriorPushoutHomeomorph hrpos hr
        (topologicalPushoutInr oneHandleBoundaryInclusion
          (unlinkPuncturedCapBoundaryInclusion hr) x) =
      unlinkAlignedPuncturedCapExteriorMap r x :=
  topologicalPushoutHomeomorph_inr _ _ _ _ _ _ _ _ _ _ x

/-- The concrete radius `1 / 8` satisfies the sharp whole-face threshold. -/
theorem oneEighth_lt_sphereHandleRadius_sub_half :
    (1 / 8 : ℝ) < sphereHandleRadius - 1 / 2 := by
  have hfive : (5 / 8 : ℝ) < sphereHandleRadius := by
    rw [← sq_lt_sq₀ (by norm_num) sphereHandleRadius_pos.le, sphereHandleRadius_sq]
    norm_num
  linarith

/-- A parameter-free concrete specialization of the exterior decomposition at tube radius
`1 / 8`. -/
def coordinateUnlinkExteriorOneEighthHomeomorph :
    CoordinateUnlinkExteriorPushout oneEighth_lt_sphereHandleRadius_sub_half ≃ₜ
      CoordinateUnlinkExteriorSpace (1 / 8) :=
  coordinateUnlinkExteriorPushoutHomeomorph (by norm_num)
    oneEighth_lt_sphereHandleRadius_sub_half

end SplittingSpheres
