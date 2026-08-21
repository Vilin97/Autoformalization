/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckCompactCollar
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckStrictCoreInteriorAccess

/-!
# Compact planar-neck cut sides and signed collars

The compact coordinate exterior is identified with the literal planar neck star.  Pulling back
the two global off-seam pieces gives disjoint open sides whose union is the complement of the
full labelled neck family.  The complementary closed carriers are the two point-set cut sides.

For every labelled compact collar, its zero slice is exactly the corresponding selected star
fiber, and its only intersection with the full labelled seam occurs at collar time zero.
Normalized closed-annulus curves show that both global sides accumulate at a common point of
each selected zero slice.  Connectedness of the two strict collar-time halves then forces them
to lie on opposite sides.  A noncomputable per-label reflection fixes the convention that
negative time is the global left side and positive time is the global right side.

This file is purely point-set topology.  It makes no manifold-with-boundary, atlas, capping, or
smooth cut assertion.
-/

@[expose] public section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-! ## Compact transport of the literal neck star -/

/-- The canonical point-set identification of the compact coordinate exterior with the
literal planar neck star. -/
def coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorEighthPowerPullback m ≃ₜ
      CoordinateUnlinkExteriorPlanarNeckStar m :=
  (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm.trans
    (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m)

/-- The selected labelled star seam, transported to the compact coordinate exterior. -/
def coordinateUnlinkExteriorPlanarCompactNeckStarFiberSeam
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Set (CoordinateUnlinkExteriorEighthPowerPullback m) :=
  coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m ⁻¹'
    coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a

/-- A labelled compact collar zero slice is exactly its transported selected star seam. -/
theorem range_coordinateUnlinkExteriorPlanarCompactCollarZero_eq_compactNeckStarFiberSeam
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    range (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m a) =
      coordinateUnlinkExteriorPlanarCompactNeckStarFiberSeam m a := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  rw [range_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero]
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    change
      coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m
          (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (coordinateUnlinkExteriorPlanarNeckSphereMap m a s)) ∈
        coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a
    rw [coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph, Homeomorph.trans_apply,
      (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm_apply_apply,
      coordinateUnlinkExteriorPlanarNeckStarFiberSeam_eq_range]
    refine ⟨s, ?_⟩
    simpa only [coordinateUnlinkExteriorPlanarNeckSphereFamily_apply] using
      coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar_neckSphereFamily
        m (a, s) |>.symm
  · intro hz
    change
      coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m z ∈
        coordinateUnlinkExteriorPlanarNeckStarFiberSeam m a at hz
    rw [coordinateUnlinkExteriorPlanarNeckStarFiberSeam_eq_range] at hz
    obtain ⟨s, hs⟩ := hz
    refine ⟨s, ?_⟩
    apply (coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m).injective
    have hfamily :=
      coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar_neckSphereFamily
        m (a, s)
    calc
      coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m
          (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (coordinateUnlinkExteriorPlanarNeckSphereMap m a s)) =
          coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
            (coordinateUnlinkExteriorPlanarNeckSphereMap m a s) := by
              rw [coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph, Homeomorph.trans_apply,
                (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm_apply_apply]
      _ = topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
            (coordinateUnlinkExteriorPlanarNeckStarToRight m)
            (coordinateUnlinkExteriorPlanarNeckStarToLeft m (a, s)) := by
              simpa only [coordinateUnlinkExteriorPlanarNeckSphereFamily_apply] using
                hfamily
      _ = coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m z := hs

/-! ## The full labelled seam and its two open sides -/

/-- The full labelled neck-star seam in compact coordinates. -/
def coordinateUnlinkExteriorPlanarCompactNeckStarSeam
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorEighthPowerPullback m) :=
  coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m ⁻¹'
    coordinateUnlinkExteriorPlanarNeckStarSeam m

/-- The global left off-seam piece in compact coordinates. -/
def coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorEighthPowerPullback m) :=
  coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m ⁻¹'
    coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam m

/-- The global right off-seam piece in compact coordinates. -/
def coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorEighthPowerPullback m) :=
  coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m ⁻¹'
    coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m

theorem isOpen_coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam
    (m : ℕ) [NeZero m] :
    IsOpen (coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m) :=
  (isOpen_coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam m).preimage
    (coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m).continuous

theorem isOpen_coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam
    (m : ℕ) [NeZero m] :
    IsOpen (coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m) :=
  (isOpen_coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m).preimage
    (coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m).continuous

theorem disjoint_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam
    (m : ℕ) [NeZero m] :
    Disjoint (coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m) := by
  rw [coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam,
    coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam]
  exact (disjoint_coordinateUnlinkExteriorPlanarNeckStarOffSeam m).preimage _

/-- The two global open sides cover exactly the complement of the full labelled seam. -/
theorem union_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ∪
        coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m =
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)ᶜ := by
  rw [coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam,
    coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam,
    coordinateUnlinkExteriorPlanarCompactNeckStarSeam, ← preimage_union, ← preimage_compl,
    union_coordinateUnlinkExteriorPlanarNeckStarOffSeam]

theorem coordinateUnlinkExteriorPlanarCompactNeckStarSeam_eq_range_transport_family
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarCompactNeckStarSeam m =
      range (fun x : ZMod m × Sphere 3 ↦
        coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (coordinateUnlinkExteriorPlanarNeckSphereFamily m x)) := by
  ext z
  constructor
  · intro hz
    change coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m z ∈
      coordinateUnlinkExteriorPlanarNeckStarSeam m at hz
    obtain ⟨x, hx⟩ := hz
    refine ⟨x, ?_⟩
    apply (coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m).injective
    have hfamily :=
      coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar_neckSphereFamily
        m x
    calc
      coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m
          (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (coordinateUnlinkExteriorPlanarNeckSphereFamily m x)) =
          coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
            (coordinateUnlinkExteriorPlanarNeckSphereFamily m x) := by
              rw [coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph, Homeomorph.trans_apply,
                (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm_apply_apply]
      _ = topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
            (coordinateUnlinkExteriorPlanarNeckStarToRight m)
            (coordinateUnlinkExteriorPlanarNeckStarToLeft m x) := hfamily
      _ = coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m z := hx
  · rintro ⟨x, rfl⟩
    change coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m
        (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (coordinateUnlinkExteriorPlanarNeckSphereFamily m x)) ∈
      coordinateUnlinkExteriorPlanarNeckStarSeam m
    rw [coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph, Homeomorph.trans_apply,
      (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm_apply_apply,
      coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar_neckSphereFamily]
    exact mem_range_self x

theorem range_coordinateUnlinkExteriorPlanarCompactCollarZero_subset_compactNeckStarSeam
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    range (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m a) ⊆
      coordinateUnlinkExteriorPlanarCompactNeckStarSeam m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  rw [range_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero,
    coordinateUnlinkExteriorPlanarCompactNeckStarSeam_eq_range_transport_family]
  rintro _ ⟨s, rfl⟩
  exact ⟨(a, s), rfl⟩

/-- A point of one labelled compact collar meets the full labelled seam exactly at time zero.
Pairwise disjointness of the collar images excludes all other labelled seam fibers. -/
theorem coordinateUnlinkExteriorPlanarCompactCollar_mem_compactNeckStarSeam_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarSeam m ↔
      p.2.1 = 0 := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  constructor
  · intro hp
    rw [coordinateUnlinkExteriorPlanarCompactNeckStarSeam_eq_range_transport_family] at hp
    obtain ⟨⟨b, s⟩, hbs⟩ := hp
    have hzB :
        coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∈
          range (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m b) := by
      rw [range_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero]
      exact ⟨s, by simpa only [coordinateUnlinkExteriorPlanarNeckSphereFamily_apply]
        using hbs⟩
    by_cases hba : b = a
    · subst b
      obtain ⟨x, hx⟩ := hzB
      have hpair :
          p = (x, ⟨0, by norm_num [equatorCollarIntervalOpens]⟩) := by
        apply
          (isOpenEmbedding_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap
            m a).injective
        exact hx.symm
      exact congrArg (fun q : Sphere 3 × EquatorCollarInterval ↦ q.2.1) hpair
    · obtain ⟨x, hx⟩ := hzB
      have hza :
          coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∈
            (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a :
              Set (CoordinateUnlinkExteriorEighthPowerPullback m)) :=
        ⟨p, rfl⟩
      have hzb :
          coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∈
            (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m b :
              Set (CoordinateUnlinkExteriorEighthPowerPullback m)) := by
        refine ⟨(x, ⟨0, by norm_num [equatorCollarIntervalOpens]⟩), ?_⟩
        exact hx
      exact False.elim <|
        Set.disjoint_left.mp
          (pairwise_disjoint_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage
            m hba) hzb hza
  · intro hp
    apply range_coordinateUnlinkExteriorPlanarCompactCollarZero_subset_compactNeckStarSeam m a
    refine ⟨p.1, ?_⟩
    unfold coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero
    congr 2
    apply Subtype.ext
    exact hp.symm

theorem preimage_coordinateUnlinkExteriorPlanarCompactCollar_compactNeckStarSeam
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a ⁻¹'
        coordinateUnlinkExteriorPlanarCompactNeckStarSeam m =
      {p | p.2.1 = 0} := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  ext p
  exact coordinateUnlinkExteriorPlanarCompactCollar_mem_compactNeckStarSeam_iff m a p

/-! ## A common seam point accumulated by both sides -/

def coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftClosedCurve
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1) (s : Sphere 2) :
    C(Set.Icc (0 : ℝ) 1, CoordinateUnlinkExteriorPlanarNeckStar m) where
  toFun t :=
    coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m a u t s
  continuous_toFun := by
    have hx : Continuous
        (fun t : Set.Icc (0 : ℝ) 1 ↦ ((a, (u, t)), s)) :=
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)).prodMk
        continuous_const
    have hp :=
      (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft).continuous.comp hx
    have hh :=
      (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement
        m).continuous.comp hp
    have hs :=
      (topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)).continuous.comp hh
    exact hs.congr fun t ↦
      (coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_eq_grid
        m a u t s).symm

def coordinateUnlinkExteriorPlanarNeckStarNormalizedRightClosedCurve
    (m : ℕ) [NeZero m] (u : Sphere 1) (s : Sphere 2) :
    C(Set.Icc (0 : ℝ) 1, CoordinateUnlinkExteriorPlanarNeckStar m) where
  toFun t :=
    coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint m u t s
  continuous_toFun := by
    have hx : Continuous
        (fun t : Set.Icc (0 : ℝ) 1 ↦ ((u, t), s)) :=
      (continuous_const.prodMk continuous_id).prodMk continuous_const
    have hp :=
      (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight).continuous.comp hx
    have hh :=
      (coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement
        m).continuous.comp hp
    have hs :=
      (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)).continuous.comp hh
    exact hs.congr fun t ↦
      (coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint_eq_grid
        m u t s).symm

theorem coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_mem_globalLeft
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) (ht : (t : ℝ) < 1) :
    coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m a u t s ∈
      coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam m := by
  obtain ⟨x, hx, hxeq⟩ :=
    coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_mem_leaf
      m a u t s ht
  exact ⟨x, hx.2, hxeq⟩

theorem coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint_mem_globalRight
    (m : ℕ) [NeZero m] (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) (ht : (t : ℝ) < 1) :
    coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint m u t s ∈
      coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m := by
  rw [coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint_eq_grid]
  refine ⟨_, ?_, rfl⟩
  exact
    coordinateUnlinkExteriorPlanarNeckGrid_bottomRight_complement_not_mem_range
      m u t s ht

theorem coordinateUnlinkExteriorPlanarNormalizedLeftSeam_tuple
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    (x.1,
        ((coordinateUnlinkExteriorPlanarNormalizedLeftSeam m x).2.1,
          (1 : Set.Icc (0 : ℝ) 1))) =
      coordinateUnlinkExteriorPlanarNormalizedLeftSeam m x := by
  apply Prod.ext
  · exact (coordinateUnlinkExteriorPlanarNormalizedLeftSeam_fst m x).symm
  · apply Prod.ext
    · rfl
    · exact (coordinateUnlinkExteriorPlanarNormalizedLeftSeam_time m x).symm

theorem coordinateUnlinkExteriorPlanarNormalizedRightSeam_tuple
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    ((coordinateUnlinkExteriorPlanarNormalizedRightSeam m x).1,
        (1 : Set.Icc (0 : ℝ) 1)) =
      coordinateUnlinkExteriorPlanarNormalizedRightSeam m x := by
  apply Prod.ext
  · rfl
  · exact (coordinateUnlinkExteriorPlanarNormalizedRightSeam_time m x).symm

theorem coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_one_mem_closure_globalLeft
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m a u 1 s ∈
      closure (coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam m) := by
  let F := coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftClosedCurve m a u s
  let G : ℝ → CoordinateUnlinkExteriorPlanarNeckStar m :=
    fun r ↦ F (Set.projIcc 0 1 (by norm_num) r)
  have hG : Continuous G :=
    F.continuous.comp continuous_projIcc
  have hone : (1 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨by norm_num, le_rfl⟩
  have hmap : MapsTo G (Set.Ioo (0 : ℝ) 1)
      (coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam m) := by
    intro r hr
    have hproj : Set.projIcc 0 1 (by norm_num) r =
        ⟨r, hr.1.le, hr.2.le⟩ :=
      Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1)
        (by exact ⟨hr.1.le, hr.2.le⟩)
    rw [show G r = F (Set.projIcc 0 1 (by norm_num) r) by rfl, hproj]
    exact coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_mem_globalLeft
      m a u ⟨r, hr.1.le, hr.2.le⟩ s hr.2
  have hclosure := hG.continuousWithinAt.mem_closure hone hmap
  simpa [G, F, coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftClosedCurve] using hclosure

theorem coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint_one_mem_closure_globalRight
    (m : ℕ) [NeZero m] (u : Sphere 1) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint m u 1 s ∈
      closure (coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m) := by
  let F := coordinateUnlinkExteriorPlanarNeckStarNormalizedRightClosedCurve m u s
  let G : ℝ → CoordinateUnlinkExteriorPlanarNeckStar m :=
    fun r ↦ F (Set.projIcc 0 1 (by norm_num) r)
  have hG : Continuous G :=
    F.continuous.comp continuous_projIcc
  have hone : (1 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨by norm_num, le_rfl⟩
  have hmap : MapsTo G (Set.Ioo (0 : ℝ) 1)
      (coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m) := by
    intro r hr
    have hproj : Set.projIcc 0 1 (by norm_num) r =
        ⟨r, hr.1.le, hr.2.le⟩ :=
      Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1)
        (by exact ⟨hr.1.le, hr.2.le⟩)
    rw [show G r = F (Set.projIcc 0 1 (by norm_num) r) by rfl, hproj]
    exact coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint_mem_globalRight
      m u ⟨r, hr.1.le, hr.2.le⟩ s hr.2
  have hclosure := hG.continuousWithinAt.mem_closure hone hmap
  simpa [G, F, coordinateUnlinkExteriorPlanarNeckStarNormalizedRightClosedCurve] using hclosure

theorem coordinateUnlinkExteriorPlanarNeckStarNormalizedSeamEndpoints_eq
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m x.1
        (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m x).2.1 1 s =
      coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint m
        (coordinateUnlinkExteriorPlanarNormalizedRightSeam m x).1 1 s := by
  have hpush := topologicalPushout_condition
    (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m)
    (coordinateUnlinkExteriorPlanarNormalizedRightSeam m) x
  have hflower := congrArg
    (coordinateUnlinkExteriorPlanarNormalizedNeckPushoutHomeomorph m) hpush
  rw [coordinateUnlinkExteriorPlanarNormalizedNeckPushoutHomeomorph_inl,
    coordinateUnlinkExteriorPlanarNormalizedNeckPushoutHomeomorph_inr] at hflower
  rw [coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint,
    coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint,
    coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint,
    coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint,
    coordinateUnlinkExteriorPlanarNormalizedLeftSeam_tuple m x,
    coordinateUnlinkExteriorPlanarNormalizedRightSeam_tuple m x]
  exact congrArg
    (fun z : CoordinateUnlinkExteriorPlanarFlower m ↦
      coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarFlowerOuter m) (z, s))) hflower

theorem coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftSeamEndpoint_mem_fiberSeam
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m x.1
        (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m x).2.1 1 s ∈
      coordinateUnlinkExteriorPlanarNeckStarFiberSeam m x.1 := by
  rw [coordinateUnlinkExteriorPlanarNeckStarFiberSeam_eq_range]
  let b := euclideanClosedBallOneHomeomorphUnitInterval.symm x.2
  let q := topologicalPushoutInl productFourCornerToSide productFourCornerToEnd
    (b, s)
  let s3 := productFourBoundaryPushoutHomeomorphSphere q
  refine ⟨s3, ?_⟩
  rw [coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_eq_grid]
  apply congrArg
    (topologicalPushoutInl
      (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
      (coordinateUnlinkExteriorPlanarNeckStarToRight m))
  rw [coordinateUnlinkExteriorPlanarNeckStarToLeft_apply]
  dsimp [s3, q]
  rw [coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_symm_side]
  apply congrArg
    (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m)
  rw [TopologicalPushoutGridDiagram.verticalCenterToLeft_inr]
  change
    topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
        (coordinateUnlinkExteriorPlanarNeckGridBottomToBottomLeft m
          ((x.1, euclideanClosedBallOneHomeomorphUnitInterval b), s)) = _
  rw [euclideanClosedBallOneHomeomorphUnitInterval.apply_symm_apply,
    coordinateUnlinkExteriorPlanarNeckGridBottomToBottomLeft_apply,
    ← coordinateUnlinkExteriorPlanarNormalizedLeftSeam_tuple m x]

def coordinateUnlinkExteriorPlanarCompactCommonSeamPoint
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (s : Sphere 2) : CoordinateUnlinkExteriorEighthPowerPullback m :=
  (coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m).symm
    (coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m x.1
      (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m x).2.1 1 s)

theorem coordinateUnlinkExteriorPlanarCompactCommonSeamPoint_mem_closure_left
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarCompactCommonSeamPoint m x s ∈
      closure (coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m) := by
  have hstar := coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint_one_mem_closure_globalLeft
    m x.1 (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m x).2.1 s
  have hmap : MapsTo (coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m).symm
      (coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m) := by
    intro z hz
    change coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m
      ((coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m).symm z) ∈
        coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam m
    simpa using hz
  exact
    (coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m).symm.continuous
      |>.continuousWithinAt.mem_closure hstar hmap

theorem coordinateUnlinkExteriorPlanarCompactCommonSeamPoint_mem_closure_right
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarCompactCommonSeamPoint m x s ∈
      closure (coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m) := by
  have hstarRight :=
    coordinateUnlinkExteriorPlanarNeckStarNormalizedRightPoint_one_mem_closure_globalRight
      m (coordinateUnlinkExteriorPlanarNormalizedRightSeam m x).1 s
  have hstar :
      coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftPoint m x.1
          (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m x).2.1 1 s ∈
        closure (coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m) := by
    rw [coordinateUnlinkExteriorPlanarNeckStarNormalizedSeamEndpoints_eq m x s]
    exact hstarRight
  have hmap : MapsTo (coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m).symm
      (coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m) := by
    intro z hz
    change coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m
      ((coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m).symm z) ∈
        coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m
    simpa using hz
  exact
    (coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m).symm.continuous
      |>.continuousWithinAt.mem_closure hstar hmap

theorem coordinateUnlinkExteriorPlanarCompactCommonSeamPoint_mem_compactCollarZeroRange
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (s : Sphere 2) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarCompactCommonSeamPoint m x s ∈
      range
        (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m x.1) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  rw [range_coordinateUnlinkExteriorPlanarCompactCollarZero_eq_compactNeckStarFiberSeam]
  change coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m
      (coordinateUnlinkExteriorPlanarCompactCommonSeamPoint m x s) ∈
    coordinateUnlinkExteriorPlanarNeckStarFiberSeam m x.1
  simpa [coordinateUnlinkExteriorPlanarCompactCommonSeamPoint] using
    coordinateUnlinkExteriorPlanarNeckStarNormalizedLeftSeamEndpoint_mem_fiberSeam m x s

theorem coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam_inter_compactCollarImage_nonempty
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (s : Sphere 2) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ∩
      (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m x.1 :
        Set (CoordinateUnlinkExteriorEighthPowerPullback m))).Nonempty := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let w := coordinateUnlinkExteriorPlanarCompactCommonSeamPoint m x s
  have hwClosure : w ∈ closure (coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m) :=
    coordinateUnlinkExteriorPlanarCompactCommonSeamPoint_mem_closure_left m x s
  have hwZero : w ∈
      range (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m x.1) :=
    coordinateUnlinkExteriorPlanarCompactCommonSeamPoint_mem_compactCollarZeroRange m x s
  obtain ⟨u, hu⟩ := hwZero
  have hwImage : w ∈
      (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m x.1 :
        Set (CoordinateUnlinkExteriorEighthPowerPullback m)) := by
    refine ⟨(u, ⟨0, by norm_num [equatorCollarIntervalOpens]⟩), ?_⟩
    exact hu
  obtain ⟨z, hzImage, hzLeft⟩ := (mem_closure_iff.mp hwClosure)
    (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m x.1)
    (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m x.1).2
    hwImage
  exact ⟨z, hzLeft, hzImage⟩

theorem coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam_inter_compactCollarImage_nonempty
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (s : Sphere 2) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    (coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m ∩
      (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m x.1 :
        Set (CoordinateUnlinkExteriorEighthPowerPullback m))).Nonempty := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let w := coordinateUnlinkExteriorPlanarCompactCommonSeamPoint m x s
  have hwClosure : w ∈ closure (coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m) :=
    coordinateUnlinkExteriorPlanarCompactCommonSeamPoint_mem_closure_right m x s
  have hwZero : w ∈
      range (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m x.1) :=
    coordinateUnlinkExteriorPlanarCompactCommonSeamPoint_mem_compactCollarZeroRange m x s
  obtain ⟨u, hu⟩ := hwZero
  have hwImage : w ∈
      (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m x.1 :
        Set (CoordinateUnlinkExteriorEighthPowerPullback m)) := by
    refine ⟨(u, ⟨0, by norm_num [equatorCollarIntervalOpens]⟩), ?_⟩
    exact hu
  obtain ⟨z, hzImage, hzRight⟩ := (mem_closure_iff.mp hwClosure)
    (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m x.1)
    (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m x.1).2
    hwImage
  exact ⟨z, hzRight, hzImage⟩

/-! ## Constancy and opposition of the two raw sign halves -/

def coordinateUnlinkExteriorPlanarCompactCollarNegativeHalf :
    Set (Sphere 3 × EquatorCollarInterval) :=
  {p | p.2.1 < 0}

def coordinateUnlinkExteriorPlanarCompactCollarPositiveHalf :
    Set (Sphere 3 × EquatorCollarInterval) :=
  {p | 0 < p.2.1}

theorem isPreconnected_coordinateUnlinkExteriorPlanarEquatorCollarNegativeHalf :
    IsPreconnected ({t : EquatorCollarInterval | t.1 < 0} :
      Set EquatorCollarInterval) := by
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
  convert (isPreconnected_Ioo :
    IsPreconnected (Set.Ioo (-(1 / 2 : ℝ)) 0)) using 1
  ext r
  simp only [mem_image, mem_Ioo]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.2.1, ht⟩
  · intro hr
    exact ⟨⟨r, hr.1, by linarith⟩, hr.2, rfl⟩

theorem isPreconnected_coordinateUnlinkExteriorPlanarEquatorCollarPositiveHalf :
    IsPreconnected ({t : EquatorCollarInterval | 0 < t.1} :
      Set EquatorCollarInterval) := by
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
  convert (isPreconnected_Ioo :
    IsPreconnected (Set.Ioo (0 : ℝ) (1 / 2))) using 1
  ext r
  simp only [mem_image, mem_Ioo]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨ht, t.2.2⟩
  · intro hr
    exact ⟨⟨r, by linarith, hr.2⟩, hr.1, rfl⟩

theorem isPreconnected_coordinateUnlinkExteriorPlanarCompactCollarNegativeHalf :
    IsPreconnected coordinateUnlinkExteriorPlanarCompactCollarNegativeHalf := by
  let _ : PreconnectedSpace (Sphere 3) :=
    Subtype.preconnectedSpace
      ((isConnected_sphere (E := EuclideanSpace ℝ (Fin 4))
        (by rw [← Module.finrank_eq_rank]; norm_num) 0
        (by norm_num)).isPreconnected)
  rw [show coordinateUnlinkExteriorPlanarCompactCollarNegativeHalf =
      (Set.univ : Set (Sphere 3)) ×ˢ
        {t : EquatorCollarInterval | t.1 < 0} by
    ext p
    simp [coordinateUnlinkExteriorPlanarCompactCollarNegativeHalf]]
  exact
    isPreconnected_univ.prod
      isPreconnected_coordinateUnlinkExteriorPlanarEquatorCollarNegativeHalf

theorem isPreconnected_coordinateUnlinkExteriorPlanarCompactCollarPositiveHalf :
    IsPreconnected coordinateUnlinkExteriorPlanarCompactCollarPositiveHalf := by
  let _ : PreconnectedSpace (Sphere 3) :=
    Subtype.preconnectedSpace
      ((isConnected_sphere (E := EuclideanSpace ℝ (Fin 4))
        (by rw [← Module.finrank_eq_rank]; norm_num) 0
        (by norm_num)).isPreconnected)
  rw [show coordinateUnlinkExteriorPlanarCompactCollarPositiveHalf =
      (Set.univ : Set (Sphere 3)) ×ˢ
        {t : EquatorCollarInterval | 0 < t.1} by
    ext p
    simp [coordinateUnlinkExteriorPlanarCompactCollarPositiveHalf]]
  exact
    isPreconnected_univ.prod
      isPreconnected_coordinateUnlinkExteriorPlanarEquatorCollarPositiveHalf

def coordinateUnlinkExteriorPlanarCompactCollarNegativeHalfImage
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    Set (CoordinateUnlinkExteriorEighthPowerPullback m) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  exact coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a ''
    coordinateUnlinkExteriorPlanarCompactCollarNegativeHalf

def coordinateUnlinkExteriorPlanarCompactCollarPositiveHalfImage
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    Set (CoordinateUnlinkExteriorEighthPowerPullback m) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  exact coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a ''
    coordinateUnlinkExteriorPlanarCompactCollarPositiveHalf

theorem isPreconnected_coordinateUnlinkExteriorPlanarCompactCollarNegativeHalfImage
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    IsPreconnected (coordinateUnlinkExteriorPlanarCompactCollarNegativeHalfImage m a) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  exact isPreconnected_coordinateUnlinkExteriorPlanarCompactCollarNegativeHalf.image _
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap
      m a).continuous.continuousOn

theorem isPreconnected_coordinateUnlinkExteriorPlanarCompactCollarPositiveHalfImage
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    IsPreconnected (coordinateUnlinkExteriorPlanarCompactCollarPositiveHalfImage m a) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  exact isPreconnected_coordinateUnlinkExteriorPlanarCompactCollarPositiveHalf.image _
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap
      m a).continuous.continuousOn

theorem coordinateUnlinkExteriorPlanarCompactCollarNegativeHalfImage_side_choice
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarCompactCollarNegativeHalfImage m a ⊆
        coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ∨
      coordinateUnlinkExteriorPlanarCompactCollarNegativeHalfImage m a ⊆
        coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  apply IsPreconnected.subset_or_subset
    (isOpen_coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m)
    (isOpen_coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m)
    (disjoint_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam m) _
    (isPreconnected_coordinateUnlinkExteriorPlanarCompactCollarNegativeHalfImage m a)
  rintro z ⟨p, hp, rfl⟩
  rw [union_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam]
  intro hz
  have hzero :=
    (coordinateUnlinkExteriorPlanarCompactCollar_mem_compactNeckStarSeam_iff m a p).mp hz
  exact (ne_of_lt hp) hzero

theorem coordinateUnlinkExteriorPlanarCompactCollarPositiveHalfImage_side_choice
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarCompactCollarPositiveHalfImage m a ⊆
        coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ∨
      coordinateUnlinkExteriorPlanarCompactCollarPositiveHalfImage m a ⊆
        coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  apply IsPreconnected.subset_or_subset
    (isOpen_coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m)
    (isOpen_coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m)
    (disjoint_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam m) _
    (isPreconnected_coordinateUnlinkExteriorPlanarCompactCollarPositiveHalfImage m a)
  rintro z ⟨p, hp, rfl⟩
  rw [union_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam]
  intro hz
  have hzero :=
    (coordinateUnlinkExteriorPlanarCompactCollar_mem_compactNeckStarSeam_iff m a p).mp hz
  exact (ne_of_gt hp) hzero

/-- The raw negative and positive collar halves occupy opposite global sides.  This is the
local two-sidedness statement: it follows from sign-half connectedness together with a common
zero-slice point accumulated by both sides. -/
theorem coordinateUnlinkExteriorPlanarCompactCollarHalfImages_opposite_side_choice
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    (coordinateUnlinkExteriorPlanarCompactCollarNegativeHalfImage m a ⊆
          coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ∧
        coordinateUnlinkExteriorPlanarCompactCollarPositiveHalfImage m a ⊆
          coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m) ∨
      (coordinateUnlinkExteriorPlanarCompactCollarNegativeHalfImage m a ⊆
          coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m ∧
        coordinateUnlinkExteriorPlanarCompactCollarPositiveHalfImage m a ⊆
          coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  have hnegChoice :=
    coordinateUnlinkExteriorPlanarCompactCollarNegativeHalfImage_side_choice m a
  rcases hnegChoice with hneg | hneg
  · have hposChoice :=
      coordinateUnlinkExteriorPlanarCompactCollarPositiveHalfImage_side_choice m a
    rcases hposChoice with hpos | hpos
    · exfalso
      obtain ⟨z, hzRight, hzImage⟩ :=
        coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam_inter_compactCollarImage_nonempty
          m (a, 0) coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint
      obtain ⟨p, rfl⟩ := hzImage
      have hzNotSeam :
          coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∉
            coordinateUnlinkExteriorPlanarCompactNeckStarSeam m := by
        have hzComp :
            coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∈
              (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)ᶜ := by
          rw [← union_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam]
          exact Or.inr hzRight
        exact hzComp
      have htime : p.2.1 ≠ 0 := by
        intro hp
        exact hzNotSeam
          ((coordinateUnlinkExteriorPlanarCompactCollar_mem_compactNeckStarSeam_iff m a p).mpr hp)
      have hzLeft :
          coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∈
            coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m := by
        rcases lt_or_gt_of_ne htime with hp | hp
        · exact hneg ⟨p, hp, rfl⟩
        · exact hpos ⟨p, hp, rfl⟩
      exact Set.disjoint_left.mp (disjoint_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam m)
        hzLeft hzRight
    · exact Or.inl ⟨hneg, hpos⟩
  · have hposChoice :=
      coordinateUnlinkExteriorPlanarCompactCollarPositiveHalfImage_side_choice m a
    rcases hposChoice with hpos | hpos
    · exact Or.inr ⟨hneg, hpos⟩
    · exfalso
      obtain ⟨z, hzLeft, hzImage⟩ :=
        coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam_inter_compactCollarImage_nonempty
          m (a, 0) coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint
      obtain ⟨p, rfl⟩ := hzImage
      have hzNotSeam :
          coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∉
            coordinateUnlinkExteriorPlanarCompactNeckStarSeam m := by
        have hzComp :
            coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∈
              (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)ᶜ := by
          rw [← union_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam]
          exact Or.inl hzLeft
        exact hzComp
      have htime : p.2.1 ≠ 0 := by
        intro hp
        exact hzNotSeam
          ((coordinateUnlinkExteriorPlanarCompactCollar_mem_compactNeckStarSeam_iff m a p).mpr hp)
      have hzRight :
          coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∈
            coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m := by
        rcases lt_or_gt_of_ne htime with hp | hp
        · exact hneg ⟨p, hp, rfl⟩
        · exact hpos ⟨p, hp, rfl⟩
      exact Set.disjoint_left.mp (disjoint_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam m)
        hzLeft hzRight

/-! ## Per-label orientation normalization -/

/-- Reflection of the symmetric equatorial collar interval. -/
def coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph :
    EquatorCollarInterval ≃ₜ EquatorCollarInterval where
  toFun t := ⟨-t.1, by
    rcases t.2 with ⟨htl, htr⟩
    constructor <;> linarith⟩
  invFun t := ⟨-t.1, by
    rcases t.2 with ⟨htl, htr⟩
    constructor <;> linarith⟩
  left_inv t := by
    apply Subtype.ext
    simp
  right_inv t := by
    apply Subtype.ext
    simp
  continuous_toFun :=
    (continuous_neg.comp continuous_subtype_val).subtype_mk (fun t ↦ by
      rcases t.2 with ⟨htl, htr⟩
      change -(1 / 2 : ℝ) < -t.1 ∧ -t.1 < 1 / 2
      constructor <;> linarith)
  continuous_invFun :=
    (continuous_neg.comp continuous_subtype_val).subtype_mk (fun t ↦ by
      rcases t.2 with ⟨htl, htr⟩
      change -(1 / 2 : ℝ) < -t.1 ∧ -t.1 < 1 / 2
      constructor <;> linarith)

def coordinateUnlinkExteriorPlanarCompactCollarFlipHomeomorph :
    (Sphere 3 × EquatorCollarInterval) ≃ₜ
      (Sphere 3 × EquatorCollarInterval) :=
  (Homeomorph.refl (Sphere 3)).prodCongr
    coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph

def coordinateUnlinkExteriorPlanarCompactCollarRawForward
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    Prop := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  exact coordinateUnlinkExteriorPlanarCompactCollarNegativeHalfImage m a ⊆
      coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ∧
    coordinateUnlinkExteriorPlanarCompactCollarPositiveHalfImage m a ⊆
      coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m

/-- Records whether the raw collar must be reflected to put negative time on the global left
side. -/
noncomputable def coordinateUnlinkExteriorPlanarCompactCollarOrientationReversed
    (m : ℕ) [NeZero m] (a : ZMod m) : Bool := by
  classical
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  exact if coordinateUnlinkExteriorPlanarCompactCollarRawForward m a then false else true

/-- The orientation flag is false precisely when the raw negative/positive assignment already
agrees with the chosen left/right convention. -/
theorem coordinateUnlinkExteriorPlanarCompactCollarOrientationReversed_eq_false_iff
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarCompactCollarOrientationReversed m a = false ↔
      coordinateUnlinkExteriorPlanarCompactCollarRawForward m a := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  classical
  simp [coordinateUnlinkExteriorPlanarCompactCollarOrientationReversed]

/-- The identity or time reflection selected by the raw side assignment. -/
noncomputable def coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (Sphere 3 × EquatorCollarInterval) ≃ₜ
      (Sphere 3 × EquatorCollarInterval) := by
  classical
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  exact if coordinateUnlinkExteriorPlanarCompactCollarRawForward m a then Homeomorph.refl _
    else coordinateUnlinkExteriorPlanarCompactCollarFlipHomeomorph

/-- The compact collar after the noncomputable per-label orientation normalization. -/
noncomputable def coordinateUnlinkExteriorPlanarOrientedCompactCollarMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    Sphere 3 × EquatorCollarInterval →
      CoordinateUnlinkExteriorEighthPowerPullback m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  exact coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a ∘
    coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph m a

theorem isOpenEmbedding_coordinateUnlinkExteriorPlanarOrientedCompactCollarMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    IsOpenEmbedding (coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  exact
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap
      m a).comp
        (coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph m a).isOpenEmbedding

theorem coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph_apply_of_forward
    (m : ℕ) [NeZero m] (a : ZMod m)
    (h : coordinateUnlinkExteriorPlanarCompactCollarRawForward m a)
    (p : Sphere 3 × EquatorCollarInterval) :
    coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph m a p = p := by
  classical
  simp [coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph, h]

theorem coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph_apply_of_not_forward
    (m : ℕ) [NeZero m] (a : ZMod m)
    (h : ¬ coordinateUnlinkExteriorPlanarCompactCollarRawForward m a)
    (p : Sphere 3 × EquatorCollarInterval) :
    coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph m a p =
      (p.1, coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2) := by
  classical
  simp [coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph, h,
    coordinateUnlinkExteriorPlanarCompactCollarFlipHomeomorph]
  rcases p with ⟨p, t⟩
  rfl

theorem coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_left_of_neg
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) (hp : p.2.1 < 0) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a p ∈
      coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  classical
  by_cases h : coordinateUnlinkExteriorPlanarCompactCollarRawForward m a
  · rw [coordinateUnlinkExteriorPlanarOrientedCompactCollarMap, Function.comp_apply,
      coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph_apply_of_forward m a h]
    exact h.1 ⟨p, hp, rfl⟩
  · have hchoices :=
      coordinateUnlinkExteriorPlanarCompactCollarHalfImages_opposite_side_choice m a
    have hreverse := hchoices.resolve_left h
    have hsource :=
      coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph_apply_of_not_forward
        m a h p
    rw [coordinateUnlinkExteriorPlanarOrientedCompactCollarMap, Function.comp_apply,
      hsource]
    apply hreverse.2
    refine ⟨(p.1, coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2), ?_, rfl⟩
    change 0 < -p.2.1
    linarith

theorem coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_right_of_pos
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) (hp : 0 < p.2.1) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a p ∈
      coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  classical
  by_cases h : coordinateUnlinkExteriorPlanarCompactCollarRawForward m a
  · rw [coordinateUnlinkExteriorPlanarOrientedCompactCollarMap, Function.comp_apply,
      coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph_apply_of_forward m a h]
    exact h.2 ⟨p, hp, rfl⟩
  · have hchoices :=
      coordinateUnlinkExteriorPlanarCompactCollarHalfImages_opposite_side_choice m a
    have hreverse := hchoices.resolve_left h
    have hsource :=
      coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph_apply_of_not_forward
        m a h p
    rw [coordinateUnlinkExteriorPlanarOrientedCompactCollarMap, Function.comp_apply,
      hsource]
    apply hreverse.1
    refine ⟨(p.1, coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2), ?_, rfl⟩
    change -p.2.1 < 0
    linarith

/-- In the oriented collar, time zero is exactly the full labelled neck seam. -/
theorem coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_seam_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a p ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarSeam m ↔
      p.2.1 = 0 := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  classical
  by_cases h : coordinateUnlinkExteriorPlanarCompactCollarRawForward m a
  · rw [coordinateUnlinkExteriorPlanarOrientedCompactCollarMap, Function.comp_apply,
      coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph_apply_of_forward m a h,
      coordinateUnlinkExteriorPlanarCompactCollar_mem_compactNeckStarSeam_iff]
  · rw [coordinateUnlinkExteriorPlanarOrientedCompactCollarMap, Function.comp_apply,
      coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph_apply_of_not_forward
        m a h,
      coordinateUnlinkExteriorPlanarCompactCollar_mem_compactNeckStarSeam_iff]
    change -p.2.1 = 0 ↔ p.2.1 = 0
    constructor <;> intro hp <;> linarith

/-- Exact oriented sign law for the global left open side. -/
theorem coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_left_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a p ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ↔
      p.2.1 < 0 := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  constructor
  · intro hpLeft
    rcases lt_trichotomy p.2.1 0 with hp | hp | hp
    · exact hp
    · have hpSeam : coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a p ∈
          coordinateUnlinkExteriorPlanarCompactNeckStarSeam m :=
        (coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_seam_iff m a p).mpr hp
      have hpComp : coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a p ∈
          (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)ᶜ := by
        rw [← union_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam]
        exact Or.inl hpLeft
      exact False.elim (hpComp hpSeam)
    · have hpRight :=
        coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_right_of_pos m a p hp
      exact False.elim <|
        Set.disjoint_left.mp (disjoint_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam m)
          hpLeft hpRight
  · exact coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_left_of_neg m a p

/-- Exact oriented sign law for the global right open side. -/
theorem coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_right_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a p ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m ↔
      0 < p.2.1 := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  constructor
  · intro hpRight
    rcases lt_trichotomy p.2.1 0 with hp | hp | hp
    · have hpLeft :=
        coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_left_of_neg m a p hp
      exact False.elim <|
        Set.disjoint_left.mp (disjoint_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam m)
          hpLeft hpRight
    · have hpSeam : coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a p ∈
          coordinateUnlinkExteriorPlanarCompactNeckStarSeam m :=
        (coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_seam_iff m a p).mpr hp
      have hpComp : coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a p ∈
          (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)ᶜ := by
        rw [← union_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam]
        exact Or.inr hpRight
      exact False.elim (hpComp hpSeam)
    · exact hp
  · exact coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_right_of_pos m a p

/-! ## Closed cut carriers -/

/-- The closed left cut carrier: the complement of the global right open side. -/
def coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorEighthPowerPullback m) :=
  (coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m)ᶜ

/-- The closed right cut carrier: the complement of the global left open side. -/
def coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorEighthPowerPullback m) :=
  (coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m)ᶜ

theorem isClosed_coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier
    (m : ℕ) [NeZero m] :
    IsClosed (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m) :=
  (isOpen_coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m).isClosed_compl

theorem isClosed_coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier
    (m : ℕ) [NeZero m] :
    IsClosed (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m) :=
  (isOpen_coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m).isClosed_compl

theorem coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier_eq
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m =
      coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ∪
        coordinateUnlinkExteriorPlanarCompactNeckStarSeam m := by
  ext z
  constructor
  · intro hz
    by_cases hseam : z ∈ coordinateUnlinkExteriorPlanarCompactNeckStarSeam m
    · exact Or.inr hseam
    · have hsides : z ∈ coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ∪
          coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m := by
        rw [union_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam]
        exact hseam
      rcases hsides with hzLeft | hzRight
      · exact Or.inl hzLeft
      · exact False.elim (hz hzRight)
  · rintro (hzLeft | hzSeam) hzRight
    · exact Set.disjoint_left.mp (disjoint_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam m)
        hzLeft hzRight
    · have hzComp : z ∈ (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)ᶜ := by
        rw [← union_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam]
        exact Or.inr hzRight
      exact hzComp hzSeam

theorem coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier_eq
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m =
      coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m ∪
        coordinateUnlinkExteriorPlanarCompactNeckStarSeam m := by
  ext z
  constructor
  · intro hz
    by_cases hseam : z ∈ coordinateUnlinkExteriorPlanarCompactNeckStarSeam m
    · exact Or.inr hseam
    · have hsides : z ∈ coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ∪
          coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m := by
        rw [union_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam]
        exact hseam
      rcases hsides with hzLeft | hzRight
      · exact False.elim (hz hzLeft)
      · exact Or.inl hzRight
  · rintro (hzRight | hzSeam) hzLeft
    · exact Set.disjoint_left.mp (disjoint_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam m)
        hzLeft hzRight
    · have hzComp : z ∈ (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)ᶜ := by
        rw [← union_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam]
        exact Or.inl hzLeft
      exact hzComp hzSeam

/-- The two closed cut carriers meet exactly in the full labelled seam. -/
theorem inter_coordinateUnlinkExteriorPlanarCompactNeckStarCutCarriers
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m ∩
        coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m =
      coordinateUnlinkExteriorPlanarCompactNeckStarSeam m := by
  rw [coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier_eq,
    coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier_eq]
  ext z
  constructor
  · rintro ⟨hzLeft | hzSeam, hzRight | hzSeam⟩
    · exact False.elim <|
        Set.disjoint_left.mp (disjoint_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam m)
          hzLeft hzRight
    · exact hzSeam
    · exact hzSeam
    · exact hzSeam
  · intro hz
    exact ⟨Or.inr hz, Or.inr hz⟩

/-- The two closed cut carriers cover the compact coordinate exterior. -/
theorem union_coordinateUnlinkExteriorPlanarCompactNeckStarCutCarriers
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m ∪
      coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m = Set.univ := by
  rw [coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier,
    coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier, ← compl_inter]
  have hdisjoint := disjoint_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam m
  rw [inter_comm, Set.disjoint_iff_inter_eq_empty.mp hdisjoint, compl_empty]

/-- The oriented collar belongs to the closed left carrier exactly at nonpositive time. -/
theorem coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_leftCut_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a p ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m ↔
      p.2.1 ≤ 0 := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  rw [coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier,
    Set.mem_compl_iff, coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_right_iff]
  exact not_lt

/-- The oriented collar belongs to the closed right carrier exactly at nonnegative time. -/
theorem coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_rightCut_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a p ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m ↔
      0 ≤ p.2.1 := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  rw [coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier,
    Set.mem_compl_iff, coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_left_iff]
  exact not_lt

theorem range_coordinateUnlinkExteriorPlanarOrientedCompactCollarMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    range (coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a) =
      (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a :
        Set (CoordinateUnlinkExteriorEighthPowerPullback m)) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph m a p, rfl⟩
  · rintro ⟨q, hq⟩
    refine ⟨(coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph m a).symm q, ?_⟩
    rw [coordinateUnlinkExteriorPlanarOrientedCompactCollarMap, Function.comp_apply,
      (coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph m a).apply_symm_apply]
    exact hq

theorem image_coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_nonpositive
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a '' {p | p.2.1 ≤ 0} =
      (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a :
          Set (CoordinateUnlinkExteriorEighthPowerPullback m)) ∩
        coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← range_coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a]
      exact mem_range_self p
    · exact
        (coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_leftCut_iff m a p).mpr hp
  · rintro ⟨hzImage, hzCut⟩
    rw [← range_coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a] at hzImage
    obtain ⟨p, hp⟩ := hzImage
    refine ⟨p, ?_, hp⟩
    apply (coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_leftCut_iff m a p).mp
    rwa [hp]

theorem image_coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_nonnegative
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a '' {p | 0 ≤ p.2.1} =
      (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a :
          Set (CoordinateUnlinkExteriorEighthPowerPullback m)) ∩
        coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← range_coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a]
      exact mem_range_self p
    · exact
        (coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_rightCut_iff m a p).mpr hp
  · rintro ⟨hzImage, hzCut⟩
    rw [← range_coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a] at hzImage
    obtain ⟨p, hp⟩ := hzImage
    refine ⟨p, ?_, hp⟩
    apply (coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_rightCut_iff m a p).mp
    rwa [hp]

abbrev CoordinateUnlinkExteriorPlanarCompactCollarNonpositiveHalf :=
  {p : Sphere 3 × EquatorCollarInterval // p.2.1 ≤ 0}

abbrev CoordinateUnlinkExteriorPlanarCompactCollarNonnegativeHalf :=
  {p : Sphere 3 × EquatorCollarInterval // 0 ≤ p.2.1}

noncomputable def coordinateUnlinkExteriorPlanarOrientedCompactCollarLeftHalfMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    CoordinateUnlinkExteriorPlanarCompactCollarNonpositiveHalf →
      CoordinateUnlinkExteriorEighthPowerPullback m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  exact coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a ∘ Subtype.val

noncomputable def coordinateUnlinkExteriorPlanarOrientedCompactCollarRightHalfMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    CoordinateUnlinkExteriorPlanarCompactCollarNonnegativeHalf →
      CoordinateUnlinkExteriorEighthPowerPullback m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  exact coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a ∘ Subtype.val

/-- Exact ambient range of the oriented nonpositive collar half. -/
theorem range_coordinateUnlinkExteriorPlanarOrientedCompactCollarLeftHalfMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    range (coordinateUnlinkExteriorPlanarOrientedCompactCollarLeftHalfMap m a) =
      (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a :
          Set (CoordinateUnlinkExteriorEighthPowerPullback m)) ∩
        coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  rw [← image_coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_nonpositive m a]
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩

/-- Exact ambient range of the oriented nonnegative collar half. -/
theorem range_coordinateUnlinkExteriorPlanarOrientedCompactCollarRightHalfMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    range (coordinateUnlinkExteriorPlanarOrientedCompactCollarRightHalfMap m a) =
      (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a :
          Set (CoordinateUnlinkExteriorEighthPowerPullback m)) ∩
        coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  rw [← image_coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_nonnegative m a]
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩

theorem coordinateUnlinkExteriorPlanarCompactCollar_mem_zeroRange_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∈
        range (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m a) ↔
      p.2.1 = 0 := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  constructor
  · rintro ⟨x, hx⟩
    have hinj :=
      (isOpenEmbedding_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap
        m a).injective
    have hpair :
        p = (x, ⟨0, by norm_num [equatorCollarIntervalOpens]⟩) := by
      apply hinj
      exact hx.symm
    exact congrArg (fun q : Sphere 3 × EquatorCollarInterval ↦ q.2.1) hpair
  · intro hp
    refine ⟨p.1, ?_⟩
    unfold coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero
    congr 2
    apply Subtype.ext
    exact hp.symm

theorem preimage_coordinateUnlinkExteriorPlanarCompactCollar_zeroRange
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a ⁻¹'
        range (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m a) =
      {p | p.2.1 = 0} := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  ext p
  exact coordinateUnlinkExteriorPlanarCompactCollar_mem_zeroRange_iff m a p

end SplittingSpheres

end
