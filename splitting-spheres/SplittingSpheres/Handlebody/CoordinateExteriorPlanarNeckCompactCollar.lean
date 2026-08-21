/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkPowerSmoothCoordinateExteriorDiffeomorph
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckGlobalCollar

/-!
# Smooth planar-neck collars in the compact coordinate exterior

The global equatorial collars are transported through the strict coordinate-exterior
diffeomorphism and then included in the full compact coordinate-exterior power pullback.  This
gives pairwise disjoint open smooth collar charts indexed by the old transported-neck labels.

The zero section is identified exactly with the compact-coordinate image of the old point-set
transported neck sphere.  This does not assert that the old source parametrization is smooth, and
does not construct a smooth cut, cap, or pushout.
-/

@[expose] public section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-- The transported smooth collar map in the full compact coordinate-exterior power pullback. -/
def coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap
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
  exact fun p ↦
    (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m
      (equatorUnlinkPowerCollarLift m
        (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) p)).1

theorem contMDiff_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      isManifold_coordinateUnlinkExteriorEighthPowerPullback m
    ContMDiff
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ))
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  exact contMDiff_subtype_val.comp
    ((standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m).contMDiff.comp
      (contMDiff_equatorUnlinkPowerCollarLift m
        (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m)))

theorem isOpenEmbedding_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    IsOpenEmbedding
      (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  exact (coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m).2
    |>.isOpenEmbedding_subtypeVal.comp
      (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph
        m).toHomeomorph.isOpenEmbedding
    |>.comp
      (isOpenEmbedding_equatorUnlinkPowerCollarLift m
        (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m))

/-- The open compact-coordinate image of the transported collar. -/
def coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Opens (CoordinateUnlinkExteriorEighthPowerPullback m) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  exact
    ⟨range (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a),
      (isOpenEmbedding_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap
        m a).isOpen_range⟩

abbrev CoordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage
    (m : ℕ) [NeZero m] (a : ZMod m) :=
  coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a

theorem isLocalDiffeomorph_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      isManifold_coordinateUnlinkExteriorEighthPowerPullback m
    IsLocalDiffeomorph
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ))
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let f₀ : Sphere 3 × EquatorCollarInterval → StandardUnlinkPowerPullback m :=
    fun p ↦ (coordinateUnlinkExteriorPlanarTransportedNeckCollarDiffeomorph
      m a p : CoordinateUnlinkExteriorPlanarTransportedNeckCollarImage m a)
  let f₁ : StandardUnlinkPowerPullback m →
      CoordinateUnlinkExteriorEighthPowerPullbackStrict m :=
    standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m
  let f₂ : CoordinateUnlinkExteriorEighthPowerPullbackStrict m →
      CoordinateUnlinkExteriorEighthPowerPullback m := Subtype.val
  have h₀ : IsLocalDiffeomorph
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ)) (𝓡 4) ∞ f₀ := by
    intro p
    have hd :=
      (coordinateUnlinkExteriorPlanarTransportedNeckCollarDiffeomorph
        m a).isLocalDiffeomorph p
    have hi := isLocalDiffeomorph_opensSubtypeVal (𝓡 4)
      (coordinateUnlinkExteriorPlanarTransportedNeckCollarImage m a)
      (coordinateUnlinkExteriorPlanarTransportedNeckCollarDiffeomorph m a p)
    simpa [f₀, Function.comp_def] using
      hd.comp (𝓡 4) (StandardUnlinkPowerPullback m) hi
  have h₁ : IsLocalDiffeomorph (𝓡 4)
      coordinateUnlinkExteriorModel ∞ f₁ :=
    (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph
      m).isLocalDiffeomorph
  have h₂ : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ f₂ :=
    isLocalDiffeomorph_opensSubtypeVal coordinateUnlinkExteriorModel
      (coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m)
  intro p
  have hcomp := (h₀ p).comp coordinateUnlinkExteriorModel
    (CoordinateUnlinkExteriorEighthPowerPullbackStrict m) (h₁ (f₀ p))
  have hcomp' := hcomp.comp coordinateUnlinkExteriorModel
    (CoordinateUnlinkExteriorEighthPowerPullback m) (h₂ (f₁ (f₀ p)))
  simpa [f₀, f₁, f₂,
    coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap,
    Function.comp_def,
    coordinateUnlinkExteriorPlanarTransportedNeckCollarDiffeomorph_apply_coe]
    using hcomp'

/-- The transported compact-coordinate collar as a diffeomorphism onto its open image. -/
def coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarDiffeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      isManifold_coordinateUnlinkExteriorEighthPowerPullback m
    (Sphere 3 × EquatorCollarInterval) ≃ₘ^∞⟮
        ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ)),
          coordinateUnlinkExteriorModel⟯
      CoordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let h :=
    isOpenEmbedding_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap
      m a
  let e : (Sphere 3 × EquatorCollarInterval) ≃ₜ
      CoordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a :=
    h.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr rfl)
  refine
    { toEquiv := e.toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · rw [← ContMDiff.subtypeVal_comp_iff
      (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a)]
    exact
      contMDiff_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a
  · apply contMDiff_of_comp_isLocalDiffeomorph
      coordinateUnlinkExteriorModel
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ))
      coordinateUnlinkExteriorModel
      (isLocalDiffeomorph_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap
        m a)
      e.symm.continuous
    apply contMDiff_subtype_val.congr
    intro z
    exact congrArg Subtype.val (e.apply_symm_apply z)

set_option maxHeartbeats 800000 in
-- Elaborating the family-level disjointness statement exceeds the default heartbeat limit.
/-- The compact-coordinate collar images for distinct old neck labels are disjoint. -/
theorem pairwise_disjoint_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    Pairwise fun a b : ZMod m ↦
      Disjoint
        (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m a :
          Set (CoordinateUnlinkExteriorEighthPowerPullback m))
        (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarImage m b :
          Set (CoordinateUnlinkExteriorEighthPowerPullback m)) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  intro a b hab
  rw [Set.disjoint_left]
  intro z hza hzb
  obtain ⟨p, hp⟩ := hza
  obtain ⟨q, hq⟩ := hzb
  have hpq :
      equatorUnlinkPowerCollarLift m
          (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) p =
        equatorUnlinkPowerCollarLift m
          (b - coordinateUnlinkExteriorPlanarSmoothNeckShift m) q := by
    apply
      (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m).injective
    apply Subtype.ext
    exact hp.trans hq.symm
  have hpq' :
      (fun w : ZMod m × (Sphere 3 × EquatorCollarInterval) ↦
        equatorUnlinkPowerCollarLift m w.1 w.2)
          (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m, p) =
        (fun w : ZMod m × (Sphere 3 × EquatorCollarInterval) ↦
          equatorUnlinkPowerCollarLift m w.1 w.2)
            (b - coordinateUnlinkExteriorPlanarSmoothNeckShift m, q) := hpq
  have hpqpair := injective_equatorUnlinkPowerCollarLift_family m hpq'
  have habshift := congrArg Prod.fst hpqpair
  exact hab (sub_left_injective habshift)

/-- The zero section of the compact-coordinate collar. -/
def coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    CoordinateUnlinkExteriorEighthPowerPullback m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  exact coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a
    (x, ⟨0, by norm_num [equatorCollarIntervalOpens]⟩)

@[simp]
theorem coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero_eq
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m a x =
      (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m
        (equatorUnlinkPowerLift m
          (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) x)).1 := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  unfold coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero
    coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap
  rw [equatorUnlinkPowerCollarLift_zero]

private theorem
    coordinateUnlinkExteriorEighthPowerPullbackToComplement_coordinateStrictDiffeomorph_equator
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorEighthPowerPullbackToComplement m
        (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m
          (equatorUnlinkPowerLift m a x)).1 =
      equatorUnlinkPowerLift m a x := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  rw [standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_equatorUnlinkPowerLift]
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    exact equatorUnlinkClosedTubeExteriorPowerLift_powerCoordinate m a x

/-- The compact collar zero section has exactly the old transported-neck sphere range. -/
theorem range_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    range (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m a) =
      range (fun s : Sphere 3 ↦
        coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (coordinateUnlinkExteriorPlanarNeckSphereMap m a s)) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    have hx :
        equatorUnlinkPowerLift m
            (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) x ∈
          range (coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m a) := by
      rw [range_transportedNeckSphereMap_eq_equatorPowerLift_sub_shift]
      exact mem_range_self x
    obtain ⟨s, hs⟩ := hx
    refine ⟨s, ?_⟩
    apply coordinateUnlinkExteriorEighthPowerPullbackToComplement_injective m
    calc
      coordinateUnlinkExteriorEighthPowerPullbackToComplement m
          (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (coordinateUnlinkExteriorPlanarNeckSphereMap m a s)) =
        coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m a s := rfl
      _ = equatorUnlinkPowerLift m
          (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) x := hs
      _ = coordinateUnlinkExteriorEighthPowerPullbackToComplement m
          (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m
            (equatorUnlinkPowerLift m
              (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) x)).1 :=
        (coordinateUnlinkExteriorEighthPowerPullbackToComplement_coordinateStrictDiffeomorph_equator
          m _ x).symm
      _ = coordinateUnlinkExteriorEighthPowerPullbackToComplement m
          (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m a x) :=
        congrArg _
          (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero_eq
            m a x).symm
  · rintro ⟨s, rfl⟩
    have hs : coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m a s ∈
        range (equatorUnlinkPowerLift m
          (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m)) := by
      rw [← range_transportedNeckSphereMap_eq_equatorPowerLift_sub_shift]
      exact mem_range_self s
    obtain ⟨x, hx⟩ := hs
    refine ⟨x, ?_⟩
    apply coordinateUnlinkExteriorEighthPowerPullbackToComplement_injective m
    calc
      coordinateUnlinkExteriorEighthPowerPullbackToComplement m
          (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m a x) =
        coordinateUnlinkExteriorEighthPowerPullbackToComplement m
          (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m
            (equatorUnlinkPowerLift m
              (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) x)).1 :=
        congrArg _
          (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero_eq m a x)
      _ = equatorUnlinkPowerLift m
          (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) x :=
        coordinateUnlinkExteriorEighthPowerPullbackToComplement_coordinateStrictDiffeomorph_equator
          m _ x
      _ = coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m a s := hx
      _ = coordinateUnlinkExteriorEighthPowerPullbackToComplement m
          (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (coordinateUnlinkExteriorPlanarNeckSphereMap m a s)) := rfl

end SplittingSpheres

end
