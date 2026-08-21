/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckCompactCollarOrientation

/-!
# Compact planar-neck sides as coordinate caps

The old radial exterior homeomorphism preserves the sign of the fourth sphere coordinate: on
each radius-`3/8` tube its image remains in the same tube, while away from both tubes it is the
identity.  This identifies its forward and inverse images of the two coordinate open caps.

On the strict part of the compact coordinate-exterior power pullback, the full-cover coordinate-cap
theorems therefore identify the transported neck-star sides with the negative and positive caps.
The full compact seam is exactly the inverse image of the coordinate equator.  The strict part is
dense: this follows directly from the closure of the interior of every extended-chart target,
together with the explicit radial-boundary description of the pulled-back atlas.  Any incorrect
intersection between a compact side and the opposite cap would consequently contain a strict
point, contradicting the strict identification.

Thus the global compact left and right sides are precisely the two cap preimages, and their closed
cut carriers are the preimages of the complements of the opposite caps.  No smoothness assertion
is made about the old radial exterior homeomorphism or the normalized planar annuli.
-/

@[expose] public section

open Function Metric Set Topology TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

private theorem dense_modelWithCorners_interior
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    {n : WithTop ℕ∞} [IsManifold I n M] (hn : n ≠ 0) :
    Dense (I.interior M) := by
  intro x
  let e := extChartAt I x
  have htarget : e x ∈ e.target := mem_extChartAt_target (I := I) x
  have hclosure : e x ∈ closure (interior e.target) :=
    extChartAt_target_subset_closure_interior htarget
  have himage : e.symm (e x) ∈ closure (e.symm '' interior e.target) :=
    mem_closure_image (continuousAt_extChartAt_symm'' htarget) hclosure
  rw [e.left_inv (mem_extChartAt_source (I := I) x)] at himage
  apply closure_mono ?_ himage
  rintro _ ⟨z, hz, rfl⟩
  have hz_target : z ∈ e.target := interior_subset hz
  have hsource : e.symm z ∈ e.source := e.map_target hz_target
  exact (I.isInteriorPoint_iff_of_mem_atlas hn (chart_mem_atlas H x)
    (by simpa [e, extChartAt_source] using hsource)).2 (by
      change e (e.symm z) ∈ interior e.target
      simpa only [e.right_inv hz_target] using hz)

private theorem standardUnlinkOpenTube_zero_subset_coordinateOpenCap_zero :
    standardUnlinkOpenTube 0 (3 / 8 : ℝ) ⊆ coordinateOpenCap 0 := by
  intro x hx
  rw [mem_coordinateOpenCap_zero]
  change dist (standardUnlinkNormalProjection x)
      (standardUnlinkNormalCenter 0) < 3 / 8 at hx
  rw [dist_eq_norm] at hx
  let v := standardUnlinkNormalProjection x - standardUnlinkNormalCenter 0
  have hsq : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    simpa [Fin.sum_univ_succ] using EuclideanSpace.real_norm_sq_eq v
  have hv0 : v 0 = x.1 3 + 1 / 2 := by
    simp [v, standardUnlinkHeight]
  have hv1sq : 0 ≤ v 1 ^ 2 := sq_nonneg _
  have hvnorm : ‖v‖ < 3 / 8 := hx
  have hvnorm_nonneg : 0 ≤ ‖v‖ := norm_nonneg _
  rw [hv0] at hsq
  nlinarith

private theorem standardUnlinkOpenTube_one_subset_coordinateOpenCap_one :
    standardUnlinkOpenTube 1 (3 / 8 : ℝ) ⊆ coordinateOpenCap 1 := by
  intro x hx
  rw [mem_coordinateOpenCap_one]
  change dist (standardUnlinkNormalProjection x)
      (standardUnlinkNormalCenter 1) < 3 / 8 at hx
  rw [dist_eq_norm] at hx
  let v := standardUnlinkNormalProjection x - standardUnlinkNormalCenter 1
  have hsq : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    simpa [Fin.sum_univ_succ] using EuclideanSpace.real_norm_sq_eq v
  have hv0 : v 0 = x.1 3 - 1 / 2 := by
    simp [v, standardUnlinkHeight]
  have hv1sq : 0 ≤ v 1 ^ 2 := sq_nonneg _
  have hvnorm : ‖v‖ < 3 / 8 := hx
  have hvnorm_nonneg : 0 ≤ ‖v‖ := norm_nonneg _
  rw [hv0] at hsq
  nlinarith

private theorem standardUnlinkComplementTubeForward_mem_openTube
    (i : Fin 2) (q : StandardUnlinkComplementTube i) :
    standardUnlinkComplementTubeForward i q ∈
      standardUnlinkOpenTube i (3 / 8 : ℝ) := by
  exact (standardUnlinkPuncturedToExteriorEighthTubeHomeomorph i
    (standardUnlinkComplementTubeToPuncturedTube i q)).1.2

/-- The old radial exterior homeomorphism preserves both coordinate open caps. -/
theorem standardUnlinkComplementExteriorHomeomorph_mem_coordinateOpenCap_iff
    (q : StandardUnlinkComplement) (i : Fin 2) :
    (standardUnlinkComplementExteriorHomeomorph q : Sphere 4) ∈ coordinateOpenCap i ↔
      q.1 ∈ coordinateOpenCap i := by
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · have hout0 : standardUnlinkComplementTubeForward 0 ⟨q, h0⟩ ∈
        standardUnlinkOpenTube 0 (3 / 8 : ℝ) :=
      standardUnlinkComplementTubeForward_mem_openTube 0 ⟨q, h0⟩
    have hqCap0 := standardUnlinkOpenTube_zero_subset_coordinateOpenCap_zero h0
    have houtCap0 := standardUnlinkOpenTube_zero_subset_coordinateOpenCap_zero hout0
    rw [standardUnlinkComplementExteriorHomeomorph_coe,
      standardUnlinkComplementExteriorForwardRaw_of_mem_zero q h0]
    fin_cases i
    · exact iff_of_true houtCap0 hqCap0
    · change 0 < (standardUnlinkComplementTubeForward 0 ⟨q, h0⟩).1 3 ↔
        0 < q.1.1 3
      rw [mem_coordinateOpenCap_zero] at houtCap0 hqCap0
      constructor <;> intro h <;> linarith
  · by_cases h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)
    · have hout1 : standardUnlinkComplementTubeForward 1 ⟨q, h1⟩ ∈
          standardUnlinkOpenTube 1 (3 / 8 : ℝ) :=
        standardUnlinkComplementTubeForward_mem_openTube 1 ⟨q, h1⟩
      have hqCap1 := standardUnlinkOpenTube_one_subset_coordinateOpenCap_one h1
      have houtCap1 := standardUnlinkOpenTube_one_subset_coordinateOpenCap_one hout1
      rw [standardUnlinkComplementExteriorHomeomorph_coe,
        standardUnlinkComplementExteriorForwardRaw_of_mem_one q h1]
      fin_cases i
      · change (standardUnlinkComplementTubeForward 1 ⟨q, h1⟩).1 3 < 0 ↔
          q.1.1 3 < 0
        rw [mem_coordinateOpenCap_one] at houtCap1 hqCap1
        constructor <;> intro h <;> linarith
      · exact iff_of_true houtCap1 hqCap1
    · rw [standardUnlinkComplementExteriorHomeomorph_coe,
        standardUnlinkComplementExteriorForwardRaw_of_not_mem q h0 h1]

/-- The inverse old radial exterior homeomorphism preserves both coordinate open caps. -/
theorem standardUnlinkComplementExteriorHomeomorph_symm_mem_coordinateOpenCap_iff
    (q : StandardUnlinkClosedTubeExterior) (i : Fin 2) :
    (standardUnlinkComplementExteriorHomeomorph.symm q : Sphere 4) ∈
        coordinateOpenCap i ↔
      q.1 ∈ coordinateOpenCap i := by
  let z := standardUnlinkComplementExteriorHomeomorph.symm q
  have h := standardUnlinkComplementExteriorHomeomorph_mem_coordinateOpenCap_iff z i
  rw [standardUnlinkComplementExteriorHomeomorph.apply_symm_apply] at h
  exact h.symm

private theorem mem_coordinateEquator_iff_not_mem_coordinateOpenCaps
    (x : Sphere 4) :
    x ∈ coordinateEquator ↔
      x ∉ coordinateOpenCap 0 ∧ x ∉ coordinateOpenCap 1 := by
  change x.1 3 = 0 ↔ ¬x.1 3 < 0 ∧ ¬0 < x.1 3
  constructor
  · intro hx
    constructor <;> linarith
  · rintro ⟨hneg, hpos⟩
    exact le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)

private theorem standardUnlinkComplementExteriorHomeomorph_mem_coordinateEquator_iff
    (q : StandardUnlinkComplement) :
    (standardUnlinkComplementExteriorHomeomorph q : Sphere 4) ∈ coordinateEquator ↔
      q.1 ∈ coordinateEquator := by
  rw [mem_coordinateEquator_iff_not_mem_coordinateOpenCaps,
    mem_coordinateEquator_iff_not_mem_coordinateOpenCaps,
    standardUnlinkComplementExteriorHomeomorph_mem_coordinateOpenCap_iff,
    standardUnlinkComplementExteriorHomeomorph_mem_coordinateOpenCap_iff]

/-- The inverse old radial exterior homeomorphism preserves the coordinate equator. -/
theorem standardUnlinkComplementExteriorHomeomorph_symm_mem_coordinateEquator_iff
    (q : StandardUnlinkClosedTubeExterior) :
    (standardUnlinkComplementExteriorHomeomorph.symm q : Sphere 4) ∈ coordinateEquator ↔
      q.1 ∈ coordinateEquator := by
  let z := standardUnlinkComplementExteriorHomeomorph.symm q
  have h := standardUnlinkComplementExteriorHomeomorph_mem_coordinateEquator_iff z
  rw [standardUnlinkComplementExteriorHomeomorph.apply_symm_apply] at h
  exact h.symm

private theorem coordinateUnlinkExteriorPlanarFullCoverToNeckStar_symm_strict
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorEighthPowerPullbackStrict m) :
    coordinateUnlinkExteriorPlanarFullCoverToNeckStar m
        ((coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).symm z) =
      coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m z.1 := by
  rw [coordinateUnlinkExteriorPlanarFullCoverToNeckStar,
    ContinuousMap.coe_mk,
    (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).apply_symm_apply]
  rfl

private theorem standardUnlinkPowerPullbackProj_fullCoverStrict_symm_mem_coordinateOpenCap_iff
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorEighthPowerPullbackStrict m) (i : Fin 2) :
    (standardUnlinkPowerPullbackProj m
        ((coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).symm z) : Sphere 4) ∈
          coordinateOpenCap i ↔
      (coordinateUnlinkExteriorEighthPowerPullbackProj m z.1 : Sphere 4) ∈
        coordinateOpenCap i := by
  change (standardUnlinkComplementExteriorHomeomorph.symm
      ((standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictHomeomorph m).symm z).1.1 :
        Sphere 4) ∈ coordinateOpenCap i ↔ (z.1.1.1 : Sphere 4) ∈ coordinateOpenCap i
  rw [standardUnlinkComplementExteriorHomeomorph_symm_mem_coordinateOpenCap_iff]
  rfl

private theorem standardUnlinkPowerPullbackProj_fullCoverStrict_symm_mem_coordinateEquator_iff
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorEighthPowerPullbackStrict m) :
    (standardUnlinkPowerPullbackProj m
        ((coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).symm z) : Sphere 4) ∈
          coordinateEquator ↔
      (coordinateUnlinkExteriorEighthPowerPullbackProj m z.1 : Sphere 4) ∈
        coordinateEquator := by
  change (standardUnlinkComplementExteriorHomeomorph.symm
      ((standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictHomeomorph m).symm z).1.1 :
        Sphere 4) ∈ coordinateEquator ↔ (z.1.1.1 : Sphere 4) ∈ coordinateEquator
  rw [standardUnlinkComplementExteriorHomeomorph_symm_mem_coordinateEquator_iff]
  rfl

private theorem mem_coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam_strict_iff
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorEighthPowerPullbackStrict m) :
    z.1 ∈ coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ↔
      (coordinateUnlinkExteriorEighthPowerPullbackProj m z.1 : Sphere 4) ∈
        coordinateOpenCap 0 := by
  let q := (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).symm z
  change coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m z.1 ∈
      coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam m ↔ _
  rw [← coordinateUnlinkExteriorPlanarFullCoverToNeckStar_symm_strict m z]
  change q ∈ coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam m ↔ _
  rw [coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam_eq_preimage_coordinateOpenCap_zero]
  exact standardUnlinkPowerPullbackProj_fullCoverStrict_symm_mem_coordinateOpenCap_iff m z 0

private theorem mem_coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam_strict_iff
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorEighthPowerPullbackStrict m) :
    z.1 ∈ coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m ↔
      (coordinateUnlinkExteriorEighthPowerPullbackProj m z.1 : Sphere 4) ∈
        coordinateOpenCap 1 := by
  let q := (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).symm z
  change coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m z.1 ∈
      coordinateUnlinkExteriorPlanarNeckStarRightOffSeam m ↔ _
  rw [← coordinateUnlinkExteriorPlanarFullCoverToNeckStar_symm_strict m z]
  change q ∈ coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam m ↔ _
  rw [coordinateUnlinkExteriorPlanarFullCoverGlobalRightOffSeam_eq_preimage_coordinateOpenCap_one]
  exact standardUnlinkPowerPullbackProj_fullCoverStrict_symm_mem_coordinateOpenCap_iff m z 1

private theorem mem_coordinateUnlinkExteriorEighthPowerPullbackStrictOpens_of_proj_mem_equator
    (m : ℕ) (z : CoordinateUnlinkExteriorEighthPowerPullback m)
    (hz : (coordinateUnlinkExteriorEighthPowerPullbackProj m z : Sphere 4) ∈
      coordinateEquator) :
    z ∈ coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m := by
  rw [mem_coordinateUnlinkExteriorEighthPowerPullbackStrictOpens]
  rw [← range_equatorSphereMap] at hz
  obtain ⟨x, hx⟩ := hz
  rw [mem_standardUnlinkClosedTubeExteriorOpens]
  intro i
  have hx' : (z.1.1.1 : Sphere 4) = equatorSphereMap x := by
    simpa using hx.symm
  change 1 / 8 < ‖standardUnlinkNormalProjection (z.1.1.1 : Sphere 4) -
    standardUnlinkNormalCenter i‖
  rw [hx']
  exact lt_trans (by norm_num)
    (quarter_lt_norm_standardUnlinkNormalProjection_equator_sub_center i x)

private theorem mem_coordinateUnlinkExteriorPlanarCompactNeckStarSeam_strict_iff
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorEighthPowerPullbackStrict m) :
    z.1 ∈ coordinateUnlinkExteriorPlanarCompactNeckStarSeam m ↔
      (coordinateUnlinkExteriorEighthPowerPullbackProj m z.1 : Sphere 4) ∈
        coordinateEquator := by
  let q := (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m).symm z
  change coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m z.1 ∈
      coordinateUnlinkExteriorPlanarNeckStarSeam m ↔ _
  rw [← coordinateUnlinkExteriorPlanarFullCoverToNeckStar_symm_strict m z]
  change q ∈ coordinateUnlinkExteriorPlanarFullCoverGlobalSeam m ↔ _
  rw [coordinateUnlinkExteriorPlanarFullCoverGlobalSeam_eq_preimage_coordinateEquator]
  exact standardUnlinkPowerPullbackProj_fullCoverStrict_symm_mem_coordinateEquator_iff m z

/-- The full compact planar-neck seam is exactly the pullback of the coordinate equator. -/
theorem coordinateUnlinkExteriorPlanarCompactNeckStarSeam_eq_preimage_coordinateEquator
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarCompactNeckStarSeam m =
      (fun z : CoordinateUnlinkExteriorEighthPowerPullback m ↦
        (coordinateUnlinkExteriorEighthPowerPullbackProj m z : Sphere 4)) ⁻¹'
          coordinateEquator := by
  ext z
  constructor
  · intro hz
    rw [coordinateUnlinkExteriorPlanarCompactNeckStarSeam_eq_range_transport_family] at hz
    obtain ⟨⟨a, s⟩, rfl⟩ := hz
    exact coordinateUnlinkExteriorPlanarNeckTransport_sphere_proj_mem_coordinateEquator m a s
  · intro hz
    let zs : CoordinateUnlinkExteriorEighthPowerPullbackStrict m :=
      ⟨z, mem_coordinateUnlinkExteriorEighthPowerPullbackStrictOpens_of_proj_mem_equator m z hz⟩
    exact (mem_coordinateUnlinkExteriorPlanarCompactNeckStarSeam_strict_iff m zs).mpr hz

private theorem coordinateUnlinkExteriorEighthPowerPullback_interior_eq_strict
    (m : ℕ) [NeZero m] :
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
    coordinateUnlinkExteriorModel.interior
        (CoordinateUnlinkExteriorEighthPowerPullback m) =
      {z | z ∈ coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m} := by
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
  rw [← coordinateUnlinkExteriorModel.compl_boundary,
    coordinateUnlinkExteriorEighthPowerPullback_boundary,
    ← preimage_compl,
    coordinateUnlinkExteriorEighthRadialBoundary_eq_compl_interior,
    compl_compl]
  ext z
  rw [mem_preimage]
  change z.1.1.1 ∈ standardUnlinkClosedTubeExteriorOpens ↔
    z.1.1 ∈ coordinateUnlinkExteriorEighthInteriorOpens
  rw [mem_standardUnlinkClosedTubeExteriorOpens,
    mem_coordinateUnlinkExteriorEighthInteriorOpens_iff]

private theorem dense_coordinateUnlinkExteriorEighthPowerPullbackStrictOpens
    (m : ℕ) [NeZero m] :
    Dense {z : CoordinateUnlinkExteriorEighthPowerPullback m |
      z ∈ coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m} := by
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
  rw [← coordinateUnlinkExteriorEighthPowerPullback_interior_eq_strict m]
  exact dense_modelWithCorners_interior (n := ∞) coordinateUnlinkExteriorModel
    (CoordinateUnlinkExteriorEighthPowerPullback m) (by simp)

private def coordinateUnlinkExteriorCompactCapPreimage
    (m : ℕ) (i : Fin 2) :
    Set (CoordinateUnlinkExteriorEighthPowerPullback m) :=
  (fun z : CoordinateUnlinkExteriorEighthPowerPullback m ↦
    (coordinateUnlinkExteriorEighthPowerPullbackProj m z : Sphere 4)) ⁻¹'
      coordinateOpenCap i

private theorem isOpen_coordinateOpenCap_probe (i : Fin 2) :
    IsOpen (coordinateOpenCap i) := by
  fin_cases i
  · change IsOpen ((fun x : Sphere 4 ↦ x.1 3) ⁻¹' Iio 0)
    exact isOpen_Iio.preimage (by fun_prop)
  · change IsOpen ((fun x : Sphere 4 ↦ x.1 3) ⁻¹' Ioi 0)
    exact isOpen_Ioi.preimage (by fun_prop)

private theorem continuous_coordinateUnlinkExteriorCompactBaseProj
    (m : ℕ) [NeZero m] :
    Continuous (fun z : CoordinateUnlinkExteriorEighthPowerPullback m ↦
      (coordinateUnlinkExteriorEighthPowerPullbackProj m z : Sphere 4)) :=
  continuous_subtype_val.comp
    (isCoveringMap_coordinateUnlinkExteriorEighthPowerPullbackProj m).continuous

private theorem isOpen_coordinateUnlinkExteriorCompactCapPreimage
    (m : ℕ) [NeZero m] (i : Fin 2) :
    IsOpen (coordinateUnlinkExteriorCompactCapPreimage m i) :=
  (isOpen_coordinateOpenCap_probe i).preimage
    (continuous_coordinateUnlinkExteriorCompactBaseProj m)

private theorem disjoint_coordinateOpenCaps_probe :
    Disjoint (coordinateOpenCap 0) (coordinateOpenCap 1) := by
  rw [Set.disjoint_left]
  intro x hx0 hx1
  rw [mem_coordinateOpenCap_zero] at hx0
  rw [mem_coordinateOpenCap_one] at hx1
  linarith

private theorem coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam_subset_cap_zero
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ⊆
      coordinateUnlinkExteriorCompactCapPreimage m 0 := by
  intro z hzLeft
  by_contra hzCapZero
  have hzNotSeam : z ∉ coordinateUnlinkExteriorPlanarCompactNeckStarSeam m := by
    have hzCompl : z ∈
        (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)ᶜ := by
      rw [← union_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam]
      exact Or.inl hzLeft
    exact hzCompl
  have hzBaseNotEquator :
      (coordinateUnlinkExteriorEighthPowerPullbackProj m z : Sphere 4) ∉
        coordinateEquator := by
    intro hzEquator
    apply hzNotSeam
    rw [coordinateUnlinkExteriorPlanarCompactNeckStarSeam_eq_preimage_coordinateEquator]
    exact hzEquator
  have hzCapUnion :
      (coordinateUnlinkExteriorEighthPowerPullbackProj m z : Sphere 4) ∈
        coordinateOpenCap 0 ∪ coordinateOpenCap 1 := by
    rw [← compl_coordinateEquator_eq_union_openCaps]
    exact hzBaseNotEquator
  have hzCapOne : z ∈ coordinateUnlinkExteriorCompactCapPreimage m 1 :=
    hzCapUnion.resolve_left hzCapZero
  let U := coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ∩
    coordinateUnlinkExteriorCompactCapPreimage m 1
  have hUOpen : IsOpen U :=
    (isOpen_coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m).inter
      (isOpen_coordinateUnlinkExteriorCompactCapPreimage m 1)
  have hUNonempty : U.Nonempty := ⟨z, hzLeft, hzCapOne⟩
  obtain ⟨y, hyStrict, hyLeft, hyCapOne⟩ :=
    (dense_coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m).exists_mem_open
      hUOpen hUNonempty
  let ys : CoordinateUnlinkExteriorEighthPowerPullbackStrict m := ⟨y, hyStrict⟩
  have hyCapZero :=
    (mem_coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam_strict_iff m ys).mp
      hyLeft
  exact (disjoint_coordinateOpenCaps_probe.le_bot ⟨hyCapZero, hyCapOne⟩).elim

private theorem coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam_subset_cap_one
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m ⊆
      coordinateUnlinkExteriorCompactCapPreimage m 1 := by
  intro z hzRight
  by_contra hzCapOne
  have hzNotSeam : z ∉ coordinateUnlinkExteriorPlanarCompactNeckStarSeam m := by
    have hzCompl : z ∈
        (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)ᶜ := by
      rw [← union_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam]
      exact Or.inr hzRight
    exact hzCompl
  have hzBaseNotEquator :
      (coordinateUnlinkExteriorEighthPowerPullbackProj m z : Sphere 4) ∉
        coordinateEquator := by
    intro hzEquator
    apply hzNotSeam
    rw [coordinateUnlinkExteriorPlanarCompactNeckStarSeam_eq_preimage_coordinateEquator]
    exact hzEquator
  have hzCapUnion :
      (coordinateUnlinkExteriorEighthPowerPullbackProj m z : Sphere 4) ∈
        coordinateOpenCap 0 ∪ coordinateOpenCap 1 := by
    rw [← compl_coordinateEquator_eq_union_openCaps]
    exact hzBaseNotEquator
  have hzCapZero : z ∈ coordinateUnlinkExteriorCompactCapPreimage m 0 :=
    hzCapUnion.resolve_right hzCapOne
  let U := coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m ∩
    coordinateUnlinkExteriorCompactCapPreimage m 0
  have hUOpen : IsOpen U :=
    (isOpen_coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m).inter
      (isOpen_coordinateUnlinkExteriorCompactCapPreimage m 0)
  have hUNonempty : U.Nonempty := ⟨z, hzRight, hzCapZero⟩
  obtain ⟨y, hyStrict, hyRight, hyCapZero⟩ :=
    (dense_coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m).exists_mem_open
      hUOpen hUNonempty
  let ys : CoordinateUnlinkExteriorEighthPowerPullbackStrict m := ⟨y, hyStrict⟩
  have hyCapOne :=
    (mem_coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam_strict_iff m ys).mp
      hyRight
  exact (disjoint_coordinateOpenCaps_probe.le_bot ⟨hyCapZero, hyCapOne⟩).elim

/-- The compact global left side is exactly the pullback of the negative coordinate cap. -/
theorem coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam_eq_preimage_coordinateOpenCap_zero
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m =
      (fun z : CoordinateUnlinkExteriorEighthPowerPullback m ↦
        (coordinateUnlinkExteriorEighthPowerPullbackProj m z : Sphere 4)) ⁻¹'
          coordinateOpenCap 0 := by
  apply Subset.antisymm
  · exact coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam_subset_cap_zero m
  · intro z hzCapZero
    have hzNotSeam : z ∉ coordinateUnlinkExteriorPlanarCompactNeckStarSeam m := by
      rw [coordinateUnlinkExteriorPlanarCompactNeckStarSeam_eq_preimage_coordinateEquator]
      exact coordinateOpenCap_subset_compl_coordinateEquator 0 hzCapZero
    have hzSides : z ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ∪
          coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m := by
      rw [union_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam]
      exact hzNotSeam
    rcases hzSides with hzLeft | hzRight
    · exact hzLeft
    · have hzCapOne :=
        coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam_subset_cap_one m hzRight
      exact (disjoint_coordinateOpenCaps_probe.le_bot ⟨hzCapZero, hzCapOne⟩).elim

/-- The compact global right side is exactly the pullback of the positive coordinate cap. -/
theorem coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam_eq_preimage_coordinateOpenCap_one
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m =
      (fun z : CoordinateUnlinkExteriorEighthPowerPullback m ↦
        (coordinateUnlinkExteriorEighthPowerPullbackProj m z : Sphere 4)) ⁻¹'
          coordinateOpenCap 1 := by
  apply Subset.antisymm
  · exact coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam_subset_cap_one m
  · intro z hzCapOne
    have hzNotSeam : z ∉ coordinateUnlinkExteriorPlanarCompactNeckStarSeam m := by
      rw [coordinateUnlinkExteriorPlanarCompactNeckStarSeam_eq_preimage_coordinateEquator]
      exact coordinateOpenCap_subset_compl_coordinateEquator 1 hzCapOne
    have hzSides : z ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ∪
          coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m := by
      rw [union_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam]
      exact hzNotSeam
    rcases hzSides with hzLeft | hzRight
    · have hzCapZero :=
        coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam_subset_cap_zero m hzLeft
      exact (disjoint_coordinateOpenCaps_probe.le_bot ⟨hzCapZero, hzCapOne⟩).elim
    · exact hzRight

/-- The compact closed left cut carrier is the pullback of the complement of the positive cap. -/
theorem coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier_eq_preimage_compl_cap_one
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m =
      (fun z : CoordinateUnlinkExteriorEighthPowerPullback m ↦
        (coordinateUnlinkExteriorEighthPowerPullbackProj m z : Sphere 4)) ⁻¹'
          (coordinateOpenCap 1)ᶜ := by
  rw [coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier,
    coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam_eq_preimage_coordinateOpenCap_one,
    preimage_compl]

/-- The compact closed right cut carrier is the pullback of the complement of the negative cap. -/
theorem coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier_eq_preimage_compl_cap_zero
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m =
      (fun z : CoordinateUnlinkExteriorEighthPowerPullback m ↦
        (coordinateUnlinkExteriorEighthPowerPullbackProj m z : Sphere 4)) ⁻¹'
          (coordinateOpenCap 0)ᶜ := by
  rw [coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier,
    coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam_eq_preimage_coordinateOpenCap_zero,
    preimage_compl]

end SplittingSpheres

end
