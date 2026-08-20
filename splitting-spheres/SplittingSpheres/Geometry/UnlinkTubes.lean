/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.IsotopyTrace

/-!
# Explicit coordinate neighborhoods of the standard unlink

Projection to the last two ambient coordinates sends each component of the standard unlink to
one of the two points `(-1/2, 0)` and `(1/2, 0)`.  On the unit four-sphere the inverse image of
either point is exactly the corresponding component.  Pulling back small disks therefore gives
explicit coordinate neighborhoods of the two components.

This file proves the point-set neighborhood and compact-exterior properties, including uniform
containment of every link-avoiding isotopy trace in one such exterior.  It does not yet identify
these neighborhoods with smooth normal disk bundles.
-/

@[expose] public section

open Function Metric Set Topology
open scoped ContDiff Manifold unitInterval

noncomputable section

namespace SplittingSpheres

/-- The two-dimensional plane of the final two ambient coordinates. -/
abbrev UnlinkNormalPlane := EuclideanSpace ℝ (Fin 2)

/-- Projection of the ambient four-sphere to coordinates `(x₃,x₄)`. -/
def standardUnlinkNormalProjection (x : Sphere 4) : UnlinkNormalPlane :=
  WithLp.toLp 2 ![x.1 3, x.1 4]

@[simp]
theorem standardUnlinkNormalProjection_apply_zero (x : Sphere 4) :
    standardUnlinkNormalProjection x 0 = x.1 3 :=
  rfl

@[simp]
theorem standardUnlinkNormalProjection_apply_one (x : Sphere 4) :
    standardUnlinkNormalProjection x 1 = x.1 4 :=
  rfl

/-- The center in the normal coordinate plane corresponding to component `i`. -/
def standardUnlinkNormalCenter (i : Fin 2) : UnlinkNormalPlane :=
  WithLp.toLp 2 ![standardUnlinkHeight i, 0]

@[simp]
theorem standardUnlinkNormalCenter_apply_zero (i : Fin 2) :
    standardUnlinkNormalCenter i 0 = standardUnlinkHeight i :=
  rfl

@[simp]
theorem standardUnlinkNormalCenter_apply_one (i : Fin 2) :
    standardUnlinkNormalCenter i 1 = 0 :=
  rfl

/-- The normal projection is continuous. -/
theorem continuous_standardUnlinkNormalProjection :
    Continuous standardUnlinkNormalProjection := by
  unfold standardUnlinkNormalProjection
  fun_prop

/-- The normal-coordinate projection is smooth. -/
theorem contMDiff_standardUnlinkNormalProjection :
    ContMDiff (𝓡 4) (𝓡 2) ∞ standardUnlinkNormalProjection := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) := ⟨by simp⟩
  have hambient : ContDiff ℝ ∞
      (fun x : EuclideanSpace ℝ (Fin 5) ↦
        (WithLp.toLp 2 ![x 3, x 4] : UnlinkNormalPlane)) := by
    rw [contDiff_piLp]
    intro j
    fin_cases j
    · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero]
      fun_prop
    · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      fun_prop
  exact hambient.comp_contMDiff contMDiff_coe_sphere

/-- The inverse image of a normal center is exactly the matching unlink component. -/
theorem preimage_singleton_standardUnlinkNormalCenter (i : Fin 2) :
    standardUnlinkNormalProjection ⁻¹' {standardUnlinkNormalCenter i} =
      standardUnlinkComponent i := by
  ext x
  simp only [mem_preimage, mem_singleton_iff, standardUnlinkComponent, mem_ofPred_eq]
  constructor
  · intro h
    have h0 := congrArg (fun z : UnlinkNormalPlane ↦ z 0) h
    have h1 := congrArg (fun z : UnlinkNormalPlane ↦ z 1) h
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    ext j
    fin_cases j
    · exact h0
    · exact h1

/-- The two normal centers as a finite subset of the normal plane. -/
def standardUnlinkNormalCenters : Set UnlinkNormalPlane :=
  {standardUnlinkNormalCenter 0, standardUnlinkNormalCenter 1}

/-- The full unlink carrier is exactly the inverse image of the two normal centers. -/
theorem preimage_standardUnlinkNormalCenters :
    standardUnlinkNormalProjection ⁻¹' standardUnlinkNormalCenters =
      standardUnlinkCarrier := by
  rw [standardUnlinkNormalCenters, pair_comm, ← union_singleton,
    preimage_union, preimage_singleton_standardUnlinkNormalCenter,
    preimage_singleton_standardUnlinkNormalCenter]
  rfl

/-- The finite set of normal centers is compact. -/
theorem isCompact_standardUnlinkNormalCenters :
    IsCompact standardUnlinkNormalCenters := by
  simp [standardUnlinkNormalCenters]

/-- The open coordinate tube of radius `r` around component `i`. -/
def standardUnlinkOpenTube (i : Fin 2) (r : ℝ) : Set (Sphere 4) :=
  standardUnlinkNormalProjection ⁻¹' ball (standardUnlinkNormalCenter i) r

/-- The closed coordinate tube of radius `r` around component `i`. -/
def standardUnlinkClosedTube (i : Fin 2) (r : ℝ) : Set (Sphere 4) :=
  standardUnlinkNormalProjection ⁻¹' closedBall (standardUnlinkNormalCenter i) r

/-- The union of the two open coordinate tubes. -/
def standardUnlinkOpenTubes (r : ℝ) : Set (Sphere 4) :=
  standardUnlinkOpenTube 0 r ∪ standardUnlinkOpenTube 1 r

/-- The union of the two closed coordinate tubes. -/
def standardUnlinkClosedTubes (r : ℝ) : Set (Sphere 4) :=
  standardUnlinkClosedTube 0 r ∪ standardUnlinkClosedTube 1 r

theorem isOpen_standardUnlinkOpenTube (i : Fin 2) (r : ℝ) :
    IsOpen (standardUnlinkOpenTube i r) :=
  isOpen_ball.preimage continuous_standardUnlinkNormalProjection

theorem isClosed_standardUnlinkClosedTube (i : Fin 2) (r : ℝ) :
    IsClosed (standardUnlinkClosedTube i r) :=
  isClosed_closedBall.preimage continuous_standardUnlinkNormalProjection

theorem isOpen_standardUnlinkOpenTubes (r : ℝ) :
    IsOpen (standardUnlinkOpenTubes r) :=
  (isOpen_standardUnlinkOpenTube 0 r).union (isOpen_standardUnlinkOpenTube 1 r)

theorem isClosed_standardUnlinkClosedTubes (r : ℝ) :
    IsClosed (standardUnlinkClosedTubes r) :=
  (isClosed_standardUnlinkClosedTube 0 r).union
    (isClosed_standardUnlinkClosedTube 1 r)

/-- Every positive-radius open tube contains its matching link component. -/
theorem standardUnlinkComponent_subset_openTube (i : Fin 2) {r : ℝ} (hr : 0 < r) :
    standardUnlinkComponent i ⊆ standardUnlinkOpenTube i r := by
  rw [← preimage_singleton_standardUnlinkNormalCenter i]
  exact preimage_mono (singleton_subset_iff.2 (mem_ball_self hr))

/-- The union of positive-radius open tubes contains the whole unlink carrier. -/
theorem standardUnlinkCarrier_subset_openTubes {r : ℝ} (hr : 0 < r) :
    standardUnlinkCarrier ⊆ standardUnlinkOpenTubes r := by
  rintro x (hx | hx)
  · exact Or.inl (standardUnlinkComponent_subset_openTube 0 hr hx)
  · exact Or.inr (standardUnlinkComponent_subset_openTube 1 hr hx)

/-- The coordinate unlink exterior obtained by removing both open tubes. -/
def coordinateUnlinkExterior (r : ℝ) : Set (Sphere 4) :=
  (standardUnlinkOpenTubes r)ᶜ

/-- Every coordinate unlink exterior is compact. -/
theorem isCompact_coordinateUnlinkExterior (r : ℝ) :
    IsCompact (coordinateUnlinkExterior r) :=
  (isOpen_standardUnlinkOpenTubes r).isClosed_compl.isCompact

/-- The two centers in the normal plane are distance one apart. -/
@[simp]
theorem dist_standardUnlinkNormalCenter_zero_one :
    dist (standardUnlinkNormalCenter 0) (standardUnlinkNormalCenter 1) = 1 := by
  rw [dist_eq_norm]
  have hsq :
      ‖standardUnlinkNormalCenter 0 - standardUnlinkNormalCenter 1‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [standardUnlinkNormalCenter, standardUnlinkHeight, Fin.sum_univ_succ]
    norm_num
  nlinarith [norm_nonneg (standardUnlinkNormalCenter 0 - standardUnlinkNormalCenter 1)]

/-- Closed coordinate tubes of radius below `1/2` are disjoint. -/
theorem disjoint_standardUnlinkClosedTube_zero_one {r : ℝ} (hr : r < 1 / 2) :
    Disjoint (standardUnlinkClosedTube 0 r) (standardUnlinkClosedTube 1 r) := by
  apply Disjoint.preimage standardUnlinkNormalProjection
  apply Metric.closedBall_disjoint_closedBall
  rw [dist_standardUnlinkNormalCenter_zero_one]
  linarith

/-- Open coordinate tubes of radius below `1/2` are disjoint as well. -/
theorem disjoint_standardUnlinkOpenTube_zero_one {r : ℝ} (hr : r < 1 / 2) :
    Disjoint (standardUnlinkOpenTube 0 r) (standardUnlinkOpenTube 1 r) :=
  (disjoint_standardUnlinkClosedTube_zero_one hr).mono
    (preimage_mono ball_subset_closedBall) (preimage_mono ball_subset_closedBall)

/-- The closed thickening of the two normal centers is the union of the two closed disks. -/
theorem cthickening_standardUnlinkNormalCenters {r : ℝ} (hr : 0 ≤ r) :
    Metric.cthickening r standardUnlinkNormalCenters =
      closedBall (standardUnlinkNormalCenter 0) r ∪
        closedBall (standardUnlinkNormalCenter 1) r := by
  rw [show standardUnlinkNormalCenters =
      ({standardUnlinkNormalCenter 0} : Set UnlinkNormalPlane) ∪
        {standardUnlinkNormalCenter 1} by
      ext z
      simp only [standardUnlinkNormalCenters, mem_insert_iff, mem_singleton_iff,
        mem_union]]
  rw [Metric.cthickening_union,
    Metric.cthickening_singleton (standardUnlinkNormalCenter 0) hr,
    Metric.cthickening_singleton (standardUnlinkNormalCenter 1) hr]

/-- Pulling back that thickening gives exactly the union of the two closed coordinate tubes. -/
theorem preimage_cthickening_standardUnlinkNormalCenters {r : ℝ} (hr : 0 ≤ r) :
    standardUnlinkNormalProjection ⁻¹'
        Metric.cthickening r standardUnlinkNormalCenters =
      standardUnlinkClosedTubes r := by
  rw [cthickening_standardUnlinkNormalCenters hr, preimage_union]
  rfl

/-- The projected image of an isotopy trace is compact. -/
theorem SmoothSphereIsotopy.isCompact_normalProjection_image_trace
    {S₀ S₁ : SmoothSphereEmbedding 3 4} (H : SmoothSphereIsotopy S₀ S₁) :
    IsCompact (standardUnlinkNormalProjection '' H.trace) :=
  H.isCompact_trace.image continuous_standardUnlinkNormalProjection

/-- Avoidance of the unlink makes the projected trace disjoint from both normal centers. -/
theorem SmoothSphereIsotopy.disjoint_normalProjection_image_trace_normalCenters
    {S₀ S₁ : SmoothSphereEmbedding 3 4} (H : SmoothSphereIsotopy S₀ S₁)
    (havoid : ∀ p : I × Sphere 3, H.toFun p ∉ standardUnlinkCarrier) :
    Disjoint (standardUnlinkNormalProjection '' H.trace)
      standardUnlinkNormalCenters := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hxtrace, rfl⟩ hxcenter
  have hxcarrier : x ∈ standardUnlinkCarrier := by
    rw [← preimage_standardUnlinkNormalCenters]
    exact hxcenter
  obtain ⟨p, rfl⟩ := hxtrace
  exact havoid p hxcarrier

/-- An open coordinate tube is contained in the corresponding closed tube. -/
theorem standardUnlinkOpenTube_subset_closedTube (i : Fin 2) (r : ℝ) :
    standardUnlinkOpenTube i r ⊆ standardUnlinkClosedTube i r :=
  preimage_mono ball_subset_closedBall

/-- The union of open tubes is contained in the union of closed tubes. -/
theorem standardUnlinkOpenTubes_subset_closedTubes (r : ℝ) :
    standardUnlinkOpenTubes r ⊆ standardUnlinkClosedTubes r := by
  rintro x (hx | hx)
  · exact Or.inl (standardUnlinkOpenTube_subset_closedTube 0 r hx)
  · exact Or.inr (standardUnlinkOpenTube_subset_closedTube 1 r hx)

/-- Increasing the radius increases each coordinate tube. -/
theorem standardUnlinkOpenTube_mono (i : Fin 2) {r q : ℝ} (hrq : r ≤ q) :
    standardUnlinkOpenTube i r ⊆ standardUnlinkOpenTube i q :=
  preimage_mono (Metric.ball_subset_ball hrq)

/-- Increasing the radius increases the union of coordinate tubes. -/
theorem standardUnlinkOpenTubes_mono {r q : ℝ} (hrq : r ≤ q) :
    standardUnlinkOpenTubes r ⊆ standardUnlinkOpenTubes q := by
  rintro x (hx | hx)
  · exact Or.inl (standardUnlinkOpenTube_mono 0 hrq hx)
  · exact Or.inr (standardUnlinkOpenTube_mono 1 hrq hx)

/-- Decreasing the tube radius increases the coordinate exterior. -/
theorem coordinateUnlinkExterior_anti {r q : ℝ} (hrq : r ≤ q) :
    coordinateUnlinkExterior q ⊆ coordinateUnlinkExterior r :=
  compl_subset_compl.mpr (standardUnlinkOpenTubes_mono hrq)

/-- Every unlink-complement isotopy trace lies in a positive-radius coordinate exterior. -/
theorem SmoothSphereIsotopy.exists_trace_subset_coordinateUnlinkExterior
    {S₀ S₁ : SmoothSphereEmbedding 3 4} (H : SmoothSphereIsotopy S₀ S₁)
    (havoid : ∀ p : I × Sphere 3, H.toFun p ∉ standardUnlinkCarrier) :
    ∃ r : ℝ, 0 < r ∧ H.trace ⊆ coordinateUnlinkExterior r := by
  have hdisj := H.disjoint_normalProjection_image_trace_normalCenters havoid
  obtain ⟨r, hr, hthick⟩ := hdisj.exists_cthickenings
    H.isCompact_normalProjection_image_trace isCompact_standardUnlinkNormalCenters.isClosed
  refine ⟨r, hr, ?_⟩
  intro x hxtrace
  rw [coordinateUnlinkExterior, mem_compl_iff]
  intro hxopen
  have hxclosed : x ∈ standardUnlinkClosedTubes r :=
    standardUnlinkOpenTubes_subset_closedTubes r hxopen
  have hxcenters : standardUnlinkNormalProjection x ∈
      Metric.cthickening r standardUnlinkNormalCenters := by
    change x ∈ standardUnlinkNormalProjection ⁻¹'
      Metric.cthickening r standardUnlinkNormalCenters
    rw [preimage_cthickening_standardUnlinkNormalCenters hr.le]
    exact hxclosed
  have hxprojected : standardUnlinkNormalProjection x ∈
      standardUnlinkNormalProjection '' H.trace :=
    ⟨x, hxtrace, rfl⟩
  have hxtraceThick : standardUnlinkNormalProjection x ∈
      Metric.cthickening r (standardUnlinkNormalProjection '' H.trace) :=
    Metric.self_subset_cthickening _ hxprojected
  exact Set.disjoint_left.1 hthick hxtraceThick hxcenters

/-- The radius can be chosen below `1/2`, so the two closed tubes are also disjoint. -/
theorem SmoothSphereIsotopy.exists_disjoint_tubes_trace_subset_coordinateUnlinkExterior
    {S₀ S₁ : SmoothSphereEmbedding 3 4} (H : SmoothSphereIsotopy S₀ S₁)
    (havoid : ∀ p : I × Sphere 3, H.toFun p ∉ standardUnlinkCarrier) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
      Disjoint (standardUnlinkClosedTube 0 r) (standardUnlinkClosedTube 1 r) ∧
      H.trace ⊆ coordinateUnlinkExterior r := by
  obtain ⟨q, hq, htrace⟩ := H.exists_trace_subset_coordinateUnlinkExterior havoid
  let r := min q (1 / 4 : ℝ)
  have hr : 0 < r := lt_min hq (by norm_num)
  have hrq : r ≤ q := min_le_left _ _
  have hrhalf : r < 1 / 2 := (min_le_right q (1 / 4 : ℝ)).trans_lt (by norm_num)
  exact ⟨r, hr, hrhalf, disjoint_standardUnlinkClosedTube_zero_one hrhalf,
    htrace.trans (coordinateUnlinkExterior_anti hrq)⟩

/-- Frozen complement isotopy unpacked together with a compact coordinate exterior containing
its whole trace and disjoint closed coordinate neighborhoods of the two link components. -/
theorem SmoothlyIsotopicInComplement.exists_isotopy_trace_in_coordinateUnlinkExterior
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (h : SmoothlyIsotopicInComplement S₀ S₁) :
    ∃ H : SmoothSphereIsotopy S₀ S₁, ∃ r : ℝ,
      0 < r ∧ r < 1 / 2 ∧
      Disjoint (standardUnlinkClosedTube 0 r) (standardUnlinkClosedTube 1 r) ∧
      H.trace ⊆ coordinateUnlinkExterior r := by
  obtain ⟨H, havoid⟩ := h
  obtain ⟨r, hr, hrhalf, hdisj, htrace⟩ :=
    H.exists_disjoint_tubes_trace_subset_coordinateUnlinkExterior havoid
  exact ⟨H, r, hr, hrhalf, hdisj, htrace⟩

end SplittingSpheres
