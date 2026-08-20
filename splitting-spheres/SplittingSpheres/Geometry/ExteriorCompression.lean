/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.OpenDiffeomorphExtension
public import SplittingSpheres.Foundations.RadialDiffeomorph
public import SplittingSpheres.Geometry.ExteriorIsotopyTransport
public import SplittingSpheres.Geometry.SpherePolarProduct

/-!
# Compressing coordinate unlink exteriors

The polar product coordinates around each displayed unlink component turn an annular radial
compression of the normal disk into a tube diffeomorphism.  Its support is closed inside the
coordinate tube, so it extends by the identity to `S⁴`.
-/

@[expose] public section

open Function Metric Set
open TopologicalSpace
open scoped ContDiff Manifold Topology unitInterval

noncomputable section

namespace SplittingSpheres

/-- The centered annular compression on one unlink normal disk. -/
def standardUnlinkNormalCompression (i : Fin 2) (d a b c R : ℝ) (hd : 0 < d)
    (hda : d < a) (hab : a < b) (hbc : b < c) (hcR : c ≤ R) :
    UnlinkNormalDisk i R ≃ₘ^∞⟮𝓘(ℝ, UnlinkNormalPlane), 𝓘(ℝ, UnlinkNormalPlane)⟯
      UnlinkNormalDisk i R :=
  centeredAnnularRadialOpenBallCompression (standardUnlinkNormalCenter i)
    d a b c R hd hda hab hbc hcR

@[simp]
theorem standardUnlinkNormalCompression_apply_coe (i : Fin 2) (d a b c R : ℝ)
    (hd : 0 < d) (hda : d < a) (hab : a < b) (hbc : b < c) (hcR : c ≤ R)
    (v : UnlinkNormalDisk i R) :
    (standardUnlinkNormalCompression i d a b c R hd hda hab hbc hcR v :
      UnlinkNormalPlane) =
      centeredAnnularRadialCompression (standardUnlinkNormalCenter i)
        d a b c hd hda hab hbc v.1 := rfl

/-- Act trivially on the unlink component and compress only the normal-disk factor. -/
def standardUnlinkTubeProductCompression (i : Fin 2) (d a b c R : ℝ) (hd : 0 < d)
    (hda : d < a) (hab : a < b) (hbc : b < c) (hcR : c ≤ R) :
    (Sphere 2 × UnlinkNormalDisk i R) ≃ₘ^∞⟮
      (𝓡 2).prod 𝓘(ℝ, UnlinkNormalPlane),
      (𝓡 2).prod 𝓘(ℝ, UnlinkNormalPlane)⟯
      (Sphere 2 × UnlinkNormalDisk i R) :=
  Diffeomorph.prodCongr (Diffeomorph.refl (𝓡 2) (Sphere 2) ∞)
    (standardUnlinkNormalCompression i d a b c R hd hda hab hbc hcR)

/-- Conjugate normal radial compression into one polar coordinate tube. -/
def standardUnlinkTubeCompression (i : Fin 2) (d a b c R : ℝ) (hd : 0 < d)
    (hda : d < a) (hab : a < b) (hbc : b < c) (hcR : c ≤ R) (hRhalf : R < 1 / 2) :
    StandardUnlinkOpenTubeSpace i R ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯
      StandardUnlinkOpenTubeSpace i R :=
  (standardUnlinkOpenTubeDiffeomorph i hRhalf).symm |>.trans
    (standardUnlinkTubeProductCompression i d a b c R hd hda hab hbc hcR) |>.trans
      (standardUnlinkOpenTubeDiffeomorph i hRhalf)

@[simp]
theorem standardUnlinkNormalProjection_openTubeDiffeomorph (i : Fin 2) {R : ℝ}
    (hRhalf : R < 1 / 2) (p : Sphere 2 × UnlinkNormalDisk i R) :
    standardUnlinkNormalProjection (standardUnlinkOpenTubeDiffeomorph i hRhalf p).1 = p.2.1 := by
  change standardUnlinkNormalProjection
    (spherePolarForward (spherePolarTubeDomainInclusion i hRhalf p)).1 = p.2.1
  rw [standardUnlinkNormalProjection_spherePolarForward]
  rfl

/-- In tube coordinates, the ambient normal projection changes by exactly the centered scalar
radial compression. -/
theorem standardUnlinkNormalProjection_tubeCompression (i : Fin 2) (d a b c R : ℝ)
    (hd : 0 < d) (hda : d < a) (hab : a < b) (hbc : b < c) (hcR : c ≤ R)
    (hRhalf : R < 1 / 2) (y : StandardUnlinkOpenTubeSpace i R) :
    standardUnlinkNormalProjection
        (standardUnlinkTubeCompression i d a b c R hd hda hab hbc hcR hRhalf y).1 =
      centeredAnnularRadialCompression (standardUnlinkNormalCenter i)
        d a b c hd hda hab hbc (standardUnlinkNormalProjection y.1) := by
  let D := standardUnlinkOpenTubeDiffeomorph i hRhalf
  let p := D.symm y
  change standardUnlinkNormalProjection
      (D ((p.1, standardUnlinkNormalCompression i d a b c R hd hda hab hbc hcR p.2))).1 = _
  rw [standardUnlinkNormalProjection_openTubeDiffeomorph,
    standardUnlinkNormalCompression_apply_coe]
  congr 1

/-- The tube compression is the identity outside its declared closed support tube. -/
theorem standardUnlinkTubeCompression_eq_self_of_not_mem_closedTube
    (i : Fin 2) (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c ≤ R) (hRhalf : R < 1 / 2)
    (y : StandardUnlinkOpenTubeSpace i R) (hy : y.1 ∉ standardUnlinkClosedTube i c) :
    standardUnlinkTubeCompression i d a b c R hd hda hab hbc hcR hRhalf y = y := by
  let D := standardUnlinkOpenTubeDiffeomorph i hRhalf
  let p := D.symm y
  have hpProjection : standardUnlinkNormalProjection y.1 = p.2.1 := by
    have hp := standardUnlinkNormalProjection_openTubeDiffeomorph i hRhalf p
    rw [D.apply_symm_apply] at hp
    exact hp
  have hy' : standardUnlinkNormalProjection y.1 ∉
      closedBall (standardUnlinkNormalCenter i) c := hy
  have hc : c ≤ ‖p.2.1 - standardUnlinkNormalCenter i‖ := by
    rw [← hpProjection]
    rw [mem_closedBall, dist_eq_norm] at hy'
    exact (not_le.mp hy').le
  have hpFixed : standardUnlinkNormalCompression i d a b c R hd hda hab hbc hcR p.2 = p.2 := by
    apply Subtype.ext
    rw [standardUnlinkNormalCompression_apply_coe]
    exact centeredAnnularRadialCompression_eq_self_of_le_norm
      (standardUnlinkNormalCenter i) d a b c hd hda hab hbc hc
  change D (p.1, standardUnlinkNormalCompression i d a b c R hd hda hab hbc hcR p.2) = y
  rw [hpFixed]
  exact D.apply_symm_apply y

/-- The inner disk is also fixed: radial compression is supported in an annulus, not at the link
core. -/
theorem standardUnlinkTubeCompression_eq_self_of_mem_closedTube_inner
    (i : Fin 2) (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c ≤ R) (hRhalf : R < 1 / 2)
    (y : StandardUnlinkOpenTubeSpace i R) (hy : y.1 ∈ standardUnlinkClosedTube i d) :
    standardUnlinkTubeCompression i d a b c R hd hda hab hbc hcR hRhalf y = y := by
  let D := standardUnlinkOpenTubeDiffeomorph i hRhalf
  let p := D.symm y
  have hpProjection : standardUnlinkNormalProjection y.1 = p.2.1 := by
    have hp := standardUnlinkNormalProjection_openTubeDiffeomorph i hRhalf p
    rw [D.apply_symm_apply] at hp
    exact hp
  have hy' : standardUnlinkNormalProjection y.1 ∈
      closedBall (standardUnlinkNormalCenter i) d := hy
  have hdNorm : ‖p.2.1 - standardUnlinkNormalCenter i‖ ≤ d := by
    rw [← hpProjection]
    rwa [mem_closedBall, dist_eq_norm] at hy'
  have hpFixed : standardUnlinkNormalCompression i d a b c R hd hda hab hbc hcR p.2 = p.2 := by
    apply Subtype.ext
    rw [standardUnlinkNormalCompression_apply_coe]
    exact centeredAnnularRadialCompression_eq_self_of_norm_le
      (standardUnlinkNormalCenter i) d a b c hd hda hab hbc hdNorm
  change D (p.1, standardUnlinkNormalCompression i d a b c R hd hda hab hbc hcR p.2) = y
  rw [hpFixed]
  exact D.apply_symm_apply y

theorem standardUnlinkClosedTube_subset_openTube (i : Fin 2) {c R : ℝ} (hcR : c < R) :
    standardUnlinkClosedTube i c ⊆ standardUnlinkOpenTube i R :=
  preimage_mono (closedBall_subset_ball hcR)

/-- Extend one tube compression to an ambient diffeomorphism of the whole four-sphere. -/
def standardUnlinkAmbientTubeCompression (i : Fin 2) (d a b c R : ℝ) (hd : 0 < d)
    (hda : d < a) (hab : a < b) (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) :
    Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4 :=
  extendOpenDiffeomorphByIdentity (standardUnlinkOpenTubeOpens i R)
    (standardUnlinkClosedTube i c)
    (standardUnlinkTubeCompression i d a b c R hd hda hab hbc hcR.le hRhalf)
    (isClosed_standardUnlinkClosedTube i c)
    (standardUnlinkClosedTube_subset_openTube i hcR)
    (fun y hy ↦ standardUnlinkTubeCompression_eq_self_of_not_mem_closedTube
      i d a b c R hd hda hab hbc hcR.le hRhalf y hy)

@[simp]
theorem standardUnlinkAmbientTubeCompression_apply_of_mem (i : Fin 2)
    (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b) (hbc : b < c)
    (hcR : c < R) (hRhalf : R < 1 / 2) {y : Sphere 4}
    (hy : y ∈ standardUnlinkOpenTube i R) :
    standardUnlinkAmbientTubeCompression i d a b c R hd hda hab hbc hcR hRhalf y =
      (standardUnlinkTubeCompression i d a b c R hd hda hab hbc hcR.le hRhalf
        ⟨y, hy⟩).1 :=
  extendOpenDiffeomorphByIdentity_apply_of_mem _ _ _ _ _ _ hy

theorem standardUnlinkAmbientTubeCompression_eq_self_of_not_mem_closedTube
    (i : Fin 2) (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) {y : Sphere 4}
    (hy : y ∉ standardUnlinkClosedTube i c) :
    standardUnlinkAmbientTubeCompression i d a b c R hd hda hab hbc hcR hRhalf y = y :=
  extendOpenDiffeomorphByIdentity_apply_of_not_mem _ _ _ _ _ _ hy

theorem standardUnlinkAmbientTubeCompression_eq_self_of_mem_closedTube_inner
    (i : Fin 2) (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) {y : Sphere 4}
    (hy : y ∈ standardUnlinkClosedTube i d) :
    standardUnlinkAmbientTubeCompression i d a b c R hd hda hab hbc hcR hRhalf y = y := by
  have hyR : y ∈ standardUnlinkOpenTube i R :=
    standardUnlinkClosedTube_subset_openTube i (by linarith) hy
  rw [standardUnlinkAmbientTubeCompression_apply_of_mem
    i d a b c R hd hda hab hbc hcR hRhalf hyR]
  exact congrArg Subtype.val
    (standardUnlinkTubeCompression_eq_self_of_mem_closedTube_inner
      i d a b c R hd hda hab hbc hcR.le hRhalf ⟨y, hyR⟩ hy)

/-- Exact radius formula for the ambient extension, valid throughout its coordinate tube. -/
theorem norm_normalProjection_ambientTubeCompression_sub_center_of_mem
    (i : Fin 2) (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) {y : Sphere 4}
    (hy : y ∈ standardUnlinkOpenTube i R) :
    ‖standardUnlinkNormalProjection
          (standardUnlinkAmbientTubeCompression i d a b c R hd hda hab hbc hcR hRhalf y) -
        standardUnlinkNormalCenter i‖ =
      annularScalarCompression d a b c hda hab hbc
        ‖standardUnlinkNormalProjection y - standardUnlinkNormalCenter i‖ := by
  rw [standardUnlinkAmbientTubeCompression_apply_of_mem i d a b c R hd hda hab hbc hcR
      hRhalf hy,
    standardUnlinkNormalProjection_tubeCompression,
    norm_centeredAnnularRadialCompression_sub_center]

/-- One ambient tube compression takes membership in the old radius-`a` tube exactly to
membership in the new radius-`b` tube. -/
theorem standardUnlinkAmbientTubeCompression_mem_openTube_iff
    (i : Fin 2) (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) (y : Sphere 4) :
    standardUnlinkAmbientTubeCompression i d a b c R hd hda hab hbc hcR hRhalf y ∈
        standardUnlinkOpenTube i b ↔
      y ∈ standardUnlinkOpenTube i a := by
  by_cases hyR : y ∈ standardUnlinkOpenTube i R
  · have hradial :
        annularScalarCompression d a b c hda hab hbc
            ‖standardUnlinkNormalProjection y - standardUnlinkNormalCenter i‖ < b ↔
          ‖standardUnlinkNormalProjection y - standardUnlinkNormalCenter i‖ < a := by
      simpa only [annularScalarCompression_apply_a] using
        (annularScalarCompression_strictMono d a b c hda hab hbc).lt_iff_lt
          (a := ‖standardUnlinkNormalProjection y - standardUnlinkNormalCenter i‖)
          (b := a)
    change standardUnlinkNormalProjection
        (standardUnlinkAmbientTubeCompression i d a b c R hd hda hab hbc hcR hRhalf y) ∈
          ball (standardUnlinkNormalCenter i) b ↔
      standardUnlinkNormalProjection y ∈ ball (standardUnlinkNormalCenter i) a
    rw [mem_ball, dist_eq_norm,
      norm_normalProjection_ambientTubeCompression_sub_center_of_mem
        i d a b c R hd hda hab hbc hcR hRhalf hyR,
      mem_ball, dist_eq_norm]
    exact hradial
  · have hyClosed : y ∉ standardUnlinkClosedTube i c := fun hy ↦
      hyR (standardUnlinkClosedTube_subset_openTube i hcR hy)
    rw [standardUnlinkAmbientTubeCompression_eq_self_of_not_mem_closedTube
      i d a b c R hd hda hab hbc hcR hRhalf hyClosed]
    constructor
    · intro hy
      exact (hyR (standardUnlinkOpenTube_mono i (by linarith) hy)).elim
    · intro hy
      exact (hyR (standardUnlinkOpenTube_mono i (by linarith) hy)).elim

theorem image_standardUnlinkOpenTube_ambientTubeCompression
    (i : Fin 2) (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) :
    standardUnlinkAmbientTubeCompression i d a b c R hd hda hab hbc hcR hRhalf ''
        standardUnlinkOpenTube i a =
      standardUnlinkOpenTube i b := by
  let F := standardUnlinkAmbientTubeCompression i d a b c R hd hda hab hbc hcR hRhalf
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (standardUnlinkAmbientTubeCompression_mem_openTube_iff
      i d a b c R hd hda hab hbc hcR hRhalf x).2 hx
  · intro hy
    refine ⟨F.symm y, ?_, F.apply_symm_apply y⟩
    have hiff := standardUnlinkAmbientTubeCompression_mem_openTube_iff
      i d a b c R hd hda hab hbc hcR hRhalf (F.symm y)
    rw [F.apply_symm_apply] at hiff
    exact hiff.mp hy

theorem standardUnlinkClosedTube_mono (i : Fin 2) {r q : ℝ} (hrq : r ≤ q) :
    standardUnlinkClosedTube i r ⊆ standardUnlinkClosedTube i q :=
  preimage_mono (closedBall_subset_closedBall hrq)

/-- Pointwise fixation of a set by a bijection is equivalent to invariance of membership. -/
theorem Diffeomorph.mem_iff_of_eqOn {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (e : M ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ M) {A : Set M} (hfix : Set.EqOn e id A) (x : M) :
    e x ∈ A ↔ x ∈ A := by
  constructor
  · intro hx
    have heqx : e x = x := by
      have h := congrArg e.symm (hfix hx)
      simpa only [id_eq, Diffeomorph.symm_apply_apply] using h
    simpa only [heqx] using hx
  · intro hx
    simpa [hfix hx] using hx

/-- The compression supported near component `0` fixes every sufficiently small tube around
component `1`. -/
theorem standardUnlinkAmbientTubeCompression_zero_eqOn_openTube_one
    (d a b c R q : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) (hqR : q ≤ R) :
    Set.EqOn
      (standardUnlinkAmbientTubeCompression 0 d a b c R hd hda hab hbc hcR hRhalf)
      id (standardUnlinkOpenTube 1 q) := by
  intro y hy
  apply standardUnlinkAmbientTubeCompression_eq_self_of_not_mem_closedTube
  intro hy0c
  have hy0R : y ∈ standardUnlinkClosedTube 0 R :=
    standardUnlinkClosedTube_mono 0 hcR.le hy0c
  have hy1R : y ∈ standardUnlinkClosedTube 1 R :=
    standardUnlinkOpenTube_subset_closedTube 1 R
      (standardUnlinkOpenTube_mono 1 hqR hy)
  have hdisj := disjoint_standardUnlinkClosedTube_zero_one hRhalf
  rw [Set.disjoint_left] at hdisj
  exact hdisj hy0R hy1R

/-- The compression supported near component `1` fixes every sufficiently small tube around
component `0`. -/
theorem standardUnlinkAmbientTubeCompression_one_eqOn_openTube_zero
    (d a b c R q : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) (hqR : q ≤ R) :
    Set.EqOn
      (standardUnlinkAmbientTubeCompression 1 d a b c R hd hda hab hbc hcR hRhalf)
      id (standardUnlinkOpenTube 0 q) := by
  intro y hy
  apply standardUnlinkAmbientTubeCompression_eq_self_of_not_mem_closedTube
  intro hy1c
  have hy1R : y ∈ standardUnlinkClosedTube 1 R :=
    standardUnlinkClosedTube_mono 1 hcR.le hy1c
  have hy0R : y ∈ standardUnlinkClosedTube 0 R :=
    standardUnlinkOpenTube_subset_closedTube 0 R
      (standardUnlinkOpenTube_mono 0 hqR hy)
  have hdisj := (disjoint_standardUnlinkClosedTube_zero_one hRhalf).symm
  rw [Set.disjoint_left] at hdisj
  exact hdisj hy1R hy0R

/-- Simultaneously expand both deleted unlink tubes from radius `a` to radius `b`.  The maps are
composed in the displayed order; no commutativity is assumed. -/
def standardUnlinkAmbientCompression (d a b c R : ℝ) (hd : 0 < d) (hda : d < a)
    (hab : a < b) (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) :
    Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4 :=
  (standardUnlinkAmbientTubeCompression 0 d a b c R hd hda hab hbc hcR hRhalf).trans
    (standardUnlinkAmbientTubeCompression 1 d a b c R hd hda hab hbc hcR hRhalf)

/-- The simultaneous compression is the identity on the outer exterior, which is the endpoint
core used in isotopy transport. -/
theorem standardUnlinkAmbientCompression_eqOn_outerExterior
    (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) :
    Set.EqOn (standardUnlinkAmbientCompression d a b c R hd hda hab hbc hcR hRhalf)
      id (coordinateUnlinkExterior R) := by
  intro y hy
  have hy0 : y ∉ standardUnlinkClosedTube 0 c := fun hy0c ↦ hy <|
    Or.inl (standardUnlinkClosedTube_subset_openTube 0 hcR hy0c)
  have hy1 : y ∉ standardUnlinkClosedTube 1 c := fun hy1c ↦ hy <|
    Or.inr (standardUnlinkClosedTube_subset_openTube 1 hcR hy1c)
  change standardUnlinkAmbientTubeCompression 1 d a b c R hd hda hab hbc hcR hRhalf
    (standardUnlinkAmbientTubeCompression 0 d a b c R hd hda hab hbc hcR hRhalf y) = y
  rw [standardUnlinkAmbientTubeCompression_eq_self_of_not_mem_closedTube
      0 d a b c R hd hda hab hbc hcR hRhalf hy0,
    standardUnlinkAmbientTubeCompression_eq_self_of_not_mem_closedTube
      1 d a b c R hd hda hab hbc hcR hRhalf hy1]

/-- Both closed inner tubes, and hence both unlink components, are fixed pointwise. -/
theorem standardUnlinkAmbientCompression_eqOn_innerClosedTubes
    (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) :
    Set.EqOn (standardUnlinkAmbientCompression d a b c R hd hda hab hbc hcR hRhalf)
      id (standardUnlinkClosedTubes d) := by
  intro y hy
  change standardUnlinkAmbientTubeCompression 1 d a b c R hd hda hab hbc hcR hRhalf
    (standardUnlinkAmbientTubeCompression 0 d a b c R hd hda hab hbc hcR hRhalf y) = y
  rcases hy with hy0 | hy1
  · have hy0R : y ∈ standardUnlinkOpenTube 0 R :=
      standardUnlinkClosedTube_subset_openTube 0 (by linarith) hy0
    rw [standardUnlinkAmbientTubeCompression_eq_self_of_mem_closedTube_inner
      0 d a b c R hd hda hab hbc hcR hRhalf hy0]
    exact standardUnlinkAmbientTubeCompression_one_eqOn_openTube_zero
      d a b c R R hd hda hab hbc hcR hRhalf le_rfl hy0R
  · have hy1R : y ∈ standardUnlinkOpenTube 1 R :=
      standardUnlinkClosedTube_subset_openTube 1 (by linarith) hy1
    rw [standardUnlinkAmbientTubeCompression_zero_eqOn_openTube_one
      d a b c R R hd hda hab hbc hcR hRhalf le_rfl hy1R]
    change standardUnlinkAmbientTubeCompression 1 d a b c R hd hda hab hbc hcR hRhalf y = y
    exact standardUnlinkAmbientTubeCompression_eq_self_of_mem_closedTube_inner
      1 d a b c R hd hda hab hbc hcR hRhalf hy1

theorem standardUnlinkAmbientCompression_eqOn_carrier
    (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) :
    Set.EqOn (standardUnlinkAmbientCompression d a b c R hd hda hab hbc hcR hRhalf)
      id standardUnlinkCarrier :=
  (standardUnlinkAmbientCompression_eqOn_innerClosedTubes
    d a b c R hd hda hab hbc hcR hRhalf).mono
      (standardUnlinkCarrier_subset_openTubes hd |>.trans
        (standardUnlinkOpenTubes_subset_closedTubes d))

theorem preimage_standardUnlinkCarrier_standardUnlinkAmbientCompression
    (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) :
    standardUnlinkAmbientCompression d a b c R hd hda hab hbc hcR hRhalf ⁻¹'
        standardUnlinkCarrier =
      standardUnlinkCarrier := by
  ext y
  exact Diffeomorph.mem_iff_of_eqOn _
    (standardUnlinkAmbientCompression_eqOn_carrier
      d a b c R hd hda hab hbc hcR hRhalf) y

theorem standardUnlinkAmbientCompression_mem_openTube_zero_iff
    (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) (y : Sphere 4) :
    standardUnlinkAmbientCompression d a b c R hd hda hab hbc hcR hRhalf y ∈
        standardUnlinkOpenTube 0 b ↔
      y ∈ standardUnlinkOpenTube 0 a := by
  let F₀ := standardUnlinkAmbientTubeCompression 0 d a b c R hd hda hab hbc hcR hRhalf
  let F₁ := standardUnlinkAmbientTubeCompression 1 d a b c R hd hda hab hbc hcR hRhalf
  change F₁ (F₀ y) ∈ standardUnlinkOpenTube 0 b ↔ y ∈ standardUnlinkOpenTube 0 a
  rw [Diffeomorph.mem_iff_of_eqOn F₁
      (standardUnlinkAmbientTubeCompression_one_eqOn_openTube_zero
        d a b c R b hd hda hab hbc hcR hRhalf (by linarith)) (F₀ y),
    standardUnlinkAmbientTubeCompression_mem_openTube_iff]

theorem standardUnlinkAmbientCompression_mem_openTube_one_iff
    (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) (y : Sphere 4) :
    standardUnlinkAmbientCompression d a b c R hd hda hab hbc hcR hRhalf y ∈
        standardUnlinkOpenTube 1 b ↔
      y ∈ standardUnlinkOpenTube 1 a := by
  let F₀ := standardUnlinkAmbientTubeCompression 0 d a b c R hd hda hab hbc hcR hRhalf
  let F₁ := standardUnlinkAmbientTubeCompression 1 d a b c R hd hda hab hbc hcR hRhalf
  change F₁ (F₀ y) ∈ standardUnlinkOpenTube 1 b ↔ y ∈ standardUnlinkOpenTube 1 a
  rw [standardUnlinkAmbientTubeCompression_mem_openTube_iff,
    Diffeomorph.mem_iff_of_eqOn F₀
      (standardUnlinkAmbientTubeCompression_zero_eqOn_openTube_one
        d a b c R a hd hda hab hbc hcR hRhalf (by linarith)) y]

theorem standardUnlinkAmbientCompression_mem_openTubes_iff
    (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) (y : Sphere 4) :
    standardUnlinkAmbientCompression d a b c R hd hda hab hbc hcR hRhalf y ∈
        standardUnlinkOpenTubes b ↔
      y ∈ standardUnlinkOpenTubes a := by
  change (_ ∈ standardUnlinkOpenTube 0 b ∨ _ ∈ standardUnlinkOpenTube 1 b) ↔
    (y ∈ standardUnlinkOpenTube 0 a ∨ y ∈ standardUnlinkOpenTube 1 a)
  rw [standardUnlinkAmbientCompression_mem_openTube_zero_iff,
    standardUnlinkAmbientCompression_mem_openTube_one_iff]

theorem standardUnlinkAmbientCompression_mem_exterior_iff
    (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) (y : Sphere 4) :
    standardUnlinkAmbientCompression d a b c R hd hda hab hbc hcR hRhalf y ∈
        coordinateUnlinkExterior b ↔
      y ∈ coordinateUnlinkExterior a :=
  not_congr (standardUnlinkAmbientCompression_mem_openTubes_iff
    d a b c R hd hda hab hbc hcR hRhalf y)

/-- Exact compact-exterior transport: expanding the deleted tubes sends the radius-`a` exterior
onto the radius-`b` exterior. -/
theorem image_coordinateUnlinkExterior_standardUnlinkAmbientCompression
    (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) :
    standardUnlinkAmbientCompression d a b c R hd hda hab hbc hcR hRhalf ''
        coordinateUnlinkExterior a =
      coordinateUnlinkExterior b := by
  let F := standardUnlinkAmbientCompression d a b c R hd hda hab hbc hcR hRhalf
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (standardUnlinkAmbientCompression_mem_exterior_iff
      d a b c R hd hda hab hbc hcR hRhalf x).2 hx
  · intro hy
    refine ⟨F.symm y, ?_, F.apply_symm_apply y⟩
    have hiff := standardUnlinkAmbientCompression_mem_exterior_iff
      d a b c R hd hda hab hbc hcR hRhalf (F.symm y)
    rw [F.apply_symm_apply] at hiff
    exact hiff.mp hy

/-- The moved-point set lies between the declared inner and outer closed tube unions. -/
theorem movedSet_standardUnlinkAmbientCompression_subset
    (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2) :
    {y | standardUnlinkAmbientCompression d a b c R hd hda hab hbc hcR hRhalf y ≠ y} ⊆
      standardUnlinkClosedTubes c \ standardUnlinkClosedTubes d := by
  intro y hy
  constructor
  · by_contra hyc
    have hy0 : y ∉ standardUnlinkClosedTube 0 c := fun h ↦ hyc (Or.inl h)
    have hy1 : y ∉ standardUnlinkClosedTube 1 c := fun h ↦ hyc (Or.inr h)
    apply hy
    change standardUnlinkAmbientTubeCompression 1 d a b c R hd hda hab hbc hcR hRhalf
      (standardUnlinkAmbientTubeCompression 0 d a b c R hd hda hab hbc hcR hRhalf y) = y
    rw [standardUnlinkAmbientTubeCompression_eq_self_of_not_mem_closedTube
        0 d a b c R hd hda hab hbc hcR hRhalf hy0,
      standardUnlinkAmbientTubeCompression_eq_self_of_not_mem_closedTube
        1 d a b c R hd hda hab hbc hcR hRhalf hy1]
  · intro hyInner
    exact hy (standardUnlinkAmbientCompression_eqOn_innerClosedTubes
      d a b c R hd hda hab hbc hcR hRhalf hyInner)

/-- Endpoint-relative compact-exterior bridge.  An isotopy trace in the larger radius-`a`
exterior is compressed into the smaller radius-`b` exterior, while endpoint images already in
the outer core exterior remain literally unchanged. -/
theorem SmoothSphereIsotopy.exists_standardUnlinkExteriorCompression
    {S₀ S₁ : SmoothSphereEmbedding 3 4} (H : SmoothSphereIsotopy S₀ S₁)
    (d a b c R : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R) (hRhalf : R < 1 / 2)
    (htrace : H.trace ⊆ coordinateUnlinkExterior a)
    (hendpoints : range S₀ ∪ range S₁ ⊆ coordinateUnlinkExterior R) :
    ∃ H' : SmoothSphereIsotopy S₀ S₁,
      (∀ p : I × Sphere 3, H'.toFun p ∉ standardUnlinkCarrier) ∧
        H'.trace ⊆ coordinateUnlinkExterior b := by
  let F := standardUnlinkAmbientCompression d a b c R hd hda hab hbc hcR hRhalf
  have houter := standardUnlinkAmbientCompression_eqOn_outerExterior
    d a b c R hd hda hab hbc hcR hRhalf
  have h₀ : Set.EqOn F id (range S₀) := houter.mono fun _ hx ↦ hendpoints (Or.inl hx)
  have h₁ : Set.EqOn F id (range S₁) := houter.mono fun _ hx ↦ hendpoints (Or.inr hx)
  apply H.exists_endpointRelativeExteriorTransport F h₀ h₁
    (preimage_standardUnlinkCarrier_standardUnlinkAmbientCompression
      d a b c R hd hda hab hbc hcR hRhalf)
    (by linarith) htrace
  rw [image_coordinateUnlinkExterior_standardUnlinkAmbientCompression
    d a b c R hd hda hab hbc hcR hRhalf]

end SplittingSpheres
