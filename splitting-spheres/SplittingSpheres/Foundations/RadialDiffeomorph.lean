/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothRadialCompression
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Radial diffeomorphisms from scalar diffeomorphisms

This file turns a diffeomorphism of the real radius coordinate into a diffeomorphism of a real
inner-product space.  Requiring the scalar map to be literally the identity on a neighborhood of
zero avoids any differentiability issue for the norm at the center.
-/

@[expose] public section

open Function Metric Set
open TopologicalSpace
open scoped ContDiff Manifold Topology

noncomputable section

namespace SplittingSpheres

universe uE

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Restrict an ambient diffeomorphism to an invariant open submanifold.  Forward and inverse
invariance are kept explicit, which avoids hiding a set-theoretic surjectivity obligation. -/
def restrictOpenDiffeomorph (U : Opens E) (e : E ≃ₘ[ℝ] E)
    (hforward : ∀ x : E, x ∈ U → e x ∈ U)
    (hinverse : ∀ x : E, x ∈ U → e.symm x ∈ U) :
    U ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ U where
  toFun x := ⟨e x.1, hforward x.1 x.2⟩
  invFun x := ⟨e.symm x.1, hinverse x.1 x.2⟩
  left_inv x := by ext; exact e.symm_apply_apply x.1
  right_inv x := by ext; exact e.apply_symm_apply x.1
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact e.contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact e.symm.contMDiff.comp contMDiff_subtype_val

@[simp]
theorem restrictOpenDiffeomorph_apply_coe (U : Opens E) (e : E ≃ₘ[ℝ] E)
    (hforward : ∀ x : E, x ∈ U → e x ∈ U)
    (hinverse : ∀ x : E, x ∈ U → e.symm x ∈ U) (x : U) :
    (restrictOpenDiffeomorph U e hforward hinverse x : E) = e x.1 := rfl

/-- Apply a scalar radius map about the center `c`, preserving every ray. -/
def centeredRadialMap (ρ : ℝ → ℝ) (c x : E) : E :=
  by
    classical
    exact if hx : x = c then c else c + (ρ ‖x - c‖ / ‖x - c‖) • (x - c)

@[simp]
theorem centeredRadialMap_center (ρ : ℝ → ℝ) (c : E) : centeredRadialMap ρ c c = c := by
  simp [centeredRadialMap]

theorem centeredRadialMap_of_ne (ρ : ℝ → ℝ) (c : E) {x : E} (hx : x ≠ c) :
    centeredRadialMap ρ c x = c + (ρ ‖x - c‖ / ‖x - c‖) • (x - c) := by
  simp [centeredRadialMap, hx]

theorem centeredRadialMap_eq_self_of_radius_eq (ρ : ℝ → ℝ) (c : E) {x : E}
    (hρ : ρ ‖x - c‖ = ‖x - c‖) : centeredRadialMap ρ c x = x := by
  by_cases hx : x = c
  · simp [hx]
  · rw [centeredRadialMap_of_ne ρ c hx, hρ, div_self (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))]
    simp

theorem centeredRadialMap_sub_center (ρ : ℝ → ℝ) (c : E) {x : E} (hx : x ≠ c) :
    centeredRadialMap ρ c x - c = (ρ ‖x - c‖ / ‖x - c‖) • (x - c) := by
  rw [centeredRadialMap_of_ne ρ c hx, add_sub_cancel_left]

theorem norm_centeredRadialMap_sub_center (ρ : ℝ → ℝ) (c : E) {x : E} (hx : x ≠ c)
    (hρ : 0 < ρ ‖x - c‖) :
    ‖centeredRadialMap ρ c x - c‖ = ρ ‖x - c‖ := by
  rw [centeredRadialMap_sub_center ρ c hx, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hρ (norm_pos_iff.mpr (sub_ne_zero.mpr hx)))]
  exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))

theorem centeredRadialMap_symm_apply (e : ℝ ≃ ℝ) (c : E)
    (hpos : ∀ r : ℝ, 0 < r → 0 < e r) (x : E) :
    centeredRadialMap e.symm c (centeredRadialMap e c x) = x := by
  by_cases hx : x = c
  · simp [hx]
  · have hr : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
    have hepos : 0 < e ‖x - c‖ := hpos _ hr
    have hnorm : ‖centeredRadialMap e c x - c‖ = e ‖x - c‖ :=
      norm_centeredRadialMap_sub_center e c hx hepos
    have hne : centeredRadialMap e c x ≠ c := by
      intro h
      rw [h, sub_self, norm_zero] at hnorm
      linarith
    rw [centeredRadialMap_of_ne e.symm c hne, hnorm, e.symm_apply_apply,
      centeredRadialMap_sub_center e c hx, smul_smul]
    have hrne : ‖x - c‖ ≠ 0 := hr.ne'
    have hene : e ‖x - c‖ ≠ 0 := hepos.ne'
    field_simp
    simp

theorem centeredRadialMap_apply_symm (e : ℝ ≃ ℝ) (c : E)
    (hposSymm : ∀ r : ℝ, 0 < r → 0 < e.symm r) (x : E) :
    centeredRadialMap e c (centeredRadialMap e.symm c x) = x := by
  simpa only [e.symm_symm] using centeredRadialMap_symm_apply e.symm c hposSymm x

/-- The ray-preserving equivalence induced by a scalar equivalence preserving positive radii. -/
def centeredRadialEquiv (e : ℝ ≃ ℝ) (c : E)
    (hpos : ∀ r : ℝ, 0 < r → 0 < e r)
    (hposSymm : ∀ r : ℝ, 0 < r → 0 < e.symm r) : E ≃ E where
  toFun := centeredRadialMap e c
  invFun := centeredRadialMap e.symm c
  left_inv := centeredRadialMap_symm_apply e c hpos
  right_inv := centeredRadialMap_apply_symm e c hposSymm

@[simp]
theorem centeredRadialEquiv_apply (e : ℝ ≃ ℝ) (c : E)
    (hpos : ∀ r : ℝ, 0 < r → 0 < e r)
    (hposSymm : ∀ r : ℝ, 0 < r → 0 < e.symm r) (x : E) :
    centeredRadialEquiv e c hpos hposSymm x = centeredRadialMap e c x := rfl

/-- Smoothness of a radialized scalar diffeomorphism which is the identity near radius zero. -/
theorem contDiff_centeredRadialMap (e : ℝ ≃ₘ[ℝ] ℝ) (c : E) {d : ℝ} (hd : 0 < d)
    (hnear : ∀ r : ℝ, r ≤ d → e r = r) :
    ContDiff ℝ ∞ (centeredRadialMap e c) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = c
  · subst x
    apply contDiffAt_id.congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hd)] with y hy
    apply centeredRadialMap_eq_self_of_radius_eq
    apply hnear
    have hyr : ‖y - c‖ < d := by simpa only [mem_ball, dist_eq_norm] using hy
    exact hyr.le
  · have hsub : ContDiffAt ℝ ∞ (fun y : E ↦ y - c) x :=
      contDiffAt_id.sub contDiffAt_const
    have hnorm : ContDiffAt ℝ ∞ (fun y : E ↦ ‖y - c‖) x :=
      hsub.norm ℝ (sub_ne_zero.mpr hx)
    have he : ContDiffAt ℝ ∞ (fun y : E ↦ e ‖y - c‖) x :=
      e.contDiff.comp_contDiffAt x hnorm
    have hcoef : ContDiffAt ℝ ∞ (fun y : E ↦ e ‖y - c‖ / ‖y - c‖) x :=
      he.div hnorm (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))
    have hsmooth : ContDiffAt ℝ ∞
        (fun y : E ↦ c + (e ‖y - c‖ / ‖y - c‖) • (y - c)) x :=
      contDiffAt_const.add (hcoef.smul hsub)
    apply hsmooth.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact centeredRadialMap_of_ne e c hy

/-- A scalar diffeomorphism preserving positive radii and fixed near zero radializes to a smooth
diffeomorphism of any real inner-product space. -/
def centeredRadialDiffeomorph (e : ℝ ≃ₘ[ℝ] ℝ) (c : E)
    (hpos : ∀ r : ℝ, 0 < r → 0 < e r)
    (hposSymm : ∀ r : ℝ, 0 < r → 0 < e.symm r)
    {d d' : ℝ} (hd : 0 < d) (hd' : 0 < d')
    (hnear : ∀ r : ℝ, r ≤ d → e r = r)
    (hnearSymm : ∀ r : ℝ, r ≤ d' → e.symm r = r) : E ≃ₘ[ℝ] E where
  toEquiv := centeredRadialEquiv e.toEquiv c hpos hposSymm
  contMDiff_toFun := (contDiff_centeredRadialMap e c hd hnear).contMDiff
  contMDiff_invFun := (contDiff_centeredRadialMap e.symm c hd' hnearSymm).contMDiff

@[simp]
theorem centeredRadialDiffeomorph_apply (e : ℝ ≃ₘ[ℝ] ℝ) (c : E)
    (hpos : ∀ r : ℝ, 0 < r → 0 < e r)
    (hposSymm : ∀ r : ℝ, 0 < r → 0 < e.symm r)
    {d d' : ℝ} (hd : 0 < d) (hd' : 0 < d')
    (hnear : ∀ r : ℝ, r ≤ d → e r = r)
    (hnearSymm : ∀ r : ℝ, r ≤ d' → e.symm r = r) (x : E) :
    centeredRadialDiffeomorph e c hpos hposSymm hd hd' hnear hnearSymm x =
      centeredRadialMap e c x :=
  rfl

theorem norm_centeredRadialDiffeomorph_sub_center (e : ℝ ≃ₘ[ℝ] ℝ) (c : E)
    (hpos : ∀ r : ℝ, 0 < r → 0 < e r)
    (hposSymm : ∀ r : ℝ, 0 < r → 0 < e.symm r)
    {d d' : ℝ} (hd : 0 < d) (hd' : 0 < d')
    (hnear : ∀ r : ℝ, r ≤ d → e r = r)
    (hnearSymm : ∀ r : ℝ, r ≤ d' → e.symm r = r) (x : E) :
    ‖centeredRadialDiffeomorph e c hpos hposSymm hd hd' hnear hnearSymm x - c‖ = e ‖x - c‖ := by
  by_cases hx : x = c
  · subst x
    simp [hnear 0 (le_of_lt hd)]
  · exact norm_centeredRadialMap_sub_center e c hx (hpos _ (norm_pos_iff.mpr (sub_ne_zero.mpr hx)))

theorem centeredRadialDiffeomorph_eq_self_of_radius_eq (e : ℝ ≃ₘ[ℝ] ℝ) (c : E)
    (hpos : ∀ r : ℝ, 0 < r → 0 < e r)
    (hposSymm : ∀ r : ℝ, 0 < r → 0 < e.symm r)
    {d d' : ℝ} (hd : 0 < d) (hd' : 0 < d')
    (hnear : ∀ r : ℝ, r ≤ d → e r = r)
    (hnearSymm : ∀ r : ℝ, r ≤ d' → e.symm r = r) {x : E}
    (hr : e ‖x - c‖ = ‖x - c‖) :
    centeredRadialDiffeomorph e c hpos hposSymm hd hd' hnear hnearSymm x = x :=
  centeredRadialMap_eq_self_of_radius_eq e c hr

theorem centeredRadialDiffeomorph_eq_self_of_le (e : ℝ ≃ₘ[ℝ] ℝ) (c : E)
    (hpos : ∀ r : ℝ, 0 < r → 0 < e r)
    (hposSymm : ∀ r : ℝ, 0 < r → 0 < e.symm r)
    {d d' : ℝ} (hd : 0 < d) (hd' : 0 < d')
    (hnear : ∀ r : ℝ, r ≤ d → e r = r)
    (hnearSymm : ∀ r : ℝ, r ≤ d' → e.symm r = r)
    {R : ℝ} (hfar : ∀ r : ℝ, R ≤ r → e r = r) {x : E}
    (hx : R ≤ ‖x - c‖) :
    centeredRadialDiffeomorph e c hpos hposSymm hd hd' hnear hnearSymm x = x :=
  centeredRadialDiffeomorph_eq_self_of_radius_eq e c hpos hposSymm hd hd' hnear hnearSymm
    (hfar _ hx)

/-- Exact radial monotonicity converts a lower bound before compression into a lower bound after
compression. -/
theorem le_norm_centeredRadialDiffeomorph_sub_center (e : ℝ ≃ₘ[ℝ] ℝ) (c : E)
    (hpos : ∀ r : ℝ, 0 < r → 0 < e r)
    (hposSymm : ∀ r : ℝ, 0 < r → 0 < e.symm r)
    {d d' : ℝ} (hd : 0 < d) (hd' : 0 < d')
    (hnear : ∀ r : ℝ, r ≤ d → e r = r)
    (hnearSymm : ∀ r : ℝ, r ≤ d' → e.symm r = r)
    (hmono : Monotone e) {a b : ℝ} (hab : e a = b) {x : E}
    (hx : a ≤ ‖x - c‖) :
    b ≤ ‖centeredRadialDiffeomorph e c hpos hposSymm hd hd' hnear hnearSymm x - c‖ := by
  rw [norm_centeredRadialDiffeomorph_sub_center e c hpos hposSymm hd hd' hnear hnearSymm, ← hab]
  exact hmono hx

theorem centeredRadialDiffeomorph_mem_ball_iff (e : ℝ ≃ₘ[ℝ] ℝ) (c : E)
    (hpos : ∀ r : ℝ, 0 < r → 0 < e r)
    (hposSymm : ∀ r : ℝ, 0 < r → 0 < e.symm r)
    {d d' : ℝ} (hd : 0 < d) (hd' : 0 < d')
    (hnear : ∀ r : ℝ, r ≤ d → e r = r)
    (hnearSymm : ∀ r : ℝ, r ≤ d' → e.symm r = r)
    (hstrict : StrictMono e) {a b : ℝ} (hab : e a = b) (x : E) :
    centeredRadialDiffeomorph e c hpos hposSymm hd hd' hnear hnearSymm x ∈ ball c b ↔
      x ∈ ball c a := by
  rw [mem_ball, dist_eq_norm, norm_centeredRadialDiffeomorph_sub_center e c hpos hposSymm hd hd'
    hnear hnearSymm, ← hab, hstrict.lt_iff_lt, mem_ball, dist_eq_norm]

theorem centeredRadialDiffeomorph_mem_closedBall_iff (e : ℝ ≃ₘ[ℝ] ℝ) (c : E)
    (hpos : ∀ r : ℝ, 0 < r → 0 < e r)
    (hposSymm : ∀ r : ℝ, 0 < r → 0 < e.symm r)
    {d d' : ℝ} (hd : 0 < d) (hd' : 0 < d')
    (hnear : ∀ r : ℝ, r ≤ d → e r = r)
    (hnearSymm : ∀ r : ℝ, r ≤ d' → e.symm r = r)
    (hstrict : StrictMono e) {a b : ℝ} (hab : e a = b) (x : E) :
    centeredRadialDiffeomorph e c hpos hposSymm hd hd' hnear hnearSymm x ∈ closedBall c b ↔
      x ∈ closedBall c a := by
  rw [mem_closedBall, dist_eq_norm,
    norm_centeredRadialDiffeomorph_sub_center e c hpos hposSymm hd hd' hnear hnearSymm,
    ← hab, hstrict.le_iff_le, mem_closedBall, dist_eq_norm]

/-- An open metric ball, bundled as an open submanifold. -/
def radialOpenBall (c : E) (R : ℝ) : Opens E := ⟨ball c R, isOpen_ball⟩

/-- Restriction of a radial diffeomorphism to a ball whose radius it fixes. -/
def radialOpenBallDiffeomorph (e : ℝ ≃ₘ[ℝ] ℝ) (c : E)
    (hpos : ∀ r : ℝ, 0 < r → 0 < e r)
    (hposSymm : ∀ r : ℝ, 0 < r → 0 < e.symm r)
    {d d' : ℝ} (hd : 0 < d) (hd' : 0 < d')
    (hnear : ∀ r : ℝ, r ≤ d → e r = r)
    (hnearSymm : ∀ r : ℝ, r ≤ d' → e.symm r = r)
    (hstrict : StrictMono e) {R : ℝ} (hR : e R = R) :
    radialOpenBall c R ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ radialOpenBall c R := by
  let F := centeredRadialDiffeomorph e c hpos hposSymm hd hd' hnear hnearSymm
  apply restrictOpenDiffeomorph (radialOpenBall c R) F
  · intro x hx
    exact (centeredRadialDiffeomorph_mem_ball_iff e c hpos hposSymm hd hd' hnear hnearSymm hstrict
      hR x).2 hx
  · intro x hx
    have hiff := centeredRadialDiffeomorph_mem_ball_iff e c hpos hposSymm hd hd' hnear hnearSymm
      hstrict hR (F.symm x)
    rw [F.apply_symm_apply] at hiff
    exact hiff.mp hx

@[simp]
theorem radialOpenBallDiffeomorph_apply_coe (e : ℝ ≃ₘ[ℝ] ℝ) (c : E)
    (hpos : ∀ r : ℝ, 0 < r → 0 < e r)
    (hposSymm : ∀ r : ℝ, 0 < r → 0 < e.symm r)
    {d d' : ℝ} (hd : 0 < d) (hd' : 0 < d')
    (hnear : ∀ r : ℝ, r ≤ d → e r = r)
    (hnearSymm : ∀ r : ℝ, r ≤ d' → e.symm r = r)
    (hstrict : StrictMono e) {R : ℝ} (hR : e R = R) (x : radialOpenBall c R) :
    (radialOpenBallDiffeomorph e c hpos hposSymm hd hd' hnear hnearSymm hstrict hR x : E) =
      centeredRadialDiffeomorph e c hpos hposSymm hd hd' hnear hnearSymm x.1 := rfl

/-! ## Centered annular compression -/

theorem annularScalarCompression_symm_pos_of_pos (d a b c : ℝ) (hd : 0 < d)
    (hda : d < a) (hab : a < b) (hbc : b < c) {r : ℝ} (hr : 0 < r) :
    0 < (annularScalarCompression d a b c hda hab hbc).symm r := by
  let e := annularScalarCompression d a b c hda hab hbc
  have hzero : e 0 = 0 := annularScalarCompression_zero d a b c hd hda hab hbc
  have hmono : StrictMono e := annularScalarCompression_strictMono d a b c hda hab hbc
  by_contra h
  have hle := hmono.monotone (le_of_not_gt h)
  rw [Diffeomorph.apply_symm_apply, hzero] at hle
  exact (not_lt_of_ge hle) hr

theorem annularScalarCompression_symm_eq_self_of_le_left (d a b c : ℝ)
    (hda : d < a) (hab : a < b) (hbc : b < c) {r : ℝ} (hr : r ≤ d) :
    (annularScalarCompression d a b c hda hab hbc).symm r = r := by
  let e := annularScalarCompression d a b c hda hab hbc
  calc
    e.symm r = e.symm (e r) := congrArg e.symm
      (annularScalarCompression_eq_self_of_le_left d a b c hda hab hbc hr).symm
    _ = r := Diffeomorph.symm_apply_apply e r

/-- Annular scalar compression about an arbitrary center. -/
def centeredAnnularRadialCompression (center : E) (d a b c : ℝ) (hd : 0 < d)
    (hda : d < a) (hab : a < b) (hbc : b < c) : E ≃ₘ[ℝ] E :=
  centeredRadialDiffeomorph (annularScalarCompression d a b c hda hab hbc) center
    (fun _ hr ↦ annularScalarCompression_pos_of_pos d a b c hd hda hab hbc hr)
    (fun _ hr ↦ annularScalarCompression_symm_pos_of_pos d a b c hd hda hab hbc hr)
    hd hd
    (fun _ hr ↦ annularScalarCompression_eq_self_of_le_left d a b c hda hab hbc hr)
    (fun _ hr ↦ annularScalarCompression_symm_eq_self_of_le_left d a b c hda hab hbc hr)

theorem norm_centeredAnnularRadialCompression_sub_center (center : E) (d a b c : ℝ)
    (hd : 0 < d) (hda : d < a) (hab : a < b) (hbc : b < c) (x : E) :
    ‖centeredAnnularRadialCompression center d a b c hd hda hab hbc x - center‖ =
      annularScalarCompression d a b c hda hab hbc ‖x - center‖ :=
  norm_centeredRadialDiffeomorph_sub_center _ center _ _ hd hd _ _ x

theorem centeredAnnularRadialCompression_mem_ball_iff (center : E) (d a b c : ℝ)
    (hd : 0 < d) (hda : d < a) (hab : a < b) (hbc : b < c) (x : E) :
    centeredAnnularRadialCompression center d a b c hd hda hab hbc x ∈ ball center b ↔
      x ∈ ball center a :=
  centeredRadialDiffeomorph_mem_ball_iff _ center _ _ hd hd _ _
    (annularScalarCompression_strictMono d a b c hda hab hbc)
    (annularScalarCompression_apply_a d a b c hda hab hbc) x

theorem centeredAnnularRadialCompression_eq_self_of_le_norm (center : E) (d a b c : ℝ)
    (hd : 0 < d) (hda : d < a) (hab : a < b) (hbc : b < c) {x : E}
    (hx : c ≤ ‖x - center‖) :
    centeredAnnularRadialCompression center d a b c hd hda hab hbc x = x :=
  centeredRadialDiffeomorph_eq_self_of_le _ center _ _ hd hd _ _
    (fun _ hr ↦ annularScalarCompression_eq_self_of_le_right d a b c hda hab hbc hr) hx

/-- The centered annular compression restricted to an outer open ball which contains its support. -/
def centeredAnnularRadialOpenBallCompression (center : E) (d a b c R : ℝ) (hd : 0 < d)
    (hda : d < a) (hab : a < b) (hbc : b < c) (hcR : c ≤ R) :
    radialOpenBall center R ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ radialOpenBall center R :=
  radialOpenBallDiffeomorph (annularScalarCompression d a b c hda hab hbc) center
    (fun _ hr ↦ annularScalarCompression_pos_of_pos d a b c hd hda hab hbc hr)
    (fun _ hr ↦ annularScalarCompression_symm_pos_of_pos d a b c hd hda hab hbc hr)
    hd hd
    (fun _ hr ↦ annularScalarCompression_eq_self_of_le_left d a b c hda hab hbc hr)
    (fun _ hr ↦ annularScalarCompression_symm_eq_self_of_le_left d a b c hda hab hbc hr)
    (annularScalarCompression_strictMono d a b c hda hab hbc)
    (annularScalarCompression_eq_self_of_le_right d a b c hda hab hbc hcR)

end SplittingSpheres
