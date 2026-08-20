/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Compactly supported smooth compression of the real line

The basic building block is an upward smooth step

`x ↦ x + δ * smoothTransition ((x - L) / w)`.

For `0 < w` and `0 ≤ δ`, this is a smooth, strictly increasing diffeomorphism.  It is the
identity on `(-∞, L]` and translation by `δ` on `[L + w, ∞)`.  Composing one such step with
the inverse of a later step cancels the translation at infinity.  This gives, for
`0 < a < b < c`, an orientation-preserving smooth diffeomorphism of `ℝ` which sends `a` to `b`
and is the identity outside `(0, c)`.
-/

@[expose] public section

open Function Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace SplittingSpheres

/-- A smooth transition from the identity to translation by `δ` across `[L, L + w]`. -/
def smoothUpStep (L w δ x : ℝ) : ℝ :=
  x + δ * Real.smoothTransition ((x - L) / w)

theorem smoothUpStep_contDiff {L w δ : ℝ} :
    ContDiff ℝ ∞ (smoothUpStep L w δ) := by
  unfold smoothUpStep
  exact contDiff_id.add <| contDiff_const.mul <|
    Real.smoothTransition.contDiff.comp <| (contDiff_id.sub contDiff_const).div_const w

theorem smoothUpStep_eq_self_of_le {L w δ x : ℝ} (hw : 0 < w) (hx : x ≤ L) :
    smoothUpStep L w δ x = x := by
  rw [smoothUpStep, Real.smoothTransition.zero_of_nonpos]
  · ring
  · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hw.le

theorem smoothUpStep_eq_add_of_le {L w δ x : ℝ} (hw : 0 < w) (hx : L + w ≤ x) :
    smoothUpStep L w δ x = x + δ := by
  rw [smoothUpStep, Real.smoothTransition.one_of_one_le]
  · ring
  · exact (le_div_iff₀ hw).mpr (by linarith)

theorem smoothUpStep_strictMono {L w δ : ℝ} (hw : 0 < w) (hδ : 0 ≤ δ) :
    StrictMono (smoothUpStep L w δ) := by
  intro x y hxy
  apply add_lt_add_of_lt_of_le hxy
  apply mul_le_mul_of_nonneg_left _ hδ
  apply Real.smoothTransition.monotone
  exact (div_le_div_iff_of_pos_right hw).mpr (sub_le_sub_right hxy.le L)

theorem smoothUpStep_surjective {L w δ : ℝ} (hw : 0 < w) :
    Surjective (smoothUpStep L w δ) := by
  intro y
  by_cases hy : y ≤ L
  · exact ⟨y, smoothUpStep_eq_self_of_le hw hy⟩
  by_cases hy' : L + w + δ ≤ y
  · refine ⟨y - δ, ?_⟩
    rw [smoothUpStep_eq_add_of_le hw (by linarith)]
    ring
  · have hwle : L ≤ L + w := by linarith
    have hy_mem : y ∈ Icc (smoothUpStep L w δ L) (smoothUpStep L w δ (L + w)) := by
      rw [smoothUpStep_eq_self_of_le hw le_rfl,
        smoothUpStep_eq_add_of_le hw le_rfl]
      exact ⟨(not_le.mp hy).le, le_of_not_ge hy'⟩
    rcases intermediate_value_Icc hwle smoothUpStep_contDiff.continuous.continuousOn hy_mem with
      ⟨x, -, hx⟩
    exact ⟨x, hx⟩

/-- The upward smooth step as an order isomorphism. -/
def smoothUpStepOrderIso (L w δ : ℝ) (hw : 0 < w) (hδ : 0 ≤ δ) : ℝ ≃o ℝ :=
  (smoothUpStep_strictMono (L := L) hw hδ).orderIsoOfSurjective _
    (smoothUpStep_surjective (L := L) (δ := δ) hw)

@[simp]
theorem smoothUpStepOrderIso_apply (L w δ : ℝ) (hw : 0 < w) (hδ : 0 ≤ δ) (x : ℝ) :
    smoothUpStepOrderIso L w δ hw hδ x = smoothUpStep L w δ x :=
  congr_fun (StrictMono.coe_orderIsoOfSurjective _
    (smoothUpStep_strictMono (L := L) hw hδ)
    (smoothUpStep_surjective (L := L) (δ := δ) hw)) x

/-- The derivative of an upward step is positive.  This is the orientation-preserving property
in one dimension and is also what makes the inverse smooth. -/
theorem smoothUpStep_hasDerivAt {L w δ : ℝ} (x : ℝ) :
    HasDerivAt (smoothUpStep L w δ)
      (1 + δ * deriv Real.smoothTransition ((x - L) / w) / w) x := by
  have hS : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((x - L) / w)) ((x - L) / w) :=
    ((Real.smoothTransition.contDiffAt (n := (⊤ : ℕ∞))).differentiableAt (by simp)).hasDerivAt
  have hi : HasDerivAt (fun y : ℝ ↦ (y - L) / w) (1 / w) x := by
    simpa only [id_eq] using ((hasDerivAt_id x).sub_const L).div_const w
  have hc := hS.comp x hi
  have hm := hc.const_mul δ
  have ha := (hasDerivAt_id x).add hm
  change HasDerivAt
    (id + fun y ↦ δ * (Real.smoothTransition ∘ fun z : ℝ ↦ (z - L) / w) y)
    (1 + δ * deriv Real.smoothTransition ((x - L) / w) / w) x
  simpa only [div_eq_mul_inv, one_mul, mul_assoc] using ha

theorem smoothUpStep_deriv_pos {L w δ : ℝ} (hw : 0 < w) (hδ : 0 ≤ δ) (x : ℝ) :
    0 < 1 + δ * deriv Real.smoothTransition ((x - L) / w) / w := by
  have hS : 0 ≤ deriv Real.smoothTransition ((x - L) / w) :=
    Real.smoothTransition.monotone.deriv_nonneg
  have : 0 ≤ δ * deriv Real.smoothTransition ((x - L) / w) / w :=
    div_nonneg (mul_nonneg hδ hS) hw.le
  linarith

/-- An upward smooth step bundled as an orientation-preserving smooth diffeomorphism of `ℝ`. -/
def smoothUpStepDiffeomorph (L w δ : ℝ) (hw : 0 < w) (hδ : 0 ≤ δ) : ℝ ≃ₘ[ℝ] ℝ where
  toEquiv := (smoothUpStepOrderIso L w δ hw hδ).toEquiv
  contMDiff_toFun := by
    apply ContDiff.contMDiff
    have hcoe : (⇑(smoothUpStepOrderIso L w δ hw hδ).toEquiv : ℝ → ℝ) =
        smoothUpStep L w δ :=
      (OrderIso.coe_toEquiv _).trans <| StrictMono.coe_orderIsoOfSurjective _
          (smoothUpStep_strictMono (L := L) hw hδ)
          (smoothUpStep_surjective (L := L) (δ := δ) hw)
    rw [hcoe]
    exact smoothUpStep_contDiff
  contMDiff_invFun := by
    apply ContDiff.contMDiff
    let e := smoothUpStepOrderIso L w δ hw hδ
    have hcoe : (⇑e.toHomeomorph : ℝ → ℝ) = smoothUpStep L w δ := by
      rw [OrderIso.coe_toHomeomorph]
      exact StrictMono.coe_orderIsoOfSurjective _
        (smoothUpStep_strictMono (L := L) hw hδ)
        (smoothUpStep_surjective (L := L) (δ := δ) hw)
    apply e.toHomeomorph.contDiff_symm_deriv
      (fun x ↦ (smoothUpStep_deriv_pos (L := L) hw hδ x).ne')
    · intro x
      rw [hcoe]
      exact smoothUpStep_hasDerivAt (L := L) (w := w) (δ := δ) x
    · rw [hcoe]
      exact smoothUpStep_contDiff

@[simp]
theorem smoothUpStepDiffeomorph_apply (L w δ : ℝ) (hw : 0 < w) (hδ : 0 ≤ δ) (x : ℝ) :
    smoothUpStepDiffeomorph L w δ hw hδ x = smoothUpStep L w δ x :=
  smoothUpStepOrderIso_apply L w δ hw hδ x

/-- A compactly supported scalar compression.  The first smooth step moves `a` to `b`; the
inverse of the second step cancels that translation by the time one reaches `c`. -/
def scalarCompression (a b c : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) : ℝ ≃ₘ[ℝ] ℝ :=
  (smoothUpStepDiffeomorph 0 a (b - a) ha (sub_nonneg.mpr hab.le)).trans
    (smoothUpStepDiffeomorph b (c - b) (b - a) (sub_pos.mpr hbc)
      (sub_nonneg.mpr hab.le)).symm

@[simp]
theorem scalarCompression_apply (a b c : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (x : ℝ) :
    scalarCompression a b c ha hab hbc x =
      (smoothUpStepDiffeomorph b (c - b) (b - a) (sub_pos.mpr hbc)
        (sub_nonneg.mpr hab.le)).symm (smoothUpStep 0 a (b - a) x) :=
by
  change (smoothUpStepDiffeomorph b (c - b) (b - a) (sub_pos.mpr hbc)
    (sub_nonneg.mpr hab.le)).symm
      (smoothUpStepDiffeomorph 0 a (b - a) ha (sub_nonneg.mpr hab.le) x) = _
  rw [smoothUpStepDiffeomorph_apply]

theorem scalarCompression_apply_a (a b c : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    scalarCompression a b c ha hab hbc a = b := by
  rw [scalarCompression_apply, smoothUpStep_eq_add_of_le ha (by simp)]
  rw [show a + (b - a) = b by ring]
  simpa only [smoothUpStepDiffeomorph_apply,
    smoothUpStep_eq_self_of_le (sub_pos.mpr hbc) le_rfl] using
      Diffeomorph.symm_apply_apply
        (smoothUpStepDiffeomorph b (c - b) (b - a) (sub_pos.mpr hbc)
          (sub_nonneg.mpr hab.le)) b

theorem scalarCompression_eq_self_of_nonpos (a b c : ℝ) (ha : 0 < a) (hab : a < b)
    (hbc : b < c) {x : ℝ} (hx : x ≤ 0) : scalarCompression a b c ha hab hbc x = x := by
  rw [scalarCompression_apply, smoothUpStep_eq_self_of_le ha hx]
  let d := smoothUpStepDiffeomorph b (c - b) (b - a) (sub_pos.mpr hbc)
    (sub_nonneg.mpr hab.le)
  have hd : d x = x := by
    rw [show d x = smoothUpStep b (c - b) (b - a) x by
      exact smoothUpStepDiffeomorph_apply _ _ _ _ _ _]
    exact smoothUpStep_eq_self_of_le (sub_pos.mpr hbc) (by linarith)
  calc
    d.symm x = d.symm (d x) := congrArg d.symm hd.symm
    _ = x := Diffeomorph.symm_apply_apply d x

theorem scalarCompression_eq_self_of_le (a b c : ℝ) (ha : 0 < a) (hab : a < b)
    (hbc : b < c) {x : ℝ} (hx : c ≤ x) : scalarCompression a b c ha hab hbc x = x := by
  rw [scalarCompression_apply, smoothUpStep_eq_add_of_le ha (by linarith)]
  let d := smoothUpStepDiffeomorph b (c - b) (b - a) (sub_pos.mpr hbc)
    (sub_nonneg.mpr hab.le)
  have hd : d x = x + (b - a) := by
    rw [show d x = smoothUpStep b (c - b) (b - a) x by
      exact smoothUpStepDiffeomorph_apply _ _ _ _ _ _]
    exact smoothUpStep_eq_add_of_le (sub_pos.mpr hbc) (by linarith)
  calc
    d.symm (x + (b - a)) = d.symm (d x) := congrArg d.symm hd.symm
    _ = x := Diffeomorph.symm_apply_apply d x

theorem scalarCompression_displacement_support_subset (a b c : ℝ) (ha : 0 < a) (hab : a < b)
    (hbc : b < c) :
    Function.support (fun x ↦ scalarCompression a b c ha hab hbc x - x) ⊆ Ioo 0 c := by
  intro x hx
  change scalarCompression a b c ha hab hbc x - x ≠ 0 at hx
  constructor
  · exact lt_of_not_ge fun h ↦ hx (by
      rw [scalarCompression_eq_self_of_nonpos a b c ha hab hbc h, sub_self])
  · exact lt_of_not_ge fun h ↦ hx (by
      rw [scalarCompression_eq_self_of_le a b c ha hab hbc h, sub_self])

/-! ## Annular version -/

/-- The annular scalar compression.  Its first transition occurs over `[d, a]`, so it is
literally the identity on a neighborhood of the origin when `0 < d`. -/
def annularScalarCompression (d a b c : ℝ) (hda : d < a) (hab : a < b) (hbc : b < c) :
    ℝ ≃ₘ[ℝ] ℝ :=
  (smoothUpStepDiffeomorph d (a - d) (b - a) (sub_pos.mpr hda)
      (sub_nonneg.mpr hab.le)).trans
    (smoothUpStepDiffeomorph b (c - b) (b - a) (sub_pos.mpr hbc)
      (sub_nonneg.mpr hab.le)).symm

@[simp]
theorem annularScalarCompression_apply (d a b c : ℝ) (hda : d < a) (hab : a < b)
    (hbc : b < c) (x : ℝ) :
    annularScalarCompression d a b c hda hab hbc x =
      (smoothUpStepDiffeomorph b (c - b) (b - a) (sub_pos.mpr hbc)
        (sub_nonneg.mpr hab.le)).symm (smoothUpStep d (a - d) (b - a) x) := by
  change (smoothUpStepDiffeomorph b (c - b) (b - a) (sub_pos.mpr hbc)
    (sub_nonneg.mpr hab.le)).symm
      (smoothUpStepDiffeomorph d (a - d) (b - a) (sub_pos.mpr hda)
        (sub_nonneg.mpr hab.le) x) = _
  rw [smoothUpStepDiffeomorph_apply]

theorem annularScalarCompression_apply_a (d a b c : ℝ) (hda : d < a) (hab : a < b)
    (hbc : b < c) : annularScalarCompression d a b c hda hab hbc a = b := by
  rw [annularScalarCompression_apply,
    smoothUpStep_eq_add_of_le (sub_pos.mpr hda) (by linarith)]
  rw [show a + (b - a) = b by ring]
  simpa only [smoothUpStepDiffeomorph_apply,
    smoothUpStep_eq_self_of_le (sub_pos.mpr hbc) le_rfl] using
      Diffeomorph.symm_apply_apply
        (smoothUpStepDiffeomorph b (c - b) (b - a) (sub_pos.mpr hbc)
          (sub_nonneg.mpr hab.le)) b

theorem annularScalarCompression_eq_self_of_le_left (d a b c : ℝ) (hda : d < a)
    (hab : a < b) (hbc : b < c) {x : ℝ} (hx : x ≤ d) :
    annularScalarCompression d a b c hda hab hbc x = x := by
  rw [annularScalarCompression_apply,
    smoothUpStep_eq_self_of_le (sub_pos.mpr hda) hx]
  let e := smoothUpStepDiffeomorph b (c - b) (b - a) (sub_pos.mpr hbc)
    (sub_nonneg.mpr hab.le)
  have he : e x = x := by
    rw [show e x = smoothUpStep b (c - b) (b - a) x by
      exact smoothUpStepDiffeomorph_apply _ _ _ _ _ _]
    exact smoothUpStep_eq_self_of_le (sub_pos.mpr hbc) (by linarith)
  calc
    e.symm x = e.symm (e x) := congrArg e.symm he.symm
    _ = x := Diffeomorph.symm_apply_apply e x

theorem annularScalarCompression_eq_self_of_le_right (d a b c : ℝ) (hda : d < a)
    (hab : a < b) (hbc : b < c) {x : ℝ} (hx : c ≤ x) :
    annularScalarCompression d a b c hda hab hbc x = x := by
  rw [annularScalarCompression_apply,
    smoothUpStep_eq_add_of_le (sub_pos.mpr hda) (by linarith)]
  let e := smoothUpStepDiffeomorph b (c - b) (b - a) (sub_pos.mpr hbc)
    (sub_nonneg.mpr hab.le)
  have he : e x = x + (b - a) := by
    rw [show e x = smoothUpStep b (c - b) (b - a) x by
      exact smoothUpStepDiffeomorph_apply _ _ _ _ _ _]
    exact smoothUpStep_eq_add_of_le (sub_pos.mpr hbc) (by linarith)
  calc
    e.symm (x + (b - a)) = e.symm (e x) := congrArg e.symm he.symm
    _ = x := Diffeomorph.symm_apply_apply e x

theorem annularScalarCompression_displacement_support_subset (d a b c : ℝ) (hda : d < a)
    (hab : a < b) (hbc : b < c) :
    Function.support (fun x ↦ annularScalarCompression d a b c hda hab hbc x - x) ⊆
      Ioo d c := by
  intro x hx
  change annularScalarCompression d a b c hda hab hbc x - x ≠ 0 at hx
  constructor
  · exact lt_of_not_ge fun h ↦ hx (by
      rw [annularScalarCompression_eq_self_of_le_left d a b c hda hab hbc h, sub_self])
  · exact lt_of_not_ge fun h ↦ hx (by
      rw [annularScalarCompression_eq_self_of_le_right d a b c hda hab hbc h, sub_self])

/-- The annular scalar compression is orientation preserving. -/
theorem annularScalarCompression_strictMono (d a b c : ℝ) (hda : d < a) (hab : a < b)
    (hbc : b < c) : StrictMono (annularScalarCompression d a b c hda hab hbc) := by
  intro x y hxy
  change (smoothUpStepOrderIso b (c - b) (b - a) (sub_pos.mpr hbc)
      (sub_nonneg.mpr hab.le)).symm
        (smoothUpStepOrderIso d (a - d) (b - a) (sub_pos.mpr hda)
          (sub_nonneg.mpr hab.le) x) <
    (smoothUpStepOrderIso b (c - b) (b - a) (sub_pos.mpr hbc)
      (sub_nonneg.mpr hab.le)).symm
        (smoothUpStepOrderIso d (a - d) (b - a) (sub_pos.mpr hda)
          (sub_nonneg.mpr hab.le) y)
  exact (smoothUpStepOrderIso b (c - b) (b - a) (sub_pos.mpr hbc)
      (sub_nonneg.mpr hab.le)).symm.strictMono <|
    (smoothUpStepOrderIso d (a - d) (b - a) (sub_pos.mpr hda)
      (sub_nonneg.mpr hab.le)).strictMono hxy

theorem scalarCompression_strictMono (a b c : ℝ) (ha : 0 < a) (hab : a < b)
    (hbc : b < c) : StrictMono (scalarCompression a b c ha hab hbc) := by
  intro x y hxy
  change (smoothUpStepOrderIso b (c - b) (b - a) (sub_pos.mpr hbc)
      (sub_nonneg.mpr hab.le)).symm
        (smoothUpStepOrderIso 0 a (b - a) ha (sub_nonneg.mpr hab.le) x) <
    (smoothUpStepOrderIso b (c - b) (b - a) (sub_pos.mpr hbc)
      (sub_nonneg.mpr hab.le)).symm
        (smoothUpStepOrderIso 0 a (b - a) ha (sub_nonneg.mpr hab.le) y)
  exact (smoothUpStepOrderIso b (c - b) (b - a) (sub_pos.mpr hbc)
      (sub_nonneg.mpr hab.le)).symm.strictMono <|
    (smoothUpStepOrderIso 0 a (b - a) ha (sub_nonneg.mpr hab.le)).strictMono hxy

theorem annularScalarCompression_zero (d a b c : ℝ) (hd : 0 < d) (hda : d < a)
    (hab : a < b) (hbc : b < c) : annularScalarCompression d a b c hda hab hbc 0 = 0 :=
  annularScalarCompression_eq_self_of_le_left d a b c hda hab hbc hd.le

theorem annularScalarCompression_pos_of_pos (d a b c : ℝ) (hd : 0 < d) (hda : d < a)
    (hab : a < b) (hbc : b < c) {r : ℝ} (hr : 0 < r) :
    0 < annularScalarCompression d a b c hda hab hbc r := by
  rw [← annularScalarCompression_zero d a b c hd hda hab hbc]
  exact annularScalarCompression_strictMono d a b c hda hab hbc hr

/-! ## Radialization in a real inner-product space -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Radially apply a scalar radius function.  At the origin the displayed quotient is `0 / 0`,
which is `0` in Lean; scalar multiplication still gives the correct value `0`. -/
def radialMap (ρ : ℝ → ℝ) (x : E) : E :=
  (ρ ‖x‖ / ‖x‖) • x

theorem radialMap_eq_self_of_norm_le {ρ : ℝ → ℝ} {d : ℝ}
    (hρ : ∀ r, r ≤ d → ρ r = r) {x : E} (hx : ‖x‖ ≤ d) : radialMap ρ x = x := by
  by_cases h0 : x = 0
  · simp [radialMap, h0]
  · rw [radialMap, hρ _ hx, div_self (norm_ne_zero_iff.mpr h0), one_smul]

/-- A radial map is smooth when its radius function is smooth and is the identity on a positive
initial interval.  The latter hypothesis removes the apparent singularity of the formula at the
origin. -/
theorem radialMap_contDiff {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) {d : ℝ} (hd : 0 < d)
    (hfix : ∀ r, r ≤ d → ρ r = r) : ContDiff ℝ ∞ (radialMap (E := E) ρ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_id.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : E) hd] with y hy
    have hyn : ‖y‖ ≤ d := by
      rw [Metric.mem_ball, dist_zero_right] at hy
      exact hy.le
    simpa only [id_eq] using radialMap_eq_self_of_norm_le hfix hyn
  · have hn : ContDiffAt ℝ ∞ (fun y : E ↦ ‖y‖) x := contDiffAt_norm ℝ hx
    have hc : ContDiffAt ℝ ∞ (fun y : E ↦ ρ ‖y‖) x := hρ.contDiffAt.comp x hn
    have hq : ContDiffAt ℝ ∞ (fun y : E ↦ ρ ‖y‖ / ‖y‖) x :=
      hc.div hn (norm_ne_zero_iff.mpr hx)
    change ContDiffAt ℝ ∞ ((fun y : E ↦ ρ ‖y‖ / ‖y‖) • id) x
    exact hq.smul contDiffAt_id

/-- Radialization commutes with inversion whenever the scalar equivalence sends positive radii
to positive radii. -/
theorem radialMap_leftInverse (e : ℝ ≃ ℝ) (hpos : ∀ r, 0 < r → 0 < e r) :
    LeftInverse (radialMap (E := E) e.symm) (radialMap (E := E) e) := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp [radialMap]
  · have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have her : 0 < e ‖x‖ := hpos _ hr
    have hn : ‖radialMap (E := E) e x‖ = e ‖x‖ := by
      rw [radialMap, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos her hr)]
      field_simp
    rw [radialMap, hn, e.symm_apply_apply, radialMap, smul_smul]
    have hr0 : ‖x‖ ≠ 0 := hr.ne'
    have her0 : e ‖x‖ ≠ 0 := her.ne'
    rw [div_mul_div_comm, mul_comm (e ‖x‖) ‖x‖]
    field_simp
    simp

theorem radialMap_norm (e : ℝ ≃ ℝ) (hzero : e 0 = 0)
    (hpos : ∀ r, 0 < r → 0 < e r) (x : E) : ‖radialMap e x‖ = e ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp [radialMap, hzero]
  · have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have her : 0 < e ‖x‖ := hpos _ hr
    rw [radialMap, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos her hr)]
    field_simp

/-- Radialize an orientation-preserving scalar diffeomorphism which is the identity near zero. -/
def radialDiffeomorphOfScalar (e : ℝ ≃ₘ[ℝ] ℝ) (d : ℝ) (hd : 0 < d)
    (hfix : ∀ r, r ≤ d → e r = r) (hmono : StrictMono e) : E ≃ₘ[ℝ] E := by
  have hzero : e 0 = 0 := hfix 0 hd.le
  have hpos : ∀ r, 0 < r → 0 < e r := by
    intro r hr
    rw [← hzero]
    exact hmono hr
  have hzeroInv : e.symm 0 = 0 := by
    calc
      e.symm 0 = e.symm (e 0) := congrArg e.symm hzero.symm
      _ = 0 := Diffeomorph.symm_apply_apply e 0
  have hposInv : ∀ r, 0 < r → 0 < e.symm r := by
    intro r hr
    by_contra h
    have hle := hmono.monotone (le_of_not_gt h)
    rw [Diffeomorph.apply_symm_apply, hzero] at hle
    exact (not_lt_of_ge hle) hr
  have hfixInv : ∀ r, r ≤ d → e.symm r = r := by
    intro r hr
    calc
      e.symm r = e.symm (e r) := congrArg e.symm (hfix r hr).symm
      _ = r := Diffeomorph.symm_apply_apply e r
  exact
    { toEquiv :=
        { toFun := radialMap e
          invFun := radialMap e.symm
          left_inv := radialMap_leftInverse e.toEquiv hpos
          right_inv := by
            intro x
            change radialMap (⇑e.toEquiv) (radialMap (⇑e.toEquiv.symm) x) = x
            exact radialMap_leftInverse (E := E) e.toEquiv.symm hposInv x }
      contMDiff_toFun := (radialMap_contDiff e.contDiff hd hfix).contMDiff
      contMDiff_invFun := (radialMap_contDiff e.symm.contDiff hd hfixInv).contMDiff }

@[simp]
theorem radialDiffeomorphOfScalar_apply (e : ℝ ≃ₘ[ℝ] ℝ) (d : ℝ) (hd : 0 < d)
    (hfix : ∀ r, r ≤ d → e r = r) (hmono : StrictMono e) (x : E) :
    radialDiffeomorphOfScalar (E := E) e d hd hfix hmono x = radialMap e x :=
  by
    change (radialDiffeomorphOfScalar (E := E) e d hd hfix hmono).toEquiv.toFun x = _
    simp only [Equiv.toFun_as_coe, Diffeomorph.coe_toEquiv]
    change radialMap e x = radialMap e x
    rfl

/-- The annular scalar compression, radialized to any real inner-product space. -/
def annularRadialCompression (d a b c : ℝ) (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) : E ≃ₘ[ℝ] E :=
  radialDiffeomorphOfScalar (E := E) (annularScalarCompression d a b c hda hab hbc) d hd
    (fun _r hr ↦ annularScalarCompression_eq_self_of_le_left d a b c hda hab hbc hr)
    (annularScalarCompression_strictMono d a b c hda hab hbc)

@[simp]
theorem annularRadialCompression_apply (d a b c : ℝ) (hd : 0 < d) (hda : d < a)
    (hab : a < b) (hbc : b < c) (x : E) :
    annularRadialCompression (E := E) d a b c hd hda hab hbc x =
      (annularScalarCompression d a b c hda hab hbc ‖x‖ / ‖x‖) • x :=
  by
    rw [annularRadialCompression, radialDiffeomorphOfScalar_apply]
    rfl

theorem annularRadialCompression_eq_self_of_norm_le (d a b c : ℝ) (hd : 0 < d)
    (hda : d < a) (hab : a < b) (hbc : b < c) {x : E} (hx : ‖x‖ ≤ d) :
    annularRadialCompression (E := E) d a b c hd hda hab hbc x = x := by
  rw [annularRadialCompression_apply]
  exact radialMap_eq_self_of_norm_le
    (fun r hr ↦ annularScalarCompression_eq_self_of_le_left d a b c hda hab hbc hr) hx

theorem annularRadialCompression_eq_self_of_le_norm (d a b c : ℝ) (hd : 0 < d)
    (hda : d < a) (hab : a < b) (hbc : b < c) {x : E} (hx : c ≤ ‖x‖) :
    annularRadialCompression (E := E) d a b c hd hda hab hbc x = x := by
  rw [annularRadialCompression_apply]
  rw [annularScalarCompression_eq_self_of_le_right d a b c hda hab hbc hx]
  have hc : 0 < c := lt_trans (lt_trans (lt_trans hd hda) hab) hbc
  have hxn : ‖x‖ ≠ 0 := ne_of_gt (hc.trans_le hx)
  rw [div_self hxn, one_smul]

theorem annularRadialCompression_norm (d a b c : ℝ) (hd : 0 < d) (hda : d < a)
    (hab : a < b) (hbc : b < c) (x : E) :
    ‖annularRadialCompression (E := E) d a b c hd hda hab hbc x‖ =
      annularScalarCompression d a b c hda hab hbc ‖x‖ := by
  rw [annularRadialCompression_apply]
  change ‖radialMap (E := E) (annularScalarCompression d a b c hda hab hbc) x‖ = _
  apply radialMap_norm
  · exact annularScalarCompression_zero d a b c hd hda hab hbc
  · intro r hr
    exact annularScalarCompression_pos_of_pos d a b c hd hda hab hbc hr

theorem annularRadialCompression_apply_of_norm_eq_a (d a b c : ℝ) (hd : 0 < d)
    (hda : d < a) (hab : a < b) (hbc : b < c) {x : E} (hx : ‖x‖ = a) :
    annularRadialCompression (E := E) d a b c hd hda hab hbc x = (b / a) • x := by
  rw [annularRadialCompression_apply, hx,
    annularScalarCompression_apply_a d a b c hda hab hbc]

theorem annularRadialCompression_norm_of_norm_eq_a (d a b c : ℝ) (hd : 0 < d)
    (hda : d < a) (hab : a < b) (hbc : b < c) {x : E} (hx : ‖x‖ = a) :
    ‖annularRadialCompression (E := E) d a b c hd hda hab hbc x‖ = b := by
  rw [annularRadialCompression_norm, hx,
    annularScalarCompression_apply_a d a b c hda hab hbc]

theorem annularRadialCompression_displacement_support_subset (d a b c : ℝ) (hd : 0 < d)
    (hda : d < a) (hab : a < b) (hbc : b < c) :
    Function.support
        (fun x : E ↦ annularRadialCompression (E := E) d a b c hd hda hab hbc x - x) ⊆
      {x | d < ‖x‖ ∧ ‖x‖ < c} := by
  intro x hx
  change annularRadialCompression (E := E) d a b c hd hda hab hbc x - x ≠ 0 at hx
  constructor
  · exact lt_of_not_ge fun h ↦ hx (by
      rw [annularRadialCompression_eq_self_of_norm_le d a b c hd hda hab hbc h, sub_self])
  · exact lt_of_not_ge fun h ↦ hx (by
      rw [annularRadialCompression_eq_self_of_le_norm d a b c hd hda hab hbc h, sub_self])

end SplittingSpheres
