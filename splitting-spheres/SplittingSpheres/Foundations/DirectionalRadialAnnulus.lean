/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.UnitInterval
public import SplittingSpheres.Foundations.RadialSphereHomeomorphExtension

/-!
# Direction-dependent radial annuli

Let `r > 0` be constant and let `ρ` be a continuous positive radial bound on the unit sphere,
with `r < ρ u` in every direction.  The closed radial annulus between these two bounds is
homeomorphic to the product of the unit sphere and `[0,1]`.  The forward radial coordinate is

`r + t * (ρ u - r)`,

and the inverse recovers direction by normalization and time by affine rescaling of the norm.
The positive inner radius means normalization is never used at zero.  No differentiability or
smooth-boundary assertion is made.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped unitInterval

namespace SplittingSpheres

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The literal radial annulus -/

/-- The closed radial annulus between the constant inner radius `r` and the direction-dependent
outer radius `ρ`.  The existential witness only supplies the nonzero proof needed to bundle
normalization as a unit-sphere point; proof irrelevance makes the displayed direction canonical.
-/
def directionalRadialAnnulus
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ) : Set E :=
  {x | ∃ hx : x ≠ 0,
    r ≤ ‖x‖ ∧ ‖x‖ ≤ ρ (nonzeroUnitDirection ⟨x, hx⟩)}

theorem mem_directionalRadialAnnulus_iff
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ) (x : E) :
    x ∈ directionalRadialAnnulus r ρ ↔
      ∃ hx : x ≠ 0,
        r ≤ ‖x‖ ∧ ‖x‖ ≤ ρ (nonzeroUnitDirection ⟨x, hx⟩) :=
  Iff.rfl

theorem directionalRadialAnnulus_ne_zero
    {r : ℝ} {ρ : sphere (0 : E) 1 → ℝ} {x : E}
    (hx : x ∈ directionalRadialAnnulus r ρ) :
    x ≠ 0 :=
  hx.choose

/-- The canonical unit direction of a point of the annulus. -/
def directionalRadialAnnulusDirection
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (x : ↑(directionalRadialAnnulus r ρ)) : sphere (0 : E) 1 :=
  nonzeroUnitDirection ⟨x.1, directionalRadialAnnulus_ne_zero x.2⟩

@[simp]
theorem directionalRadialAnnulusDirection_coe
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (x : ↑(directionalRadialAnnulus r ρ)) :
    (directionalRadialAnnulusDirection r ρ x : E) =
      NormedSpace.normalize x.1 :=
  rfl

theorem directionalRadialAnnulus_lower
    {r : ℝ} {ρ : sphere (0 : E) 1 → ℝ}
    (x : ↑(directionalRadialAnnulus r ρ)) :
    r ≤ ‖x.1‖ := by
  exact x.2.choose_spec.1

theorem directionalRadialAnnulus_upper
    {r : ℝ} {ρ : sphere (0 : E) 1 → ℝ}
    (x : ↑(directionalRadialAnnulus r ρ)) :
    ‖x.1‖ ≤ ρ (directionalRadialAnnulusDirection r ρ x) := by
  simpa [directionalRadialAnnulusDirection] using x.2.choose_spec.2

theorem continuous_directionalRadialAnnulusDirection
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ) :
    Continuous (directionalRadialAnnulusDirection r ρ) := by
  exact continuous_nonzeroUnitDirection.comp <|
    continuous_subtype_val.subtype_mk _

/-! ## Forward radial coordinates -/

/-- Affine interpolation from `r` to the outer radius `ρ u`. -/
def directionalRadialAnnulusRadius
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (u : sphere (0 : E) 1) (t : Set.Icc (0 : ℝ) 1) : ℝ :=
  r + (t : ℝ) * (ρ u - r)

omit [NormedSpace ℝ E] in
theorem directionalRadialAnnulusRadius_pos
    {r : ℝ} {ρ : sphere (0 : E) 1 → ℝ}
    (hr : 0 < r) (hρ : ∀ u, r < ρ u)
    (u : sphere (0 : E) 1) (t : Set.Icc (0 : ℝ) 1) :
    0 < directionalRadialAnnulusRadius r ρ u t := by
  unfold directionalRadialAnnulusRadius
  have hgap : 0 < ρ u - r := sub_pos.mpr (hρ u)
  nlinarith [t.2.1]

omit [NormedSpace ℝ E] in
theorem directionalRadialAnnulusRadius_lower
    {r : ℝ} {ρ : sphere (0 : E) 1 → ℝ}
    (hρ : ∀ u, r < ρ u)
    (u : sphere (0 : E) 1) (t : Set.Icc (0 : ℝ) 1) :
    r ≤ directionalRadialAnnulusRadius r ρ u t := by
  unfold directionalRadialAnnulusRadius
  exact le_add_of_nonneg_right <| mul_nonneg t.2.1 (sub_pos.mpr (hρ u)).le

omit [NormedSpace ℝ E] in
theorem directionalRadialAnnulusRadius_upper
    {r : ℝ} {ρ : sphere (0 : E) 1 → ℝ}
    (hρ : ∀ u, r < ρ u)
    (u : sphere (0 : E) 1) (t : Set.Icc (0 : ℝ) 1) :
    directionalRadialAnnulusRadius r ρ u t ≤ ρ u := by
  unfold directionalRadialAnnulusRadius
  have hgap : 0 ≤ ρ u - r := (sub_pos.mpr (hρ u)).le
  nlinarith [mul_le_mul_of_nonneg_right t.2.2 hgap]

omit [NormedSpace ℝ E] in
@[simp]
theorem directionalRadialAnnulusRadius_zero
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ) (u : sphere (0 : E) 1) :
    directionalRadialAnnulusRadius r ρ u 0 = r := by
  simp [directionalRadialAnnulusRadius]

omit [NormedSpace ℝ E] in
@[simp]
theorem directionalRadialAnnulusRadius_one
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ) (u : sphere (0 : E) 1) :
    directionalRadialAnnulusRadius r ρ u 1 = ρ u := by
  simp [directionalRadialAnnulusRadius]

/-- The radial interpolation map before restricting its codomain. -/
def directionalRadialAnnulusMap
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (x : sphere (0 : E) 1 × Set.Icc (0 : ℝ) 1) : E :=
  directionalRadialAnnulusRadius r ρ x.1 x.2 • x.1.1

theorem norm_directionalRadialAnnulusMap
    {r : ℝ} {ρ : sphere (0 : E) 1 → ℝ}
    (hr : 0 < r) (hρ : ∀ u, r < ρ u)
    (x : sphere (0 : E) 1 × Set.Icc (0 : ℝ) 1) :
    ‖directionalRadialAnnulusMap r ρ x‖ =
      directionalRadialAnnulusRadius r ρ x.1 x.2 := by
  rw [directionalRadialAnnulusMap, norm_smul, Real.norm_eq_abs,
    abs_of_pos (directionalRadialAnnulusRadius_pos hr hρ x.1 x.2),
    mem_sphere_zero_iff_norm.mp x.1.2, mul_one]

theorem directionalRadialAnnulusMap_ne_zero
    {r : ℝ} {ρ : sphere (0 : E) 1 → ℝ}
    (hr : 0 < r) (hρ : ∀ u, r < ρ u)
    (x : sphere (0 : E) 1 × Set.Icc (0 : ℝ) 1) :
    directionalRadialAnnulusMap r ρ x ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_directionalRadialAnnulusMap hr hρ]
  exact (directionalRadialAnnulusRadius_pos hr hρ x.1 x.2).ne'

theorem nonzeroUnitDirection_directionalRadialAnnulusMap
    {r : ℝ} {ρ : sphere (0 : E) 1 → ℝ}
    (hr : 0 < r) (hρ : ∀ u, r < ρ u)
    (x : sphere (0 : E) 1 × Set.Icc (0 : ℝ) 1) :
    nonzeroUnitDirection
        ⟨directionalRadialAnnulusMap r ρ x,
          directionalRadialAnnulusMap_ne_zero hr hρ x⟩ = x.1 := by
  apply Subtype.ext
  rw [nonzeroUnitDirection_coe]
  change NormedSpace.normalize
      (directionalRadialAnnulusRadius r ρ x.1 x.2 • x.1.1) = x.1.1
  rw [NormedSpace.normalize_smul_of_pos
    (directionalRadialAnnulusRadius_pos hr hρ x.1 x.2)]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one <|
    mem_sphere_zero_iff_norm.mp x.1.2

/-- The radial interpolation bundled in the literal annulus subtype. -/
def directionalRadialAnnulusForward
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (hr : 0 < r) (hρ : ∀ u, r < ρ u)
    (x : sphere (0 : E) 1 × Set.Icc (0 : ℝ) 1) :
    ↑(directionalRadialAnnulus r ρ) :=
  ⟨directionalRadialAnnulusMap r ρ x, ⟨
    directionalRadialAnnulusMap_ne_zero hr hρ x,
    by rw [norm_directionalRadialAnnulusMap hr hρ]
       exact directionalRadialAnnulusRadius_lower hρ x.1 x.2,
    by
      rw [norm_directionalRadialAnnulusMap hr hρ,
        nonzeroUnitDirection_directionalRadialAnnulusMap hr hρ]
      exact directionalRadialAnnulusRadius_upper hρ x.1 x.2⟩⟩

@[simp]
theorem directionalRadialAnnulusForward_coe
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (hr : 0 < r) (hρ : ∀ u, r < ρ u)
    (x : sphere (0 : E) 1 × Set.Icc (0 : ℝ) 1) :
    (directionalRadialAnnulusForward r ρ hr hρ x : E) =
      directionalRadialAnnulusMap r ρ x :=
  rfl

theorem continuous_directionalRadialAnnulusForward
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (hr : 0 < r) (hρ : ∀ u, r < ρ u)
    (hρcont : Continuous ρ) :
    Continuous (directionalRadialAnnulusForward r ρ hr hρ) := by
  apply Continuous.subtype_mk
  unfold directionalRadialAnnulusMap directionalRadialAnnulusRadius
  exact (continuous_const.add <|
    (continuous_subtype_val.comp continuous_snd).mul <|
      (hρcont.comp continuous_fst).sub continuous_const).smul
        (continuous_subtype_val.comp continuous_fst)

/-! ## Inverse radial coordinates -/

/-- The inverse affine interval coordinate of a point in the annulus. -/
def directionalRadialAnnulusTime
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (x : ↑(directionalRadialAnnulus r ρ)) : ℝ :=
  (‖x.1‖ - r) / (ρ (directionalRadialAnnulusDirection r ρ x) - r)

theorem directionalRadialAnnulusTime_nonneg
    {r : ℝ} {ρ : sphere (0 : E) 1 → ℝ}
    (hρ : ∀ u, r < ρ u)
    (x : ↑(directionalRadialAnnulus r ρ)) :
    0 ≤ directionalRadialAnnulusTime r ρ x := by
  unfold directionalRadialAnnulusTime
  exact div_nonneg (sub_nonneg.mpr (directionalRadialAnnulus_lower x))
    (sub_pos.mpr (hρ _)).le

theorem directionalRadialAnnulusTime_le_one
    {r : ℝ} {ρ : sphere (0 : E) 1 → ℝ}
    (hρ : ∀ u, r < ρ u)
    (x : ↑(directionalRadialAnnulus r ρ)) :
    directionalRadialAnnulusTime r ρ x ≤ 1 := by
  unfold directionalRadialAnnulusTime
  rw [div_le_one (sub_pos.mpr (hρ _))]
  linarith [directionalRadialAnnulus_upper x]

/-- Direction and normalized radial time recovered from an annulus point. -/
def directionalRadialAnnulusInverse
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (hρ : ∀ u, r < ρ u)
    (x : ↑(directionalRadialAnnulus r ρ)) :
    sphere (0 : E) 1 × Set.Icc (0 : ℝ) 1 :=
  (directionalRadialAnnulusDirection r ρ x,
    ⟨directionalRadialAnnulusTime r ρ x,
      directionalRadialAnnulusTime_nonneg hρ x,
      directionalRadialAnnulusTime_le_one hρ x⟩)

@[simp]
theorem directionalRadialAnnulusInverse_fst
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (hρ : ∀ u, r < ρ u)
    (x : ↑(directionalRadialAnnulus r ρ)) :
    (directionalRadialAnnulusInverse r ρ hρ x).1 =
      directionalRadialAnnulusDirection r ρ x :=
  rfl

@[simp]
theorem directionalRadialAnnulusInverse_snd_coe
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (hρ : ∀ u, r < ρ u)
    (x : ↑(directionalRadialAnnulus r ρ)) :
    ((directionalRadialAnnulusInverse r ρ hρ x).2 : ℝ) =
      directionalRadialAnnulusTime r ρ x :=
  rfl

theorem continuous_directionalRadialAnnulusTime
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (hρ : ∀ u, r < ρ u) (hρcont : Continuous ρ) :
    Continuous (directionalRadialAnnulusTime r ρ) := by
  unfold directionalRadialAnnulusTime
  exact ((continuous_norm.comp continuous_subtype_val).sub continuous_const).div
    ((hρcont.comp (continuous_directionalRadialAnnulusDirection r ρ)).sub
      continuous_const)
    (fun x ↦ (sub_pos.mpr (hρ _)).ne')

theorem continuous_directionalRadialAnnulusInverse
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (hρ : ∀ u, r < ρ u) (hρcont : Continuous ρ) :
    Continuous (directionalRadialAnnulusInverse r ρ hρ) :=
  (continuous_directionalRadialAnnulusDirection r ρ).prodMk <|
    (continuous_directionalRadialAnnulusTime r ρ hρ hρcont).subtype_mk _

/-! ## The product homeomorphism -/

theorem directionalRadialAnnulusInverse_forward
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (hr : 0 < r) (hρ : ∀ u, r < ρ u)
    (x : sphere (0 : E) 1 × Set.Icc (0 : ℝ) 1) :
    directionalRadialAnnulusInverse r ρ hρ
        (directionalRadialAnnulusForward r ρ hr hρ x) = x := by
  have hdir : directionalRadialAnnulusDirection r ρ
      (directionalRadialAnnulusForward r ρ hr hρ x) = x.1 :=
    nonzeroUnitDirection_directionalRadialAnnulusMap hr hρ x
  apply Prod.ext
  · exact hdir
  · apply Subtype.ext
    rw [directionalRadialAnnulusInverse_snd_coe]
    unfold directionalRadialAnnulusTime
    rw [directionalRadialAnnulusForward_coe,
      norm_directionalRadialAnnulusMap hr hρ, hdir]
    unfold directionalRadialAnnulusRadius
    field_simp [(sub_pos.mpr (hρ x.1)).ne']
    ring

theorem directionalRadialAnnulusForward_inverse
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (hr : 0 < r) (hρ : ∀ u, r < ρ u)
    (x : ↑(directionalRadialAnnulus r ρ)) :
    directionalRadialAnnulusForward r ρ hr hρ
        (directionalRadialAnnulusInverse r ρ hρ x) = x := by
  apply Subtype.ext
  change directionalRadialAnnulusRadius r ρ
      (directionalRadialAnnulusDirection r ρ x)
      ⟨directionalRadialAnnulusTime r ρ x,
        directionalRadialAnnulusTime_nonneg hρ x,
        directionalRadialAnnulusTime_le_one hρ x⟩ •
      (directionalRadialAnnulusDirection r ρ x : E) = x.1
  have hgap : ρ (directionalRadialAnnulusDirection r ρ x) - r ≠ 0 :=
    (sub_pos.mpr (hρ _)).ne'
  have hradius : directionalRadialAnnulusRadius r ρ
      (directionalRadialAnnulusDirection r ρ x)
        ⟨directionalRadialAnnulusTime r ρ x,
          directionalRadialAnnulusTime_nonneg hρ x,
          directionalRadialAnnulusTime_le_one hρ x⟩ = ‖x.1‖ := by
    unfold directionalRadialAnnulusRadius directionalRadialAnnulusTime
    field_simp [hgap]
    ring
  rw [hradius, directionalRadialAnnulusDirection_coe,
    NormedSpace.norm_smul_normalize]

/-- The explicit homeomorphism from sphere times interval onto the literal radial annulus. -/
def directionalRadialAnnulusHomeomorph
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (hr : 0 < r) (hρ : ∀ u, r < ρ u) (hρcont : Continuous ρ) :
    sphere (0 : E) 1 × Set.Icc (0 : ℝ) 1 ≃ₜ
      ↑(directionalRadialAnnulus r ρ) where
  toFun := directionalRadialAnnulusForward r ρ hr hρ
  invFun := directionalRadialAnnulusInverse r ρ hρ
  left_inv := directionalRadialAnnulusInverse_forward r ρ hr hρ
  right_inv := directionalRadialAnnulusForward_inverse r ρ hr hρ
  continuous_toFun := continuous_directionalRadialAnnulusForward r ρ hr hρ hρcont
  continuous_invFun := continuous_directionalRadialAnnulusInverse r ρ hρ hρcont

@[simp]
theorem directionalRadialAnnulusHomeomorph_apply_coe
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (hr : 0 < r) (hρ : ∀ u, r < ρ u) (hρcont : Continuous ρ)
    (x : sphere (0 : E) 1 × Set.Icc (0 : ℝ) 1) :
    (directionalRadialAnnulusHomeomorph r ρ hr hρ hρcont x : E) =
      directionalRadialAnnulusRadius r ρ x.1 x.2 • x.1.1 :=
  rfl

@[simp]
theorem directionalRadialAnnulusHomeomorph_symm_apply_fst
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (hr : 0 < r) (hρ : ∀ u, r < ρ u) (hρcont : Continuous ρ)
    (x : ↑(directionalRadialAnnulus r ρ)) :
    ((directionalRadialAnnulusHomeomorph r ρ hr hρ hρcont).symm x).1 =
      directionalRadialAnnulusDirection r ρ x :=
  rfl

@[simp]
theorem directionalRadialAnnulusHomeomorph_symm_apply_snd_coe
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (hr : 0 < r) (hρ : ∀ u, r < ρ u) (hρcont : Continuous ρ)
    (x : ↑(directionalRadialAnnulus r ρ)) :
    (((directionalRadialAnnulusHomeomorph r ρ hr hρ hρcont).symm x).2 : ℝ) =
      directionalRadialAnnulusTime r ρ x :=
  rfl

@[simp]
theorem norm_directionalRadialAnnulusHomeomorph_apply
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (hr : 0 < r) (hρ : ∀ u, r < ρ u) (hρcont : Continuous ρ)
    (x : sphere (0 : E) 1 × Set.Icc (0 : ℝ) 1) :
    ‖(directionalRadialAnnulusHomeomorph r ρ hr hρ hρcont x : E)‖ =
      directionalRadialAnnulusRadius r ρ x.1 x.2 :=
  norm_directionalRadialAnnulusMap hr hρ x

/-- The zero-time face is exactly the inner sphere of radius `r`. -/
@[simp]
theorem directionalRadialAnnulusHomeomorph_apply_zero_coe
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (hr : 0 < r) (hρ : ∀ u, r < ρ u) (hρcont : Continuous ρ)
    (u : sphere (0 : E) 1) :
    (directionalRadialAnnulusHomeomorph r ρ hr hρ hρcont (u, 0) : E) =
      r • u.1 := by
  rw [directionalRadialAnnulusHomeomorph_apply_coe,
    directionalRadialAnnulusRadius_zero]

/-- The one-time face is exactly the direction-dependent outer radial boundary. -/
@[simp]
theorem directionalRadialAnnulusHomeomorph_apply_one_coe
    (r : ℝ) (ρ : sphere (0 : E) 1 → ℝ)
    (hr : 0 < r) (hρ : ∀ u, r < ρ u) (hρcont : Continuous ρ)
    (u : sphere (0 : E) 1) :
    (directionalRadialAnnulusHomeomorph r ρ hr hρ hρcont (u, 1) : E) =
      ρ u • u.1 := by
  rw [directionalRadialAnnulusHomeomorph_apply_coe,
    directionalRadialAnnulusRadius_one]

end SplittingSpheres
