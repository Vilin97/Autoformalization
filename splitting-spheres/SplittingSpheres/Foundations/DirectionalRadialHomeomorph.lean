/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Direction-dependent radial homeomorphisms

A positive scale which is constant along every positive ray defines a homeomorphism by
`x ↦ ρ x • x`.  Continuity of the scale is needed only away from the origin; uniform positive
lower and upper bounds make both the forward and inverse maps continuous at the origin.

The final result identifies the image of the closed unit ball with the exact radial body
`{x | ‖x‖ ≤ ρ x}`.  This is point-set topology only; no differentiability is asserted.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Scale a vector by a factor which may depend on its direction. -/
def directionalRadialMap (ρ : E → ℝ) (x : E) : E :=
  ρ x • x

@[simp]
theorem directionalRadialMap_zero (ρ : E → ℝ) :
    directionalRadialMap ρ (0 : E) = 0 := by
  simp [directionalRadialMap]

theorem norm_directionalRadialMap {a : ℝ} {ρ : E → ℝ}
    (hρ : ∀ x, a ≤ ρ x) (ha : 0 ≤ a) (x : E) :
    ‖directionalRadialMap ρ x‖ = ρ x * ‖x‖ := by
  rw [directionalRadialMap, norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha.trans (hρ x))]

/-- The radial map is continuous at the origin under a uniform positive upper bound. -/
theorem continuousAt_directionalRadialMap_zero
    {a b : ℝ} {ρ : E → ℝ} (ha : 0 < a) (hb : 0 < b)
    (hρ_lower : ∀ x, a ≤ ρ x) (hρ_upper : ∀ x, ρ x ≤ b) :
    ContinuousAt (directionalRadialMap ρ) (0 : E) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε / b, div_pos hε hb, ?_⟩
  intro x hx
  rw [directionalRadialMap_zero, dist_zero_right,
    norm_directionalRadialMap hρ_lower ha.le]
  have hxnorm : ‖x‖ < ε / b := by simpa [dist_zero_right] using hx
  calc
    ρ x * ‖x‖ ≤ b * ‖x‖ :=
      mul_le_mul_of_nonneg_right (hρ_upper x) (norm_nonneg x)
    _ < b * (ε / b) := mul_lt_mul_of_pos_left hxnorm hb
    _ = ε := by field_simp [hb.ne']

/-- Continuity away from zero follows from continuity of the scalar factor there. -/
theorem continuousAt_directionalRadialMap_of_ne_zero
    {ρ : E → ℝ} (hρ : ContinuousOn ρ ({0} : Set E)ᶜ)
    {x : E} (hx : x ≠ 0) :
    ContinuousAt (directionalRadialMap ρ) x := by
  have hxc : x ∈ ({0} : Set E)ᶜ := by simpa
  have hopen : IsOpen (({0} : Set E)ᶜ) := isClosed_singleton.isOpen_compl
  exact ((hρ.continuousAt (hopen.mem_nhds hxc)).smul continuousAt_id)

/-- Global continuity of a uniformly bounded direction-dependent radial scaling. -/
theorem continuous_directionalRadialMap
    {a b : ℝ} {ρ : E → ℝ} (ha : 0 < a) (hb : 0 < b)
    (hρ_lower : ∀ x, a ≤ ρ x) (hρ_upper : ∀ x, ρ x ≤ b)
    (hρ_cont : ContinuousOn ρ ({0} : Set E)ᶜ) :
    Continuous (directionalRadialMap ρ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · simpa [hx] using
      continuousAt_directionalRadialMap_zero ha hb hρ_lower hρ_upper
  · exact continuousAt_directionalRadialMap_of_ne_zero hρ_cont hx

/-- Reciprocal direction scale. -/
def reciprocalDirectionScale (ρ : E → ℝ) (x : E) : ℝ :=
  (ρ x)⁻¹

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem reciprocalDirectionScale_pos
    {a : ℝ} {ρ : E → ℝ} (ha : 0 < a) (hρ_lower : ∀ x, a ≤ ρ x)
    (x : E) :
    0 < reciprocalDirectionScale ρ x :=
  inv_pos.mpr (ha.trans_le (hρ_lower x))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem reciprocalDirectionScale_lower
    {b : ℝ} {ρ : E → ℝ} (hb : 0 < b) (hρ_upper : ∀ x, ρ x ≤ b)
    (hρ_pos : ∀ x, 0 < ρ x) (x : E) :
    b⁻¹ ≤ reciprocalDirectionScale ρ x := by
  exact (inv_le_inv₀ hb (hρ_pos x)).mpr (hρ_upper x)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem reciprocalDirectionScale_upper
    {a : ℝ} {ρ : E → ℝ} (ha : 0 < a) (hρ_lower : ∀ x, a ≤ ρ x)
    (x : E) :
    reciprocalDirectionScale ρ x ≤ a⁻¹ := by
  exact (inv_le_inv₀ (ha.trans_le (hρ_lower x)) ha).mpr (hρ_lower x)

omit [NormedSpace ℝ E] in
theorem continuousOn_reciprocalDirectionScale
    {a : ℝ} {ρ : E → ℝ} (ha : 0 < a) (hρ_lower : ∀ x, a ≤ ρ x)
    (hρ_cont : ContinuousOn ρ ({0} : Set E)ᶜ) :
    ContinuousOn (reciprocalDirectionScale ρ) ({0} : Set E)ᶜ := by
  intro x hx
  exact (hρ_cont x hx).inv₀ (by exact (ha.trans_le (hρ_lower x)).ne')

theorem reciprocalDirectionScale_smul_of_pos
    {ρ : E → ℝ}
    (hρ_ray : ∀ (r : ℝ), 0 < r → ∀ x, ρ (r • x) = ρ x)
    {r : ℝ} (hr : 0 < r) (x : E) :
    reciprocalDirectionScale ρ (r • x) = reciprocalDirectionScale ρ x := by
  simp [reciprocalDirectionScale, hρ_ray r hr x]

theorem directionalRadialMap_reciprocal_leftInverse
    {a : ℝ} {ρ : E → ℝ} (ha : 0 < a) (hρ_lower : ∀ x, a ≤ ρ x)
    (hρ_ray : ∀ (r : ℝ), 0 < r → ∀ x, ρ (r • x) = ρ x) :
    LeftInverse (directionalRadialMap (reciprocalDirectionScale ρ))
      (directionalRadialMap ρ) := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have hpos : 0 < ρ x := ha.trans_le (hρ_lower x)
    rw [directionalRadialMap, directionalRadialMap,
      reciprocalDirectionScale_smul_of_pos hρ_ray hpos]
    simp [reciprocalDirectionScale, hpos.ne', smul_smul]

theorem directionalRadialMap_reciprocal_rightInverse
    {a : ℝ} {ρ : E → ℝ} (ha : 0 < a) (hρ_lower : ∀ x, a ≤ ρ x)
    (hρ_ray : ∀ (r : ℝ), 0 < r → ∀ x, ρ (r • x) = ρ x) :
    RightInverse (directionalRadialMap (reciprocalDirectionScale ρ))
      (directionalRadialMap ρ) := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have hpos : 0 < ρ x := ha.trans_le (hρ_lower x)
    have hinvpos : 0 < reciprocalDirectionScale ρ x := inv_pos.mpr hpos
    rw [directionalRadialMap, directionalRadialMap]
    have hray := hρ_ray (reciprocalDirectionScale ρ x) hinvpos x
    rw [hray]
    simp [reciprocalDirectionScale, hpos.ne', smul_smul]

/-- A uniformly positive, bounded scale constant on positive rays produces a global radial
homeomorphism. -/
def directionalRadialHomeomorph
    {a b : ℝ} (ρ : E → ℝ) (ha : 0 < a) (hb : 0 < b)
    (hρ_lower : ∀ x, a ≤ ρ x) (hρ_upper : ∀ x, ρ x ≤ b)
    (hρ_cont : ContinuousOn ρ ({0} : Set E)ᶜ)
    (hρ_ray : ∀ (r : ℝ), 0 < r → ∀ x, ρ (r • x) = ρ x) : E ≃ₜ E where
  toFun := directionalRadialMap ρ
  invFun := directionalRadialMap (reciprocalDirectionScale ρ)
  left_inv := directionalRadialMap_reciprocal_leftInverse ha hρ_lower hρ_ray
  right_inv := directionalRadialMap_reciprocal_rightInverse ha hρ_lower hρ_ray
  continuous_toFun := continuous_directionalRadialMap ha hb hρ_lower hρ_upper hρ_cont
  continuous_invFun := by
    apply continuous_directionalRadialMap (inv_pos.mpr hb) (inv_pos.mpr ha)
    · exact reciprocalDirectionScale_lower hb hρ_upper
        (fun x ↦ ha.trans_le (hρ_lower x))
    · exact reciprocalDirectionScale_upper ha hρ_lower
    · exact continuousOn_reciprocalDirectionScale ha hρ_lower hρ_cont

@[simp]
theorem directionalRadialHomeomorph_apply
    {a b : ℝ} (ρ : E → ℝ) (ha : 0 < a) (hb : 0 < b)
    (hρ_lower : ∀ x, a ≤ ρ x) (hρ_upper : ∀ x, ρ x ≤ b)
    (hρ_cont : ContinuousOn ρ ({0} : Set E)ᶜ)
    (hρ_ray : ∀ (r : ℝ), 0 < r → ∀ x, ρ (r • x) = ρ x)
    (x : E) :
    directionalRadialHomeomorph ρ ha hb hρ_lower hρ_upper hρ_cont hρ_ray x =
      ρ x • x :=
  rfl

/-- The closed radial body cut out by a direction scale. -/
def directionalRadialBody (ρ : E → ℝ) : Set E :=
  {x | ‖x‖ ≤ ρ x}

/-- The outer radial boundary cut out by equality with the direction scale. -/
def directionalRadialBoundary (ρ : E → ℝ) : Set E :=
  {x | ‖x‖ = ρ x}

theorem image_directionalRadialHomeomorph_closedBall
    {a b : ℝ} (ρ : E → ℝ) (ha : 0 < a) (hb : 0 < b)
    (hρ_lower : ∀ x, a ≤ ρ x) (hρ_upper : ∀ x, ρ x ≤ b)
    (hρ_cont : ContinuousOn ρ ({0} : Set E)ᶜ)
    (hρ_ray : ∀ (r : ℝ), 0 < r → ∀ x, ρ (r • x) = ρ x) :
    directionalRadialHomeomorph ρ ha hb hρ_lower hρ_upper hρ_cont hρ_ray ''
        closedBall (0 : E) 1 = directionalRadialBody ρ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ‖ρ y • y‖ ≤ ρ (ρ y • y)
    have hpos : 0 < ρ y := ha.trans_le (hρ_lower y)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos, hρ_ray (ρ y) hpos]
    exact mul_le_of_le_one_right hpos.le (by simpa [mem_closedBall, dist_zero_right] using hy)
  · intro hx
    refine ⟨directionalRadialMap (reciprocalDirectionScale ρ) x, ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      rw [norm_directionalRadialMap
        (reciprocalDirectionScale_lower hb hρ_upper
          (fun z ↦ ha.trans_le (hρ_lower z))) (inv_pos.mpr hb).le]
      change (ρ x)⁻¹ * ‖x‖ ≤ 1
      exact (inv_mul_le_one₀ (ha.trans_le (hρ_lower x))).mpr hx
    · exact directionalRadialMap_reciprocal_rightInverse ha hρ_lower hρ_ray x

theorem image_directionalRadialHomeomorph_sphere
    {a b : ℝ} (ρ : E → ℝ) (ha : 0 < a) (hb : 0 < b)
    (hρ_lower : ∀ x, a ≤ ρ x) (hρ_upper : ∀ x, ρ x ≤ b)
    (hρ_cont : ContinuousOn ρ ({0} : Set E)ᶜ)
    (hρ_ray : ∀ (r : ℝ), 0 < r → ∀ x, ρ (r • x) = ρ x) :
    directionalRadialHomeomorph ρ ha hb hρ_lower hρ_upper hρ_cont hρ_ray ''
        sphere (0 : E) 1 = directionalRadialBoundary ρ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ‖ρ y • y‖ = ρ (ρ y • y)
    have hpos : 0 < ρ y := ha.trans_le (hρ_lower y)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos, hρ_ray (ρ y) hpos]
    have hynorm : ‖y‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hy
    rw [hynorm, mul_one]
  · intro hx
    refine ⟨directionalRadialMap (reciprocalDirectionScale ρ) x, ?_, ?_⟩
    · rw [mem_sphere, dist_zero_right]
      rw [norm_directionalRadialMap
        (reciprocalDirectionScale_lower hb hρ_upper
          (fun z ↦ ha.trans_le (hρ_lower z))) (inv_pos.mpr hb).le]
      change (ρ x)⁻¹ * ‖x‖ = 1
      rw [hx]
      exact inv_mul_cancel₀ (ha.trans_le (hρ_lower x)).ne'
    · exact directionalRadialMap_reciprocal_rightInverse ha hρ_lower hρ_ray x

/-- Restriction of a direction-dependent radial homeomorphism to the closed unit ball. -/
def directionalRadialBodyHomeomorph
    {a b : ℝ} (ρ : E → ℝ) (ha : 0 < a) (hb : 0 < b)
    (hρ_lower : ∀ x, a ≤ ρ x) (hρ_upper : ∀ x, ρ x ≤ b)
    (hρ_cont : ContinuousOn ρ ({0} : Set E)ᶜ)
    (hρ_ray : ∀ (r : ℝ), 0 < r → ∀ x, ρ (r • x) = ρ x) :
    closedBall (0 : E) 1 ≃ₜ directionalRadialBody ρ :=
  let e := directionalRadialHomeomorph ρ ha hb hρ_lower hρ_upper hρ_cont hρ_ray
  (e.image (closedBall (0 : E) 1)).trans
    (Homeomorph.setCongr <| image_directionalRadialHomeomorph_closedBall
      ρ ha hb hρ_lower hρ_upper hρ_cont hρ_ray)

/-- Restriction of a direction-dependent radial homeomorphism to the unit sphere. -/
def directionalRadialBoundaryHomeomorph
    {a b : ℝ} (ρ : E → ℝ) (ha : 0 < a) (hb : 0 < b)
    (hρ_lower : ∀ x, a ≤ ρ x) (hρ_upper : ∀ x, ρ x ≤ b)
    (hρ_cont : ContinuousOn ρ ({0} : Set E)ᶜ)
    (hρ_ray : ∀ (r : ℝ), 0 < r → ∀ x, ρ (r • x) = ρ x) :
    sphere (0 : E) 1 ≃ₜ directionalRadialBoundary ρ :=
  let e := directionalRadialHomeomorph ρ ha hb hρ_lower hρ_upper hρ_cont hρ_ray
  (e.image (sphere (0 : E) 1)).trans
    (Homeomorph.setCongr <| image_directionalRadialHomeomorph_sphere
      ρ ha hb hρ_lower hρ_upper hρ_cont hρ_ray)

end SplittingSpheres
