import Aristotle.Landau.main.Theorem42
import Aristotle.Landau.main.TorusInstance

/-!
# Schwartz Decay Definitions and Integrability Helpers

Defines `UniformSchwartzDecay` (uniform-in-x Schwartz-class decay in velocity)
and proves basic integrability lemmas. This is the standard regularity assumption
for kinetic theory used throughout the Coulomb concrete theorem files.
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

/-- Uniform Schwartz decay in velocity: f(x,·) and all its velocity derivatives
    decay faster than any polynomial in |v|, uniformly in x ∈ T³.

    This is the standard "sufficient regularity and decay" assumption
    in kinetic theory (Desvillettes, Villani, Guo). -/
structure UniformSchwartzDecay
    (f : Torus3 → (Fin 3 → ℝ) → ℝ) : Prop where
  /-- All velocity derivatives of f decay faster than any polynomial, uniformly in x -/
  hDecay : ∀ (N k : ℕ), ∃ C > 0, ∀ (x : Torus3) (v : Fin 3 → ℝ),
    ‖iteratedFDeriv ℝ k (f x) v‖ * (1 + ‖v‖) ^ N ≤ C
  /-- Spatial gradients of f also have Schwartz decay in v -/
  hGradDecay : ∀ (N : ℕ) (i : Fin 3), ∃ C > 0, ∀ (x : Torus3) (v : Fin 3 → ℝ),
    |torusGradX (fun y => f y v) x i| * (1 + ‖v‖) ^ N ≤ C

lemma inverse_poly_integrable (C : ℝ) :
    Integrable (fun (v : Fin 3 → ℝ) => C / (1 + ‖v‖) ^ 4) := by
  -- Proved by Aristotle (job 3a0ec4f6)
  have h_integrable : Integrable (fun v : Fin 3 → ℝ => (1 + ‖v‖)⁻¹ ^ 4) volume := by
    have h_integrable : IntegrableOn (fun v : Fin 3 → ℝ => (1 + ‖v‖)⁻¹ ^ 4) (Set.univ : Set (Fin 3 → ℝ)) := by
      have : ∀ v : Fin 3 → ℝ, (1 + ‖v‖)⁻¹ ^ 4 ≤ (1 + ‖v‖ ^ 2)⁻¹ ^ 2 := by
        intro v
        rw [inv_pow, inv_pow]
        gcongr
        nlinarith [norm_nonneg v]
      have h_integrable : IntegrableOn (fun v : Fin 3 → ℝ => (1 + ‖v‖ ^ 2)⁻¹ ^ 2) (Set.univ : Set (Fin 3 → ℝ)) := by
        have := @integrable_rpow_neg_one_add_norm_sq
        specialize @this (Fin 3 → ℝ) _ _ _ _ _ (MeasureSpace.volume) _ 4; norm_num at this
        simpa [add_comm] using this
      refine h_integrable.mono' ?_ ?_
      · exact Measurable.aestronglyMeasurable (by measurability)
      · filter_upwards [] using fun v => by rw [Real.norm_of_nonneg (by positivity)]; exact this v
    aesop
  simpa using h_integrable.const_mul C

/-- Schwartz decay implies integrability. -/
lemma UniformSchwartzDecay.integrable {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hS : UniformSchwartzDecay f) (hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x))
    (x : Torus3) : Integrable (f x) := by
  obtain ⟨C, hC_pos, hbound⟩ := hS.hDecay 4 0
  have hint := inverse_poly_integrable C
  apply hint.mono' (hf_smooth x).continuous.aestronglyMeasurable
  filter_upwards [] with v
  have hb := hbound x v
  simp at hb
  -- hb : |f x v| * (1 + ‖v‖) ^ 4 ≤ C
  -- goal : ‖f x v‖ ≤ (fun v => C / (1 + ‖v‖) ^ 4) v
  have hv_pos : (0 : ℝ) < (1 + ‖v‖) ^ 4 := by positivity
  rw [Real.norm_eq_abs]
  rwa [le_div_iff₀ hv_pos]

/-- Schwartz decay implies integrability with polynomial weight.
    If f(x,·) decays faster than any polynomial, then (1+‖v‖)^M * |f(x,v)| is integrable for any M. -/
lemma UniformSchwartzDecay.integrable_poly_mul {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hS : UniformSchwartzDecay f) (hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x))
    (x : Torus3) (M : ℕ) :
    Integrable (fun v => (1 + ‖v‖) ^ M * f x v) := by
  obtain ⟨C, hC_pos, hbound⟩ := hS.hDecay (M + 4) 0
  have hint := inverse_poly_integrable C
  apply hint.mono' ((continuous_const.add continuous_norm).pow M |>.mul
    (hf_smooth x).continuous).aestronglyMeasurable
  filter_upwards [] with v
  have hb := hbound x v
  simp at hb
  have hv_pos : (0 : ℝ) < (1 + ‖v‖) ^ 4 := by positivity
  have hv1_pos : (0 : ℝ) < (1 + ‖v‖) ^ M := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  rw [le_div_iff₀ hv_pos]
  calc (1 + ‖v‖) ^ M * |f x v| * (1 + ‖v‖) ^ 4
      = |f x v| * ((1 + ‖v‖) ^ M * (1 + ‖v‖) ^ 4) := by ring
    _ = |f x v| * (1 + ‖v‖) ^ (M + 4) := by rw [pow_add]
    _ ≤ C := hb


/-- If ‖v‖^k * |φ(v)| is integrable for every k, then (1+‖v‖)^K * |φ(v)| is too.
    Uses the binomial theorem to expand (1+‖v‖)^K as a finite sum. -/
lemma integrable_one_add_norm_pow_mul
    {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    (K : ℕ) :
    Integrable (fun v => (1 + ‖v‖) ^ K * |φ v|) := by
  have h_binom : ∀ v : (Fin 3 → ℝ), (1 + ‖v‖) ^ K * |φ v| =
      ∑ k ∈ Finset.range (K + 1), Nat.choose K k * ‖v‖ ^ k * |φ v| := by
    simp +decide [add_comm (1 : ℝ), add_pow, mul_assoc, mul_comm, mul_left_comm,
      Finset.mul_sum _ _ _]
  simp_rw [h_binom]
  exact MeasureTheory.integrable_finset_sum _ fun k _ => by
    simpa only [mul_assoc] using MeasureTheory.Integrable.const_mul (hφ k) _

/-- If ‖v‖^k * |φ(v)| is integrable for every k, and ‖g(v)‖ ≤ C*(1+‖v‖)^K*|φ(v)|,
    then g is integrable. Core tool for Schwartz-dominance arguments. -/
lemma integrable_of_schwartz_bound
    {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    {g : (Fin 3 → ℝ) → ℝ}
    (hg_meas : AEStronglyMeasurable g)
    {C : ℝ} (_ : 0 ≤ C) {K : ℕ}
    (hbound : ∀ v, ‖g v‖ ≤ C * (1 + ‖v‖) ^ K * |φ v|) :
    Integrable g := by
  have hdom : Integrable (fun v => C * ((1 + ‖v‖) ^ K * |φ v|)) :=
    (integrable_one_add_norm_pow_mul hφ K).const_mul C
  exact hdom.mono' hg_meas (by
    filter_upwards with v
    calc ‖g v‖ ≤ C * (1 + ‖v‖) ^ K * |φ v| := hbound v
    _ = C * ((1 + ‖v‖) ^ K * |φ v|) := by ring)

end VML
