/-
  Concrete Theorem 42: VML steady state on T³ = (ℝ/ℤ)³.

  This states the main result with paper-style hypotheses on the concrete
  3-torus, replacing the abstract FlatTorus3 typeclass (23 proved fields)
  and the VelocityDecayConditions bundle (18 fields) with standard
  analytical hypotheses: uniform Schwartz decay, kernel regularity, and
  a stretched-exponential lower bound on f.

  Hypotheses (15 total):
  - 5 physical/kernel parameters (ν, ρ_ion, Ψ positive/C¹/poly growth)
  - 1 strict positivity (f > 0)
  - 3 smoothness (f smooth in v and x, B smooth)
  - 2 decay conditions (Schwartz in v, at most stretched-exponential decay)
  - 4 equations (Vlasov, Ampère, Gauss, div B = 0)
-/
import Aristotle.Landau.main.Theorem42
import Aristotle.Landau.main.TorusInstance
import Aristotle.Landau.main.VelocityDecayInstance

set_option linter.all false
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
        intro v; rw [inv_pow, inv_pow]; gcongr; nlinarith [norm_nonneg v]
      have h_integrable : IntegrableOn (fun v : Fin 3 → ℝ => (1 + ‖v‖ ^ 2)⁻¹ ^ 2) (Set.univ : Set (Fin 3 → ℝ)) := by
        have := @integrable_rpow_neg_one_add_norm_sq
        specialize @this (Fin 3 → ℝ) _ _ _ _ _ (MeasureSpace.volume) _ 4; norm_num at this
        simpa [add_comm] using this
      refine' h_integrable.mono' _ _
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


end VML
