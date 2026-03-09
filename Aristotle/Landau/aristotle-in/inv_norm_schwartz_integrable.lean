import Mathlib

set_option linter.all false
set_option maxHeartbeats 800000
open MeasureTheory Real

noncomputable section

-- Harmonic `generalize_proofs` tactic

/-- Convolution of ‖·‖⁻¹ with a Schwartz-class function is integrable on ℝ³.
    This is the key integrability fact for the Coulomb collision kernel.

    The function ‖z‖⁻¹ is locally integrable in ℝ³ (the singularity is of order
    r⁻¹ in 3D, and ∫₀^R r⁻¹ · r² dr = R²/2 < ∞). Combined with the rapid
    decay of g at infinity (|g(w)| ≤ C/(1+‖w‖)^N for all N), Young's
    convolution inequality gives integrability of w ↦ ‖v-w‖⁻¹ · g(w).

    More concretely: split the integral into |v-w| ≤ 1 and |v-w| > 1.
    - Near part: ‖v-w‖⁻¹ is in L^p for p < 3, and g is bounded → Hölder.
    - Far part: ‖v-w‖⁻¹ ≤ 1, and g is integrable → bounded by ∫|g|. -/
lemma inv_norm_schwartz_integrable
    (g : (Fin 3 → ℝ) → ℝ)
    (hg_decay : ∀ N : ℕ, ∃ C > 0, ∀ w : Fin 3 → ℝ, |g w| * (1 + ‖w‖) ^ N ≤ C)
    (hg_meas : AEStronglyMeasurable g volume)
    (v : Fin 3 → ℝ) :
    Integrable (fun w => ‖v - w‖⁻¹ * g w) := by sorry
