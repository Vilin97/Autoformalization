import Mathlib

set_option linter.all false
set_option maxHeartbeats 800000
open MeasureTheory Real

noncomputable section

-- Harmonic `generalize_proofs` tactic

/-- Convolution of a locally integrable kernel with a Schwartz function is integrable.
    Splits the integral at ‖v-w‖ = 1:
    - Near part (‖v-w‖ ≤ 1): K is locally integrable and g is bounded → product integrable
    - Far part (‖v-w‖ > 1): K ≤ 1 and g is integrable → product integrable -/
lemma convolution_local_int_schwartz
    (g : (Fin 3 → ℝ) → ℝ)
    (hg_decay : ∀ N : ℕ, ∃ C > 0, ∀ w : Fin 3 → ℝ, |g w| * (1 + ‖w‖) ^ N ≤ C)
    (hg_meas : AEStronglyMeasurable g volume)
    (hK_local : IntegrableOn (fun z : Fin 3 → ℝ => ‖z‖⁻¹)
      (Metric.closedBall (0 : Fin 3 → ℝ) 1))
    (v : Fin 3 → ℝ) :
    Integrable (fun w => ‖v - w‖⁻¹ * g w) := by sorry
