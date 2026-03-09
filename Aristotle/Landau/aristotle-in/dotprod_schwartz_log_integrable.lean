import Mathlib

set_option linter.all false
set_option maxHeartbeats 800000
open MeasureTheory Real

noncomputable section

-- Harmonic `generalize_proofs` tactic

/-- If g : ℝ³ → ℝ³ has Schwartz-type component decay
    (|g(v)_i| * (1+‖v‖)^N ≤ C for all N, i)
    and h : ℝ³ → ℝ has polynomial growth
    (|h(v)| ≤ C_log * (1+‖v‖)^K_log),
    then v ↦ v · g(v) * h(v) is integrable on ℝ³.

    Proof idea: |v · g(v) * h(v)| ≤ Σᵢ ‖v‖ * |g(v)_i| * |h(v)|
    ≤ 3 * ‖v‖ * C/(1+‖v‖)^(K_log+5) * C_log*(1+‖v‖)^K_log
    = C' / (1+‖v‖)^4, integrable in ℝ³. -/
lemma dotprod_schwartz_log_integrable
    (g : (Fin 3 → ℝ) → Fin 3 → ℝ) (h : (Fin 3 → ℝ) → ℝ)
    (hg_decay : ∀ (N : ℕ) (i : Fin 3), ∃ C > 0, ∀ (v : Fin 3 → ℝ),
      |g v i| * (1 + ‖v‖) ^ N ≤ C)
    (hh_bound : ∃ (C_h : ℝ) (K_h : ℕ), ∀ (v : Fin 3 → ℝ),
      |h v| ≤ C_h * (1 + ‖v‖) ^ K_h)
    (hg_meas : ∀ i, AEStronglyMeasurable (fun v => g v i) volume)
    (hh_meas : AEStronglyMeasurable h volume) :
    Integrable (fun v => dotProduct v (g v) * h v) := by sorry
