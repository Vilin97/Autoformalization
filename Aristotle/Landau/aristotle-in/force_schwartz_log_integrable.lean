import Mathlib

set_option linter.all false
set_option maxHeartbeats 800000
open MeasureTheory Real

noncomputable section

-- Harmonic `generalize_proofs` tactic

/-- If F : ℝ³ → ℝ³ has linear growth (|F(v)_i| ≤ CL*(1+‖v‖)),
    φ has Schwartz derivative decay (|∂φ/∂vᵢ| * (1+‖v‖)^N ≤ C for all N),
    and |log φ| ≤ C_log*(1+‖v‖)^K,
    then v ↦ F(v)·∇φ(v)*log(φ(v)) is integrable on ℝ³.

    Bound: CL*(1+‖v‖) * C_der/(1+‖v‖)^N * C_log*(1+‖v‖)^K = C/(1+‖v‖)^(N-K-1). -/
lemma force_schwartz_log_integrable
    (F : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (φ : (Fin 3 → ℝ) → ℝ)
    (hF_bound : ∃ CL, 0 ≤ CL ∧ ∀ v (i : Fin 3), |F v i| ≤ CL * (1 + ‖v‖))
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    (hφ_pos : ∀ v, 0 < φ v)
    (hφ_deriv_decay : ∀ (N : ℕ) (i : Fin 3), ∃ C > 0, ∀ (v : Fin 3 → ℝ),
      |fderiv ℝ φ v (Pi.single i 1)| * (1 + ‖v‖) ^ N ≤ C)
    (hLogBound : ∃ (C_log : ℝ) (K_log : ℕ), ∀ (v : Fin 3 → ℝ),
      |Real.log (φ v)| ≤ C_log * (1 + ‖v‖) ^ K_log) :
    Integrable (fun v => dotProduct (F v)
      (fun i => fderiv ℝ φ v (Pi.single i 1)) * Real.log (φ v)) := by sorry
