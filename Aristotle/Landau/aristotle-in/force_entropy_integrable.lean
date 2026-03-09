import Mathlib

set_option linter.all false
set_option maxHeartbeats 800000
open MeasureTheory Real

noncomputable section

-- Harmonic `generalize_proofs` tactic

/-- If F : ℝ³ → ℝ³ has linear growth (|F(v)_i| ≤ CL*(1+‖v‖)),
    φ is smooth positive with Schwartz decay (|φ| * (1+‖v‖)^N ≤ C for all N),
    and |log φ| ≤ C_log*(1+‖v‖)^K,
    then v ↦ F(v)_i * (φ(v)*log(φ(v)) - φ(v)) is integrable.

    Bound: CL*(1+‖v‖) * C_φ/(1+‖v‖)^N * (C_log*(1+‖v‖)^K + 1) = C/(1+‖v‖)^(N-K-1). -/
lemma force_entropy_integrable
    (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (i : Fin 3)
    (φ : (Fin 3 → ℝ) → ℝ)
    (hF_bound : ∃ CL, 0 ≤ CL ∧ ∀ v (j : Fin 3), |F v j| ≤ CL * (1 + ‖v‖))
    (hφ_pos : ∀ v, 0 < φ v)
    (hφ_decay : ∀ (N : ℕ), ∃ C > 0, ∀ (v : Fin 3 → ℝ),
      |φ v| * (1 + ‖v‖) ^ N ≤ C)
    (hLogBound : ∃ (C_log : ℝ) (K_log : ℕ), ∀ (v : Fin 3 → ℝ),
      |Real.log (φ v)| ≤ C_log * (1 + ‖v‖) ^ K_log)
    (hφ_smooth : ContDiff ℝ ⊤ φ) :
    Integrable (fun v => F v i * (φ v * Real.log (φ v) - φ v)) := by sorry
