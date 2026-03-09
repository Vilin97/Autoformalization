import Mathlib

set_option linter.all false
set_option maxHeartbeats 800000
open MeasureTheory Real

noncomputable section

-- Harmonic `generalize_proofs` tactic

/-- Product of ‖z‖⁻¹ with two Schwartz functions (of v-w and w) is jointly integrable.
    This is needed for Fubini conditions in the Coulomb Landau operator.

    For Schwartz f: |f(v)| * (1+‖v‖)^N ≤ C and similarly for derivatives.
    The integrand ‖v-w‖⁻¹ * |f(v)| * |f(w)| is integrable over (v,w) ∈ ℝ³ × ℝ³
    by splitting: the ‖·‖⁻¹ factor is locally L^p (p < 3) in 3D, while the
    Schwartz functions provide rapid decay. -/
lemma inv_norm_schwartz_product_integrable
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_decay : ∀ N : ℕ, ∃ C > 0, ∀ v : Fin 3 → ℝ, |f v| * (1 + ‖v‖) ^ N ≤ C)
    (hf_meas : AEStronglyMeasurable f volume) :
    Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      ‖p.1 - p.2‖⁻¹ * f p.1 * f p.2) (volume.prod volume) := by sorry
