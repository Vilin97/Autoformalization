import Mathlib

set_option linter.all false
set_option maxHeartbeats 800000
open MeasureTheory Real

noncomputable section

-- Harmonic `generalize_proofs` tactic

/-- ‖·‖⁻¹ is locally integrable in ℝ³ (finite-dimensional).
    The singularity at 0 is of order r⁻¹ in 3D, and in spherical coordinates
    ∫₀^R r⁻¹ · r² dr = R²/2 < ∞.

    Alternatively, by AM-GM: ‖z‖_∞ ≥ (|z₁|·|z₂|·|z₃|)^{1/3}, so
    ‖z‖⁻¹ ≤ |z₁|^{-1/3} · |z₂|^{-1/3} · |z₃|^{-1/3}.
    By Fubini, ∫ ∏ |zᵢ|^{-1/3} = (∫ |t|^{-1/3} dt)³ < ∞
    since |t|^{-1/3} has exponent -1/3 > -1, so is locally integrable in 1D. -/
lemma inv_norm_local_integrable (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun z : Fin 3 → ℝ => ‖z‖⁻¹)
      (Metric.closedBall (0 : Fin 3 → ℝ) R) := by sorry
