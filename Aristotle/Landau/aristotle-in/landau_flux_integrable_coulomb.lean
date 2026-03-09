import Mathlib

set_option linter.all false
set_option maxHeartbeats 800000
open MeasureTheory Real Matrix Finset BigOperators

noncomputable section

-- Harmonic `generalize_proofs` tactic

-- Inline definitions
def normSq' (z : Fin 3 → ℝ) : ℝ := dotProduct z z
def eucNorm' (z : Fin 3 → ℝ) : ℝ := Real.sqrt (normSq' z)
def innerLandauMatrix' (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  normSq' z • (1 : Matrix (Fin 3) (Fin 3) ℝ) - vecMulVec z z
def coulombKernel' (r : ℝ) : ℝ := if r ≤ 0 then 1 else r ^ (-3 : ℝ)
def landauMatrix' (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  coulombKernel' (eucNorm' z) • innerLandauMatrix' z
def vGrad' (f : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => fderiv ℝ f v (Pi.single i 1)

/-- The Landau collision flux integrand is integrable for the Coulomb kernel.
    For each fixed v, the integrand as a function of w involves:
    - landauMatrix'(v-w), which has |A_{ij}| ≤ ‖v-w‖⁻¹ for Coulomb
    - f(w) and vGrad'(f)(w), which have Schwartz decay in w
    The product ‖v-w‖⁻¹ × Schwartz(w) is integrable in ℝ³ since
    ‖·‖⁻¹ is locally integrable in 3D. -/
lemma landau_flux_integrable_coulomb
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ (v : Fin 3 → ℝ),
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (v : Fin 3 → ℝ) :
    Integrable (fun w =>
      mulVec (landauMatrix' (v - w))
        (f w • vGrad' f v - f v • vGrad' f w)) := by sorry
