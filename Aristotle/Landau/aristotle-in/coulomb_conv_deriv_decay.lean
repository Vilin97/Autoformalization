/-
The derivative of a Coulomb kernel entry convolution with a Schwartz function has Schwartz decay.

After substituting u = v - w:
  fderiv(∫ A_{ij}(v-w) g(w) dw) = ∫ A_{ij}(u) • fderiv(g)(v-u) du

For the decay bound at large ‖v‖:
  ‖∫ A_{ij}(u) fderiv(g)(v-u) du‖ ≤ ∫ ‖u‖⁻¹ * C_N/(1+‖v-u‖)^N du

Split into ‖u‖ ≤ ‖v‖/2 and ‖u‖ > ‖v‖/2:
- Near part: ‖v-u‖ ≥ ‖v‖/2, so (1+‖v-u‖)^N ≥ (1+‖v‖/2)^N, giving O((1+‖v‖)^(-N))
- Far part: ‖u‖ > ‖v‖/2, use ‖u‖⁻¹ ≤ 2/‖v‖ and Schwartz decay of fderiv g, giving O(‖v‖⁻¹)
Both parts give polynomial decay in ‖v‖.
-/
import Mathlib

-- Harmonic `generalize_proofs` tactic

set_option linter.all false
set_option maxHeartbeats 800000

open MeasureTheory Real Matrix Finset BigOperators

noncomputable section

def normSq' (z : Fin 3 → ℝ) : ℝ := dotProduct z z
def eucNorm' (z : Fin 3 → ℝ) : ℝ := Real.sqrt (normSq' z)
def innerLandauMatrix' (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  normSq' z • (1 : Matrix (Fin 3) (Fin 3) ℝ) - vecMulVec z z
def coulombKernel' (r : ℝ) : ℝ := if r ≤ 0 then 1 else r ^ (-3 : ℝ)
def landauMatrix' (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  coulombKernel' (eucNorm' z) • innerLandauMatrix' z

-- |A_{ij}(z)| ≤ ‖z‖⁻¹
lemma coulomb_entry_bound (i j : Fin 3) (z : Fin 3 → ℝ) :
    |landauMatrix' z i j| ≤ ‖z‖⁻¹ := by admit

-- ‖z‖⁻¹ is locally integrable in ℝ³
lemma inv_norm_locallyIntegrable :
    LocallyIntegrable (fun z : Fin 3 → ℝ => ‖z‖⁻¹) := by admit

-- ‖z‖⁻¹ / (1+‖z‖)^4 is integrable in ℝ³
lemma inv_norm_poly_integrable :
    Integrable (fun z : Fin 3 → ℝ => ‖z‖⁻¹ / (1 + ‖z‖) ^ 4) := by admit

-- ‖z‖⁻¹ * Schwartz is integrable
lemma inv_norm_schwartz_integrable'
    (g : (Fin 3 → ℝ) → ℝ) (hg_smooth : ContDiff ℝ ⊤ g)
    (hg_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k g v‖ * (1 + ‖v‖) ^ N ≤ C)
    (v : Fin 3 → ℝ) :
    Integrable (fun w => ‖v - w‖⁻¹ * g w) := by admit

-- The convolution is differentiable (companion result)
lemma coulomb_entry_conv_differentiable'
    (g : (Fin 3 → ℝ) → ℝ) (hg_smooth : ContDiff ℝ ⊤ g)
    (hg_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k g v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i j : Fin 3) :
    Differentiable ℝ (fun v => ∫ w, landauMatrix' (v - w) i j * g w) := by admit

/-- The derivative of a Coulomb entry convolution with a Schwartz function has Schwartz decay. -/
lemma coulomb_entry_conv_deriv_decay'
    (g : (Fin 3 → ℝ) → ℝ) (hg_smooth : ContDiff ℝ ⊤ g)
    (hg_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k g v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i j : Fin 3) (N : ℕ) :
    ∃ C > 0, ∀ v, ‖fderiv ℝ (fun v => ∫ w, landauMatrix' (v - w) i j * g w) v‖ *
      (1 + ‖v‖) ^ N ≤ C := by
  sorry
