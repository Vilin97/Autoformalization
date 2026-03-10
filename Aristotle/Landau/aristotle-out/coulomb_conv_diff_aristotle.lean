/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b419ae41-85e5-4a04-a68d-0a7a4960d351

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
Convolution of a Coulomb kernel matrix entry with a Schwartz function is differentiable.

After substituting u = v - w, the integrand becomes A_{ij}(u) * g(v-u), where
A_{ij}(u) doesn't depend on v. Apply hasFDerivAt_integral_of_dominated_of_fderiv_le:

The v-derivative of A_{ij}(u) * g(v-u) is A_{ij}(u) • fderiv(g)(v-u).
Uniform bound for v ∈ ball(v₀, 1):
  ‖A_{ij}(u) • fderiv(g)(v-u)‖ = |A_{ij}(u)| * ‖fderiv(g)(v-u)‖
  ≤ ‖u‖⁻¹ * C/(1+‖u‖)^4
This is integrable in ℝ³ (exponent 1+4=5 > 3).

Key Schwartz bound: ‖fderiv(g)(v-u)‖ ≤ C₄/(1+‖v-u‖)^4,
and for v ∈ ball(v₀,1): (1+‖v-u‖) ≥ (1+‖u‖)/(2+‖v₀‖) by triangle inequality,
so ‖fderiv(g)(v-u)‖ ≤ C₄*(2+‖v₀‖)^4/(1+‖u‖)^4.
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

-- Key bound: |A_{ij}(z)| ≤ ‖z‖⁻¹ for the Coulomb kernel
-- (from the cancellation in ‖z‖⁻³ * ‖z‖² = ‖z‖⁻¹)
-- Admitted as a building block.
lemma coulomb_entry_bound (i j : Fin 3) (z : Fin 3 → ℝ) :
    |landauMatrix' z i j| ≤ ‖z‖⁻¹ := by admit

-- ‖z‖⁻¹ is locally integrable in ℝ³
lemma inv_norm_locallyIntegrable :
    LocallyIntegrable (fun z : Fin 3 → ℝ => ‖z‖⁻¹) := by admit

-- ‖z‖⁻¹ / (1+‖z‖)^4 is integrable in ℝ³
lemma inv_norm_poly_integrable :
    Integrable (fun z : Fin 3 → ℝ => ‖z‖⁻¹ / (1 + ‖z‖) ^ 4) := by admit

/- Aristotle took a wrong turn (reason code: 9). Please try again. -/
/-- Convolution of a Coulomb kernel matrix entry with a Schwartz function is differentiable.
    Key idea: substitute u = v - w so the kernel A(u) doesn't depend on v,
    then apply hasFDerivAt_integral_of_dominated_of_fderiv_le.
    The v-derivative acts only on the Schwartz factor g(v-u), giving
    A(u) • fderiv(g)(v-u) which is dominated by ‖u‖⁻¹ * C/(1+‖u‖)^4. -/
lemma coulomb_entry_schwartz_conv_differentiable
    (g : (Fin 3 → ℝ) → ℝ) (hg_smooth : ContDiff ℝ ⊤ g)
    (hg_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k g v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i j : Fin 3) :
    Differentiable ℝ (fun v => ∫ w, landauMatrix' (v - w) i j * g w) := by
  sorry