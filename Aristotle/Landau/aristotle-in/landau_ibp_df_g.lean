/-
Integrability of fderiv(flux_i) × log(f) for the Coulomb kernel.

The goal: show that v ↦ (∂/∂v_i Φ_i)(v) * log(f(v)) is integrable,
where Φ_i(v) = (∫ w, A(v-w) *ᵥ [f(w)∇f(v) - f(v)∇f(w)])_i
is the i-th component of the Landau collision flux.

Key idea: The flux derivative has Schwartz decay (since it's a
convolution of locally-integrable kernels ‖z‖⁻¹, ‖z‖⁻² with Schwartz
functions). Combined with the polynomial bound on |log f|, the product
decays like 1/(1+‖v‖)^4 and is hence integrable.

Building blocks: flux integrability, differentiability, and Schwartz bounds admitted.
-/
import Mathlib

-- Harmonic `generalize_proofs` tactic

set_option linter.all false
set_option maxHeartbeats 800000

open MeasureTheory Real Matrix Finset BigOperators

noncomputable section

def vGrad' (f : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => fderiv ℝ f v (Pi.single i 1)

def normSq' (z : Fin 3 → ℝ) : ℝ := dotProduct z z
def eucNorm' (z : Fin 3 → ℝ) : ℝ := Real.sqrt (normSq' z)
def innerLandauMatrix' (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  normSq' z • (1 : Matrix (Fin 3) (Fin 3) ℝ) - vecMulVec z z
def coulombKernel' (r : ℝ) : ℝ := if r ≤ 0 then 1 else r ^ (-3 : ℝ)
def landauMatrix' (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  coulombKernel' (eucNorm' z) • innerLandauMatrix' z

/-- The flux integrand is integrable (proved separately). -/
lemma flux_integrable'
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (v : Fin 3 → ℝ) :
    Integrable (fun w =>
      mulVec (landauMatrix' (v - w))
        (f w • vGrad' f v - f v • vGrad' f w)) := by admit

/-- The flux component is differentiable (proved separately). -/
lemma flux_differentiable'
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i : Fin 3) :
    Differentiable ℝ (fun v =>
      (∫ w, mulVec (landauMatrix' (v - w))
        (f w • vGrad' f v - f v • vGrad' f w)) i) := by admit

/-- C/(1+‖v‖)^4 is integrable in ℝ³ (proved separately). -/
lemma inverse_poly_integrable' (C : ℝ) :
    Integrable (fun v : Fin 3 → ℝ => C / (1 + ‖v‖) ^ 4) := by admit

/-- The flux derivative has Schwartz-class decay: for any N, the derivative
    times (1+‖v‖)^N is bounded. This follows from the flux being a convolution
    of locally-integrable Coulomb kernels (‖z‖⁻¹, ‖z‖⁻²) with Schwartz functions. -/
lemma flux_deriv_schwartz_decay'
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i : Fin 3) (N : ℕ) :
    ∃ (C₁ : ℝ), ∀ v : Fin 3 → ℝ,
      ‖fderiv ℝ (fun v' =>
        ∫ w, (mulVec (landauMatrix' (v' - w))
          (f w • vGrad' f v' - f v' • vGrad' f w)) i) v‖ *
      (1 + ‖v‖) ^ N ≤ C₁ := by admit

/-- The derivative of flux × log(f) is integrable for Coulomb kernel. -/
lemma landau_ibp_df_g
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (hLogBound : ∃ (Cl : ℝ) (Kl : ℕ), ∀ v : Fin 3 → ℝ,
      |(Real.log ∘ f) v| ≤ Cl * (1 + ‖v‖) ^ Kl)
    (i : Fin 3) :
    Integrable (fun v =>
      fderiv ℝ (fun v' => (∫ w, mulVec (landauMatrix' (v' - w))
        (f w • vGrad' f v' - f v' • vGrad' f w)) i) v (Pi.single i 1) *
      (Real.log ∘ f) v) := by sorry
