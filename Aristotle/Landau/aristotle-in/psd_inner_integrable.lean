/-
PSD inner integrability for the Coulomb kernel.

Show that for fixed v, the function
  w ↦ f(v) * f(w) * (∇log f(v) - ∇log f(w))^T A(v-w) (∇log f(v) - ∇log f(w))
is integrable.

Key: A(v-w) has entries bounded by |v-w|^{-1} (Coulomb), and the quadratic form
in the score differences gives an O(|v-w|^2) factor from Taylor expansion.
Combined: the integrand behaves like |v-w|^{-1} × |v-w|^2 × f(v)f(w) near v=w,
which is locally integrable. The Schwartz decay of f handles the tail.

Building blocks admitted: Coulomb entry bound, Schwartz convolution integrability.
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

/-- PSD integrand for Coulomb kernel -/
def PSDIntegrand' (f : (Fin 3 → ℝ) → ℝ) (v w : Fin 3 → ℝ) : ℝ :=
  f v * f w *
    dotProduct (vGrad' (Real.log ∘ f) v - vGrad' (Real.log ∘ f) w)
      (mulVec (landauMatrix' (v - w))
        (vGrad' (Real.log ∘ f) v - vGrad' (Real.log ∘ f) w))

/-- For fixed v, the PSD integrand w ↦ PSDIntegrand(v,w) is integrable. -/
lemma psd_inner_integrable
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (hf_lower : ∃ (C : ℝ) (K : ℕ), ∀ v : Fin 3 → ℝ,
      Real.exp (-C * (1 + ‖v‖) ^ K) ≤ f v)
    (v : Fin 3 → ℝ) :
    Integrable (PSDIntegrand' f v) := by sorry
