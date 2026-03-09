/-
Joint (v,w) integrability for the Fubini swap in the entropy dissipation identity.

Show that (v,w) ↦ score(v) · (A(v-w) *ᵥ (f(w)∇f(v) - f(v)∇f(w))) is integrable
on the product space (Fin 3 → ℝ) × (Fin 3 → ℝ).

This is the Fubini condition for swapping ∫∫ → ∫∫ in the symmetrization argument.

Strategy: The integrand is bounded by
  |score(v)| * ∑_j |A(v-w)_{ij}| * |f(w)∇f(v)_j - f(v)∇f(w)_j|
For Coulomb, |A_{ij}| ≤ |v-w|^{-1}, so this reduces to
  |score(v)| * |v-w|^{-1} * (f(w)|∇f(v)| + f(v)|∇f(w)|)
The score = ∇f/f grows at most exponentially while f decays super-polynomially.

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

/-- Joint integrability for Fubini swap in entropy dissipation. -/
lemma fubini_double_integrable
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (hf_lower : ∃ (C : ℝ) (K : ℕ), ∀ v : Fin 3 → ℝ,
      Real.exp (-C * (1 + ‖v‖) ^ K) ≤ f v) :
    Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      dotProduct (vGrad' (Real.log ∘ f) p.1)
        (mulVec (landauMatrix' (p.1 - p.2))
          (f p.2 • vGrad' f p.1 - f p.1 • vGrad' f p.2))) := by sorry
