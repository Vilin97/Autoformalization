/-
PSD outer integrability for the Coulomb kernel.

Show that v ↦ ∫ w, PSDIntegrand(v,w) dw is integrable.

The PSD integrand is f(v)f(w)(Δ log f)^T A(v-w)(Δ log f) where A is the Coulomb
Landau matrix with entries bounded by |v-w|^{-1}.

Strategy: bound |∫_w PSD(v,w)dw| ≤ f(v) * C_v where C_v has polynomial growth,
then use f(v) Schwartz decay to get the integrand bounded by C/(1+|v|)^4.

Building blocks admitted: PSD inner integrability, Schwartz decay, Coulomb bounds.
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

def PSDIntegrand' (f : (Fin 3 → ℝ) → ℝ) (v w : Fin 3 → ℝ) : ℝ :=
  f v * f w *
    dotProduct (vGrad' (Real.log ∘ f) v - vGrad' (Real.log ∘ f) w)
      (mulVec (landauMatrix' (v - w))
        (vGrad' (Real.log ∘ f) v - vGrad' (Real.log ∘ f) w))

/-- PSD inner integrability (admitted). -/
lemma psd_inner_int
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (hf_lower : ∃ (C : ℝ) (K : ℕ), ∀ v : Fin 3 → ℝ,
      Real.exp (-C * (1 + ‖v‖) ^ K) ≤ f v)
    (v : Fin 3 → ℝ) :
    Integrable (PSDIntegrand' f v) := by admit

/-- The iterated PSD integral v ↦ ∫ w, PSD(v,w) dw is integrable. -/
lemma psd_outer_integrable
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (hf_lower : ∃ (C : ℝ) (K : ℕ), ∀ v : Fin 3 → ℝ,
      Real.exp (-C * (1 + ‖v‖) ^ K) ≤ f v) :
    Integrable (fun v => ∫ w, PSDIntegrand' f v w) := by sorry
