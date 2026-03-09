import Mathlib

set_option linter.all false
set_option maxHeartbeats 800000
open MeasureTheory Real Matrix Finset BigOperators

noncomputable section

-- Harmonic `generalize_proofs` tactic

-- Inline definitions from the project
def normSq' (z : Fin 3 → ℝ) : ℝ := dotProduct z z
def eucNorm' (z : Fin 3 → ℝ) : ℝ := Real.sqrt (normSq' z)
def innerLandauMatrix' (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  normSq' z • (1 : Matrix (Fin 3) (Fin 3) ℝ) - vecMulVec z z
def coulombKernel' (r : ℝ) : ℝ := if r ≤ 0 then 1 else r ^ (-3 : ℝ)
def landauMatrix' (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  coulombKernel' (eucNorm' z) • innerLandauMatrix' z
def vGrad' (f : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => fderiv ℝ f v (Pi.single i 1)

def PSDIntegrand' (f : (Fin 3 → ℝ) → ℝ) (v w : Fin 3 → ℝ) : ℝ :=
  f v * f w *
    dotProduct (vGrad' (Real.log ∘ f) v - vGrad' (Real.log ∘ f) w)
      (mulVec (landauMatrix' (v - w))
        (vGrad' (Real.log ∘ f) v - vGrad' (Real.log ∘ f) w))

/-- The PSD integrand for the Coulomb kernel Ψ(r)=r⁻³ is jointly continuous in (v,w).
    Key insight: even though the Landau matrix A(z) = |z|⁻³(|z|²I - zz^T) diverges as
    z → 0, the PSD integrand involves the quadratic form Δᵀ A(z) Δ where
    Δ = ∇log f(v) - ∇log f(w). The score difference Δ = O(|v-w|) (Lipschitz, from C²
    regularity of log f) cancels the O(|z|⁻¹) singularity:
      |Δᵀ A(v-w) Δ| ≤ |Δ|² * |v-w|⁻¹ ≤ L² * |v-w|² * |v-w|⁻¹ = L² * |v-w| → 0.
    At v = w: A(0) = 0 (innerLandauMatrix 0 = 0), so PSD(v,v) = 0. -/
lemma psd_continuous_coulomb
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f) :
    Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      PSDIntegrand' f p.1 p.2) := by sorry
