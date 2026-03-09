/-
Landau IBP integrability: ∫ flux_i(v) * ∂_i(log f)(v) dv is integrable.

The flux Q_i(v) = ∫_w A_{ij}(v-w)(f(w)∂_j f(v) - f(v)∂_j f(w)) dw satisfies
|Q_i(v)| ≤ M(|∇f(v)| + f(v)) using the uniform convolution bound.
Then Q_i(v) * score_i(v) = Q_i(v) * ∂_i f(v) / f(v)
≤ M(|∇f(v)|² / f(v) + |∇f(v)|).

The second term is Schwartz, integrable. The first is the Fisher info density
f * |score|², which is integrable because f decays super-polynomially and
|score| grows at most exp(C|v|^K/2).

Building blocks: coulomb_bound (|A(z)_{ij}| ≤ ‖z‖⁻¹) and
inv_norm_schwartz_int (‖v-w‖⁻¹ × Schwartz is integrable) are admitted.
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

/-- Coulomb matrix entry bound: |A(z)_{ij}| ≤ ‖z‖⁻¹ for z ≠ 0. -/
lemma coulomb_bound (z : Fin 3 → ℝ) (i j : Fin 3) (hz : z ≠ 0) :
    |landauMatrix' z i j| ≤ ‖z‖⁻¹ := by admit

/-- Coulomb matrix vanishes at 0. -/
lemma coulomb_zero : landauMatrix' 0 = 0 := by
  ext i j
  simp [landauMatrix', innerLandauMatrix', normSq', eucNorm', dotProduct,
    vecMulVec, coulombKernel', Fin.sum_univ_three]

/-- ‖v-w‖⁻¹ × g(w) is integrable when g has Schwartz decay. -/
lemma inv_norm_schwartz_int
    (g : (Fin 3 → ℝ) → ℝ)
    (hg_decay : ∀ N : ℕ, ∃ C > 0, ∀ w : Fin 3 → ℝ, |g w| * (1 + ‖w‖) ^ N ≤ C)
    (hg_meas : AEStronglyMeasurable g volume)
    (v : Fin 3 → ℝ) :
    Integrable (fun w => ‖v - w‖⁻¹ * g w) := by admit

/-- The flux integrand is integrable (proved separately). -/
lemma flux_integrable
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (v : Fin 3 → ℝ) :
    Integrable (fun w =>
      mulVec (landauMatrix' (v - w))
        (f w • vGrad' f v - f v • vGrad' f w)) := by admit

/-- The flux component × d(log f) is integrable. -/
lemma landau_ibp_f_dg_integrable
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (hf_lower : ∃ (C : ℝ) (K : ℕ), ∀ v : Fin 3 → ℝ,
      Real.exp (-C * (1 + ‖v‖) ^ K) ≤ f v)
    (i : Fin 3) :
    Integrable (fun v =>
      (∫ w, mulVec (landauMatrix' (v - w))
        (f w • vGrad' f v - f v • vGrad' f w)) i *
      fderiv ℝ (Real.log ∘ f) v (Pi.single i 1)) := by sorry
