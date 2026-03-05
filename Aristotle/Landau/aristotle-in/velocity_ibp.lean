import Mathlib

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section

/-- Velocity gradient: ∇ᵥf(v), the vector of partial derivatives of f at v. -/
def vGrad (f : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => fderiv ℝ f v (Pi.single i 1)

/-- Velocity divergence: ∇ᵥ · F(v) = ∑ᵢ ∂Fᵢ/∂vᵢ -/
def vDiv (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (v : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun w => F w i) v (Pi.single i 1)

/-- Velocity-space integration by parts on ℝ³.
    ∫ (∇ᵥ · F)(v) · g(v) dv = -∫ F(v) · (∇ᵥg)(v) dv.

    The decay hypothesis ensures the boundary terms in the 1D IBP
    (applied via Fubini in each coordinate) vanish. -/
lemma velocity_ibp
    (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (g : (Fin 3 → ℝ) → ℝ)
    (hF_smooth : ∀ i, ContDiff ℝ ⊤ (fun v => F v i))
    (hg_smooth : ContDiff ℝ ⊤ g)
    (h_int1 : Integrable (fun v => vDiv F v * g v))
    (h_int2 : Integrable (fun v => dotProduct (F v) (vGrad g v)))
    (h_decay : ∀ i, Filter.Tendsto (fun v => F v i * g v)
      (Filter.cocompact _) (nhds 0)) :
    ∫ v, vDiv F v * g v = -(∫ v, dotProduct (F v) (vGrad g v)) := by
  sorry
