import Mathlib

set_option linter.all false
open Matrix Finset BigOperators Real MeasureTheory
noncomputable section

namespace VML

def normSq (z : Fin 3 → ℝ) : ℝ := dotProduct z z
def eucNorm (z : Fin 3 → ℝ) : ℝ := Real.sqrt (normSq z)
def innerLandauMatrix (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  normSq z • (1 : Matrix (Fin 3) (Fin 3) ℝ) - vecMulVec z z
def landauMatrix (Ψ : ℝ → ℝ) (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Ψ (eucNorm z) • innerLandauMatrix z

def vGrad (f : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => fderiv ℝ f v (Pi.single i 1)

def vDiv (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (v : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun w => F w i) v (Pi.single i 1)

def LandauOperator (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  vDiv (fun v' =>
    ∫ w, mulVec (landauMatrix Ψ (v' - w))
      (f w • vGrad f v' - f v' • vGrad f w)) v

/-- IBP for the Landau operator: ∫ Q(f)(v) · log f(v) dv =
    -∫∫ ⟨∇(log f)(v), A(v-w) · flux(v,w)⟩ dw dv.

    Proof sketch:
    1. Expand Q = div_v(∫ A·flux dw).
    2. Apply vector IBP: ∫ (div F)·φ = -∫ F·∇φ (boundary terms vanish by decay).
    3. Pull w-integral inside dot product by linearity. -/
lemma landau_ibp_logf (Ψ : ℝ → ℝ) (g : (Fin 3 → ℝ) → ℝ)
    (hg_pos : ∀ v, 0 < g v)
    (hg_smooth : ContDiff ℝ ⊤ g)
    -- Integrability hypotheses
    (h_lhs : Integrable (fun v => LandauOperator Ψ g v * Real.log (g v)))
    (h_flux_int : ∀ v, Integrable (fun w =>
      mulVec (landauMatrix Ψ (v - w))
        (g w • vGrad g v - g v • vGrad g w)))
    (h_rhs_inner : ∀ v, Integrable (fun w =>
      dotProduct (vGrad (Real.log ∘ g) v)
        (mulVec (landauMatrix Ψ (v - w))
          (g w • vGrad g v - g v • vGrad g w))))
    (h_rhs_outer : Integrable (fun v => ∫ w,
      dotProduct (vGrad (Real.log ∘ g) v)
        (mulVec (landauMatrix Ψ (v - w))
          (g w • vGrad g v - g v • vGrad g w)))) :
    ∫ v, LandauOperator Ψ g v * (Real.log ∘ g) v =
      -(∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ g) v)
          (mulVec (landauMatrix Ψ (v - w))
            (g w • vGrad g v - g v • vGrad g w))) := by
  sorry

end VML
