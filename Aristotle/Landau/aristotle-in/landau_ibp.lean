import Mathlib

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section

/-- Squared norm in ℝ³: |z|² = z · z. -/
def normSq (z : Fin 3 → ℝ) : ℝ := dotProduct z z

/-- Euclidean norm in ℝ³. -/
def eucNorm (z : Fin 3 → ℝ) : ℝ := Real.sqrt (normSq z)

/-- The inner part of the Landau matrix: B(z) = |z|² I₃ - z zᵀ. -/
def innerLandauMatrix (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  normSq z • (1 : Matrix (Fin 3) (Fin 3) ℝ) - vecMulVec z z

/-- The Landau collision matrix: A(z) = Ψ(|z|) · (|z|² I₃ - z zᵀ). -/
def landauMatrix (Ψ : ℝ → ℝ) (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Ψ (eucNorm z) • innerLandauMatrix z

/-- Velocity gradient: ∇ᵥf(v). -/
def vGrad (f : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => fderiv ℝ f v (Pi.single i 1)

/-- Velocity divergence: ∇ᵥ · F(v) = ∑ᵢ ∂Fᵢ/∂vᵢ -/
def vDiv (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (v : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun w => F w i) v (Pi.single i 1)

/-- The Landau collision operator Q(f,f)(v). -/
def LandauOperator (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  vDiv (fun v' =>
    ∫ w, mulVec (landauMatrix Ψ (v' - w))
      (f w • vGrad f v' - f v' • vGrad f w)) v

/-- IBP for the Landau operator: ∫ Q(g,g)·log g = -∫∫ ⟨∇log g(v), A(v-w)·flux⟩.
    Combines velocity-space IBP with pulling the w-integral through the dot product.
    The decay hypothesis ensures boundary terms vanish at velocity-space infinity. -/
lemma landau_ibp (Ψ : ℝ → ℝ) (g : (Fin 3 → ℝ) → ℝ)
    (hg_pos : ∀ v, 0 < g v) (hg_smooth : ContDiff ℝ ⊤ g) (hg_int : Integrable g)
    (h_decay : ∀ i, Filter.Tendsto (fun v =>
      (∫ w, mulVec (landauMatrix Ψ (v - w))
        (g w • vGrad g v - g v • vGrad g w)) i * (Real.log ∘ g) v)
      (Filter.cocompact _) (nhds 0)) :
    ∫ v, LandauOperator Ψ g v * (Real.log ∘ g) v =
    -(∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ g) v)
        (mulVec (landauMatrix Ψ (v - w))
          (g w • vGrad g v - g v • vGrad g w))) := by
  sorry
