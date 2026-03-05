import Aristotle.Landau.main.VMLInputDerive
set_option linter.all false
open Matrix Finset BigOperators Real MeasureTheory
noncomputable section
namespace VML

-- ============================================================================
-- Theorem 42: Clean statement with minimal physical hypotheses
--
-- Reference: H-theorem-formal.pdf, Section 10, Theorem 42.
-- This is the main result: any sufficiently smooth steady-state solution
-- of the VML system on a periodic domain must be a global Maxwellian
-- equilibrium with E = 0 and B = const.
-- ============================================================================

/-- **Theorem 42** (Global steady state of the VML system).

    Consider the Vlasov-Maxwell-Landau system on a periodic spatial domain
    (modeled by a FlatTorus3) with collision frequency ν > 0, interaction
    potential Ψ > 0, and uniform neutralizing ion background density ρ_ion > 0.

    Let (f, E, B) be a sufficiently smooth steady-state solution with f > 0
    and f(x, ·) ∈ L¹(ℝ³) for each x. Then:

    (i)   f is a spatially uniform, zero-drift Maxwellian:
          f(v) = ρ_ion / (2πT)^(3/2) · exp(-|v|²/(2T))

    (ii)  The electric field vanishes: E = 0.

    (iii) The magnetic field is spatially constant.

    Reference: H-theorem-formal.pdf, Theorem 42. -/
theorem Theorem42
    -- === Spatial domain (abstract flat 3-torus) ===
    {X : Type*} [FlatTorus3 X] [inst : Nonempty X] [TopologicalSpace X] [CompactSpace X]
    -- === Physical state at steady state ===
    (f : X → (Fin 3 → ℝ) → ℝ)
    (E B : X → (Fin 3 → ℝ))
    -- === Physical parameters ===
    (Ψ : ℝ → ℝ) (ν ρ_ion : ℝ)
    -- === Derived quantities ===
    (ρ : X → ℝ) (J : X → (Fin 3 → ℝ))
    -- === Physical hypotheses ===
    (hν : 0 < ν)
    (hρ_ion : 0 < ρ_ion)
    (hΨ : ∀ r, 0 < Ψ r)
    (hΨ_cont : Continuous Ψ)
    (hf_pos : ∀ x v, 0 < f x v)
    (hρ_def : ∀ x, ρ x = ∫ v, f x v)
    (hJ_def : ∀ x, J x = fun i => ∫ v, v i * f x v)
    (hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x))
    (hf_int : ∀ x, Integrable (f x))
    -- Density is continuous on the spatial domain (follows from f smooth + integration)
    (hρ_cont : Continuous ρ)
    -- === Steady-state Maxwell equations ===
    -- Ampère's law (∂ₜE = 0): ∇×B = J
    (hAmpere : ∀ x, FlatTorus3.curlX B x = J x)
    -- Gauss's law: ∇·E = ρ − ρ_ion
    (hGauss : ∀ x, FlatTorus3.divX E x = ρ x - ρ_ion)
    -- Solenoidal constraint: ∇·B = 0
    (hDivB : ∀ x, FlatTorus3.divX B x = 0)
    -- === Steady-state Vlasov equation ===
    -- v · ∇ₓf + (E + v×B) · ∇ᵥf = ν Q(f,f)
    (hVlasov : ∀ x v,
      dotProduct v (FlatTorus3.gradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator Ψ (f x) v)
    -- === Velocity-space decay hypotheses ===
    -- PSD integrand integrability (velocity-space decay condition).
    -- These hold for distribution functions with sufficient velocity-space decay
    -- (e.g., Schwartz class or sub-Gaussian tails). Needed for the
    -- "nonneg integral = 0 → pointwise = 0" argument in the H-theorem chain.
    (hPSD_inner_int : ∀ x v, Integrable (PSDIntegrand Ψ (f x) v))
    (hPSD_outer_int : ∀ x, Integrable (fun v => ∫ w, PSDIntegrand Ψ (f x) v w))
    -- Fubini integrability for the symmetrized weak form (velocity-space decay condition).
    -- These hold for distribution functions with sufficient velocity-space decay.
    (hFubini_double : ∀ x, Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      dotProduct (vGrad (Real.log ∘ f x) p.1)
        (mulVec (landauMatrix Ψ (p.1 - p.2))
          (f x p.2 • vGrad (f x) p.1 - f x p.1 • vGrad (f x) p.2))))
    (hFubini_inner : ∀ x v, Integrable (fun w =>
      dotProduct (vGrad (Real.log ∘ f x) v)
        (mulVec (landauMatrix Ψ (v - w))
          (f x w • vGrad (f x) v - f x v • vGrad (f x) w))))
    (hFubini_outer : ∀ x, Integrable (fun v => ∫ w,
      dotProduct (vGrad (Real.log ∘ f x) v)
        (mulVec (landauMatrix Ψ (v - w))
          (f x w • vGrad (f x) v - f x v • vGrad (f x) w))))
    -- Transport integrability (velocity-space decay condition).
    -- Needed for decomposing ∫_v (Vlasov · log f) into spatial + force transport terms.
    (hSpatialTransport_int : ∀ x, Integrable (fun v =>
      v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v)))
    (hForceTransport_int : ∀ x, Integrable (fun v =>
      (E x + cross v (B x)) ⬝ᵥ vGrad (f x) v * Real.log (f x v)))
    -- Landau flux × log f decay (boundary terms vanish at velocity-space infinity).
    -- Holds for distribution functions with sub-Gaussian tails.
    (hLandauFluxDecay : ∀ x i, Filter.Tendsto (fun v =>
      (∫ w, mulVec (landauMatrix Ψ (v - w))
        (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) i * (Real.log ∘ f x) v)
      (Filter.cocompact _) (nhds 0))
    -- Force transport decay (boundary terms vanish for velocity-space IBP in entropy estimate).
    (hForceDecay : ∀ x i, Filter.Tendsto (fun v =>
      (E x + cross v (B x)) i * (f x v * Real.log (f x v) - f x v))
      (Filter.cocompact _) (nhds 0)) :
    -- === Conclusion ===
    ∃ (T_eq : ℝ) (B₀ : Fin 3 → ℝ), 0 < T_eq ∧
    (∀ x v, f x v = equilibriumMaxwellian ρ_ion T_eq v) ∧
    (∀ x, E x = 0) ∧
    (∀ x, B x = B₀) := by
  -- Step 0: Derive mathematical consequences of the Vlasov equation.
  have hρ_pos : ∀ x, 0 < ρ x := by
    intro x; rw [hρ_def x]
    exact density_positive_of_integral (f x) (hf_pos x) (hf_int x)
  have hTransportEntropy : (∫ x, entropyDissipation Ψ (f x)) = 0 :=
    transport_entropy_from_vlasov f E B Ψ ν hν hf_pos hf_smooth hf_int hVlasov
      hSpatialTransport_int hForceTransport_int hForceDecay
  have hPolynomialId := polynomial_identity_from_vlasov f E B Ψ ν hf_pos hf_smooth hf_int hΨ hVlasov
  have hPB := poisson_boltzmann_from_vlasov f E B Ψ ν ρ ρ_ion hf_pos hf_smooth hf_int hΨ hρ_def hGauss hVlasov
  -- Extremizers of ρ (extreme value theorem on compact T³)
  obtain ⟨x_max, hmax⟩ := continuous_attains_max ρ hρ_cont
  obtain ⟨x_min, hmin⟩ := continuous_attains_min ρ hρ_cont
  -- Step 1: Symmetrized weak form for each x (the core analytical input).
  -- Decomposed into IBP + Fubini symmetrization (both proved by Aristotle separately).
  -- Sub-step 1a: IBP + pull integral: ∫ Q·logf = -∫∫ ⟨∇logf(v), A·flux⟩
  -- Decomposes into: (i) vector IBP on ℝ³: ∫ (div_v F)·g = -∫ F·∇g,
  -- (ii) linearity: ⟨c, ∫_w H dw⟩ = ∫_w ⟨c, H⟩ dw (pull w-integral through dot product).
  have hIBP : ∀ x, ∫ v, LandauOperator Ψ (f x) v * (Real.log ∘ f x) v =
      -(∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f x) v)
          (mulVec (landauMatrix Ψ (v - w))
            (f x w • vGrad (f x) v - f x v • vGrad (f x) w))) :=
    fun x => landau_ibp Ψ (f x) (hf_pos x) (hf_smooth x) (hf_int x) (hLandauFluxDecay x)
  -- Sub-step 1b: Fubini symmetrization: ∫∫⟨Δ, A·flux⟩ = 2·∫∫⟨∇logf(v), A·flux⟩
  have hFubiniSym : ∀ x, ∫ v, ∫ w, dotProduct
        (vGrad (Real.log ∘ f x) v - vGrad (Real.log ∘ f x) w)
        (mulVec (landauMatrix Ψ (v - w))
          (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) =
      2 * ∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f x) v)
          (mulVec (landauMatrix Ψ (v - w))
            (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) := by
    intro x; exact fubini_symmetrization_logf Ψ (f x) (hf_smooth x) (hFubini_double x) (hFubini_inner x) (hFubini_outer x)
  -- Compose: ∫Q·logf = -I₁ = -(1/2)·(2·I₁) = -(1/2)·I₂
  have hSWF_all : ∀ x, ∫ v, LandauOperator Ψ (f x) v * (Real.log ∘ f x) v =
      -(1 / 2) * ∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f x) v - vGrad (Real.log ∘ f x) w)
        (mulVec (landauMatrix Ψ (v - w))
          (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) := by
    intro x; rw [hIBP x, hFubiniSym x]; ring
  -- Step 2: Derive D(f) = 0 from the Vlasov equation.
  have hD_zero : ∀ x, entropyDissipation Ψ (f x) = 0 := by
    have hD_nonpos : ∀ x, entropyDissipation Ψ (f x) ≤ 0 := by
      intro x
      exact H_theorem Ψ (f x) (fun r => le_of_lt (hΨ r)) (hf_pos x) (hf_smooth x) (hSWF_all x)
    have hD_int_zero : FlatTorus3.spatialIntegral (fun x => entropyDissipation Ψ (f x)) = 0 :=
      hTransportEntropy
    intro x
    have hD_neg : ∀ y, 0 ≤ -(entropyDissipation Ψ (f y)) := fun y => neg_nonneg.mpr (hD_nonpos y)
    have hD_neg_int : FlatTorus3.spatialIntegral (fun y => -(entropyDissipation Ψ (f y))) = 0 := by
      have h := FlatTorus3.hSpatialMul (fun y => entropyDissipation Ψ (f y)) (-1)
      simp only [mul_neg_one] at h
      linarith [hD_int_zero]
    linarith [FlatTorus3.hSpatialNonnegZero _ hD_neg hD_neg_int x]
  -- Step 3: Apply the main theorem via VMLInput.
  have result := main_from_physics {
    inst_ne := inst
    x₀ := Classical.arbitrary X
    f := f
    E := E
    B := B
    ν := ν
    ρ_ion := ρ_ion
    Ψ := Ψ
    hν := hν
    hρ_ion := hρ_ion
    hΨ := hΨ
    hf_pos := hf_pos
    hf_smooth := hf_smooth
    hf_int := hf_int
    ρ := ρ
    hρ_pos := hρ_pos
    J := J
    hAmpere := hAmpere
    hGauss := hGauss
    hDivB := hDivB
    hD_zero := hD_zero
    hScoreForm := fun x => entropy_score_form Ψ (f x) (hf_pos x) (hf_smooth x) (hSWF_all x)
    hPSD_cont := fun x =>
      PSDIntegrand_continuous Ψ (f x) hΨ_cont (hf_pos x) (hf_smooth x)
    hPSD_inner := hPSD_inner_int
    hPSD_outer := hPSD_outer_int
    hPolynomialIdentity := hPolynomialId
    hJ_from_maxwellian := fun b_func c₀ hform => by
      intro x
      obtain ⟨a₀, ha₀⟩ := hform x
      rw [hJ_def x]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      -- J x i = ∫ vᵢ f(x,v) dv = ∫ vᵢ exp(a₀ + b·v + c₀|v|²) dv
      have h_rw : ∫ v, v i * f x v = ∫ v, v i *
          Real.exp (a₀ + dotProduct (b_func x) v + c₀ * normSq v) := by
        congr 1; ext v; rw [ha₀]
      rw [h_rw]
      -- Apply Gaussian first moment
      have hc₀_neg : c₀ < 0 := by
        have := analysis_gaussian_integrability (f x) a₀ (b_func x) c₀
          (hf_pos x) (hf_int x) ha₀
        exact this
      have h_int : Integrable (fun v : Fin 3 → ℝ =>
          Real.exp (a₀ + dotProduct (b_func x) v + c₀ * normSq v)) := by
        convert hf_int x using 1; ext v; rw [ha₀]
      have h_fm := gaussian_first_moment a₀ (b_func x) c₀ hc₀_neg h_int i
      rw [h_fm]
      -- (-bᵢ/(2c₀)) * ∫ exp = ρ(x) * (-1/(2c₀)) * bᵢ
      have h_rho : ∫ v : Fin 3 → ℝ,
          Real.exp (a₀ + dotProduct (b_func x) v + c₀ * normSq v) = ρ x := by
        rw [hρ_def x]; congr 1; ext v; rw [ha₀]
      rw [h_rho]; ring
    x_max := x_max
    hmax := hmax
    x_min := x_min
    hmin := hmin
    hPB_eq := hPB
    hNormalization := fun a₀ c₀ hc₀ hf_form hdens => by
      intro x v
      have h_int : ∫ w : Fin 3 → ℝ, f x w = ρ_ion := by
        rw [← hdens x, hρ_def x]
      exact gaussian_normalization_maxwellian ρ_ion a₀ c₀ hρ_ion hc₀
        (f x) (hf_form x) h_int v
  }
  obtain ⟨eq, hf_eq, hE, hB⟩ := result
  exact ⟨eq.T, eq.B₀, eq.hT, hf_eq, hE, hB⟩

end VML
