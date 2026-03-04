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
    with collision frequency ν > 0, interaction potential Ψ > 0, and uniform
    neutralizing ion background density ρ_ion > 0.

    Let (f, E, B) be a sufficiently smooth steady-state solution with f > 0
    and f(x, ·) ∈ L¹(ℝ³) for each x. Then:

    (i)   f is a spatially uniform, zero-drift Maxwellian:
          f(v) = ρ_ion / (2πT)^(3/2) · exp(-|v|²/(2T))

    (ii)  The electric field vanishes: E = 0.

    (iii) The magnetic field is spatially constant.

    Reference: H-theorem-formal.pdf, Theorem 42. -/
theorem Theorem42
    -- === Spatial domain (abstract T³) with differential operators ===
    {X : Type*} [inst : Nonempty X] [TopologicalSpace X] [CompactSpace X]
    (gradX : (X → ℝ) → X → (Fin 3 → ℝ))
    (divX : (X → (Fin 3 → ℝ)) → X → ℝ)
    (curlX : (X → (Fin 3 → ℝ)) → X → (Fin 3 → ℝ))
    (spatialIntegral : (X → ℝ) → ℝ)
    (vol : ℝ)
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
    (hvol : 0 < vol)
    (hρ_def : ∀ x, ρ x = ∫ v, f x v)
    (hJ_def : ∀ x, J x = fun i => ∫ v, v i * f x v)
    (hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x))
    (hf_int : ∀ x, Integrable (f x))
    -- Density is continuous on the spatial domain (follows from f smooth + integration)
    (hρ_cont : Continuous ρ)
    -- === Steady-state Maxwell equations ===
    -- Ampère's law (∂ₜE = 0): ∇×B = J
    (hAmpere : ∀ x, curlX B x = J x)
    -- Gauss's law: ∇·E = ρ − ρ_ion
    (hGauss : ∀ x, divX E x = ρ x - ρ_ion)
    -- Solenoidal constraint: ∇·B = 0
    (hDivB : ∀ x, divX B x = 0)
    -- === Steady-state Vlasov equation ===
    -- v · ∇ₓf + (E + v×B) · ∇ᵥf = ν Q(f,f)
    (hVlasov : ∀ x v,
      dotProduct v (gradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator Ψ (f x) v)
    -- === Domain: flat compact torus T³ ===
    -- These characterize X as a flat compact 3-torus with its differential operators.
    (hStokes : ∀ F : X → (Fin 3 → ℝ), spatialIntegral (divX F) = 0)
    (hHarmonic_const : ∀ φ : X → ℝ, (∀ x, divX (gradX φ) x = 0) → ∀ x y, φ x = φ y)
    (hKillingToHarmonic : ∀ (b : X → Fin 3 → ℝ),
      (∀ x i j, gradX (fun y => b y j) x i + gradX (fun y => b y i) x j = 0) →
      ∀ j : Fin 3, ∀ x, divX (gradX (fun y => b y j)) x = 0)
    (hGradConst : ∀ (φ : X → ℝ), (∀ x y, φ x = φ y) → ∀ x, gradX φ x = 0)
    (hDivLinear : ∀ (α : ℝ) (G : X → (Fin 3 → ℝ)),
      ∀ x, divX (fun y => α • G y) x = α * divX G x)
    (hCurlDotConst : ∀ (u : Fin 3 → ℝ),
      spatialIntegral (fun x => dotProduct u (curlX B x)) = 0)
    (hCurlZeroDivZeroHarmonic : ∀ F : X → (Fin 3 → ℝ),
      (∀ x, curlX F x = 0) → (∀ x, divX F x = 0) →
      ∀ i, ∀ x, divX (gradX (fun y => F y i)) x = 0)
    (hSpatialMul : ∀ (g : X → ℝ) (c : ℝ),
      spatialIntegral (fun x => g x * c) = spatialIntegral g * c)
    (hSpatialPos : ∀ g : X → ℝ, (∀ x, 0 < g x) → 0 < spatialIntegral g)
    (hSpatialNonnegZero : ∀ g : X → ℝ,
      (∀ x, 0 ≤ g x) → spatialIntegral g = 0 → ∀ x, g x = 0)
    -- === Velocity-space decay hypotheses ===
    -- PSD integrand integrability (velocity-space decay condition).
    -- These hold for distribution functions with sufficient velocity-space decay
    -- (e.g., Schwartz class or sub-Gaussian tails). Needed for the
    -- "nonneg integral = 0 → pointwise = 0" argument in the H-theorem chain.
    (hPSD_inner_int : ∀ x v, Integrable (PSDIntegrand Ψ (f x) v))
    (hPSD_outer_int : ∀ x, Integrable (fun v => ∫ w, PSDIntegrand Ψ (f x) v w)) :
    -- === Conclusion ===
    ∃ (T_eq : ℝ) (B₀ : Fin 3 → ℝ), 0 < T_eq ∧
    (∀ x v, f x v = equilibriumMaxwellian ρ_ion T_eq v) ∧
    (∀ x, E x = 0) ∧
    (∀ x, B x = B₀) := by
  -- Step 0: Derive mathematical consequences of the Vlasov equation.
  -- These were previously hypotheses but are derivable from the physical equations.
  have hρ_pos : ∀ x, 0 < ρ x := by
    intro x; rw [hρ_def x]
    exact density_positive_of_integral (f x) (hf_pos x) (hf_int x)
  have hTransportEntropy : spatialIntegral (fun x => entropyDissipation Ψ (f x)) = 0 :=
    transport_entropy_from_vlasov gradX divX spatialIntegral f E B Ψ ν
      hν hf_pos hf_smooth hVlasov hStokes
  have hPolynomialId := polynomial_identity_from_vlasov
    gradX f E B Ψ ν hf_pos hf_smooth hf_int hΨ hVlasov
  have hPB := poisson_boltzmann_from_vlasov
    gradX divX f E B Ψ ν ρ ρ_ion hf_pos hf_smooth hf_int hΨ hρ_def hGauss hDivLinear hVlasov
  -- Derive domain-structure consequences from compactness, harmonic theory, etc.
  -- hGradZeroConst: zero gradient → constant (follows from harmonic → constant + div linearity)
  have hGradZeroConst : ∀ (φ : X → ℝ), (∀ x, gradX φ x = 0) → ∀ x y, φ x = φ y := by
    intro φ hφ; apply hHarmonic_const; intro x
    have h := hDivLinear 0 (gradX φ) x
    have hg : (fun y : X => (0 : ℝ) • gradX φ y) = gradX φ := by
      ext y; simp [hφ y]
    rw [hg, zero_mul] at h; exact h
  -- Extremizers of ρ (extreme value theorem on compact T³)
  obtain ⟨x_max, hmax⟩ := continuous_attains_max ρ hρ_cont
  obtain ⟨x_min, hmin⟩ := continuous_attains_min ρ hρ_cont
  -- Laplacian sign at extrema of log ∘ ρ (second derivative test)
  have hmax_logρ : ∀ x, (Real.log ∘ ρ) x ≤ (Real.log ∘ ρ) x_max :=
    fun x => Real.log_le_log (hρ_pos x) (hmax x)
  have hmin_logρ : ∀ x, (Real.log ∘ ρ) x_min ≤ (Real.log ∘ ρ) x :=
    fun x => Real.log_le_log (hρ_pos x_min) (hmin x)
  have hmax_lapl := laplacian_nonpos_at_max divX gradX (Real.log ∘ ρ) x_max hmax_logρ
  have hmin_lapl := laplacian_nonneg_at_min divX gradX (Real.log ∘ ρ) x_min hmin_logρ
  -- Step 1: Symmetrized weak form for each x (the core analytical input).
  -- Decomposed into IBP + Fubini symmetrization (both proved by Aristotle separately).
  -- Sub-step 1a: IBP + pull integral: ∫ Q·logf = -∫∫ ⟨∇logf(v), A·flux⟩
  have hIBP : ∀ x, ∫ v, LandauOperator Ψ (f x) v * (Real.log ∘ f x) v =
      -(∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f x) v)
          (mulVec (landauMatrix Ψ (v - w))
            (f x w • vGrad (f x) v - f x v • vGrad (f x) w))) := by
    sorry -- IBP: ∫ (div F)·g = -∫ F·∇g, then pull w-integral inside dot product
  -- Sub-step 1b: Fubini symmetrization: ∫∫⟨Δ, A·flux⟩ = 2·∫∫⟨∇logf(v), A·flux⟩
  have hFubiniSym : ∀ x, ∫ v, ∫ w, dotProduct
        (vGrad (Real.log ∘ f x) v - vGrad (Real.log ∘ f x) w)
        (mulVec (landauMatrix Ψ (v - w))
          (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) =
      2 * ∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f x) v)
          (mulVec (landauMatrix Ψ (v - w))
            (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) := by
    sorry -- Fubini swap + A(-z)=A(z) + flux antisymmetry → factor of 2
  -- Compose: ∫Q·logf = -I₁ = -(1/2)·(2·I₁) = -(1/2)·I₂
  have hSWF_all : ∀ x, ∫ v, LandauOperator Ψ (f x) v * (Real.log ∘ f x) v =
      -(1 / 2) * ∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f x) v - vGrad (Real.log ∘ f x) w)
        (mulVec (landauMatrix Ψ (v - w))
          (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) := by
    intro x; rw [hIBP x, hFubiniSym x]; ring
  -- Step 2: Derive D(f) = 0 from the Vlasov equation.
  -- Uses the H-theorem chain (Lemmas 21–23 in the paper):
  --   H-theorem (D ≤ 0) + transport entropy vanishes (∫D = 0) → D = 0
  have hD_zero : ∀ x, entropyDissipation Ψ (f x) = 0 := by
    -- Sub-result 1: D(f)(x) ≤ 0 for all x (H-theorem for the Landau operator)
    have hD_nonpos : ∀ x, entropyDissipation Ψ (f x) ≤ 0 := by
      intro x
      exact H_theorem Ψ (f x) (fun r => le_of_lt (hΨ r)) (hf_pos x) (hf_smooth x) (hSWF_all x)
    -- Sub-result 2: ∫_X D(f)(x) dx = 0 (transport entropy vanishes on T³)
    have hD_int_zero : spatialIntegral (fun x => entropyDissipation Ψ (f x)) = 0 :=
      hTransportEntropy
    -- Sub-result 3: D ≤ 0 everywhere + ∫ D = 0 → D = 0 (using hSpatialNonnegZero)
    -- -D ≥ 0 and ∫(-D) = 0, so -D = 0, hence D = 0
    intro x
    have hD_neg : ∀ y, 0 ≤ -(entropyDissipation Ψ (f y)) := fun y => neg_nonneg.mpr (hD_nonpos y)
    have hD_neg_int : spatialIntegral (fun y => -(entropyDissipation Ψ (f y))) = 0 := by
      have h := hSpatialMul (fun y => entropyDissipation Ψ (f y)) (-1)
      simp only [mul_neg_one] at h
      linarith [hD_int_zero]
    linarith [hSpatialNonnegZero _ hD_neg hD_neg_int x]
  -- Step 3: Apply the main theorem via VMLInput.
  have result := main_from_physics {
    X := X
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
    gradX := gradX
    divX := divX
    curlX := curlX
    spatialIntegral := spatialIntegral
    vol := vol
    hvol := hvol
    hAmpere := hAmpere
    hGauss := hGauss
    hDivB := hDivB
    hD_zero := hD_zero
    hStokes := hStokes
    hHarmonic_const := hHarmonic_const
    hKillingToHarmonic := hKillingToHarmonic
    hGradZeroConst := hGradZeroConst
    hGradConst := hGradConst
    hDivLinear := hDivLinear
    x_max := x_max
    hmax := hmax
    x_min := x_min
    hmin := hmin
    hmax_lapl := hmax_lapl
    hmin_lapl := hmin_lapl
    hCurlDotConst := hCurlDotConst
    hCurlZeroDivZeroHarmonic := hCurlZeroDivZeroHarmonic
    hSpatialMul := hSpatialMul
    hSpatialPos := hSpatialPos
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
    hNormalization := fun a₀ c₀ hc₀ hf_form hdens => by
      intro x v
      have h_int : ∫ w : Fin 3 → ℝ, f x w = ρ_ion := by
        rw [← hdens x, hρ_def x]
      exact gaussian_normalization_maxwellian ρ_ion a₀ c₀ hρ_ion hc₀
        (f x) (hf_form x) h_int v
    hPB_eq := hPB
  }
  obtain ⟨eq, hf_eq, hE, hB⟩ := result
  exact ⟨eq.T, eq.B₀, eq.hT, hf_eq, hE, hB⟩

end VML
