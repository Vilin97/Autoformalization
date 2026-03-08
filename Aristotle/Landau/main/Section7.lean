import Aristotle.Landau.main.Defs
import Aristotle.Landau.main.Section3
import Aristotle.Landau.main.Section6
set_option linter.all false
set_option linter.unusedSimpArgs false
open Matrix Finset BigOperators Real MeasureTheory
noncomputable section
namespace VML

-- ============================================================================
-- Helper lemma proved by Aristotle
-- ============================================================================

/-- Poisson-Boltzmann algebraic core: force balance + Gauss → PB equation.
    Proved by Aristotle (Harmonic). -/
lemma poisson_boltzmann_algebraic
    {X : Type*}
    (gradX : (X → ℝ) → X → (Fin 3 → ℝ))
    (divX : (X → (Fin 3 → ℝ)) → X → ℝ)
    (E : X → (Fin 3 → ℝ))
    (ρ : X → ℝ) (ρ_ion : ℝ)
    (a₀ : X → ℝ) (c₀ : ℝ)
    (_hc₀ : c₀ < 0)
    (hForce : ∀ x, gradX a₀ x = (-2 * c₀) • E x)
    (hGradLogRho : ∀ x, gradX (Real.log ∘ ρ) x = gradX a₀ x)
    (hGauss : ∀ x, divX E x = ρ x - ρ_ion)
    (hDivLinear : ∀ (α : ℝ) (G : X → Fin 3 → ℝ),
      ∀ x, divX (fun y => α • G y) x = α * divX G x) :
    ∀ x, (-1 / (2 * c₀)) * divX (gradX (Real.log ∘ ρ)) x = ρ x - ρ_ion := by
  simp_all +decide [div_eq_mul_inv]
  intro x
  rw [show gradX (Real.log ∘ ρ) = _ from funext hGradLogRho]
  specialize hDivLinear (-(2 * c₀)) E x
  simp_all +decide [mul_assoc, mul_comm, mul_left_comm]
  rw [mul_left_comm, mul_inv_cancel₀ _hc₀.ne, mul_one]

-- ============================================================================
-- Section 5d: Maximum Principle / Spatial Uniformity (Section 7 of tex)
-- Reference: Lemmas 20-21, Corollary 3
-- ============================================================================

/-- Lemma 20 (Poisson–Boltzmann equation for the density).
    Reference: lem:poisson_boltzmann

    With u∞ = 0, the force balance and Gauss's law yield:
    T∞ Δₓ(log n) = n(x) - ρ_ion -/
theorem poisson_boltzmann_density
    (X : Type*)
    (n : X → ℝ) (E : X → (Fin 3 → ℝ))
    (ρ_ion T_infty : ℝ)
    (gradX : (X → ℝ) → X → (Fin 3 → ℝ))
    (divX : (X → (Fin 3 → ℝ)) → X → ℝ)
    (_hT : 0 < T_infty)
    (_hforce : ∀ x, gradX (Real.log ∘ n) x = (1 / T_infty) • E x)
    (_hGauss : ∀ x, divX E x = n x - ρ_ion)
    (hDivLinear : ∀ (α : ℝ) (G : X → (Fin 3 → ℝ)),
      ∀ x, divX (fun y => α • G y) x = α * divX G x) :
    ∀ x, T_infty * divX (gradX (Real.log ∘ n)) x = n x - ρ_ion := by
  intro x
  have hgrad_eq : gradX (Real.log ∘ n) = fun y => (1 / T_infty) • E y := funext _hforce
  rw [hgrad_eq, divergence_scalar_linear X divX _ _ hDivLinear, _hGauss]
  field_simp

/-- Lemma 21 (Maximum principle: density is constant).
    Reference: lem:density_constant

    If n : T³ → (0,∞) satisfies T∞ Δₓ(log n) = n - ρ_ion with T∞ > 0,
    then n(x) ≡ ρ_ion.

    Proof: At the maximum of n (hence log n), Δ(log n) ≤ 0, so n ≤ ρ_ion.
    At the minimum, Δ(log n) ≥ 0, so n ≥ ρ_ion. Hence n ≡ ρ_ion. -/
theorem density_constant_max_principle
    (X : Type*) [Nonempty X]
    (n : X → ℝ) (ρ_ion T_infty : ℝ)
    (laplacian : (X → ℝ) → X → ℝ)
    (hn_pos : ∀ x, 0 < n x)
    (hT : 0 < T_infty) (hρ : 0 < ρ_ion)
    (hPB : ∀ x, T_infty * laplacian (Real.log ∘ n) x = n x - ρ_ion)
    (x_max : X) (hmax : ∀ x, n x ≤ n x_max)
    (x_min : X) (hmin : ∀ x, n x_min ≤ n x)
    (hmax_lapl : laplacian (Real.log ∘ n) x_max ≤ 0)
    (hmin_lapl : 0 ≤ laplacian (Real.log ∘ n) x_min) :
    ∀ x, n x = ρ_ion :=
  poisson_boltzmann_max_principle X n ρ_ion T_infty laplacian hn_pos hT hρ hPB
    x_max hmax x_min hmin hmax_lapl hmin_lapl

/-- Corollary 3: The electric field vanishes: E(x) = 0.
    Reference: cor:E_zero

    With u∞ = 0 and ρ constant, ∇a = 0, so force balance gives
    0 = -2c₀ E, and since c₀ ≠ 0, E = 0. -/
theorem electric_field_zero {X : Type*} [FlatTorus3 X] (ss : VMLSteadyState X) :
    ∀ x, ss.E x = 0 := by
  have hb0 := bulk_velocity_zero ss
  intro x
  have hGradA := ss.hGradA_zero hb0 ss.hDensityConst x
  have hfb := ss.hForceBalance x
  rw [hb0, cross_zero_left, add_zero] at hfb
  -- hfb : gradX a_loc x = -(2 * c₀) • E x
  -- hGradA : gradX a_loc x = 0
  rw [hGradA] at hfb
  -- hfb : 0 = -(2 * c₀) • E x
  have hne : -(2 * ss.c₀) ≠ (0 : ℝ) := by nlinarith [ss.hc₀_neg]
  have hsm : -(2 * ss.c₀) • ss.E x = 0 := hfb.symm
  exact (smul_eq_zero.mp hsm).resolve_left hne

/-- On a compact topological space, a continuous real-valued function attains
    its maximum. (Extreme value theorem.) -/
lemma continuous_attains_max {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (g : X → ℝ) (hg : Continuous g) :
    ∃ x_max : X, ∀ x, g x ≤ g x_max := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hg.continuousOn
  exact ⟨x, fun y => hx (Set.mem_univ y)⟩

/-- On a compact topological space, a continuous real-valued function attains
    its minimum. (Extreme value theorem.) -/
lemma continuous_attains_min {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (g : X → ℝ) (hg : Continuous g) :
    ∃ x_min : X, ∀ x, g x_min ≤ g x := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hg.continuousOn
  exact ⟨x, fun y => hx (Set.mem_univ y)⟩

/-- At a global maximum of a function on a FlatTorus3, the Laplacian is non-positive.
    This is a direct consequence of the FlatTorus3 axiom hLaplacianMaxNonpos. -/
lemma laplacian_nonpos_at_max {X : Type*} [FlatTorus3 X]
    (φ : X → ℝ) (hφ : FlatTorus3.IsSpatiallyDiff φ) (x_max : X) (hmax : ∀ x, φ x ≤ φ x_max) :
    FlatTorus3.divX (FlatTorus3.gradX φ) x_max ≤ 0 :=
  FlatTorus3.hLaplacianMaxNonpos φ x_max hφ hmax

/-- At a global minimum of a function on a FlatTorus3, the Laplacian is non-negative.
    This is a direct consequence of the FlatTorus3 axiom hLaplacianMinNonneg. -/
lemma laplacian_nonneg_at_min {X : Type*} [FlatTorus3 X]
    (φ : X → ℝ) (hφ : FlatTorus3.IsSpatiallyDiff φ) (x_min : X) (hmin : ∀ x, φ x_min ≤ φ x) :
    0 ≤ FlatTorus3.divX (FlatTorus3.gradX φ) x_min :=
  FlatTorus3.hLaplacianMinNonneg φ hφ x_min hmin

/-- Poisson-Boltzmann equation from the Vlasov equation (isotropic case).
    When f is locally Maxwellian with b₀ = 0 (zero drift) and spatially constant c₀,
    the force balance gives gradX(a₀) = -(2c₀)E, and since a₀ = log ρ + const
    (by the Gaussian integral), we get T∞ Δ(log ρ) = ρ − ρ_ion via Gauss's law.
    Reference: Lemma 20 (lem:poisson_boltzmann) in H-theorem-formal.tex. -/
private lemma dot_cross_self_zero (v B : Fin 3 → ℝ) :
    dotProduct v (cross v B) = 0 := by
  unfold dotProduct cross
  simp [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const]
  ring

lemma poisson_boltzmann_from_vlasov
    {X : Type*} [FlatTorus3 X]
    (f : X → (Fin 3 → ℝ) → ℝ) (E B : X → (Fin 3 → ℝ))
    (Ψ : ℝ → ℝ) (ν : ℝ)
    (ρ : X → ℝ) (ρ_ion : ℝ)
    (_hf_pos : ∀ x v, 0 < f x v)
    (_hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x))
    (_hf_int : ∀ x, Integrable (f x))
    (_hΨ : ∀ r, 0 < Ψ r)
    (_hρ_def : ∀ x, ρ x = ∫ v, f x v)
    (_hGauss : ∀ x, FlatTorus3.divX E x = ρ x - ρ_ion)
    (_hDiff_fv : ∀ v, FlatTorus3.IsSpatiallyDiff (fun x => f x v))
    (_hVlasov : ∀ x v,
      dotProduct v (FlatTorus3.gradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator Ψ (f x) v) :
    ∀ (c₀ : ℝ), c₀ < 0 →
    -- Isotropic case: b₀ = 0, so f(x,v) = exp(a₀(x) + c₀|v|²)
    (∀ x, ∃ a₀, ∀ v, f x v = Real.exp (a₀ + c₀ * normSq v)) →
    ∀ x, (-1 / (2 * c₀)) * FlatTorus3.divX (FlatTorus3.gradX (Real.log ∘ ρ)) x =
      ρ x - ρ_ion := by
  intro c₀ hc₀ hform
  -- Define a₀ : X → ℝ from the existential
  let a₀ : X → ℝ := fun x => (hform x).choose
  have ha₀ : ∀ x v, f x v = Real.exp (a₀ x + c₀ * normSq v) :=
    fun x => (hform x).choose_spec
  -- a₀ is spatially differentiable: a₀(x) = log(f(x,0)) and f(·,0) is IsSpatiallyDiff
  have ha₀_diff : FlatTorus3.IsSpatiallyDiff a₀ := by
    have ha₀_eq : a₀ = fun x => Real.log (f x 0) := by
      ext x; have h := ha₀ x 0; simp [normSq, Fin.sum_univ_three] at h
      have : a₀ x = Real.log (Real.exp (a₀ x)) := (Real.log_exp _).symm
      rw [this, h]
    rw [ha₀_eq]
    exact FlatTorus3.hDiff_log _ (_hDiff_fv 0) (fun x => _hf_pos x 0)
  -- Isotropic form with b=0 for nullspace_sufficiency
  have ha₀_b0 : ∀ x v, f x v =
      Real.exp (a₀ x + dotProduct 0 v + c₀ * normSq v) := fun x v => by
    rw [ha₀ x v]; simp [dotProduct, Fin.sum_univ_three, normSq]
  -- Step 1: Q(f(x,·)) = 0 for all x (isotropic Maxwellian in nullspace, b=0)
  have hQ : ∀ x v, LandauOperator Ψ (f x) v = 0 := fun x =>
    nullspace_sufficiency Ψ (f x) (a₀ x) 0 c₀ hc₀ (ha₀_b0 x)
  -- Step 2: Vlasov reduces to collisionless transport
  have hTransport : ∀ x v,
      dotProduct v (FlatTorus3.gradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) = 0 := by
    intro x v; have h := _hVlasov x v; rw [hQ x v, mul_zero] at h; exact h
  -- Step 3: Compute vGrad(f(x,·))(v) = f(x,v) • 2c₀v (isotropic: b=0)
  have hvGrad : ∀ x v, vGrad (f x) v = f x v • ((2 * c₀) • v) := by
    intro x v
    have h1 := vGrad_exp_quadratic (a₀ x) 0 c₀ v
    conv_lhs => rw [show f x = (fun w => Real.exp (a₀ x + dotProduct 0 w + c₀ * normSq w))
      from funext (ha₀_b0 x)]
    rw [h1]; congr 1
    · exact (ha₀_b0 x v).symm
    · simp
  -- Step 4: Compute gradX(f(·,v))(x)(i) = f(x,v) * gradX(a₀)(x)(i)
  have hgradX : ∀ x v i, FlatTorus3.gradX (fun y => f y v) x i =
      f x v * FlatTorus3.gradX a₀ x i := by
    intro x v i
    have hf_eq : (fun y => f y v) = (fun y => Real.exp (a₀ y + c₀ * normSq v)) :=
      funext (fun y => ha₀ y v)
    rw [hf_eq, FlatTorus3.hGradChainExp _ (FlatTorus3.hDiff_add _ _ ha₀_diff (FlatTorus3.hDiff_const _)),
        FlatTorus3.hGradAddConst _ ha₀_diff]
    simp [ha₀ x v]
  -- Step 5: Force balance: gradX(a₀) = -(2c₀) E
  have hForce : ∀ x, FlatTorus3.gradX a₀ x = (-2 * c₀) • E x := by
    intro x
    -- Show v · [gradX(a₀) + 2c₀ E] = 0 for all v
    suffices hzero : FlatTorus3.gradX a₀ x + (2 * c₀) • E x = 0 by
      ext i; have hi := congr_fun hzero i
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢; linarith
    exact (poly_linear_extraction _ 0 (fun v => by
      -- Transport: f(x,v) · [v · gradX(a₀) + 2c₀(E+v×B)·v] = 0, f > 0, (v×B)·v = 0
      have ht := hTransport x v
      have hg : dotProduct v (FlatTorus3.gradX (fun y => f y v) x) =
          f x v * dotProduct v (FlatTorus3.gradX a₀ x) := by
        unfold dotProduct; simp_rw [Fin.sum_univ_three, hgradX x v]; ring
      have hv : dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
          f x v * ((2 * c₀) * dotProduct v (E x) +
            (2 * c₀) * dotProduct (cross v (B x)) v) := by
        rw [hvGrad x v]; unfold dotProduct
        simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Fin.sum_univ_three]; ring
      rw [hg, hv] at ht
      have hfv_ne : f x v ≠ 0 := ne_of_gt (_hf_pos x v)
      have hfact : f x v * (v ⬝ᵥ FlatTorus3.gradX a₀ x +
          (2 * c₀ * v ⬝ᵥ E x + 2 * c₀ * cross v (B x) ⬝ᵥ v)) = 0 := by linarith
      have hdp := (mul_eq_zero.mp hfact).resolve_left hfv_ne
      have hcross : dotProduct (cross v (B x)) v = 0 := by
        rw [dotProduct_comm]; exact dot_cross_self_zero v (B x)
      simp only [hcross, mul_zero, add_zero] at hdp
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
      linarith)).1
  -- Step 6: gradX(log ∘ ρ) = gradX(a₀)
  -- ρ(x) = exp(a₀(x)) * C, so log(ρ) = a₀ + log(C), gradient of constant = 0
  have hGradLogRho : ∀ x, FlatTorus3.gradX (Real.log ∘ ρ) x = FlatTorus3.gradX a₀ x := by
    set C := ∫ v : Fin 3 → ℝ, Real.exp (c₀ * normSq v) with hC_def
    have hρ_eq : ∀ y, ρ y = Real.exp (a₀ y) * C := by
      intro y; rw [_hρ_def y]
      simp_rw [ha₀ y, Real.exp_add]
      exact MeasureTheory.integral_mul_left _ _
    have hρ_pos : ∀ y, 0 < ρ y := fun y => by
      rw [_hρ_def y]; exact density_positive_of_integral (f y) (_hf_pos y) (_hf_int y)
    intro x
    -- C > 0 (from ρ(x) = exp(a₀ x) * C > 0 and exp > 0)
    have hC_pos : 0 < C := by
      have h := hρ_pos x; rw [hρ_eq x] at h
      rcases mul_pos_iff.mp h with ⟨_, hc⟩ | ⟨hexp_neg, _⟩
      · exact hc
      · exact absurd hexp_neg (not_lt_of_gt (Real.exp_pos _))
    -- log(ρ(y)) = a₀(y) + log(C) for all y
    have hlog_eq : Real.log ∘ ρ = fun y => a₀ y + Real.log C := funext (fun y => by
      show Real.log (ρ y) = a₀ y + Real.log C
      rw [hρ_eq y, Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hC_pos), Real.log_exp])
    -- gradX(log ∘ ρ) = gradX(a₀ + const) = gradX(a₀) by hGradAddConst
    rw [hlog_eq, FlatTorus3.hGradAddConst _ ha₀_diff]
  -- Step 7: Apply poisson_boltzmann_algebraic
  exact poisson_boltzmann_algebraic FlatTorus3.gradX FlatTorus3.divX E ρ ρ_ion
    a₀ c₀ hc₀ hForce hGradLogRho _hGauss FlatTorus3.hDivLinear

end VML
