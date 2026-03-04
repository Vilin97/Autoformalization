import Aristotle.Landau.main.Defs
import Aristotle.Landau.main.Section3
import Aristotle.Landau.main.Section6
set_option linter.all false
open Matrix Finset BigOperators Real MeasureTheory
noncomputable section
namespace VML

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
theorem electric_field_zero (ss : VMLSteadyState) : ∀ x, ss.E x = 0 := by
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

/-- At a global maximum of a smooth function on a Riemannian manifold,
    the Laplacian is non-positive. (Second derivative test.) -/
lemma laplacian_nonpos_at_max {X : Type*}
    (divX : (X → (Fin 3 → ℝ)) → X → ℝ)
    (gradX : (X → ℝ) → X → (Fin 3 → ℝ))
    (φ : X → ℝ) (x_max : X) (hmax : ∀ x, φ x ≤ φ x_max) :
    divX (gradX φ) x_max ≤ 0 := by
  sorry

/-- At a global minimum of a smooth function on a Riemannian manifold,
    the Laplacian is non-negative. (Second derivative test.) -/
lemma laplacian_nonneg_at_min {X : Type*}
    (divX : (X → (Fin 3 → ℝ)) → X → ℝ)
    (gradX : (X → ℝ) → X → (Fin 3 → ℝ))
    (φ : X → ℝ) (x_min : X) (hmin : ∀ x, φ x_min ≤ φ x) :
    0 ≤ divX (gradX φ) x_min := by
  sorry

/-- Poisson-Boltzmann equation from the Vlasov equation.
    When f is locally Maxwellian with spatially constant c₀, combining the
    force balance (from the polynomial identity) with Gauss's law gives
    T∞ Δ(log ρ) = ρ − ρ_ion, where T∞ = −1/(2c₀).
    Reference: Lemma 20 (lem:poisson_boltzmann) in H-theorem-formal.tex. -/
lemma poisson_boltzmann_from_vlasov
    {X : Type*}
    (gradX : (X → ℝ) → X → (Fin 3 → ℝ))
    (divX : (X → (Fin 3 → ℝ)) → X → ℝ)
    (f : X → (Fin 3 → ℝ) → ℝ) (E B : X → (Fin 3 → ℝ))
    (Ψ : ℝ → ℝ) (ν : ℝ)
    (ρ : X → ℝ) (ρ_ion : ℝ)
    (_hf_pos : ∀ x v, 0 < f x v)
    (_hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x))
    (_hf_int : ∀ x, Integrable (f x))
    (_hΨ : ∀ r, 0 < Ψ r)
    (_hρ_def : ∀ x, ρ x = ∫ v, f x v)
    (_hGauss : ∀ x, divX E x = ρ x - ρ_ion)
    (_hDivLinear : ∀ (α : ℝ) (G : X → (Fin 3 → ℝ)),
      ∀ x, divX (fun y => α • G y) x = α * divX G x)
    (_hVlasov : ∀ x v,
      dotProduct v (gradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator Ψ (f x) v) :
    ∀ (c₀ : ℝ), c₀ < 0 →
    (∀ x, ∃ a₀ b₀, ∀ v, f x v = Real.exp (a₀ + dotProduct b₀ v + c₀ * normSq v)) →
    ∀ x, (-1 / (2 * c₀)) * divX (gradX (Real.log ∘ ρ)) x = ρ x - ρ_ion := by
  sorry

end VML
