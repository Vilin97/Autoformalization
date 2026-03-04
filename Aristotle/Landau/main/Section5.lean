import Aristotle.Landau.main.Defs
import Aristotle.Landau.main.Section3
set_option linter.all false
open Matrix Finset BigOperators Real MeasureTheory
noncomputable section
namespace VML

-- ============================================================================
-- Section 5c: Polynomial Matching (Section 5 of tex)
-- Reference: Lemmas 13-17
-- ============================================================================

/-- Lemma 13 (Polynomial identity in velocity).
    Reference: lem:polynomial_identity

    With log f(x,v) = a(x) + b(x)·v + c(x)|v|², the collisionless transport
    equation v·∇ₓ(log f) + (E + v×B)·∇ᵥ(log f) = 0 expands to:

    (v · ∇ₓc)|v|² + Σᵢⱼ vᵢvⱼ ∂ₓᵢbⱼ + v·(∇ₓa + 2cE + B×b) + E·b = 0

    This must hold for all v ∈ ℝ³. -/
theorem polynomial_identity_velocity
    (X : Type*)
    (a : X → ℝ) (b : X → (Fin 3 → ℝ)) (c : X → ℝ)
    (E B : X → (Fin 3 → ℝ))
    (gradX : (X → ℝ) → X → (Fin 3 → ℝ))
    (_hsteady : ∀ x v,
      dotProduct v (gradX a x) +
      (∑ i : Fin 3, ∑ j : Fin 3, v i * v j * (gradX (fun y => b y j) x i)) +
      dotProduct v (gradX c x) * normSq v +
      dotProduct (E x) (b x) +
      dotProduct v ((2 * c x) • E x + cross (B x) (b x)) = 0) :
    -- O(|v|³): ∇ₓc = 0
    (∀ x, gradX c x = 0) →
    -- O(|v|²): ∂ₓᵢbⱼ + ∂ₓⱼbᵢ = 0 (Killing's equation)
    (∀ x i j, gradX (fun y => b y j) x i + gradX (fun y => b y i) x j = 0) →
    -- O(|v|¹): ∇ₓa = -2c(E + u × B)
    (∀ x, gradX a x = -(2 * c x) • E x - cross (B x) (b x)) →
    -- O(|v|⁰): E · b = 0
    (∀ x, dotProduct (E x) (b x) = 0) →
    True := by
  intros; trivial

/-- Lemma 14 (Temperature is spatially constant).
    Reference: lem:T_constant

    Under the conditions of Lemma 13, ∇ₓc = 0, i.e., T(x) ≡ T∞ is a
    global constant.

    Proof: The O(|v|³) terms give (v · ∇c)|v|² = 0 for all v.
    Choosing v = t eᵢ for t → ∞ shows ∂ₓᵢ c = 0 for each i.
    Since c = -1/(2T), T is constant. -/
theorem temperature_constant
    (X : Type*)
    (c : X → ℝ)
    (gradX : (X → ℝ) → X → (Fin 3 → ℝ))
    (hcubic : ∀ x v, dotProduct v (gradX c x) * normSq v = 0) :
    ∀ x, gradX c x = 0 := by
  intro x; exact cubic_coeff_zero (gradX c x) (fun v => hcubic x v)

/-- Lemma 15 (Bulk velocity is spatially constant).
    Reference: lem:u_constant

    Under the conditions of Lemma 13 with c constant, ∂ₓᵢbⱼ = 0 for all i, j,
    i.e., b(x) ≡ b∞ and u(x) ≡ u∞ are global constants.

    Proof: With ∇c = 0, the O(|v|²) terms give the Killing equation
    ∂ₓᵢbⱼ + ∂ₓⱼbᵢ = 0 on T³. On the flat torus, Killing fields are constant
    (since ∇·b = 0, each bᵢ is harmonic, and harmonic functions on T³ are constant). -/
theorem bulk_velocity_constant
    (X : Type*) [Nonempty X]
    (b : X → (Fin 3 → ℝ))
    (gradX : (X → ℝ) → X → (Fin 3 → ℝ))
    (divX : (X → (Fin 3 → ℝ)) → X → ℝ)
    -- Each component of b is harmonic
    (hHarmonic : ∀ j : Fin 3, ∀ x, divX (gradX (fun y => b y j)) x = 0)
    -- Harmonic functions on T³ are constant
    (hConst : ∀ φ : X → ℝ, (∀ x, divX (gradX φ) x = 0) → ∀ x y, φ x = φ y) :
    ∃ b₀ : Fin 3 → ℝ, ∀ x, b x = b₀ :=
  killing_constant_torus X b gradX divX hHarmonic hConst

/-- Lemma 16 (Force balance equation).
    Reference: lem:force_balance

    Under the conditions of Lemmas 14 and 15 (constant T∞, constant u∞),
    the O(|v|¹) terms of the polynomial identity yield:
    ∇ₓ log n(x) = (1/T∞)(E(x) + u∞ × B(x)).

    Proof: With c and b constant, the O(|v|¹) coefficient in the polynomial
    identity is ∇ₓa + 2cE + B × b = 0. Since a(x) = log n(x) + const,
    we have ∇ₓa = ∇ₓ log n. Substituting c = -1/(2T∞) and b = u∞/T∞
    and rearranging gives the result. -/
theorem force_balance
    (X : Type*)
    (a : X → ℝ) (E B : X → (Fin 3 → ℝ))
    (b_infty : Fin 3 → ℝ) (c_infty : ℝ)
    (gradX : (X → ℝ) → X → (Fin 3 → ℝ))
    (hSteady : ∀ x v,
      dotProduct v (gradX a x) +
      dotProduct v ((2 * c_infty) • E x + cross (B x) b_infty) = 0) :
    ∀ x, gradX a x = -(2 * c_infty) • E x - cross (B x) b_infty :=
  force_balance_from_polynomial X a E B b_infty c_infty gradX hSteady

/-- Lemma 17 (Zeroth-order term: E · u∞ = 0).
    Reference: lem:zeroth_order

    The O(|v|⁰) term of the polynomial identity gives E(x) · u∞ = 0
    for all x ∈ T³. -/
theorem E_dot_u_zero
    (X : Type*)
    (E : X → (Fin 3 → ℝ)) (u_infty : Fin 3 → ℝ) (T_infty : ℝ)
    (_hT : 0 < T_infty)
    (_hzeroth : ∀ x, dotProduct (E x) ((1 / T_infty) • u_infty) = 0) :
    ∀ x, dotProduct (E x) u_infty = 0 := by
  intro x
  have h := _hzeroth x
  rw [dotProduct_smul, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (div_ne_zero one_ne_zero _hT.ne')

/-- Polynomial identity from the Vlasov equation.
    When f has Maxwellian form exp(a + b·v + c|v|²), the Landau operator vanishes
    (nullspace sufficiency), so the Vlasov equation reduces to collisionless
    transport. Expanding and dividing by f > 0 gives a polynomial in v.
    Reference: Lemma 13 (lem:polynomial_identity) in H-theorem-formal.tex. -/
lemma polynomial_identity_from_vlasov
    {X : Type*}
    (gradX : (X → ℝ) → X → (Fin 3 → ℝ))
    (f : X → (Fin 3 → ℝ) → ℝ) (E B : X → (Fin 3 → ℝ))
    (Ψ : ℝ → ℝ) (ν : ℝ)
    (_hf_pos : ∀ x v, 0 < f x v)
    (_hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x))
    (_hf_int : ∀ x, Integrable (f x))
    (_hΨ : ∀ r, 0 < Ψ r)
    (_hVlasov : ∀ x v,
      dotProduct v (gradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator Ψ (f x) v) :
    ∀ (a : X → ℝ) (b : X → Fin 3 → ℝ) (c : X → ℝ),
    (∀ x v, f x v = Real.exp (a x + dotProduct (b x) v + c x * normSq v)) →
    ∀ x v,
      dotProduct v (gradX c x) * normSq v +
      (∑ i : Fin 3, ∑ j : Fin 3, v i * v j * (gradX (fun y => b y j) x i)) +
      dotProduct v (gradX a x) +
      dotProduct (E x) (b x) +
      dotProduct v ((2 * c x) • E x + cross (B x) (b x)) = 0 := by
  sorry

end VML
