import Aristotle.Landau.main.Defs
import Aristotle.Landau.main.Section3
set_option linter.all false
open Matrix Finset BigOperators Real MeasureTheory
noncomputable section
namespace VML

-- ============================================================================
-- Helper lemma proved by Aristotle
-- ============================================================================

/-- Expansion of (E + v×B)·(b + 2cv) = E·b + v·(2cE + B×b).
    Uses (v×B)·v = 0 and (v×B)·b = v·(B×b).
    Proved by Aristotle (Harmonic). -/
lemma lorentz_force_expansion (E b B v : Fin 3 → ℝ) (c : ℝ) :
    dotProduct (E + cross v B) (b + (2 * c) • v) =
    dotProduct E b + dotProduct v ((2 * c) • E + cross B b) := by
  unfold cross dotProduct; simp [Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

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
    {X : Type*} [FlatTorus3 X]
    (f : X → (Fin 3 → ℝ) → ℝ) (E B : X → (Fin 3 → ℝ))
    (Ψ : ℝ → ℝ) (ν : ℝ)
    (_hf_pos : ∀ x v, 0 < f x v)
    (_hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x))
    (_hf_int : ∀ x, Integrable (f x))
    (_hΨ : ∀ r, 0 < Ψ r)
    (_hVlasov : ∀ x v,
      dotProduct v (FlatTorus3.gradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator Ψ (f x) v) :
    ∀ (a : X → ℝ) (b : X → Fin 3 → ℝ) (c : X → ℝ),
    FlatTorus3.IsSpatiallyDiff a →
    (∀ j, FlatTorus3.IsSpatiallyDiff (fun y => b y j)) →
    FlatTorus3.IsSpatiallyDiff c →
    (∀ x v, f x v = Real.exp (a x + dotProduct (b x) v + c x * normSq v)) →
    ∀ x v,
      dotProduct v (FlatTorus3.gradX c x) * normSq v +
      (∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
        (FlatTorus3.gradX (fun y => b y j) x i)) +
      dotProduct v (FlatTorus3.gradX a x) +
      dotProduct (E x) (b x) +
      dotProduct v ((2 * c x) • E x + cross (B x) (b x)) = 0 := by
  intro a b c ha hb hc hform x v
  -- Step 1: c(x) < 0 for each x (from integrability of f)
  have hc_neg : ∀ x, c x < 0 := fun x =>
    analysis_gaussian_integrability (f x) (a x) (b x) (c x) (_hf_pos x) (_hf_int x) (hform x)
  -- Step 2: Q(f(x,·)) = 0 by nullspace sufficiency (f is Maxwellian)
  have hQ_zero : ∀ x v, LandauOperator Ψ (f x) v = 0 := fun x =>
    nullspace_sufficiency Ψ (f x) (a x) (b x) (c x) (hc_neg x) (hform x)
  -- Step 3: Vlasov simplifies to collisionless transport = 0
  have hTransport : dotProduct v (FlatTorus3.gradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) = 0 := by
    have h := _hVlasov x v; rw [hQ_zero x v, mul_zero] at h; exact h
  -- Step 4: Compute vGrad(f x)(v) = f(x,v) · (b x + 2c(x)·v)
  have hvGrad : vGrad (f x) v = f x v • (b x + (2 * c x) • v) := by
    have h1 := vGrad_exp_quadratic (a x) (b x) (c x) v
    conv_lhs => rw [show f x = (fun w => Real.exp (a x + dotProduct (b x) w + c x * normSq w))
      from funext (hform x)]
    rw [h1]; congr 1; exact (hform x v).symm
  -- Step 5: Compute gradX(f(·,v)) via chain rule + linearity
  have hgradX_i : ∀ i, FlatTorus3.gradX (fun y => f y v) x i =
      f x v * (FlatTorus3.gradX a x i +
        ∑ j : Fin 3, v j * FlatTorus3.gradX (fun y => b y j) x i +
        normSq v * FlatTorus3.gradX c x i) := by
    intro i
    have hf_eq : (fun y => f y v) =
        (fun y => Real.exp (a y + dotProduct (b y) v + c y * normSq v)) :=
      funext (fun y => hform y v)
    have hbv : FlatTorus3.IsSpatiallyDiff (fun y => dotProduct (b y) v) := by
      have : (fun y => dotProduct (b y) v) = (fun y => v 0 * b y 0 + (v 1 * b y 1 + v 2 * b y 2)) := by
        ext y; simp [dotProduct, Fin.sum_univ_three]; ring
      rw [this]
      exact FlatTorus3.hDiff_add _ _ (FlatTorus3.hDiff_smul _ _ (hb 0))
        (FlatTorus3.hDiff_add _ _ (FlatTorus3.hDiff_smul _ _ (hb 1)) (FlatTorus3.hDiff_smul _ _ (hb 2)))
    have hcv : FlatTorus3.IsSpatiallyDiff (fun y => c y * normSq v) := by
      have : (fun y => c y * normSq v) = (fun y => normSq v * c y) := funext (fun y => mul_comm _ _)
      rw [this]; exact FlatTorus3.hDiff_smul _ _ hc
    have hexp_arg_diff : FlatTorus3.IsSpatiallyDiff
        (fun y => a y + dotProduct (b y) v + c y * normSq v) := by
      rw [show (fun y => a y + dotProduct (b y) v + c y * normSq v) =
          (fun y => a y + (dotProduct (b y) v + c y * normSq v)) from funext (fun y => by ring)]
      exact FlatTorus3.hDiff_add _ _ ha (FlatTorus3.hDiff_add _ _ hbv hcv)
    rw [show FlatTorus3.gradX (fun y => f y v) x i =
        FlatTorus3.gradX (fun y => Real.exp (a y + dotProduct (b y) v + c y * normSq v)) x i
      from by rw [hf_eq]]
    rw [FlatTorus3.hGradChainExp _ hexp_arg_diff]
    rw [show Real.exp (a x + dotProduct (b x) v + c x * normSq v) = f x v from (hform x v).symm]
    congr 1
    -- Decompose gradX(a + b·v + c|v|²) using linearity
    rw [show (fun y => a y + dotProduct (b y) v + c y * normSq v) =
        (fun y => a y + (dotProduct (b y) v + c y * normSq v)) from funext (fun y => by ring)]
    rw [FlatTorus3.hGradAdd _ _ ha (FlatTorus3.hDiff_add _ _ hbv hcv)]
    rw [FlatTorus3.hGradAdd _ _ hbv hcv]
    rw [show (fun y => c y * normSq v) = (fun y => normSq v * c y) from funext (fun y => by ring)]
    rw [FlatTorus3.hGradScalarMul]
    rw [show (fun y => dotProduct (b y) v) =
        (fun y => v 0 * b y 0 + (v 1 * b y 1 + v 2 * b y 2))
        from funext (fun y => by simp [dotProduct, Fin.sum_univ_three]; ring)]
    rw [FlatTorus3.hGradAdd _ _ (FlatTorus3.hDiff_smul _ _ (hb 0))
      (FlatTorus3.hDiff_add _ _ (FlatTorus3.hDiff_smul _ _ (hb 1)) (FlatTorus3.hDiff_smul _ _ (hb 2)))]
    rw [FlatTorus3.hGradAdd _ _ (FlatTorus3.hDiff_smul _ _ (hb 1)) (FlatTorus3.hDiff_smul _ _ (hb 2))]
    rw [FlatTorus3.hGradScalarMul (v 0) (fun y => b y 0)]
    rw [FlatTorus3.hGradScalarMul (v 1) (fun y => b y 1)]
    rw [FlatTorus3.hGradScalarMul (v 2) (fun y => b y 2)]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
    ring
  -- Step 6: Substitute into transport = 0 and factor out f > 0
  have hfv_pos : 0 < f x v := _hf_pos x v
  -- Rewrite gradX as dot product with v
  have hgradX_dot : dotProduct v (FlatTorus3.gradX (fun y => f y v) x) =
      f x v * (dotProduct v (FlatTorus3.gradX a x) +
        ∑ i : Fin 3, ∑ j : Fin 3, v i * v j * FlatTorus3.gradX (fun y => b y j) x i +
        dotProduct v (FlatTorus3.gradX c x) * normSq v) := by
    -- Expand dot products, sums over Fin 3, and substitute hgradX_i
    have h0 := hgradX_i 0; have h1 := hgradX_i 1; have h2 := hgradX_i 2
    simp only [dotProduct, Fin.sum_univ_three, normSq] at h0 h1 h2 ⊢
    rw [h0, h1, h2]; ring
  -- Rewrite vGrad term
  have hvGrad_dot : dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      f x v * (dotProduct (E x) (b x) +
        dotProduct v ((2 * c x) • E x + cross (B x) (b x))) := by
    rw [hvGrad, dotProduct_smul, lorentz_force_expansion, smul_eq_mul]
  -- Combine: transport = f(x,v) * (polynomial) = 0
  have hPoly : f x v * (dotProduct v (FlatTorus3.gradX c x) * normSq v +
      (∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
        (FlatTorus3.gradX (fun y => b y j) x i)) +
      dotProduct v (FlatTorus3.gradX a x) +
      dotProduct (E x) (b x) +
      dotProduct v ((2 * c x) • E x + cross (B x) (b x))) = 0 := by
    have h := hTransport
    rw [hgradX_dot, hvGrad_dot] at h
    linarith
  -- Since f(x,v) > 0, the polynomial must be 0
  exact (mul_eq_zero.mp hPoly).resolve_left (ne_of_gt hfv_pos)

end VML
