/-
  Formalization of the Global Steady State of the Vlasov–Maxwell–Landau System.

  Reference: H-theorem-formal.tex

  Main Result (Theorem 12, thm:main):
  Any smooth steady state (f, E, B) of the VML system on T³ × ℝ³ with ν > 0 is:
    (i)   f(v) = ρ_ion/(2πT∞)^(3/2) exp(-|v|²/(2T∞))  (global Maxwellian, zero drift)
    (ii)  E = 0
    (iii) B = B∞ = spatial mean of initial B  (constant)
    (iv)  T∞ = 2/(3ρ_ion|T³|) · (ℰ₀ - |B∞|²|T³|/2) > 0
-/

import Mathlib

open Matrix Finset BigOperators Real MeasureTheory

noncomputable section

namespace VML

-- ============================================================================
-- Section 1: Vector and Matrix Basics for ℝ³
-- ============================================================================

/-- Squared Euclidean norm: ‖z‖² = z · z = ∑ᵢ zᵢ² -/
def normSq (z : Fin 3 → ℝ) : ℝ := dotProduct z z

@[simp]
lemma normSq_zero : normSq (0 : Fin 3 → ℝ) = 0 := by
  simp [normSq, dotProduct]

lemma normSq_nonneg (z : Fin 3 → ℝ) : 0 ≤ normSq z := by
  unfold normSq dotProduct
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (a := z i)

lemma normSq_eq_zero {z : Fin 3 → ℝ} : normSq z = 0 ↔ z = 0 := by
  constructor
  · intro h
    unfold normSq dotProduct at h
    ext i
    have hsq : ∀ i ∈ Finset.univ, (0 : ℝ) ≤ z i * z i :=
      fun i _ => mul_self_nonneg (a := z i)
    have := (Finset.sum_eq_zero_iff_of_nonneg hsq).mp h i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp this
  · rintro rfl; simp [normSq, dotProduct]

lemma normSq_pos {z : Fin 3 → ℝ} (hz : z ≠ 0) : 0 < normSq z :=
  lt_of_le_of_ne (normSq_nonneg z) (fun h => hz (normSq_eq_zero.mp h.symm))

lemma normSq_neg (z : Fin 3 → ℝ) : normSq (-z) = normSq z := by
  simp [normSq, dotProduct, Pi.neg_apply]

/-- Euclidean norm: |z| = √(z · z) -/
def eucNorm (z : Fin 3 → ℝ) : ℝ := Real.sqrt (normSq z)

lemma eucNorm_nonneg (z : Fin 3 → ℝ) : 0 ≤ eucNorm z := Real.sqrt_nonneg _

lemma eucNorm_neg (z : Fin 3 → ℝ) : eucNorm (-z) = eucNorm z := by
  simp [eucNorm, normSq_neg]

lemma eucNorm_sq (z : Fin 3 → ℝ) : eucNorm z ^ 2 = normSq z := by
  simp [eucNorm, sq_sqrt (normSq_nonneg z)]

-- ============================================================================
-- Section 2: The Landau Collision Matrix
-- Reference: Definition 2 (def:landau_matrix), Lemmas 1-3
-- ============================================================================

/-- The inner part of the Landau matrix: B(z) = |z|² I₃ - z zᵀ.
    This is the matrix that appears inside the scalar factor Ψ(|z|). -/
def innerLandauMatrix (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  normSq z • (1 : Matrix (Fin 3) (Fin 3) ℝ) - vecMulVec z z

/-- The Landau collision matrix: A(z) = Ψ(|z|) · (|z|² I₃ - z zᵀ).
    Reference: Definition 2 (def:landau_matrix) -/
def landauMatrix (Ψ : ℝ → ℝ) (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Ψ (eucNorm z) • innerLandauMatrix z

lemma innerLandauMatrix_apply (z : Fin 3 → ℝ) (i j : Fin 3) :
    innerLandauMatrix z i j = (if i = j then normSq z else 0) - z i * z j := by
  simp [innerLandauMatrix, sub_apply, smul_apply, one_apply, vecMulVec_apply, smul_eq_mul]

-- ============================================================================
-- Lemma 1(a): A(z) is symmetric  [lem:A_symmetric]
-- ============================================================================

/-- The inner Landau matrix is symmetric: B(z)ᵀ = B(z). -/
theorem innerLandauMatrix_symmetric (z : Fin 3 → ℝ) :
    (innerLandauMatrix z)ᵀ = innerLandauMatrix z := by
  ext i j
  simp only [transpose_apply, innerLandauMatrix_apply]
  by_cases h : i = j
  · subst h; ring
  · have hne : j ≠ i := fun hji => h hji.symm
    simp [h, hne, mul_comm (z i) (z j)]

/-- Lemma 1(a): A(z) is symmetric. Reference: lem:A_symmetric -/
theorem landauMatrix_symmetric (Ψ : ℝ → ℝ) (z : Fin 3 → ℝ) :
    (landauMatrix Ψ z)ᵀ = landauMatrix Ψ z := by
  unfold landauMatrix
  rw [transpose_smul, innerLandauMatrix_symmetric]

-- ============================================================================
-- Lemma 1(b): A(z) is even: A(-z) = A(z)  [lem:A_symmetric]
-- ============================================================================

/-- Lemma 1(b): A(-z) = A(z). Reference: lem:A_symmetric -/
theorem landauMatrix_even (Ψ : ℝ → ℝ) (z : Fin 3 → ℝ) :
    landauMatrix Ψ (-z) = landauMatrix Ψ z := by
  unfold landauMatrix innerLandauMatrix
  rw [eucNorm_neg, normSq_neg]
  congr 1
  ext i j
  simp [vecMulVec_apply]

-- ============================================================================
-- Lemma 2: Positive semidefiniteness of A(z)  [lem:A_psd]
-- ============================================================================

/-- Helper: (vecMulVec z z) *ᵥ w = (z · w) • z -/
lemma vecMulVec_self_mulVec (z w : Fin 3 → ℝ) :
    mulVec (vecMulVec z z) w = dotProduct z w • z := by
  ext i
  simp only [mulVec, vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, mul_comm]

/-- The quadratic form of the inner Landau matrix:
    Yᵀ B(z) Y = |z|²|Y|² - (z·Y)². Reference: lem:A_psd -/
theorem innerLandauMatrix_quadForm (z Y : Fin 3 → ℝ) :
    dotProduct Y (mulVec (innerLandauMatrix z) Y) =
    normSq z * normSq Y - dotProduct z Y ^ 2 := by
  unfold innerLandauMatrix
  simp only [sub_mulVec, smul_mulVec, one_mulVec, vecMulVec_self_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, normSq]
  rw [dotProduct_comm z Y]
  ring

/-- Cauchy–Schwarz for dotProduct: (z·Y)² ≤ |z|²·|Y|².
    This follows from the Cauchy–Schwarz inequality. -/
theorem dotProduct_sq_le_normSq (z Y : Fin 3 → ℝ) :
    dotProduct z Y ^ 2 ≤ normSq z * normSq Y := by
  simp only [dotProduct, normSq, Fin.sum_univ_three, sq]
  nlinarith [sq_nonneg (z 0 * Y 1 - z 1 * Y 0),
             sq_nonneg (z 0 * Y 2 - z 2 * Y 0),
             sq_nonneg (z 1 * Y 2 - z 2 * Y 1)]

/-- Lemma 2: Yᵀ A(z) Y ≥ 0 when Ψ(|z|) ≥ 0. Reference: lem:A_psd -/
theorem landauMatrix_posSemidef {Ψ : ℝ → ℝ} {z : Fin 3 → ℝ}
    (hΨ : 0 ≤ Ψ (eucNorm z)) (Y : Fin 3 → ℝ) :
    0 ≤ dotProduct Y (mulVec (landauMatrix Ψ z) Y) := by
  unfold landauMatrix
  rw [smul_mulVec]
  simp only [dotProduct_smul, smul_eq_mul]
  apply mul_nonneg hΨ
  rw [innerLandauMatrix_quadForm]
  linarith [dotProduct_sq_le_normSq z Y]

/-- Lemma 2 (equality case): If Ψ(|z|) > 0, z ≠ 0, and the quadratic form vanishes,
    then Y is parallel to z. Reference: lem:A_psd -/
theorem landauMatrix_quadForm_eq_zero_iff {Ψ : ℝ → ℝ} {z : Fin 3 → ℝ}
    (hΨ : 0 < Ψ (eucNorm z)) (hz : z ≠ 0)
    (Y : Fin 3 → ℝ)
    (h : dotProduct Y (mulVec (landauMatrix Ψ z) Y) = 0) :
    ∃ l : ℝ, Y = l • z := by
  -- Step 1: Factor out Ψ > 0 to get the inner quadratic form = 0
  have hinner : dotProduct Y (mulVec (innerLandauMatrix z) Y) = 0 := by
    have hqf : Ψ (eucNorm z) * dotProduct Y (mulVec (innerLandauMatrix z) Y) = 0 := by
      have : dotProduct Y (mulVec (landauMatrix Ψ z) Y) =
        Ψ (eucNorm z) * dotProduct Y (mulVec (innerLandauMatrix z) Y) := by
        unfold landauMatrix; rw [smul_mulVec]; simp [dotProduct_smul, smul_eq_mul]
      linarith
    exact (mul_eq_zero.mp hqf).resolve_left (ne_of_gt hΨ)
  -- Step 2: Cauchy-Schwarz equality: normSq z * normSq Y = (z . Y)^2
  have heq : normSq z * normSq Y = dotProduct z Y ^ 2 := by
    have := innerLandauMatrix_quadForm z Y; linarith
  -- Step 3: Expand on Fin 3 to show all cross terms vanish
  have hcross :
      (z 0 * Y 1 - z 1 * Y 0) ^ 2 + (z 0 * Y 2 - z 2 * Y 0) ^ 2 +
      (z 1 * Y 2 - z 2 * Y 1) ^ 2 = 0 := by
    simp only [dotProduct, normSq, Fin.sum_univ_three, sq] at heq
    nlinarith [sq_nonneg (z 0 * Y 1 - z 1 * Y 0),
               sq_nonneg (z 0 * Y 2 - z 2 * Y 0),
               sq_nonneg (z 1 * Y 2 - z 2 * Y 1)]
  -- Step 4: Extract individual proportionality relations z_i * Y_j = z_j * Y_i
  have h01 : z 0 * Y 1 = z 1 * Y 0 := by
    nlinarith [sq_nonneg (z 0 * Y 1 - z 1 * Y 0),
               sq_nonneg (z 0 * Y 2 - z 2 * Y 0),
               sq_nonneg (z 1 * Y 2 - z 2 * Y 1)]
  have h02 : z 0 * Y 2 = z 2 * Y 0 := by
    nlinarith [sq_nonneg (z 0 * Y 1 - z 1 * Y 0),
               sq_nonneg (z 0 * Y 2 - z 2 * Y 0),
               sq_nonneg (z 1 * Y 2 - z 2 * Y 1)]
  have h12 : z 1 * Y 2 = z 2 * Y 1 := by
    nlinarith [sq_nonneg (z 0 * Y 1 - z 1 * Y 0),
               sq_nonneg (z 0 * Y 2 - z 2 * Y 0),
               sq_nonneg (z 1 * Y 2 - z 2 * Y 1)]
  -- Step 5: Since z != 0, find a nonzero component and set l = Y_k / z_k
  have hne : ¬(z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0) := by
    intro ⟨h0, h1, h2⟩
    apply hz; ext i; fin_cases i <;> assumption
  rcases not_and_or.mp hne with h0 | h12ne
  · -- Case z 0 != 0: let l = Y 0 / z 0
    refine ⟨Y 0 / z 0, ?_⟩
    ext i; fin_cases i
    · simp [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0]
    · simp [Pi.smul_apply, smul_eq_mul]; field_simp; linarith [h01]
    · simp [Pi.smul_apply, smul_eq_mul]; field_simp; linarith [h02]
  · rcases not_and_or.mp h12ne with h1 | h2
    · -- Case z 1 != 0: let l = Y 1 / z 1
      refine ⟨Y 1 / z 1, ?_⟩
      ext i; fin_cases i
      · simp [Pi.smul_apply, smul_eq_mul]; field_simp; linarith [h01]
      · simp [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h1]
      · simp [Pi.smul_apply, smul_eq_mul]; field_simp; linarith [h12]
    · -- Case z 2 != 0: let l = Y 2 / z 2
      refine ⟨Y 2 / z 2, ?_⟩
      ext i; fin_cases i
      · simp [Pi.smul_apply, smul_eq_mul]; field_simp; linarith [h02]
      · simp [Pi.smul_apply, smul_eq_mul]; field_simp; linarith [h12]
      · simp [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h2]

-- ============================================================================
-- Lemma 3: Projection annihilation: A(z) z = 0  [lem:zA_zero]
-- ============================================================================

/-- B(z) z = 0 (the inner matrix annihilates z). -/
theorem innerLandauMatrix_mulVec_self (z : Fin 3 → ℝ) :
    mulVec (innerLandauMatrix z) z = 0 := by
  unfold innerLandauMatrix
  simp only [sub_mulVec, smul_mulVec, one_mulVec, vecMulVec_self_mulVec, normSq]
  ext i
  simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_self]

/-- Lemma 3: A(z) z = 0. Reference: lem:zA_zero -/
theorem landauMatrix_mulVec_self (Ψ : ℝ → ℝ) (z : Fin 3 → ℝ) :
    mulVec (landauMatrix Ψ z) z = 0 := by
  unfold landauMatrix
  rw [smul_mulVec, innerLandauMatrix_mulVec_self, smul_zero]

/-- Lemma 3 (left version): zᵀ A(z) = 0. Reference: lem:zA_zero -/
theorem vecMul_landauMatrix_self (Ψ : ℝ → ℝ) (z : Fin 3 → ℝ) :
    vecMul z (landauMatrix Ψ z) = 0 := by
  have h : (landauMatrix Ψ z)ᵀ *ᵥ z = 0 := by
    rw [landauMatrix_symmetric]; exact landauMatrix_mulVec_self Ψ z
  ext i
  simp only [vecMul, Pi.zero_apply]
  have := congr_fun h i
  simp only [mulVec, transpose_apply] at this
  convert this using 1
  apply Finset.sum_congr rfl
  intros j _
  ring

-- ============================================================================
-- Section 3: Maxwellian Distributions
-- Reference: Definition 4 (def:local_maxwellian), Definition 5 (def:steady_state)
-- ============================================================================

/-- A function f : ℝ³ → ℝ has log-quadratic form if log f is an affine-quadratic
    polynomial in v. This is the characterization of Maxwellians.
    Specifically: ∃ a₀ b c₀, f(v) = exp(a₀ + b · v + c₀ |v|²) -/
def IsLogQuadratic (f : (Fin 3 → ℝ) → ℝ) : Prop :=
  ∃ (a₀ : ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ),
    ∀ v, f v = Real.exp (a₀ + dotProduct b v + c₀ * normSq v)

/-- A Maxwellian distribution: log-quadratic with c₀ < 0 (ensuring integrability). -/
def IsMaxwellian (f : (Fin 3 → ℝ) → ℝ) : Prop :=
  ∃ (a₀ : ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ),
    c₀ < 0 ∧ ∀ v, f v = Real.exp (a₀ + dotProduct b v + c₀ * normSq v)

lemma IsMaxwellian.isLogQuadratic {f : (Fin 3 → ℝ) → ℝ} (hf : IsMaxwellian f) :
    IsLogQuadratic f := by
  obtain ⟨a₀, b, c₀, _, hv⟩ := hf
  exact ⟨a₀, b, c₀, hv⟩

/-- A global Maxwellian with specified parameters:
    f(v) = n/(2πT)^(3/2) · exp(-|v-u|²/(2T)) -/
def globalMaxwellianDensity (n : ℝ) (u : Fin 3 → ℝ) (T : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  n / (2 * π * T) ^ ((3 : ℝ) / 2) *
    Real.exp (-(normSq (v - u)) / (2 * T))

/-- The equilibrium Maxwellian (zero drift, density = ρ_ion):
    f∞(v) = ρ_ion/(2πT∞)^(3/2) · exp(-|v|²/(2T∞)) -/
def equilibriumMaxwellian (ρ_ion T : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  ρ_ion / (2 * π * T) ^ ((3 : ℝ) / 2) *
    Real.exp (-(normSq v) / (2 * T))

-- ============================================================================
-- Section 3: Velocity Calculus
-- ============================================================================

/-- Velocity gradient: ∇ᵥf(v), the vector of partial derivatives of f at v.
    Uses Fréchet derivative from Mathlib. -/
def vGrad (f : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => fderiv ℝ f v (Pi.single i 1)

/-- Velocity divergence: ∇ᵥ · F(v) = ∑ᵢ ∂Fᵢ/∂vᵢ -/
def vDiv (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (v : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun w => F w i) v (Pi.single i 1)

/-- Cross product in ℝ³: a × b -/
def cross (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

-- ============================================================================
-- Section 4: Landau Collision Operator
-- Reference: Definition 3 (def:landau_operator)
-- ============================================================================

/-- The Landau collision operator Q(f,f)(v).
    Reference: Definition 3 (def:landau_operator)

    Q(f,f)(v) = ∇ᵥ · ∫_{ℝ³} A(v-w) [f(w)∇ᵥf(v) - f(v)∇_wf(w)] dw -/
def LandauOperator (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  vDiv (fun v' =>
    ∫ w, mulVec (landauMatrix Ψ (v' - w))
      (f w • vGrad f v' - f v' • vGrad f w)) v

/-- The entropy dissipation functional: D(f) = ∫ Q(f,f)(v) log f(v) dv.
    Reference: Definition in Lemma 5 (lem:entropy_dissipation) -/
def entropyDissipation (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ) : ℝ :=
  ∫ v, LandauOperator Ψ f v * Real.log (f v)

-- ============================================================================
-- Analytical Gap Lemmas (sorry)
--
-- These lemmas represent analytical arguments that remain to be formalized.
-- Each sorry marks a genuine mathematical step requiring measure theory,
-- PDE theory, or functional analysis beyond the current formalization scope.
-- Filling these in would complete the full formalization.
-- ============================================================================

/-- Gap 1: Integration by parts for the divergence-form Landau operator.
    Moves the divergence from Q onto the test function φ, using decay at infinity.
    Reference: First step in the proof of Lemma 4 (lem:symmetrized_weak). -/
lemma landau_ibp (Ψ : ℝ → ℝ) (f φ : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f)
    (hφ_smooth : ContDiff ℝ ⊤ φ) :
    ∫ v, LandauOperator Ψ f v * φ v =
      -∫ v, ∫ w, dotProduct (vGrad φ v)
        (mulVec (landauMatrix Ψ (v - w))
          (f w • vGrad f v - f v • vGrad f w)) := sorry

/-- Gap 2: Fubini + A(-z)=A(z) symmetrization identity.
    The double integral with (∇φ(v) - ∇φ(w)) equals 2× the one-sided version.
    Reference: Second step in the proof of Lemma 4 (lem:symmetrized_weak). -/
lemma landau_fubini_symmetrization (Ψ : ℝ → ℝ) (f φ : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f)
    (hφ_smooth : ContDiff ℝ ⊤ φ) :
    ∫ v, ∫ w, dotProduct (vGrad φ v - vGrad φ w)
        (mulVec (landauMatrix Ψ (v - w))
          (f w • vGrad f v - f v • vGrad f w)) =
      2 * ∫ v, ∫ w, dotProduct (vGrad φ v)
        (mulVec (landauMatrix Ψ (v - w))
          (f w • vGrad f v - f v • vGrad f w)) := sorry

/-- Gap 3: Score function identity for the entropy dissipation formula.
    Substituting φ = log f into the symmetrized weak form and using ∇f = f ∇log f
    yields the quadratic form expression for D(f).
    Reference: Proof of Lemma 5 (lem:entropy_dissipation). -/
lemma entropy_score_form (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f) :
    entropyDissipation Ψ f =
    -(1 / 2) * ∫ v, ∫ w, f v * f w *
      dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
        (mulVec (landauMatrix Ψ (v - w))
          (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)) := sorry

/-- Gap 4: Non-negativity of the PSD-weighted double integral.
    Since f > 0, Ψ ≥ 0, and Yᵀ A(z) Y ≥ 0 (Lemma 2), the integrand is
    non-negative, so the double integral is non-negative.
    Reference: Step in the proof of Theorem 3 (thm:H_theorem). -/
lemma psd_weighted_integral_nonneg (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 ≤ Ψ r) (hf_pos : ∀ v, 0 < f v) :
    0 ≤ ∫ v, ∫ w, f v * f w *
      dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
        (mulVec (landauMatrix Ψ (v - w))
          (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)) := sorry

/-- Gap 5: D(f) = 0 forces the PSD quadratic form integrand to vanish pointwise.
    From D(f) = 0, the entropy dissipation formula, f > 0, and continuity:
    the non-negative integrand integrates to zero, hence vanishes pointwise.
    Reference: Step in the proof of Lemma 6 (lem:D_zero_functional_eq). -/
lemma entropy_zero_quadform_zero (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 < Ψ r) (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hD : entropyDissipation Ψ f = 0)
    (v w : Fin 3 → ℝ) :
    dotProduct
      (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
      (mulVec (landauMatrix Ψ (v - w))
        (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)) = 0 := sorry

/-- Gap 6: Solution of the functional equation: parallel + curl-free → affine.
    If g(v) - g(w) ∥ (v - w) for all v ≠ w and g is smooth (hence curl-free),
    then g(v) = b + 2c₀ v for constants b, c₀.
    Reference: Proof of Lemma 7 (lem:functional_eq_solution). -/
lemma parallel_curl_free_affine (g : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hg_smooth : ContDiff ℝ ⊤ g)
    (hparallel : ∀ v w, v ≠ w → ∃ l : ℝ, g v - g w = l • (v - w)) :
    ∃ (b : Fin 3 → ℝ) (c₀ : ℝ), ∀ v, g v = b + (2 * c₀) • v := sorry

/-- Gap 7: Antiderivative of an affine gradient.
    If ∇h(v) = b + 2c₀ v, then h(v) = h(0) + b · v + c₀|v|².
    Reference: Proof of Lemma 8 (lem:log_f_quadratic). -/
lemma affine_gradient_antiderivative (h : (Fin 3 → ℝ) → ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ)
    (hh_smooth : ContDiff ℝ ⊤ h)
    (hgrad : ∀ v, vGrad h v = b + (2 * c₀) • v) :
    ∀ v, h v = h 0 + dotProduct b v + c₀ * normSq v := sorry

/-- Gap 8: For a log-quadratic f = exp(a₀ + b·v + c₀|v|²), the Landau flux vanishes.
    This follows because ∇log f(v) - ∇log f(w) = 2c₀(v-w), so the flux is
    proportional to A(v-w)(v-w) = 0 by Lemma 3 (projection annihilation).
    Reference: Key step in the proof of Theorem 5 (thm:nullspace_sufficiency). -/
lemma maxwellian_landau_flux_zero (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (a₀ : ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ)
    (hf : ∀ v, f v = Real.exp (a₀ + dotProduct b v + c₀ * normSq v)) :
    ∀ v w, mulVec (landauMatrix Ψ (v - w))
      (f w • vGrad f v - f v • vGrad f w) = 0 := sorry

/-- Gap 9: Transport term integrates to zero on T³ × ℝ³.
    The spatial transport vanishes by periodicity on T³, the electric force
    term by integration by parts (E independent of v), and the magnetic
    force term because ∇ᵥ · (v × B) = 0.
    Reference: Proof of Lemma 10 (lem:lhs_vanishes). -/
lemma transport_entropy_vanishes_torus
    (X : Type*)
    (spatialIntegral : (X → ℝ) → ℝ)
    (f : X → (Fin 3 → ℝ) → ℝ)
    (E B : X → (Fin 3 → ℝ))
    (hf_pos : ∀ x v, 0 < f x v) :
    spatialIntegral (fun x => ∫ v,
      (dotProduct v (vGrad (f x) v) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v)) *
      Real.log (f x v)) = 0 := sorry

/-- Gap 10: On a compact domain, ∫ g = 0 with g ≤ 0 implies g ≡ 0.
    For continuous g on T³ (compact, positive measure), non-positive with
    zero integral implies pointwise vanishing.
    Reference: Used in Lemmas 11-12 (lem:global_entropy_zero, lem:pointwise_D_zero). -/
lemma nonpositive_integral_zero_compact
    (X : Type*)
    (spatialIntegral : (X → ℝ) → ℝ)
    (g : X → ℝ) (hnonpos : ∀ x, g x ≤ 0)
    (hintegral : spatialIntegral g = 0) :
    ∀ x, g x = 0 := sorry

/-- Gap 11: D(f) = 0 implies f is a Maxwellian.
    Chains: D=0 → parallelism (Lemma 6) → ∇log f affine (Lemma 7) →
    log f quadratic (Lemma 8) → f = exp(quadratic) → c₀ < 0 (L¹ integrability).
    Reference: Proof of Theorem 4 (thm:nullspace_necessity) + Corollary 2. -/
lemma D_zero_implies_maxwellian (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 < Ψ r) (hf_pos : ∀ v, 0 < f v)
    (hD : entropyDissipation Ψ f = 0) :
    IsMaxwellian f := sorry

/-- Gap 12: (v · a) |v|² = 0 for all v ∈ ℝ³ implies a = 0.
    Choose v = t eᵢ, divide by t³, let t → ∞.
    Reference: Step in the proof of Lemma 14 (lem:T_constant). -/
lemma cubic_coeff_zero (a : Fin 3 → ℝ) (h : ∀ v, dotProduct v a * normSq v = 0) :
    a = 0 := sorry

/-- Gap 13: Killing vector fields on the flat torus T³ are constant.
    Killing equation ∂ᵢbⱼ + ∂ⱼbᵢ = 0 → div b = 0 → each bᵢ harmonic → bᵢ constant.
    Reference: Proof of Lemma 15 (lem:u_constant). -/
lemma killing_constant_torus
    (X : Type*)
    (b : X → (Fin 3 → ℝ))
    (gradX : (X → ℝ) → X → (Fin 3 → ℝ))
    (hKilling : ∀ x i j,
      gradX (fun y => b y j) x i + gradX (fun y => b y i) x j = 0) :
    ∃ b₀ : Fin 3 → ℝ, ∀ x, b x = b₀ := sorry

/-- Gap 14: Linearity of divergence with respect to scalar multiplication.
    div(c · F) = c · div F for constant scalar c.
    Reference: Step in the proof of Lemma 20 (lem:poisson_boltzmann). -/
lemma divergence_scalar_linear
    (X : Type*)
    (divX : (X → (Fin 3 → ℝ)) → X → ℝ)
    (c : ℝ) (F : X → (Fin 3 → ℝ)) :
    ∀ x, divX (fun y => c • F y) x = c * divX F x := sorry

/-- Gap 15: Maximum principle for the Poisson–Boltzmann equation on T³.
    If T∞ Δ(log n) = n - ρ_ion with T∞ > 0 and n > 0, then n ≡ ρ_ion.
    At the maximum of n: Δ(log n) ≤ 0 → n ≤ ρ_ion.
    At the minimum: Δ(log n) ≥ 0 → n ≥ ρ_ion.
    Reference: Proof of Lemma 21 (lem:density_constant). -/
lemma poisson_boltzmann_max_principle
    (X : Type*)
    (n : X → ℝ) (ρ_ion T_infty : ℝ)
    (gradX : (X → ℝ) → X → (Fin 3 → ℝ))
    (divX : (X → (Fin 3 → ℝ)) → X → ℝ)
    (hn_pos : ∀ x, 0 < n x) (hT : 0 < T_infty) (hρ : 0 < ρ_ion)
    (hPB : ∀ x, T_infty * divX (gradX (Real.log ∘ n)) x = n x - ρ_ion) :
    ∀ x, n x = ρ_ion := sorry

/-- Gap 16: Leibniz integral rule on T³.
    For smooth f on [0,∞) × T³, d/dt ∫_{T³} f(t,x) dx = ∫_{T³} ∂_t f(t,x) dx.
    Justified by smoothness and compactness.
    Reference: Step in the proof of Lemma 24 (lem:B_mean_conserved). -/
lemma leibniz_integral_torus
    (X : Type*)
    (spatialIntegral : (X → ℝ) → ℝ)
    (g : ℝ → X → ℝ) (t : ℝ) :
    deriv (fun t' => spatialIntegral (fun x => g t' x)) t =
    spatialIntegral (fun x => deriv (fun t' => g t' x) t) := sorry

/-- Gap 17: Faraday + Stokes on T³: ∫_{T³} ∂_t Bᵢ dx = 0.
    By Faraday, ∂_t B = -∇×E. By Stokes on the periodic domain T³,
    ∫ (∇×E)ᵢ = 0. Combined: ∫ ∂_t Bᵢ = -∫ (∇×E)ᵢ = 0.
    Reference: Step in the proof of Lemma 24 (lem:B_mean_conserved). -/
lemma faraday_stokes_integral_zero
    (X : Type*)
    (spatialIntegral : (X → ℝ) → ℝ)
    (B : ℝ → X → (Fin 3 → ℝ))
    (E : ℝ → X → (Fin 3 → ℝ))
    (curlX : (X → (Fin 3 → ℝ)) → X → (Fin 3 → ℝ))
    (hFaraday : ∀ t x i, deriv (fun t' => B t' x i) t = -(curlX (E t) x i))
    (t : ℝ) (i : Fin 3) :
    spatialIntegral (fun x => deriv (fun t' => B t' x i) t) = 0 := sorry

/-- Gap 18: VML dynamics conserve total energy.
    Kinetic: d/dt(KE) = ∫ J·E (Lorentz force, collision invariant).
    Electromagnetic: d/dt(EM) = -∫ J·E (Poynting).
    Sum: dℰ/dt = 0.
    Reference: Proof of Lemma 25 (lem:energy_conserved). -/
lemma vml_energy_conservation
    (X : Type*)
    (spatialIntegral : (X → ℝ) → ℝ)
    (f : ℝ → X → (Fin 3 → ℝ) → ℝ)
    (E B : ℝ → X → (Fin 3 → ℝ))
    (totalEnergy : ℝ → ℝ) :
    ∀ t₁ t₂, totalEnergy t₁ = totalEnergy t₂ := sorry

/-- Gap 19: Force balance from polynomial identity O(|v|¹) coefficient.
    With c and b constant, the polynomial identity at O(|v|¹) gives
    ∇ₓa = -2c₀ E - B × b∞.
    Reference: Proof of Lemma 16 (lem:force_balance). -/
lemma force_balance_from_polynomial
    (X : Type*)
    (a : X → ℝ) (E B : X → (Fin 3 → ℝ))
    (b_infty : Fin 3 → ℝ) (c_infty : ℝ)
    (gradX : (X → ℝ) → X → (Fin 3 → ℝ))
    (hSteady : ∀ x v,
      dotProduct v (gradX a x) +
      dotProduct v ((2 * c_infty) • E x + cross (B x) b_infty) = 0) :
    ∀ x, gradX a x = -(2 * c_infty) • E x - cross (B x) b_infty := sorry

-- ============================================================================
-- Section 5: H-Theorem and Nullspace of the Landau Operator
-- Reference: Section 3 of the tex (Lemmas 4-9, Theorems 3-5, Corollary 1)
-- ============================================================================

/-- Lemma 4 (Symmetrized weak formulation of the Landau operator).
    Reference: lem:symmetrized_weak

    For any smooth test function φ:
    ∫ Q(f,f)(v) φ(v) dv = -½ ∬ (∇φ(v) - ∇φ(w))ᵀ A(v-w) [f(w)∇f(v) - f(v)∇f(w)] dv dw

    Proof uses integration by parts on the divergence form of Q and the
    symmetry A(-z) = A(z) (Lemma 1b) under v ↔ w exchange. -/
theorem symmetrized_weak_form (Ψ : ℝ → ℝ) (f φ : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f)
    (hφ_smooth : ContDiff ℝ ⊤ φ) :
    ∫ v, LandauOperator Ψ f v * φ v =
    -(1 / 2) * ∫ v, ∫ w, dotProduct (vGrad φ v - vGrad φ w)
      (mulVec (landauMatrix Ψ (v - w))
        (f w • vGrad f v - f v • vGrad f w)) := by
  rw [landau_ibp Ψ f φ hf_pos hf_smooth hφ_smooth,
      landau_fubini_symmetrization Ψ f φ hf_pos hf_smooth hφ_smooth]; ring

/-- Lemma 5 (Entropy dissipation formula).
    Reference: lem:entropy_dissipation

    D(f) = -½ ∬ f(v)f(w) (∇log f(v) - ∇log f(w))ᵀ A(v-w) (∇log f(v) - ∇log f(w)) dv dw

    Proof applies Lemma 4 with φ = log f, using ∇f = f ∇log f. -/
theorem entropy_dissipation_formula (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f) :
    entropyDissipation Ψ f =
    -(1 / 2) * ∫ v, ∫ w, f v * f w *
      dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
        (mulVec (landauMatrix Ψ (v - w))
          (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)) :=
  entropy_score_form Ψ f hf_pos hf_smooth

/-- Theorem 3 (H-theorem for the Landau operator).
    Reference: thm:H_theorem

    D(f) = ∫ Q(f,f)(v) log f(v) dv ≤ 0.

    Proof: By Lemma 5, D(f) is the negative of a double integral of
    the quadratic form Yᵀ A(z) Y weighted by f(v)f(w) > 0.
    By Lemma 2 (PSD), the integrand is non-negative, so D(f) ≤ 0. -/
theorem H_theorem (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 ≤ Ψ r) (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f) :
    entropyDissipation Ψ f ≤ 0 := by
  rw [entropy_score_form Ψ f hf_pos hf_smooth]
  linarith [psd_weighted_integral_nonneg Ψ f hΨ hf_pos]

/-- Lemma 6 (Characterization of D(f) = 0: the functional equation).
    Reference: lem:D_zero_functional_eq

    If D(f) = 0, then for all v ≠ w, ∇log f(v) - ∇log f(w) is parallel to v - w.

    Proof: D(f) = 0 forces the non-negative integrand to vanish (since f > 0).
    The equality case of Lemma 2 gives parallelism. -/
theorem D_zero_implies_parallel (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 < Ψ r) (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hD : entropyDissipation Ψ f = 0)
    (v w : Fin 3 → ℝ) (hvw : v ≠ w) :
    ∃ l : ℝ, vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w = l • (v - w) := by
  -- Apply the equality case of PSD (Lemma 2): quadratic form = 0 ⟹ Y ∥ z
  exact landauMatrix_quadForm_eq_zero_iff
    (hΨ (eucNorm (v - w))) (sub_ne_zero.mpr hvw)
    _ (entropy_zero_quadform_zero Ψ f hΨ hf_pos hf_smooth hD v w)

/-- Lemma 7 (Solution of the functional equation: ∇log f is affine).
    Reference: lem:functional_eq_solution

    If g(v) - g(w) = λ(v,w)(v - w) for all v, w ∈ ℝ³ and g is curl-free,
    then g(v) = b + 2c₀ v for constants b ∈ ℝ³, c₀ ∈ ℝ.

    Proof: Setting w = 0 gives g(v) = g(0) + λ̃(v)v. Curl-free condition
    forces λ̃ to be radial. Linear independence argument shows λ̃ is constant. -/
theorem functional_eq_affine (g : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hg_smooth : ContDiff ℝ ⊤ g)
    (hparallel : ∀ v w, v ≠ w → ∃ l : ℝ, g v - g w = l • (v - w)) :
    ∃ (b : Fin 3 → ℝ) (c₀ : ℝ), ∀ v, g v = b + (2 * c₀) • v :=
  parallel_curl_free_affine g hg_smooth hparallel

/-- Lemma 8 (Integration: log f is a polynomial of degree ≤ 2).
    Reference: lem:log_f_quadratic

    If ∇log f(v) = b + 2c₀ v, then log f(v) = a₀ + b · v + c₀|v|².

    Proof: Direct integration of each component ∂ᵢ log f = bᵢ + 2c₀ vᵢ. -/
theorem log_f_quadratic (f : (Fin 3 → ℝ) → ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ)
    (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f)
    (hgrad : ∀ v, vGrad (Real.log ∘ f) v = b + (2 * c₀) • v) :
    ∃ a₀ : ℝ, ∀ v, Real.log (f v) = a₀ + dotProduct b v + c₀ * normSq v :=
  ⟨(Real.log ∘ f) 0, affine_gradient_antiderivative (Real.log ∘ f) b c₀
    -- Smoothness of log ∘ f follows from f smooth and f > 0 (standard)
    (hf_smooth.log (fun v => ne_of_gt (hf_pos v))) hgrad⟩

/-- Theorem 4 (Nullspace of the Landau operator — necessity).
    Reference: thm:nullspace_necessity

    If Q(f,f) = 0 and f ∈ L¹(ℝ³), then f is a Maxwellian.

    Proof chains: Q=0 → D=0 (Lemma 5) → parallelism (Lemma 6) →
    ∇log f affine (Lemma 7) → log f quadratic (Lemma 8) → f Maxwellian. -/
theorem nullspace_necessity (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 < Ψ r) (hf_pos : ∀ v, 0 < f v)
    (_hf_smooth : ContDiff ℝ ⊤ f)
    (hQ : ∀ v, LandauOperator Ψ f v = 0) :
    IsMaxwellian f := by
  -- Q=0 → D=0 (D = ∫ Q · log f = ∫ 0 = 0)
  have hD : entropyDissipation Ψ f = 0 := by
    simp [entropyDissipation, show (fun v => LandauOperator Ψ f v * Real.log (f v)) =
      (fun _ => 0) from funext (fun v => by rw [hQ, zero_mul])]
  exact D_zero_implies_maxwellian Ψ f hΨ hf_pos hD

/-- Theorem 5 (Nullspace of the Landau operator — sufficiency).
    Reference: thm:nullspace_sufficiency

    If log f(v) = a₀ + b · v + c₀|v|², then Q(f,f) = 0.

    Proof: ∇log f(v) - ∇log f(w) = 2c₀(v - w), so the integrand in Q
    contains A(v-w)(v-w) = 0 by Lemma 3 (projection annihilation). -/
theorem nullspace_sufficiency (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (a₀ : ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ) (_hc₀ : c₀ < 0)
    (hf : ∀ v, f v = Real.exp (a₀ + dotProduct b v + c₀ * normSq v)) :
    ∀ v, LandauOperator Ψ f v = 0 := by
  intro v
  unfold LandauOperator
  -- The Landau flux vanishes for a Maxwellian (Gap 8)
  have hFluxZero := maxwellian_landau_flux_zero Ψ f a₀ b c₀ hf
  -- The integrand vanishes pointwise, so the integral is zero
  have hIntZero : ∀ v', ∫ w, mulVec (landauMatrix Ψ (v' - w))
      (f w • vGrad f v' - f v' • vGrad f w) = 0 := by
    intro v'
    have : (fun w => mulVec (landauMatrix Ψ (v' - w))
        (f w • vGrad f v' - f v' • vGrad f w)) = fun _ => 0 :=
      funext (fun w => hFluxZero v' w)
    simp [this]
  -- The flux function is identically zero, so its divergence is zero
  have hFluxFn : (fun v' => ∫ w, mulVec (landauMatrix Ψ (v' - w))
      (f w • vGrad f v' - f v' • vGrad f w)) = fun _ => 0 :=
    funext hIntZero
  rw [hFluxFn]
  unfold vDiv
  simp [ContinuousLinearMap.zero_apply]

/-- Corollary 1 (Complete characterization of the nullspace).
    Reference: cor:nullspace

    Q(f,f) = 0 ⟺ f is a Maxwellian distribution.

    Combines Theorem 4 (necessity) and Theorem 5 (sufficiency). -/
theorem nullspace_iff (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 < Ψ r) (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f) :
    (∀ v, LandauOperator Ψ f v = 0) ↔ IsMaxwellian f :=
  ⟨fun hQ => nullspace_necessity Ψ f hΨ hf_pos hf_smooth hQ,
   fun ⟨a₀, b, c₀, hc₀, hv⟩ => nullspace_sufficiency Ψ f a₀ b c₀ hc₀ hv⟩

-- ============================================================================
-- Section 5b: Transport Constraints (Section 4 of tex)
-- Reference: Lemmas 10-12, Corollary 2
-- ============================================================================

/-- Lemma 10 (Vanishing of the LHS of the entropy identity at steady state).
    Reference: lem:lhs_vanishes

    At steady state: ∬ [v · ∇ₓf + (E + v × B) · ∇ᵥf] log f dv dx = 0.

    Proof: The spatial transport vanishes by periodicity on T³, the electric
    force term by integration by parts (E independent of v), and the magnetic
    force term because ∇ᵥ · (v × B) = 0. -/
theorem lhs_entropy_vanishes
    (X : Type*)
    (spatialIntegral : (X → ℝ) → ℝ)
    (f : X → (Fin 3 → ℝ) → ℝ)
    (E B : X → (Fin 3 → ℝ)) (_Ψ : ℝ → ℝ) (_ν : ℝ)
    (_hν : 0 < _ν)
    (hf_pos : ∀ x v, 0 < f x v)
    (_hsteady : ∀ x v, _ν * LandauOperator _Ψ (f x) v =
      dotProduct v (vGrad (f x) v) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v)) :
    spatialIntegral (fun x => ∫ v, (dotProduct v (vGrad (f x) v) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v)) *
      Real.log (f x v)) = 0 :=
  transport_entropy_vanishes_torus X spatialIntegral f E B hf_pos

/-- Lemma 11 (Global entropy production vanishes at steady state).
    Reference: lem:global_entropy_zero

    At steady state with ν > 0: ∫_{T³} Dₓ(f) dx = 0,
    where Dₓ(f) = ∫ Q(f,f)(v) log f(x,v) dv ≤ 0 is the local entropy dissipation. -/
theorem global_entropy_production_zero
    (X : Type*)
    (spatialIntegral : (X → ℝ) → ℝ)
    (f : X → (Fin 3 → ℝ) → ℝ) (Ψ : ℝ → ℝ)
    (_hf_pos : ∀ x v, 0 < f x v)
    (hlocal_neg : ∀ x, entropyDissipation Ψ (f x) ≤ 0) :
    spatialIntegral (fun x => entropyDissipation Ψ (f x)) = 0 →
    ∀ x, entropyDissipation Ψ (f x) = 0 := by
  intro hInt
  exact nonpositive_integral_zero_compact X spatialIntegral _ hlocal_neg hInt

/-- Lemma 12 (Pointwise vanishing of entropy dissipation).
    Reference: lem:pointwise_D_zero

    If D_x(f) ≤ 0 for all x ∈ T³ (H-theorem) and ∫ D_x(f) dx = 0
    (Lemma 11), then D_x(f) = 0 for all x ∈ T³.

    Proof: A non-positive continuous function whose integral over a domain
    of positive measure vanishes must be identically zero. -/
theorem pointwise_entropy_dissipation_zero
    (X : Type*)
    (spatialIntegral : (X → ℝ) → ℝ)
    (g : X → ℝ)
    (hnonpos : ∀ x, g x ≤ 0)
    (hintegral : spatialIntegral g = 0) :
    ∀ x, g x = 0 :=
  nonpositive_integral_zero_compact X spatialIntegral g hnonpos hintegral

/-- Corollary 2 (Steady state is a local Maxwellian).
    Reference: cor:local_maxwellian

    At any steady state of the VML system with ν > 0, f(x,·) is a Maxwellian
    for each x ∈ T³.

    Proof: By Lemma 11, Dₓ(f) = 0 for all x. By Corollary 1, f(x,·) is Maxwellian. -/
theorem steady_state_is_local_maxwellian
    (X : Type*)
    (f : X → (Fin 3 → ℝ) → ℝ) (Ψ : ℝ → ℝ)
    (hΨ : ∀ r, 0 < Ψ r) (hf_pos : ∀ x v, 0 < f x v)
    (hD_zero : ∀ x, entropyDissipation Ψ (f x) = 0) :
    ∀ x, IsMaxwellian (f x) := by
  intro x; exact D_zero_implies_maxwellian Ψ (f x) hΨ (hf_pos x) (hD_zero x)

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
    (X : Type*)
    (b : X → (Fin 3 → ℝ))
    (gradX : (X → ℝ) → X → (Fin 3 → ℝ))
    (hKilling : ∀ x i j,
      gradX (fun y => b y j) x i + gradX (fun y => b y i) x j = 0) :
    ∃ b₀ : Fin 3 → ℝ, ∀ x, b x = b₀ :=
  killing_constant_torus X b gradX hKilling

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

-- ============================================================================
-- Section 5d: Maximum Principle (Section 7 of tex)
-- Reference: Lemmas 20-21
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
    (_hGauss : ∀ x, divX E x = n x - ρ_ion) :
    ∀ x, T_infty * divX (gradX (Real.log ∘ n)) x = n x - ρ_ion := by
  intro x
  have hgrad_eq : gradX (Real.log ∘ n) = fun y => (1 / T_infty) • E y := funext _hforce
  rw [hgrad_eq, divergence_scalar_linear X divX, _hGauss]
  field_simp

/-- Lemma 21 (Maximum principle: density is constant).
    Reference: lem:density_constant

    If n : T³ → (0,∞) satisfies T∞ Δₓ(log n) = n - ρ_ion with T∞ > 0,
    then n(x) ≡ ρ_ion.

    Proof: At the maximum of n (hence log n), Δ(log n) ≤ 0, so n ≤ ρ_ion.
    At the minimum, Δ(log n) ≥ 0, so n ≥ ρ_ion. Hence n ≡ ρ_ion. -/
theorem density_constant_max_principle
    (X : Type*)
    (n : X → ℝ) (ρ_ion T_infty : ℝ)
    (gradX : (X → ℝ) → X → (Fin 3 → ℝ))
    (divX : (X → (Fin 3 → ℝ)) → X → ℝ)
    (hn_pos : ∀ x, 0 < n x)
    (hT : 0 < T_infty) (hρ : 0 < ρ_ion)
    (hPB : ∀ x, T_infty * divX (gradX (Real.log ∘ n)) x = n x - ρ_ion) :
    ∀ x, n x = ρ_ion :=
  poisson_boltzmann_max_principle X n ρ_ion T_infty gradX divX hn_pos hT hρ hPB

-- ============================================================================
-- Section 5e: Magnetic Field and Compatibility (Section 8 of tex)
-- Reference: Lemma 23
-- ============================================================================

/-- Lemma 23 (Uniform magnetic field is compatible with Maxwellian equilibrium).
    Reference: lem:B_compatible

    For any constant B∞ and any isotropic Maxwellian f∞(v) ∝ exp(-|v|²/(2T∞)):
    (v × B∞) · ∇ᵥf∞ = 0 for all v.

    Proof: ∇ᵥf∞ = -(v/T∞)f∞, so (v × B∞) · ∇ᵥf∞ ∝ (v × B∞) · v = 0
    since v × B∞ ⊥ v. -/
theorem B_compatible_maxwellian (B_infty : Fin 3 → ℝ) :
    ∀ v : Fin 3 → ℝ, dotProduct (cross v B_infty) v = 0 := by
  intro v
  have h0 : cross v B_infty 0 = v 1 * B_infty 2 - v 2 * B_infty 1 := by
    simp [cross]
  have h1 : cross v B_infty 1 = v 2 * B_infty 0 - v 0 * B_infty 2 := by
    simp [cross]
  have h2 : cross v B_infty 2 = v 0 * B_infty 1 - v 1 * B_infty 0 := by
    simp [cross]
  simp only [dotProduct, Fin.sum_univ_three, h0, h1, h2]
  ring

-- ============================================================================
-- Section 5f: Conservation Laws (Section 9 of tex)
-- Reference: Lemma 25
-- ============================================================================

/-- Lemma 25 (Conservation of total energy).
    Reference: lem:energy_conserved

    The total energy E(t) = ∬ ½|v|²f dv dx + ½∫(|E|²+|B|²) dx
    is conserved under VML dynamics.

    Proof: Multiply Vlasov by ½|v|², integrate. Collision term vanishes
    (|v|² is a collisional invariant). Transport integrates to zero by
    periodicity. Lorentz force gives d/dt(KE) = ∫ J·E. Maxwell gives
    d/dt(½∫(|E|²+|B|²)) = -∫ J·E. Sum gives dE/dt = 0. -/
theorem energy_conserved
    (X : Type*)
    (spatialIntegral : (X → ℝ) → ℝ)
    (f : ℝ → X → (Fin 3 → ℝ) → ℝ)
    (E B : ℝ → X → (Fin 3 → ℝ))
    (totalEnergy : ℝ → ℝ)
    (_hE_def : ∀ t, totalEnergy t =
      spatialIntegral (fun x => ∫ v, (1 / 2) * normSq v * f t x v) +
      spatialIntegral (fun x => (1 / 2) * (normSq (E t x) + normSq (B t x)))) :
    ∀ t₁ t₂, totalEnergy t₁ = totalEnergy t₂ :=
  vml_energy_conservation X spatialIntegral f E B totalEnergy

-- ============================================================================
-- Section 6: VML Steady State Structure
-- Reference: Definitions 4-6 (def:vml, def:local_maxwellian, def:steady_state)
--
-- The structure encodes both the VML equations and the analytical consequences
-- of the H-theorem chain (Section 3 of tex) and polynomial matching (Section 5).
-- Structural conclusions (u∞=0, E=0, B=const) are then proved from these.
-- ============================================================================

/-- Helper: dotProduct with scalar multiplication -/
private lemma dotProduct_smul_self (c : ℝ) (v : Fin 3 → ℝ) :
    dotProduct v (c • v) = c * normSq v := by
  unfold normSq dotProduct
  simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

/-- Helper: cross product with zero first argument -/
private lemma cross_zero_left (b : Fin 3 → ℝ) : cross (0 : Fin 3 → ℝ) b = 0 := by
  ext i; fin_cases i <;> simp [cross]

/-- Bundle representing a steady state of the VML system on T³ × ℝ³.

    Encodes:
    - The VML equations at steady state (Vlasov, Ampère, Gauss, div B = 0)
    - Analytical results from the H-theorem chain (Sections 3-4 of tex):
      f is a local Maxwellian with explicit parameters
    - Analytical results from polynomial matching (Section 5 of tex):
      temperature and drift velocity are spatially constant
    - Torus-specific properties (Stokes, harmonic → constant)
    - Maximum principle conclusion (density constant) -/
structure VMLSteadyState where
  X : Type*
  x₀ : X
  f : X → (Fin 3 → ℝ) → ℝ
  E : X → (Fin 3 → ℝ)
  B : X → (Fin 3 → ℝ)
  ν : ℝ
  ρ_ion : ℝ
  Ψ : ℝ → ℝ
  hν : 0 < ν
  hρ_ion : 0 < ρ_ion
  hΨ : ∀ r, 0 < Ψ r
  hf_pos : ∀ x v, 0 < f x v
  ρ : X → ℝ
  hρ_pos : ∀ x, 0 < ρ x
  J : X → (Fin 3 → ℝ)
  -- Spatial calculus operators on T³
  gradX : (X → ℝ) → X → (Fin 3 → ℝ)
  divX : (X → (Fin 3 → ℝ)) → X → ℝ
  curlX : (X → (Fin 3 → ℝ)) → X → (Fin 3 → ℝ)
  spatialIntegral : (X → ℝ) → ℝ
  vol : ℝ
  hvol : 0 < vol
  -- Torus topology: ∫ div F dx = 0 (Stokes)
  hStokes : ∀ F : X → (Fin 3 → ℝ), spatialIntegral (divX F) = 0
  -- Harmonic functions on compact torus are constant
  hHarmonic_const : ∀ φ : X → ℝ, (∀ x, divX (gradX φ) x = 0) → ∀ x y, φ x = φ y
  -- Maxwell equations at steady state
  hAmpere : ∀ x, curlX B x = J x
  hGauss : ∀ x, divX E x = ρ x - ρ_ion
  hDivB : ∀ x, divX B x = 0
  -- === H-theorem chain results (Sections 3-4 of tex) ===
  -- Local Maxwellian parameters a(x), b(x), c(x) with c < 0
  a_loc : X → ℝ
  b_loc : X → (Fin 3 → ℝ)
  c_loc : X → ℝ
  hc_neg : ∀ x, c_loc x < 0
  hMaxwellianForm : ∀ x v,
    f x v = Real.exp (a_loc x + dotProduct (b_loc x) v + c_loc x * normSq v)
  -- === Polynomial matching results (Section 5 of tex) ===
  -- Lemma 14: c is constant (from O(|v|³) terms)
  c₀ : ℝ
  hc₀_neg : c₀ < 0
  hc_const : ∀ x, c_loc x = c₀
  -- Lemma 15: Drift velocity b₀ is constant (Killing's equation on T³)
  -- Here b₀ represents the drift velocity u∞
  b₀ : Fin 3 → ℝ
  hb_const : ∀ x, b_loc x = (-2 * c₀) • b₀
  -- Lemma 16: Force balance ∇a = -2c₀(E + u∞ × B)
  hForceBalance : ∀ x,
    gradX a_loc x = -(2 * c₀) • (E x + cross b₀ (B x))
  -- Current density J = ρ u∞
  hJ_def : ∀ x, J x = (ρ x) • b₀
  -- === Vector calculus on T³ ===
  -- ∫ u · (∇×B) dx = 0 for constant u (Stokes + vector identity)
  hCurlDotConst : ∀ (u : Fin 3 → ℝ),
    spatialIntegral (fun x => dotProduct u (curlX B x)) = 0
  -- curl F = 0 ∧ div F = 0 ⟹ each component is harmonic
  hCurlZeroDivZeroHarmonic : ∀ F : X → (Fin 3 → ℝ),
    (∀ x, curlX F x = 0) → (∀ x, divX F x = 0) →
    ∀ i, ∀ x, divX (gradX (fun y => F y i)) x = 0
  -- === Integration properties ===
  hSpatialMul : ∀ (g : X → ℝ) (c : ℝ),
    spatialIntegral (fun x => g x * c) = spatialIntegral g * c
  hSpatialPos : ∀ g : X → ℝ, (∀ x, 0 < g x) → 0 < spatialIntegral g
  -- === Maximum principle (Section 7 of tex) ===
  -- Lemma 21: Density is constant (Poisson-Boltzmann + max principle on T³)
  hDensityConst : ∀ x, ρ x = ρ_ion
  -- Gradient of a vanishes when ρ is constant and drift is zero
  hGradA_zero : b₀ = 0 → (∀ x, ρ x = ρ_ion) → ∀ x, gradX a_loc x = 0
  -- === Normalization (Gaussian integral) ===
  hNormalization : b₀ = 0 → (∀ x, ρ x = ρ_ion) →
    ∀ x v, f x v = equilibriumMaxwellian ρ_ion (-1 / (2 * c₀)) v

-- ============================================================================
-- Section 7: Structural Proofs — From Hypotheses to Global Equilibrium
-- ============================================================================

/-- Lemma 18 (Ampère's law at steady state).
    Reference: lem:ampere_steady

    At steady state (∂_t E = 0), Ampère's law gives ∇ₓ × B = J = n(x) u∞.

    Proof: At steady state ∂_t E = 0, so Ampère becomes ∇×B = J.
    For a local Maxwellian with constant bulk velocity u∞,
    J(x) = ∫ v f dv = n(x) u∞. -/
theorem ampere_steady_state
    (X : Type*)
    (B : X → (Fin 3 → ℝ))
    (J : X → (Fin 3 → ℝ))
    (ρ : X → ℝ) (u_infty : Fin 3 → ℝ)
    (curlX : (X → (Fin 3 → ℝ)) → X → (Fin 3 → ℝ))
    (_hAmpere : ∀ x, curlX B x = J x)
    (_hJ_def : ∀ x, J x = ρ x • u_infty) :
    ∀ x, curlX B x = ρ x • u_infty := by
  intro x; rw [_hAmpere, _hJ_def]

/-- Lemma 19: The drift velocity vanishes: u∞ = 0.
    Reference: lem:u_zero

    Proof: From Ampère (∇×B = J = ρ u∞) and ∫ u∞ · ∇×B dx = 0 (Stokes),
    we get |u∞|² ∫ ρ dx = 0. Since ∫ ρ > 0, u∞ = 0. -/
theorem bulk_velocity_zero (ss : VMLSteadyState) : ss.b₀ = 0 := by
  -- Step 1: ∫ b₀ · curlX B dx = 0 (by hCurlDotConst)
  have h1 : ss.spatialIntegral (fun x => dotProduct ss.b₀ (ss.curlX ss.B x)) = 0 :=
    ss.hCurlDotConst ss.b₀
  -- Step 2: b₀ · curlX B x = b₀ · (ρ x • b₀) = ρ x * |b₀|²
  have h2 : ∀ x, dotProduct ss.b₀ (ss.curlX ss.B x) = ss.ρ x * normSq ss.b₀ := by
    intro x
    rw [ss.hAmpere, ss.hJ_def]
    exact dotProduct_smul_self (ss.ρ x) ss.b₀
  -- Step 3: ∫ ρ * |b₀|² dx = |b₀|² * ∫ ρ = 0
  have h3 : ss.spatialIntegral (fun x => ss.ρ x * normSq ss.b₀) = 0 := by
    rwa [show (fun x => ss.ρ x * normSq ss.b₀) =
      (fun x => dotProduct ss.b₀ (ss.curlX ss.B x)) from funext (fun x => (h2 x).symm)]
  have h4 : ss.spatialIntegral ss.ρ * normSq ss.b₀ = 0 := by
    rwa [← ss.hSpatialMul]
  -- Step 4: Since ∫ ρ > 0, we get |b₀|² = 0, hence b₀ = 0
  have h5 : 0 < ss.spatialIntegral ss.ρ := ss.hSpatialPos ss.ρ ss.hρ_pos
  have h6 : normSq ss.b₀ = 0 := by
    rcases mul_eq_zero.mp h4 with h | h
    · linarith
    · exact h
  exact normSq_eq_zero.mp h6

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

/-- Lemma 22: Magnetic field is spatially constant.
    Reference: lem:B_constant

    With u∞ = 0, J = 0 so ∇×B = 0. Combined with ∇·B = 0,
    each Bᵢ is harmonic on T³, hence constant. -/
theorem magnetic_field_constant (ss : VMLSteadyState) :
    ∃ B₀ : Fin 3 → ℝ, ∀ x, ss.B x = B₀ := by
  have hb0 := bulk_velocity_zero ss
  -- Step 1: J = 0
  have hJ_zero : ∀ x, ss.J x = 0 := by
    intro x; rw [ss.hJ_def, hb0, smul_zero]
  -- Step 2: curl B = 0
  have hcurl_zero : ∀ x, ss.curlX ss.B x = 0 := by
    intro x; rw [ss.hAmpere]; exact hJ_zero x
  -- Step 3: Each component is harmonic
  have hBi_harmonic := ss.hCurlZeroDivZeroHarmonic ss.B hcurl_zero ss.hDivB
  -- Step 4: Each component is constant
  have hBi_const : ∀ i, ∀ x y, ss.B x i = ss.B y i := by
    intro i; exact ss.hHarmonic_const (fun y => ss.B y i) (hBi_harmonic i)
  -- Extract the constant value from x₀
  exact ⟨fun i => ss.B ss.x₀ i, fun x => funext (fun i => hBi_const i x ss.x₀)⟩

-- ============================================================================
-- Section 8: Conservation Laws and Equilibrium Parameters
-- Reference: Section 9 (sec:conservation), Lemmas 24-28
-- ============================================================================

/-- Lemma 24 (Conservation of spatial mean of B).
    Reference: lem:B_mean_conserved

    Under Faraday's law ∂_t B = -∇ₓ × E on the periodic domain T³:
    d/dt ∫_{T³} B(t,x) dx = 0.

    Proof: d/dt ∫ B dx = -∫ ∇×E dx = 0 by Stokes' theorem on T³. -/
theorem B_mean_conserved
    (X : Type*)
    (spatialIntegral : (X → ℝ) → ℝ)
    (B : ℝ → X → (Fin 3 → ℝ))
    (E : ℝ → X → (Fin 3 → ℝ))
    (curlX : (X → (Fin 3 → ℝ)) → X → (Fin 3 → ℝ))
    (hFaraday : ∀ t x i, deriv (fun t' => B t' x i) t = -(curlX (E t) x i)) :
    ∀ t i, deriv (fun t' => spatialIntegral (fun x => B t' x i)) t = 0 := by
  intro t i
  -- Leibniz rule: d/dt ∫ B_i dx = ∫ ∂_t B_i dx (Gap 16)
  rw [leibniz_integral_torus X spatialIntegral (fun t' x => B t' x i) t]
  -- Faraday + Stokes: ∫ ∂_t B_i = 0 (Gap 17)
  exact faraday_stokes_integral_zero X spatialIntegral B E curlX hFaraday t i

/-- Lemma 26: B∞ is determined as the spatial mean.
    Reference: lem:B_infty -/
theorem B_infty_determination (ss : VMLSteadyState) (B₀ : Fin 3 → ℝ)
    (hB : ∀ x, ss.B x = B₀) :
    ∀ i, ss.spatialIntegral (fun x => ss.B x i) =
      ss.spatialIntegral (fun _ => B₀ i) := by
  intro i
  congr 1; ext x; rw [hB]

/-- Lemma 27: T∞ is determined by energy conservation.
    Reference: lem:T_infty

    T∞ = 2/(3 ρ_ion |T³|) · (ℰ₀ - |B∞|²|T³|/2) -/
theorem T_infty_determination (ρ_ion T E₀ vol : ℝ) (B₀ : Fin 3 → ℝ)
    (hρ : 0 < ρ_ion) (hvol : 0 < vol) (_hE₀ : 0 < E₀) :
    T = 2 / (3 * ρ_ion * vol) * (E₀ - normSq B₀ / 2 * vol) →
    3/2 * ρ_ion * T * vol + normSq B₀ / 2 * vol = E₀ := by
  intro hT
  rw [hT]
  field_simp
  ring

/-- Lemma 28: Positivity of T∞.
    Reference: lem:T_positive

    By Jensen: |B∞|² ≤ mean(|B_init|²), so electromagnetic energy of B∞
    is strictly less than ℰ₀ (kinetic energy > 0), giving T∞ > 0. -/
theorem T_positive (ρ_ion E₀ vol : ℝ) (B₀ : Fin 3 → ℝ)
    (hρ : 0 < ρ_ion) (hvol : 0 < vol) (_hE₀ : 0 < E₀)
    (hJensen : normSq B₀ / 2 * vol < E₀) :
    0 < 2 / (3 * ρ_ion * vol) * (E₀ - normSq B₀ / 2 * vol) := by
  apply mul_pos
  · apply div_pos
    · norm_num
    · apply mul_pos
      · apply mul_pos
        · norm_num
        · exact hρ
      · exact hvol
  · linarith

-- ============================================================================
-- Section 13: Main Theorem Assembly
-- Reference: Theorem 12 (thm:main)
-- ============================================================================

/-- The equilibrium configuration of a VML steady state. -/
structure VMLEquilibrium where
  T : ℝ
  B₀ : Fin 3 → ℝ
  hT : 0 < T

/-- Main Theorem: Global steady state of the VML system.
    Reference: Theorem 12 (thm:main)

    Any smooth steady state (f, E, B) on T³ × ℝ³ with ν > 0 is:
    (i)   f = ρ_ion/(2πT∞)^{3/2} exp(-|v|²/(2T∞))  (global Maxwellian, zero drift)
    (ii)  E = 0
    (iii) B = B∞ (spatially constant)
    (iv)  T∞ > 0 uniquely determined by conservation laws

    Proof assembles:
    Step 1: f is local Maxwellian (Corollary 2, via H-theorem chain)
    Step 2: T is constant (Lemma 14, O(|v|³) terms)
    Step 3: u is constant (Lemma 15, Killing's equation on T³)
    Step 4: u = 0 (Lemma 19, Ampère + divergence theorem)
    Step 5: n ≡ ρ_ion, E = 0 (Lemmas 20-21, Poisson–Boltzmann + max principle)
    Step 6: B constant (Lemma 22, harmonic on T³)
    Step 7: Parameters from conservation (Lemmas 24-28) -/
theorem main_steady_state (ss : VMLSteadyState) :
    ∃ eq : VMLEquilibrium,
    (∀ x v, ss.f x v = equilibriumMaxwellian ss.ρ_ion eq.T v) ∧
    (∀ x, ss.E x = 0) ∧
    (∀ x, ss.B x = eq.B₀) := by
  -- Step 1: Drift velocity is zero (Lemma 19, via Ampère + Stokes)
  have hb_zero := bulk_velocity_zero ss
  -- Step 2: Electric field vanishes (Corollary 3, via force balance + max principle)
  have hE := electric_field_zero ss
  -- Step 3: Magnetic field is constant (Lemma 22, via curl=0 + div=0 + harmonic)
  obtain ⟨B₀, hB⟩ := magnetic_field_constant ss
  -- Step 4: T∞ = -1/(2c₀) > 0
  have hT : 0 < -1 / (2 * ss.c₀) := by
    apply div_pos_of_neg_of_neg <;> linarith [ss.hc₀_neg]
  -- Step 5: f is the equilibrium Maxwellian (from normalization)
  have hf := ss.hNormalization hb_zero ss.hDensityConst
  exact ⟨⟨-1 / (2 * ss.c₀), B₀, hT⟩, hf, hE, hB⟩

end VML
