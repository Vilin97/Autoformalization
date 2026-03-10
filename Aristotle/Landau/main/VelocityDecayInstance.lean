/-
  Main VelocityDecayConditions proofs for smooth kernels.

  Contains:
  - landau_flux_component_diff_with_bound (differentiability + bound for flux component)
  - schwartzDecayConditions (all 18 VelocityDecayConditions fields for Schwartz φ)

  Split from VelocityDecayInstance.lean (cycle 41) for maintainability.
-/
import Aristotle.Landau.main.VelocityDecayHelpers

open Matrix Finset BigOperators Real MeasureTheory

noncomputable section
namespace VML

set_option maxHeartbeats 4000000 in
/-- The Landau flux integrand component is differentiable in v with a product-form bound.

    This is the key analysis lemma for flux differentiability. For each fixed w:
    - g_i(v,w) = (A(v-w) *ᵥ (φ(w)·∇φ(v) - φ(v)·∇φ(w)))_i is differentiable in v
    - ‖D_v g_i(v,w)‖ ≤ C · (1+‖v‖)^M · φ(v) · (1+‖w‖)^M · |φ(w)|

    The differentiability follows from:
    - Away from v = w: Ψ ∘ ‖·‖ is C¹ (since ‖·‖ smooth for z ≠ 0 and Ψ is C¹)
    - At v = w: A(0) *ᵥ Δ(w,w) = 0 and the integrand is O(‖v-w‖³) (bounded Ψ × vanishing A × vanishing Δ)
    - The bound combines the Landau matrix bound (O(‖v-w‖²)), gradient bounds, and Schwartz decay. -/
lemma landau_flux_component_diff_with_bound
    {Ψ : ℝ → ℝ} (hΨ : ∃ CΨ, ∀ r, |Ψ r| ≤ CΨ) (hΨ_cts : Continuous Ψ)
    (hΨ_diff : ContDiff ℝ 1 Ψ) (hΨ'_bound : ∃ CΨ', ∀ r, |deriv Ψ r| ≤ CΨ')
    {φ : (Fin 3 → ℝ) → ℝ} (hφ_pos : ∀ v, 0 < φ v) (hφ_smooth : ContDiff ℝ ⊤ φ)
    (hφ_decay : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    -- Pointwise second derivative bound: |∂²φ/∂vⱼ∂vₖ(v)| ≤ C₂(1+‖v‖)^K₂ × φ(v)
    -- Natural for Schwartz-class functions (e.g. exp(-|v|⁴) gives K₂ = 6)
    (hφ_deriv2_bound : ∃ C₂ K₂, ∀ v (j : Fin 3),
      ‖fderiv ℝ (fun v' => fderiv ℝ φ v' (Pi.single j 1)) v‖ ≤ C₂ * (1 + ‖v‖) ^ K₂ * φ v)
    (hGradBound : ∃ C K, ∀ v i,
      |fderiv ℝ φ v (Pi.single i 1)| ≤ C * (1 + ‖v‖) ^ K * φ v)
    (i : Fin 3) :
    -- (1) Differentiable in v for each w
    (∀ w, Differentiable ℝ (fun v =>
      (landauMatrix Ψ (v - w) *ᵥ (φ w • vGrad φ v - φ v • vGrad φ w)) i)) ∧
    -- (2) Product-form derivative bound
    (∃ C₀ M, ∀ v w, ‖fderiv ℝ (fun v' =>
      (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v‖ ≤
      C₀ * ((1 + ‖v‖) ^ M * φ v) * ((1 + ‖w‖) ^ M * |φ w|)) ∧
    -- (3) Derivative integrable for each v
    (∀ v, Integrable (fun w => fderiv ℝ (fun v' =>
      (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v)) ∧
    -- (4) Flux integral derivative has Schwartz bound (for IBP integrability)
    (∃ C₁ M₁, ∀ v, ‖fderiv ℝ (fun v' =>
      ∫ w, (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v‖ ≤
      C₁ * (1 + ‖v‖) ^ M₁ * φ v) := by
  obtain ⟨CΨ, hCΨ⟩ := hΨ
  obtain ⟨CΨ', hCΨ'⟩ := hΨ'_bound
  obtain ⟨Cg, Kg, hCg⟩ := hGradBound
  obtain ⟨C₂, K₂, hC₂⟩ := hφ_deriv2_bound
  have hCΨ_nn : 0 ≤ CΨ := le_trans (abs_nonneg _) (hCΨ 0)
  have hCg_nn : 0 ≤ Cg := by
    have h := hCg 0 0; simp only [norm_zero, add_zero, one_pow] at h
    nlinarith [abs_nonneg (fderiv ℝ φ 0 (Pi.single 0 1)), hφ_pos 0]
  have hC₂_nn : 0 ≤ C₂ := by
    have h := hC₂ 0 0; simp only [norm_zero, add_zero, one_pow] at h
    nlinarith [norm_nonneg (fderiv ℝ (fun v' => fderiv ℝ φ v' (Pi.single 0 1)) 0), hφ_pos 0]
  -- Helper: ∂_j φ is differentiable (φ is C^∞)
  have hφ_deriv_diff : ∀ j : Fin 3,
      Differentiable ℝ (fun v => fderiv ℝ φ v (Pi.single j 1)) :=
    fun j => ((contDiff_succ_iff_fderiv_apply.mp
      (hφ_smooth.of_le le_top : ContDiff ℝ (1 + 1) φ)).2.2
      (Pi.single j 1)).differentiable le_rfl
  -- Helper: the flux integrand component as a finite sum
  have hsum_eq : ∀ v w, (landauMatrix Ψ (v - w) *ᵥ
      (φ w • vGrad φ v - φ v • vGrad φ w)) i =
    ∑ j : Fin 3, landauMatrix Ψ (v - w) i j *
      (φ w * fderiv ℝ φ v (Pi.single j 1) - φ v * fderiv ℝ φ w (Pi.single j 1)) := by
    intro v w
    simp only [Matrix.mulVec, dotProduct, vGrad, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  -- Part 1: Differentiable in v for each w
  -- Each A_{ij}(v-w) differentiable by landauMatrix_entry_differentiable,
  -- each D_j(v,w) differentiable since φ is C^∞, so (A *ᵥ D)_i = ∑ A_{ij}*D_j is diff.
  have hpart1 : ∀ w, Differentiable ℝ (fun v =>
      (landauMatrix Ψ (v - w) *ᵥ (φ w • vGrad φ v - φ v • vGrad φ w)) i) := by
    intro w v
    show DifferentiableAt ℝ (fun v => (landauMatrix Ψ (v - w) *ᵥ
        (φ w • vGrad φ v - φ v • vGrad φ w)) i) v
    simp only [Matrix.mulVec, dotProduct, vGrad, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Fin.sum_univ_three]
    have hmul : ∀ j : Fin 3, DifferentiableAt ℝ (fun v =>
        landauMatrix Ψ (v - w) i j *
          (φ w * fderiv ℝ φ v (Pi.single j 1) - φ v * fderiv ℝ φ w (Pi.single j 1))) v :=
      fun j => (landauMatrix_entry_differentiable hΨ_diff ⟨CΨ, hCΨ⟩ w i j v).mul
        (((hφ_deriv_diff j v).const_mul (φ w)).sub
          ((hφ_smooth.differentiable le_top v).mul_const (fderiv ℝ φ w (Pi.single j 1))))
    exact ((hmul 0).add (hmul 1)).add (hmul 2)
  -- Parts 2-4: Product-form derivative bound, integrability, and integral interchange.
  -- These follow from: (a) product rule for fderiv of A_{ij} × (φ·∇φ) terms,
  -- (b) quadratic bound ‖D A_{ij}(z)‖ ≤ C(1+‖z‖)² (submitted to Aristotle),
  -- (c) AEStronglyMeasurable of fderiv (continuity in w of the explicit product-rule expression),
  -- (d) hasFDerivAt_integral_of_dominated_of_fderiv_le (Mathlib parametric differentiation).
  -- Part 2: Product-form derivative bound (the core analysis bound)
  have hpart2 : ∃ C₀ M, ∀ v w, ‖fderiv ℝ (fun v' =>
      (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v‖ ≤
      C₀ * ((1 + ‖v‖) ^ M * φ v) * ((1 + ‖w‖) ^ M * |φ w|) := by
    -- Get matrix bounds
    have hmat_fderiv : ∀ j, ∃ C, ∀ z, ‖fderiv ℝ (fun z => landauMatrix Ψ z i j) z‖ ≤
        C * (1 + ‖z‖) ^ 2 :=
      fun j => landauMatrix_entry_fderiv_norm_bound' hΨ_diff ⟨CΨ, hCΨ⟩ ⟨CΨ', hCΨ'⟩ i j
    have hmat_abs : ∀ j, ∃ C, ∀ z, |landauMatrix Ψ z i j| ≤ C * ‖z‖ ^ 2 :=
      fun j => landauMatrix_entry_abs_bound' ⟨CΨ, hCΨ⟩ i j
    choose CD hCD using hmat_fderiv
    choose CA hCA using hmat_abs
    -- Use operator norm bound: ‖fderiv φ v‖ ≤ 3*Cg*(1+‖v‖)^Kg*φ(v)
    -- From component bounds via: ‖L‖ ≤ ∑_k |L(e_k)| for sup-norm on Fin 3 → ℝ
    have hφ_fderiv_norm : ∀ v, ‖fderiv ℝ φ v‖ ≤ 3 * Cg * (1 + ‖v‖) ^ Kg * φ v := by
      intro v
      have h_nn : (0 : ℝ) ≤ 3 * Cg * (1 + ‖v‖) ^ Kg * φ v :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCg_nn)
          (pow_nonneg (by linarith [norm_nonneg v]) Kg)) (le_of_lt (hφ_pos v))
      rw [ContinuousLinearMap.opNorm_le_iff h_nn]
      intro x
      simp only [Real.norm_eq_abs]
      -- Decompose x into standard basis
      have hx_eq : (fderiv ℝ φ v) x = x 0 * (fderiv ℝ φ v) (Pi.single 0 1) +
          x 1 * (fderiv ℝ φ v) (Pi.single 1 1) + x 2 * (fderiv ℝ φ v) (Pi.single 2 1) := by
        have hd : x = x 0 • (Pi.single 0 1 : Fin 3 → ℝ) +
            x 1 • (Pi.single 1 1 : Fin 3 → ℝ) + x 2 • (Pi.single 2 1 : Fin 3 → ℝ) := by
          ext i; fin_cases i <;> simp
        conv_lhs => rw [hd]
        rw [map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      rw [hx_eq]
      have h0 := hCg v 0; have h1 := hCg v 1; have h2 := hCg v 2
      have hb0 : |x 0| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x 0
      have hb1 : |x 1| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x 1
      have hb2 : |x 2| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x 2
      -- Triangle inequality for 3-term sum
      have tri : |x 0 * (fderiv ℝ φ v) (Pi.single 0 1) +
          x 1 * (fderiv ℝ φ v) (Pi.single 1 1) +
          x 2 * (fderiv ℝ φ v) (Pi.single 2 1)| ≤
          |x 0| * |(fderiv ℝ φ v) (Pi.single 0 1)| +
          |x 1| * |(fderiv ℝ φ v) (Pi.single 1 1)| +
          |x 2| * |(fderiv ℝ φ v) (Pi.single 2 1)| := by
        calc _ ≤ |x 0 * (fderiv ℝ φ v) (Pi.single 0 1) +
                  x 1 * (fderiv ℝ φ v) (Pi.single 1 1)| +
                |x 2 * (fderiv ℝ φ v) (Pi.single 2 1)| := abs_add_le _ _
          _ ≤ _ := by
              have := abs_add_le (x 0 * (fderiv ℝ φ v) (Pi.single 0 1))
                (x 1 * (fderiv ℝ φ v) (Pi.single 1 1))
              simp only [abs_mul] at *; linarith
      -- Each |x k| * |Lk| ≤ Cg * (1+‖v‖)^Kg * φ(v) * ‖x‖
      have b0 : |x 0| * |(fderiv ℝ φ v) (Pi.single 0 1)| ≤
          Cg * (1 + ‖v‖) ^ Kg * φ v * ‖x‖ := by
        calc _ ≤ ‖x‖ * (Cg * (1 + ‖v‖) ^ Kg * φ v) :=
              mul_le_mul hb0 h0 (abs_nonneg _) (norm_nonneg _)
          _ = _ := by ring
      have b1 : |x 1| * |(fderiv ℝ φ v) (Pi.single 1 1)| ≤
          Cg * (1 + ‖v‖) ^ Kg * φ v * ‖x‖ := by
        calc _ ≤ ‖x‖ * (Cg * (1 + ‖v‖) ^ Kg * φ v) :=
              mul_le_mul hb1 h1 (abs_nonneg _) (norm_nonneg _)
          _ = _ := by ring
      have b2 : |x 2| * |(fderiv ℝ φ v) (Pi.single 2 1)| ≤
          Cg * (1 + ‖v‖) ^ Kg * φ v * ‖x‖ := by
        calc _ ≤ ‖x‖ * (Cg * (1 + ‖v‖) ^ Kg * φ v) :=
              mul_le_mul hb2 h2 (abs_nonneg _) (norm_nonneg _)
          _ = _ := by ring
      linarith
    -- Constants: C₀ and M
    let C_D := max (max (CD 0) (CD 1)) (CD 2)
    let C_A := max (max (CA 0) (CA 1)) (CA 2)
    use 3 * (2 * C_D * Cg + C_A * (C₂ + 3 * Cg * Cg)), 2 + Kg + K₂
    intro v w
    -- Step 1: Rewrite as sum
    have hrewrite : (fun v' =>
        (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) =
      (fun v' =>
        ∑ j, landauMatrix Ψ (v' - w) i j *
          (φ w * fderiv ℝ φ v' (Pi.single j 1) - φ v' * fderiv ℝ φ w (Pi.single j 1))) :=
      funext (fun v' => hsum_eq v' w)
    rw [hrewrite]
    -- Step 2: Per-summand differentiability
    have hdiff_j : ∀ j : Fin 3, DifferentiableAt ℝ (fun v' =>
        landauMatrix Ψ (v' - w) i j *
          (φ w * fderiv ℝ φ v' (Pi.single j 1) - φ v' * fderiv ℝ φ w (Pi.single j 1))) v :=
      fun j => (landauMatrix_entry_differentiable hΨ_diff ⟨CΨ, hCΨ⟩ w i j v).mul
        (((hφ_deriv_diff j v).const_mul (φ w)).sub
          ((hφ_smooth.differentiable le_top v).mul_const (fderiv ℝ φ w (Pi.single j 1))))
    -- Step 3: Per-summand bound (the core analysis estimate)
    suffices hsb : ∀ j : Fin 3,
        ‖fderiv ℝ (fun v' => landauMatrix Ψ (v' - w) i j *
          (φ w * fderiv ℝ φ v' (Pi.single j 1) - φ v' * fderiv ℝ φ w (Pi.single j 1))) v‖ ≤
        (2 * CD j * Cg + CA j * (C₂ + 3 * Cg * Cg)) *
          ((1 + ‖v‖) ^ (2 + Kg + K₂) * φ v) * ((1 + ‖w‖) ^ (2 + Kg + K₂) * |φ w|) by
      -- Assembly: triangle inequality on Finset sum, bound via max constants
      have h0 := hsb 0; have h1 := hsb 1; have h2 := hsb 2
      have hpv : 0 ≤ (1 + ‖v‖) ^ (2 + Kg + K₂) * φ v :=
        mul_nonneg (pow_nonneg (by linarith [norm_nonneg v]) _) (le_of_lt (hφ_pos v))
      have hpw : 0 ≤ (1 + ‖w‖) ^ (2 + Kg + K₂) * |φ w| :=
        mul_nonneg (pow_nonneg (by linarith [norm_nonneg w]) _) (abs_nonneg _)
      -- Each per-summand const ≤ max const
      have hCD0 : CD 0 ≤ C_D := le_max_of_le_left (le_max_left _ _)
      have hCD1 : CD 1 ≤ C_D := le_max_of_le_left (le_max_right _ _)
      have hCD2 : CD 2 ≤ C_D := le_max_right _ _
      have hCA0 : CA 0 ≤ C_A := le_max_of_le_left (le_max_left _ _)
      have hCA1 : CA 1 ≤ C_A := le_max_of_le_left (le_max_right _ _)
      have hCA2 : CA 2 ≤ C_A := le_max_right _ _
      -- Expand sum, split fderiv via HasFDerivAt, triangle inequality
      simp only [Fin.sum_univ_three]
      have hd012 : HasFDerivAt (fun v' =>
          landauMatrix Ψ (v' - w) i 0 * (φ w * (fderiv ℝ φ v') (Pi.single 0 1) -
            φ v' * (fderiv ℝ φ w) (Pi.single 0 1)) +
          landauMatrix Ψ (v' - w) i 1 * (φ w * (fderiv ℝ φ v') (Pi.single 1 1) -
            φ v' * (fderiv ℝ φ w) (Pi.single 1 1)) +
          landauMatrix Ψ (v' - w) i 2 * (φ w * (fderiv ℝ φ v') (Pi.single 2 1) -
            φ v' * (fderiv ℝ φ w) (Pi.single 2 1)))
        (fderiv ℝ (fun v' => landauMatrix Ψ (v' - w) i 0 *
            (φ w * (fderiv ℝ φ v') (Pi.single 0 1) - φ v' * (fderiv ℝ φ w) (Pi.single 0 1))) v +
          fderiv ℝ (fun v' => landauMatrix Ψ (v' - w) i 1 *
            (φ w * (fderiv ℝ φ v') (Pi.single 1 1) - φ v' * (fderiv ℝ φ w) (Pi.single 1 1))) v +
          fderiv ℝ (fun v' => landauMatrix Ψ (v' - w) i 2 *
            (φ w * (fderiv ℝ φ v') (Pi.single 2 1) - φ v' * (fderiv ℝ φ w) (Pi.single 2 1))) v) v :=
        ((hdiff_j 0).hasFDerivAt.add (hdiff_j 1).hasFDerivAt).add (hdiff_j 2).hasFDerivAt
      rw [hd012.fderiv]
      -- Triangle inequality: ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖
      have htri := norm_add_le
        (fderiv ℝ (fun v' => landauMatrix Ψ (v' - w) i 0 *
          (φ w * (fderiv ℝ φ v') (Pi.single 0 1) - φ v' * (fderiv ℝ φ w) (Pi.single 0 1))) v +
        fderiv ℝ (fun v' => landauMatrix Ψ (v' - w) i 1 *
          (φ w * (fderiv ℝ φ v') (Pi.single 1 1) - φ v' * (fderiv ℝ φ w) (Pi.single 1 1))) v)
        (fderiv ℝ (fun v' => landauMatrix Ψ (v' - w) i 2 *
          (φ w * (fderiv ℝ φ v') (Pi.single 2 1) - φ v' * (fderiv ℝ φ w) (Pi.single 2 1))) v)
      have htri2 := norm_add_le
        (fderiv ℝ (fun v' => landauMatrix Ψ (v' - w) i 0 *
          (φ w * (fderiv ℝ φ v') (Pi.single 0 1) - φ v' * (fderiv ℝ φ w) (Pi.single 0 1))) v)
        (fderiv ℝ (fun v' => landauMatrix Ψ (v' - w) i 1 *
          (φ w * (fderiv ℝ φ v') (Pi.single 1 1) - φ v' * (fderiv ℝ φ w) (Pi.single 1 1))) v)
      -- Bound constants via max
      have hle0 : 2 * CD 0 * Cg + CA 0 * (C₂ + 3 * Cg * Cg) ≤
          2 * C_D * Cg + C_A * (C₂ + 3 * Cg * Cg) := by
        nlinarith [hCD0, hCA0, hCg_nn, hC₂_nn, sq_nonneg Cg]
      have hle1 : 2 * CD 1 * Cg + CA 1 * (C₂ + 3 * Cg * Cg) ≤
          2 * C_D * Cg + C_A * (C₂ + 3 * Cg * Cg) := by
        nlinarith [hCD1, hCA1, hCg_nn, hC₂_nn, sq_nonneg Cg]
      have hle2 : 2 * CD 2 * Cg + CA 2 * (C₂ + 3 * Cg * Cg) ≤
          2 * C_D * Cg + C_A * (C₂ + 3 * Cg * Cg) := by
        nlinarith [hCD2, hCA2, hCg_nn, hC₂_nn, sq_nonneg Cg]
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle0 hpv) hpw,
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle1 hpv) hpw,
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle2 hpv) hpw]
    -- Apply Aristotle-proved per-summand bound
    intro j
    have hA_diff : Differentiable ℝ (fun z => landauMatrix Ψ z i j) := by
      intro z
      have h := landauMatrix_entry_differentiable hΨ_diff ⟨CΨ, hCΨ⟩ 0 i j z
      simp only [sub_zero] at h; exact h
    have hCD_nn_j : 0 ≤ CD j := by
      have h := hCD j 0; simp only [norm_zero, add_zero, one_pow, mul_one] at h
      exact le_trans (norm_nonneg _) h
    have hCA_nn_j : 0 ≤ CA j := by
      by_contra hlt; push_neg at hlt
      have hone : (1 : Fin 3 → ℝ) ≠ 0 := fun h => one_ne_zero (congr_fun h 0)
      linarith [hCA j 1, abs_nonneg (landauMatrix Ψ 1 i j),
                mul_neg_of_neg_of_pos hlt (sq_pos_of_pos (norm_pos_iff.mpr hone))]
    exact single_summand_deriv_bound
      (fun z => landauMatrix Ψ z i j) φ (fun v => fderiv ℝ φ v (Pi.single j 1))
      hA_diff (hφ_smooth.differentiable le_top) (hφ_deriv_diff j) hφ_pos
      (CA j) (CD j) Cg C₂ (3 * Cg) Kg K₂
      hCA_nn_j hCD_nn_j hCg_nn hC₂_nn (by linarith)
      (hCA j) (hCD j) (fun v => hCg v j) (fun v => hC₂ v j) hφ_fderiv_norm
      v w
  -- Joint continuity of the integrand (used by Parts 3 and 4)
  have hcont : Continuous (Function.uncurry (fun (w : Fin 3 → ℝ) (v' : Fin 3 → ℝ) =>
      (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i)) := by
    have hφ_cont : Continuous φ := hφ_smooth.continuous
    have hφ_fderiv_cont : ∀ j, Continuous (fun v => (fderiv ℝ φ v) (Pi.single j 1)) := by
      intro j
      exact ((hφ_smooth.of_le le_top : ContDiff ℝ 1 φ).continuous_fderiv le_rfl).clm_apply
        continuous_const
    have heq : (Function.uncurry (fun (w : Fin 3 → ℝ) (v' : Fin 3 → ℝ) =>
        (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i)) =
      (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
        ∑ j, landauMatrix Ψ (p.2 - p.1) i j *
          (φ p.1 * (fderiv ℝ φ p.2) (Pi.single j 1) -
           φ p.2 * (fderiv ℝ φ p.1) (Pi.single j 1))) := by
      ext ⟨w, v'⟩; exact hsum_eq v' w
    rw [heq]
    exact continuous_finset_sum _ fun j _ =>
      (((continuous_apply j).comp ((continuous_apply i).comp
        (landauMatrix_continuous hΨ_cts))).comp
        (continuous_snd.sub continuous_fst)).mul
      (((hφ_cont.comp continuous_fst).mul
        ((hφ_fderiv_cont j).comp continuous_snd)).sub
       ((hφ_cont.comp continuous_snd).mul
        ((hφ_fderiv_cont j).comp continuous_fst)))
  -- Part 3: Derivative integrable (follows from Part 2 + Schwartz decay)
  have hpart3 : ∀ v, Integrable (fun w => fderiv ℝ (fun v' =>
      (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v) := by
    obtain ⟨C₀, M, hC₀⟩ := hpart2
    intro v
    refine Integrable.mono'
      ((integrable_one_add_norm_pow_mul hφ_decay M).const_mul (C₀ * (1 + ‖v‖) ^ M * φ v))
      ?_ (Filter.Eventually.of_forall fun w =>
        le_trans (hC₀ v w) (le_of_eq (by ring)))
    exact ((measurable_fderiv_with_param ℝ hcont).comp
      (measurable_id.prod_mk measurable_const)).aestronglyMeasurable
  -- Part 4: Schwartz bound on integral derivative (from Parts 2-3 + norm_integral_le)
  have hpart4 : ∃ C₁ M₁, ∀ v, ‖fderiv ℝ (fun v' =>
      ∫ w, (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v‖ ≤
      C₁ * (1 + ‖v‖) ^ M₁ * φ v := by
    obtain ⟨C₀, M, hC₀⟩ := hpart2
    refine ⟨C₀ * ∫ w, (1 + ‖w‖) ^ M * |φ w|, M, fun v => ?_⟩
    -- Differentiation under the integral sign (Leibniz integral rule)
    have h_int : HasFDerivAt (fun v' => ∫ w,
        (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i)
      (∫ w, fderiv ℝ (fun v' =>
        (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v)
      v := by
        -- Integrability of the original integrand at v
        have hF_int_v : Integrable (fun w =>
            (landauMatrix Ψ (v - w) *ᵥ (φ w • vGrad φ v - φ v • vGrad φ w)) i) :=
          (schwartz_flux_integrable ⟨CΨ, hCΨ⟩ hΨ_cts hφ_pos hφ_smooth hφ_decay
            ⟨Cg, Kg, hCg⟩ v).eval i
        -- Bound φ on compact closedBall v 1
        obtain ⟨v_max, _, hv_max⟩ := (ProperSpace.isCompact_closedBall v 1).exists_isMaxOn
          ⟨v, Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1)⟩
          hφ_smooth.continuous.continuousOn
        -- Apply Leibniz integral rule (parametric differentiation)
        refine hasFDerivAt_integral_of_dominated_of_fderiv_le
          (F := fun v' w => (landauMatrix Ψ (v' - w) *ᵥ
            (φ w • vGrad φ v' - φ v' • vGrad φ w)) i)
          (F' := fun v' w => fderiv ℝ (fun v'' =>
            (landauMatrix Ψ (v'' - w) *ᵥ
              (φ w • vGrad φ v'' - φ v'' • vGrad φ w)) i) v')
          (bound := fun w => C₀ * ((2 + ‖v‖) ^ M * φ v_max) *
            ((1 + ‖w‖) ^ M * |φ w|))
          (ε := 1) one_pos ?_ ?_ ?_ ?_ ?_ ?_
        · -- hF_meas: AEStronglyMeasurable for v' near v
          exact Filter.Eventually.of_forall fun v' =>
            (hcont.comp (continuous_id.prod_mk continuous_const)).aestronglyMeasurable
        · -- hF_int: integrable at v
          exact hF_int_v
        · -- hF'_meas: AEStronglyMeasurable of derivative
          exact (hpart3 v).aestronglyMeasurable
        · -- h_bound: ‖F'(v', w)‖ ≤ bound(w) for v' ∈ ball v 1
          refine Filter.Eventually.of_forall fun w v' hv' => ?_
          have hv'_norm : 1 + ‖v'‖ ≤ 2 + ‖v‖ := by
            have h1 : dist v' v < 1 := Metric.mem_ball.mp hv'
            have h2 : ‖v'‖ ≤ ‖v‖ + ‖v' - v‖ := by
              calc ‖v'‖ = ‖v + (v' - v)‖ := by congr 1; abel
                _ ≤ ‖v‖ + ‖v' - v‖ := norm_add_le _ _
            rw [dist_eq_norm] at h1; linarith
          have hC₀_nn : 0 ≤ C₀ := by
            have h_nn := le_trans (norm_nonneg (fderiv ℝ (fun v' => (landauMatrix Ψ (v' - w) *ᵥ
              (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v')) (hC₀ v' w)
            have h_pos : 0 < ((1 + ‖v'‖) ^ M * φ v') * ((1 + ‖w‖) ^ M * |φ w|) :=
              mul_pos (mul_pos (pow_pos (by linarith [norm_nonneg v']) M) (hφ_pos v'))
                (mul_pos (pow_pos (by linarith [norm_nonneg w]) M)
                  (abs_pos.mpr (ne_of_gt (hφ_pos w))))
            exact nonneg_of_mul_nonneg_left (by linarith) h_pos
          exact le_trans (hC₀ v' w) (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (mul_le_mul (pow_le_pow_left₀ (by linarith [norm_nonneg v']) hv'_norm M)
                (hv_max (Metric.ball_subset_closedBall hv'))
                (le_of_lt (hφ_pos v'))
                (pow_nonneg (by linarith [norm_nonneg v]) M))
              hC₀_nn)
            (mul_nonneg (pow_nonneg (by linarith [norm_nonneg w]) M) (abs_nonneg _)))
        · -- bound_integrable
          exact (integrable_one_add_norm_pow_mul hφ_decay M).const_mul _
        · -- h_diff: HasFDerivAt for each w, at each v' in the ball
          exact Filter.Eventually.of_forall fun w v' _ => (hpart1 w v').hasFDerivAt
    rw [h_int.fderiv]
    calc ‖∫ w, fderiv ℝ (fun v' =>
            (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v‖
        ≤ ∫ w, ‖fderiv ℝ (fun v' =>
            (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v‖ :=
          norm_integral_le_integral_norm _
      _ ≤ (C₀ * (1 + ‖v‖) ^ M * φ v) * ∫ w, (1 + ‖w‖) ^ M * |φ w| := by
          rw [← integral_mul_left]
          exact integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun w => norm_nonneg _)
            ((integrable_one_add_norm_pow_mul hφ_decay M).const_mul _)
            (Filter.Eventually.of_forall fun w =>
              le_trans (hC₀ v w) (le_of_eq (by ring)))
      _ = C₀ * (∫ w, (1 + ‖w‖) ^ M * |φ w|) * (1 + ‖v‖) ^ M * φ v := by ring
  exact ⟨hpart1, hpart2, hpart3, hpart4⟩

/-- **VelocityDecayConditions for Schwartz-class distributions.**

    Demonstrates the velocity decay conditions are satisfiable by a broad
    class of positive smooth functions with sufficient decay — not just
    Maxwellians. The hypotheses are standard in kinetic theory:

    - φ > 0, smooth, with ‖v‖^k × |φ(v)| integrable for all k (Schwartz decay)
    - Ψ bounded (finite-range interaction kernel)
    - |∂φ/∂vᵢ| ≤ C(1+‖v‖)^K × φ (gradient-to-value bound)
    - |log φ| ≤ C(1+‖v‖)^K (φ doesn't decay super-exponentially)

    For non-Maxwellian φ (e.g. φ(v) = exp(-|v|⁴)), the collision integrands
    are genuinely non-zero. Integrability follows from the general principle:
    Schwartz decay × polynomial growth = integrable. -/
def schwartzDecayConditions {X : Type*} [FlatTorus3 X]
    (Ψ : ℝ → ℝ) (hΨ : ∃ CΨ, ∀ r, |Ψ r| ≤ CΨ) (hΨ_cts : Continuous Ψ)
    -- Ψ is C¹ with bounded derivative (needed for flux differentiability)
    (hΨ_diff : ContDiff ℝ 1 Ψ) (hΨ'_bound : ∃ CΨ', ∀ r, |deriv Ψ r| ≤ CΨ')
    (φ : (Fin 3 → ℝ) → ℝ)
    (hφ_pos : ∀ v, 0 < φ v)
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    -- Schwartz decay: polynomial × |φ| and polynomial × |∂φ| integrable
    (hφ_decay : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    (hφ_deriv_decay : ∀ (k : ℕ) (i : Fin 3),
      Integrable (fun v => ‖v‖ ^ k * |fderiv ℝ φ v (Pi.single i 1)|))
    -- Second derivative bound: |∂²φ/∂vⱼ∂vₖ| ≤ C₂(1+‖v‖)^K₂ × φ(v)
    (hφ_deriv2_bound : ∃ C₂ K₂, ∀ v (j : Fin 3),
      ‖fderiv ℝ (fun v' => fderiv ℝ φ v' (Pi.single j 1)) v‖ ≤ C₂ * (1 + ‖v‖) ^ K₂ * φ v)
    -- Gradient bound: |∂φ/∂vᵢ| ≤ C(1+‖v‖)^K × φ (equiv: ∇ log φ polynomial)
    (hGradBound : ∃ C K, ∀ v i,
      |fderiv ℝ φ v (Pi.single i 1)| ≤ C * (1 + ‖v‖) ^ K * φ v)
    -- Log bound: |log φ| ≤ C(1+‖v‖)^K (equiv: φ ≥ exp(-polynomial))
    (hLogBound : ∃ C K, ∀ v, |Real.log (φ v)| ≤ C * (1 + ‖v‖) ^ K) :
    VelocityDecayConditions (X := X) Ψ (fun _ => φ) zeroField zeroField where
  -- ===== Collision conditions (non-trivial: Schwartz decay dominates) =====
  -- Each integrand is bounded by C × (1+‖v‖)^K × φ(v) × (1+‖w‖)^K × φ(w),
  -- integrable by hφ_decay (polynomial × Schwartz is integrable).
  -- PSD: φ(v)φ(w)⟨Δ,A(v-w)Δ⟩ where Δ = ∇log φ(v) - ∇log φ(w)
  -- |Δ| ≤ C(1+‖v‖)^K + C(1+‖w‖)^K by hGradBound
  -- |A| ≤ CΨ‖v-w‖² by hΨ
  hPSD_inner_int := fun _ v => by
    obtain ⟨CΨ, hCΨ⟩ := hΨ
    obtain ⟨Cg, Kg, hCg⟩ := hGradBound
    have hCΨ_nn : 0 ≤ CΨ := le_trans (abs_nonneg _) (hCΨ 0)
    have hCg_nn : 0 ≤ Cg := by
      have h := hCg 0 0; simp only [norm_zero, add_zero, one_pow] at h
      nlinarith [abs_nonneg (fderiv ℝ φ 0 (Pi.single 0 1)), hφ_pos 0]
    have h_cts : Continuous (PSDIntegrand Ψ φ v) :=
      (psd_integrand_continuous_joint hΨ_cts hφ_smooth hφ_pos).comp
        (continuous_const.prod_mk continuous_id')
    exact integrable_of_schwartz_bound hφ_decay h_cts.aestronglyMeasurable
      (C := 108 * CΨ * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|)
      (K := 2 * Kg + 2)
      (by positivity)
      fun w => by
        rw [show ‖PSDIntegrand Ψ φ v w‖ = |PSDIntegrand Ψ φ v w| from Real.norm_eq_abs _]
        calc |PSDIntegrand Ψ φ v w|
            ≤ (108 * CΨ * Cg ^ 2) * ((1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|) *
              ((1 + ‖w‖) ^ (2 * Kg + 2) * |φ w|) :=
            psd_integrand_bound hφ_smooth hφ_pos hCΨ hCΨ_nn hCg hCg_nn v w
          _ = (108 * CΨ * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|) *
              (1 + ‖w‖) ^ (2 * Kg + 2) * |φ w| := by ring
  hPSD_outer_int := fun _ => by
    obtain ⟨CΨ, hCΨ⟩ := hΨ
    obtain ⟨Cg, Kg, hCg⟩ := hGradBound
    have hCΨ_nn : 0 ≤ CΨ := le_trans (abs_nonneg _) (hCΨ 0)
    have hCg_nn : 0 ≤ Cg := by
      have h := hCg 0 0; simp only [norm_zero, add_zero, one_pow] at h
      nlinarith [abs_nonneg (fderiv ℝ φ 0 (Pi.single 0 1)), hφ_pos 0]
    refine integrable_integral_schwartz hφ_decay ?_ ?_ ?_
      (psd_integrand_bound hφ_smooth hφ_pos hCΨ hCΨ_nn hCg hCg_nn)
    · intro v
      exact integrable_of_schwartz_bound hφ_decay
        ((psd_integrand_continuous_joint hΨ_cts hφ_smooth hφ_pos).comp
          (continuous_const.prod_mk continuous_id')).aestronglyMeasurable
        (C := 108 * CΨ * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|)
        (K := 2 * Kg + 2)
        (by positivity)
        fun w => by
          rw [show ‖PSDIntegrand Ψ φ v w‖ = |PSDIntegrand Ψ φ v w| from Real.norm_eq_abs _]
          calc |PSDIntegrand Ψ φ v w|
              ≤ (108 * CΨ * Cg ^ 2) * ((1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|) *
                ((1 + ‖w‖) ^ (2 * Kg + 2) * |φ w|) :=
              psd_integrand_bound hφ_smooth hφ_pos hCΨ hCΨ_nn hCg hCg_nn v w
            _ = (108 * CΨ * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|) *
                (1 + ‖w‖) ^ (2 * Kg + 2) * |φ w| := by ring
    · exact (psd_integrand_continuous_joint hΨ_cts hφ_smooth hφ_pos).aestronglyMeasurable.integral_prod_right'
    · nlinarith [sq_nonneg Cg]
  hFubini_double := fun _ => by
    obtain ⟨CΨ, hCΨ⟩ := hΨ
    obtain ⟨Cg, Kg, hCg⟩ := hGradBound
    have hCΨ_nn : 0 ≤ CΨ := le_trans (abs_nonneg _) (hCΨ 0)
    have hCg_nn : 0 ≤ Cg := by
      have h := hCg 0 0; simp only [norm_zero, add_zero, one_pow] at h
      nlinarith [abs_nonneg (fderiv ℝ φ 0 (Pi.single 0 1)), hφ_pos 0]
    exact integrable_prod_schwartz_bound hφ_decay
      (fubini_integrand_continuous hΨ_cts hφ_smooth hφ_pos).aestronglyMeasurable
      (by nlinarith [sq_nonneg Cg])
      (fubini_integrand_bound hφ_smooth hφ_pos hCΨ hCΨ_nn hCg hCg_nn)
  hFubini_inner := fun _ v => by
    -- Integrand = ⟨∇logφ(v), flux(v,w)⟩ where ∇logφ(v) is constant in w
    -- Since flux is integrable (vec-valued), dot product with constant is integrable
    have hflux := schwartz_flux_integrable hΨ hΨ_cts hφ_pos hφ_smooth hφ_decay hGradBound v
    -- Each component of the flux is integrable (projection of integrable vector function)
    have hcomp : ∀ i : Fin 3, Integrable (fun w => (landauMatrix Ψ (v - w) *ᵥ
        (φ w • vGrad φ v - φ v • vGrad φ w)) i) := fun i =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).integrable_comp hflux
    -- dotProduct c u = ∑ i, c_i * u_i = c₀*u₀ + c₁*u₁ + c₂*u₂
    simp only [dotProduct, Fin.sum_univ_three]
    exact ((hcomp 0).const_mul _).add ((hcomp 1).const_mul _) |>.add ((hcomp 2).const_mul _)
  hFubini_outer := fun _ => by
    obtain ⟨CΨ, hCΨ⟩ := hΨ
    obtain ⟨Cg, Kg, hCg⟩ := hGradBound
    have hCΨ_nn : 0 ≤ CΨ := le_trans (abs_nonneg _) (hCΨ 0)
    have hCg_nn : 0 ≤ Cg := by
      have h := hCg 0 0; simp only [norm_zero, add_zero, one_pow] at h
      nlinarith [abs_nonneg (fderiv ℝ φ 0 (Pi.single 0 1)), hφ_pos 0]
    refine integrable_integral_schwartz hφ_decay ?_ ?_ ?_
      (fubini_integrand_bound hφ_smooth hφ_pos hCΨ hCΨ_nn hCg hCg_nn)
    · -- ∀ v, Integrable (g v)
      intro v
      have hflux := schwartz_flux_integrable ⟨CΨ, hCΨ⟩ hΨ_cts hφ_pos hφ_smooth hφ_decay
        ⟨Cg, Kg, hCg⟩ v
      have hcomp := fun i =>
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).integrable_comp hflux
      simp only [dotProduct, Fin.sum_univ_three]
      exact ((hcomp 0).const_mul _).add ((hcomp 1).const_mul _) |>.add ((hcomp 2).const_mul _)
    · exact (fubini_integrand_continuous hΨ_cts hφ_smooth hφ_pos).aestronglyMeasurable.integral_prod_right'
    · nlinarith [sq_nonneg Cg]
  -- Flux differentiability: differentiation under the integral sign
  hLandauFluxDiff := fun _ i => by
    obtain ⟨CΨ, hCΨ⟩ := hΨ
    obtain ⟨Cg, Kg, hCg⟩ := hGradBound
    have hlfc := landau_flux_component_diff_with_bound ⟨CΨ, hCΨ⟩ hΨ_cts hΨ_diff hΨ'_bound
        hφ_pos hφ_smooth hφ_decay hφ_deriv2_bound ⟨Cg, Kg, hCg⟩ i
    obtain ⟨hg_diff, ⟨C₀, M, hbound⟩, hderiv_int, _⟩ := hlfc
    have hg_int : ∀ v, Integrable (fun w =>
        (landauMatrix Ψ (v - w) *ᵥ
          (φ w • vGrad φ v - φ v • vGrad φ w)) i) := fun v =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).integrable_comp
        (schwartz_flux_integrable ⟨CΨ, hCΨ⟩ hΨ_cts hφ_pos hφ_smooth hφ_decay ⟨Cg, Kg, hCg⟩ v)
    have hflux_int := fun v => schwartz_flux_integrable ⟨CΨ, hCΨ⟩ hΨ_cts hφ_pos hφ_smooth
      hφ_decay ⟨Cg, Kg, hCg⟩ v
    have heq : (fun v => (∫ w, landauMatrix Ψ (v - w) *ᵥ
        (φ w • vGrad φ v - φ v • vGrad φ w)) i) =
      fun v => ∫ w, (landauMatrix Ψ (v - w) *ᵥ
        (φ w • vGrad φ v - φ v • vGrad φ w)) i :=
      funext fun v => ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).integral_comp_comm
        (hflux_int v)).symm
    rw [heq]
    exact differentiable_integral_of_product_dominated hg_diff hg_int
      (continuous_const.mul (((continuous_const.add continuous_norm).pow M).mul hφ_smooth.continuous))
      (integrable_one_add_norm_pow_mul hφ_decay M)
      (fun w => mul_nonneg (pow_nonneg (by linarith [norm_nonneg w]) _) (abs_nonneg _))
      (fun v w => hbound v w)
      hderiv_int
  -- Derivative-of-flux × log integrability: follows from flux derivative Schwartz bound
  -- |d/dv_i flux_i(v)| ≤ C₁(1+‖v‖)^M₁ φ(v) and |log φ(v)| ≤ Cl(1+‖v‖)^Kl
  -- so product ≤ C₁*Cl*(1+‖v‖)^(M₁+Kl)*φ(v), integrable by Schwartz decay
  hLandauIBP_df_g := fun _ i => by
    obtain ⟨CΨ, hCΨ⟩ := hΨ
    obtain ⟨Cg, Kg, hCg⟩ := hGradBound
    obtain ⟨Cl, Kl, hCl⟩ := hLogBound
    have hlfc := landau_flux_component_diff_with_bound ⟨CΨ, hCΨ⟩ hΨ_cts hΨ_diff hΨ'_bound
        hφ_pos hφ_smooth hφ_decay hφ_deriv2_bound ⟨Cg, Kg, hCg⟩ i
    obtain ⟨_, _, _, ⟨C₁, M₁, hflux_bound⟩⟩ := hlfc
    -- Rewrite goal: (∫ w, F v w) i = ∫ w, (F v w) i
    have hflux_int := fun v => schwartz_flux_integrable ⟨CΨ, hCΨ⟩ hΨ_cts hφ_pos hφ_smooth
      hφ_decay ⟨Cg, Kg, hCg⟩ v
    have heq : ∀ v, (∫ w, landauMatrix Ψ (v - w) *ᵥ
        (φ w • vGrad φ v - φ v • vGrad φ w)) i =
      ∫ w, (landauMatrix Ψ (v - w) *ᵥ
        (φ w • vGrad φ v - φ v • vGrad φ w)) i :=
      fun v => ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).integral_comp_comm
        (hflux_int v)).symm
    simp_rw [heq]
    -- Now goal has ∫ w, (F v w) i and the bound from hlfc applies
    -- |fderiv(...) v (Pi.single i 1)| ≤ ‖fderiv(...) v‖ ≤ C₁(1+‖v‖)^M₁ φ(v)
    -- |log φ v| ≤ Cl(1+‖v‖)^Kl
    -- Product ≤ C₁*Cl*(1+‖v‖)^(M₁+Kl) * φ(v) ≤ C₁*Cl*(1+‖v‖)^(M₁+Kl) * |φ(v)|
    have hCl_nn : 0 ≤ Cl := by
      have h := hCl 0; simp only [norm_zero, add_zero, one_pow, mul_one] at h
      exact le_trans (abs_nonneg _) h
    have hC₁_nn : 0 ≤ C₁ := by
      have h := hflux_bound 0
      simp only [norm_zero, add_zero, one_pow, mul_one] at h
      nlinarith [norm_nonneg (fderiv ℝ (fun v' => ∫ w, (landauMatrix Ψ (v' - w) *ᵥ
        (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) 0), hφ_pos 0]
    have hdom : Integrable (fun v => C₁ * Cl * ((1 + ‖v‖) ^ (M₁ + Kl) * |φ v|)) :=
      (integrable_one_add_norm_pow_mul hφ_decay (M₁ + Kl)).const_mul _
    apply hdom.mono'
    · exact (measurable_fderiv_apply_const ℝ _ (Pi.single i 1)).aestronglyMeasurable.mul
        ((hφ_smooth.log (fun v => ne_of_gt (hφ_pos v))).continuous.aestronglyMeasurable)
    · filter_upwards with v
      rw [Real.norm_eq_abs, abs_mul]
      have hpi_norm : ‖(Pi.single i (1:ℝ) : Fin 3 → ℝ)‖ ≤ 1 := by
        simp [Pi.norm_def, Pi.single_apply, Finset.sup_le_iff]; intro j; split <;> simp
      set L := fderiv ℝ (fun v' => ∫ w, (landauMatrix Ψ (v' - w) *ᵥ
          (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v
      have h1 : |L (Pi.single i 1)| ≤ ‖L‖ := by
        calc |L (Pi.single i 1)| = ‖L (Pi.single i 1)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖L‖ * ‖(Pi.single i (1:ℝ) : Fin 3 → ℝ)‖ := L.le_opNorm _
          _ ≤ ‖L‖ * 1 := by gcongr
          _ = ‖L‖ := mul_one _
      have hCl_v : |(Real.log ∘ φ) v| ≤ Cl * (1 + ‖v‖) ^ Kl := hCl v
      have hflux_v := hflux_bound v
      have h1v : 0 ≤ 1 + ‖v‖ := by linarith [norm_nonneg v]
      calc |L (Pi.single i 1)| * |(Real.log ∘ φ) v|
          ≤ ‖L‖ * |(Real.log ∘ φ) v| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ ≤ ‖L‖ * (Cl * (1 + ‖v‖) ^ Kl) :=
            mul_le_mul_of_nonneg_left hCl_v (norm_nonneg _)
        _ ≤ (C₁ * (1 + ‖v‖) ^ M₁ * φ v) * (Cl * (1 + ‖v‖) ^ Kl) :=
            mul_le_mul_of_nonneg_right hflux_v (mul_nonneg hCl_nn (pow_nonneg h1v _))
        _ = C₁ * Cl * ((1 + ‖v‖) ^ (M₁ + Kl) * φ v) := by rw [pow_add]; ring
        _ ≤ C₁ * Cl * ((1 + ‖v‖) ^ (M₁ + Kl) * |φ v|) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self _)
              (pow_nonneg h1v _)) (mul_nonneg hC₁_nn hCl_nn)
  hLandauIBP_f_dg := by
    intro _ i
    obtain ⟨CΨ, hCΨ⟩ := hΨ
    obtain ⟨Cg, Kg, hCg⟩ := hGradBound
    have hCΨ_nn : 0 ≤ CΨ := le_trans (abs_nonneg _) (hCΨ 0)
    have hCg_nn : 0 ≤ Cg := by
      have h := hCg 0 0; simp only [norm_zero, add_zero, one_pow] at h
      nlinarith [abs_nonneg (fderiv ℝ φ 0 (Pi.single 0 1)), hφ_pos 0]
    set I := ∫ w, (1 + ‖w‖) ^ (Kg + 2) * |φ w|
    have hI_nn : 0 ≤ I := integral_nonneg fun w => mul_nonneg
      (pow_nonneg (by linarith [norm_nonneg w]) _) (abs_nonneg _)
    set Cf := 18 * CΨ * Cg * I
    set M := 2 * Kg + 2
    have hCf_nn : 0 ≤ Cf := mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hCΨ_nn) hCg_nn) hI_nn
    have hdom : Integrable (fun v => Cf * Cg * ((1 + ‖v‖) ^ M * |φ v|)) :=
      (integrable_one_add_norm_pow_mul hφ_decay M).const_mul _
    apply hdom.mono'
    · -- Measurability: flux integral component × fderiv(log ∘ φ)
      exact (((continuous_apply i).comp_aestronglyMeasurable
        (landau_flux_integral_aestronglyMeasurable hΨ_cts hφ_smooth)).aemeasurable.mul
        ((ContDiff.continuous_fderiv
          ((hφ_smooth.log (fun v => ne_of_gt (hφ_pos v))).of_le le_top) le_rfl).clm_apply
          continuous_const).aemeasurable).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_mul]
        set flux_v := ∫ w, landauMatrix Ψ (v - w) *ᵥ
            (φ w • vGrad φ v - φ v • vGrad φ w)
        have h_flux_bound : |flux_v i| ≤ Cf * (1 + ‖v‖) ^ (Kg + 2) * φ v := by
          calc |flux_v i|
              ≤ ‖flux_v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i
            _ ≤ ∫ w, ‖landauMatrix Ψ (v - w) *ᵥ
                  (φ w • vGrad φ v - φ v • vGrad φ w)‖ :=
                norm_integral_le_integral_norm (μ := volume) _
            _ ≤ ∫ w, (18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v *
                  ((1 + ‖w‖) ^ (Kg + 2) * |φ w|)) := by
                apply integral_mono_of_nonneg
                  (Filter.Eventually.of_forall fun w => norm_nonneg _)
                  ((integrable_one_add_norm_pow_mul hφ_decay (Kg + 2)).const_mul _)
                  (Filter.Eventually.of_forall fun w =>
                    le_trans (landau_flux_pointwise_bound hCΨ hCΨ_nn hCg hCg_nn hφ_pos v w)
                      (by apply mul_le_mul_of_nonneg_left
                          · exact mul_le_mul_of_nonneg_left (le_abs_self _)
                              (pow_nonneg (by linarith [norm_nonneg w]) _)
                          · apply mul_nonneg _ (le_of_lt (hφ_pos v))
                            apply mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hCΨ_nn) hCg_nn)
                              (pow_nonneg (by linarith [norm_nonneg v]) _)))
            _ = 18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v * I := integral_mul_left _ _
            _ = Cf * (1 + ‖v‖) ^ (Kg + 2) * φ v := by ring
        -- |∂(log∘φ)/∂vi| = |∂φ/∂vi|/φ(v) ≤ Cg * (1+‖v‖)^Kg
        have h_dlog : |fderiv ℝ (Real.log ∘ φ) v (Pi.single i 1)| ≤
            Cg * (1 + ‖v‖) ^ Kg := by
          rw [vGrad_log_eq_div (hφ_smooth.differentiable le_top) hφ_pos v i, abs_div,
              abs_of_pos (hφ_pos v)]
          exact div_le_of_le_mul₀ (le_of_lt (hφ_pos v))
            (mul_nonneg hCg_nn (pow_nonneg (by linarith [norm_nonneg v]) _))
            (hCg v i)
        calc |flux_v i| * |fderiv ℝ (Real.log ∘ φ) v (Pi.single i 1)|
            ≤ (Cf * (1 + ‖v‖) ^ (Kg + 2) * φ v) *
                (Cg * (1 + ‖v‖) ^ Kg) := mul_le_mul h_flux_bound h_dlog
              (abs_nonneg _)
              (mul_nonneg (mul_nonneg hCf_nn (pow_nonneg (by linarith [norm_nonneg v]) _))
                (le_of_lt (hφ_pos v)))
          _ = Cf * Cg * ((1 + ‖v‖) ^ M * φ v) := by
              simp only [M]; rw [show 2 * Kg + 2 = Kg + 2 + Kg from by omega, pow_add]; ring
          _ ≤ Cf * Cg * ((1 + ‖v‖) ^ M * |φ v|) := by
              gcongr; exact le_abs_self _
  hLandauIBP_fg := by
    intro _ i
    obtain ⟨CΨ, hCΨ⟩ := hΨ
    obtain ⟨Cg, Kg, hCg⟩ := hGradBound
    obtain ⟨Clog, Klog, hlog⟩ := hLogBound
    have hCΨ_nn : 0 ≤ CΨ := le_trans (abs_nonneg _) (hCΨ 0)
    have hCg_nn : 0 ≤ Cg := by
      have h := hCg 0 0; simp only [norm_zero, add_zero, one_pow] at h
      nlinarith [abs_nonneg (fderiv ℝ φ 0 (Pi.single 0 1)), hφ_pos 0]
    -- I = ∫ (1+‖w‖)^(Kg+2) * |φ(w)| (finite by Schwartz decay)
    set I := ∫ w, (1 + ‖w‖) ^ (Kg + 2) * |φ w|
    have hI_nn : 0 ≤ I := integral_nonneg fun w => mul_nonneg
      (pow_nonneg (by linarith [norm_nonneg w]) _) (abs_nonneg _)
    -- Total constant and power
    set Cf := 18 * CΨ * Cg * I
    set M := Kg + 2 + Klog
    have hCf_nn : 0 ≤ Cf := mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hCΨ_nn) hCg_nn) hI_nn
    have hClog_nn : 0 ≤ |Clog| := abs_nonneg _
    -- Dominator: Cf * |Clog| * (1+‖v‖)^M * |φ(v)|
    have hdom : Integrable (fun v => Cf * |Clog| * ((1 + ‖v‖) ^ M * |φ v|)) :=
      (integrable_one_add_norm_pow_mul hφ_decay M).const_mul _
    apply hdom.mono'
    · -- Measurability: flux integral component × log φ
      exact (((continuous_apply i).comp_aestronglyMeasurable
        (landau_flux_integral_aestronglyMeasurable hΨ_cts hφ_smooth)).aemeasurable.mul
        (hφ_smooth.continuous.log (fun v => ne_of_gt (hφ_pos v))).aemeasurable).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_mul]
        -- Key: bound ‖∫ w, flux(v,w)‖ using pointwise bound + integral monotonicity
        -- Abbreviate the flux integral for readability
        set flux_v := ∫ w, landauMatrix Ψ (v - w) *ᵥ
            (φ w • vGrad φ v - φ v • vGrad φ w)
        have h_flux_bound : |flux_v i| ≤ Cf * (1 + ‖v‖) ^ (Kg + 2) * φ v := by
          calc |flux_v i|
              ≤ ‖flux_v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i
            _ ≤ ∫ w, ‖landauMatrix Ψ (v - w) *ᵥ
                  (φ w • vGrad φ v - φ v • vGrad φ w)‖ :=
                norm_integral_le_integral_norm (μ := volume) _
            _ ≤ ∫ w, (18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v *
                  ((1 + ‖w‖) ^ (Kg + 2) * |φ w|)) := by
                apply integral_mono_of_nonneg
                  (Filter.Eventually.of_forall fun w => norm_nonneg _)
                  ((integrable_one_add_norm_pow_mul hφ_decay (Kg + 2)).const_mul _)
                  (Filter.Eventually.of_forall fun w =>
                    le_trans (landau_flux_pointwise_bound hCΨ hCΨ_nn hCg hCg_nn hφ_pos v w)
                      (by apply mul_le_mul_of_nonneg_left
                          · exact mul_le_mul_of_nonneg_left (le_abs_self _)
                              (pow_nonneg (by linarith [norm_nonneg w]) _)
                          · apply mul_nonneg _ (le_of_lt (hφ_pos v))
                            apply mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hCΨ_nn) hCg_nn)
                              (pow_nonneg (by linarith [norm_nonneg v]) _)))
            _ = 18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v * I := integral_mul_left _ _
            _ = Cf * (1 + ‖v‖) ^ (Kg + 2) * φ v := by ring
        calc |flux_v i| * |(Real.log ∘ φ) v|
            ≤ (Cf * (1 + ‖v‖) ^ (Kg + 2) * φ v) *
                (|Clog| * (1 + ‖v‖) ^ Klog) := by
              apply mul_le_mul h_flux_bound
              · exact le_trans (hlog v) (mul_le_mul_of_nonneg_right (le_abs_self _)
                  (pow_nonneg (by linarith [norm_nonneg v]) _))
              · exact abs_nonneg _
              · exact mul_nonneg (mul_nonneg hCf_nn (pow_nonneg (by linarith [norm_nonneg v]) _))
                  (le_of_lt (hφ_pos v))
          _ = Cf * |Clog| * ((1 + ‖v‖) ^ M * φ v) := by
              simp only [M]; rw [pow_add]; ring
          _ ≤ Cf * |Clog| * ((1 + ‖v‖) ^ M * |φ v|) := by
              gcongr; exact le_abs_self _
  hLandauFluxInt := fun _ v =>
    schwartz_flux_integrable hΨ hΨ_cts hφ_pos hφ_smooth hφ_decay hGradBound v
  -- ===== Transport/force conditions (trivially 0) =====
  -- gradX of spatially-constant function = 0; E = B = 0.
  hSpatialTransport_int := by
    intro x
    have : (fun v => v ⬝ᵥ FlatTorus3.gradX (fun _ => φ v) x *
        Real.log (φ v)) = fun _ => 0 := by
      ext v; simp [gradX_const_fun φ v x, dotProduct]
    rw [this]; exact integrable_zero _ _ _
  hForceTransport_int := by
    intro x
    have : (fun v => (zeroField (X := X) x + cross v (zeroField x)) ⬝ᵥ
        vGrad φ v * Real.log (φ v)) = fun _ => 0 := by
      ext v; rw [force_zero]; simp [dotProduct]
    rw [this]; exact integrable_zero _ _ _
  hForceIBP_f_dg := by
    intro x i
    have : (fun v => (zeroField (X := X) x + cross v (zeroField x)) i *
        fderiv ℝ (fun w => φ w * Real.log (φ w) - φ w) v
          (Pi.single i 1)) = fun _ => 0 := by
      ext v; rw [force_zero]; simp
    rw [this]; exact integrable_zero _ _ _
  hForceIBP_fg := by
    intro x i
    have : (fun v => (zeroField (X := X) x + cross v (zeroField x)) i *
        (φ v * Real.log (φ v) - φ v)) = fun _ => 0 := by
      ext v; rw [force_zero]; simp
    rw [this]; exact integrable_zero _ _ _
  hSpatialTransport_joint := by
    have : (Function.uncurry (fun (x : X) (v : Fin 3 → ℝ) =>
        v ⬝ᵥ FlatTorus3.gradX (fun _ => φ v) x *
        Real.log (φ v))) = fun _ => 0 := by
      ext ⟨x, v⟩
      simp only [Function.uncurry]
      simp [gradX_const_fun φ v x, dotProduct]
    rw [this]; exact integrable_zero _ _ _
  hSpatTransComp := by
    intro v i
    have : (fun (x : X) => FlatTorus3.gradX (fun _ => φ v) x i *
        Real.log (φ v)) = fun _ => 0 := by
      ext x; simp [gradX_const_fun φ v x]
    rw [this]; exact integrable_zero _ _ _
  hf_velocity_dominated := by
    -- f(x,v) = φ(v) is independent of x, so g = |φ|
    refine ⟨fun v => |φ v|, ?_, fun _ v => le_abs_self _⟩
    exact (hφ_decay 0).congr (.of_forall fun v => by simp)
  hPSD_cont := fun _ =>
    psd_integrand_continuous_joint hΨ_cts hφ_smooth hφ_pos
  hD_cont := continuous_const

/-- Bound on a Lorentz force component: |(E₀ + v × B₀)ᵢ| ≤ C·(1 + ‖v‖).
    Each cross product component is bilinear in v, B₀, hence linear in ‖v‖.
    Proved by Aristotle. -/
lemma lorentz_component_bound (E₀ B₀ : Fin 3 → ℝ) :
    ∃ CL : ℝ, 0 ≤ CL ∧ ∀ (v : Fin 3 → ℝ) (i : Fin 3),
      |(E₀ + cross v B₀) i| ≤ CL * (1 + ‖v‖) := by
  simp only [cross]
  use ‖E₀‖ + ∑ i, ‖B₀ i‖ * 3 + 1
  refine' ⟨ by positivity, fun v i => _ ⟩ ; fin_cases i <;> simp +decide [ Fin.sum_univ_succ ] <;> ring_nf
  · have h_triangle : |E₀ 0 + (v 1 * B₀ 2 - v 2 * B₀ 1)| ≤ |E₀ 0| + |v 1 * B₀ 2| + |v 2 * B₀ 1| := by
      cases abs_cases ( E₀ 0 + ( v 1 * B₀ 2 - v 2 * B₀ 1 ) ) <;> cases abs_cases ( E₀ 0 ) <;> cases abs_cases ( v 1 * B₀ 2 ) <;> cases abs_cases ( v 2 * B₀ 1 ) <;> linarith
    have h_triangle2 : |E₀ 0| ≤ ‖E₀‖ ∧ |v 1 * B₀ 2| ≤ ‖v‖ * |B₀ 2| ∧ |v 2 * B₀ 1| ≤ ‖v‖ * |B₀ 1| := by
      exact ⟨ by simpa using norm_le_pi_norm E₀ 0, by simpa [ abs_mul ] using mul_le_mul_of_nonneg_right ( norm_le_pi_norm v 1 ) ( abs_nonneg _ ), by simpa [ abs_mul ] using mul_le_mul_of_nonneg_right ( norm_le_pi_norm v 2 ) ( abs_nonneg _ ) ⟩
    nlinarith [ abs_nonneg ( E₀ 0 ), abs_nonneg ( v 1 * B₀ 2 ), abs_nonneg ( v 2 * B₀ 1 ), abs_nonneg ( B₀ 0 ), abs_nonneg ( B₀ 1 ), abs_nonneg ( B₀ 2 ), norm_nonneg E₀, norm_nonneg v ]
  · have h_triangle : |E₀ 1| ≤ ‖E₀‖ ∧ |v 2 * B₀ 0| ≤ ‖v‖ * |B₀ 0| ∧ |v 0 * B₀ 2| ≤ ‖v‖ * |B₀ 2| := by
      exact ⟨ by simpa using norm_le_pi_norm E₀ 1, by rw [ abs_mul ] ; exact mul_le_mul_of_nonneg_right ( norm_le_pi_norm v 2 ) ( abs_nonneg _ ), by rw [ abs_mul ] ; exact mul_le_mul_of_nonneg_right ( norm_le_pi_norm v 0 ) ( abs_nonneg _ ) ⟩
    exact abs_le.mpr ⟨ by nlinarith [ abs_le.mp h_triangle.1, abs_le.mp h_triangle.2.1, abs_le.mp h_triangle.2.2, abs_nonneg ( B₀ 0 ), abs_nonneg ( B₀ 1 ), abs_nonneg ( B₀ 2 ), norm_nonneg v ], by nlinarith [ abs_le.mp h_triangle.1, abs_le.mp h_triangle.2.1, abs_le.mp h_triangle.2.2, abs_nonneg ( B₀ 0 ), abs_nonneg ( B₀ 1 ), abs_nonneg ( B₀ 2 ), norm_nonneg v ] ⟩
  · have h_triangle : abs (E₀ 2 + (v 0 * B₀ 1 - v 1 * B₀ 0)) ≤ abs (E₀ 2) + abs (v 0 * B₀ 1) + abs (v 1 * B₀ 0) := by
      cases abs_cases ( E₀ 2 + ( v 0 * B₀ 1 - v 1 * B₀ 0 ) ) <;> cases abs_cases ( E₀ 2 ) <;> cases abs_cases ( v 0 * B₀ 1 ) <;> cases abs_cases ( v 1 * B₀ 0 ) <;> linarith
    norm_num [ abs_mul ] at * ; nlinarith! [ abs_nonneg ( E₀ 2 ), abs_nonneg ( v 0 ), abs_nonneg ( v 1 ), abs_nonneg ( B₀ 0 ), abs_nonneg ( B₀ 1 ), abs_nonneg ( B₀ 2 ), show ‖E₀‖ ≥ |E₀ 2| by exact norm_le_pi_norm E₀ 2, show ‖v‖ ≥ |v 0| by exact norm_le_pi_norm v 0, show ‖v‖ ≥ |v 1| by exact norm_le_pi_norm v 1 ]


end VML
