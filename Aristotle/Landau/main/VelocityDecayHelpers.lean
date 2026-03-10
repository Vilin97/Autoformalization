/-
  Helper lemmas for constructing VelocityDecayConditions instances.

  Provides the Schwartz-class construction: for smooth Ψ with polynomial
  growth, and Schwartz-class f with polynomial score bound, all 19
  velocity decay conditions hold.
-/
import Aristotle.Landau.main.Theorem42
import Aristotle.Landau.main.LandauMatrixDerivBound

open Matrix Finset BigOperators Real MeasureTheory

noncomputable section
namespace VML

/-- Zero field. -/
def zeroField {X : Type*} (_ : X) : Fin 3 → ℝ := 0

variable {X : Type*} [FlatTorus3 X]

-- ============================================================================
-- Schwartz-class VelocityDecayConditions
--
-- For a positive smooth function φ with Schwartz-like decay, bounded Ψ,
-- and polynomial growth of ∇ log φ and log φ, all 19 velocity decay
-- conditions are satisfied. The Landau flux does NOT vanish for
-- non-Maxwellian φ — the collision integrands are genuinely non-zero.
-- ============================================================================

-- Helper lemmas: polynomial × Schwartz decay is integrable
-- Proved by Aristotle (Harmonic)

/-- If ‖v‖^k * |φ(v)| is integrable for every k, then (1+‖v‖)^K * |φ(v)| is too.
    Uses the binomial theorem to expand (1+‖v‖)^K as a finite sum. -/
lemma integrable_one_add_norm_pow_mul
    {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    (K : ℕ) :
    Integrable (fun v => (1 + ‖v‖) ^ K * |φ v|) := by
  have h_binom : ∀ v : (Fin 3 → ℝ), (1 + ‖v‖) ^ K * |φ v| =
      ∑ k ∈ Finset.range (K + 1), Nat.choose K k * ‖v‖ ^ k * |φ v| := by
    simp +decide [add_comm (1 : ℝ), add_pow, mul_assoc, mul_comm, mul_left_comm,
      Finset.mul_sum _ _ _]
  simp_rw [h_binom]
  exact MeasureTheory.integrable_finset_sum _ fun k _ => by
    simpa only [mul_assoc] using MeasureTheory.Integrable.const_mul (hφ k) _

/-- If ‖v‖^k * |φ(v)| is integrable for every k, and ‖g(v)‖ ≤ C*(1+‖v‖)^K*|φ(v)|,
    then g is integrable. Core tool for Schwartz-dominance arguments. -/
lemma integrable_of_schwartz_bound
    {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    {g : (Fin 3 → ℝ) → ℝ}
    (hg_meas : AEStronglyMeasurable g)
    {C : ℝ} (_ : 0 ≤ C) {K : ℕ}
    (hbound : ∀ v, ‖g v‖ ≤ C * (1 + ‖v‖) ^ K * |φ v|) :
    Integrable g := by
  have hdom : Integrable (fun v => C * ((1 + ‖v‖) ^ K * |φ v|)) :=
    (integrable_one_add_norm_pow_mul hφ K).const_mul C
  exact hdom.mono' hg_meas (by
    filter_upwards with v
    calc ‖g v‖ ≤ C * (1 + ‖v‖) ^ K * |φ v| := hbound v
    _ = C * ((1 + ‖v‖) ^ K * |φ v|) := by ring)

-- Helper lemmas for bounding collision integrands.
-- All proved by Aristotle (Harmonic); proofs to be ported.

/-- ‖α • a - β • b‖ ≤ |α| * ‖a‖ + |β| * ‖b‖. -/
private lemma norm_smul_sub_le_of_smul (a b : Fin 3 → ℝ) (α β : ℝ) :
    ‖α • a - β • b‖ ≤ |α| * ‖a‖ + |β| * ‖b‖ :=
  calc ‖α • a - β • b‖ ≤ ‖α • a‖ + ‖β • b‖ := norm_sub_le _ _
  _ = |α| * ‖a‖ + |β| * ‖b‖ := by simp [norm_smul]

/-- ‖M *ᵥ u‖ ≤ 3 * B * ‖u‖ when all |M i j| ≤ B (for 3×3 matrices). -/
lemma norm_mulVec_le_of_entry_bound (M : Matrix (Fin 3) (Fin 3) ℝ)
    (u : Fin 3 → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hM : ∀ i j, |M i j| ≤ B) :
    ‖mulVec M u‖ ≤ 3 * B * ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  simp only [mulVec, dotProduct]
  calc |∑ j : Fin 3, M i j * u j|
      ≤ ∑ j : Fin 3, |M i j * u j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, B * ‖u‖ := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul (hM i j) (norm_le_pi_norm u j) (abs_nonneg _) hB
    _ = 3 * B * ‖u‖ := by simp [Fin.sum_univ_three]; ring

/-- Each entry of innerLandauMatrix z is bounded by normSq z. -/
lemma innerLandauMatrix_entry_le (z : Fin 3 → ℝ) (i j : Fin 3) :
    |innerLandauMatrix z i j| ≤ normSq z := by
  rw [innerLandauMatrix_apply]
  have hns : normSq z = ∑ k : Fin 3, z k * z k := by
    simp [normSq, dotProduct, Fin.sum_univ_three]
  split_ifs with hij
  · -- diagonal: |normSq z - zᵢ * zᵢ| ≤ normSq z
    subst hij
    rw [hns]; simp only [Fin.sum_univ_three]
    fin_cases i <;> simp <;> (rw [abs_of_nonneg (by nlinarith [mul_self_nonneg (z 0), mul_self_nonneg (z 1), mul_self_nonneg (z 2)])]; nlinarith [mul_self_nonneg (z 0), mul_self_nonneg (z 1), mul_self_nonneg (z 2)])
  · -- off-diagonal: |0 - zᵢ * zⱼ| ≤ normSq z
    simp only [zero_sub, abs_neg]
    rw [hns]; simp only [Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp_all <;>
      nlinarith [sq_nonneg (|z 0| - |z 1|), sq_nonneg (|z 0| - |z 2|),
        sq_nonneg (|z 1| - |z 2|),
        abs_mul_abs_self (z 0), abs_mul_abs_self (z 1), abs_mul_abs_self (z 2)]

/-- Bound on landauMatrix entries: |A(z)_{ij}| ≤ CΨ * normSq z. -/
lemma landauMatrix_entry_le (Ψ : ℝ → ℝ) {CΨ : ℝ} (hΨ : ∀ r, |Ψ r| ≤ CΨ)
    (z : Fin 3 → ℝ) (i j : Fin 3) :
    |landauMatrix Ψ z i j| ≤ CΨ * normSq z := by
  simp only [landauMatrix, smul_apply, smul_eq_mul]
  calc |Ψ (eucNorm z) * innerLandauMatrix z i j|
      = |Ψ (eucNorm z)| * |innerLandauMatrix z i j| := abs_mul _ _
    _ ≤ CΨ * normSq z := by
        exact mul_le_mul (hΨ _) (innerLandauMatrix_entry_le z i j)
          (abs_nonneg _) (le_trans (abs_nonneg _) (hΨ 0))


/-- Product-space integrability from Schwartz decay:
    if |g(v,w)| ≤ C * (1+‖v‖)^K₁ * |φ(v)| * (1+‖w‖)^K₂ * |φ(w)|,
    then g is integrable on the product space. -/
lemma integrable_prod_schwartz_bound
    {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    {g : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ}
    (hg_meas : AEStronglyMeasurable g (volume.prod volume))
    {C : ℝ} (hC : 0 ≤ C) {K₁ K₂ : ℕ}
    (hbound : ∀ v w, |g (v, w)| ≤ C * ((1 + ‖v‖) ^ K₁ * |φ v|) *
      ((1 + ‖w‖) ^ K₂ * |φ w|)) :
    Integrable g (volume.prod volume) := by
  have h_integrable : Integrable (fun (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) =>
      C * ((1 + ‖p.1‖) ^ K₁ * |φ p.1|) * ((1 + ‖p.2‖) ^ K₂ * |φ p.2|))
      (volume.prod volume) := by
    suffices h : Integrable (fun v => (1 + ‖v‖) ^ K₁ * |φ v|) ∧
        Integrable (fun w => (1 + ‖w‖) ^ K₂ * |φ w|) by
      convert h.1.prod_mul h.2 |> fun h => h.const_mul C using 1; ring!
    exact ⟨integrable_one_add_norm_pow_mul hφ K₁, integrable_one_add_norm_pow_mul hφ K₂⟩
  exact h_integrable.mono' hg_meas (Filter.Eventually.of_forall fun p => hbound p.1 p.2)

/-- Integrability of iterated integral from Schwartz decay.
    Proved by Aristotle (Harmonic). -/
private lemma integrable_integral_schwartz
    {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    {g : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ}
    (hg_int : ∀ v, Integrable (g v))
    (hg_meas : AEStronglyMeasurable (fun v => ∫ w, g v w))
    {C : ℝ} (hC : 0 ≤ C) {K₁ K₂ : ℕ}
    (hbound : ∀ v w, |g v w| ≤ C * ((1 + ‖v‖) ^ K₁ * |φ v|) *
      ((1 + ‖w‖) ^ K₂ * |φ w|)) :
    Integrable (fun v => ∫ w, g v w) := by
  refine' (((integrable_one_add_norm_pow_mul hφ K₁).const_mul C).mul_const
    (∫ w, (1 + ‖w‖) ^ K₂ * |φ w|)).mono' hg_meas _
  filter_upwards with v
  exact le_trans (norm_integral_le_integral_norm _) (by
    rw [← integral_const_mul]
    exact integral_mono (hg_int v).norm
      ((integrable_one_add_norm_pow_mul hφ K₂).const_mul _)
      (fun w => by
        rw [Real.norm_eq_abs]
        exact le_trans (hbound v w) (by ring_nf; rfl)))

/-- Differentiation under the integral sign for Schwartz-dominated integrands.
    Uses `hasFDerivAt_integral_of_dominated_of_fderiv_le` from Mathlib. -/
private lemma differentiable_integral_of_schwartz_dominated
    {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    {g : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ}
    (hg_diff : ∀ w, Differentiable ℝ (fun v => g v w))
    (hg_int : ∀ v, Integrable (g v))
    {C : ℝ} {K : ℕ}
    (hderiv_bound : ∀ v w, ‖fderiv ℝ (fun v' => g v' w) v‖ ≤
      C * (1 + ‖w‖) ^ K * |φ w|)
    (hderiv_int : ∀ v, Integrable (fun w => fderiv ℝ (fun v' => g v' w) v)) :
    Differentiable ℝ (fun v => ∫ w, g v w) := by
  intro v₀
  have hbound_int : Integrable (fun w => C * (1 + ‖w‖) ^ K * |φ w|) := by
    convert (integrable_one_add_norm_pow_mul hφ K).const_mul C using 1; ext; ring
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun v w => fderiv ℝ (fun v' => g v' w) v)
    (ε := 1) one_pos
    (Filter.Eventually.of_forall fun v => (hg_int v).aestronglyMeasurable)
    (hg_int v₀)
    (hderiv_int v₀).aestronglyMeasurable
    (ae_of_all _ fun w v _ => hderiv_bound v w)
    hbound_int
    (ae_of_all _ fun w v _ => (hg_diff w).differentiableAt.hasFDerivAt)).differentiableAt

/-- Differentiation under the integral sign with product-form bound.

    Unlike `differentiable_integral_of_schwartz_dominated`, this allows the derivative
    bound to depend on v: ‖D_v g(v,w)‖ ≤ P(v) * Q(w) where P is continuous and
    Q is integrable. The proof localizes to a compact ball around each v₀ where
    P is bounded. -/
private lemma differentiable_integral_of_product_dominated
    {g : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ}
    (hg_diff : ∀ w, Differentiable ℝ (fun v => g v w))
    (hg_int : ∀ v, Integrable (g v))
    {P : (Fin 3 → ℝ) → ℝ} (hP : Continuous P)
    {Q : (Fin 3 → ℝ) → ℝ} (hQ_int : Integrable Q) (hQ_nn : ∀ w, 0 ≤ Q w)
    (hderiv_bound : ∀ v w, ‖fderiv ℝ (fun v' => g v' w) v‖ ≤ P v * Q w)
    (hderiv_int : ∀ v, Integrable (fun w => fderiv ℝ (fun v' => g v' w) v)) :
    Differentiable ℝ (fun v => ∫ w, g v w) := by
  intro v₀
  -- P is continuous → bounded on compact ball
  have hP_bound : ∃ M, ∀ v ∈ Metric.closedBall v₀ 1, P v ≤ M := by
    have := isCompact_closedBall (x := v₀) (α := Fin 3 → ℝ) 1
    exact ⟨sSup (P '' Metric.closedBall v₀ 1),
      fun v hv => le_csSup (this.image hP).bddAbove ⟨v, hv, rfl⟩⟩
  obtain ⟨M, hM⟩ := hP_bound
  -- Bound in ball: ‖D_v g(v,w)‖ ≤ M * Q(w)
  have hball_bound : ∀ w, ∀ v ∈ Metric.ball v₀ 1,
      ‖fderiv ℝ (fun v' => g v' w) v‖ ≤ M * Q w := fun w v hv => by
    exact le_trans (hderiv_bound v w) (mul_le_mul_of_nonneg_right
      (hM v (Metric.ball_subset_closedBall hv)) (hQ_nn w))
  have hdom_int : Integrable (fun w => M * Q w) := hQ_int.const_mul M
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun v w => fderiv ℝ (fun v' => g v' w) v)
    (ε := 1) one_pos
    (Filter.Eventually.of_forall fun v => (hg_int v).aestronglyMeasurable)
    (hg_int v₀)
    (hderiv_int v₀).aestronglyMeasurable
    (ae_of_all _ fun w v hv => hball_bound w v hv)
    hdom_int
    (ae_of_all _ fun w v _ => (hg_diff w).differentiableAt.hasFDerivAt)).differentiableAt

/-- ∂(log ∘ φ)/∂vᵢ = (∂φ/∂vᵢ) / φ(v) when φ is differentiable and positive. -/
private lemma vGrad_log_eq_div {φ : (Fin 3 → ℝ) → ℝ}
    (hφ_diff : Differentiable ℝ φ) (hφ_pos : ∀ v, 0 < φ v)
    (v : Fin 3 → ℝ) (i : Fin 3) :
    fderiv ℝ (Real.log ∘ φ) v (Pi.single i 1) =
      fderiv ℝ φ v (Pi.single i 1) / φ v := by
  erw [fderiv_comp] <;> norm_num [hφ_diff.differentiableAt, hφ_pos, ne_of_gt]; ring!

/-- normSq z ≤ 3 * ‖z‖² (dotProduct z z ≤ n * sup_norm²). -/
private lemma normSq_le_three_mul_sq_norm (z : Fin 3 → ℝ) :
    normSq z ≤ 3 * ‖z‖ ^ 2 := by
  simp [normSq, dotProduct, Fin.sum_univ_three]
  have h : ∀ i : Fin 3, z i * z i ≤ ‖z‖ ^ 2 := fun i =>
    calc z i * z i = |z i| * |z i| := (abs_mul_abs_self (z i)).symm
    _ ≤ ‖z‖ * ‖z‖ := mul_le_mul (norm_le_pi_norm z i) (norm_le_pi_norm z i)
        (abs_nonneg _) (norm_nonneg _)
    _ = ‖z‖ ^ 2 := (sq ‖z‖).symm
  linarith [h 0, h 1, h 2]

/-- The pi norm of vGrad φ is bounded by C*(1+‖v‖)^K*φ(v) when we have a per-component bound. -/
lemma vGrad_norm_le {φ : (Fin 3 → ℝ) → ℝ} {C : ℝ} {K : ℕ}
    (hbound : ∀ v i, |fderiv ℝ φ v (Pi.single i 1)| ≤ C * (1 + ‖v‖) ^ K * φ v)
    (v : Fin 3 → ℝ) :
    ‖vGrad φ v‖ ≤ C * (1 + ‖v‖) ^ K * φ v := by
  apply (pi_norm_le_iff_of_nonneg (le_trans (abs_nonneg _) (hbound v 0))).2
  intro i; exact hbound v i

/-- Pointwise norm bound on the Landau flux integrand:
  ‖A(v-w)(φ(w)∇φ(v) - φ(v)∇φ(w))‖ ≤ 18CΨCg(1+‖v‖)^{Kg+2}φ(v)(1+‖w‖)^{Kg+2}φ(w). -/
lemma landau_flux_pointwise_bound
    {Ψ : ℝ → ℝ} {φ : (Fin 3 → ℝ) → ℝ}
    {CΨ : ℝ} (hCΨ : ∀ r, |Ψ r| ≤ CΨ) (hCΨ_nn : 0 ≤ CΨ)
    {Cg : ℝ} {Kg : ℕ}
    (hCg : ∀ v i, |fderiv ℝ φ v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * φ v)
    (hCg_nn : 0 ≤ Cg) (hφ_pos : ∀ v, 0 < φ v)
    (v w : Fin 3 → ℝ) :
    ‖landauMatrix Ψ (v - w) *ᵥ (φ w • vGrad φ v - φ v • vGrad φ w)‖ ≤
      18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v *
        ((1 + ‖w‖) ^ (Kg + 2) * φ w) := by
  have h1 := norm_mulVec_le_of_entry_bound (landauMatrix Ψ (v - w))
    (φ w • vGrad φ v - φ v • vGrad φ w)
    (mul_nonneg hCΨ_nn (normSq_nonneg _)) (landauMatrix_entry_le Ψ hCΨ (v - w))
  have h2 := normSq_le_three_mul_sq_norm (v - w)
  have h3 := norm_smul_sub_le_of_smul (vGrad φ v) (vGrad φ w) (φ w) (φ v)
  rw [abs_of_pos (hφ_pos w), abs_of_pos (hφ_pos v)] at h3
  have h4 := vGrad_norm_le hCg v
  have h5 := vGrad_norm_le hCg w
  have h6 : ‖v - w‖ ^ 2 ≤ (1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ 2 := by
    have : ‖v - w‖ ≤ (1 + ‖v‖) * (1 + ‖w‖) :=
      le_trans (norm_sub_le v w) (by nlinarith [norm_nonneg v, norm_nonneg w])
    calc ‖v - w‖ ^ 2 ≤ ((1 + ‖v‖) * (1 + ‖w‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := by ring
  have h_ns : normSq (v - w) ≤ 3 * ((1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ 2) :=
    le_trans h2 (by linarith)
  have h_u : ‖φ w • vGrad φ v - φ v • vGrad φ w‖ ≤
      Cg * φ v * φ w * ((1 + ‖v‖) ^ Kg + (1 + ‖w‖) ^ Kg) := by
    calc _ ≤ φ w * (Cg * (1 + ‖v‖) ^ Kg * φ v) +
             φ v * (Cg * (1 + ‖w‖) ^ Kg * φ w) :=
          le_trans h3 (add_le_add
            (mul_le_mul_of_nonneg_left h4 (le_of_lt (hφ_pos w)))
            (mul_le_mul_of_nonneg_left h5 (le_of_lt (hφ_pos v))))
      _ = _ := by ring
  have h7 : (1 + ‖w‖) ^ 2 ≤ (1 + ‖w‖) ^ (Kg + 2) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg w]) (by omega)
  have h8 : (1 + ‖v‖) ^ 2 ≤ (1 + ‖v‖) ^ (Kg + 2) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg v]) (by omega)
  have hpv : (1 + ‖v‖) ^ (Kg + 2) = (1 + ‖v‖) ^ 2 * (1 + ‖v‖) ^ Kg := by ring
  have hpw : (1 + ‖w‖) ^ (Kg + 2) = (1 + ‖w‖) ^ 2 * (1 + ‖w‖) ^ Kg := by ring
  have hcross1 : (1 + ‖v‖) ^ (Kg + 2) * (1 + ‖w‖) ^ 2 ≤
      (1 + ‖v‖) ^ (Kg + 2) * (1 + ‖w‖) ^ (Kg + 2) :=
    mul_le_mul_of_nonneg_left h7 (pow_nonneg (by linarith [norm_nonneg v]) _)
  have hcross2 : (1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ (Kg + 2) ≤
      (1 + ‖v‖) ^ (Kg + 2) * (1 + ‖w‖) ^ (Kg + 2) :=
    mul_le_mul_of_nonneg_right h8 (pow_nonneg (by linarith [norm_nonneg w]) _)
  calc ‖landauMatrix Ψ (v - w) *ᵥ (φ w • vGrad φ v - φ v • vGrad φ w)‖
      ≤ 3 * (CΨ * normSq (v - w)) * ‖φ w • vGrad φ v - φ v • vGrad φ w‖ := h1
    _ ≤ 3 * (CΨ * (3 * ((1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ 2))) *
          (Cg * φ v * φ w * ((1 + ‖v‖) ^ Kg + (1 + ‖w‖) ^ Kg)) := by gcongr
    _ = 9 * CΨ * Cg * φ v * φ w *
          ((1 + ‖v‖) ^ 2 * (1 + ‖v‖) ^ Kg * (1 + ‖w‖) ^ 2 +
           (1 + ‖v‖) ^ 2 * ((1 + ‖w‖) ^ 2 * (1 + ‖w‖) ^ Kg)) := by ring
    _ = 9 * CΨ * Cg * φ v * φ w *
          ((1 + ‖v‖) ^ (Kg + 2) * (1 + ‖w‖) ^ 2 +
           (1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ (Kg + 2)) := by rw [hpv, hpw]
    _ ≤ 9 * CΨ * Cg * φ v * φ w *
          ((1 + ‖v‖) ^ (Kg + 2) * (1 + ‖w‖) ^ (Kg + 2) +
           (1 + ‖v‖) ^ (Kg + 2) * (1 + ‖w‖) ^ (Kg + 2)) := by
        have : 0 ≤ 9 * CΨ * Cg * φ v * φ w := by
          apply mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hCΨ_nn) hCg_nn)
            (le_of_lt (hφ_pos v))) (le_of_lt (hφ_pos w))
        gcongr
    _ = 18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v *
          ((1 + ‖w‖) ^ (Kg + 2) * φ w) := by ring

/-- Continuity of the Landau flux integrand in w. -/
private lemma landau_flux_continuous_w
    {Ψ : ℝ → ℝ} (hΨ_cts : Continuous Ψ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ_smooth : ContDiff ℝ ⊤ φ)
    (v : Fin 3 → ℝ) :
    Continuous (fun w => landauMatrix Ψ (v - w) *ᵥ
      (φ w • vGrad φ v - φ v • vGrad φ w)) := by
  have hcsub : Continuous (fun w => v - w) := continuous_const.sub continuous_id
  apply Continuous.matrix_mulVec
  · simp only [landauMatrix]
    apply Continuous.smul
    · simp only [eucNorm]
      exact hΨ_cts.comp (Real.continuous_sqrt.comp (Continuous.dotProduct hcsub hcsub))
    · simp only [innerLandauMatrix]
      exact ((Continuous.dotProduct hcsub hcsub).smul continuous_const).sub
        (Continuous.matrix_vecMulVec hcsub hcsub)
  · apply Continuous.sub
    · exact hφ_smooth.continuous.smul continuous_const
    · exact continuous_const.smul (continuous_pi fun i =>
        (ContDiff.continuous_fderiv (hφ_smooth.of_le le_top) le_rfl).clm_apply continuous_const)

/-- Joint continuity of the Landau flux integrand in (v,w). -/
private lemma landau_flux_continuous_joint
    {Ψ : ℝ → ℝ} (hΨ_cts : Continuous Ψ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ_smooth : ContDiff ℝ ⊤ φ) :
    Continuous (fun (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) =>
      landauMatrix Ψ (p.1 - p.2) *ᵥ
        (φ p.2 • vGrad φ p.1 - φ p.1 • vGrad φ p.2)) := by
  have hcsub : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 - p.2) :=
    continuous_fst.sub continuous_snd
  apply Continuous.matrix_mulVec
  · simp only [landauMatrix]
    apply Continuous.smul
    · simp only [eucNorm]
      exact hΨ_cts.comp (Real.continuous_sqrt.comp (Continuous.dotProduct hcsub hcsub))
    · simp only [innerLandauMatrix]
      exact ((Continuous.dotProduct hcsub hcsub).smul continuous_const).sub
        (Continuous.matrix_vecMulVec hcsub hcsub)
  · apply Continuous.sub
    · exact (hφ_smooth.continuous.comp continuous_snd).smul
        (continuous_pi fun i =>
          (ContDiff.continuous_fderiv (hφ_smooth.of_le le_top) le_rfl).comp continuous_fst
            |>.clm_apply continuous_const)
    · exact (hφ_smooth.continuous.comp continuous_fst).smul
        (continuous_pi fun i =>
          (ContDiff.continuous_fderiv (hφ_smooth.of_le le_top) le_rfl).comp continuous_snd
            |>.clm_apply continuous_const)

/-- AEStronglyMeasurable for the Landau flux integral as a function of v. -/
private lemma landau_flux_integral_aestronglyMeasurable
    {Ψ : ℝ → ℝ} (hΨ_cts : Continuous Ψ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ_smooth : ContDiff ℝ ⊤ φ) :
    AEStronglyMeasurable (fun v => ∫ w, landauMatrix Ψ (v - w) *ᵥ
      (φ w • vGrad φ v - φ v • vGrad φ w)) volume :=
  (landau_flux_continuous_joint hΨ_cts hφ_smooth).aestronglyMeasurable.integral_prod_right'

/-- Spatial gradient of any spatially-constant function is 0. -/
private lemma gradX_const_fun (g : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) (x : X) :
    FlatTorus3.gradX (fun (_ : X) => g v) x = 0 :=
  FlatTorus3.hGradConst _ (fun _ _ => rfl) x

/-- Grad-log bound: ‖∇(log∘φ)(v)‖ ≤ Cg*(1+‖v‖)^Kg from grad/value bound. -/
lemma vGrad_log_norm_le {φ : (Fin 3 → ℝ) → ℝ}
    (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_pos : ∀ v, 0 < φ v)
    {Cg : ℝ} {Kg : ℕ} (hCg_nn : 0 ≤ Cg)
    (hCg : ∀ v i, |fderiv ℝ φ v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * φ v)
    (v : Fin 3 → ℝ) :
    ‖vGrad (Real.log ∘ φ) v‖ ≤ Cg * (1 + ‖v‖) ^ Kg := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hCg_nn
    (pow_nonneg (by linarith [norm_nonneg v]) _))).2
  intro i
  simp only [vGrad]
  rw [vGrad_log_eq_div (hφ_smooth.differentiable le_top) hφ_pos v i,
      Real.norm_eq_abs, abs_div, abs_of_pos (hφ_pos v)]
  exact div_le_of_le_mul₀ (le_of_lt (hφ_pos v))
    (mul_nonneg hCg_nn (pow_nonneg (by linarith [norm_nonneg v]) _)) (hCg v i)

/-- Flux integrability for Schwartz-class φ. -/
lemma schwartz_flux_integrable
    {Ψ : ℝ → ℝ} (hΨ : ∃ CΨ, ∀ r, |Ψ r| ≤ CΨ) (hΨ_cts : Continuous Ψ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ_pos : ∀ v, 0 < φ v) (hφ_smooth : ContDiff ℝ ⊤ φ)
    (hφ_decay : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    (hGradBound : ∃ C K, ∀ v i,
      |fderiv ℝ φ v (Pi.single i 1)| ≤ C * (1 + ‖v‖) ^ K * φ v)
    (v : Fin 3 → ℝ) :
    Integrable (fun w => landauMatrix Ψ (v - w) *ᵥ
      (φ w • vGrad φ v - φ v • vGrad φ w)) := by
  obtain ⟨CΨ, hCΨ⟩ := hΨ
  obtain ⟨Cg, Kg, hCg⟩ := hGradBound
  have hCΨ_nn : 0 ≤ CΨ := le_trans (abs_nonneg _) (hCΨ 0)
  have hCg_nn : 0 ≤ Cg := by
    have h := hCg 0 0; simp only [norm_zero, add_zero, one_pow] at h
    nlinarith [abs_nonneg (fderiv ℝ φ 0 (Pi.single 0 1)), hφ_pos 0]
  set C0 := 18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v
  have hdom : Integrable (fun w => C0 * ((1 + ‖w‖) ^ (Kg + 2) * |φ w|)) :=
    (integrable_one_add_norm_pow_mul hφ_decay (Kg + 2)).const_mul C0
  refine hdom.mono' (landau_flux_continuous_w hΨ_cts hφ_smooth v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [abs_of_pos (hφ_pos w)]
  exact landau_flux_pointwise_bound hCΨ hCΨ_nn hCg hCg_nn hφ_pos v w

/-- Dot product bound: |⟨c, u⟩| ≤ 3*‖c‖*‖u‖ for Fin 3 → ℝ (sup norm). -/
private lemma abs_dotProduct_le (c u : Fin 3 → ℝ) :
    |dotProduct c u| ≤ 3 * ‖c‖ * ‖u‖ := by
  simp only [dotProduct]
  rw [← Real.norm_eq_abs]
  calc ‖∑ i : Fin 3, c i * u i‖
      ≤ ∑ i : Fin 3, ‖c i * u i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖c‖ * ‖u‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_mul]; exact mul_le_mul (norm_le_pi_norm c i) (norm_le_pi_norm u i)
          (norm_nonneg _) (norm_nonneg _)
    _ = 3 * ‖c‖ * ‖u‖ := by simp [Fin.sum_univ_three]; ring

/-- Fubini integrand pointwise bound. Combines dotProduct bound + flux bound + grad-log bound. -/
lemma fubini_integrand_bound
    {Ψ : ℝ → ℝ} {φ : (Fin 3 → ℝ) → ℝ}
    (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_pos : ∀ v, 0 < φ v)
    {CΨ : ℝ} (hCΨ : ∀ r, |Ψ r| ≤ CΨ) (hCΨ_nn : 0 ≤ CΨ)
    {Cg : ℝ} {Kg : ℕ}
    (hCg : ∀ v i, |fderiv ℝ φ v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * φ v)
    (hCg_nn : 0 ≤ Cg)
    (v w : Fin 3 → ℝ) :
    |dotProduct (vGrad (Real.log ∘ φ) v)
      (landauMatrix Ψ (v - w) *ᵥ
        (φ w • vGrad φ v - φ v • vGrad φ w))| ≤
    (54 * CΨ * Cg ^ 2) * ((1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|) *
      ((1 + ‖w‖) ^ (Kg + 2) * |φ w|) := by
  calc |dotProduct (vGrad (Real.log ∘ φ) v)
        (landauMatrix Ψ (v - w) *ᵥ (φ w • vGrad φ v - φ v • vGrad φ w))|
      ≤ 3 * ‖vGrad (Real.log ∘ φ) v‖ *
        ‖landauMatrix Ψ (v - w) *ᵥ (φ w • vGrad φ v - φ v • vGrad φ w)‖ :=
      abs_dotProduct_le _ _
    _ ≤ 3 * (Cg * (1 + ‖v‖) ^ Kg) *
        (18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v *
          ((1 + ‖w‖) ^ (Kg + 2) * φ w)) := by
      gcongr
      · exact vGrad_log_norm_le hφ_smooth hφ_pos hCg_nn hCg v
      · exact landau_flux_pointwise_bound hCΨ hCΨ_nn hCg hCg_nn hφ_pos v w
    _ = (54 * CΨ * Cg ^ 2) * ((1 + ‖v‖) ^ (2 * Kg + 2) * φ v) *
        ((1 + ‖w‖) ^ (Kg + 2) * φ w) := by
      rw [show 2 * Kg + 2 = Kg + (Kg + 2) from by omega, pow_add]; ring
    _ ≤ (54 * CΨ * Cg ^ 2) * ((1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|) *
        ((1 + ‖w‖) ^ (Kg + 2) * |φ w|) := by
      rw [abs_of_pos (hφ_pos v), abs_of_pos (hφ_pos w)]

/-- Continuity of vGrad in the v argument. -/
private lemma continuous_vGrad {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ ⊤ f) (i : Fin 3) :
    Continuous (fun v => vGrad f v i) := by
  simp only [vGrad]
  exact (ContDiff.continuous_fderiv (hf.of_le le_top) le_rfl).clm_apply continuous_const

/-- Joint continuity of the Fubini integrand ⟨∇logφ(v), flux(v,w)⟩. -/
private lemma fubini_integrand_continuous
    {Ψ : ℝ → ℝ} (hΨ_cts : Continuous Ψ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_pos : ∀ v, 0 < φ v) :
    Continuous (fun (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) =>
      dotProduct (vGrad (Real.log ∘ φ) p.1)
        (landauMatrix Ψ (p.1 - p.2) *ᵥ
          (φ p.2 • vGrad φ p.1 - φ p.1 • vGrad φ p.2))) := by
  simp only [dotProduct, Fin.sum_univ_three]
  refine Continuous.add (Continuous.add ?_ ?_) ?_ <;>
    exact ((continuous_vGrad (hφ_smooth.log (fun v => ne_of_gt (hφ_pos v))) _).comp
      continuous_fst).mul
      ((continuous_apply _).comp (landau_flux_continuous_joint hΨ_cts hφ_smooth))

/-- Joint continuity of the PSD integrand in (v, w). -/
private lemma psd_integrand_continuous_joint
    {Ψ : ℝ → ℝ} (hΨ_cts : Continuous Ψ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_pos : ∀ v, 0 < φ v) :
    Continuous (fun (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) => PSDIntegrand Ψ φ p.1 p.2) := by
  unfold PSDIntegrand
  have h_log_smooth := hφ_smooth.log (fun v => ne_of_gt (hφ_pos v))
  have hΔ : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      vGrad (Real.log ∘ φ) p.1 - vGrad (Real.log ∘ φ) p.2) :=
    (continuous_pi fun i => (continuous_vGrad h_log_smooth i).comp continuous_fst).sub
      (continuous_pi fun i => (continuous_vGrad h_log_smooth i).comp continuous_snd)
  have hcsub : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 - p.2) :=
    continuous_fst.sub continuous_snd
  have hA : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => landauMatrix Ψ (p.1 - p.2)) := by
    simp only [landauMatrix]; apply Continuous.smul
    · simp only [eucNorm]
      exact hΨ_cts.comp (Real.continuous_sqrt.comp (Continuous.dotProduct hcsub hcsub))
    · simp only [innerLandauMatrix]
      exact ((Continuous.dotProduct hcsub hcsub).smul continuous_const).sub
        (Continuous.matrix_vecMulVec hcsub hcsub)
  exact ((hφ_smooth.continuous.comp continuous_fst).mul (hφ_smooth.continuous.comp continuous_snd)).mul
    (Continuous.dotProduct hΔ (hA.matrix_mulVec hΔ))

/-- PSD integrand pointwise bound. -/
lemma psd_integrand_bound
    {Ψ : ℝ → ℝ} {φ : (Fin 3 → ℝ) → ℝ}
    (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_pos : ∀ v, 0 < φ v)
    {CΨ : ℝ} (hCΨ : ∀ r, |Ψ r| ≤ CΨ) (hCΨ_nn : 0 ≤ CΨ)
    {Cg : ℝ} {Kg : ℕ}
    (hCg : ∀ v i, |fderiv ℝ φ v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * φ v)
    (hCg_nn : 0 ≤ Cg)
    (v w : Fin 3 → ℝ) :
    |PSDIntegrand Ψ φ v w| ≤
    (108 * CΨ * Cg ^ 2) * ((1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|) *
      ((1 + ‖w‖) ^ (2 * Kg + 2) * |φ w|) := by
  unfold PSDIntegrand
  set Δ := vGrad (Real.log ∘ φ) v - vGrad (Real.log ∘ φ) w
  rw [abs_mul, abs_mul, abs_of_pos (hφ_pos v), abs_of_pos (hφ_pos w)]
  -- Step 1: |⟨Δ, AΔ⟩| ≤ 9*CΨ*normSq(v-w)*‖Δ‖²
  have h_dot : |dotProduct Δ (landauMatrix Ψ (v - w) *ᵥ Δ)| ≤
      9 * CΨ * normSq (v - w) * ‖Δ‖ ^ 2 := by
    calc _ ≤ 3 * ‖Δ‖ * ‖landauMatrix Ψ (v - w) *ᵥ Δ‖ := abs_dotProduct_le _ _
      _ ≤ 3 * ‖Δ‖ * (3 * (CΨ * normSq (v - w)) * ‖Δ‖) := by
        gcongr; exact norm_mulVec_le_of_entry_bound _ _
          (mul_nonneg hCΨ_nn (normSq_nonneg _)) (landauMatrix_entry_le _ hCΨ _)
      _ = _ := by ring
  -- Step 2: normSq(v-w) ≤ 3*(1+‖v‖)²*(1+‖w‖)²
  have h_nsq : normSq (v - w) ≤ 3 * (1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ 2 := by
    calc normSq (v - w) ≤ 3 * ‖v - w‖ ^ 2 := normSq_le_three_mul_sq_norm _
      _ ≤ 3 * ((1 + ‖v‖) * (1 + ‖w‖)) ^ 2 := by
        gcongr; exact le_trans (norm_sub_le v w)
          (by nlinarith [norm_nonneg v, norm_nonneg w])
      _ = _ := by ring
  -- Step 3: ‖Δ‖ ≤ 2*Cg*(1+‖v‖)^Kg*(1+‖w‖)^Kg
  have h_delta : ‖Δ‖ ≤ 2 * Cg * (1 + ‖v‖) ^ Kg * (1 + ‖w‖) ^ Kg := by
    have hv := vGrad_log_norm_le hφ_smooth hφ_pos hCg_nn hCg v
    have hw := vGrad_log_norm_le hφ_smooth hφ_pos hCg_nn hCg w
    have hv1 : 1 ≤ (1 + ‖v‖) ^ Kg :=
      one_le_pow₀ (by linarith [norm_nonneg v])
    have hw1 : 1 ≤ (1 + ‖w‖) ^ Kg :=
      one_le_pow₀ (by linarith [norm_nonneg w])
    calc ‖Δ‖ ≤ ‖vGrad (Real.log ∘ φ) v‖ + ‖vGrad (Real.log ∘ φ) w‖ := norm_sub_le _ _
      _ ≤ Cg * (1 + ‖v‖) ^ Kg + Cg * (1 + ‖w‖) ^ Kg := add_le_add hv hw
      _ ≤ Cg * (1 + ‖v‖) ^ Kg * (1 + ‖w‖) ^ Kg +
          Cg * (1 + ‖v‖) ^ Kg * (1 + ‖w‖) ^ Kg := by
        apply add_le_add
        · exact le_mul_of_one_le_right (mul_nonneg hCg_nn (pow_nonneg (by linarith [norm_nonneg v]) _)) hw1
        · calc Cg * (1 + ‖w‖) ^ Kg = Cg * 1 * (1 + ‖w‖) ^ Kg := by ring
            _ ≤ Cg * (1 + ‖v‖) ^ Kg * (1 + ‖w‖) ^ Kg := by
              gcongr
      _ = _ := by ring
  -- Combine: |PSD| ≤ φv * φw * 9*CΨ * 3*(1+‖v‖)²*(1+‖w‖)² * (2*Cg*(1+‖v‖)^Kg*(1+‖w‖)^Kg)²
  --               = 108*CΨ*Cg² * (1+‖v‖)^(2Kg+2)*φv * (1+‖w‖)^(2Kg+2)*φw
  have h_Δ_sq : ‖Δ‖ ^ 2 ≤ 4 * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg) * (1 + ‖w‖) ^ (2 * Kg) := by
    calc ‖Δ‖ ^ 2 ≤ (2 * Cg * (1 + ‖v‖) ^ Kg * (1 + ‖w‖) ^ Kg) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h_delta 2
      _ = 4 * Cg ^ 2 * ((1 + ‖v‖) ^ Kg) ^ 2 * ((1 + ‖w‖) ^ Kg) ^ 2 := by ring
      _ = 4 * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg) * (1 + ‖w‖) ^ (2 * Kg) := by
        simp only [← pow_mul]; ring
  -- Bound |⟨Δ,AΔ⟩| independently
  have h_mid : |dotProduct Δ (landauMatrix Ψ (v - w) *ᵥ Δ)| ≤
      108 * CΨ * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg + 2) * (1 + ‖w‖) ^ (2 * Kg + 2) := by
    calc _ ≤ 9 * CΨ * normSq (v - w) * ‖Δ‖ ^ 2 := h_dot
      _ ≤ 9 * CΨ * (3 * (1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ 2) *
          (4 * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg) * (1 + ‖w‖) ^ (2 * Kg)) := by
        gcongr
      _ = _ := by
        rw [show 2 * Kg + 2 = 2 + 2 * Kg from by omega]; simp only [pow_add]; ring
  -- Multiply by φ v * φ w (left-associated from abs_mul)
  calc φ v * φ w * |dotProduct Δ (landauMatrix Ψ (v - w) *ᵥ Δ)|
      ≤ φ v * φ w * (108 * CΨ * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg + 2) *
          (1 + ‖w‖) ^ (2 * Kg + 2)) :=
        mul_le_mul_of_nonneg_left h_mid
          (mul_nonneg (le_of_lt (hφ_pos v)) (le_of_lt (hφ_pos w)))
    _ = (108 * CΨ * Cg ^ 2) * ((1 + ‖v‖) ^ (2 * Kg + 2) * φ v) *
        ((1 + ‖w‖) ^ (2 * Kg + 2) * φ w) := by ring


-- ===== Building blocks for flux derivative bound =====

/-- Product rule norm bound (proved by Aristotle, job 85fc02e5). -/
private lemma fderiv_mul_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (x : E) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y => f y * g y) x‖ ≤
      ‖fderiv ℝ f x‖ * |g x| + |f x| * ‖fderiv ℝ g x‖ := by
  have hfg := hf.hasFDerivAt.mul hg.hasFDerivAt
  show ‖fderiv ℝ (f * g) x‖ ≤ _
  rw [hfg.fderiv]
  calc ‖f x • fderiv ℝ g x + g x • fderiv ℝ f x‖
      ≤ ‖f x • fderiv ℝ g x‖ + ‖g x • fderiv ℝ f x‖ := norm_add_le _ _
    _ = |f x| * ‖fderiv ℝ g x‖ + |g x| * ‖fderiv ℝ f x‖ := by
        simp [norm_smul, Real.norm_eq_abs]
    _ = ‖fderiv ℝ f x‖ * |g x| + |f x| * ‖fderiv ℝ g x‖ := by ring

set_option maxHeartbeats 800000 in
/-- Each entry of the Landau matrix A_{ij}(v-w) is differentiable in v.
    At z ≠ 0: composition of C¹ functions (Ψ ∘ ‖·‖ smooth, polynomial smooth).
    At z = 0: A_{ij}(0) = 0 and |A_{ij}(z)| ≤ CΨ·2‖z‖², giving hasFDerivAt 0.
    Proved by Aristotle. -/
private lemma landauMatrix_entry_differentiable
    {Ψ : ℝ → ℝ} (hΨ_diff : ContDiff ℝ 1 Ψ) (hΨ_bound : ∃ CΨ, ∀ r, |Ψ r| ≤ CΨ)
    (w : Fin 3 → ℝ) (i j : Fin 3) :
    Differentiable ℝ (fun v => landauMatrix Ψ (v - w) i j) := by
  -- Proved by Aristotle (job 648b5b5b).
  unfold landauMatrix eucNorm normSq
  have h_combined : Differentiable ℝ (fun v : (Fin 3) → ℝ => Ψ (Real.sqrt ((v - w) ⬝ᵥ (v - w))) * (Real.sqrt ((v - w) ⬝ᵥ (v - w))^2 * (if i = j then 1 else 0) - (v - w) i * (v - w) j)) := by
    intro v
    by_cases hv : v = w
    · refine' ⟨ _, hasFDerivAt_iff_isLittleO_nhds_zero.mpr _ ⟩
      exact 0
      have h_bound : ∀ h : Fin 3 → ℝ, abs (Ψ (Real.sqrt ((h ⬝ᵥ h))) * ((Real.sqrt ((h ⬝ᵥ h)) ^ 2 * (if i = j then 1 else 0) - h i * h j))) ≤ hΨ_bound.choose * 2 * (‖h‖ ^ 2) := by
        intro h
        have h_bound : abs ((Real.sqrt ((h ⬝ᵥ h)) ^ 2 * (if i = j then 1 else 0) - h i * h j)) ≤ 2 * (‖h‖ ^ 2) := by
          split_ifs <;> norm_num [ Real.sq_sqrt ( show 0 ≤ h ⬝ᵥ h by exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _ ) ]
          · simp_all +decide [ dotProduct, Fin.sum_univ_three ]
            fin_cases j <;> norm_num [ Norm.norm ] <;> ring_nf <;> norm_num [ abs_le ]
            · norm_num [ Fin.univ_succ ]
              constructor <;> nlinarith only [ abs_le.mp ( show |h 0| ≤ Max.max |h 0| ( Max.max |h 1| |h 2| ) by exact le_max_left _ _ ), abs_le.mp ( show |h 1| ≤ Max.max |h 0| ( Max.max |h 1| |h 2| ) by exact le_max_of_le_right ( le_max_left _ _ ) ), abs_le.mp ( show |h 2| ≤ Max.max |h 0| ( Max.max |h 1| |h 2| ) by exact le_max_of_le_right ( le_max_right _ _ ) ) ]
            · norm_num [ Fin.univ_succ ]
              constructor <;> nlinarith only [ abs_le.mp ( show |h 0| ≤ Max.max |h 0| ( Max.max |h 1| |h 2| ) by exact le_max_left _ _ ), abs_le.mp ( show |h 1| ≤ Max.max |h 0| ( Max.max |h 1| |h 2| ) by exact le_max_of_le_right ( le_max_left _ _ ) ), abs_le.mp ( show |h 2| ≤ Max.max |h 0| ( Max.max |h 1| |h 2| ) by exact le_max_of_le_right ( le_max_right _ _ ) ) ]
            · norm_num [ Fin.univ_succ ]
              constructor <;> nlinarith! [ abs_le.mp ( le_max_left |h 0| ( Max.max |h 1| |h 2| ) ), abs_le.mp ( le_max_right |h 0| ( Max.max |h 1| |h 2| ) |> le_trans ( le_max_left |h 1| |h 2| ) ), abs_le.mp ( le_max_right |h 0| ( Max.max |h 1| |h 2| ) |> le_trans ( le_max_right |h 1| |h 2| ) ) ]
          · nlinarith only [ abs_nonneg ( h i ), abs_nonneg ( h j ), show |h i| ≤ ‖h‖ from by simpa using norm_le_pi_norm h i, show |h j| ≤ ‖h‖ from by simpa using norm_le_pi_norm h j ]
        simpa only [ mul_assoc, abs_mul ] using mul_le_mul ( hΨ_bound.choose_spec _ ) h_bound ( by positivity ) ( by linarith [ abs_le.mp ( hΨ_bound.choose_spec ( Real.sqrt ( h ⬝ᵥ h ) ) ) ] )
      rw [ Asymptotics.isLittleO_iff ]
      intro ε ε_pos; filter_upwards [ Metric.ball_mem_nhds _ ( show 0 < ε / ( hΨ_bound.choose * 2 + 1 ) by exact div_pos ε_pos ( by linarith [ show 0 ≤ hΨ_bound.choose by exact le_trans ( abs_nonneg _ ) ( hΨ_bound.choose_spec 0 ) ] ) ) ] with x hx; simp_all +decide [ abs_mul, abs_of_nonneg, add_nonneg ]
      rw [ lt_div_iff₀ ] at hx <;> nlinarith [ h_bound x, show 0 ≤ hΨ_bound.choose by exact le_trans ( abs_nonneg _ ) ( hΨ_bound.choose_spec 0 ), norm_nonneg x ]
    · refine' DifferentiableAt.mul _ _
      · refine' DifferentiableAt.comp v ( hΨ_diff.contDiffAt.differentiableAt ( by norm_num ) ) _
        refine' DifferentiableAt.sqrt _ _ <;> norm_num [ hv, dotProduct ]
        · fun_prop (disch := norm_num)
        · exact fun h => hv <| by ext x; fin_cases x <;> norm_num [ Fin.sum_univ_three ] at * <;> nlinarith!
      · refine' DifferentiableAt.sub _ _
        · refine' DifferentiableAt.mul _ _
          · refine' DifferentiableAt.pow _ _
            refine' DifferentiableAt.sqrt _ _ <;> norm_num [ dotProduct ]
            · fun_prop (disch := norm_num)
            · exact fun h => hv <| by ext x; fin_cases x <;> norm_num [ Fin.sum_univ_three ] at * <;> nlinarith!
          · norm_num
        · fun_prop
  convert h_combined using 1 ; norm_num [ innerLandauMatrix, Matrix.mulVec, dotProduct ] ; ring!
  ext; norm_num [ Matrix.vecMulVec, normSq ] ; ring
  rw [ Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => by nlinarith only [ sq_nonneg ( ( ‹Fin 3 → ℝ› ) ‹_› - w ‹_› ) ] ) ] ; simp +decide [ Fin.sum_univ_three, dotProduct ] ; ring
  fin_cases i <;> fin_cases j <;> simp +decide [ Matrix.one_apply ] <;> ring!

/-- Chain rule for translation: fderiv(f(·-w))(v) = fderiv(f)(v-w). -/
private lemma fderiv_translate' (f : (Fin 3 → ℝ) → ℝ) (w : Fin 3 → ℝ)
    (hf : Differentiable ℝ f) :
    ∀ v, fderiv ℝ (fun v' => f (v' - w)) v = fderiv ℝ f (v - w) := by
  intro v
  have h1 : (fun v' => f (v' - w)) = (fun v' => f (v' + (-w))) :=
    funext fun v' => by simp [sub_eq_add_neg]
  rw [h1, fderiv_comp_add_right]; simp [sub_eq_add_neg]

/-- Per-summand derivative bound for the Landau flux integrand.
    Proved by Aristotle (job a743f055). -/
private lemma single_summand_deriv_bound
    (A : (Fin 3 → ℝ) → ℝ)
    (φ dφ : (Fin 3 → ℝ) → ℝ)
    (hA_diff : Differentiable ℝ A)
    (hφ_diff : Differentiable ℝ φ) (hdφ_diff : Differentiable ℝ dφ)
    (hφ_pos : ∀ v, 0 < φ v)
    (CA CD Cg C₂ Cop : ℝ) (Kg K₂ : ℕ)
    (hCA_nn : 0 ≤ CA) (hCD_nn : 0 ≤ CD) (hCg_nn : 0 ≤ Cg)
    (hC₂_nn : 0 ≤ C₂) (hCop_nn : 0 ≤ Cop)
    (hCA : ∀ z, |A z| ≤ CA * ‖z‖ ^ 2)
    (hCD : ∀ z, ‖fderiv ℝ A z‖ ≤ CD * (1 + ‖z‖) ^ 2)
    (hCg : ∀ v, |dφ v| ≤ Cg * (1 + ‖v‖) ^ Kg * φ v)
    (hC₂ : ∀ v, ‖fderiv ℝ dφ v‖ ≤ C₂ * (1 + ‖v‖) ^ K₂ * φ v)
    (hCop : ∀ v, ‖fderiv ℝ φ v‖ ≤ Cop * (1 + ‖v‖) ^ Kg * φ v) :
    ∀ v w : Fin 3 → ℝ,
      ‖fderiv ℝ (fun v' => A (v' - w) * (φ w * dφ v' - φ v' * dφ w)) v‖ ≤
      (2 * CD * Cg + CA * (C₂ + Cop * Cg)) *
        ((1 + ‖v‖) ^ (2 + Kg + K₂) * φ v) *
        ((1 + ‖w‖) ^ (2 + Kg + K₂) * |φ w|) := by
  intro v w
  have h_prod_rule : ‖fderiv ℝ (fun v' => A (v' - w) * (φ w * dφ v' - φ v' * dφ w)) v‖ ≤ ‖fderiv ℝ (fun v' => A (v' - w)) v‖ * |φ w * dφ v - φ v * dφ w| + |A (v - w)| * ‖fderiv ℝ (fun v' => φ w * dφ v' - φ v' * dφ w) v‖ := by
    convert fderiv_mul_norm_le ( fun v' => A ( v' - w ) ) ( fun v' => φ w * dφ v' - φ v' * dφ w ) v _ _ using 1 <;> norm_num [ hA_diff.differentiableAt, hφ_diff.differentiableAt, hdφ_diff.differentiableAt ];
    exact hA_diff.differentiableAt.comp _ ( differentiableAt_id.sub_const _ );
  have h_deriv_bounds : ‖fderiv ℝ (fun v' => A (v' - w)) v‖ ≤ CD * (1 + ‖v - w‖) ^ 2 ∧ |A (v - w)| ≤ CA * ‖v - w‖ ^ 2 ∧ |φ w * dφ v - φ v * dφ w| ≤ φ w * Cg * (1 + ‖v‖) ^ Kg * φ v + φ v * Cg * (1 + ‖w‖) ^ Kg * φ w ∧ ‖fderiv ℝ (fun v' => φ w * dφ v' - φ v' * dφ w) v‖ ≤ φ w * C₂ * (1 + ‖v‖) ^ K₂ * φ v + Cop * (1 + ‖v‖) ^ Kg * φ v * Cg * (1 + ‖w‖) ^ Kg * φ w := by
    refine' ⟨ _, _, _, _ ⟩ <;> try exact hCA _;
    · convert fderiv_translate' A w hA_diff v ▸ hCD ( v - w ) using 1;
    · refine' le_trans ( abs_sub _ _ ) _;
      rw [ abs_mul, abs_mul, abs_of_pos ( hφ_pos _ ), abs_of_pos ( hφ_pos _ ) ] ; nlinarith [ hCg v, hCg w, hφ_pos v, hφ_pos w ] ;
    · have h_prod_rule : fderiv ℝ (fun v' => φ w * dφ v' - φ v' * dφ w) v = (φ w) • fderiv ℝ dφ v - (dφ w) • fderiv ℝ φ v := by
        convert HasFDerivAt.fderiv ( HasFDerivAt.sub ( HasFDerivAt.const_mul ( hdφ_diff.differentiableAt.hasFDerivAt ) _ ) ( HasFDerivAt.mul ( hφ_diff.differentiableAt.hasFDerivAt ) ( hasFDerivAt_const _ _ ) ) ) using 1 ; norm_num;
      rw [ h_prod_rule ];
      refine' le_trans ( norm_sub_le _ _ ) _;
      norm_num [ norm_smul, abs_of_pos ( hφ_pos _ ) ];
      refine' add_le_add _ _;
      · simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_left ( hC₂ v ) ( le_of_lt ( hφ_pos w ) );
      · convert mul_le_mul ( hCg w ) ( hCop v ) ( by positivity ) ( by exact mul_nonneg ( mul_nonneg hCg_nn ( pow_nonneg ( by positivity ) _ ) ) ( le_of_lt ( hφ_pos _ ) ) ) using 1 ; ring;
  have h_norm_diff_bounds : (1 + ‖v - w‖) ^ 2 ≤ (1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ 2 ∧ ‖v - w‖ ^ 2 ≤ (1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ 2 := by
    constructor <;> nlinarith only [ norm_nonneg ( v - w ), norm_nonneg v, norm_nonneg w, norm_sub_le v w, mul_nonneg ( norm_nonneg v ) ( norm_nonneg w ) ] ;
  have h_prod_norm_bounds : φ w * Cg * (1 + ‖v‖) ^ Kg * φ v + φ v * Cg * (1 + ‖w‖) ^ Kg * φ w ≤ 2 * Cg * (1 + ‖v‖) ^ (Kg + K₂) * (1 + ‖w‖) ^ (Kg + K₂) * φ v * φ w ∧ φ w * C₂ * (1 + ‖v‖) ^ K₂ * φ v + Cop * (1 + ‖v‖) ^ Kg * φ v * Cg * (1 + ‖w‖) ^ Kg * φ w ≤ (C₂ + Cop * Cg) * (1 + ‖v‖) ^ (Kg + K₂) * (1 + ‖w‖) ^ (Kg + K₂) * φ v * φ w := by
    constructor <;> ring_nf;
    · suffices h_simp : (1 + ‖v‖) ^ Kg + (1 + ‖w‖) ^ Kg ≤ 2 * (1 + ‖v‖) ^ Kg * (1 + ‖w‖) ^ Kg * (1 + ‖v‖) ^ K₂ * (1 + ‖w‖) ^ K₂ by
        nlinarith only [ show 0 ≤ φ w * Cg * φ v by exact mul_nonneg ( mul_nonneg ( le_of_lt ( hφ_pos _ ) ) hCg_nn ) ( le_of_lt ( hφ_pos _ ) ), h_simp ];
      have h_sum_le : (1 + ‖v‖)^Kg + (1 + ‖w‖)^Kg ≤ 2 * (1 + ‖v‖)^Kg * (1 + ‖w‖)^Kg := by
        nlinarith only [ show 1 ≤ ( 1 + ‖v‖ ) ^ Kg by exact one_le_pow₀ ( by linarith [ norm_nonneg v ] ), show 1 ≤ ( 1 + ‖w‖ ) ^ Kg by exact one_le_pow₀ ( by linarith [ norm_nonneg w ] ) ];
      exact le_trans h_sum_le ( le_trans ( le_mul_of_one_le_right ( by positivity ) ( one_le_pow₀ ( by linarith [ norm_nonneg v, norm_nonneg w ] ) ) ) ( le_mul_of_one_le_right ( by positivity ) ( one_le_pow₀ ( by linarith [ norm_nonneg v, norm_nonneg w ] ) ) ) );
    · refine' add_le_add _ _;
      · norm_num [ mul_assoc ];
        gcongr;
        · exact le_of_lt ( hφ_pos _ );
        · exact le_of_lt ( hφ_pos v );
        · exact le_mul_of_one_le_right ( by positivity ) ( one_le_mul_of_one_le_of_one_le ( one_le_pow₀ ( by linarith [ norm_nonneg v ] ) ) ( one_le_mul_of_one_le_of_one_le ( one_le_pow₀ ( by linarith [ norm_nonneg w ] ) ) ( one_le_pow₀ ( by linarith [ norm_nonneg w ] ) ) ) );
      · norm_num [ mul_assoc, mul_comm, mul_left_comm ];
        gcongr;
        · exact le_of_lt ( hφ_pos v );
        · exact le_of_lt ( hφ_pos _ );
        · rw [ mul_left_comm ];
          exact le_mul_of_one_le_right ( by positivity ) ( one_le_mul_of_one_le_of_one_le ( one_le_pow₀ ( by linarith [ norm_nonneg v ] ) ) ( one_le_pow₀ ( by linarith [ norm_nonneg w ] ) ) );
  have h_final_bound : ‖fderiv ℝ (fun v' => A (v' - w) * (φ w * dφ v' - φ v' * dφ w)) v‖ ≤ CD * (1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ 2 * 2 * Cg * (1 + ‖v‖) ^ (Kg + K₂) * (1 + ‖w‖) ^ (Kg + K₂) * φ v * φ w + CA * (1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ 2 * (C₂ + Cop * Cg) * (1 + ‖v‖) ^ (Kg + K₂) * (1 + ‖w‖) ^ (Kg + K₂) * φ v * φ w := by
    refine le_trans h_prod_rule ?_;
    refine le_trans ( add_le_add ( mul_le_mul h_deriv_bounds.1 h_deriv_bounds.2.2.1 ( by positivity ) ( by positivity ) ) ( mul_le_mul h_deriv_bounds.2.1 h_deriv_bounds.2.2.2 ( by positivity ) ( by positivity ) ) ) ?_;
    refine le_trans ( add_le_add ( mul_le_mul_of_nonneg_left h_prod_norm_bounds.1 <| by positivity ) ( mul_le_mul_of_nonneg_left h_prod_norm_bounds.2 <| by positivity ) ) ?_;
    refine' add_le_add _ _;
    · convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left h_norm_diff_bounds.1 hCD_nn ) ( show 0 ≤ 2 * Cg * ( 1 + ‖v‖ ) ^ ( Kg + K₂ ) * ( 1 + ‖w‖ ) ^ ( Kg + K₂ ) * φ v * φ w by exact mul_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg zero_le_two hCg_nn ) ( pow_nonneg ( by positivity ) _ ) ) ( pow_nonneg ( by positivity ) _ ) ) ( le_of_lt ( hφ_pos _ ) ) ) ( le_of_lt ( hφ_pos _ ) ) ) using 1 ; ring;
    · convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left h_norm_diff_bounds.2 hCA_nn ) ( show 0 ≤ ( C₂ + Cop * Cg ) * ( 1 + ‖v‖ ) ^ ( Kg + K₂ ) * ( 1 + ‖w‖ ) ^ ( Kg + K₂ ) * φ v * φ w by exact mul_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) ( by positivity ) ) ( by positivity ) ) ( by exact le_of_lt ( hφ_pos _ ) ) ) ( by exact le_of_lt ( hφ_pos _ ) ) ) using 1 ; ring;
  convert h_final_bound using 1 ; rw [ abs_of_pos ( hφ_pos w ) ] ; ring

/-- The Landau matrix as a matrix-valued function is continuous. -/
private lemma landauMatrix_continuous
    {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ) :
    Continuous (fun z : Fin 3 → ℝ => landauMatrix Ψ z) := by
  unfold landauMatrix
  apply Continuous.smul
  · -- Continuous (fun z => Ψ(eucNorm z))
    unfold eucNorm normSq
    exact hΨ.comp (continuous_sqrt.comp
      (continuous_finset_sum _ (fun k _ => (continuous_apply k).mul (continuous_apply k))))
  · -- Continuous (fun z => innerLandauMatrix z)
    unfold innerLandauMatrix normSq
    apply Continuous.sub
    · exact (continuous_finset_sum _ (fun k _ =>
        (continuous_apply k).mul (continuous_apply k))).smul continuous_const
    · exact continuous_pi (fun r => continuous_pi (fun c =>
        (continuous_apply r).mul (continuous_apply c)))


end VML
