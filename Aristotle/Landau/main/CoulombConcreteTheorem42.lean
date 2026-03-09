/-
  Concrete Theorem 42 for Coulomb collisions on T³ = (ℝ/ℤ)³.

  This specializes ConcreteTheorem42 to the physical Coulomb collision kernel
  Ψ(r) = r⁻³, the most important case in plasma physics. The Coulomb kernel
  is singular at r = 0 (NOT continuous), so it cannot satisfy `Continuous Ψ`.

  Key mathematical fact: even though the Landau matrix A(z) = Ψ(|z|)(|z|²I - zz^T)
  diverges as z → 0 for Coulomb, the PSD integrand is continuous because the score
  difference Δ = ∇log f(v) - ∇log f(w) = O(|v-w|) cancels the singularity:
    |PSDIntegrand(v,w)| ≤ C|v-w|^{γ+4} = C|v-w| → 0  (γ = -3).

  We define coulombKernel with value 1 at r ≤ 0 (instead of 0 or ∞) so that
  ∀ r, 0 < coulombKernel r. The value at 0 is irrelevant since
  landauMatrix Ψ 0 = 0 always (the projection |z|²I - zz^T vanishes at z = 0).

  Hypotheses (12 total, down from 15 in ConcreteTheorem42):
  - 2 physical parameters (ν > 0, ρ_ion > 0)
  - 1 strict positivity (f > 0)
  - 3 smoothness (f smooth in v and x, B smooth)
  - 2 decay (Schwartz in v, stretched-exponential lower bound)
  - 4 equations (Vlasov, Ampère, Gauss, div B = 0)
-/
import Aristotle.Landau.main.ConcreteTheorem42

set_option linter.all false
open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

/-- The Coulomb collision kernel: Ψ(r) = r⁻³ for r > 0, extended to 1 for r ≤ 0.
    The value at r ≤ 0 is irrelevant since landauMatrix Ψ 0 = 0 always
    (the projection |z|²I - zz^T vanishes at z = 0). Setting it to 1 ensures
    ∀ r, 0 < Ψ r, which the abstract theorem requires. -/
def coulombKernel (r : ℝ) : ℝ :=
  if r ≤ 0 then 1 else r ^ (-3 : ℝ)

lemma coulombKernel_pos : ∀ r, 0 < coulombKernel r := by
  intro r
  simp only [coulombKernel]
  split
  · exact one_pos
  · exact rpow_pos_of_pos (by linarith) _

-- ============================================================================
-- Helper lemmas for deriving VelocityDecayConditions from Schwartz + ExpDecay
-- ============================================================================

/-- Log bound from Schwartz upper bound + stretched-exponential lower bound.
    From Schwartz N=0, k=0: |f x v| ≤ C_upper (uniform in x, v).
    From ExpDecay: f x v ≥ exp(-C_exp * (1+‖v‖)^K_exp).
    Together: |log(f x v)| ≤ max(|log C_upper|, C_exp * (1+‖v‖)^K_exp). -/
lemma schwartz_log_bound
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hf_pos : ∀ x v, 0 < f x v)
    (hSchwartz : UniformSchwartzDecay f)
    (hExpDecay : ∃ (C : ℝ) (K : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      Real.exp (-C * (1 + ‖v‖) ^ K) ≤ f x v) :
    ∃ (C_log : ℝ) (K_log : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log := by
  -- Upper bound on f from Schwartz (N=0, k=0)
  obtain ⟨C_up, hC_up_pos, hbound_up⟩ := hSchwartz.hDecay 0 0
  -- Lower bound from stretched-exponential decay
  obtain ⟨C_exp, K_exp, hbound_low⟩ := hExpDecay
  -- From Schwartz: ‖iteratedFDeriv ℝ 0 (f x) v‖ * 1 ≤ C_up → |f x v| ≤ C_up
  have hf_le : ∀ x v, f x v ≤ C_up := by
    intro x v
    have h := hbound_up x v; simp at h
    exact le_trans (le_abs_self _) h
  -- log(f x v) ≤ log(C_up)
  have hlog_upper : ∀ x v, Real.log (f x v) ≤ Real.log C_up := by
    intro x v; exact Real.log_le_log (hf_pos x v) (hf_le x v)
  -- log(f x v) ≥ -C_exp * (1 + ‖v‖)^K_exp from exp lower bound
  have hlog_lower : ∀ x v, -C_exp * (1 + ‖v‖) ^ K_exp ≤ Real.log (f x v) := by
    intro x v
    rw [← Real.log_exp (-C_exp * (1 + ‖v‖) ^ K_exp)]
    exact Real.log_le_log (Real.exp_pos _) (hbound_low x v)
  -- |log(f x v)| ≤ (|log C_up| + |C_exp|) * (1 + ‖v‖)^K_exp
  refine ⟨|Real.log C_up| + |C_exp| + 1, K_exp, fun x v => ?_⟩
  rw [abs_le]
  have h1v_ge : (1 : ℝ) ≤ (1 + ‖v‖) ^ K_exp :=
    one_le_pow₀ (by linarith [norm_nonneg v])
  have h1v_nn : (0 : ℝ) ≤ (1 + ‖v‖) ^ K_exp := le_trans zero_le_one h1v_ge
  constructor
  · -- -((|log C_up| + |C_exp| + 1) * (1+‖v‖)^K_exp) ≤ log(f x v)
    calc -(( |Real.log C_up| + |C_exp| + 1) * (1 + ‖v‖) ^ K_exp)
        ≤ -(C_exp * (1 + ‖v‖) ^ K_exp) := by
          apply neg_le_neg
          exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self C_exp, abs_nonneg (Real.log C_up)]) h1v_nn
      _ = -C_exp * (1 + ‖v‖) ^ K_exp := by ring
      _ ≤ Real.log (f x v) := hlog_lower x v
  · -- log(f x v) ≤ (|log C_up| + |C_exp| + 1) * (1+‖v‖)^K_exp
    have hC_nn : (0 : ℝ) ≤ |Real.log C_up| + |C_exp| + 1 := by positivity
    calc Real.log (f x v) ≤ Real.log C_up := hlog_upper x v
      _ ≤ |Real.log C_up| := le_abs_self _
      _ ≤ |Real.log C_up| + |C_exp| + 1 := by linarith [abs_nonneg C_exp]
      _ = (|Real.log C_up| + |C_exp| + 1) * 1 := by ring
      _ ≤ (|Real.log C_up| + |C_exp| + 1) * (1 + ‖v‖) ^ K_exp :=
          mul_le_mul_of_nonneg_left h1v_ge hC_nn

/-- Schwartz decay implies moment integrability with norm powers. -/
lemma schwartz_norm_pow_integrable
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x))
    (hSchwartz : UniformSchwartzDecay f)
    (x : Torus3) (k : ℕ) :
    Integrable (fun v => ‖v‖ ^ k * |f x v|) := by
  -- Since f > 0, |f| = f
  have habs : (fun v => ‖v‖ ^ k * |f x v|) = (fun v => ‖v‖ ^ k * f x v) :=
    funext fun v => by rw [abs_of_pos (hf_pos x v)]
  rw [habs]
  -- From Schwartz: |f x v| * (1+‖v‖)^(k+4) ≤ C, so f x v ≤ C/(1+‖v‖)^(k+4)
  -- Then ‖v‖^k * f x v ≤ (1+‖v‖)^k * C/(1+‖v‖)^(k+4) = C/(1+‖v‖)^4
  obtain ⟨C, hC_pos, hbound⟩ := hSchwartz.hDecay (k + 4) 0
  apply (inverse_poly_integrable C).mono'
    ((continuous_norm.pow k |>.mul (hf_smooth x).continuous).aestronglyMeasurable)
  filter_upwards [] with v
  have hb := hbound x v; simp at hb
  -- hb : |f x v| * (1 + ‖v‖) ^ (k + 4) ≤ C
  have hfv_pos := hf_pos x v
  rw [abs_of_pos hfv_pos] at hb
  have h1v : (0 : ℝ) < 1 + ‖v‖ := by linarith [norm_nonneg v]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _)
    (le_of_lt hfv_pos)), le_div_iff₀ (pow_pos h1v 4)]
  have h_norm_le : ‖v‖ ≤ 1 + ‖v‖ := le_add_of_nonneg_left zero_le_one
  calc ‖v‖ ^ k * f x v * (1 + ‖v‖) ^ 4
      ≤ (1 + ‖v‖) ^ k * f x v * (1 + ‖v‖) ^ 4 := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h_norm_le _)
            (le_of_lt hfv_pos)
        · exact pow_nonneg (le_of_lt h1v) _
    _ = f x v * (1 + ‖v‖) ^ (k + 4) := by ring_nf
    _ ≤ C := hb

/-- Spatial transport integrand is dominated by inverse polynomial
    (from Schwartz grad decay + log bound). -/
lemma spatial_transport_integrable
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hf_pos : ∀ x v, 0 < f x v)
    (hSchwartz : UniformSchwartzDecay f)
    (hLogBound : ∃ (C_log : ℝ) (K_log : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log)
    (x : Torus3) :
    Integrable (fun v =>
      v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v)) := by
  obtain ⟨C_log, K_log, hLB⟩ := hLogBound
  -- Suffices to show each component v i * gradX(f)_i * log(f) is integrable
  suffices h : ∀ i : Fin 3,
      Integrable (fun v => v i * FlatTorus3.gradX (fun y => f y v) x i *
        Real.log (f x v)) by
    have heq : (fun v => v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v)) =
        fun v => ∑ i : Fin 3, v i * FlatTorus3.gradX (fun y => f y v) x i *
          Real.log (f x v) := by
      ext v; simp only [dotProduct, Fin.sum_univ_three]; ring
    rw [heq]; exact integrable_finset_sum _ fun i _ => h i
  intro i
  obtain ⟨Ci, hCi, hGi⟩ := hSchwartz.hGradDecay (K_log + 6) i
  apply (inverse_poly_integrable (Ci * (|C_log| + 1))).mono'
  · -- AEStronglyMeasurable — from continuity of the integrand
    sorry
  · filter_upwards [] with v
    rw [Real.norm_eq_abs, le_div_iff₀ (pow_pos (by linarith [norm_nonneg v] : (0:ℝ) < 1 + ‖v‖) 4)]
    have h1v : (1 : ℝ) ≤ 1 + ‖v‖ := le_add_of_nonneg_right (norm_nonneg v)
    have hvi : |v i| ≤ 1 + ‖v‖ :=
      le_trans ((Real.norm_eq_abs _) ▸ norm_le_pi_norm v i) (le_add_of_nonneg_left zero_le_one)
    have hlog : |Real.log (f x v)| ≤ |C_log| * (1 + ‖v‖) ^ K_log :=
      le_trans (hLB x v) (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (by linarith) _))
    have h1v_nn : (0 : ℝ) ≤ 1 + ‖v‖ := le_trans zero_le_one h1v
    have hpow_mono : (1 + ‖v‖) ^ (K_log + 5) ≤ (1 + ‖v‖) ^ (K_log + 6) := by
      have h6eq : (1 + ‖v‖) ^ (K_log + 6) = (1 + ‖v‖) ^ (K_log + 5) * (1 + ‖v‖) := by
        rw [show K_log + 6 = K_log + 5 + 1 from by omega, pow_succ]
      rw [h6eq]; exact le_mul_of_one_le_right (pow_nonneg h1v_nn _) h1v
    have hgrad : |FlatTorus3.gradX (fun y => f y v) x i| * (1 + ‖v‖) ^ (K_log + 5) ≤ Ci :=
      le_trans (mul_le_mul_of_nonneg_left hpow_mono (abs_nonneg _)) (hGi x v)
    set g_i := |FlatTorus3.gradX (fun y => f y v) x i| with hg_i_def
    calc |v i * FlatTorus3.gradX (fun y => f y v) x i * Real.log (f x v)| * (1 + ‖v‖) ^ 4
        = |v i| * g_i * |Real.log (f x v)| *
            (1 + ‖v‖) ^ 4 := by rw [abs_mul, abs_mul]
      _ ≤ (1 + ‖v‖) * g_i *
            (|C_log| * (1 + ‖v‖) ^ K_log) * (1 + ‖v‖) ^ 4 := by gcongr
      _ = |C_log| * (g_i * ((1 + ‖v‖) * (1 + ‖v‖) ^ K_log * (1 + ‖v‖) ^ 4)) := by ring
      _ = |C_log| * (g_i * (1 + ‖v‖) ^ (K_log + 5)) := by
          congr 2; rw [← pow_succ', ← pow_add]
      _ ≤ |C_log| * Ci := by gcongr
      _ ≤ Ci * (|C_log| + 1) := by nlinarith [abs_nonneg C_log, hCi.le]

set_option maxHeartbeats 800000 in
/-- Each force × fderiv × log component is integrable (shared helper for
    force_transport and force_ibp_f_dg). -/
private lemma force_fderiv_log_component_integrable
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (E B : Torus3 → Fin 3 → ℝ)
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x))
    (hSchwartz : UniformSchwartzDecay f)
    (C_log : ℝ) (K_log : ℕ)
    (hLB : ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log)
    (x : Torus3) (i : Fin 3) :
    Integrable (fun v => (E x + cross v (B x)) i *
      fderiv ℝ (f x) v (Pi.single i 1) * Real.log (f x v)) := by
  obtain ⟨CL, hCL_nn, hCL⟩ := lorentz_component_bound (E x) (B x)
  obtain ⟨C_fder, hC_fder_pos, hbound_fder⟩ := hSchwartz.hDecay (K_log + 6) 1
  apply (inverse_poly_integrable (CL * |C_log| * C_fder + 1)).mono'
  · -- AEStronglyMeasurable: each factor is continuous in v
    refine Continuous.aestronglyMeasurable ?_
    have h1 : Continuous (fun v => (E x + cross v (B x)) i) := by
      show Continuous (fun v => E x i + (cross v (B x)) i)
      apply Continuous.add continuous_const
      unfold cross
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        exact (continuous_apply _ |>.mul continuous_const).sub
          (continuous_apply _ |>.mul continuous_const)
    have h2 : Continuous (fun v => fderiv ℝ (f x) v (Pi.single i 1)) :=
      ((hf_smooth x).continuous_fderiv le_top).clm_apply continuous_const
    have h3 : Continuous (fun v => Real.log (f x v)) :=
      (hf_smooth x).continuous.log (fun v => ne_of_gt (hf_pos x v))
    exact (h1.mul h2).mul h3
  · filter_upwards [] with v
    rw [Real.norm_eq_abs, le_div_iff₀ (pow_pos (by linarith [norm_nonneg v] : (0:ℝ) < 1 + ‖v‖) 4)]
    have h1v : (1 : ℝ) ≤ 1 + ‖v‖ := le_add_of_nonneg_right (norm_nonneg v)
    have h1v_nn : (0 : ℝ) ≤ 1 + ‖v‖ := le_trans zero_le_one h1v
    have hfder_le : |fderiv ℝ (f x) v (Pi.single i 1)| ≤ ‖iteratedFDeriv ℝ 1 (f x) v‖ := by
      have h_single_norm : ‖(Pi.single i (1 : ℝ) : Fin 3 → ℝ)‖ ≤ 1 := by
        have : ‖(Pi.single i (1 : ℝ) : Fin 3 → ℝ)‖ = ‖(1 : ℝ)‖ :=
          @Pi.norm_single (Fin 3) (fun _ => ℝ) _ _ (fun _ => inferInstance) (i := i) 1
        rw [this]; simp
      have h_fder_eq : ‖fderiv ℝ (f x) v‖ = ‖iteratedFDeriv ℝ 1 (f x) v‖ := by
        rw [show (1 : ℕ) = 0 + 1 from rfl, ← norm_iteratedFDeriv_fderiv,
          norm_iteratedFDeriv_zero]
      calc |fderiv ℝ (f x) v (Pi.single i 1)|
          = ‖fderiv ℝ (f x) v (Pi.single i 1)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ (f x) v‖ * ‖(Pi.single i (1 : ℝ) : Fin 3 → ℝ)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ (f x) v‖ * 1 := by gcongr
        _ = ‖fderiv ℝ (f x) v‖ := mul_one _
        _ = ‖iteratedFDeriv ℝ 1 (f x) v‖ := h_fder_eq
    have hfder := hbound_fder x v
    have hlog : |Real.log (f x v)| ≤ |C_log| * (1 + ‖v‖) ^ K_log :=
      le_trans (hLB x v) (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg h1v_nn _))
    have hpow_mono : (1 + ‖v‖) ^ (K_log + 5) ≤ (1 + ‖v‖) ^ (K_log + 6) := by
      have h6eq : (1 + ‖v‖) ^ (K_log + 6) = (1 + ‖v‖) ^ (K_log + 5) * (1 + ‖v‖) := by
        rw [show K_log + 6 = K_log + 5 + 1 from by omega, pow_succ]
      rw [h6eq]; exact le_mul_of_one_le_right (pow_nonneg h1v_nn _) h1v
    set D := ‖iteratedFDeriv ℝ 1 (f x) v‖ with hD_def
    calc |(E x + cross v (B x)) i * fderiv ℝ (f x) v (Pi.single i 1) *
              Real.log (f x v)| * (1 + ‖v‖) ^ 4
        = |(E x + cross v (B x)) i| * |fderiv ℝ (f x) v (Pi.single i 1)| *
            |Real.log (f x v)| * (1 + ‖v‖) ^ 4 := by rw [abs_mul, abs_mul]
      _ ≤ (CL * (1 + ‖v‖)) * D * (|C_log| * (1 + ‖v‖) ^ K_log) *
            (1 + ‖v‖) ^ 4 := by gcongr; exact hCL v i
      _ = CL * |C_log| * (D * ((1 + ‖v‖) * (1 + ‖v‖) ^ K_log *
            (1 + ‖v‖) ^ 4)) := by ring
      _ = CL * |C_log| * (D * (1 + ‖v‖) ^ (K_log + 5)) := by
          congr 2; rw [← pow_succ', ← pow_add]
      _ ≤ CL * |C_log| * (D * (1 + ‖v‖) ^ (K_log + 6)) := by gcongr
      _ ≤ CL * |C_log| * C_fder := by gcongr
      _ ≤ CL * |C_log| * C_fder + 1 := le_add_of_nonneg_right zero_le_one

/-- Force transport integrand is integrable
    (from Schwartz derivative decay + log bound + Lorentz bound). -/
lemma force_transport_integrable_coulomb
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (E B : Torus3 → Fin 3 → ℝ)
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x))
    (hSchwartz : UniformSchwartzDecay f)
    (hLogBound : ∃ (C_log : ℝ) (K_log : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log)
    (x : Torus3) :
    Integrable (fun v =>
      (E x + cross v (B x)) ⬝ᵥ vGrad (f x) v * Real.log (f x v)) := by
  obtain ⟨C_log, K_log, hLB⟩ := hLogBound
  have heq : (fun v => (E x + cross v (B x)) ⬝ᵥ vGrad (f x) v * Real.log (f x v)) =
      fun v => ∑ i : Fin 3, (E x + cross v (B x)) i *
        fderiv ℝ (f x) v (Pi.single i 1) * Real.log (f x v) := by
    ext v; simp only [dotProduct, vGrad, Fin.sum_univ_three]; ring
  rw [heq]; exact integrable_finset_sum _ fun i _ =>
    force_fderiv_log_component_integrable E B hf_pos hf_smooth hSchwartz C_log K_log hLB x i

set_option maxHeartbeats 800000 in
/-- Force IBP (f·dg form) integrand is integrable.
    Uses chain rule: d/dv(f·log f - f) = f'·log f. -/
lemma force_ibp_f_dg_integrable_coulomb
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (E B : Torus3 → Fin 3 → ℝ)
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x))
    (hSchwartz : UniformSchwartzDecay f)
    (hLogBound : ∃ (C_log : ℝ) (K_log : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log)
    (x : Torus3) (i : Fin 3) :
    Integrable (fun v =>
      (E x + cross v (B x)) i *
        fderiv ℝ (fun w => f x w * Real.log (f x w) - f x w) v (Pi.single i 1)) := by
  obtain ⟨C_log, K_log, hLB⟩ := hLogBound
  -- Chain rule: fderiv(f·log f - f) = log(f) • fderiv(f)
  have hfder_eq : ∀ v,
      fderiv ℝ (fun w => f x w * Real.log (f x w) - f x w) v (Pi.single i 1) =
      Real.log (f x v) * fderiv ℝ (f x) v (Pi.single i 1) := by
    intro v
    have hfx_hfd : HasFDerivAt (f x) (fderiv ℝ (f x) v) v :=
      ((hf_smooth x).differentiable le_top).differentiableAt.hasFDerivAt
    have hlog_hfd : HasFDerivAt (fun w => Real.log (f x w))
        ((f x v)⁻¹ • fderiv ℝ (f x) v) v :=
      hfx_hfd.log (ne_of_gt (hf_pos x v))
    have h_mul_hfd : HasFDerivAt (fun w => f x w * Real.log (f x w))
        (f x v • ((f x v)⁻¹ • fderiv ℝ (f x) v) +
         Real.log (f x v) • fderiv ℝ (f x) v) v :=
      hfx_hfd.fun_mul hlog_hfd
    have h_sub_hfd := h_mul_hfd.fun_sub hfx_hfd
    rw [h_sub_hfd.fderiv]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hfv_ne : f x v ≠ 0 := ne_of_gt (hf_pos x v)
    rw [← mul_assoc, mul_inv_cancel₀ hfv_ne, one_mul]
    ring
  -- Rewrite integrand using the chain rule
  have heq : (fun v => (E x + cross v (B x)) i *
      fderiv ℝ (fun w => f x w * Real.log (f x w) - f x w) v (Pi.single i 1)) =
      fun v => (E x + cross v (B x)) i *
        fderiv ℝ (f x) v (Pi.single i 1) * Real.log (f x v) := by
    ext v; rw [hfder_eq]; ring
  rw [heq]
  exact force_fderiv_log_component_integrable E B hf_pos hf_smooth hSchwartz
    C_log K_log hLB x i

/-- Force IBP (f·g form) integrand is integrable. -/
lemma force_ibp_fg_integrable_coulomb
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (E B : Torus3 → Fin 3 → ℝ)
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x))
    (hSchwartz : UniformSchwartzDecay f)
    (hLogBound : ∃ (C_log : ℝ) (K_log : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log)
    (x : Torus3) (i : Fin 3) :
    Integrable (fun v =>
      (E x + cross v (B x)) i * (f x v * Real.log (f x v) - f x v)) := by
  obtain ⟨C_log, K_log, hLB⟩ := hLogBound
  obtain ⟨CL, hCL_nn, hCL⟩ := lorentz_component_bound (E x) (B x)
  apply integrable_of_schwartz_bound
    (fun k => schwartz_norm_pow_integrable hf_pos hf_smooth hSchwartz x k)
  · -- AEStronglyMeasurable: force term * entropy density is continuous in v
    refine Continuous.aestronglyMeasurable ?_
    have h1 : Continuous (fun v => (E x + cross v (B x)) i) := by
      show Continuous (fun v => E x i + (cross v (B x)) i)
      apply Continuous.add continuous_const
      unfold cross
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        exact (continuous_apply _ |>.mul continuous_const).sub
          (continuous_apply _ |>.mul continuous_const)
    have h2 : Continuous (fun v => f x v * Real.log (f x v) - f x v) :=
      ((hf_smooth x).continuous.mul
        ((hf_smooth x).continuous.log (fun v => ne_of_gt (hf_pos x v)))).sub
        (hf_smooth x).continuous
    exact h1.mul h2
  · exact mul_nonneg hCL_nn (by positivity : 0 ≤ |C_log| + 1)
  · intro v
    rw [Real.norm_eq_abs]
    have hfv := hf_pos x v
    -- |F_i * (f * log f - f)| = |F_i| * f * |log f - 1|
    have hab : |f x v * Real.log (f x v) - f x v| = f x v * |Real.log (f x v) - 1| := by
      rw [show f x v * Real.log (f x v) - f x v = f x v * (Real.log (f x v) - 1) from by ring,
        abs_mul, abs_of_pos hfv]
    -- |log f - 1| ≤ |log f| + 1 ≤ (|C_log| + 1) * (1+‖v‖)^K_log
    have h1v : (1 : ℝ) ≤ (1 + ‖v‖) ^ K_log := one_le_pow₀ (by linarith [norm_nonneg v])
    have hlog_sub : |Real.log (f x v) - 1| ≤ (|C_log| + 1) * (1 + ‖v‖) ^ K_log := by
      calc |Real.log (f x v) - 1|
          = |Real.log (f x v) + (-1)| := by ring_nf
        _ ≤ |Real.log (f x v)| + |-1| := by
            have := norm_add_le (Real.log (f x v)) (-1)
            rwa [show Real.log (f x v) + -1 = Real.log (f x v) - 1 from by ring,
              Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at this
        _ = |Real.log (f x v)| + 1 := by rw [abs_neg, abs_one]
        _ ≤ |C_log| * (1 + ‖v‖) ^ K_log + 1 := by
            linarith [le_trans (hLB x v) (mul_le_mul_of_nonneg_right (le_abs_self _)
              (pow_nonneg (by linarith [norm_nonneg v]) _))]
        _ ≤ (|C_log| + 1) * (1 + ‖v‖) ^ K_log := by nlinarith
    calc |(E x + cross v (B x)) i * (f x v * Real.log (f x v) - f x v)|
        = |(E x + cross v (B x)) i| * |f x v * Real.log (f x v) - f x v| := abs_mul _ _
      _ = |(E x + cross v (B x)) i| * (f x v * |Real.log (f x v) - 1|) := by rw [hab]
      _ ≤ CL * (1 + ‖v‖) * (f x v * ((|C_log| + 1) * (1 + ‖v‖) ^ K_log)) := by
          gcongr; exact hCL v i
      _ = CL * (|C_log| + 1) * (1 + ‖v‖) ^ (K_log + 1) * |f x v| := by
          rw [abs_of_pos hfv]
          have h_pow : (1 + ‖v‖) * (1 + ‖v‖) ^ K_log = (1 + ‖v‖) ^ (K_log + 1) :=
            (pow_succ' _ _).symm
          calc CL * (1 + ‖v‖) * (f x v * ((|C_log| + 1) * (1 + ‖v‖) ^ K_log))
              = CL * (|C_log| + 1) * ((1 + ‖v‖) * (1 + ‖v‖) ^ K_log) * f x v := by ring
            _ = CL * (|C_log| + 1) * (1 + ‖v‖) ^ (K_log + 1) * f x v := by rw [h_pow]

set_option maxHeartbeats 800000 in
/-- Spatial transport joint integrability (Fubini on compact torus × ℝ³).
    Uses: uniform Schwartz grad decay → uniform velocity integral bound,
    combined with finite measure on compact T³ → joint integrability. -/
lemma spatial_transport_joint_integrable
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth_v : ∀ x, ContDiff ℝ ⊤ (f x))
    (hf_smooth_x : ∀ v, ContDiff ℝ ⊤ (periodicLift (fun x => f x v)))
    (hSchwartz : UniformSchwartzDecay f)
    (hLogBound : ∃ (C_log : ℝ) (K_log : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log) :
    Integrable (Function.uncurry (fun x v =>
      v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v)))
      (volume.prod volume) := by
  obtain ⟨C_log, K_log, hLB⟩ := hLogBound
  set g : Torus3 → (Fin 3 → ℝ) → ℝ :=
    fun x v => v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v) with hg_def
  -- Uniform bound: |g x v| ≤ C_total / (1+‖v‖)^4 for all x, v
  -- from Schwartz grad decay + log bound
  have h_unif_bound : ∃ C_total > 0, ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |g x v| ≤ C_total / (1 + ‖v‖) ^ 4 := by
    -- Get gradient decay bounds for each component
    have hLB' : ∀ (x : Torus3) (v : Fin 3 → ℝ),
        |Real.log (f x v)| ≤ |C_log| * (1 + ‖v‖) ^ K_log :=
      fun x v => le_trans (hLB x v) (mul_le_mul_of_nonneg_right (le_abs_self _)
        (pow_nonneg (by linarith [norm_nonneg v]) _))
    -- Sum of 3 components bound
    obtain ⟨C0, hC0, hG0⟩ := hSchwartz.hGradDecay (K_log + 6) 0
    obtain ⟨C1, hC1, hG1⟩ := hSchwartz.hGradDecay (K_log + 6) 1
    obtain ⟨C2, hC2, hG2⟩ := hSchwartz.hGradDecay (K_log + 6) 2
    refine ⟨(C0 + C1 + C2) * (|C_log| + 1) + 1, by positivity, fun x v => ?_⟩
    have h1v : (1 : ℝ) ≤ 1 + ‖v‖ := le_add_of_nonneg_right (norm_nonneg v)
    have h1v_nn : (0 : ℝ) ≤ 1 + ‖v‖ := le_trans zero_le_one h1v
    -- Decompose g into 3 components
    have hg_eq : g x v = ∑ i : Fin 3, v i *
        FlatTorus3.gradX (fun y => f y v) x i * Real.log (f x v) := by
      simp only [hg_def, dotProduct, Fin.sum_univ_three]; ring
    rw [hg_eq]
    -- |∑ᵢ comp_i| ≤ ∑ᵢ |comp_i|
    calc |∑ i : Fin 3, v i * FlatTorus3.gradX (fun y => f y v) x i * Real.log (f x v)|
        ≤ ∑ i : Fin 3, |v i * FlatTorus3.gradX (fun y => f y v) x i *
            Real.log (f x v)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 3, (1 + ‖v‖) *
            (if i = 0 then C0 else if i = 1 then C1 else C2) /
            (1 + ‖v‖) ^ (K_log + 6) *
            (|C_log| * (1 + ‖v‖) ^ K_log) := by
          apply Finset.sum_le_sum; intro i _
          rw [abs_mul, abs_mul]
          have hvi : |v i| ≤ 1 + ‖v‖ := le_trans
            ((Real.norm_eq_abs _) ▸ norm_le_pi_norm v i) (le_add_of_nonneg_left zero_le_one)
          have hlog := hLB' x v
          have hgrad : |FlatTorus3.gradX (fun y => f y v) x i| ≤
              (if i = 0 then C0 else if i = 1 then C1 else C2) /
              (1 + ‖v‖) ^ (K_log + 6) := by
            rw [le_div_iff₀ (pow_pos (by linarith : (0 : ℝ) < 1 + ‖v‖) _)]
            fin_cases i
            · exact hG0 x v
            · exact hG1 x v
            · exact hG2 x v
          calc |v i| * |FlatTorus3.gradX (fun y => f y v) x i| * |Real.log (f x v)|
              ≤ (1 + ‖v‖) * ((if i = 0 then C0 else if i = 1 then C1 else C2) /
                (1 + ‖v‖) ^ (K_log + 6)) * (|C_log| * (1 + ‖v‖) ^ K_log) := by
                gcongr
            _ = _ := by ring
      _ ≤ (C0 + C1 + C2) * (|C_log| + 1) / (1 + ‖v‖) ^ 4 := by
          simp only [Fin.sum_univ_three, Fin.isValue, ↓reduceIte, Fin.reduceEq]
          have hpow_bound : (1 + ‖v‖) * (1 + ‖v‖) ^ K_log / (1 + ‖v‖) ^ (K_log + 6) ≤
              1 / (1 + ‖v‖) ^ 4 := by
            rw [div_le_div_iff₀ (pow_pos (by linarith) _) (pow_pos (by linarith) _)]
            rw [one_mul, show K_log + 6 = (K_log + 1) + 5 from by omega, pow_add,
              show (1 + ‖v‖) * (1 + ‖v‖) ^ K_log = (1 + ‖v‖) ^ (K_log + 1) from
                (pow_succ' _ _).symm]
            exact mul_le_mul_of_nonneg_left (by nlinarith [pow_nonneg h1v_nn 4])
              (pow_nonneg h1v_nn _)
          -- Each summand bounded via hpow_bound
          have h_factor : ∀ Ci : ℝ, 0 < Ci →
              (1 + ‖v‖) * Ci / (1 + ‖v‖) ^ (K_log + 6) * (|C_log| * (1 + ‖v‖) ^ K_log) ≤
              Ci * |C_log| / (1 + ‖v‖) ^ 4 := by
            intro Ci hCi
            rw [show (1 + ‖v‖) * Ci / (1 + ‖v‖) ^ (K_log + 6) * (|C_log| * (1 + ‖v‖) ^ K_log) =
                Ci * |C_log| * ((1 + ‖v‖) * (1 + ‖v‖) ^ K_log / (1 + ‖v‖) ^ (K_log + 6))
                from by ring,
              show Ci * |C_log| / (1 + ‖v‖) ^ 4 =
                Ci * |C_log| * (1 / (1 + ‖v‖) ^ 4) from by ring]
            exact mul_le_mul_of_nonneg_left hpow_bound (by positivity)
          have hp4 : (0 : ℝ) < (1 + ‖v‖) ^ 4 := pow_pos (by linarith) 4
          have h_sum_bound : C0 * |C_log| / (1 + ‖v‖) ^ 4 + C1 * |C_log| / (1 + ‖v‖) ^ 4 +
              C2 * |C_log| / (1 + ‖v‖) ^ 4 ≤
              (C0 + C1 + C2) * (|C_log| + 1) / (1 + ‖v‖) ^ 4 := by
            rw [show C0 * |C_log| / (1 + ‖v‖) ^ 4 + C1 * |C_log| / (1 + ‖v‖) ^ 4 +
                C2 * |C_log| / (1 + ‖v‖) ^ 4 =
                (C0 + C1 + C2) * |C_log| / (1 + ‖v‖) ^ 4 from by ring,
              div_le_div_iff₀ hp4 hp4]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg C_log]) (by linarith)) hp4.le
          linarith [h_factor C0 hC0, h_factor C1 hC1, h_factor C2 hC2]
      _ ≤ ((C0 + C1 + C2) * (|C_log| + 1) + 1) / (1 + ‖v‖) ^ 4 := by
          gcongr; linarith
  obtain ⟨C_total, hC_total_pos, h_bound⟩ := h_unif_bound
  -- Use integrable_prod_iff
  refine (integrable_prod_iff ?_).mpr ⟨?_, ?_⟩
  · -- AEStronglyMeasurable on product (joint regularity)
    sorry
  · -- ∀ᵐ x, Integrable (fun v => g x v)
    exact Filter.Eventually.of_forall (fun x =>
      spatial_transport_integrable hf_pos hSchwartz ⟨C_log, K_log, hLB⟩ x)
  · -- Integrable (fun x => ∫ v, ‖g x v‖) on compact T³
    -- The velocity integral is uniformly bounded by C_total * M
    -- where M = ∫ v, 1/(1+‖v‖)^4, so the function is bounded on T³ (finite measure)
    apply (integrable_const (C_total * ∫ v : Fin 3 → ℝ, (1 + ‖v‖)⁻¹ ^ 4)).mono'
    · sorry -- AEStronglyMeasurable (x ↦ ∫ v, ‖g x v‖)
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun v => norm_nonneg _))]
      calc ∫ v, ‖g x v‖
          ≤ ∫ v, C_total / (1 + ‖v‖) ^ 4 := by
            apply integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall (fun v => norm_nonneg _)
            · exact inverse_poly_integrable C_total
            · exact Filter.Eventually.of_forall (fun v => by
                show ‖g x v‖ ≤ C_total / (1 + ‖v‖) ^ 4
                rw [Real.norm_eq_abs]; exact h_bound x v)
        _ = C_total * ∫ v, (1 + ‖v‖)⁻¹ ^ 4 := by
            simp_rw [div_eq_mul_inv, inv_pow]; exact integral_mul_left _ _

/-- Coulomb Landau matrix entry bound: |A(z)_{ij}| ≤ (eucNorm z)⁻¹ for z ≠ 0,
    and A(0) = 0. This is the key bound enabling integrability of collision
    integrands despite the singular kernel Ψ(r) = r⁻³. -/
lemma coulomb_landauMatrix_entry_le (z : Fin 3 → ℝ) (i j : Fin 3) :
    |landauMatrix coulombKernel z i j| ≤
      if z = 0 then 0 else (eucNorm z)⁻¹ := by
  by_cases hz : z = 0
  · -- z = 0: landauMatrix _ 0 = 0 (inner matrix vanishes)
    simp [hz, landauMatrix, innerLandauMatrix, normSq, dotProduct, vecMulVec, eucNorm]
  · simp [hz]
    -- |Ψ(|z|) * B(z)_{ij}| ≤ |z|^{-3} * |z|² = |z|^{-1}
    simp only [landauMatrix, smul_apply, smul_eq_mul]
    have henz : 0 < eucNorm z := by
      rw [eucNorm]; exact Real.sqrt_pos_of_pos (normSq_pos hz)
    have h_inner : |innerLandauMatrix z i j| ≤ normSq z := by
      rw [innerLandauMatrix_apply]
      have hns : normSq z = ∑ k : Fin 3, z k * z k := by
        simp [normSq, dotProduct, Fin.sum_univ_three]
      split_ifs with hij
      · subst hij; rw [hns]; simp only [Fin.sum_univ_three]
        fin_cases i <;> simp <;> (rw [abs_of_nonneg (by nlinarith [mul_self_nonneg (z 0), mul_self_nonneg (z 1), mul_self_nonneg (z 2)])]; nlinarith [mul_self_nonneg (z 0), mul_self_nonneg (z 1), mul_self_nonneg (z 2)])
      · simp only [zero_sub, abs_neg]; rw [hns]; simp only [Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> simp_all <;>
          nlinarith [sq_nonneg (|z 0| - |z 1|), sq_nonneg (|z 0| - |z 2|),
            sq_nonneg (|z 1| - |z 2|),
            abs_mul_abs_self (z 0), abs_mul_abs_self (z 1), abs_mul_abs_self (z 2)]
    calc |coulombKernel (eucNorm z) * innerLandauMatrix z i j|
        = |coulombKernel (eucNorm z)| * |innerLandauMatrix z i j| := abs_mul _ _
      _ ≤ |coulombKernel (eucNorm z)| * normSq z :=
          mul_le_mul_of_nonneg_left h_inner (abs_nonneg _)
      _ = eucNorm z ^ (-3 : ℝ) * normSq z := by
          congr 1
          rw [coulombKernel, if_neg (by linarith : ¬eucNorm z ≤ 0)]
          exact abs_of_pos (rpow_pos_of_pos henz _)
      _ = eucNorm z ^ (-3 : ℝ) * eucNorm z ^ (2 : ℕ) := by
          congr 1; exact (eucNorm_sq z).symm
      _ = (eucNorm z)⁻¹ := by
          rw [← rpow_natCast (eucNorm z) 2, ← rpow_add henz]
          show eucNorm z ^ ((-3 : ℝ) + (2 : ℝ)) = (eucNorm z)⁻¹
          norm_num [rpow_neg_one]

/-- Pi norm ≤ Euclidean norm in ℝ³: ‖z‖_∞ ≤ √(z·z). -/
private lemma pi_norm_le_eucNorm (z : Fin 3 → ℝ) : ‖z‖ ≤ eucNorm z := by
  rw [pi_norm_le_iff_of_nonneg (eucNorm_nonneg z)]
  intro i; rw [Real.norm_eq_abs, eucNorm, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  unfold normSq dotProduct; simp only [Fin.sum_univ_three]
  fin_cases i <;> simp <;>
    nlinarith [mul_self_nonneg (z 0), mul_self_nonneg (z 1), mul_self_nonneg (z 2)]

/-- Coulomb matrix entry bound in Pi norm: |A(z)_{ij}| ≤ ‖z‖⁻¹ for z ≠ 0. -/
private lemma coulomb_landauMatrix_entry_le_pi (z : Fin 3 → ℝ) (i j : Fin 3)
    (hz : z ≠ 0) :
    |landauMatrix coulombKernel z i j| ≤ ‖z‖⁻¹ := by
  have h := coulomb_landauMatrix_entry_le z i j
  simp [hz] at h
  exact le_trans h (inv_anti₀ (norm_pos_iff.mpr hz) (pi_norm_le_eucNorm z))

/-- Key integrability fact for Coulomb kernel: ‖·‖⁻¹ × Schwartz is integrable in ℝ³.
    Awaiting Aristotle proof (jobs 403eee35, 3dc1b4dc, 1ba752be). -/
private lemma inv_norm_schwartz_integrable
    (g : (Fin 3 → ℝ) → ℝ)
    (hg_decay : ∀ N : ℕ, ∃ C > 0, ∀ w : Fin 3 → ℝ, |g w| * (1 + ‖w‖) ^ N ≤ C)
    (hg_meas : AEStronglyMeasurable g volume)
    (v : Fin 3 → ℝ) :
    Integrable (fun w => ‖v - w‖⁻¹ * g w) := by sorry

/-- **Coulomb Theorem 42.** Characterization of smooth steady states of the
    Vlasov–Maxwell–Landau system with Coulomb collisions on T³ = (ℝ/ℤ)³.

    This is the physically most important case: Coulomb interactions between
    charged particles in a plasma. The collision kernel Ψ(r) = r⁻³ is singular
    at r = 0 but the formalization handles this via the PSD continuity condition
    in VelocityDecayConditions (the singularity cancels in the quadratic form).

    **Hypotheses** (12 total):
    - 2 physical parameters (ν > 0, ρ_ion > 0)
    - 1 strict positivity (f > 0)
    - 3 smoothness (f smooth in v and x, B smooth)
    - 2 decay (f Schwartz in v uniform in x; at most stretched-exponential decay)
    - 4 equations (Vlasov, Ampère, Gauss, div B = 0) -/
theorem CoulombConcreteTheorem42
    -- === Physical state at steady state ===
    (f : Torus3 → (Fin 3 → ℝ) → ℝ)
    (E B : Torus3 → Fin 3 → ℝ)
    (ν ρ_ion : ℝ)
    -- === Physical parameters ===
    (hν : 0 < ν)                                -- (1)
    (hρ_ion : 0 < ρ_ion)                        -- (2)
    (hf_pos : ∀ x v, 0 < f x v)                -- (3)
    -- === Smoothness ===
    (hf_smooth_v : ∀ x, ContDiff ℝ ⊤ (f x))                             -- (4)
    (hf_smooth_x : ∀ v, ContDiff ℝ ⊤ (periodicLift (fun x => f x v)))   -- (5)
    (hB_smooth : ∀ i, ContDiff ℝ ⊤ (periodicLift (fun x => B x i)))     -- (6)
    -- === Schwartz-class velocity decay, uniform in x ===
    (hSchwartz : UniformSchwartzDecay f)         -- (7)
    (hExpDecay : ∃ (C : ℝ) (K : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      Real.exp (-C * (1 + ‖v‖) ^ K) ≤ f x v)   -- (8)
    -- === Steady-state Vlasov equation with Coulomb kernel ===
    (hVlasov : ∀ x v,
      dotProduct v (torusGradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator coulombKernel (f x) v)  -- (9)
    -- === Steady-state Maxwell equations ===
    (hAmpere : ∀ x, torusCurlX B x = fun i => ∫ v, v i * f x v)       -- (10)
    (hGauss : ∀ x, torusDivX E x = (∫ v, f x v) - ρ_ion)              -- (11)
    (hDivB : ∀ x, torusDivX B x = 0)             -- (12)
    :
    -- === Conclusion ===
    ∃ (T_eq : ℝ) (B₀ : Fin 3 → ℝ), 0 < T_eq ∧
    (∀ x v, f x v = equilibriumMaxwellian ρ_ion T_eq v) ∧
    (∀ x, E x = 0) ∧
    (∀ x, B x = B₀) := by
  -- Derive log bound from Schwartz + ExpDecay (used by many fields)
  have hLogBound := schwartz_log_bound hf_pos hSchwartz hExpDecay
  have hDecay : VelocityDecayConditions coulombKernel f E B := {
    hPSD_inner_int := by sorry
    hPSD_outer_int := by sorry
    hFubini_double := by sorry
    hFubini_inner := by sorry
    hFubini_outer := by sorry
    hSpatialTransport_int := fun x =>
      spatial_transport_integrable hf_pos hSchwartz hLogBound x
    hForceTransport_int := fun x =>
      force_transport_integrable_coulomb E B hf_pos hf_smooth_v hSchwartz hLogBound x
    hLandauFluxDiff := by sorry
    hLandauIBP_df_g := by sorry
    hLandauIBP_f_dg := by sorry
    hLandauIBP_fg := by sorry
    hLandauFluxInt := by sorry
    hForceIBP_f_dg := fun x i =>
      force_ibp_f_dg_integrable_coulomb E B hf_pos hf_smooth_v hSchwartz hLogBound x i
    hForceIBP_fg := fun x i =>
      force_ibp_fg_integrable_coulomb E B hf_pos hf_smooth_v hSchwartz hLogBound x i
    hSpatialTransport_joint :=
      spatial_transport_joint_integrable hf_pos hf_smooth_v hf_smooth_x hSchwartz hLogBound
    hSpatTransComp := by
      intro v i
      have hDiff_fv : FlatTorus3.IsSpatiallyDiff (fun x => f x v) := hf_smooth_x v
      have hcont_grad := FlatTorus3.hDiff_continuous _ (FlatTorus3.hDiff_grad _ i hDiff_fv)
      have hcont_log := FlatTorus3.hDiff_continuous _
        (FlatTorus3.hDiff_log _ hDiff_fv (fun x => hf_pos x v))
      exact (hcont_grad.mul hcont_log).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    hf_velocity_dominated := by
      obtain ⟨C, hC_pos, hbound⟩ := hSchwartz.hDecay 4 0
      refine ⟨fun v => C / (1 + ‖v‖) ^ 4, inverse_poly_integrable C, fun x v => ?_⟩
      have hb := hbound x v
      simp at hb
      have hv_pos : (0 : ℝ) < (1 + ‖v‖) ^ 4 := by positivity
      rw [abs_of_pos (hf_pos x v)] at hb
      rwa [le_div_iff₀ hv_pos]
    -- PSD continuity: the key Coulomb-specific condition.
    -- Despite Ψ(r) = r⁻³ being singular, the PSD integrand is continuous
    -- because the score difference Δ = O(|v-w|) cancels the singularity.
    hPSD_cont := by sorry
    hD_cont := by sorry
  }
  exact Theorem42 f E B coulombKernel ν ρ_ion
    hν hρ_ion coulombKernel_pos hf_pos hf_smooth_v
    (hSchwartz.integrable hf_smooth_v)
    hAmpere hGauss hDivB hB_smooth hVlasov hf_smooth_x hDecay

end VML
