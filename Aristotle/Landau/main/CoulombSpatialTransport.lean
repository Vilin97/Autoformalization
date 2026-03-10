import Aristotle.Landau.main.CoulombKernel

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 1600000 in
/-- Spatial gradient of f w.r.t. x is AEStronglyMeasurable in v, via difference quotient limits. -/
lemma torusGradX_aestronglyMeasurable
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hf_smooth_v : ∀ x, ContDiff ℝ ⊤ (f x))
    (hf_smooth_x : ∀ v, ContDiff ℝ ⊤ (periodicLift (fun x => f x v)))
    (x : Torus3) (i : Fin 3) :
    AEStronglyMeasurable
      (fun v => torusGradX (fun y => f y v) x i) volume := by
  set x₀ := (torusMk_surjective x).choose
  set ei := (Pi.single i (1 : ℝ) : Fin 3 → ℝ)
  set G : ℕ → (Fin 3 → ℝ) → ℝ := fun n v =>
    (↑n + 1 : ℝ) * (f (torusMk (x₀ + (↑n + 1 : ℝ)⁻¹ • ei)) v - f (torusMk x₀) v)
  have hG_meas : ∀ n, AEStronglyMeasurable (G n) volume := fun n =>
    ((hf_smooth_v (torusMk (x₀ + _))).continuous.sub
      (hf_smooth_v (torusMk x₀)).continuous).aestronglyMeasurable.const_mul _
  have hG_lim : ∀ v, Filter.Tendsto (fun n => G n v) Filter.atTop
      (nhds (torusGradX (fun y => f y v) x i)) := by
    intro v
    unfold torusGradX
    set F := periodicLift (fun y => f y v)
    have hF_diff : DifferentiableAt ℝ F x₀ :=
      (hf_smooth_x v).differentiable le_top |>.differentiableAt
    have hg : HasDerivAt (fun t : ℝ => x₀ + t • (Pi.single i (1 : ℝ) : Fin 3 → ℝ))
        (Pi.single i (1 : ℝ) : Fin 3 → ℝ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
        (Pi.single i (1 : ℝ) : Fin 3 → ℝ)).const_add x₀
    have h_eq : x₀ + (0 : ℝ) • (Pi.single i (1 : ℝ) : Fin 3 → ℝ) = x₀ := by simp
    have hF_at : HasFDerivAt F (fderiv ℝ F x₀)
        (x₀ + (0 : ℝ) • (Pi.single i (1 : ℝ) : Fin 3 → ℝ)) := by
      rw [h_eq]; exact hF_diff.hasFDerivAt
    have hline : HasDerivAt (fun t : ℝ => F (x₀ + t • ei)) (fderiv ℝ F x₀ ei) 0 := by
      change HasDerivAt (fun t => F (x₀ + t • ei)) (fderiv ℝ F x₀ ei) 0
      convert hF_at.comp_hasDerivAt (x := (0 : ℝ)) hg using 1
    have htendsto_inv : Filter.Tendsto (fun n : ℕ => ((↑n + 1 : ℝ))⁻¹) Filter.atTop
        (nhdsWithin 0 (Set.Ioi 0)) :=
      tendsto_nhdsWithin_iff.mpr ⟨
        Filter.Tendsto.comp tendsto_inv_atTop_zero
          (Filter.Tendsto.atTop_add (tendsto_natCast_atTop_atTop (R := ℝ)) tendsto_const_nhds),
        Filter.Eventually.of_forall fun n => Set.mem_Ioi.mpr (by positivity)⟩
    have h := Filter.Tendsto.comp hline.tendsto_slope_zero_right htendsto_inv
    simp only [smul_eq_mul, Function.comp_def, inv_inv, zero_smul, add_zero, zero_add] at h
    convert h using 1
  exact aestronglyMeasurable_of_tendsto_ae Filter.atTop hG_meas
    (Filter.Eventually.of_forall hG_lim)

set_option maxHeartbeats 800000 in
/-- Spatial transport integrand is dominated by inverse polynomial
    (from Schwartz grad decay + log bound). -/
lemma spatial_transport_integrable
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth_v : ∀ x, ContDiff ℝ ⊤ (f x))
    (hf_smooth_x : ∀ v, ContDiff ℝ ⊤ (periodicLift (fun x => f x v)))
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
  · -- AEStronglyMeasurable — product of measurable/continuous functions
    -- v ↦ v i is continuous, v ↦ log(f x v) is continuous, v ↦ gradX is AEStronglyMeasurable
    exact ((continuous_apply i).aestronglyMeasurable.mul
      (torusGradX_aestronglyMeasurable hf_smooth_v hf_smooth_x x i)).mul
      ((hf_smooth_v x).continuous.log (fun v => ne_of_gt (hf_pos x v))).aestronglyMeasurable
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
lemma force_fderiv_log_component_integrable
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

set_option maxHeartbeats 1600000 in
/-- The spatial gradient component `v ↦ gradX(fun y => f y v)(x)(i)` is strongly measurable
    in `v`. Proved via difference quotient approximation: each quotient is continuous in `v`
    (since `f(x,·)` is smooth for each torus point), and the fderiv is their pointwise limit. -/
lemma gradX_stronglyMeasurable_v
    (f : Torus3 → (Fin 3 → ℝ) → ℝ)
    (hf_smooth_v : ∀ x, ContDiff ℝ ⊤ (f x))
    (hf_smooth_x : ∀ v, ContDiff ℝ ⊤ (periodicLift (fun x => f x v)))
    (x : Torus3) (i : Fin 3) :
    StronglyMeasurable (fun v => FlatTorus3.gradX (fun y => f y v) x i) := by
  -- Unfold to torusGradX on concrete torus
  show StronglyMeasurable (fun v => torusGradX (fun y => f y v) x i)
  unfold torusGradX
  set x₀ := (torusMk_surjective x).choose
  set ei := (Pi.single i (1 : ℝ) : Fin 3 → ℝ)
  -- Approximate fderiv by difference quotients
  set G : ℕ → (Fin 3 → ℝ) → ℝ := fun n v =>
    (↑n + 1 : ℝ) * (f (torusMk (x₀ + (↑n + 1 : ℝ)⁻¹ • ei)) v - f (torusMk x₀) v)
  have hG_sm : ∀ n, StronglyMeasurable (G n) := fun n =>
    ((hf_smooth_v (torusMk (x₀ + _))).continuous.sub
      (hf_smooth_v (torusMk x₀)).continuous).stronglyMeasurable.const_mul _
  apply stronglyMeasurable_of_tendsto Filter.atTop hG_sm
  rw [tendsto_pi_nhds]
  intro v
  set F := periodicLift (fun y => f y v)
  have hF_diff : DifferentiableAt ℝ F x₀ :=
    (hf_smooth_x v).differentiable le_top |>.differentiableAt
  have hg : HasDerivAt (fun t : ℝ => x₀ + t • ei) ei 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ei).const_add x₀
  have h_eq : x₀ + (0 : ℝ) • ei = x₀ := by simp
  have hF_at : HasFDerivAt F (fderiv ℝ F x₀) (x₀ + (0 : ℝ) • ei) := by
    rw [h_eq]; exact hF_diff.hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => F (x₀ + t • ei)) (fderiv ℝ F x₀ ei) 0 := by
    convert hF_at.comp_hasDerivAt (x := (0 : ℝ)) hg using 1
  have htendsto_inv : Filter.Tendsto (fun n : ℕ => ((↑n + 1 : ℝ))⁻¹) Filter.atTop
      (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨
      Filter.Tendsto.comp tendsto_inv_atTop_zero
        (Filter.Tendsto.atTop_add (tendsto_natCast_atTop_atTop (R := ℝ)) tendsto_const_nhds),
      Filter.Eventually.of_forall fun n => Set.mem_Ioi.mpr (by positivity)⟩
  have h := Filter.Tendsto.comp hline.tendsto_slope_zero_right htendsto_inv
  simp only [smul_eq_mul, Function.comp_def, inv_inv, zero_smul, add_zero, zero_add] at h
  convert h using 1

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
    -- Use stronglyMeasurable_uncurry: need ∀ v, Continuous(x ↦ g x v) and ∀ x, SM(v ↦ g x v)
    have hg_cont_x : ∀ v, Continuous (fun x => g x v) := by
      intro v
      have hcont_f : Continuous (fun x => f x v) :=
        FlatTorus3.hDiff_continuous _ (hf_smooth_x v)
      have hcont_log : Continuous (fun x => Real.log (f x v)) :=
        hcont_f.log (fun x => ne_of_gt (hf_pos x v))
      have hcont_grad : ∀ i, Continuous (fun x =>
          FlatTorus3.gradX (fun y => f y v) x i) :=
        fun i => FlatTorus3.hDiff_continuous _ (FlatTorus3.hDiff_grad _ i (hf_smooth_x v))
      have hcont_dot : Continuous (fun x =>
          v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x) := by
        simp only [dotProduct, Fin.sum_univ_three]
        exact ((continuous_const.mul (hcont_grad 0)).add
          (continuous_const.mul (hcont_grad 1))).add (continuous_const.mul (hcont_grad 2))
      exact hcont_dot.mul hcont_log
    have hg_sm_v : ∀ x, StronglyMeasurable (fun v => g x v) := by
      intro x
      have hlog_sm : StronglyMeasurable (fun v => Real.log (f x v)) :=
        ((hf_smooth_v x).continuous.log (fun v => ne_of_gt (hf_pos x v))).stronglyMeasurable
      have hgrad_sm : ∀ i, StronglyMeasurable
          (fun v => FlatTorus3.gradX (fun y => f y v) x i) :=
        fun i => gradX_stronglyMeasurable_v f hf_smooth_v hf_smooth_x x i
      have hdot_sm : StronglyMeasurable
          (fun v => v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x) := by
        simp only [dotProduct, Fin.sum_univ_three]
        exact (((continuous_apply 0).stronglyMeasurable.mul (hgrad_sm 0)).add
          ((continuous_apply 1).stronglyMeasurable.mul (hgrad_sm 1))).add
          ((continuous_apply 2).stronglyMeasurable.mul (hgrad_sm 2))
      exact hdot_sm.mul hlog_sm
    exact (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      hg_cont_x hg_sm_v).aestronglyMeasurable
  · -- ∀ᵐ x, Integrable (fun v => g x v)
    exact Filter.Eventually.of_forall (fun x =>
      spatial_transport_integrable hf_pos hf_smooth_v hf_smooth_x hSchwartz ⟨C_log, K_log, hLB⟩ x)
  · -- Integrable (fun x => ∫ v, ‖g x v‖) on compact T³
    -- The velocity integral is uniformly bounded by C_total * M
    -- where M = ∫ v, 1/(1+‖v‖)^4, so the function is bounded on T³ (finite measure)
    apply (integrable_const (C_total * ∫ v : Fin 3 → ℝ, (1 + ‖v‖)⁻¹ ^ 4)).mono'
    · -- AEStronglyMeasurable (x ↦ ∫ v, ‖g x v‖) via dominated convergence → continuous
      have hg_cont : ∀ v, Continuous (fun x => g x v) := by
        intro v
        have hcont_f : Continuous (fun x => f x v) :=
          FlatTorus3.hDiff_continuous _ (hf_smooth_x v)
        have hcont_log : Continuous (fun x => Real.log (f x v)) :=
          hcont_f.log (fun x => ne_of_gt (hf_pos x v))
        have hcont_grad : ∀ i, Continuous (fun x =>
            FlatTorus3.gradX (fun y => f y v) x i) :=
          fun i => FlatTorus3.hDiff_continuous _ (FlatTorus3.hDiff_grad _ i (hf_smooth_x v))
        have hcont_dot : Continuous (fun x =>
            v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x) := by
          simp only [dotProduct, Fin.sum_univ_three]
          exact ((continuous_const.mul (hcont_grad 0)).add
            (continuous_const.mul (hcont_grad 1))).add (continuous_const.mul (hcont_grad 2))
        exact hcont_dot.mul hcont_log
      exact (continuous_of_dominated
        (fun x => (spatial_transport_integrable hf_pos hf_smooth_v hf_smooth_x hSchwartz
          ⟨C_log, K_log, hLB⟩ x).norm.aestronglyMeasurable)
        (fun x => Filter.Eventually.of_forall fun v => by
          show ‖‖g x v‖‖ ≤ C_total / (1 + ‖v‖) ^ 4
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Real.norm_eq_abs]
          exact h_bound x v)
        (inverse_poly_integrable C_total)
        (Filter.Eventually.of_forall fun v => (hg_cont v).norm)).aestronglyMeasurable
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

set_option maxHeartbeats 800000 in
/-- The parametric integral `x ↦ ∫ v, v ⬝ᵥ gradX(f)(x) * log(f(x,v))` is continuous
    on the torus. Proved via `continuous_of_dominated` using the uniform Schwartz+log bound
    from `spatial_transport_joint_integrable`. -/
lemma spatial_transport_continuous
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth_v : ∀ x, ContDiff ℝ ⊤ (f x))
    (hf_smooth_x : ∀ v, ContDiff ℝ ⊤ (periodicLift (fun x => f x v)))
    (hSchwartz : UniformSchwartzDecay f)
    (hLogBound : ∃ (C_log : ℝ) (K_log : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log) :
    Continuous (fun x => ∫ v, v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x *
      Real.log (f x v)) := by
  obtain ⟨C_log, K_log, hLB⟩ := hLogBound
  set g : Torus3 → (Fin 3 → ℝ) → ℝ :=
    fun x v => v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v) with hg_def
  -- Reuse the uniform bound from spatial_transport_joint_integrable
  have hLB' : ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ |C_log| * (1 + ‖v‖) ^ K_log :=
    fun x v => le_trans (hLB x v) (mul_le_mul_of_nonneg_right (le_abs_self _)
      (pow_nonneg (by linarith [norm_nonneg v]) _))
  obtain ⟨C0, hC0, hG0⟩ := hSchwartz.hGradDecay (K_log + 6) 0
  obtain ⟨C1, hC1, hG1⟩ := hSchwartz.hGradDecay (K_log + 6) 1
  obtain ⟨C2, hC2, hG2⟩ := hSchwartz.hGradDecay (K_log + 6) 2
  set C_total := (C0 + C1 + C2) * (|C_log| + 1) + 1
  have hC_total_pos : 0 < C_total := by positivity
  have h_bound : ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |g x v| ≤ C_total / (1 + ‖v‖) ^ 4 := by
    intro x v
    have h1v : (1 : ℝ) ≤ 1 + ‖v‖ := le_add_of_nonneg_right (norm_nonneg v)
    have h1v_nn : (0 : ℝ) ≤ 1 + ‖v‖ := le_trans zero_le_one h1v
    have hg_eq : g x v = ∑ i : Fin 3, v i *
        FlatTorus3.gradX (fun y => f y v) x i * Real.log (f x v) := by
      simp only [hg_def, dotProduct, Fin.sum_univ_three]; ring
    rw [hg_eq]
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
      _ ≤ C_total / (1 + ‖v‖) ^ 4 := by
          gcongr; linarith
  -- Apply continuous_of_dominated
  exact continuous_of_dominated
    (fun x => (spatial_transport_integrable hf_pos hf_smooth_v hf_smooth_x hSchwartz
      ⟨C_log, K_log, hLB⟩ x).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall fun v => by
      show ‖g x v‖ ≤ C_total / (1 + ‖v‖) ^ 4
      rw [Real.norm_eq_abs]; exact h_bound x v)
    (inverse_poly_integrable C_total)
    (Filter.Eventually.of_forall fun v => by
      show Continuous (fun x => g x v)
      have hcont_f : Continuous (fun x => f x v) :=
        FlatTorus3.hDiff_continuous _ (hf_smooth_x v)
      have hcont_log : Continuous (fun x => Real.log (f x v)) :=
        hcont_f.log (fun x => ne_of_gt (hf_pos x v))
      have hcont_grad : ∀ i, Continuous (fun x =>
          FlatTorus3.gradX (fun y => f y v) x i) :=
        fun i => FlatTorus3.hDiff_continuous _ (FlatTorus3.hDiff_grad _ i (hf_smooth_x v))
      have hcont_dot : Continuous (fun x =>
          v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x) := by
        simp only [dotProduct, Fin.sum_univ_three]
        exact ((continuous_const.mul (hcont_grad 0)).add
          (continuous_const.mul (hcont_grad 1))).add (continuous_const.mul (hcont_grad 2))
      exact hcont_dot.mul hcont_log)

end VML
