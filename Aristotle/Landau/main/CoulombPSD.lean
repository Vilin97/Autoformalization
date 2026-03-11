import Aristotle.Landau.main.CoulombPSDHelpers

/-!
# PSD Integrability and Fubini Symmetrization for Coulomb

Inner and outer integrability of the PSD integrand, and the Fubini
symmetrization needed for the H-theorem entropy dissipation identity.
Depends on continuity and pointwise bounds from CoulombPSDHelpers.
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

/-- PSD integrand is integrable for Coulomb kernel (inner integral, fixing v).
    Uses element-wise Coulomb matrix bound |A_{ij}| ≤ ‖z‖⁻¹ combined with
    polynomial score bound and Newtonian potential of Schwartz functions. -/
lemma psd_inner_integrable_coulomb
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 → ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    {Cg : ℝ} {Kg : ℕ}
    (hGrad : ∀ v i, |fderiv ℝ f v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * f v)
    (v : Fin 3 → ℝ) :
    Integrable (PSDIntegrand coulombKernel f v) := by
  -- Score bound: |∂_i log f(u)| ≤ Cg * (1+‖u‖)^Kg
  have h_score : ∀ u i, |vGrad (Real.log ∘ f) u i| ≤ Cg * (1 + ‖u‖) ^ Kg := by
    intro u i; simp only [vGrad]
    have hfu := hf_pos u
    rw [show Real.log ∘ f = fun u => Real.log (f u) from rfl,
        fderiv.log (hf_smooth.differentiable le_top).differentiableAt (ne_of_gt hfu)]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (inv_pos.mpr hfu)]
    rw [inv_mul_le_iff₀ hfu]; linarith [hGrad u i]
  -- Schwartz decay of f
  have hf_decay : ∀ N, ∃ C > 0, ∀ w, |f w| * (1 + ‖w‖) ^ N ≤ C := by
    intro N; obtain ⟨C, hC, hb⟩ := hf_schwartz N (by omega)
    exact ⟨C, hC, fun w => by simpa [iteratedFDeriv_zero_eq_comp] using hb w⟩
  -- Schwartz decay of (1+‖w‖)^{2Kg} * f(w)
  have hpf_decay : ∀ N, ∃ C > 0, ∀ w,
      |(1 + ‖w‖) ^ (2 * Kg) * f w| * (1 + ‖w‖) ^ N ≤ C := by
    intro N; obtain ⟨C, hC, hb⟩ := hf_decay (2 * Kg + N)
    refine ⟨C, hC, fun w => ?_⟩
    rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith [norm_nonneg w]) _)]
    calc (1 + ‖w‖) ^ (2 * Kg) * |f w| * (1 + ‖w‖) ^ N
        = |f w| * (1 + ‖w‖) ^ (2 * Kg + N) := by rw [pow_add]; ring
      _ ≤ C := hb w
  -- Newtonian potential integrability
  have h_int_f : Integrable (fun w => ‖v - w‖⁻¹ * f w) :=
    inv_norm_schwartz_integrable f hf_decay hf_smooth.continuous.aestronglyMeasurable v
  have h_int_pf : Integrable (fun w => ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w)) :=
    inv_norm_schwartz_integrable _ hpf_decay
      ((continuous_const.add continuous_norm).pow _ |>.mul
        hf_smooth.continuous).aestronglyMeasurable v
  -- AEStronglyMeasurable of PSD integrand
  have h_meas : AEStronglyMeasurable (PSDIntegrand coulombKernel f v) volume :=
    ((psd_continuous_coulomb f hf_pos hf_smooth).comp
      (continuous_const.prod_mk continuous_id')).aestronglyMeasurable
  -- Dominating constant
  set C_dom := 18 * Cg ^ 2 * f v
  -- Apply Integrable.mono' with dominating function
  refine ((h_int_f.const_mul ((1 + ‖v‖) ^ (2 * Kg))).add h_int_pf
    |>.const_mul C_dom).mono' h_meas (Filter.Eventually.of_forall fun w => ?_)
  -- Pointwise bound via extracted lemma
  rw [Real.norm_eq_abs]
  exact psd_pointwise_bound_coulomb f hf_pos h_score v w


/-- PSD integrand is integrable for Coulomb kernel (outer integral).
    Uses pointwise bound + Newtonian uniform bounds + Schwartz decay. -/
lemma psd_outer_integrable_coulomb
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 → ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    {Cg : ℝ} {Kg : ℕ}
    (hGrad : ∀ v i, |fderiv ℝ f v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * f v) :
    Integrable (fun v => ∫ w, PSDIntegrand coulombKernel f v w) := by
  -- Score bound
  have h_score : ∀ u i, |vGrad (Real.log ∘ f) u i| ≤ Cg * (1 + ‖u‖) ^ Kg := by
    intro u i; simp only [vGrad]
    have hfu := hf_pos u
    rw [show Real.log ∘ f = fun u => Real.log (f u) from rfl,
        fderiv.log (hf_smooth.differentiable le_top).differentiableAt (ne_of_gt hfu)]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (inv_pos.mpr hfu)]
    rw [inv_mul_le_iff₀ hfu]; linarith [hGrad u i]
  -- Schwartz decay
  have hf_decay : ∀ N, ∃ C > 0, ∀ w, |f w| * (1 + ‖w‖) ^ N ≤ C :=
    fun N => (hf_schwartz N (by omega)).imp fun C ⟨hC, hb⟩ =>
      ⟨hC, fun w => by simpa [iteratedFDeriv_zero_eq_comp] using hb w⟩
  have hpf_decay : ∀ N, ∃ C > 0, ∀ w,
      |(1 + ‖w‖) ^ (2 * Kg) * f w| * (1 + ‖w‖) ^ N ≤ C := by
    intro N; obtain ⟨C, hC, hb⟩ := hf_decay (2 * Kg + N)
    exact ⟨C, hC, fun w => by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith [norm_nonneg w]) _)]
      calc _ = |f w| * (1 + ‖w‖) ^ (2 * Kg + N) := by rw [pow_add]; ring
        _ ≤ C := hb w⟩
  -- Newtonian uniform bounds
  obtain ⟨M₁, hM₁, hM₁b⟩ := newtonian_schwartz_uniform_bound f hf_decay
    hf_smooth.continuous.aestronglyMeasurable
  obtain ⟨M₂, hM₂, hM₂b⟩ := newtonian_schwartz_uniform_bound
    (fun w => (1 + ‖w‖) ^ (2 * Kg) * f w) hpf_decay
    ((continuous_const.add continuous_norm).pow _ |>.mul hf_smooth.continuous).aestronglyMeasurable
  -- Integrability of Newtonian terms
  have h_int_f := fun v => inv_norm_schwartz_integrable f hf_decay
    hf_smooth.continuous.aestronglyMeasurable v
  have h_int_pf := fun v => inv_norm_schwartz_integrable
    (fun w => (1 + ‖w‖) ^ (2 * Kg) * f w) hpf_decay
    ((continuous_const.add continuous_norm).pow _ |>.mul
      hf_smooth.continuous).aestronglyMeasurable v
  -- Dominating function: C_out * (1+‖v‖)^{2Kg} * f(v), integrable by Schwartz decay
  set C_out := 18 * Cg ^ 2 * (M₁ + M₂) with hC_out_def
  have h_poly_int : Integrable (fun v => (1 + ‖v‖) ^ (2 * Kg) * f v) := by
    obtain ⟨C, hC_pos, hbound⟩ := hf_decay (2 * Kg + 4)
    apply (inverse_poly_integrable C).mono'
    · exact ((continuous_const.add continuous_norm).pow _ |>.mul
        hf_smooth.continuous).aestronglyMeasurable
    · filter_upwards with v
      simp only [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (pow_nonneg (by linarith [norm_nonneg v]) _),
        abs_of_pos (hf_pos v)]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ‖v‖) ^ 4)]
      have : (1 + ‖v‖) ^ (2 * Kg) * f v * (1 + ‖v‖) ^ 4 =
          |f v| * (1 + ‖v‖) ^ (2 * Kg + 4) := by
        rw [abs_of_pos (hf_pos v), pow_add]; ring
      linarith [hbound v]
  -- AEStronglyMeasurable of parametric integral
  have h_meas : AEStronglyMeasurable
      (fun v => ∫ w, PSDIntegrand coulombKernel f v w) volume :=
    (psd_continuous_coulomb f hf_pos hf_smooth).aestronglyMeasurable.integral_prod_right'
  -- Apply Integrable.mono'
  apply (h_poly_int.const_mul C_out).mono' h_meas
  filter_upwards with v
  rw [Real.norm_eq_abs]
  -- Dominating function for inner integral
  have hdom_w : Integrable (fun w =>
      18 * Cg ^ 2 * f v * ((1 + ‖v‖) ^ (2 * Kg) * (‖v - w‖⁻¹ * f w) +
                            ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w))) :=
    ((h_int_f v).const_mul ((1 + ‖v‖) ^ (2 * Kg))).add (h_int_pf v)
      |>.const_mul (18 * Cg ^ 2 * f v)
  calc |∫ w, PSDIntegrand coulombKernel f v w|
      ≤ ∫ w, |PSDIntegrand coulombKernel f v w| :=
        abs_integral_le_integral_abs _
    _ ≤ ∫ w, (18 * Cg ^ 2 * f v * ((1 + ‖v‖) ^ (2 * Kg) * (‖v - w‖⁻¹ * f w) +
                                     ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w))) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hdom_w
          (ae_of_all _ fun w => psd_pointwise_bound_coulomb f hf_pos h_score v w)
    _ = 18 * Cg ^ 2 * f v * ∫ w, ((1 + ‖v‖) ^ (2 * Kg) * (‖v - w‖⁻¹ * f w) +
                                    ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w)) :=
        integral_mul_left _ _
    _ = 18 * Cg ^ 2 * f v * ((1 + ‖v‖) ^ (2 * Kg) * ∫ w, ‖v - w‖⁻¹ * f w +
                              ∫ w, ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w)) := by
        congr 1
        rw [integral_add ((h_int_f v).const_mul _) (h_int_pf v), integral_mul_left]
    _ ≤ 18 * Cg ^ 2 * f v * ((1 + ‖v‖) ^ (2 * Kg) * M₁ + M₂) := by
        gcongr
        · calc ∫ w, ‖v - w‖⁻¹ * f w
              = ∫ w, ‖v - w‖⁻¹ * |f w| :=
                integral_congr_ae (ae_of_all _ fun w => by rw [abs_of_pos (hf_pos w)])
            _ ≤ M₁ := hM₁b v
        · calc ∫ w, ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w)
              = ∫ w, ‖v - w‖⁻¹ * |(1 + ‖w‖) ^ (2 * Kg) * f w| :=
                integral_congr_ae (ae_of_all _ fun w => by
                  rw [abs_of_nonneg (mul_nonneg (pow_nonneg (by linarith [norm_nonneg w]) _)
                    (le_of_lt (hf_pos w)))])
            _ ≤ M₂ := hM₂b v
    _ ≤ C_out * ((1 + ‖v‖) ^ (2 * Kg) * f v) := by
        have h1 : (1 : ℝ) ≤ (1 + ‖v‖) ^ (2 * Kg) :=
          one_le_pow_of_one_le (by linarith [norm_nonneg v]) _
        have h2 : M₂ ≤ (1 + ‖v‖) ^ (2 * Kg) * M₂ := le_mul_of_one_le_left (le_of_lt hM₂) h1
        simp only [C_out]
        calc 18 * Cg ^ 2 * f v * ((1 + ‖v‖) ^ (2 * Kg) * M₁ + M₂)
            ≤ 18 * Cg ^ 2 * f v * ((M₁ + M₂) * (1 + ‖v‖) ^ (2 * Kg)) := by
              gcongr; linarith
          _ = 18 * Cg ^ 2 * (M₁ + M₂) * ((1 + ‖v‖) ^ (2 * Kg) * f v) := by ring


/-- The Fubini integrand (score · flux) is jointly integrable on the product space
    for the Coulomb kernel. Uses `integrable_prod_iff` with:
    - Joint measurability from measurability of each factor
    - Inner integrability from `landau_flux_integrable_coulomb`
    - Norm integral bound from PSD pointwise bound + Newtonian uniform bounds -/
lemma fubini_double_integrable_coulomb
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 → ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    {Cg : ℝ} {Kg : ℕ}
    (hGrad : ∀ v i, |fderiv ℝ f v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * f v) :
    Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      dotProduct (vGrad (Real.log ∘ f) p.1)
        (mulVec (landauMatrix coulombKernel (p.1 - p.2))
          (f p.2 • vGrad f p.1 - f p.1 • vGrad f p.2))) := by
  -- Score bound
  have h_score : ∀ u i, |vGrad (Real.log ∘ f) u i| ≤ Cg * (1 + ‖u‖) ^ Kg := by
    intro u i; simp only [vGrad]
    have hfu := hf_pos u
    rw [show Real.log ∘ f = fun u => Real.log (f u) from rfl,
        fderiv.log (hf_smooth.differentiable le_top).differentiableAt (ne_of_gt hfu)]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (inv_pos.mpr hfu)]
    rw [inv_mul_le_iff₀ hfu]; linarith [hGrad u i]
  -- Schwartz decay
  have hf_decay : ∀ N, ∃ C > 0, ∀ w, |f w| * (1 + ‖w‖) ^ N ≤ C :=
    fun N => (hf_schwartz N (by omega)).imp fun C ⟨hC, hb⟩ =>
      ⟨hC, fun w => by simpa [iteratedFDeriv_zero_eq_comp] using hb w⟩
  have hpf_decay : ∀ N, ∃ C > 0, ∀ w,
      |(1 + ‖w‖) ^ (2 * Kg) * f w| * (1 + ‖w‖) ^ N ≤ C := by
    intro N; obtain ⟨C, hC, hb⟩ := hf_decay (2 * Kg + N)
    exact ⟨C, hC, fun w => by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith [norm_nonneg w]) _)]
      calc _ = |f w| * (1 + ‖w‖) ^ (2 * Kg + N) := by rw [pow_add]; ring
        _ ≤ C := hb w⟩
  -- Flux integrability
  have hFlux : ∀ v, Integrable (fun w => mulVec (landauMatrix coulombKernel (v - w))
      (f w • vGrad f v - f v • vGrad f w)) :=
    fun v => landau_flux_integrable_coulomb f hf_pos hf_smooth hf_schwartz v
  -- Newtonian uniform bounds
  obtain ⟨M₁, hM₁, hM₁b⟩ := newtonian_schwartz_uniform_bound f hf_decay
    hf_smooth.continuous.aestronglyMeasurable
  obtain ⟨M₂, hM₂, hM₂b⟩ := newtonian_schwartz_uniform_bound
    (fun w => (1 + ‖w‖) ^ (2 * Kg) * f w) hpf_decay
    ((continuous_const.add continuous_norm).pow _ |>.mul hf_smooth.continuous).aestronglyMeasurable
  -- Integrability of Newtonian terms
  have h_int_f := fun v => inv_norm_schwartz_integrable f hf_decay
    hf_smooth.continuous.aestronglyMeasurable v
  have h_int_pf := fun v => inv_norm_schwartz_integrable
    (fun w => (1 + ‖w‖) ^ (2 * Kg) * f w) hpf_decay
    ((continuous_const.add continuous_norm).pow _ |>.mul
      hf_smooth.continuous).aestronglyMeasurable v
  -- Cg ≥ 0
  have hCg_nn : 0 ≤ Cg := by
    by_contra h_neg; push_neg at h_neg
    have : Cg * (1 + ‖(0 : Fin 3 → ℝ)‖) ^ Kg * f 0 < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h_neg (by positivity)) (hf_pos 0)
    linarith [hGrad 0 0, abs_nonneg (fderiv ℝ f 0 (Pi.single 0 1))]
  -- The integrand as a function on product space
  set F : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ := fun p =>
    dotProduct (vGrad (Real.log ∘ f) p.1)
      (mulVec (landauMatrix coulombKernel (p.1 - p.2))
        (f p.2 • vGrad f p.1 - f p.1 • vGrad f p.2)) with hF_def
  -- Step 1: AEStronglyMeasurable on product space
  have h_meas : AEStronglyMeasurable F (volume.prod volume) := by
    -- F(v,w) = ∑_i score_i(v) * (∑_j A_{ij}(v-w) * flux_j(v,w))
    -- = ∑_i ∑_j score_i(v) * A_{ij}(v-w) * flux_j(v,w)
    show AEStronglyMeasurable (fun p => dotProduct (vGrad (Real.log ∘ f) p.1)
      (mulVec (landauMatrix coulombKernel (p.1 - p.2))
        (f p.2 • vGrad f p.1 - f p.1 • vGrad f p.2))) _
    simp only [dotProduct, mulVec]
    apply Finset.aestronglyMeasurable_sum
    intro i _
    apply AEStronglyMeasurable.mul
    · -- score_i(v) is measurable in p.1
      exact ((hf_smooth.continuous.log (fun v => ne_of_gt (hf_pos v))).fderiv le_top
        |>.clm_apply continuous_const).comp continuous_fst |>.aestronglyMeasurable
    · -- (∑_j A_{ij}(v-w) * flux_j(v,w)) is measurable on product
      apply Finset.aestronglyMeasurable_sum
      intro j _
      apply AEStronglyMeasurable.mul
      · -- A_{ij}(v-w) is measurable
        apply Measurable.aestronglyMeasurable
        simp only [landauMatrix, smul_apply, smul_eq_mul]
        apply Measurable.mul
        · apply ((Measurable.ite measurableSet_Iic measurable_const
            (measurable_id.pow measurable_const)) : Measurable coulombKernel).comp
          simp only [eucNorm, normSq, dotProduct]
          exact (continuous_sqrt.comp (continuous_finset_sum _ fun k _ =>
            ((continuous_apply k).comp (continuous_fst.sub continuous_snd)).mul
            ((continuous_apply k).comp (continuous_fst.sub continuous_snd)))).measurable
        · simp only [innerLandauMatrix, sub_apply, HSMul.hSMul, SMul.smul,
            one_apply, vecMulVec_apply]
          apply Continuous.measurable
          apply Continuous.sub
          · by_cases h : i = j
            · simp only [h, ↓reduceIte, normSq, dotProduct, mul_one]
              exact continuous_finset_sum _ fun k _ =>
                ((continuous_apply k).comp (continuous_fst.sub continuous_snd)).mul
                ((continuous_apply k).comp (continuous_fst.sub continuous_snd))
            · simp [h]; exact continuous_const
          · exact ((continuous_apply i).comp (continuous_fst.sub continuous_snd)).mul
                  ((continuous_apply j).comp (continuous_fst.sub continuous_snd))
      · -- flux_j(v,w) = f(w)*∂_jf(v) - f(v)*∂_jf(w) is measurable
        apply Continuous.aestronglyMeasurable
        apply Continuous.sub
        · exact (hf_smooth.continuous.comp continuous_snd).mul
            ((hf_smooth.continuous_fderiv le_top).comp continuous_fst |>.clm_apply continuous_const)
        · exact (hf_smooth.continuous.comp continuous_fst).mul
            ((hf_smooth.continuous_fderiv le_top).comp continuous_snd |>.clm_apply continuous_const)
  -- Step 2: Inner integrability (for a.e. v, w ↦ F(v,w) integrable)
  have h_inner : ∀ v, Integrable (fun w => F (v, w)) := by
    intro v
    -- F(v,w) = dotProduct(score(v), A(v-w) · flux(v,w))
    -- = ∑_i score_i(v) * (A(v-w) · flux(v,w))_i
    -- Each (A·flux)_i is integrable by landau_flux_integrable_coulomb
    simp only [F, dotProduct, Fin.sum_univ_three]
    exact ((integrable_pi_iff.mp (hFlux v) 0).const_mul _).add
      ((integrable_pi_iff.mp (hFlux v) 1).const_mul _) |>.add
      ((integrable_pi_iff.mp (hFlux v) 2).const_mul _)
  -- Step 3: ∫ ‖F(v,·)‖ is integrable in v
  -- We reuse the bound from psd_outer_integrable_coulomb style argument
  -- |F(v,w)| ≤ 3 * Cg * (1+‖v‖)^Kg * ‖v-w‖⁻¹ * (3*Cg*(1+‖v‖)^Kg*f(w) + ...)
  -- But more directly: |F(v,w)| = |score(v) · (A·flux)(v,w)|
  -- ≤ (∑_i |score_i(v)|) * max_i |(A·flux)_i(v,w)|
  -- The bound on (A·flux)_i follows from |A_{ij}| ≤ ‖v-w‖⁻¹
  -- Overall: |F(v,w)| ≤ 3*Cg*(1+‖v‖)^Kg * ‖v-w‖⁻¹ * (3*Cg*(1+‖v‖)^Kg*f(w) + 3*f(v)*...)
  -- Actually, let's use a cleaner approach: bound via the PSD-style bound
  have h_norm_int : Integrable (fun v => ∫ w, ‖F (v, w)‖) := by
    -- Pointwise bound: |F(v,w)| ≤ 3Cg(1+‖v‖)^Kg * ‖v-w‖⁻¹ * 3 *
    --   (f(w)*3Cg(1+‖v‖)^Kg + f(v)*3Cg(1+‖w‖)^Kg)
    -- which simplifies to 9Cg²(1+‖v‖)^{2Kg} * ‖v-w‖⁻¹ * f(w) +
    --   9Cg²(1+‖v‖)^Kg * f(v) * ‖v-w‖⁻¹ * (1+‖w‖)^Kg * ...
    -- This gets complicated. Let's just use that ∫‖F(v,w)‖ ≤ C * (1+‖v‖)^{2Kg} * f(v)
    -- and f(v)*(1+‖v‖)^{2Kg} is integrable by Schwartz decay
    -- Bound on ∫ ‖F(v,·)‖:
    -- |F(v,w)| = |∑_i score_i(v) * (A·flux)_i(v,w)|
    -- ≤ ∑_i |score_i(v)| * |(A·flux)_i(v,w)|
    -- ≤ ∑_i |score_i(v)| * (‖v-w‖⁻¹ * ∑_j |flux_j(v,w)|)
    -- ≤ (∑_i Cg(1+‖v‖)^Kg) * ‖v-w‖⁻¹ * ∑_j (f(w)*|∂_jf(v)| + f(v)*|∂_jf(w)|)
    -- = 3Cg(1+‖v‖)^Kg * ‖v-w‖⁻¹ * ∑_j (f(w)*|∂_jf(v)| + f(v)*|∂_jf(w)|)
    -- Integrate in w:
    -- ≤ 3Cg(1+‖v‖)^Kg * (∑_j |∂_jf(v)| * M₁ + f(v) * M_dj)
    -- ≤ 3Cg(1+‖v‖)^Kg * (3*Cg*(1+‖v‖)^Kg*f(v)*M₁ + f(v) * M_df)
    -- = f(v) * (9Cg²(1+‖v‖)^{2Kg}*M₁ + 3Cg(1+‖v‖)^Kg * M_df)
    -- ≤ C_out * (1+‖v‖)^{2Kg} * f(v)
    -- which is integrable by Schwartz decay
    -- Partial derivative Schwartz decay
    have hdg_decay : ∀ j : Fin 3, ∀ N, ∃ C > 0, ∀ w,
        |fderiv ℝ f w (Pi.single j 1)| * (1 + ‖w‖) ^ N ≤ C := by
      intro j N; obtain ⟨C, hC, hb⟩ := hf_schwartz N (by omega)
      refine ⟨C, hC, fun w => le_trans (mul_le_mul_of_nonneg_right ?_ (by positivity)) (hb w)⟩
      rw [← Real.norm_eq_abs]
      exact le_trans (le_trans (ContinuousLinearMap.le_opNorm _ _)
        (mul_le_of_le_one_right (norm_nonneg _) (by simp [Pi.norm_single])))
        (by rw [show (1:ℕ) = 0+1 from rfl, ← norm_iteratedFDeriv_fderiv,
                norm_iteratedFDeriv_zero])
    -- Newtonian bounds for partial derivatives
    have hMj : ∀ j, ∃ M > 0, ∀ v,
        ∫ w, ‖v - w‖⁻¹ * |fderiv ℝ f w (Pi.single j 1)| ≤ M :=
      fun j => newtonian_schwartz_uniform_bound _ (hdg_decay j)
        ((hf_smooth.continuous_fderiv le_top).clm_apply continuous_const).aestronglyMeasurable
    obtain ⟨Md₀, hMd₀, hMd₀b⟩ := hMj 0
    obtain ⟨Md₁, hMd₁, hMd₁b⟩ := hMj 1
    obtain ⟨Md₂, hMd₂, hMd₂b⟩ := hMj 2
    set M_df := Md₀ + Md₁ + Md₂
    -- Integrability helpers
    have h_f_abs : ∀ v, Integrable (fun w => ‖v - w‖⁻¹ * |f w|) := fun v =>
      (h_int_f v).norm.congr (Filter.Eventually.of_forall fun w => by
        rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), Real.norm_eq_abs])
    have h_dj_abs : ∀ j : Fin 3, ∀ v,
        Integrable (fun w => ‖v - w‖⁻¹ * |vGrad f w j|) := fun j v =>
      (inv_norm_schwartz_integrable _ (hdg_decay j)
        ((hf_smooth.continuous_fderiv le_top).clm_apply continuous_const).aestronglyMeasurable
        v).norm.congr (Filter.Eventually.of_forall fun w => by
        rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          Real.norm_eq_abs]; rfl)
    -- Dominating function
    set C_out := 9 * Cg ^ 2 * M₁ + 3 * Cg * M_df
    have h_poly_int : Integrable (fun v => (1 + ‖v‖) ^ (2 * Kg) * f v) := by
      obtain ⟨C, hC_pos, hbound⟩ := hf_decay (2 * Kg + 4)
      apply (inverse_poly_integrable C).mono'
      · exact ((continuous_const.add continuous_norm).pow _ |>.mul
          hf_smooth.continuous).aestronglyMeasurable
      · filter_upwards with v
        simp only [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (pow_nonneg (by linarith [norm_nonneg v]) _),
          abs_of_pos (hf_pos v)]
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ‖v‖) ^ 4)]
        have : (1 + ‖v‖) ^ (2 * Kg) * f v * (1 + ‖v‖) ^ 4 =
            |f v| * (1 + ‖v‖) ^ (2 * Kg + 4) := by
          rw [abs_of_pos (hf_pos v), pow_add]; ring
        linarith [hbound v]
    -- Measurability of norm integral
    have h_norm_meas : AEStronglyMeasurable (fun v => ∫ w, ‖F (v, w)‖) volume := by
      apply h_meas.norm.integral_prod_right'
    -- Pointwise bound on |F(v,w)|
    have h_pw_bound : ∀ v w, |F (v, w)| ≤
        3 * Cg * (1 + ‖v‖) ^ Kg * (‖v - w‖⁻¹ *
          (∑ j : Fin 3, (f w * |vGrad f v j| + f v * |vGrad f w j|))) := by
      intro v w
      simp only [F, dotProduct, mulVec]
      -- |∑_i score_i * ∑_j A_{ij} * flux_j| ≤ ∑_i |score_i| * |∑_j A_{ij} * flux_j|
      calc |∑ i : Fin 3, vGrad (Real.log ∘ f) v i *
              ∑ j : Fin 3, landauMatrix coulombKernel (v - w) i j *
                (f w • vGrad f v - f v • vGrad f w) j|
          ≤ ∑ i : Fin 3, |vGrad (Real.log ∘ f) v i| *
              |∑ j : Fin 3, landauMatrix coulombKernel (v - w) i j *
                (f w • vGrad f v - f v • vGrad f w) j| := by
            exact le_trans (Finset.abs_sum_le_sum_abs _ _)
              (Finset.sum_le_sum fun i _ => abs_mul _ _)
        _ ≤ ∑ i : Fin 3, Cg * (1 + ‖v‖) ^ Kg *
              (‖v - w‖⁻¹ * ∑ j : Fin 3, |(f w • vGrad f v - f v • vGrad f w) j|) := by
            apply Finset.sum_le_sum; intro i _
            apply mul_le_mul (h_score v i) _ (abs_nonneg _) (by positivity)
            by_cases hvw : v - w = 0
            · have : v = w := sub_eq_zero.mp hvw; subst this
              simp [mulVec, dotProduct, landauMatrix, innerLandauMatrix, normSq, vecMulVec,
                eucNorm, coulombKernel]
            · calc |∑ j, landauMatrix coulombKernel (v - w) i j *
                    (f w • vGrad f v - f v • vGrad f w) j|
                  ≤ ∑ j, |landauMatrix coulombKernel (v - w) i j *
                    (f w • vGrad f v - f v • vGrad f w) j| :=
                    Finset.abs_sum_le_sum_abs _ _
                _ ≤ ∑ j, ‖v - w‖⁻¹ * |(f w • vGrad f v - f v • vGrad f w) j| := by
                    apply Finset.sum_le_sum; intro j _
                    rw [abs_mul]
                    exact mul_le_mul_of_nonneg_right
                      (coulomb_landauMatrix_entry_le_pi _ _ _ hvw) (abs_nonneg _)
                _ = ‖v - w‖⁻¹ * ∑ j, |(f w • vGrad f v - f v • vGrad f w) j| :=
                    (Finset.mul_sum _ _ _).symm
        _ = 3 * (Cg * (1 + ‖v‖) ^ Kg) *
              (‖v - w‖⁻¹ * ∑ j, |(f w • vGrad f v - f v • vGrad f w) j|) := by
            simp [Fin.sum_univ_three]; ring
        _ ≤ 3 * Cg * (1 + ‖v‖) ^ Kg * (‖v - w‖⁻¹ *
              ∑ j, (f w * |vGrad f v j| + f v * |vGrad f w j|)) := by
            congr 1
            congr 1
            ring
            congr 1
            apply Finset.sum_le_sum; intro j _
            simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
            have := norm_sub_le (f w * vGrad f v j) (f v * vGrad f w j)
            rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_mul, abs_mul, abs_of_pos (hf_pos w), abs_of_pos (hf_pos v)] at this
            exact this
    -- Bound on ∫_w |F(v,w)|
    have h_int_bound : ∀ v, ∫ w, ‖F (v, w)‖ ≤
        C_out * ((1 + ‖v‖) ^ (2 * Kg) * f v) := by
      intro v
      calc ∫ w, ‖F (v, w)‖
          = ∫ w, |F (v, w)| := integral_congr_ae (ae_of_all _ fun w => Real.norm_eq_abs _)
        _ ≤ ∫ w, 3 * Cg * (1 + ‖v‖) ^ Kg * (‖v - w‖⁻¹ *
              ∑ j : Fin 3, (f w * |vGrad f v j| + f v * |vGrad f w j|)) := by
            apply integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
            · -- Integrability of the bound
              apply Integrable.const_mul
              simp_rw [Finset.mul_sum]
              refine (integrable_finset_sum _ fun j _ => ?_).const_mul _
              simp_rw [mul_add, mul_comm (‖_ - _‖⁻¹)]
              exact ((h_f_abs v).mul_const _).add ((h_dj_abs j v).const_mul _)
            · exact ae_of_all _ (h_pw_bound v)
        _ = 3 * Cg * (1 + ‖v‖) ^ Kg * ∫ w, ‖v - w‖⁻¹ *
              ∑ j : Fin 3, (f w * |vGrad f v j| + f v * |vGrad f w j|) := by
            rw [integral_mul_left]
        _ ≤ 3 * Cg * (1 + ‖v‖) ^ Kg *
              ((∑ j : Fin 3, |vGrad f v j|) * M₁ + f v * M_df) := by
            gcongr
            -- Expand ∑_j and integrate
            simp_rw [Finset.mul_sum]
            rw [integral_finset_sum _ (fun j _ => by
              simp_rw [mul_add, mul_comm (‖_ - _‖⁻¹)]
              exact ((h_f_abs v).mul_const _).add ((h_dj_abs j v).const_mul _))]
            simp_rw [mul_add, mul_comm (‖_ - _‖⁻¹)]
            rw [Finset.sum_add_distrib]
            apply add_le_add
            · -- ∑_j ∫ |vGrad f v j| * ‖v-w‖⁻¹ * f(w) ≤ (∑|∂_j f(v)|) * M₁
              calc ∑ j : Fin 3, ∫ w, |vGrad f v j| * (‖v - w‖⁻¹ * |f w|)
                  = ∑ j : Fin 3, |vGrad f v j| * ∫ w, ‖v - w‖⁻¹ * |f w| := by
                    congr 1
                    ext j
                    rw [integral_mul_left]
                _ ≤ ∑ j : Fin 3, |vGrad f v j| * M₁ :=
                    Finset.sum_le_sum fun j _ =>
                      mul_le_mul_of_nonneg_left (hM₁b v) (abs_nonneg _)
                _ = (∑ j : Fin 3, |vGrad f v j|) * M₁ := Finset.sum_mul _ _ _
            · -- ∑_j ∫ f(v) * (‖v-w‖⁻¹ * |∂_j f(w)|) ≤ f(v) * M_df
              calc ∑ j : Fin 3, ∫ w, f v * (‖v - w‖⁻¹ * |vGrad f w j|)
                  = f v * ∑ j : Fin 3, ∫ w, ‖v - w‖⁻¹ * |vGrad f w j| := by
                    simp_rw [integral_mul_left]; rw [← Finset.mul_sum]
                _ ≤ f v * M_df := by
                    gcongr
                    simp only [Fin.sum_univ_three, M_df]
                    linarith [hMd₀b v, hMd₁b v, hMd₂b v]
        _ ≤ 3 * Cg * (1 + ‖v‖) ^ Kg *
              (3 * (Cg * (1 + ‖v‖) ^ Kg * f v) * M₁ + f v * M_df) := by
            gcongr
            calc (∑ j : Fin 3, |vGrad f v j|) * M₁
                ≤ 3 * (Cg * (1 + ‖v‖) ^ Kg * f v) * M₁ := by
                  gcongr
                  simp only [Fin.sum_univ_three]
                  linarith [hGrad v 0, hGrad v 1, hGrad v 2]
        _ = C_out * ((1 + ‖v‖) ^ (2 * Kg) * f v) := by
            simp only [C_out]
            have h1 : (1 : ℝ) ≤ (1 + ‖v‖) ^ Kg :=
              one_le_pow_of_one_le (by linarith [norm_nonneg v]) _
            rw [show 2 * Kg = Kg + Kg from by omega, pow_add]
            nlinarith [hf_pos v]
    -- Apply integrable_prod_iff
    rw [show volume = (volume : Measure (Fin 3 → ℝ)).prod (volume : Measure (Fin 3 → ℝ)) from
      (MeasureTheory.Measure.pi_pi_eq_prod (fun _ : Fin 3 => volume) (fun _ : Fin 3 => volume)
        |>.symm ▸ by rfl)]
    rw [show volume = (volume : Measure (Fin 3 → ℝ)).prod (volume : Measure (Fin 3 → ℝ)) from
      (MeasureTheory.Measure.pi_pi_eq_prod (fun _ : Fin 3 => volume) (fun _ : Fin 3 => volume)
        |>.symm ▸ by rfl)] at h_meas
    refine (integrable_prod_iff h_meas).mpr ⟨ae_of_all _ h_inner, ?_⟩
    exact (h_poly_int.const_mul C_out).mono' h_norm_meas (ae_of_all _ fun v => by
      exact le_trans (h_int_bound v) (le_of_eq rfl))

end VML
