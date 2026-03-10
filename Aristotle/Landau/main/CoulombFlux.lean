import Aristotle.Landau.main.NewtonianPotential

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

-- ============================================================================
-- Inline definitions for standalone Aristotle proofs (all equal to VML defs by rfl)
-- ============================================================================
def normSq' (z : Fin 3 → ℝ) : ℝ := dotProduct z z
def eucNorm' (z : Fin 3 → ℝ) : ℝ := Real.sqrt (normSq' z)
def innerLandauMatrix' (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  normSq' z • (1 : Matrix (Fin 3) (Fin 3) ℝ) - vecMulVec z z
def coulombKernel' (r : ℝ) : ℝ := if r ≤ 0 then 1 else r ^ (-3 : ℝ)
def landauMatrix' (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  coulombKernel' (eucNorm' z) • innerLandauMatrix' z
def vGrad' (f : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => fderiv ℝ f v (Pi.single i 1)

-- Bridging lemmas: primed defs equal VML namespace defs (by definitional equality)
lemma normSq'_eq : normSq' = normSq := rfl
lemma eucNorm'_eq : eucNorm' = eucNorm := rfl
lemma innerLandauMatrix'_eq : innerLandauMatrix' = innerLandauMatrix := rfl
lemma coulombKernel'_eq : coulombKernel' = coulombKernel := rfl
lemma landauMatrix'_eq : landauMatrix' = landauMatrix coulombKernel := rfl
lemma vGrad'_eq : vGrad' = vGrad := rfl

-- ============================================================================
-- Landau flux integrability for Coulomb kernel (proved by Aristotle, job aabe3f3d)
-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-- ============================================================================

/-- The Landau collision flux is integrable for the Coulomb kernel. -/
lemma landau_flux_integrable_coulomb
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ (v : Fin 3 → ℝ),
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (v : Fin 3 → ℝ) :
    Integrable (fun w =>
      mulVec (landauMatrix coulombKernel (v - w))
        (f w • vGrad f v - f v • vGrad f w)) := by
  -- Bridge: landauMatrix coulombKernel = landauMatrix' and vGrad = vGrad' by rfl
  show Integrable (fun w =>
      mulVec (landauMatrix' (v - w))
        (f w • vGrad' f v - f v • vGrad' f w))
  -- Each component (i,j) is integrable via ‖v-w‖⁻¹ × Schwartz bound
  have h_comp : ∀ i j : Fin 3, Integrable (fun w =>
      (landauMatrix' (v - w)) i j *
      (f w • vGrad' f v - f v • vGrad' f w) j) := by
    have h_inv : ∀ i j : Fin 3, Integrable (fun w =>
        ‖v - w‖⁻¹ * (f w • vGrad' f v - f v • vGrad' f w) j) := by
      intro i j
      have h_int : Integrable (fun w => ‖v - w‖⁻¹ * f w) ∧
          Integrable (fun w => ‖v - w‖⁻¹ * (vGrad' f w) j) := by
        constructor
        · apply inv_norm_schwartz_integrable
          · intro N; specialize hf_schwartz N 0; aesop
          · exact hf_smooth.continuous.aestronglyMeasurable
        · apply inv_norm_schwartz_integrable
          · intro N
            obtain ⟨C, hC_pos, hC⟩ := hf_schwartz N 1
            use C, hC_pos; intro w
            have h_deriv_bound : |vGrad' f w j| ≤ ‖iteratedFDeriv ℝ 1 f w‖ := by
              have : |fderiv ℝ f w (Pi.single j 1)| ≤ ‖fderiv ℝ f w‖ := by
                simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ f w) (Pi.single j 1))
                  |> le_trans <| mul_le_of_le_one_right (norm_nonneg _) <|
                  by simp +decide [Pi.norm_single]
              generalize_proofs at *
              erw [iteratedFDeriv_succ_eq_comp_left]; norm_num [fderiv_deriv]
              erw [iteratedFDeriv_zero_eq_comp]; norm_num [fderiv_deriv]
              erw [fderiv_comp] <;> norm_num [hf_smooth.contDiffAt.differentiableAt]
              · erw [LinearIsometryEquiv.fderiv]; norm_num [fderiv_deriv]
                erw [ContinuousLinearMap.norm_def]; norm_num [ContinuousLinearMap.opNorm]
                ring; aesop
              · exact (LinearIsometryEquiv.differentiable _) _
            exact le_trans (mul_le_mul_of_nonneg_right h_deriv_bound (by positivity)) (hC w)
          · exact ((hf_smooth.continuous_fderiv le_top).eval_const (Pi.single j 1)).aestronglyMeasurable
      convert h_int.1.mul_const ((vGrad' f v) j) |>.sub (h_int.2.const_mul (f v)) using 2
      simp [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    intro i j
    refine (h_inv i j).norm.mono' ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ ?_
      · refine Measurable.aestronglyMeasurable ?_
        refine Measurable.mul ?_ ?_
        · refine Measurable.ite ?_ ?_ ?_ <;> norm_num [eucNorm', coulombKernel']
          · exact measurableSet_Iic.mem.comp (Real.continuous_sqrt.measurable.comp
              (show Measurable fun a : Fin 3 → ℝ => normSq' (v - a) from
                Continuous.measurable (Continuous.dotProduct
                  (continuous_const.sub continuous_id') (continuous_const.sub continuous_id'))))
          · exact Measurable.pow_const (Measurable.sqrt <| Continuous.measurable <|
              Continuous.dotProduct (continuous_const.sub continuous_id')
                (continuous_const.sub continuous_id')) _
        · unfold innerLandauMatrix'
          simp +decide [normSq', Matrix.vecMulVec]
          fun_prop (disch := norm_num)
      · exact AEStronglyMeasurable.sub
          (Continuous.aestronglyMeasurable (hf_smooth.continuous.mul continuous_const))
          (AEStronglyMeasurable.mul aestronglyMeasurable_const
            ((hf_smooth.continuous_fderiv le_top).eval_const (Pi.single j 1)).aestronglyMeasurable)
    · filter_upwards [] with w
      by_cases hw : v - w = 0 <;> simp_all +decide
      · simp_all +decide [sub_eq_zero, landauMatrix']
      · exact mul_le_mul_of_nonneg_right
          (coulomb_landauMatrix_entry_le_pi _ _ _ hw) (abs_nonneg _)
  exact integrable_pi_iff.mpr fun i => by
    simp only [mulVec, dotProduct]
    exact integrable_finset_sum Finset.univ fun j _ => by
      convert h_comp i j using 2 with w

-- ============================================================================
-- Flux × log(f) integrability for Coulomb kernel
-- ============================================================================

/-- Schwartz decay of partial derivatives: |∂_j f(x,w)| * (1+‖w‖)^N ≤ C.
    Follows from ‖iteratedFDeriv 1 f w‖ bounds and |∂_jf| ≤ ‖fderiv f w‖ ≤ ‖iteratedFDeriv 1 f w‖. -/
lemma schwartz_partial_decay
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hSchwartz : UniformSchwartzDecay f) (x : Torus3) (j : Fin 3) :
    ∀ N : ℕ, ∃ C > 0, ∀ w : Fin 3 → ℝ,
      |fderiv ℝ (f x) w (Pi.single j 1)| * (1 + ‖w‖) ^ N ≤ C := by
  intro N
  obtain ⟨C, hC_pos, hC⟩ := hSchwartz.hDecay N 1
  refine ⟨C, hC_pos, fun w => ?_⟩
  have h1 : |fderiv ℝ (f x) w (Pi.single j 1)| ≤ ‖fderiv ℝ (f x) w‖ := by
    rw [← Real.norm_eq_abs]
    exact le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_of_le_one_right (norm_nonneg _) (by simp +decide [Pi.norm_single]))
  have h2 : ‖fderiv ℝ (f x) w‖ = ‖iteratedFDeriv ℝ 1 (f x) w‖ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, ← norm_iteratedFDeriv_fderiv,
      norm_iteratedFDeriv_zero]
  rw [h2] at h1
  exact le_trans (mul_le_mul_of_nonneg_right h1 (by positivity)) (hC x w)

set_option maxHeartbeats 3200000 in
/-- The Landau flux component is AEStronglyMeasurable as a parametric integral.
    Uses joint measurability on the product space + integral_prod_right'. -/
lemma flux_component_aestronglyMeasurable
    (φ : (Fin 3 → ℝ) → ℝ)
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    (hFlux : ∀ v, Integrable (fun w => mulVec (landauMatrix coulombKernel (v - w))
      (φ w • vGrad φ v - φ v • vGrad φ w)))
    (i : Fin 3) :
    AEStronglyMeasurable (fun v =>
      (∫ w, mulVec (landauMatrix coulombKernel (v - w))
        (φ w • vGrad φ v - φ v • vGrad φ w)) i) volume := by
  have heval2 : (fun v => (∫ w, mulVec (landauMatrix coulombKernel (v - w))
      (φ w • vGrad φ v - φ v • vGrad φ w)) i) =
    (fun v => ∫ w, (mulVec (landauMatrix coulombKernel (v - w))
      (φ w • vGrad φ v - φ v • vGrad φ w)) i) :=
    funext fun v => eval_integral (hFlux v).eval i
  rw [heval2]
  let g : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ :=
    fun p => (mulVec (landauMatrix coulombKernel (p.1 - p.2))
      (φ p.2 • vGrad φ p.1 - φ p.1 • vGrad φ p.2)) i
  show AEStronglyMeasurable (fun v => ∫ w, g (v, w)) volume
  apply AEStronglyMeasurable.integral_prod_right'
  apply Measurable.aestronglyMeasurable
  show Measurable g
  simp only [g, mulVec, dotProduct]
  apply Finset.measurable_sum
  intro j _
  apply Measurable.mul
  · -- landauMatrix coulombKernel (p.1-p.2) i j is measurable
    show Measurable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      landauMatrix coulombKernel (p.1 - p.2) i j)
    simp only [landauMatrix, smul_apply, smul_eq_mul]
    apply Measurable.mul
    · -- coulombKernel (eucNorm (p.1-p.2)) is measurable
      apply ((Measurable.ite measurableSet_Iic measurable_const
        (measurable_id.pow measurable_const)) : Measurable coulombKernel).comp
      simp only [eucNorm, normSq, dotProduct]
      exact (continuous_sqrt.comp (continuous_finset_sum _ fun k _ =>
        ((continuous_apply k).comp (continuous_fst.sub continuous_snd)).mul
        ((continuous_apply k).comp (continuous_fst.sub continuous_snd)))).measurable
    · -- innerLandauMatrix (p.1-p.2) i j is continuous
      simp only [innerLandauMatrix, sub_apply, HSMul.hSMul, SMul.smul,
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
  · -- The vector part is continuous
    have hf_cont := hφ_smooth.continuous
    have hdf_cont := hφ_smooth.continuous_fderiv le_top
    apply Continuous.measurable
    apply Continuous.sub
    · exact (hf_cont.comp continuous_snd).mul
        ((hdf_cont.comp continuous_fst).clm_apply continuous_const)
    · exact (hf_cont.comp continuous_fst).mul
        ((hdf_cont.comp continuous_snd).clm_apply continuous_const)

set_option maxHeartbeats 1600000 in
/-- The Landau flux × log(f) is integrable for the Coulomb kernel.
    Uses the uniform Newtonian bound to control the flux pointwise. -/
lemma flux_times_log_integrable_coulomb
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth_v : ∀ x, ContDiff ℝ ⊤ (f x))
    (hSchwartz : UniformSchwartzDecay f)
    (hLogBound : ∃ (C_log : ℝ) (K_log : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log)
    (x : Torus3) (i : Fin 3) :
    Integrable (fun v =>
      (∫ w, mulVec (landauMatrix coulombKernel (v - w))
        (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) i *
        (Real.log ∘ f x) v) := by
  obtain ⟨C_log, K_log, hLB⟩ := hLogBound
  -- Schwartz decay for f(x) and ∂_j(f(x))
  have hf_decay : ∀ N : ℕ, ∃ C > 0, ∀ w, |f x w| * (1 + ‖w‖) ^ N ≤ C := by
    intro N; obtain ⟨C, hC, hb⟩ := hSchwartz.hDecay N 0
    exact ⟨C, hC, fun w => by simpa using hb x w⟩
  have hdf_decay : ∀ j : Fin 3, ∀ N : ℕ, ∃ C > 0, ∀ w,
      |fderiv ℝ (f x) w (Pi.single j 1)| * (1 + ‖w‖) ^ N ≤ C :=
    fun j N => schwartz_partial_decay hSchwartz x j N
  -- Uniform Newtonian bounds
  obtain ⟨M₀, hM₀, hM₀_bound⟩ := newtonian_schwartz_uniform_bound (fun w => f x w)
    (fun N => by obtain ⟨C, hC, hb⟩ := hf_decay N; exact ⟨C, hC, fun w => by
      show |(fun w => f x w) w| * _ ≤ C; exact hb w⟩)
    (hf_smooth_v x).continuous.aestronglyMeasurable
  have hMj : ∀ j : Fin 3, ∃ M > 0, ∀ v,
      ∫ w, ‖v - w‖⁻¹ * |fderiv ℝ (f x) w (Pi.single j 1)| ≤ M := by
    intro j
    exact newtonian_schwartz_uniform_bound _ (hdf_decay j)
      ((hf_smooth_v x).continuous_fderiv le_top |>.eval_const (Pi.single j 1)).aestronglyMeasurable
  obtain ⟨M₁, hM₁, hM₁b⟩ := hMj 0
  obtain ⟨M₂, hM₂, hM₂b⟩ := hMj 1
  obtain ⟨M₃, hM₃, hM₃b⟩ := hMj 2
  set M_df := M₁ + M₂ + M₃
  -- Dominating function: C_bound / (1+‖v‖)^4
  -- |flux_i(v)| ≤ M₀ * ∑|∂_jf(v)| + M_df * f(v)
  -- |flux_i(v) * log(f(v))| ≤ (M₀ * ∑|∂_jf(v)| + M_df * f(v)) * C_log * (1+‖v‖)^K
  -- Each term like |∂_jf(v)| * (1+‖v‖)^K ≤ C_{j,K+4}/(1+‖v‖)^4
  obtain ⟨C_f, hC_f, hC_f_bound⟩ := hSchwartz.hDecay (K_log + 4) 0
  obtain ⟨C_df, hC_df, hC_df_bound⟩ := hSchwartz.hDecay (K_log + 4) 1
  set C_bound := (M₀ * 3 * C_df + M_df * C_f) * C_log + 1
  -- Flux integrability for eval_integral
  have hf_schwartz_x : ∀ N k, ∃ C > 0, ∀ v,
      ‖iteratedFDeriv ℝ k (f x) v‖ * (1 + ‖v‖) ^ N ≤ C :=
    fun N k => hSchwartz.hDecay N k |>.imp fun C hC => ⟨hC.1, fun v => hC.2 x v⟩
  have hFlux : ∀ v, Integrable (fun w => mulVec (landauMatrix coulombKernel (v - w))
      (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) :=
    fun v => landau_flux_integrable_coulomb (f x) (fun v => hf_pos x v)
      (hf_smooth_v x) hf_schwartz_x v
  -- Pointwise flux bound (proved separately)
  have h_flux_bound : ∀ v, |(∫ w, mulVec (landauMatrix coulombKernel (v - w))
      (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) i| ≤
      M₀ * (3 * ‖iteratedFDeriv ℝ 1 (f x) v‖) +
      M_df * ‖iteratedFDeriv ℝ 0 (f x) v‖ := by
    intro v
    -- Step 1: pull component i out of the integral
    rw [eval_integral (fun j => (hFlux v).eval j)]
    -- Step 2: pointwise bound on |(mulVec A u) i|
    set u := fun w => f x w • vGrad (f x) v - f x v • vGrad (f x) w with hu_def
    -- Key: (mulVec A u) i = ∑ j, A i j * u j, each |A i j| ≤ ‖v-w‖⁻¹
    have h_pw : ∀ w, |(landauMatrix coulombKernel (v - w) *ᵥ (u w)) i| ≤
        ‖v - w‖⁻¹ * ∑ j : Fin 3, |u w j| := by
      intro w
      by_cases hvw : v - w = 0
      · have : v = w := sub_eq_zero.mp hvw
        subst this; simp [mulVec, dotProduct, landauMatrix, innerLandauMatrix,
          normSq, vecMulVec, eucNorm, coulombKernel]
      · simp only [mulVec, dotProduct]
        calc |∑ j : Fin 3, landauMatrix coulombKernel (v - w) i j * u w j|
            ≤ ∑ j : Fin 3, |landauMatrix coulombKernel (v - w) i j * u w j| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j : Fin 3, |landauMatrix coulombKernel (v - w) i j| * |u w j| := by
              congr 1; ext j; exact abs_mul _ _
          _ ≤ ∑ j : Fin 3, ‖v - w‖⁻¹ * |u w j| :=
              Finset.sum_le_sum fun j _ =>
                mul_le_mul_of_nonneg_right (coulomb_landauMatrix_entry_le_pi _ _ _ hvw)
                  (abs_nonneg _)
          _ = ‖v - w‖⁻¹ * ∑ j : Fin 3, |u w j| := (Finset.mul_sum _ _ _).symm
    -- Step 3: |∫| ≤ ∫|·| ≤ ∫ bound
    calc |∫ w, (landauMatrix coulombKernel (v - w) *ᵥ (u w)) i|
        ≤ ∫ w, |(landauMatrix coulombKernel (v - w) *ᵥ (u w)) i| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ w, ‖v - w‖⁻¹ * ∑ j : Fin 3, |u w j| :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => abs_nonneg _)
            (by -- Integrable (fun w => ‖v - w‖⁻¹ * ∑ j, |u w j|)
              simp_rw [Finset.mul_sum]
              refine integrable_finset_sum _ fun j _ => ?_
              have h_uj_int : Integrable (fun w => ‖v - w‖⁻¹ * (u w j)) := by
                have h_f := inv_norm_schwartz_integrable (f x) hf_decay
                  (hf_smooth_v x).continuous.aestronglyMeasurable v
                have h_dj := inv_norm_schwartz_integrable
                  (fun w => fderiv ℝ (f x) w (Pi.single j 1)) (hdf_decay j)
                  (((hf_smooth_v x).continuous_fderiv le_top).clm_apply
                    continuous_const).aestronglyMeasurable v
                convert h_f.mul_const (vGrad (f x) v j) |>.sub
                  (h_dj.const_mul (f x v)) using 1
                ext w; simp only [hu_def, vGrad, Pi.smul_apply, Pi.sub_apply,
                  smul_eq_mul, mul_assoc, mul_comm (‖v - w‖⁻¹)]
                ring
              exact h_uj_int.norm.congr (Filter.Eventually.of_forall fun w => by
                show ‖‖v - w‖⁻¹ * u w j‖ = ‖v - w‖⁻¹ * |u w j|
                rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
                  Real.norm_eq_abs]))
            (Filter.Eventually.of_forall h_pw)
      _ ≤ M₀ * (3 * ‖iteratedFDeriv ℝ 1 (f x) v‖) +
          M_df * ‖iteratedFDeriv ℝ 0 (f x) v‖ := by
          -- Integrability helpers
          have h_f_abs : Integrable (fun w => ‖v - w‖⁻¹ * |f x w|) :=
            (inv_norm_schwartz_integrable (f x) hf_decay
              (hf_smooth_v x).continuous.aestronglyMeasurable v).norm.congr
              (Filter.Eventually.of_forall fun w => by
                show ‖‖v - w‖⁻¹ * f x w‖ = ‖v - w‖⁻¹ * |f x w|
                rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
                  Real.norm_eq_abs])
          have h_dj_abs : ∀ j : Fin 3,
              Integrable (fun w => ‖v - w‖⁻¹ * |vGrad (f x) w j|) := by
            intro j
            exact (inv_norm_schwartz_integrable
              (fun w => fderiv ℝ (f x) w (Pi.single j 1)) (hdf_decay j)
              (((hf_smooth_v x).continuous_fderiv le_top).clm_apply
                continuous_const).aestronglyMeasurable v).norm.congr
              (Filter.Eventually.of_forall fun w => by
                show ‖‖v - w‖⁻¹ * fderiv ℝ (f x) w (Pi.single j 1)‖ =
                  ‖v - w‖⁻¹ * |vGrad (f x) w j|
                rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
                  Real.norm_eq_abs]; rfl)
          -- Triangle inequality: |u w j| ≤ |f w|*|∇v j| + |f v|*|∇w j|
          have h_tri : ∀ w j, |u w j| ≤
              |f x w| * |vGrad (f x) v j| + |f x v| * |vGrad (f x) w j| := by
            intro w j
            simp only [hu_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
            have := norm_sub_le (f x w * vGrad (f x) v j) (f x v * vGrad (f x) w j)
            rwa [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul] at this
          -- Sum triangle: ∑|u j| ≤ |f w| * S_v + |f v| * S_w
          have h_sum_tri : ∀ w, ∑ j : Fin 3, |u w j| ≤
              |f x w| * ∑ j : Fin 3, |vGrad (f x) v j| +
              |f x v| * ∑ j : Fin 3, |vGrad (f x) w j| := by
            intro w
            calc ∑ j : Fin 3, |u w j|
                ≤ ∑ j, (|f x w| * |vGrad (f x) v j| + |f x v| * |vGrad (f x) w j|) :=
                  Finset.sum_le_sum fun j _ => h_tri w j
              _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          -- vGrad bound: |vGrad v j| ≤ ‖iteratedFDeriv 1 f v‖
          have hvg : ∀ j : Fin 3, |vGrad (f x) v j| ≤
              ‖iteratedFDeriv ℝ 1 (f x) v‖ := by
            intro j; simp only [vGrad]
            have h1 : ‖(Pi.single j (1:ℝ) : Fin 3 → ℝ)‖ ≤ 1 := by
              rw [Pi.norm_single, norm_one]
            calc |fderiv ℝ (f x) v (Pi.single j 1)|
                = ‖fderiv ℝ (f x) v (Pi.single j 1)‖ := (Real.norm_eq_abs _).symm
              _ ≤ ‖fderiv ℝ (f x) v‖ * ‖(Pi.single j (1:ℝ) : Fin 3 → ℝ)‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ ≤ ‖fderiv ℝ (f x) v‖ * 1 := by gcongr
              _ = ‖fderiv ℝ (f x) v‖ := mul_one _
              _ = ‖iteratedFDeriv ℝ 1 (f x) v‖ := by
                  rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0)]; simp
          -- |f v| = ‖iteratedFDeriv 0 f v‖
          have hf0 : |f x v| = ‖iteratedFDeriv ℝ 0 (f x) v‖ := by
            rw [iteratedFDeriv_zero_eq_comp]; simp [Real.norm_eq_abs]
          -- Main bound via integral monotonicity + linearity
          -- Step 1: pointwise bound
          have h_pw2 : ∀ w, ‖v - w‖⁻¹ * ∑ j : Fin 3, |u w j| ≤
              (∑ j : Fin 3, |vGrad (f x) v j|) * (‖v - w‖⁻¹ * |f x w|) +
              |f x v| * ∑ j : Fin 3, (‖v - w‖⁻¹ * |vGrad (f x) w j|) := by
            intro w
            calc ‖v - w‖⁻¹ * ∑ j, |u w j|
                ≤ ‖v - w‖⁻¹ * (|f x w| * ∑ j, |vGrad (f x) v j| +
                    |f x v| * ∑ j, |vGrad (f x) w j|) :=
                  mul_le_mul_of_nonneg_left (h_sum_tri w) (inv_nonneg.mpr (norm_nonneg _))
              _ = _ := by simp only [← Finset.mul_sum]; ring
          -- Step 2: integrate
          calc ∫ w, ‖v - w‖⁻¹ * ∑ j : Fin 3, |u w j|
              ≤ ∫ w, ((∑ j, |vGrad (f x) v j|) * (‖v - w‖⁻¹ * |f x w|) +
                  |f x v| * ∑ j, (‖v - w‖⁻¹ * |vGrad (f x) w j|)) :=
                integral_mono_of_nonneg
                  (Filter.Eventually.of_forall fun w => mul_nonneg
                    (inv_nonneg.mpr (norm_nonneg _))
                    (Finset.sum_nonneg fun j _ => abs_nonneg _))
                  ((h_f_abs.const_mul _).add
                    ((integrable_finset_sum _ fun j _ => h_dj_abs j).const_mul _))
                  (Filter.Eventually.of_forall h_pw2)
            _ ≤ (∑ j, |vGrad (f x) v j|) * M₀ +
                |f x v| * (M₁ + M₂ + M₃) := by
                rw [integral_add (h_f_abs.const_mul _)
                  ((integrable_finset_sum _ fun j _ => h_dj_abs j).const_mul _),
                  integral_mul_left, integral_mul_left]
                apply add_le_add
                · exact mul_le_mul_of_nonneg_left (hM₀_bound v)
                    (Finset.sum_nonneg fun j _ => abs_nonneg _)
                · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                  rw [integral_finset_sum _ fun j _ => h_dj_abs j]
                  simp only [Fin.sum_univ_three, vGrad]
                  linarith [hM₁b v, hM₂b v, hM₃b v]
            _ ≤ 3 * ‖iteratedFDeriv ℝ 1 (f x) v‖ * M₀ +
                ‖iteratedFDeriv ℝ 0 (f x) v‖ * M_df := by
                gcongr
                · simp only [Fin.sum_univ_three]
                  linarith [hvg 0, hvg 1, hvg 2]
                · rw [← hf0]
            _ = M₀ * (3 * ‖iteratedFDeriv ℝ 1 (f x) v‖) +
                M_df * ‖iteratedFDeriv ℝ 0 (f x) v‖ := by ring
  -- Apply Integrable.mono' with C_bound / (1+‖v‖)^4
  refine (inverse_poly_integrable C_bound).mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
  · -- AEStronglyMeasurable of flux_i × log(f)
    refine AEStronglyMeasurable.mul ?_ ?_
    · -- flux_i is AEStronglyMeasurable: parametric integral of jointly measurable integrand
      exact flux_component_aestronglyMeasurable (f x) (hf_smooth_v x) hFlux i
    · -- log ∘ f x is continuous hence AEStronglyMeasurable
      exact ((hf_smooth_v x).continuous.log (fun v => ne_of_gt (hf_pos x v))).aestronglyMeasurable
  · -- Pointwise bound: ‖flux_i(v) * log(f x v)‖ ≤ C_bound / (1+‖v‖)^4
    rw [Real.norm_eq_abs, abs_mul]
    have hv_pos : (0 : ℝ) < 1 + ‖v‖ := by linarith [norm_nonneg v]
    have h_pow_pos : (0 : ℝ) < (1 + ‖v‖) ^ (K_log + 4) := by positivity
    have h_iterfd0_le : ‖iteratedFDeriv ℝ 0 (f x) v‖ ≤
        C_f / (1 + ‖v‖) ^ (K_log + 4) :=
      (le_div_iff₀ h_pow_pos).mpr (hC_f_bound x v)
    have h_iterfd1_le : ‖iteratedFDeriv ℝ 1 (f x) v‖ ≤
        C_df / (1 + ‖v‖) ^ (K_log + 4) :=
      (le_div_iff₀ h_pow_pos).mpr (hC_df_bound x v)
    have hlog : |(Real.log ∘ f x) v| ≤ C_log * (1 + ‖v‖) ^ K_log := hLB x v
    -- Chain: |flux| * |log| ≤ bound1 * |log| ≤ bound1 * bound2 ≤ ... ≤ C_bound/(1+‖v‖)^4
    have h_Clog_nn : (0:ℝ) ≤ C_log * (1 + ‖v‖) ^ K_log :=
      le_trans (abs_nonneg _) hlog
    calc |(∫ w, mulVec (landauMatrix coulombKernel (v - w))
            (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) i| *
          |(Real.log ∘ f x) v|
        ≤ (M₀ * (3 * ‖iteratedFDeriv ℝ 1 (f x) v‖) +
           M_df * ‖iteratedFDeriv ℝ 0 (f x) v‖) *
          |(Real.log ∘ f x) v| :=
          mul_le_mul_of_nonneg_right (h_flux_bound v) (abs_nonneg _)
      _ ≤ (M₀ * (3 * ‖iteratedFDeriv ℝ 1 (f x) v‖) +
           M_df * ‖iteratedFDeriv ℝ 0 (f x) v‖) *
          (C_log * (1 + ‖v‖) ^ K_log) :=
          mul_le_mul_of_nonneg_left hlog (by simp only [M_df]; positivity)
      _ ≤ (M₀ * (3 * (C_df / (1 + ‖v‖) ^ (K_log + 4))) +
           M_df * (C_f / (1 + ‖v‖) ^ (K_log + 4))) *
          (C_log * (1 + ‖v‖) ^ K_log) := by
          gcongr
      _ = (M₀ * 3 * C_df + M_df * C_f) * C_log / (1 + ‖v‖) ^ 4 := by
          rw [pow_add (1 + ‖v‖) K_log 4]; field_simp
      _ ≤ C_bound / (1 + ‖v‖) ^ 4 := by
          gcongr; simp only [C_bound]; linarith

-- ============================================================================
-- Flux component bound with polynomial gradient hypothesis
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Pointwise bound on the Coulomb flux component: |flux_i(v)| ≤ Cf * g(v) * (1+‖v‖)^Kg.
    Combines the Newtonian potential bound (∫ ‖v-w‖⁻¹ |g| ≤ M) with the polynomial
    gradient bound |∂_j g(v)| ≤ Cg * (1+‖v‖)^Kg * g(v). -/
lemma coulomb_flux_component_bound
    (g : (Fin 3 → ℝ) → ℝ)
    (hg_pos : ∀ v, 0 < g v)
    (hg_smooth : ContDiff ℝ ⊤ g)
    (hg_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k g v‖ * (1 + ‖v‖) ^ N ≤ C)
    {Cg : ℝ} {Kg : ℕ}
    (hGrad : ∀ (v : Fin 3 → ℝ) (j : Fin 3),
      |fderiv ℝ g v (Pi.single j 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * g v)
    (i : Fin 3) :
    ∃ Cf > 0, ∀ v,
    |(∫ w, mulVec (landauMatrix coulombKernel (v - w))
      (g w • vGrad g v - g v • vGrad g w)) i| ≤ Cf * g v * (1 + ‖v‖) ^ Kg := by
  -- Schwartz decay for g and ∂_j g
  have hg_decay : ∀ N, ∃ C > 0, ∀ w, |g w| * (1 + ‖w‖) ^ N ≤ C := by
    intro N; obtain ⟨C, hC, hb⟩ := hg_schwartz N 0
    exact ⟨C, hC, fun w => by simpa [iteratedFDeriv_zero_eq_comp] using hb w⟩
  have hdg_decay : ∀ j : Fin 3, ∀ N, ∃ C > 0, ∀ w,
      |fderiv ℝ g w (Pi.single j 1)| * (1 + ‖w‖) ^ N ≤ C := by
    intro j N; obtain ⟨C, hC, hb⟩ := hg_schwartz N 1
    refine ⟨C, hC, fun w => le_trans (mul_le_mul_of_nonneg_right ?_ (by positivity)) (hb w)⟩
    rw [← Real.norm_eq_abs]
    exact le_trans (le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_of_le_one_right (norm_nonneg _) (by simp [Pi.norm_single])))
      (by rw [show (1:ℕ) = 0+1 from rfl, ← norm_iteratedFDeriv_fderiv,
              norm_iteratedFDeriv_zero])
  -- Newtonian uniform bounds
  obtain ⟨M₀, hM₀, hM₀_bound⟩ := newtonian_schwartz_uniform_bound g hg_decay
    hg_smooth.continuous.aestronglyMeasurable
  have hMj : ∀ j, ∃ M > 0, ∀ v,
      ∫ w, ‖v - w‖⁻¹ * |fderiv ℝ g w (Pi.single j 1)| ≤ M :=
    fun j => newtonian_schwartz_uniform_bound _ (hdg_decay j)
      ((hg_smooth.continuous_fderiv le_top).clm_apply continuous_const).aestronglyMeasurable
  obtain ⟨M₁, hM₁, hM₁b⟩ := hMj 0
  obtain ⟨M₂, hM₂, hM₂b⟩ := hMj 1
  obtain ⟨M₃, hM₃, hM₃b⟩ := hMj 2
  set M_df := M₁ + M₂ + M₃
  -- Flux integrability
  have hFlux : ∀ v, Integrable (fun w => mulVec (landauMatrix coulombKernel (v - w))
      (g w • vGrad g v - g v • vGrad g w)) :=
    fun v => landau_flux_integrable_coulomb g hg_pos hg_smooth hg_schwartz v
  -- Integrability of ‖v-w‖⁻¹ * |g| and ‖v-w‖⁻¹ * |∂_j g|
  have h_f_abs : ∀ v, Integrable (fun w => ‖v - w‖⁻¹ * |g w|) := fun v =>
    (inv_norm_schwartz_integrable g hg_decay
      hg_smooth.continuous.aestronglyMeasurable v).norm.congr
      (Filter.Eventually.of_forall fun w => by
        show ‖‖v - w‖⁻¹ * g w‖ = ‖v - w‖⁻¹ * |g w|
        rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), Real.norm_eq_abs])
  have h_dj_abs : ∀ j : Fin 3, ∀ v,
      Integrable (fun w => ‖v - w‖⁻¹ * |vGrad g w j|) := fun j v =>
    (inv_norm_schwartz_integrable _ (hdg_decay j)
      ((hg_smooth.continuous_fderiv le_top).clm_apply continuous_const).aestronglyMeasurable
      v).norm.congr (Filter.Eventually.of_forall fun w => by
        show ‖‖v - w‖⁻¹ * fderiv ℝ g w (Pi.single j 1)‖ = ‖v - w‖⁻¹ * |vGrad g w j|
        rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          Real.norm_eq_abs]; rfl)
  -- Cg ≥ 0 from the gradient bound (|∂_j g| ≤ Cg * poly * g, all nonneg)
  have hCg_nn : 0 ≤ Cg := by
    by_contra h_neg; push_neg at h_neg
    have : Cg * (1 + ‖(0 : Fin 3 → ℝ)‖) ^ Kg * g 0 < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h_neg (by positivity)) (hg_pos 0)
    linarith [hGrad 0 0, abs_nonneg (fderiv ℝ g 0 (Pi.single 0 1))]
  -- Target constant
  refine ⟨3 * Cg * M₀ + M_df + 1, by nlinarith, fun v => ?_⟩
  set u := fun w => g w • vGrad g v - g v • vGrad g w with hu_def
  -- Step 1: pull component i out of integral
  rw [eval_integral (fun j => (hFlux v).eval j)]
  -- Step 2: pointwise bound |(A *ᵥ u)_i| ≤ ‖v-w‖⁻¹ * ∑ |u_j|
  have h_pw : ∀ w, |(landauMatrix coulombKernel (v - w) *ᵥ u w) i| ≤
      ‖v - w‖⁻¹ * ∑ j : Fin 3, |u w j| := by
    intro w
    by_cases hvw : v - w = 0
    · have : v = w := sub_eq_zero.mp hvw
      subst this; simp [mulVec, dotProduct, landauMatrix, innerLandauMatrix,
        normSq, vecMulVec, eucNorm, coulombKernel]
    · simp only [mulVec, dotProduct]
      calc |∑ j, landauMatrix coulombKernel (v - w) i j * u w j|
          ≤ ∑ j, |landauMatrix coulombKernel (v - w) i j * u w j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |landauMatrix coulombKernel (v - w) i j| * |u w j| := by
            congr 1; ext j; exact abs_mul _ _
        _ ≤ ∑ j, ‖v - w‖⁻¹ * |u w j| :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_right (coulomb_landauMatrix_entry_le_pi _ _ _ hvw)
                (abs_nonneg _)
        _ = ‖v - w‖⁻¹ * ∑ j, |u w j| := (Finset.mul_sum _ _ _).symm
  -- Step 3: triangle inequality |u_j(w)| ≤ g(w)*|∂_jg(v)| + g(v)*|∂_jg(w)|
  have h_tri : ∀ w j, |u w j| ≤
      g w * |vGrad g v j| + g v * |vGrad g w j| := by
    intro w j
    simp only [hu_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have := norm_sub_le (g w * vGrad g v j) (g v * vGrad g w j)
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_of_pos (hg_pos w), abs_of_pos (hg_pos v)] at this
  have h_sum_tri : ∀ w, ∑ j : Fin 3, |u w j| ≤
      g w * ∑ j : Fin 3, |vGrad g v j| + g v * ∑ j : Fin 3, |vGrad g w j| := by
    intro w
    calc ∑ j, |u w j|
        ≤ ∑ j, (g w * |vGrad g v j| + g v * |vGrad g w j|) :=
          Finset.sum_le_sum fun j _ => h_tri w j
      _ = g w * ∑ j, |vGrad g v j| + g v * ∑ j, |vGrad g w j| := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- Step 4: pointwise bound for integral_mono
  have h_pw2 : ∀ w, ‖v - w‖⁻¹ * ∑ j : Fin 3, |u w j| ≤
      (∑ j : Fin 3, |vGrad g v j|) * (‖v - w‖⁻¹ * |g w|) +
      g v * ∑ j : Fin 3, (‖v - w‖⁻¹ * |vGrad g w j|) := by
    intro w
    calc ‖v - w‖⁻¹ * ∑ j, |u w j|
        ≤ ‖v - w‖⁻¹ * (g w * ∑ j, |vGrad g v j| +
            g v * ∑ j, |vGrad g w j|) :=
          mul_le_mul_of_nonneg_left (h_sum_tri w) (inv_nonneg.mpr (norm_nonneg _))
      _ = _ := by
          rw [abs_of_pos (hg_pos w)]
          simp only [← Finset.mul_sum]; ring
  -- Step 5: integrate and apply newtonian bounds
  have h_rhs_int : Integrable (fun w =>
      (∑ j : Fin 3, |vGrad g v j|) * (‖v - w‖⁻¹ * |g w|) +
      g v * ∑ j : Fin 3, (‖v - w‖⁻¹ * |vGrad g w j|)) :=
    ((h_f_abs v).const_mul _).add
      ((integrable_finset_sum _ fun j _ => h_dj_abs j v).const_mul _)
  calc |∫ w, (landauMatrix coulombKernel (v - w) *ᵥ u w) i|
      ≤ ∫ w, |(landauMatrix coulombKernel (v - w) *ᵥ u w) i| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ w, ‖v - w‖⁻¹ * ∑ j : Fin 3, |u w j| :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => abs_nonneg _)
          (h_rhs_int.mono' (by fun_prop) (Filter.Eventually.of_forall fun w =>
            le_trans (h_pw w) (h_pw2 w)))
          (Filter.Eventually.of_forall h_pw)
    _ ≤ ∫ w, ((∑ j : Fin 3, |vGrad g v j|) * (‖v - w‖⁻¹ * |g w|) +
        g v * ∑ j : Fin 3, (‖v - w‖⁻¹ * |vGrad g w j|)) :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun w =>
            mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
              (Finset.sum_nonneg fun j _ => abs_nonneg _))
          h_rhs_int
          (Filter.Eventually.of_forall h_pw2)
    _ = (∑ j : Fin 3, |vGrad g v j|) * ∫ w, ‖v - w‖⁻¹ * |g w| +
        g v * ∑ j : Fin 3, ∫ w, ‖v - w‖⁻¹ * |vGrad g w j| := by
        rw [integral_add ((h_f_abs v).const_mul _)
          ((integrable_finset_sum _ fun j _ => h_dj_abs j v).const_mul _),
          integral_mul_left, integral_mul_left,
          integral_finset_sum _ fun j _ => h_dj_abs j v]
    _ ≤ (∑ j : Fin 3, |vGrad g v j|) * M₀ + g v * M_df := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hM₀_bound v)
            (Finset.sum_nonneg fun j _ => abs_nonneg _)
        · apply mul_le_mul_of_nonneg_left _ (le_of_lt (hg_pos v))
          simp only [Fin.sum_univ_three, vGrad, M_df]
          linarith [hM₁b v, hM₂b v, hM₃b v]
    _ ≤ 3 * (Cg * (1 + ‖v‖) ^ Kg * g v) * M₀ + g v * M_df := by
        gcongr
        simp only [Fin.sum_univ_three]
        linarith [hGrad v 0, hGrad v 1, hGrad v 2]
    _ ≤ (3 * Cg * M₀ + M_df) * g v * (1 + ‖v‖) ^ Kg := by
        have h1 : (1 : ℝ) ≤ (1 + ‖v‖) ^ Kg :=
          one_le_pow_of_one_le_of_le (by linarith [norm_nonneg v]) le_rfl
        nlinarith [hg_pos v, hM₀.le]
    _ ≤ (3 * Cg * M₀ + M_df + 1) * g v * (1 + ‖v‖) ^ Kg := by
        nlinarith [hg_pos v, one_le_pow_of_one_le_of_le
          (show (1:ℝ) ≤ 1 + ‖v‖ by linarith [norm_nonneg v]) (le_refl Kg)]

end VML
