import Aristotle.Landau.main.CoulombFlux

/-!
# Coulomb Entry Convolution: Differentiability and Bounds

Establishes that partial derivatives of functions with C² decay are C² decay,
Coulomb kernel entry convolutions are differentiable with uniform derivative bounds,
and the full Coulomb flux component is differentiable with a decomposition formula.
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

private lemma landauMatrix_coulombKernel_zero (i j : Fin 3) :
    landauMatrix coulombKernel 0 i j = 0 := by
  simp +decide [landauMatrix, innerLandauMatrix, normSq, eucNorm, coulombKernel,
    dotProduct, vecMulVec]

/-- Partial derivatives of a Schwartz function are Schwartz. Uses
    `ContinuousLinearMap.iteratedFDeriv_comp_left` + `norm_iteratedFDeriv_fderiv`. -/
lemma schwartz_fderiv_component_schwartz
    (f : (Fin 3 → ℝ) → ℝ) (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 → ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (j : Fin 3) (N : ℕ) {k : ℕ} (hk : k + 1 ≤ 2) :
    ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k (fun w => fderiv ℝ f w (Pi.single j 1)) v‖ *
        (1 + ‖v‖) ^ N ≤ C := by
  obtain ⟨C, hC_pos, hC⟩ := hf_schwartz N hk
  refine ⟨C, hC_pos, fun v => ?_⟩
  have h1 : (fun w => fderiv ℝ f w (Pi.single j 1)) =
      (ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1 : Fin 3 → ℝ)) ∘ (fderiv ℝ f) := rfl
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_left _
    (hf_smooth.fderiv_right le_top).contDiffAt le_top]
  have h_norm_eval : ‖(ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1 : Fin 3 → ℝ))‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro L
    simp only [ContinuousLinearMap.apply_apply]
    exact le_trans (L.le_opNorm _) (by simp [Pi.norm_single])
  calc ‖(ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1 : Fin 3 → ℝ)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (fderiv ℝ f) v)‖ * (1 + ‖v‖) ^ N
      ≤ ‖ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1 : Fin 3 → ℝ)‖ *
        ‖iteratedFDeriv ℝ k (fderiv ℝ f) v‖ * (1 + ‖v‖) ^ N := by
          gcongr; exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ‖iteratedFDeriv ℝ k (fderiv ℝ f) v‖ * (1 + ‖v‖) ^ N := by gcongr
    _ = ‖iteratedFDeriv ℝ (k + 1) f v‖ * (1 + ‖v‖) ^ N := by
          rw [one_mul, norm_iteratedFDeriv_fderiv]
    _ ≤ C := hC v

/-- Coulomb matrix entry times Schwartz function is integrable in ℝ³.
    Domination: |A_{ij}(v-w) * g(w)| ≤ ‖v-w‖⁻¹ * |g(w)| by entry bound. -/
lemma coulomb_entry_schwartz_integrable
    (g : (Fin 3 → ℝ) → ℝ) (hg_smooth : ContDiff ℝ ⊤ g)
    (hg_decay : ∀ N : ℕ, ∃ C > 0, ∀ v, |g v| * (1 + ‖v‖) ^ N ≤ C)
    (v : Fin 3 → ℝ) (i j : Fin 3) :
    Integrable (fun w => landauMatrix coulombKernel (v - w) i j * g w) := by
  show Integrable (fun w => landauMatrix coulombKernel (v - w) i j * g w)
  refine (inv_norm_schwartz_integrable g hg_decay hg_smooth.continuous.aestronglyMeasurable v).mono
    ?_ (ae_of_all _ fun w => ?_)
  · -- AEStronglyMeasurable: matrix entry is measurable, g is continuous
    change AEStronglyMeasurable (fun w => coulombKernel (eucNorm (v - w)) *
        innerLandauMatrix (v - w) i j * g w) volume
    exact ((((Measurable.ite measurableSet_Iic measurable_const
      (measurable_id.pow_const _)).comp ((Continuous.measurable (Continuous.dotProduct
        (continuous_const.sub continuous_id')
        (continuous_const.sub continuous_id'))).sqrt)).mul
      (by apply Continuous.measurable; unfold innerLandauMatrix
          simp +decide [normSq, vecMulVec]; fun_prop (disch := norm_num)
      )).aestronglyMeasurable).mul hg_smooth.continuous.aestronglyMeasurable
  · -- Domination bound
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    by_cases hvw : v - w = 0
    · simp [hvw, landauMatrix_coulombKernel_zero]
    · exact mul_le_mul_of_nonneg_right
        (le_trans (le_of_eq (Real.norm_eq_abs _)) (coulomb_landauMatrix_entry_le_pi _ _ _ hvw))
        (norm_nonneg _)

/-- Convolution of a Coulomb kernel matrix entry with a Schwartz function is differentiable.
    After substituting u = v - w, the kernel A(u) doesn't depend on v, so differentiation
    under the integral sign applies via hasFDerivAt_integral_of_dominated_of_fderiv_le:
    the v-derivative acts only on g(v-u), giving a bound
    |A(u)_{ij}| * ‖fderiv g(v-u)‖ ≤ ‖u‖⁻¹ * C/(1+‖u‖)^4 which is integrable in ℝ³. -/
/-- Core helper: the derivative of the Coulomb entry convolution at v₀ equals
    ∫ A(u) • fderiv(g)(v₀-u) du, with HasFDerivAt witness. -/
private lemma coulomb_entry_conv_hasFDerivAt_aux
    (g : (Fin 3 → ℝ) → ℝ) (hg_smooth : ContDiff ℝ ⊤ g)
    (hg_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k g v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i j : Fin 3) (v₀ : Fin 3 → ℝ) :
    HasFDerivAt (fun v => ∫ u, landauMatrix coulombKernel u i j * g (v - u))
      (∫ u, landauMatrix coulombKernel u i j • fderiv ℝ g (v₀ - u)) v₀ := by
  -- Uniform bound on ‖fderiv g‖: from Schwartz decay with N=0, k=1
  obtain ⟨Cf, hCf_pos, hCf⟩ : ∃ Cf > 0, ∀ w : Fin 3 → ℝ, ‖fderiv ℝ g w‖ ≤ Cf := by
    obtain ⟨Cf, hCf_pos, hCf⟩ := hg_schwartz 0 1
    exact ⟨Cf, hCf_pos, fun w => by simpa [pow_zero] using hCf w⟩
  have hg_diff : ∀ w, HasFDerivAt g (fderiv ℝ g w) w :=
    fun w => (hg_smooth.differentiable le_top).differentiableAt.hasFDerivAt
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun v u => landauMatrix coulombKernel u i j • fderiv ℝ g (v - u))
    (bound := fun u => ‖u‖⁻¹ * Cf)
    (s := Set.univ)
    (Filter.univ_mem' (fun _ => trivial))
    ?_ ?_ ?_ ?_ ?_ ?_
  · -- F measurable
    apply Filter.Eventually.of_forall
    intro v
    exact (coulomb_entry_schwartz_integrable g hg_smooth hg_schwartz v i j).aestronglyMeasurable
  · -- F integrable at v₀
    exact coulomb_entry_schwartz_integrable g hg_smooth hg_schwartz v₀ i j
  · -- F' measurable at v₀
    exact ((coulomb_entry_schwartz_integrable g hg_smooth hg_schwartz v₀ i j)
        .aestronglyMeasurable.mono (fun u => by simp)).smul
      ((hg_smooth.fderiv_right le_top).continuous.comp
        (continuous_const.sub continuous_id')).aestronglyMeasurable
  · -- Bound: ‖F'(v, u)‖ ≤ bound(u)
    apply ae_of_all
    intro u v _
    simp only [norm_smul]
    by_cases hu : u = 0
    · simp [hu, landauMatrix_coulombKernel_zero]
    · calc ‖landauMatrix coulombKernel u i j‖ * ‖fderiv ℝ g (v - u)‖
          ≤ ‖u‖⁻¹ * ‖fderiv ℝ g (v - u)‖ := by
            gcongr
            rw [Real.norm_eq_abs]
            exact le_trans (le_abs_self _) (coulomb_landauMatrix_entry_le_pi u i j hu)
        _ ≤ ‖u‖⁻¹ * Cf := by gcongr; exact hCf _
  · -- Dominator integrable
    have : Integrable (fun u : Fin 3 → ℝ => ‖u‖⁻¹ * (1 : ℝ)) := by
      have h1_decay : ∀ N : ℕ, ∃ C > 0, ∀ w : Fin 3 → ℝ, |(1 : ℝ)| * (1 + ‖w‖) ^ N ≤ C := by
        intro N
        exact ⟨1, one_pos, fun _ => by
          simp [one_le_pow_of_one_le (by linarith [norm_nonneg (α := Fin 3 → ℝ)])]⟩
      exact inv_norm_schwartz_integrable _ h1_decay aestronglyMeasurable_const 0
    exact this.const_mul Cf |>.congr (ae_of_all _ fun u => by ring)
  · -- HasFDerivAt pointwise
    apply ae_of_all
    intro u v _
    have : HasFDerivAt (fun v => g (v - u)) (fderiv ℝ g (v - u)) v := by
      exact (hg_diff (v - u)).comp v ((hasFDerivAt_id v).sub (hasFDerivAt_const u v))
    exact this.const_mul (landauMatrix coulombKernel u i j)

lemma coulomb_entry_conv_differentiable
    (g : (Fin 3 → ℝ) → ℝ) (hg_smooth : ContDiff ℝ ⊤ g)
    (hg_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k g v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i j : Fin 3) :
    Differentiable ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * g w) := by
  -- Rewrite in u-coordinates and use HasFDerivAt
  suffices h : Differentiable ℝ (fun v => ∫ u, landauMatrix coulombKernel u i j * g (v - u)) by
    refine h.congr (fun v => ?_)
    show (∫ u, landauMatrix coulombKernel u i j * g (v - u)) =
        ∫ w, landauMatrix coulombKernel (v - w) i j * g w
    rw [← integral_sub_left_eq_self
      (fun w => landauMatrix coulombKernel w i j * g (v - w)) volume v]
    simp [sub_sub_cancel]
  exact fun v₀ =>
    (coulomb_entry_conv_hasFDerivAt_aux g hg_smooth hg_schwartz i j v₀).differentiableAt

/-- The derivative of a Coulomb entry convolution with a Schwartz function is uniformly bounded.
    After substituting u = v - w, the fderiv acts only on g(v-u), giving
    fderiv(conv)(v) = ∫ A(u) • fderiv(g)(v-u) du. The bound follows from
    |A(u)| ≤ ‖u‖⁻¹ and integrability of ‖u‖⁻¹ * ‖fderiv g(·)‖ via
    newtonian_schwartz_uniform_bound.

    NOTE: The convolution does NOT have Schwartz decay (only O(‖v‖⁻²) since the
    Coulomb kernel is degree -1 homogeneous). But the uniform bound suffices because
    in `coulomb_flux_deriv_schwartz_decay`, convolution derivatives are multiplied by
    Schwartz-decaying factors (f, ∂_j f). -/
lemma coulomb_entry_conv_deriv_bounded
    (g : (Fin 3 → ℝ) → ℝ) (hg_smooth : ContDiff ℝ ⊤ g)
    (hg_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k g v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i j : Fin 3) :
    ∃ C > 0, ∀ v,
        ‖fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * g w) v‖ ≤ C := by
  -- Schwartz decay of fderiv g (absolute value form)
  have hfderiv_abs_decay : ∀ N : ℕ, ∃ C > 0, ∀ w,
      |‖fderiv ℝ g w‖| * (1 + ‖w‖) ^ N ≤ C := by
    intro N; obtain ⟨C, hC, hb⟩ := hg_schwartz N 1
    refine ⟨C, hC, fun w => ?_⟩
    rw [abs_of_nonneg (norm_nonneg _)]
    calc ‖fderiv ℝ g w‖ * (1 + ‖w‖) ^ N
        = ‖iteratedFDeriv ℝ 1 g w‖ * (1 + ‖w‖) ^ N := by
          rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := fderiv ℝ g),
              norm_iteratedFDeriv_fderiv]
      _ ≤ C := hb w
  -- Uniform bound on convolution via newtonian_schwartz_uniform_bound
  obtain ⟨M, hM_pos, hM⟩ := newtonian_schwartz_uniform_bound
    (fun w => ‖fderiv ℝ g w‖) hfderiv_abs_decay
    ((hg_smooth.fderiv_right le_top).continuous.norm.aestronglyMeasurable)
  refine ⟨M + 1, by linarith, fun v => ?_⟩
  -- The fderiv in u-coordinates equals ∫ A(u) • fderiv(g)(v-u)
  -- We use HasFDerivAt.fderiv to get the concrete representation
  have h_conv_eq : (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * g w) =
      (fun v => ∫ u, landauMatrix coulombKernel u i j * g (v - u)) := by
    ext v
    show ∫ w, landauMatrix coulombKernel (v - w) i j * g w =
        ∫ u, landauMatrix coulombKernel u i j * g (v - u)
    rw [← integral_sub_left_eq_self
      (fun w => landauMatrix coulombKernel w i j * g (v - w)) volume v]
    simp [sub_sub_cancel]
  rw [h_conv_eq]
  have h_hfd := coulomb_entry_conv_hasFDerivAt_aux g hg_smooth hg_schwartz i j v
  rw [h_hfd.fderiv]
  -- Bound ‖∫ A(u) • fderiv(g)(v-u) du‖ ≤ ∫ ‖u‖⁻¹ * ‖fderiv(g)(v-u)‖ du ≤ M
  calc ‖∫ u, landauMatrix coulombKernel u i j • fderiv ℝ g (v - u)‖
      ≤ ∫ u, ‖landauMatrix coulombKernel u i j • fderiv ℝ g (v - u)‖ :=
          norm_integral_le_integral_norm _
    _ = ∫ u, ‖landauMatrix coulombKernel u i j‖ * ‖fderiv ℝ g (v - u)‖ := by
        congr 1
        ext u
        exact norm_smul _ _
    _ ≤ ∫ u, ‖u‖⁻¹ * ‖fderiv ℝ g (v - u)‖ := by
        apply integral_mono_of_nonneg
          (ae_of_all _ fun u => by positivity)
          (inv_norm_schwartz_integrable (fun w => ‖fderiv ℝ g w‖)
            hfderiv_abs_decay
            (hg_smooth.fderiv_right le_top).continuous.norm.aestronglyMeasurable v)
          (ae_of_all _ fun u => by
            by_cases hu : u = 0
            · simp [hu, landauMatrix_coulombKernel_zero]
            · exact mul_le_mul_of_nonneg_right
                (le_trans (le_of_eq (Real.norm_eq_abs _).symm)
                  (le_trans (le_abs_self _) (coulomb_landauMatrix_entry_le_pi u i j hu)))
                (norm_nonneg _))
    _ = ∫ w, ‖v - w‖⁻¹ * ‖fderiv ℝ g w‖ := by
        rw [← integral_sub_left_eq_self (fun u => ‖u‖⁻¹ * ‖fderiv ℝ g (v - u)‖) volume v]
        congr 1
        ext u
        simp [sub_sub_cancel]
    _ ≤ M := hM v
    _ ≤ M + 1 := le_add_of_nonneg_right one_pos.le

/-- The Coulomb flux component v ↦ (∫_w A(v-w)·[f(w)∇f(v)-f(v)∇f(w)])_i is differentiable.

    Proof strategy: Decompose the flux as
      flux_i(v) = Σ_j (∂_j f)(v) * K_{ij}(v) - f(v) * Σ_j L_{ij}(v)
    where K_{ij}(v) = ∫ A_{ij}(v-w) f(w) dw and L_{ij}(v) = ∫ A_{ij}(v-w) (∂_j f)(w) dw.
    Each K_{ij} and L_{ij} is differentiable by coulomb_entry_conv_differentiable.
    Then flux_i is differentiable by product/sum rules. -/
lemma coulomb_flux_differentiable
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 → ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i : Fin 3) :
    Differentiable ℝ (fun v =>
      (∫ w, mulVec (landauMatrix coulombKernel (v - w))
        (f w • vGrad f v - f v • vGrad f w)) i) := by
  -- K_{ij}(v) = ∫ A_{ij}(v-w) f(w) dw is differentiable
  have hK_diff : ∀ j, Differentiable ℝ
      (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * f w) :=
    fun j => coulomb_entry_conv_differentiable f hf_smooth hf_schwartz i j
  -- ∂_j f is Schwartz
  have hdf_schwartz := fun j => schwartz_fderiv_component_schwartz f hf_smooth hf_schwartz j
  -- L_{ij}(v) = ∫ A_{ij}(v-w) (∂_j f)(w) dw is differentiable
  have hL_diff : ∀ j, Differentiable ℝ
      (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j *
        fderiv ℝ f w (Pi.single j 1)) :=
    fun j => coulomb_entry_conv_differentiable _ (hf_smooth.fderiv_right le_top |>.clm_apply
      contDiff_const) (hdf_schwartz j) i j
  -- The decomposed form Σ_j [∂_j f(v) * K_{ij}(v) - f(v) * L_{ij}(v)] is differentiable
  have h_decomp_diff : Differentiable ℝ (fun v => ∑ j : Fin 3,
      (fderiv ℝ f v (Pi.single j 1) *
        (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
       f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
        fderiv ℝ f w (Pi.single j 1)))) :=
    Differentiable.sum fun j _ =>
      (((hf_smooth.fderiv_right le_top).clm_apply contDiff_const).differentiable le_top).mul
        (hK_diff j) |>.sub ((hf_smooth.differentiable le_top).mul (hL_diff j))
  -- The flux equals the decomposed form at each point
  -- Entry integrabilities for the flux decomposition
  have h_Af : ∀ v j, Integrable (fun w => landauMatrix coulombKernel (v - w) i j * f w) :=
    fun v j => coulomb_entry_schwartz_integrable f hf_smooth hf_schwartz v i j
  have h_Adf : ∀ v j, Integrable (fun w => landauMatrix coulombKernel (v - w) i j *
      fderiv ℝ f w (Pi.single j 1)) :=
    fun v j => coulomb_entry_schwartz_integrable _ (hf_smooth.fderiv_right le_top |>.clm_apply
      contDiff_const) (hdf_schwartz j) v i j
  exact h_decomp_diff.congr fun v => by
    -- Step 1: extract component i from vector integral
    rw [eval_integral (fun k =>
      (landau_flux_integrable_coulomb f hf_pos hf_smooth hf_schwartz v).eval k) i]
    -- Step 2: expand mulVec as dot product
    simp only [mulVec, dotProduct]
    -- Step 3: exchange sum and integral (need each summand integrable)
    rw [integral_finset_sum _ (fun j _ => by
      have : (fun w => landauMatrix coulombKernel (v - w) i j *
          (f w • vGrad f v - f v • vGrad f w) j) =
        (fun w => fderiv ℝ f v (Pi.single j 1) * (landauMatrix coulombKernel (v - w) i j * f w) -
          f v * (landauMatrix coulombKernel (v - w) i j * fderiv ℝ f w (Pi.single j 1))) := by
        ext w
        simp [vGrad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [this]; exact ((h_Af v j).const_mul _).sub ((h_Adf v j).const_mul _))]
    -- Step 4: for each j, expand and distribute the integral
    congr 1; ext j
    have h_eq : ∀ w, landauMatrix coulombKernel (v - w) i j *
        (f w • vGrad f v - f v • vGrad f w) j =
      fderiv ℝ f v (Pi.single j 1) * (landauMatrix coulombKernel (v - w) i j * f w) -
      f v * (landauMatrix coulombKernel (v - w) i j * fderiv ℝ f w (Pi.single j 1)) := by
      intro w
      simp [vGrad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [h_eq]
    rw [integral_sub ((h_Af v j).const_mul _) ((h_Adf v j).const_mul _),
        integral_const_mul_of_integrable (h_Af v j),
        integral_const_mul_of_integrable (h_Adf v j)]

/-- The Coulomb flux component equals the K/L decomposition pointwise:
    (∫ w, mulVec A(v-w) (f(w)•∇f(v) - f(v)•∇f(w)))_i = Σ_j [∂_j f(v) * K_j(v) - f(v) * L_j(v)]
    where K_j(v) = ∫ A_{ij}(v-w) f(w) dw and L_j(v) = ∫ A_{ij}(v-w) ∂_j f(w) dw. -/
lemma coulomb_flux_eq_decomposed
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 → ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i : Fin 3) (v : Fin 3 → ℝ) :
    (∫ w, mulVec (landauMatrix coulombKernel (v - w))
      (f w • vGrad f v - f v • vGrad f w)) i =
    ∑ j : Fin 3,
      (fderiv ℝ f v (Pi.single j 1) *
        (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
       f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
        fderiv ℝ f w (Pi.single j 1))) := by
  have hdf_schwartz := fun j => schwartz_fderiv_component_schwartz f hf_smooth hf_schwartz j
  have h_Af : ∀ j, Integrable (fun w => landauMatrix coulombKernel (v - w) i j * f w) :=
    fun j => coulomb_entry_schwartz_integrable f hf_smooth hf_schwartz v i j
  have h_Adf : ∀ j, Integrable (fun w => landauMatrix coulombKernel (v - w) i j *
      fderiv ℝ f w (Pi.single j 1)) :=
    fun j => coulomb_entry_schwartz_integrable _ (hf_smooth.fderiv_right le_top |>.clm_apply
      contDiff_const) (hdf_schwartz j) v i j
  rw [eval_integral (fun k =>
    (landau_flux_integrable_coulomb f hf_pos hf_smooth hf_schwartz v).eval k) i]
  simp only [mulVec, dotProduct]
  rw [integral_finset_sum _ (fun j _ => by
    have : (fun w => landauMatrix coulombKernel (v - w) i j *
        (f w • vGrad f v - f v • vGrad f w) j) =
      (fun w => fderiv ℝ f v (Pi.single j 1) * (landauMatrix coulombKernel (v - w) i j * f w) -
        f v * (landauMatrix coulombKernel (v - w) i j * fderiv ℝ f w (Pi.single j 1))) := by
      ext w
      simp [vGrad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]; exact ((h_Af j).const_mul _).sub ((h_Adf j).const_mul _))]
  congr 1; ext j
  have h_eq : ∀ w, landauMatrix coulombKernel (v - w) i j *
      (f w • vGrad f v - f v • vGrad f w) j =
    fderiv ℝ f v (Pi.single j 1) * (landauMatrix coulombKernel (v - w) i j * f w) -
    f v * (landauMatrix coulombKernel (v - w) i j * fderiv ℝ f w (Pi.single j 1)) := by
    intro w
    simp [vGrad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [h_eq]
  rw [integral_sub ((h_Af j).const_mul _) ((h_Adf j).const_mul _),
      integral_const_mul_of_integrable (h_Af j),
      integral_const_mul_of_integrable (h_Adf j)]


end VML
