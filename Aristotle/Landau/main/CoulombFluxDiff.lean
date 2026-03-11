import Aristotle.Landau.main.CoulombFlux

/-!
# Flux Differentiability and Integration by Parts for Coulomb

Establishes that partial derivatives of Schwartz functions are Schwartz, Coulomb
entry convolutions are differentiable with uniform bounds, and the flux component
is differentiable with Schwartz-class derivative decay. Proves the IBP
integrability condition for the flux derivative times log f.
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
    (hf_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (j : Fin 3) (N k : ℕ) :
    ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k (fun w => fderiv ℝ f w (Pi.single j 1)) v‖ *
        (1 + ‖v‖) ^ N ≤ C := by
  obtain ⟨C, hC_pos, hC⟩ := hf_schwartz N (k + 1)
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
    (hg_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k g v‖ * (1 + ‖v‖) ^ N ≤ C)
    (v : Fin 3 → ℝ) (i j : Fin 3) :
    Integrable (fun w => landauMatrix coulombKernel (v - w) i j * g w) := by
  have hg_decay : ∀ N : ℕ, ∃ C > 0, ∀ w, |g w| * (1 + ‖w‖) ^ N ≤ C := by
    intro N; obtain ⟨C, hC, hb⟩ := hg_schwartz N 0
    exact ⟨C, hC, fun w => by simpa [norm_iteratedFDeriv_zero] using hb w⟩
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
    exact ((coulomb_entry_schwartz_integrable g hg_smooth hg_schwartz v₀ i j).aestronglyMeasurable.mono
      (fun u => by simp)).smul
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
        exact ⟨1, one_pos, fun _ => by simp [one_le_pow_of_one_le (by linarith [norm_nonneg (α := Fin 3 → ℝ)])]⟩
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
    show (∫ u, landauMatrix coulombKernel u i j * g (v - u)) = ∫ w, landauMatrix coulombKernel (v - w) i j * g w
    rw [← integral_sub_left_eq_self (fun w => landauMatrix coulombKernel w i j * g (v - w)) volume v]
    simp [sub_sub_cancel]
  exact fun v₀ => (coulomb_entry_conv_hasFDerivAt_aux g hg_smooth hg_schwartz i j v₀).differentiableAt

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
    ∃ C > 0, ∀ v, ‖fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * g w) v‖ ≤ C := by
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
    show ∫ w, landauMatrix coulombKernel (v - w) i j * g w = ∫ u, landauMatrix coulombKernel u i j * g (v - u)
    rw [← integral_sub_left_eq_self (fun w => landauMatrix coulombKernel w i j * g (v - w)) volume v]
    simp [sub_sub_cancel]
  rw [h_conv_eq]
  have h_hfd := coulomb_entry_conv_hasFDerivAt_aux g hg_smooth hg_schwartz i j v
  rw [h_hfd.fderiv]
  -- Bound ‖∫ A(u) • fderiv(g)(v-u) du‖ ≤ ∫ ‖u‖⁻¹ * ‖fderiv(g)(v-u)‖ du ≤ M
  calc ‖∫ u, landauMatrix coulombKernel u i j • fderiv ℝ g (v - u)‖
      ≤ ∫ u, ‖landauMatrix coulombKernel u i j • fderiv ℝ g (v - u)‖ := norm_integral_le_integral_norm _
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
    (hf_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
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
    (hf_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
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

/-- The derivative of the Coulomb flux component has Schwartz-class decay.
    Since the flux decomposes into convolutions of Coulomb entries with Schwartz functions,
    its derivatives inherit Schwartz decay via coulomb_entry_conv_deriv_decay. -/
lemma coulomb_flux_deriv_schwartz_decay
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i : Fin 3) (N : ℕ) :
    ∃ C > 0, ∀ v, ‖fderiv ℝ (fun v =>
      (∫ w, mulVec (landauMatrix coulombKernel (v - w))
        (f w • vGrad f v - f v • vGrad f w)) i) v‖ * (1 + ‖v‖) ^ N ≤ C := by
  -- ∂_j f is Schwartz
  have hdf_schwartz := fun j => schwartz_fderiv_component_schwartz f hf_smooth hf_schwartz j
  -- Each convolution K_{ij}, L_{ij} has uniformly bounded derivatives
  have hK_fderiv_bdd : ∀ j, ∃ C > 0, ∀ v,
      ‖fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * f w) v‖ ≤ C :=
    fun j => coulomb_entry_conv_deriv_bounded f hf_smooth hf_schwartz i j
  have hL_fderiv_bdd : ∀ j, ∃ C > 0, ∀ v,
      ‖fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j *
        fderiv ℝ f w (Pi.single j 1)) v‖ ≤ C :=
    fun j => coulomb_entry_conv_deriv_bounded _ (hf_smooth.fderiv_right le_top |>.clm_apply
      contDiff_const) (hdf_schwartz j) i j
  -- Replace flux with K/L decomposition
  have h_fn_eq : (fun v => (∫ w, mulVec (landauMatrix coulombKernel (v - w))
      (f w • vGrad f v - f v • vGrad f w)) i) =
    (fun v => ∑ j : Fin 3,
      (fderiv ℝ f v (Pi.single j 1) *
        (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
       f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
        fderiv ℝ f w (Pi.single j 1)))) :=
    funext (coulomb_flux_eq_decomposed f hf_pos hf_smooth hf_schwartz i)
  rw [h_fn_eq]
  -- Differentiability of components
  have hK_diff : ∀ j, Differentiable ℝ
      (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * f w) :=
    fun j => coulomb_entry_conv_differentiable f hf_smooth hf_schwartz i j
  have hL_diff : ∀ j, Differentiable ℝ
      (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j *
        fderiv ℝ f w (Pi.single j 1)) :=
    fun j => coulomb_entry_conv_differentiable _ (hf_smooth.fderiv_right le_top |>.clm_apply
      contDiff_const) (hdf_schwartz j) i j
  have ha_diff : ∀ j, Differentiable ℝ (fun v => fderiv ℝ f v (Pi.single j 1)) :=
    fun j => ((hf_smooth.fderiv_right le_top).clm_apply contDiff_const).differentiable le_top
  have hf_diff := hf_smooth.differentiable le_top
  -- Schwartz decay facts: f and ∂_j f bounded, their fderiv decays
  have hf_decay : ∀ M : ℕ, ∃ C > 0, ∀ w, |f w| * (1 + ‖w‖) ^ M ≤ C := by
    intro M; obtain ⟨C, hC, h⟩ := hf_schwartz M 0
    exact ⟨C, hC, fun w => by simpa [norm_iteratedFDeriv_zero] using h w⟩
  -- K_j bounded: |∫ A * f| ≤ ∫ ‖v-w‖⁻¹ * |f| ≤ M
  obtain ⟨MK, hMK, hMK_bdd⟩ := newtonian_schwartz_uniform_bound f hf_decay
    hf_smooth.continuous.aestronglyMeasurable
  have hK_sup : ∀ j v, |∫ w, landauMatrix coulombKernel (v - w) i j * f w| ≤ MK := by
    intro j v
    calc |∫ w, landauMatrix coulombKernel (v - w) i j * f w|
        ≤ ∫ w, |landauMatrix coulombKernel (v - w) i j * f w| := norm_integral_le_integral_norm _
      _ ≤ ∫ w, ‖v - w‖⁻¹ * |f w| := by
          apply integral_mono_of_nonneg (ae_of_all _ fun w => abs_nonneg _)
            (inv_norm_schwartz_integrable f hf_decay hf_smooth.continuous.aestronglyMeasurable v)
            (ae_of_all _ fun w => by
              rw [abs_mul]
              by_cases hvw : v - w = 0
              · simp [hvw, landauMatrix_coulombKernel_zero]
              · exact mul_le_mul_of_nonneg_right
                  (le_trans (le_of_eq (Real.norm_eq_abs _))
                    (coulomb_landauMatrix_entry_le_pi _ i j hvw)) (abs_nonneg _))
      _ ≤ MK := hMK_bdd v
  -- L_j bounded similarly
  have hdf_decay_abs : ∀ j, ∀ M : ℕ, ∃ C > 0, ∀ w,
      |fderiv ℝ f w (Pi.single j 1)| * (1 + ‖w‖) ^ M ≤ C := by
    intro j M; obtain ⟨C, hC, h⟩ := hdf_schwartz j M 0
    exact ⟨C, hC, fun w => by simpa [norm_iteratedFDeriv_zero] using h w⟩
  obtain ⟨ML, hML, hML_bdd⟩ := newtonian_schwartz_uniform_bound
    (fun w => fderiv ℝ f w (Pi.single 0 1)) (hdf_decay_abs 0)
    ((hf_smooth.fderiv_right le_top |>.clm_apply contDiff_const).continuous.aestronglyMeasurable)
  -- Use single bound ML' that works for all j
  have hL_sup : ∀ j v, |∫ w, landauMatrix coulombKernel (v - w) i j *
      fderiv ℝ f w (Pi.single j 1)| ≤ ML + 1 := by
    intro j v
    -- Each ∂_j f is Schwartz with the same structure
    obtain ⟨MLj, hMLj, hMLj_bdd⟩ := newtonian_schwartz_uniform_bound
      (fun w => fderiv ℝ f w (Pi.single j 1)) (hdf_decay_abs j)
      ((hf_smooth.fderiv_right le_top |>.clm_apply contDiff_const).continuous.aestronglyMeasurable)
    calc |∫ w, landauMatrix coulombKernel (v - w) i j * fderiv ℝ f w (Pi.single j 1)|
        ≤ ∫ w, |landauMatrix coulombKernel (v - w) i j * fderiv ℝ f w (Pi.single j 1)| :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ w, ‖v - w‖⁻¹ * |fderiv ℝ f w (Pi.single j 1)| := by
          apply integral_mono_of_nonneg (ae_of_all _ fun w => abs_nonneg _)
            (inv_norm_schwartz_integrable _ (hdf_decay_abs j)
              (hf_smooth.fderiv_right le_top |>.clm_apply contDiff_const).continuous.aestronglyMeasurable v)
            (ae_of_all _ fun w => by
              rw [abs_mul]
              by_cases hvw : v - w = 0
              · simp [hvw, landauMatrix_coulombKernel_zero]
              · exact mul_le_mul_of_nonneg_right
                  (le_trans (le_of_eq (Real.norm_eq_abs _))
                    (coulomb_landauMatrix_entry_le_pi _ i j hvw)) (abs_nonneg _))
      _ ≤ MLj := hMLj_bdd v
      _ ≤ MLj + 0 := (add_zero _).symm ▸ le_refl _
      _ ≤ ML + 1 := by linarith
  -- f is bounded
  obtain ⟨Mf, hMf_pos, hMf⟩ := hf_decay 0
  have hf_sup : ∀ v, |f v| ≤ Mf := fun v => by simpa using hMf v
  -- ∂_j f is bounded
  have hdf_sup : ∀ j, ∃ M, ∀ v, |fderiv ℝ f v (Pi.single j 1)| ≤ M := by
    intro j; obtain ⟨C, _, h⟩ := hdf_decay_abs j 0
    exact ⟨C, fun v => by simpa using h v⟩
  obtain ⟨Mdf, hMdf⟩ := hdf_sup 0  -- use as proxy; bound for all j by taking max
  -- fderiv(f) Schwartz decay: ‖fderiv f v‖ * (1+‖v‖)^N ≤ Cf
  obtain ⟨Cf, hCf_pos, hCf⟩ := hf_schwartz N 1
  -- fderiv(∂_j f) Schwartz decay
  -- Per-component fderiv decay: for each j, bound ‖fderiv(∂_j f * K_j - f * L_j)(v)‖ * (1+‖v‖)^N
  -- by product rule: ≤ |∂_j f(v)| * ‖fderiv(K_j)(v)‖ + |K_j(v)| * ‖fderiv(∂_j f)(v)‖
  --                    + |f(v)| * ‖fderiv(L_j)(v)‖ + |L_j(v)| * ‖fderiv(f)(v)‖
  -- Each pair is (bounded) * (Schwartz decay) so (bounded) * (Schwartz) ≤ const
  have h_per_term : ∀ j, ∃ C > 0, ∀ v,
      ‖fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1) *
        (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
       f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
        fderiv ℝ f w (Pi.single j 1))) v‖ * (1 + ‖v‖) ^ N ≤ C := by
    intro j
    -- Extract per-component bounds
    -- Schwartz decay of ∂_j f with polynomial weight N
    obtain ⟨Mdj_N, hMdj_N_pos, hMdj_N⟩ := hdf_decay_abs j N
    obtain ⟨Cdj, hCdj_pos, hCdj⟩ := schwartz_fderiv_component_schwartz f hf_smooth hf_schwartz j N 1
    -- Uniform bounds on fderiv of K and L convolutions
    obtain ⟨CKj, hCKj_pos, hCKj⟩ := hK_fderiv_bdd j
    obtain ⟨CLj, hCLj_pos, hCLj⟩ := hL_fderiv_bdd j
    -- Schwartz decay of f with polynomial weight N
    obtain ⟨Mf_N, hMf_N_pos, hMf_N⟩ := hf_decay N
    refine ⟨Mdj_N * CKj + MK * Cdj + Mf_N * CLj + (ML + 1) * Cf + 1, by positivity, fun v => ?_⟩
    -- Product rule: fderiv (a * b - c * d) = a • fderiv b + b • fderiv a - (c • fderiv d + d • fderiv c)
    have h_ab := (ha_diff j v).hasFDerivAt.mul (hK_diff j v).hasFDerivAt
    have h_cd := (hf_diff v).hasFDerivAt.mul (hL_diff j v).hasFDerivAt
    have h_fderiv := (h_ab.sub h_cd).fderiv
    rw [h_fderiv]
    -- ‖a•K' + K•a' - (f•L' + L•f')‖ * (1+‖v‖)^N
    calc ‖fderiv ℝ f v (Pi.single j 1) • fderiv ℝ (fun v => ∫ w,
            landauMatrix coulombKernel (v - w) i j * f w) v +
          (∫ w, landauMatrix coulombKernel (v - w) i j * f w) •
            fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1)) v -
          (f v • fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j *
            fderiv ℝ f w (Pi.single j 1)) v +
          (∫ w, landauMatrix coulombKernel (v - w) i j *
            fderiv ℝ f w (Pi.single j 1)) • fderiv ℝ f v)‖ * (1 + ‖v‖) ^ N
        ≤ (‖fderiv ℝ f v (Pi.single j 1) • fderiv ℝ (fun v => ∫ w,
              landauMatrix coulombKernel (v - w) i j * f w) v‖ +
           ‖(∫ w, landauMatrix coulombKernel (v - w) i j * f w) •
              fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1)) v‖ +
           ‖f v • fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j *
              fderiv ℝ f w (Pi.single j 1)) v‖ +
           ‖(∫ w, landauMatrix coulombKernel (v - w) i j *
              fderiv ℝ f w (Pi.single j 1)) • fderiv ℝ f v‖) * (1 + ‖v‖) ^ N := by
          gcongr; exact le_trans (norm_sub_le _ _) (add_le_add_right (norm_add_le _ _) _)
      _ = (|fderiv ℝ f v (Pi.single j 1)| * ‖fderiv ℝ (fun v => ∫ w,
              landauMatrix coulombKernel (v - w) i j * f w) v‖ +
           |∫ w, landauMatrix coulombKernel (v - w) i j * f w| *
              ‖fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1)) v‖ +
           |f v| * ‖fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j *
              fderiv ℝ f w (Pi.single j 1)) v‖ +
           |∫ w, landauMatrix coulombKernel (v - w) i j *
              fderiv ℝ f w (Pi.single j 1)| * ‖fderiv ℝ f v‖) * (1 + ‖v‖) ^ N := by
          simp [norm_smul, Real.norm_eq_abs]
      _ ≤ (Mdj_N * CKj + MK * Cdj + Mf_N * CLj + (ML + 1) * Cf) * 1 + 0 := by
          rw [mul_one, add_zero]
          -- Convert iteratedFDeriv 1 norms to fderiv norms
          have hCf_v : ‖fderiv ℝ f v‖ * (1 + ‖v‖) ^ N ≤ Cf := by
            have : ‖fderiv ℝ f v‖ = ‖iteratedFDeriv ℝ 1 f v‖ := by
              rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := fderiv ℝ f),
                  norm_iteratedFDeriv_fderiv]
            rw [this]; exact hCf v
          have hCdj_v : ‖fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1)) v‖ *
              (1 + ‖v‖) ^ N ≤ Cdj := by
            have : ‖fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1)) v‖ =
                ‖iteratedFDeriv ℝ 1 (fun w => fderiv ℝ f w (Pi.single j 1)) v‖ := by
              rw [← norm_iteratedFDeriv_zero
                    (𝕜 := ℝ) (f := fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1))),
                  norm_iteratedFDeriv_fderiv]
            rw [this]; exact hCdj v
          -- Each term: one factor has Schwartz decay × P, the other is bounded
          -- t1: |∂_j f(v)| * ‖DK(v)‖ * P ≤ (|∂_j f(v)| * P) * ‖DK(v)‖ ≤ Mdj_N * CKj
          have hMdj_N_v : |fderiv ℝ f v (Pi.single j 1)| * (1 + ‖v‖) ^ N ≤ Mdj_N := by
            simpa [norm_iteratedFDeriv_zero] using hMdj_N v
          have t1 := mul_le_mul hMdj_N_v (hCKj v)
            (by positivity) (le_trans (by positivity) hMdj_N_v)
          -- t2: |K(v)| * ‖D(∂_j f)(v)‖ * P ≤ |K(v)| * (‖D(∂_j f)(v)‖ * P) ≤ MK * Cdj
          have t2 := mul_le_mul (hK_sup j v) hCdj_v
            (by positivity) (le_trans (abs_nonneg _) (hK_sup j v))
          -- t3: |f(v)| * ‖DL(v)‖ * P ≤ (|f(v)| * P) * ‖DL(v)‖ ≤ Mf_N * CLj
          have hMf_N_v : |f v| * (1 + ‖v‖) ^ N ≤ Mf_N := by
            simpa [norm_iteratedFDeriv_zero] using hMf_N v
          have t3 := mul_le_mul hMf_N_v (hCLj v)
            (by positivity) (le_trans (by positivity) hMf_N_v)
          -- t4: |L(v)| * ‖Df(v)‖ * P ≤ |L(v)| * (‖Df(v)‖ * P) ≤ (ML+1) * Cf
          have t4 := mul_le_mul (hL_sup j v) hCf_v
            (by positivity) (le_trans (abs_nonneg _) (hL_sup j v))
          nlinarith [t1, t2, t3, t4]
      _ ≤ Mdj_N * CKj + MK * Cdj + Mf_N * CLj + (ML + 1) * Cf + 1 := by linarith
  -- Sum over j
  obtain ⟨C0, hC0, h0⟩ := h_per_term 0
  obtain ⟨C1, hC1, h1⟩ := h_per_term 1
  obtain ⟨C2, hC2, h2⟩ := h_per_term 2
  refine ⟨C0 + C1 + C2 + 1, by positivity, fun v => ?_⟩
  -- fderiv of sum
  have h_sum_diff : ∀ j, DifferentiableAt ℝ (fun v => fderiv ℝ f v (Pi.single j 1) *
      (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
     f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
      fderiv ℝ f w (Pi.single j 1))) v :=
    fun j => ((ha_diff j v).hasFDerivAt.mul (hK_diff j v).hasFDerivAt).differentiableAt.sub
      ((hf_diff v).hasFDerivAt.mul (hL_diff j v).hasFDerivAt).differentiableAt
  have h_fderiv_sum : fderiv ℝ (fun v => ∑ j : Fin 3, (fderiv ℝ f v (Pi.single j 1) *
      (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
     f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
      fderiv ℝ f w (Pi.single j 1)))) v =
    ∑ j : Fin 3, fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1) *
      (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
     f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
      fderiv ℝ f w (Pi.single j 1))) v :=
    fderiv_sum (fun j _ => h_sum_diff j)
  rw [h_fderiv_sum]
  calc ‖∑ j : Fin 3, fderiv ℝ _ v‖ * (1 + ‖v‖) ^ N
      ≤ (∑ j : Fin 3, ‖fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1) *
          (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
         f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
          fderiv ℝ f w (Pi.single j 1))) v‖) * (1 + ‖v‖) ^ N := by
        gcongr; exact norm_sum_le _ _
    _ = ∑ j : Fin 3, ‖fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1) *
          (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
         f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
          fderiv ℝ f w (Pi.single j 1))) v‖ * (1 + ‖v‖) ^ N := by
        rw [Fin.sum_univ_three]; ring
    _ ≤ C0 + C1 + C2 := by
        rw [Fin.sum_univ_three]; linarith [h0 v, h1 v, h2 v]
    _ ≤ C0 + C1 + C2 + 1 := le_add_of_nonneg_right (by positivity)

/-- The product fderiv(flux_i)(v) * log(f(v)) is integrable for the Coulomb kernel.
    Uses Schwartz decay of the flux derivative and polynomial growth of log(f). -/
lemma coulomb_ibp_df_g_integrable
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (hLogBound : ∃ C K, ∀ v, |Real.log (f v)| ≤ C * (1 + ‖v‖) ^ K)
    (i : Fin 3) :
    Integrable (fun v =>
      fderiv ℝ (fun v' => (∫ w, mulVec (landauMatrix coulombKernel (v' - w))
        (f w • vGrad f v' - f v' • vGrad f w)) i) v (Pi.single i 1) *
      (Real.log ∘ f) v) := by
  obtain ⟨C_log, K_log, hLB⟩ := hLogBound
  -- Flux derivative Schwartz decay: ‖fderiv(flux_i)(v)‖ * (1+‖v‖)^(K_log+4) ≤ C_fd
  obtain ⟨C_fd, hC_fd, hfd_bound⟩ := coulomb_flux_deriv_schwartz_decay f hf_pos hf_smooth
    hf_schwartz i (K_log + 4)
  -- Apply domination by C_fd * C_log / (1+‖v‖)^4
  apply (inverse_poly_integrable (C_fd * C_log)).mono'
  · apply AEStronglyMeasurable.mul
    · exact ((coulomb_flux_differentiable f hf_pos hf_smooth hf_schwartz i).fderiv
        |>.continuous.clm_apply continuous_const).aestronglyMeasurable
    · exact (hf_smooth.continuous.log (fun v => ne_of_gt (hf_pos v))).aestronglyMeasurable
  · filter_upwards with v
    rw [Real.norm_eq_abs, abs_mul, Function.comp_apply]
    have hv_pos : (0 : ℝ) < (1 + ‖v‖) ^ 4 := by positivity
    rw [le_div_iff₀ hv_pos]
    -- |fderiv(flux)(v)(e_i)| ≤ ‖fderiv(flux)(v)‖ ≤ C_fd / (1+‖v‖)^(K_log+4)
    have h1 : |fderiv ℝ (fun v' => (∫ w, mulVec (landauMatrix coulombKernel (v' - w))
        (f w • vGrad f v' - f v' • vGrad f w)) i) v (Pi.single i 1)| ≤
        C_fd / (1 + ‖v‖) ^ (K_log + 4) := by
      have hv_pos' : (0 : ℝ) < (1 + ‖v‖) ^ (K_log + 4) := by positivity
      rw [le_div_iff₀ hv_pos']
      calc |fderiv ℝ _ v (Pi.single i 1)|
          ≤ ‖fderiv ℝ _ v‖ * ‖Pi.single i (1 : ℝ)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ _ v‖ * 1 := by
            gcongr; simp [Pi.norm_single]
        _ = ‖fderiv ℝ _ v‖ := mul_one _
        _ ≤ ‖fderiv ℝ _ v‖ * (1 + ‖v‖) ^ (K_log + 4) :=
            le_mul_of_one_le_right (norm_nonneg _) (one_le_pow_of_one_le (by linarith [norm_nonneg v]) _)
        _ ≤ C_fd := hfd_bound v
    -- Combine: |deriv| * |log f| ≤ (C_fd/(1+‖v‖)^(K+4)) * (C_log*(1+‖v‖)^K) = C_fd*C_log/(1+‖v‖)^4
    calc |fderiv ℝ _ v (Pi.single i 1)| * |Real.log (f v)|
        ≤ C_fd / (1 + ‖v‖) ^ (K_log + 4) * (C_log * (1 + ‖v‖) ^ K_log) :=
          mul_le_mul h1 (hLB v) (abs_nonneg _) (div_nonneg (le_of_lt hC_fd) (by positivity))
      _ = C_fd * C_log / (1 + ‖v‖) ^ 4 * (1 + ‖v‖) ^ 4 := by
          rw [div_mul_cancel₀]; exact ne_of_gt hv_pos
      _ ≤ C_fd * C_log * (1 + ‖v‖) ^ 4 := by
          rw [div_mul_cancel₀]; exact ne_of_gt hv_pos

end VML
