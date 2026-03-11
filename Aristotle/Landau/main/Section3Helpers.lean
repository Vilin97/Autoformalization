import Aristotle.Landau.main.Defs
import Aristotle.Landau.main.Section2
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Helper Lemmas for Section 3

Gaussian normalization, gradient of exponential-quadratic functions, Maxwellian
characterization, and derivative bounds used in the nullspace analysis of the
Landau operator.
-/

open Matrix Finset BigOperators Real MeasureTheory

noncomputable section

namespace VML

-- ============================================================================
-- Part 1: vGrad_exp_quadratic
-- ============================================================================

/-- The velocity gradient of exp(a + b·v + c·|v|²) equals exp(a + b·v + c·|v|²)·(b + 2c·v).
    Proved by Aristotle (Harmonic). -/
lemma vGrad_exp_quadratic (a : ℝ) (b : Fin 3 → ℝ) (c : ℝ) :
    ∀ v : Fin 3 → ℝ,
    vGrad (fun w => Real.exp (a + dotProduct b w + c * normSq w)) v =
    Real.exp (a + dotProduct b v + c * normSq v) • (b + (2 * c) • v) := by
  unfold vGrad normSq
  intro v
  ext i
  erw [ fderiv_exp ]
  norm_num [ dotProduct, Fin.sum_univ_three ]
  ring
  · field_simp
    erw [ HasFDerivAt.fderiv (by
      exact HasFDerivAt.add
        (HasFDerivAt.add
          (HasFDerivAt.add
            (HasFDerivAt.add
              (HasFDerivAt.add
                (HasFDerivAt.add
                  (hasFDerivAt_const _ _)
                  (HasFDerivAt.mul
                    (hasFDerivAt_const _ _)
                    (hasFDerivAt_apply _ _)))
                (HasFDerivAt.mul
                  (hasFDerivAt_apply _ _ |> HasFDerivAt.pow <| 2)
                  (hasFDerivAt_const _ _)))
              (HasFDerivAt.mul
                (hasFDerivAt_const _ _)
                (hasFDerivAt_apply _ _)))
            (HasFDerivAt.mul
              (hasFDerivAt_const _ _)
              (hasFDerivAt_apply _ _ |> HasFDerivAt.pow <| 2)))
          (HasFDerivAt.mul
            (hasFDerivAt_const _ _)
            (hasFDerivAt_apply _ _)))
        (HasFDerivAt.mul
          (hasFDerivAt_const _ _)
          (hasFDerivAt_apply _ _ |> HasFDerivAt.pow <| 2))) ]
    ring
    fin_cases i <;> simp +decide [ Pi.single_apply ] <;> ring!
  · norm_num [ dotProduct ]
    fun_prop (disch := norm_num)

/-- Gaussian normalization: if f(v) = exp(a₀ + c₀|v|²) with c₀ < 0 and ∫f = ρ_ion,
    then f = equilibriumMaxwellian ρ_ion T with T = -1/(2c₀).
    Proved by Aristotle (project 1236b757). -/
lemma gaussian_normalization_maxwellian
    (ρ_ion a₀ c₀ : ℝ) (hρ : 0 < ρ_ion) (hc₀ : c₀ < 0)
    (f : (Fin 3 → ℝ) → ℝ)
    (hf : ∀ v, f v = Real.exp (a₀ + c₀ * normSq v))
    (hf_int : ∫ v : Fin 3 → ℝ, f v = ρ_ion) :
    ∀ v, f v = equilibriumMaxwellian ρ_ion (-1 / (2 * c₀)) v := by
  -- Proved by Aristotle (project 1236b757), adapted to standard Mathlib generalize_proofs.
  have h_m_int : ∫ v : Fin 3 → ℝ, Real.exp (c₀ * (normSq v)) = (Real.pi / (-c₀)) ^ ((3 : ℝ) / 2) := by
    have h_gauss : ∫ v : Fin 3 → ℝ, Real.exp (c₀ * normSq v) = (∏ i : Fin 3, ∫ v : ℝ, Real.exp (c₀ * v^2)) := by
      have h_fubini : ∫ v : Fin 3 → ℝ, Real.exp (c₀ * normSq v) = ∫ v : Fin 3 → ℝ, (∏ i : Fin 3, Real.exp (c₀ * (v i) ^ 2)) := by
        norm_num [ ← Real.exp_sum, normSq ]
        norm_num [ dotProduct, Fin.sum_univ_three ] ; congr ; ext ; ring
      generalize_proofs at *; (
      erw [ h_fubini, ← MeasureTheory.integral_fintype_prod_eq_prod ] ; aesop;)
    generalize_proofs at *; (
    have := integral_gaussian ( -c₀)
    simp_all +decide [ div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm ]
    ring; (
    rw [ Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by nlinarith [ Real.pi_pos, mul_inv_cancel₀ hc₀.ne ]) ]
    norm_num;) ;)
  simp_all +decide [ Real.exp_add, MeasureTheory.integral_const_mul ]
  intro v; rw [ ← hf_int ] ; unfold equilibriumMaxwellian; ring
  norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt (Real.rpow_pos_of_pos (show 0 < - (Real.pi * c₀⁻¹) by nlinarith [ Real.pi_pos, mul_inv_cancel₀ (ne_of_lt hc₀) ]) _) ]


/-- Gaussian first moment: ∫ vᵢ exp(a+b·v+c|v|²) = (-bᵢ/(2c)) · ∫ exp(a+b·v+c|v|²).
    Proved by Aristotle (project 4c5e7998). -/
lemma gaussian_first_moment (a : ℝ) (b : Fin 3 → ℝ) (c : ℝ) (hc : c < 0)
    (hf_int : Integrable (fun v : Fin 3 → ℝ => Real.exp (a + dotProduct b v + c * normSq v))) :
    ∀ i : Fin 3, ∫ v, v i * Real.exp (a + dotProduct b v + c * normSq v) =
      (-b i / (2 * c)) * ∫ v, Real.exp (a + dotProduct b v + c * normSq v) := by
  -- Proved by Aristotle (project 4c5e7998), adapted with erw for Fubini steps.
  intro i
  have h_gauss : ∫ v : Fin 3 → ℝ, v i * Real.exp (a + b ⬝ᵥ v + c * normSq v) = (-b i / (2 * c)) * (∫ v : Fin 3 → ℝ, Real.exp (a + b ⬝ᵥ v + c * normSq v)) := by
    have h_gauss_integral : ∀ a b c : ℝ, c < 0 → ∫ v : ℝ, v * Real.exp (a + b * v + c * v^2) = (-b / (2 * c)) * (∫ v : ℝ, Real.exp (a + b * v + c * v^2)) := by
      intro a b c hc_neg
      have h_gauss_integral : ∫ v : ℝ, (v + b / (2 * c)) * Real.exp (a + b * v + c * v^2) = 0 := by
        suffices h_subst : ∫ v : ℝ, (v + b / (2 * c)) * Real.exp (a + b * v + c * v^2) = ∫ u : ℝ, u * Real.exp (a - b^2 / (4 * c) + c * u^2) by
          have h_odd : ∀ f : ℝ → ℝ, (∀ x, f (-x) = -f x) → ∫ x : ℝ, f x = 0 := by
            intro f hf_odd
            have h_symm : ∫ x : ℝ, f x = ∫ x : ℝ, f (-x) := by
              rw [ MeasureTheory.integral_neg_eq_self ]
            have h_zero : ∫ x : ℝ, f x = -∫ x : ℝ, f x := by
              rw [ ← MeasureTheory.integral_neg ] ; aesop
            linarith [h_zero]
          exact h_subst.trans (h_odd _ fun x => by ring)
        rw [ ← MeasureTheory.integral_add_right_eq_self _ ( -b / (2 * c) ) ]
        congr
        ext
        ring
        norm_num [ hc_neg.ne ]
        ring
        grind
      simp_all +decide [ add_mul, div_eq_mul_inv, MeasureTheory.integral_const_mul ]
      rw [ MeasureTheory.integral_add ] at h_gauss_integral <;> norm_num at *
      · rw [ MeasureTheory.integral_const_mul ] at h_gauss_integral ; linarith
      · have h_integrable : MeasureTheory.Integrable (fun v : ℝ => v * Real.exp (c * v^2 + b * v)) MeasureTheory.MeasureSpace.volume := by
          have h_gauss : ∀ v : ℝ, |v * Real.exp (c * v^2 + b * v)| ≤ |v| * Real.exp (c * v^2 / 2) * Real.exp (b^2 / (2 * |c|)) := by
            intro v
            simp [abs_mul]
            rw [ mul_assoc, ← Real.exp_add ]
            ring_nf
            norm_num [ abs_of_neg hc_neg ]
            ring_nf
            norm_num [ hc_neg ]; (
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr <| by nlinarith [ sq_nonneg (v * c + b), mul_inv_cancel₀ (ne_of_lt hc_neg) ]) (abs_nonneg v))
          have h_integrable : MeasureTheory.Integrable (fun v : ℝ => |v| * Real.exp (c * v^2 / 2)) MeasureTheory.MeasureSpace.volume := by
            have h_integrable : MeasureTheory.Integrable (fun v : ℝ => v * Real.exp (c * v^2 / 2)) MeasureTheory.MeasureSpace.volume := by
              have := @integrable_rpow_mul_exp_neg_mul_sq
              convert @this ( -c / 2) (by linarith) 1 (by norm_num) using 3 ; ring
              · norm_num
              · ring
            convert h_integrable.norm using 2 ; norm_num [ abs_mul, abs_of_nonneg, Real.exp_nonneg ]
          refine MeasureTheory.Integrable.mono' ?_ ?_ ?_
          exacts [
            fun v => |v| * Real.exp (c * v ^ 2 / 2) * Real.exp (b ^ 2 / (2 * |c|)),
            h_integrable.mul_const _,
            Continuous.aestronglyMeasurable (by continuity),
            Filter.Eventually.of_forall h_gauss ]
        convert h_integrable.mul_const (Real.exp a) using 2 ; ring
        rw [ mul_assoc, ← Real.exp_add ]
      · have h_gauss_integral : ∫ v : ℝ, Real.exp (a + b * v + c * v^2) = Real.sqrt (Real.pi / (-c)) * Real.exp (a - b^2 / (4 * c)) := by
          have h_gauss_integral : ∫ v : ℝ, Real.exp (c * (v - (-b / (2 * c)))^2) = Real.sqrt (Real.pi / (-c)) := by
            convert integral_gaussian ( -c) using 1 <;> norm_num [ hc_neg.le ]
            rw [ eq_comm, ← MeasureTheory.integral_sub_right_eq_self ]
          rw [ ← h_gauss_integral, ← MeasureTheory.integral_mul_const ] ; congr ; ext v ; ring
          rw [ ← Real.exp_add ] ; norm_num [ sq, mul_assoc, hc_neg.ne ] ; ring
        exact MeasureTheory.Integrable.const_mul (by
          exact (by
            contrapose! h_gauss_integral
            rw [ MeasureTheory.integral_undef h_gauss_integral ]
            exact ne_of_lt (mul_pos
              (Real.sqrt_pos.mpr
                (div_pos Real.pi_pos (neg_pos.mpr hc_neg)))
              (Real.exp_pos _)))) _
    have h_gauss_integral_component :
        ∀ i : Fin 3,
        ∫ v : Fin 3 → ℝ, v i * Real.exp (a + b ⬝ᵥ v + c * normSq v) =
        (∫ v : ℝ, v * Real.exp (a + b i * v + c * v^2)) *
        (∏ j ∈ Finset.univ.erase i,
          ∫ v : ℝ, Real.exp (b j * v + c * v^2)) := by
      intro i
      have h_fubini :
          ∫ v : Fin 3 → ℝ,
            v i * Real.exp (a + b ⬝ᵥ v + c * normSq v) =
          ∫ v : Fin 3 → ℝ,
            (∏ j, (if j = i
              then v j * Real.exp (a + b j * v j + c * v j^2)
              else Real.exp (b j * v j + c * v j^2))) := by
        simp +decide [ Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ]
        simp +decide [ mul_assoc, ← Real.exp_sum, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul, normSq ]
        simp +decide [ ← Real.exp_add, Fin.sum_univ_three, dotProduct ] ; congr ; ext ; ring!
      have h_fubini2 :
          ∫ v : Fin 3 → ℝ, (∏ j, (if j = i
            then v j * Real.exp (a + b j * v j + c * v j^2)
            else Real.exp (b j * v j + c * v j^2))) =
          (∏ j, ∫ v : ℝ, (if j = i
            then v * Real.exp (a + b j * v + c * v^2)
            else Real.exp (b j * v + c * v^2))) := by
        erw [← MeasureTheory.integral_fintype_prod_eq_prod]; rfl
      simp_all +decide [ Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i) ]
      exact Or.inl (by rw [ Finset.sdiff_singleton_eq_erase ]
                       exact Finset.prod_congr rfl fun x hx => by aesop)
    have h_gauss_integral_component2 : ∫ v : Fin 3 → ℝ, Real.exp (a + b ⬝ᵥ v + c * normSq v) = (∏ j : Fin 3, ∫ v : ℝ, Real.exp (b j * v + c * v^2)) * Real.exp a := by
      have h_gauss_integral_component3 : ∫ v : Fin 3 → ℝ, Real.exp (a + b ⬝ᵥ v + c * normSq v) = (∫ v : Fin 3 → ℝ, Real.exp (a) * (∏ j : Fin 3, Real.exp (b j * v j + c * v j^2))) := by
        simp +decide [ normSq, dotProduct, Fin.sum_univ_three, ← Real.exp_sum, ← Real.exp_add ]
        congr
        ext
        ring
      rw [ h_gauss_integral_component3, mul_comm ]
      rw [ MeasureTheory.integral_const_mul ]
      congr 1
      erw [← MeasureTheory.integral_fintype_prod_eq_prod]; rfl
    simp_all +decide [ Finset.prod_erase_mul _ _ (Finset.mem_univ i) ]
    rw [ ← Finset.mul_prod_erase _ _ (Finset.mem_univ i) ] ; ring
    simp +decide [ Real.exp_add, mul_add, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm, MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const ]
  exact h_gauss

/-- Flux factoring: f(w)∇f(v) - f(v)∇f(w) = f(v)f(w)(∇logf(v) - ∇logf(w)). -/
lemma analysis_fluxFactor
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) :
    ∀ v w, f w • vGrad f v - f v • vGrad f w =
    (f v * f w) • (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w) := by
  -- Proved by Aristotle (Harmonic)
  intro v w
  have h_log_grad : ∀ (v : (Fin 3) → ℝ), VML.vGrad (Real.log ∘ f) v = (1 / f v) • VML.vGrad f v := by
    intro v; ext i; by_cases H : DifferentiableAt ℝ f v <;> simp_all +decide [ VML.vGrad, fderiv_deriv ] ; ring
    · erw [ fderiv_comp ] <;> norm_num [ H, ne_of_gt (hf_pos v) ]; ring
    · rw [ fderiv_zero_of_not_differentiableAt ]
      · rw [ fderiv_zero_of_not_differentiableAt H ] ; norm_num
      · exact fun h => H <| by simpa [ Real.exp_log (hf_pos _) ] using h.exp.congr_of_eventuallyEq (by filter_upwards [ ] using fun _ => by simp +decide [ Real.exp_log (hf_pos _) ])
  simp +decide [ h_log_grad, mul_sub, smul_sub, mul_assoc, mul_comm, mul_left_comm, ne_of_gt (hf_pos _) ]
  simp +decide [ mul_assoc, mul_comm (f v), mul_left_comm (f v), ne_of_gt (hf_pos _), smul_smul ]

/-- Scalar factors through mulVec and dotProduct:
    y ⬝ (A *ᵥ (c • y)) = c * (y ⬝ (A *ᵥ y)). -/
lemma analysis_scalarFactor
    (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ) :
    ∀ v w, dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
      (mulVec (landauMatrix Ψ (v - w))
        ((f v * f w) • (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w))) =
    f v * f w *
      dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
        (mulVec (landauMatrix Ψ (v - w))
          (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)) := by
  -- Proved by Aristotle (Harmonic)
  simp +decide [ dotProduct, Matrix.mulVec ]
  simp +decide [ mul_assoc, mul_left_comm, Finset.mul_sum _ _ _ ]

/-- Nonneg double integral zero → pointwise zero. -/
lemma analysis_nonneg_dbl_zero
    (g : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ)
    (hnn : ∀ v w, 0 ≤ g v w)
    (hcont : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => g p.1 p.2))
    (hint_inner : ∀ v, Integrable (g v))
    (hint_outer : Integrable (fun v => ∫ w, g v w))
    (hint : (∫ v, ∫ w, g v w) = 0) :
    ∀ v w, g v w = 0 := by
  -- Proved by Aristotle (Harmonic)
  have h_fubini : ∫ v, (∫ w, g v w) = 0 := hint
  rw [ MeasureTheory.integral_eq_zero_iff_of_nonneg_ae ] at h_fubini
  · have h_zero_ae : ∀ᵐ v ∂MeasureTheory.volume, ∀ w, g v w = 0 := by
      filter_upwards [ h_fubini ] with v hv w
      contrapose! hv
      simp_all +decide [ ne_of_gt, MeasureTheory.integral_pos_iff_support_of_nonneg_ae ]
      rw [ MeasureTheory.integral_eq_zero_iff_of_nonneg_ae ]
      · obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ w', dist w' w < ε → g v w' ≠ 0 := by
          exact Metric.mem_nhds_iff.mp
            (hcont.continuousAt.comp
              (continuousAt_const.prodMk continuousAt_id)
            |> fun h => h.eventually_ne hv)
            |> fun ⟨ ε, εpos, hε ⟩ =>
              ⟨ ε, εpos, fun w' hw' => hε <| by simpa using hw' ⟩
        exact ne_of_gt (lt_of_lt_of_le
          (by simpa using (Metric.measure_ball_pos _ _ hε.1))
          (MeasureTheory.measure_mono
            (show { a : Fin 3 → ℝ | ¬g v a = 0 } ⊇ Metric.ball w ε
              from fun x hx => hε.2 x hx)))
      · exact Filter.Eventually.of_forall fun x => hnn v x
      · exact hint_inner v
    intro v w; by_contra h_nonzero; push_neg at h_nonzero
    obtain ⟨U, hU_open, hU_v, hU_nonzero⟩ : ∃ U : Set (Fin 3 → ℝ), IsOpen U ∧ v ∈ U ∧ ∀ u ∈ U, g u w ≠ 0 := by
      exact ⟨ { u | g u w ≠ 0 }, isOpen_ne.preimage (show Continuous fun u => g u w from hcont.comp (continuous_id.prodMk continuous_const) ), h_nonzero, fun u hu => hu ⟩
    exact absurd h_zero_ae (ne_of_gt (lt_of_lt_of_le
      (by exact (hU_open.measure_pos
        (MeasureTheory.MeasureSpace.volume) ⟨ v, hU_v ⟩))
      (MeasureTheory.measure_mono
        (show U ⊆ { a : Fin 3 → ℝ | ¬∀ w : Fin 3 → ℝ, g a w = 0 }
          from fun u hu => fun h => hU_nonzero u hu <| h w))))
  · exact Filter.Eventually.of_forall fun v => MeasureTheory.integral_nonneg fun w => hnn v w
  · exact hint_outer

/-- Gaussian integrability: exp(a₀+b·v+c₀|v|²) with f integrable implies c₀ < 0. -/
lemma analysis_gaussian_integrability
    (f : (Fin 3 → ℝ) → ℝ) (a₀ : ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_int : Integrable f)
    (hf_exp : ∀ v, f v = Real.exp (a₀ + dotProduct b v + c₀ * normSq v)) :
    c₀ < 0 := by
  -- Proved by Aristotle (Harmonic)
  contrapose! hf_int
  by_contra h_contra
  have h_integrable : MeasureTheory.Integrable (fun v : Fin 3 → ℝ => Real.exp (a₀ + b ⬝ᵥ v)) MeasureTheory.MeasureSpace.volume := by
    refine h_contra.mono' ?_ ?_
    · fun_prop
    · simp_all +decide [ Real.exp_pos ]
      exact Filter.Eventually.of_forall fun x => mul_nonneg hf_int (by
        show 0 ≤ VML.normSq x
        unfold VML.normSq
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  have h_integrable : MeasureTheory.Integrable (fun v : Fin 3 → ℝ => Real.exp (b ⬝ᵥ v)) MeasureTheory.MeasureSpace.volume := by
    convert h_integrable.const_mul (Real.exp ( -a₀) ) using 2 ; rw [ ← Real.exp_add ] ; ring
  have h_integrable : MeasureTheory.Integrable (fun v : ℝ => Real.exp (b 0 * v)) MeasureTheory.MeasureSpace.volume := by
    have h_integrable :
        MeasureTheory.Integrable
          (fun v : Fin 3 → ℝ => Real.exp (b ⬝ᵥ v))
          MeasureTheory.MeasureSpace.volume →
        MeasureTheory.Integrable
          (fun v : ℝ => Real.exp (b 0 * v))
          MeasureTheory.MeasureSpace.volume := by
      intro h_integrable
      have h_integrable :
          MeasureTheory.Integrable
            (fun v : ℝ × (Fin 2 → ℝ) =>
              Real.exp (b 0 * v.1 + ∑ i : Fin 2, b (Fin.succ i) * v.2 i))
            (MeasureTheory.MeasureSpace.volume.prod
              MeasureTheory.MeasureSpace.volume) := by
        convert h_integrable using 1
        have h_iso :
            (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ)) =
            MeasureTheory.Measure.map
              (fun v : ℝ × (Fin 2 → ℝ) => Fin.cons v.1 v.2)
              (MeasureTheory.volume.prod MeasureTheory.volume) := by
          simp +decide [ MeasureTheory.MeasureSpace.volume ]
          erw [ MeasureTheory.Measure.pi_eq ]
          intro s hs
          erw [ MeasureTheory.Measure.map_apply ]
          · simp +decide [ Set.preimage, Fin.forall_fin_succ ]
            erw [ show
              { x : ℝ × (Fin 2 → ℝ) |
                x.1 ∈ s 0 ∧ x.2 0 ∈ s 1 ∧ x.2 1 ∈ s 2 } =
              (s 0 ×ˢ { x : Fin 2 → ℝ | x 0 ∈ s 1 ∧ x 1 ∈ s 2 })
              by ext ; aesop,
              MeasureTheory.Measure.prod_prod ]
            simp +decide [ Fin.prod_univ_three ]
            erw [ show
              { x : Fin 2 → ℝ | x 0 ∈ s 1 ∧ x 1 ∈ s 2 } =
              (Set.pi Set.univ fun i : Fin 2 =>
                if i = 0 then s 1 else s 2)
              by ext; simp +decide [ Fin.forall_fin_two ] ]
            erw [ MeasureTheory.Measure.pi_pi ]
            simp +decide [ mul_assoc ]
          · exact measurable_pi_iff.mpr fun i => by
              fin_cases i <;> [
                exact measurable_fst
                exact measurable_pi_iff.mp measurable_snd 0
                exact measurable_pi_iff.mp measurable_snd 1 ]
          · exact MeasurableSet.univ_pi hs
        rw [ h_iso, MeasureTheory.integrable_map_measure ]
        · rfl
        · exact Continuous.aestronglyMeasurable (by exact Real.continuous_exp.comp <| continuous_const.dotProduct continuous_id')
        · refine Continuous.aemeasurable ?_
          exact continuous_pi_iff.mpr fun i => by
            fin_cases i <;> [
              exact continuous_fst
              exact continuous_apply 0 |> Continuous.comp <| continuous_snd
              exact continuous_apply 1 |> Continuous.comp <| continuous_snd ]
      rw [ MeasureTheory.integrable_prod_iff ] at h_integrable
      · simp_all +decide [ Real.exp_add, MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const ]
        by_cases h : ∫ (a : Fin 2 → ℝ), Real.exp (b 1 * a 0) * Real.exp (b 2 * a 1) = 0 <;> simp_all +decide [ MeasureTheory.integrable_const_mul_iff ]
        · rw [ MeasureTheory.integral_eq_zero_iff_of_nonneg (fun _ => by positivity) ] at h
          · exact absurd (h.exists) (by norm_num [ Real.exp_ne_zero ])
          · exact h_integrable
        · convert h_integrable.2.div_const (∫ (a : Fin 2 → ℝ), Real.exp (b 1 * a 0) * Real.exp (b 2 * a 1) ) using 1
          aesop
      · exact h_integrable.1
    exact h_integrable ‹_›
  by_cases hb0 : b 0 = 0
  · simp_all +decide [ MeasureTheory.integrable_const_iff ]
    exact absurd (h_integrable.measure_univ_lt_top) (by norm_num)
  · have := h_integrable.comp_smul (inv_ne_zero hb0)
    simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ]
    convert absurd (this.lintegral_lt_top) _ ; norm_num [ Real.exp_pos ]
    have h_exp_inf : ∫⁻ (x : ℝ), ENNReal.ofReal (Real.exp x) ≥ ∫⁻ (x : ℝ) in Set.Ioi 0, ENNReal.ofReal (Real.exp x) := by
      exact MeasureTheory.setLIntegral_le_lintegral _ _
    exact le_top.antisymm (h_exp_inf.trans' <| by exact le_trans (by norm_num) <| MeasureTheory.setLIntegral_mono' measurableSet_Ioi fun x hx => ENNReal.ofReal_le_ofReal <| Real.one_le_exp hx.out.le)

/-- Smoothness of velocity gradient: if g is smooth, so is vGrad g. -/
lemma analysis_vGrad_smooth
    (g : (Fin 3 → ℝ) → ℝ) (hg : ContDiff ℝ 3 g) :
    ContDiff ℝ 2 (fun v => vGrad g v) := by
  -- Proved by Aristotle (Harmonic)
  refine contDiff_pi.2 fun i => ?_
  apply_rules [ ContDiff.fderiv_apply, contDiff_id, contDiff_const ]
  fun_prop (disch := solve_by_elim)
  norm_num

-- ============================================================================
-- Polynomial Extraction Lemmas
--
-- These pure algebra lemmas extract coefficient equations from polynomial
-- identities that hold for all v ∈ ℝ³.
-- ============================================================================

/-- Polynomial cubic extraction: cubic part of a vanishing polynomial vanishes.
    Proved by Aristotle (Harmonic). -/
lemma poly_cubic_extraction
    (d_c : Fin 3 → ℝ) (K : Fin 3 → Fin 3 → ℝ) (d_lin : Fin 3 → ℝ) (C : ℝ)
    (h : ∀ v : Fin 3 → ℝ,
      dotProduct v d_c * normSq v +
      (∑ i : Fin 3, ∑ j : Fin 3, v i * v j * K i j) +
      dotProduct v d_lin + C = 0) :
    ∀ v : Fin 3 → ℝ, dotProduct v d_c * normSq v = 0 := by
  intro v
  by_contra h_nonzero
  have hv : v ⬝ᵥ d_c * normSq v ≠ 0 := h_nonzero
  have h_poly_zero : ∀ t : ℝ, (t • v) ⬝ᵥ d_c * normSq (t • v) +
      ∑ i, ∑ j, (t • v i) * (t • v j) * (K i j) +
      (t • v) ⬝ᵥ d_lin + C = 0 := fun t => h _
  simp [normSq] at h_poly_zero
  have h_cubic_zero : ∀ t : ℝ, t^3 * (v ⬝ᵥ d_c * (v ⬝ᵥ v)) +
      t^2 * (∑ i, ∑ j, (v i) * (v j) * (K i j)) +
      t * (v ⬝ᵥ d_lin) + C = 0 := by
    convert h_poly_zero using 2 ; ring; simp +decide [ Fin.sum_univ_three ] ; ring
  have h_coeff_zero : v ⬝ᵥ d_c * (v ⬝ᵥ v) = 0 := by
    linarith [ h_cubic_zero ( -2), h_cubic_zero ( -1), h_cubic_zero 0,
               h_cubic_zero 1, h_cubic_zero 2 ]
  exact h_nonzero (by simpa [normSq] using h_coeff_zero)

/-- Polynomial quadratic extraction: Killing equation from vanishing quadratic form.
    Proved by Aristotle (Harmonic). -/
lemma poly_killing_extraction
    (K : Fin 3 → Fin 3 → ℝ)
    (h : ∀ v : Fin 3 → ℝ,
      (∑ i : Fin 3, ∑ j : Fin 3, v i * v j * K i j) = 0) :
    ∀ i j : Fin 3, K i j + K j i = 0 := by
  intros i j
  have h_diff : ∑ k, ∑ l, (if k = i then 1 else 0) * (if l = j then 1 else 0) * K k l +
      ∑ k, ∑ l, (if k = j then 1 else 0) * (if l = i then 1 else 0) * K k l = 0 := by
    convert h (fun x => if x = i then 1 else if x = j then 1 else 0) using 1
    simp +decide [Fin.sum_univ_three]; ring
    fin_cases i <;> fin_cases j <;> simp +decide
    all_goals
      have := h (fun i => if i = 0 then 1 else 0)
      have := h (fun i => if i = 1 then 1 else 0)
      have := h (fun i => if i = 2 then 1 else 0)
      simp_all +decide [Fin.sum_univ_three]
    · ring
    · ring
    · ring
  simp_all +decide [Fin.sum_univ_three]

/-- Polynomial linear extraction: coefficients of vanishing linear polynomial vanish.
    Proved by Aristotle (Harmonic). -/
lemma poly_linear_extraction
    (d : Fin 3 → ℝ) (C : ℝ)
    (h : ∀ v : Fin 3 → ℝ, dotProduct v d + C = 0) :
    d = 0 ∧ C = 0 := by
  constructor
  <;> have := h 0
  <;> have := h (fun i => if i = 0 then 1 else 0)
  <;> have := h (fun i => if i = 1 then 1 else 0)
  <;> have := h (fun i => if i = 2 then 1 else 0)
  <;> simp_all +decide [Fin.sum_univ_three, dotProduct]
  exact funext fun i => by fin_cases i <;> assumption

-- ============================================================================
-- Analytical Gap Lemmas (proved using axioms above)
--
-- Each lemma uses standard analytical axioms declared above to bridge
-- the gap between Lean's Mathlib and the required analysis.
-- ============================================================================

/-- Gap 1-3 combined: Score function identity for the entropy dissipation formula.
    D(f) = -(1/2) ∫∫ f(v)f(w) ⟨Δ, A(v-w) Δ⟩ where Δ = ∇log f(v) - ∇log f(w).
    Derived from: IBP (Gap 1) + Fubini+symmetrization (Gap 2) + score substitution (Gap 3).
    Reference: Proof of Lemma 5 (lem:entropy_dissipation). -/
lemma entropy_score_form (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ 3 f)
    (hSWF : ∫ v, LandauOperator Ψ f v * (Real.log ∘ f) v =
      -(1 / 2) * ∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
        (mulVec (landauMatrix Ψ (v - w))
          (f w • vGrad f v - f v • vGrad f w))) :
    entropyDissipation Ψ f =
    -(1 / 2) * ∫ v, ∫ w, PSDIntegrand Ψ f v w := by
  unfold entropyDissipation
  simp_rw [show ∀ v, Real.log (f v) = (Real.log ∘ f) v from fun _ => rfl]
  rw [hSWF]
  unfold PSDIntegrand
  simp_rw [analysis_fluxFactor f hf_pos, analysis_scalarFactor]

/-- Gap 4: Non-negativity of the PSD-weighted double integral.
    Since f > 0, Ψ ≥ 0, and Yᵀ A(z) Y ≥ 0 (Lemma 2), the integrand is
    non-negative, so the double integral is non-negative.
    Reference: Step in the proof of Theorem 3 (thm:H_theorem). -/
lemma psd_weighted_integral_nonneg (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 ≤ Ψ r) (hf_pos : ∀ v, 0 < f v) :
    0 ≤ ∫ v, ∫ w, f v * f w *
      dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
        (mulVec (landauMatrix Ψ (v - w))
          (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)) := by
  -- Proved by Aristotle (Harmonic). Integrand is nonneg (f>0, PSD quadratic form).
  exact integral_nonneg fun v => integral_nonneg fun w =>
    mul_nonneg (le_of_lt (mul_pos (hf_pos v) (hf_pos w)))
      (landauMatrix_posSemidef (hΨ (eucNorm (v - w))) _)

/-- Gap 5: D(f) = 0 forces the PSD quadratic form integrand to vanish pointwise.
    From D(f) = 0, the entropy dissipation formula, f > 0, and continuity:
    the non-negative integrand integrates to zero, hence vanishes pointwise.
    Reference: Step in the proof of Lemma 6 (lem:D_zero_functional_eq). -/
lemma entropy_zero_quadform_zero (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 < Ψ r) (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ 3 f)
    (hD : entropyDissipation Ψ f = 0)
    -- Analytical interface hypotheses:
    -- Score form identity (from IBP + Fubini + score substitution)
    (hScoreForm : entropyDissipation Ψ f =
      -(1 / 2) * ∫ v, ∫ w, PSDIntegrand Ψ f v w)
    -- PSD integrand properties (continuity + integrability for nonneg_dbl_zero)
    (hPSD_cont : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      PSDIntegrand Ψ f p.1 p.2))
    (hPSD_inner : ∀ v, Integrable (PSDIntegrand Ψ f v))
    (hPSD_outer : Integrable (fun v => ∫ w, PSDIntegrand Ψ f v w))
    (v w : Fin 3 → ℝ) :
    dotProduct
      (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
      (mulVec (landauMatrix Ψ (v - w))
        (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)) = 0 := by
  -- D=0 + score form → ∫∫ PSDIntegrand = 0
  have h_int_zero : ∫ v, ∫ w, PSDIntegrand Ψ f v w = 0 := by linarith [hScoreForm ▸ hD]
  -- nonneg + continuous + integrable + integral=0 → pointwise = 0
  have h_pw := analysis_nonneg_dbl_zero (PSDIntegrand Ψ f) (fun v w =>
    show 0 ≤ PSDIntegrand Ψ f v w from
      mul_nonneg (le_of_lt (mul_pos (hf_pos v) (hf_pos w)))
        (landauMatrix_posSemidef (le_of_lt (hΨ (eucNorm (v - w)))) _))
    hPSD_cont hPSD_inner hPSD_outer h_int_zero v w
  -- PSDIntegrand = 0 with f(v)*f(w) > 0 → quadratic form = 0
  have := h_pw
  unfold PSDIntegrand at this
  nlinarith [mul_pos (hf_pos v) (hf_pos w)]


/-- Gap 6: Solution of the functional equation: parallel + curl-free → affine.
    If g(v) - g(w) ∥ (v - w) for all v ≠ w and g is smooth (hence curl-free),
    then g(v) = b + 2c₀ v for constants b, c₀.
    Reference: Proof of Lemma 7 (lem:functional_eq_solution). -/
lemma parallel_curl_free_affine (g : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hg_smooth : ContDiff ℝ 2 g)
    (hparallel : ∀ v w, v ≠ w → ∃ l : ℝ, g v - g w = l • (v - w)) :
    ∃ (b : Fin 3 → ℝ) (c₀ : ℝ), ∀ v, g v = b + (2 * c₀) • v := by
  -- Proved by Aristotle (Harmonic). Full proof in gap06_aristotle.lean.
  -- Step 1: Show fderiv g v = c(v) • id for some scalar function c
  have h_deriv : ∀ v : Fin 3 → ℝ, ∃ c : ℝ, ∀ w : Fin 3 → ℝ, (fderiv ℝ g v) w = c • w := by
    intro v
    have h_deriv_eq : ∀ w : Fin 3 → ℝ, (fderiv ℝ g v) w ∈ Submodule.span ℝ {w} := by
      intro w
      have h_deriv_eq : ∀ t : ℝ, g (v + t • w) - g v ∈ Submodule.span ℝ {w} := by
        intro t
        by_cases ht : t = 0 ∨ w = 0 <;> simp_all +decide [Submodule.mem_span_singleton]
        · aesop
        · obtain ⟨l, hl⟩ := hparallel (v + t • w) v (by aesop)
          use l * t
          simp_all +decide [mul_comm, smul_smul]
      have h_lim : Filter.Tendsto (fun t : ℝ => (1 / t) • (g (v + t • w) - g v)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((fderiv ℝ g v) w)) := by
        have h_lim : HasDerivAt (fun t : ℝ => g (v + t • w)) ((fderiv ℝ g v) w) 0 := by
          convert HasFDerivAt.hasDerivAt
            (HasFDerivAt.comp 0
              (hg_smooth.differentiable (by norm_num)
                |> Differentiable.differentiableAt
                |> DifferentiableAt.hasFDerivAt)
              (HasFDerivAt.add (hasFDerivAt_const _ _)
                (HasFDerivAt.smul (hasFDerivAt_id 0)
                  (hasFDerivAt_const _ _)))) using 1
          norm_num
        simpa [div_eq_inv_mul] using h_lim.tendsto_slope_zero_right
      exact Submodule.closed_of_finiteDimensional _ |> fun h => h.mem_of_tendsto h_lim <| Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => Submodule.smul_mem _ _ <| h_deriv_eq t
    have h_deriv_scalar : ∀ w : Fin 3 → ℝ, ∃ c : ℝ, (fderiv ℝ g v) w = c • w := by
      exact fun w => by simpa [eq_comm] using Submodule.mem_span_singleton.mp (h_deriv_eq w)
    choose c hc using h_deriv_scalar
    have h_c_const : ∀ i j : Fin 3, c (Pi.single i 1) = c (Pi.single j 1) := by
      intro i j
      have := hc (Pi.single i 1 + Pi.single j 1)
      simp_all +decide [funext_iff, Fin.forall_fin_succ]
      fin_cases i <;> fin_cases j <;> simp +decide at this ⊢ <;> linarith!
    use c (Pi.single 0 1)
    intro w; rw [hc]; ext i; simp +decide [← h_c_const i 0]
    have h_c_const : ∀ w : Fin 3 → ℝ, (fderiv ℝ g v) w = ∑ i, w i • (fderiv ℝ g v) (Pi.single i 1) := by
      intro w; exact (by
      rw [show w = ∑ i, Pi.single i (w i) by ext i; simp +decide]
      simp +decide [Finset.sum_apply, Pi.single_apply]
      ring
      exact Finset.sum_congr rfl fun i _ => by rw [← map_smul]; congr; ext j; fin_cases i <;> fin_cases j <;> simp +decide [Pi.single_apply])
    specialize h_c_const w; rw [hc] at h_c_const; simp +decide [Fin.sum_univ_three] at h_c_const
    replace h_c_const := congr_fun h_c_const i; fin_cases i <;> simp +decide [hc] at h_c_const ⊢
    · exact Classical.or_iff_not_imp_right.2 fun h => mul_left_cancel₀ h <| by linarith
    · exact Classical.or_iff_not_imp_right.2 fun h => mul_left_cancel₀ h <| by linarith
    · exact Classical.or_iff_not_imp_right.2 fun h => mul_left_cancel₀ h <| by linarith
  -- Step 2: c is constant (via symmetry of second derivatives)
  have h_const_deriv : ∃ c₀ : ℝ, ∀ v : Fin 3 → ℝ, ∀ w : Fin 3 → ℝ, (fderiv ℝ g v) w = c₀ • w := by
    choose c hc using h_deriv
    have h_const_c : ∀ v w : Fin 3 → ℝ, c v = c w := by
      have hc_partial : ∀ v : Fin 3 → ℝ, ∀ i j : Fin 3, (fderiv ℝ g v) (Pi.single j 1) i = c v * (if i = j then 1 else 0) := by
        aesop
      have h_symm_second_deriv :
          ∀ v : Fin 3 → ℝ, ∀ i j k : Fin 3,
          (fderiv ℝ (fun v => (fderiv ℝ g v) (Pi.single j 1)) v)
            (Pi.single k 1) i =
          (fderiv ℝ (fun v => (fderiv ℝ g v) (Pi.single k 1)) v)
            (Pi.single j 1) i := by
        intro v i j k
        rw [fderiv_clm_apply, fderiv_clm_apply]
        simp +decide [hg_smooth.contDiffAt.differentiableAt]
        ring
        · apply_rules [ContDiffAt.isSymmSndFDerivAt]
          exacts [hg_smooth.contDiffAt, by norm_num [minSmoothness]]
        · have h_diff : ContDiff ℝ 1 (fderiv ℝ g) := by
            exact hg_smooth.fderiv_right le_rfl
          exact h_diff.differentiable le_rfl v
        · exact differentiableAt_const _
        · have h_diff : ContDiff ℝ 1 (fderiv ℝ g) := by
            exact hg_smooth.fderiv_right le_rfl
          exact h_diff.differentiable le_rfl v
        · exact differentiableAt_const _
      have h_second_deriv : ∀ v : Fin 3 → ℝ, ∀ i j k : Fin 3, (fderiv ℝ (fun v => (fderiv ℝ g v) (Pi.single j 1)) v) (Pi.single k 1) i = (fderiv ℝ c v) (Pi.single k 1) * (if i = j then 1 else 0) := by
        intro v i j k; rw [fderiv_pi]; aesop
        have h_diff : ContDiff ℝ 1 (fun v => (fderiv ℝ g v) (Pi.single j 1)) := by
          exact (hg_smooth.fderiv_right le_rfl).clm_apply contDiff_const
        exact fun i => DifferentiableAt.comp v (differentiableAt_pi.1 (h_diff.contDiffAt.differentiableAt le_rfl) i) (differentiableAt_id)
      have h_zero_deriv : ∀ v : Fin 3 → ℝ, ∀ k : Fin 3, (fderiv ℝ c v) (Pi.single k 1) = 0 := by
        intros v k
        by_contra h_nonzero_deriv
        obtain ⟨i, hi⟩ : ∃ i : Fin 3, i ≠ k := by fin_cases k <;> trivial
        have h_eq : (fderiv ℝ c v) (Pi.single k 1) = (fderiv ℝ c v) (Pi.single i 1) := by
          specialize h_symm_second_deriv v i k i; aesop
        have h_zero : (fderiv ℝ c v) (Pi.single k 1) = 0 := by
          specialize h_symm_second_deriv v i i k; aesop
        exact h_nonzero_deriv h_zero
        skip
      have h_const_c : ∀ v : Fin 3 → ℝ, (fderiv ℝ c v) = 0 := by
        intro v; ext w; simp [h_zero_deriv]
        convert (show (fderiv ℝ c v) w = ∑ k : Fin 3, w k • (fderiv ℝ c v) (Pi.single k 1) from ?_) using 1
        · simp [h_zero_deriv]
        · rw [show w = ∑ k, Pi.single k (w k) by ext i; simp +decide [Pi.single_apply]]
          simp +decide [Finset.sum_apply, Pi.single_apply]
          ring
          exact Finset.sum_congr rfl fun i _ => by rw [← smul_eq_mul, ← ContinuousLinearMap.map_smul]; congr; ext j; by_cases hi : i = j <;> aesop
      intro v w; exact is_const_of_fderiv_eq_zero (show Differentiable ℝ c from by
        have h_diff_c : ContDiff ℝ 1 (fun v => (fderiv ℝ g v) (Pi.single 0 1) 0) := by
          exact (contDiff_apply ℝ ℝ 0).comp
            ((hg_smooth.fderiv_right (m := 1) le_rfl).clm_apply contDiff_const)
        convert h_diff_c.differentiable le_rfl using 1
        aesop (simp_config := { singlePass := true })) h_const_c v w
    use c 0
    intro v w
    rw [hc, h_const_c v 0]
  -- Step 3: FTC to get g(v) = g(0) + c₀ v
  obtain ⟨c₀, hc₀⟩ := h_const_deriv
  have h_ftc : ∀ v : Fin 3 → ℝ, g v = g 0 + ∫ t in (0 : ℝ)..1, (fderiv ℝ g (t • v)) v := by
    intro v
    have h_integral_eq : ∀ a b : ℝ, ∫ t in a..b, (fderiv ℝ g (t • v)) v = g (b • v) - g (a • v) := by
      intro a b
      rw [intervalIntegral.integral_deriv_eq_sub']
      · ext t; erw [deriv]; erw [fderiv_comp] <;> norm_num [hg_smooth.contDiffAt.differentiableAt (by norm_num), hc₀]
        rw [deriv_pi] <;> norm_num [Fin.forall_fin_succ]
      · exact fun x hx => DifferentiableAt.comp x (hg_smooth.contDiffAt.differentiableAt (by norm_num)) (differentiableAt_id.smul_const _)
      · exact Continuous.continuousOn (by continuity)
    simp +decide [h_integral_eq]
  use g 0, c₀ / 2; intro v; rw [h_ftc v]; norm_num [hc₀]; ring

/-- Gap 7: Antiderivative of an affine gradient.
    If ∇h(v) = b + 2c₀ v, then h(v) = h(0) + b · v + c₀|v|².
    Reference: Proof of Lemma 8 (lem:log_f_quadratic). -/
lemma affine_gradient_antiderivative (h : (Fin 3 → ℝ) → ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ)
    (hh_smooth : ContDiff ℝ 3 h)
    (hgrad : ∀ v, vGrad h v = b + (2 * c₀) • v) :
    ∀ v, h v = h 0 + dotProduct b v + c₀ * normSq v := by
  -- Proved by Aristotle (Harmonic). Full proof in gap07_aristotle.lean.
  have h_deriv : ∀ v : Fin 3 → ℝ, ∀ t : ℝ, deriv (fun t => h (t • v)) t = (b + 2 * c₀ • (t • v)) ⬝ᵥ v := by
    intro v t
    have h_deriv_def : deriv (fun t => h (t • v)) t = (VML.vGrad h (t • v)) ⬝ᵥ v := by
      unfold VML.vGrad
      convert HasDerivAt.deriv
        (HasFDerivAt.hasDerivAt
          (hh_smooth.differentiable (by norm_num)
            |> Differentiable.differentiableAt
            |> DifferentiableAt.hasFDerivAt
            |> HasFDerivAt.comp _
            <| HasFDerivAt.smul (hasFDerivAt_id t)
            <| hasFDerivAt_const _ _)) using 1
      norm_num [fderiv_deriv, dotProduct]
      rw [show v = ∑ i, Pi.single i (v i) by ext i; simp +decide]
      simp +decide [mul_comm, Finset.mul_sum _ _ _, Finset.sum_mul]
      ring
      exact Finset.sum_congr rfl fun i _ => by
        rw [← smul_eq_mul, ← ContinuousLinearMap.map_smul]
        congr; ext j; by_cases hi : i = j <;> aesop
    simp_all +decide [two_mul]
    ring
  intros v
  have : ∫ t in (0 : ℝ)..1, deriv (fun t => h (t • v)) t = h v - h 0 := by
    rw [intervalIntegral.integral_deriv_eq_sub]; aesop
    · exact fun t ht => DifferentiableAt.comp t (hh_smooth.contDiffAt.differentiableAt (by norm_num)) (differentiableAt_id.smul_const _)
    · exact Continuous.intervalIntegrable (by rw [show deriv _ = _ from funext fun t => h_deriv v t]
                                               continuity) _ _
  simp_all +decide [VML.normSq]
  norm_num [mul_assoc, mul_comm, mul_left_comm, Fin.sum_univ_three, dotProduct] at *; linarith!

/-- Gap 8: For a log-quadratic f = exp(a₀ + b·v + c₀|v|²), the Landau flux vanishes.
    This follows because ∇log f(v) - ∇log f(w) = 2c₀(v-w), so the flux is
    proportional to A(v-w)(v-w) = 0 by Lemma 3 (projection annihilation).
    Reference: Key step in the proof of Theorem 5 (thm:nullspace_sufficiency). -/
lemma maxwellian_landau_flux_zero (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (a₀ : ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ)
    (hf : ∀ v, f v = Real.exp (a₀ + dotProduct b v + c₀ * normSq v)) :
    ∀ v w, mulVec (landauMatrix Ψ (v - w))
      (f w • vGrad f v - f v • vGrad f w) = 0 := by
  -- Proved by Aristotle (Harmonic). Full proof in gap08_aristotle.lean.
  -- Key: ∇f(v) = f(v)·(b + 2c₀v), so flux ∝ A(v-w)(v-w) = 0
  have h_grad : ∀ v : Fin 3 → ℝ, VML.vGrad f v = f v • (b + 2 * c₀ • v) := by
    unfold VML.vGrad
    rw [show f = _ from funext hf]
    intro v; ext i; rw [fderiv_exp]
    norm_num [dotProduct, Fin.sum_univ_three]
    ring
    · unfold VML.normSq
      norm_num [Fin.sum_univ_three, dotProduct]
      ring
      erw [HasFDerivAt.fderiv
        (HasFDerivAt.add
          (HasFDerivAt.add
            (HasFDerivAt.add
              (HasFDerivAt.add
                (HasFDerivAt.add
                  (HasFDerivAt.add
                    (hasFDerivAt_const _ _)
                    (HasFDerivAt.mul
                      (hasFDerivAt_const _ _)
                      (hasFDerivAt_apply _ _)))
                  (HasFDerivAt.mul
                    (hasFDerivAt_apply _ _ |> HasFDerivAt.pow <| 2)
                    (hasFDerivAt_const _ _)))
                (HasFDerivAt.mul
                  (hasFDerivAt_const _ _)
                  (hasFDerivAt_apply _ _)))
              (HasFDerivAt.mul
                (hasFDerivAt_apply _ _ |> HasFDerivAt.pow <| 2)
                (hasFDerivAt_const _ _)))
            (HasFDerivAt.mul
              (hasFDerivAt_const _ _)
              (hasFDerivAt_apply _ _)))
          (HasFDerivAt.mul
            (hasFDerivAt_apply _ _ |> HasFDerivAt.pow <| 2)
            (hasFDerivAt_const _ _)))]
      norm_num
      ring
      fin_cases i <;> norm_num <;> ring!
      · simp +decide
      · simp +decide
      · simp +decide
    · apply_rules [DifferentiableAt.add, DifferentiableAt.mul, differentiableAt_id, differentiableAt_const]
      all_goals apply_rules [differentiableAt_pi.1, differentiableAt_id]
  intros v w
  simp [h_grad]
  convert congr_arg (fun x : Fin 3 → ℝ => f w • f v • c₀ • (2 : ℝ) • x) (landauMatrix_mulVec_self Ψ (v - w)) using 1
  ext
  norm_num
  ring!
  · simp +decide [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Matrix.mulVec, dotProduct]
    ring!
  · norm_num [Algebra.smul_def]

/-- Gap 11: D(f) = 0 implies f is a Maxwellian.
    Chains: D=0 → parallelism (Lemma 6) → ∇log f affine (Lemma 7) →
    log f quadratic (Lemma 8) → f = exp(quadratic) → c₀ < 0 (L¹ integrability).
    Reference: Proof of Theorem 4 (thm:nullspace_necessity) + Corollary 2. -/
lemma D_zero_implies_maxwellian (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 < Ψ r) (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ 3 f) (hf_int : Integrable f)
    (hD : entropyDissipation Ψ f = 0)
    -- Analytical interface (from IBP + Fubini + score + integrability)
    (hScoreForm : entropyDissipation Ψ f =
      -(1 / 2) * ∫ v, ∫ w, PSDIntegrand Ψ f v w)
    (hPSD_cont : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      PSDIntegrand Ψ f p.1 p.2))
    (hPSD_inner : ∀ v, Integrable (PSDIntegrand Ψ f v))
    (hPSD_outer : Integrable (fun v => ∫ w, PSDIntegrand Ψ f v w)) :
    IsMaxwellian f := by
  -- Chain: D=0 → quadform=0 → parallel → affine → quadratic → Maxwellian
  have hlog_smooth := hf_smooth.log (fun v => ne_of_gt (hf_pos v))
  -- Step 1: D=0 → parallelism (via gap 5 + PSD equality case)
  have hpar : ∀ v w, v ≠ w →
      ∃ l : ℝ, vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w = l • (v - w) :=
    fun v w hvw => landauMatrix_quadForm_eq_zero_iff
      (hΨ (eucNorm (v - w))) (sub_ne_zero.mpr hvw) _
      (entropy_zero_quadform_zero Ψ f hΨ hf_pos hf_smooth hD
        hScoreForm hPSD_cont hPSD_inner hPSD_outer v w)
  -- Step 2: parallel → affine (gap 6)
  -- vGrad (log ∘ f) is smooth (each component is fderiv applied to a smooth function)
  have hvGrad_smooth : ContDiff ℝ 2 (fun v => vGrad (Real.log ∘ f) v) :=
    analysis_vGrad_smooth _ hlog_smooth
  obtain ⟨b, c₀, haffine⟩ := parallel_curl_free_affine _ hvGrad_smooth hpar
  -- Step 3: affine gradient → quadratic (gap 7)
  have hquad := affine_gradient_antiderivative (Real.log ∘ f) b c₀ hlog_smooth haffine
  -- Step 4: f = exp(quadratic)
  set a₀ := Real.log (f 0) with ha₀
  have hf_exp : ∀ v, f v = Real.exp (a₀ + dotProduct b v + c₀ * normSq v) := by
    intro v
    rw [← Real.exp_log (hf_pos v)]
    congr 1
    have := hquad v
    simp [Function.comp] at this
    exact this
  -- Step 5: c₀ < 0 from the form of f
  exact ⟨a₀, b, c₀, analysis_gaussian_integrability f a₀ b c₀ hf_pos hf_int hf_exp, hf_exp⟩

/-- Gap 12: (v · a) |v|² = 0 for all v ∈ ℝ³ implies a = 0.
    Choose v = t eᵢ, divide by t³, let t → ∞.
    Reference: Step in the proof of Lemma 14 (lem:T_constant). -/
lemma cubic_coeff_zero (a : Fin 3 → ℝ) (h : ∀ v, dotProduct v a * normSq v = 0) :
    a = 0 := by
  -- Proved by Aristotle (Harmonic)
  ext j; by_contra h_a_nonzero; specialize h (Pi.single j 1)
  simp_all +decide [Fin.sum_univ_three, dotProduct]
  fin_cases j <;> simp_all +decide [VML.normSq]

/-- Gap 15: Maximum principle for the Poisson–Boltzmann equation on T³.
    If T∞ Δ(log n) = n - ρ_ion with T∞ > 0 and n > 0, then n ≡ ρ_ion.
    At the maximum of n: Δ(log n) ≤ 0 → n ≤ ρ_ion.
    At the minimum: Δ(log n) ≥ 0 → n ≥ ρ_ion.
    Reference: Proof of Lemma 21 (lem:density_constant). -/
lemma poisson_boltzmann_max_principle
    (X : Type*) [Nonempty X]
    (n : X → ℝ) (ρ_ion T_infty : ℝ)
    (laplacian : (X → ℝ) → X → ℝ)
    (_hn_pos : ∀ x, 0 < n x) (hT : 0 < T_infty) (_hρ : 0 < ρ_ion)
    -- PB equation: T∞ Δ(log n) = n - ρ_ion
    (hPB : ∀ x, T_infty * laplacian (Real.log ∘ n) x = n x - ρ_ion)
    -- Maximum principle: n attains its max and min (compactness)
    (x_max : X) (hmax : ∀ x, n x ≤ n x_max)
    (x_min : X) (hmin : ∀ x, n x_min ≤ n x)
    -- At a maximum of n, Δ(log n) ≤ 0 (second derivative test)
    (hmax_lapl : laplacian (Real.log ∘ n) x_max ≤ 0)
    -- At a minimum of n, Δ(log n) ≥ 0
    (hmin_lapl : 0 ≤ laplacian (Real.log ∘ n) x_min) :
    ∀ x, n x = ρ_ion := by
  -- Proved by Aristotle (Harmonic)
  have h_eq : n x_max = ρ_ion ∧ n x_min = ρ_ion := by
    constructor <;> nlinarith [hPB x_max, hPB x_min, hmax x_min, hmin x_max]
  exact fun x => le_antisymm (by linarith [hmax x]) (by linarith [hmin x])

-- ============================================================================
-- Iterated derivative helpers for continuous linear maps
-- ============================================================================

/-- The iterated derivative of a continuous linear map vanishes at order ≥ 2. -/
lemma iteratedFDeriv_clm_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →L[ℝ] F) (n : ℕ) (hn : 2 ≤ n) (x : E) :
    iteratedFDeriv ℝ n f x = 0 := by
  rw [show n = (n - 1) + 1 from by omega, iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp, show (fun y => fderiv ℝ (↑f) y) = fun _ => (f : E →L[ℝ] F) from
    funext fun y => f.hasFDerivAt.fderiv]
  rw [iteratedFDeriv_const_of_ne (by omega : n - 1 ≠ 0)]; simp

/-- The norm of the first iterated derivative of a CLM equals the operator norm. -/
lemma norm_iteratedFDeriv_one_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E →L[ℝ] F) (x : E) :
    ‖iteratedFDeriv ℝ 1 f x‖ = ‖f‖ := by
  rw [show (1:ℕ) = 0 + 1 from rfl, iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp, show (fun y => fderiv ℝ (↑f) y) = fun _ => (f : E →L[ℝ] F) from
    funext fun y => f.hasFDerivAt.fderiv, iteratedFDeriv_zero_eq_comp,
    LinearIsometryEquiv.norm_map]

-- ============================================================================
-- Polynomial/quadratic iterated derivative bounds
-- ============================================================================

/-- For `Fin 3 → ℝ` with sup norm: ‖v‖² ≤ normSq v = ∑ vᵢ². -/
private lemma norm_sq_le_normSq (v : Fin 3 → ℝ) : ‖v‖ ^ 2 ≤ normSq v := by
  unfold normSq dotProduct; simp only [Fin.sum_univ_three]
  obtain ⟨j, _, hj⟩ := (Finset.univ (α := Fin 3)).exists_max_image
    (fun i => ‖v i‖) ⟨0, Finset.mem_univ _⟩
  have hj_eq : ‖v‖ = ‖v j‖ :=
    le_antisymm
      (pi_norm_le_iff_of_nonneg (norm_nonneg (v j)) |>.mpr
        (fun i => hj i (Finset.mem_univ i)))
      (norm_le_pi_norm v j)
  calc ‖v‖ ^ 2 = ‖v j‖ ^ 2 := by rw [hj_eq]
    _ = |v j| ^ 2 := by rw [Real.norm_eq_abs]
    _ = v j * v j := by rw [sq_abs]; ring
    _ ≤ ∑ i : Fin 3, v i * v i :=
        Finset.single_le_sum (fun i _ => mul_self_nonneg (v i)) (Finset.mem_univ j)
    _ = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 := by simp [Fin.sum_univ_three]

lemma contDiff_negNormSq_div (T : ℝ) :
    ContDiff ℝ ⊤ (fun v : Fin 3 → ℝ => -(normSq v) / (2 * T)) := by
  apply ContDiff.div_const; apply ContDiff.neg; unfold normSq dotProduct
  exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)

/-- ‖iteratedFDeriv i (v_j²) v‖ ≤ 2(1+‖v‖) for i ≥ 1, via Leibniz on proj_j * proj_j. -/
lemma norm_iteratedFDeriv_proj_sq_le (j : Fin 3) (i : ℕ) (hi : 1 ≤ i)
    (v : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ i (fun w : Fin 3 → ℝ => w j * w j) v‖ ≤ 2 * (1 + ‖v‖) := by
  set pj := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) j
  have hpj : ContDiff ℝ ⊤ (fun w : Fin 3 → ℝ => w j) := contDiff_apply ℝ ℝ j
  have hleib := norm_iteratedFDeriv_mul_le hpj hpj v (n := i) le_top
  have hpj_le : ‖pj‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
      simp only [one_mul]; exact norm_le_pi_norm w j
  have hpj_eq : (fun w : Fin 3 → ℝ => w j) = (pj : (Fin 3 → ℝ) →L[ℝ] ℝ) := rfl
  have hpj_sq : ‖pj‖ * ‖pj‖ ≤ 1 := mul_le_one₀ hpj_le (norm_nonneg pj) hpj_le
  refine le_trans hleib ?_
  by_cases h3 : 3 ≤ i
  · refine le_trans (Finset.sum_nonpos fun s hs => ?_) (by positivity)
    rw [Finset.mem_range] at hs
    rcases show s ≥ 2 ∨ i - s ≥ 2 from by omega with h | h
    · simp [hpj_eq, iteratedFDeriv_clm_zero pj s h v]
    · simp [hpj_eq, iteratedFDeriv_clm_zero pj (i - s) h v]
  · push_neg at h3; interval_cases i
    · -- i = 1
      simp only [Nat.reduceAdd, Nat.reduceSub, Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add, Nat.choose, norm_iteratedFDeriv_zero, hpj_eq,
        norm_iteratedFDeriv_one_clm pj v]
      push_cast
      have := mul_le_mul_of_nonneg_right (pj.le_opNorm v) (norm_nonneg pj)
      nlinarith [norm_nonneg v]
    · -- i = 2
      simp only [Nat.reduceAdd, Nat.reduceSub, Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add, Nat.choose, norm_iteratedFDeriv_zero, hpj_eq,
        norm_iteratedFDeriv_one_clm pj v,
        iteratedFDeriv_clm_zero pj 2 le_rfl v, norm_zero]
      push_cast; linarith [norm_nonneg v]

/-- Derivative bound for the quadratic form q(v) = -normSq(v)/(2T).
    Since q is a degree-2 polynomial: fderiv is O(1+‖v‖), second derivative is constant,
    and all higher derivatives vanish. -/
lemma quadratic_iteratedFDeriv_bound (T : ℝ) (hT : 0 < T) (k : ℕ) :
    ∃ c > 0, ∀ v : Fin 3 → ℝ, ∀ i : ℕ, 1 ≤ i → i ≤ k →
      ‖iteratedFDeriv ℝ i (fun v => -(normSq v) / (2 * T)) v‖ ≤ (c * (1 + ‖v‖)) ^ i := by
  refine ⟨3 / T + 1, by positivity, fun v i hi1 hik => ?_⟩
  set c := 3 / T + 1
  -- Step 1: Express q as sum of scaled components and bound iteratedFDeriv
  have hfn_eq : (fun v : Fin 3 → ℝ => -(normSq v) / (2 * T)) =
      (fun v => ∑ j : Fin 3, -(v j * v j) / (2 * T)) := by
    ext w; unfold normSq dotProduct; simp [Fin.sum_univ_three]; ring
  have hcomp_smooth : ∀ j : Fin 3,
      ContDiff ℝ ⊤ (fun v : Fin 3 → ℝ => -(v j * v j) / (2 * T)) := fun j =>
    ((contDiff_apply ℝ ℝ j).mul (contDiff_apply ℝ ℝ j)).neg.div_const _
  -- iteratedFDeriv of sum = sum of iteratedFDeriv
  have h_sum := congrFun (iteratedFDeriv_sum (i := i)
    (fun j _ => (hcomp_smooth j).of_le le_top)) v
  -- Each component: -(v_j²)/(2T) = (-1/(2T)) • (v_j²)
  have hcomp_eq : ∀ j : Fin 3, (fun v : Fin 3 → ℝ => -(v j * v j) / (2 * T)) =
      (-1 / (2 * T)) • (fun v : Fin 3 → ℝ => v j * v j) := by
    intro j; ext w; simp [Pi.smul_apply, smul_eq_mul]; ring
  -- Bound: ‖iteratedFDeriv i q v‖ ≤ (3/T)(1+‖v‖)
  have hbound : ‖iteratedFDeriv ℝ i (fun v : Fin 3 → ℝ => -(normSq v) / (2 * T)) v‖ ≤
      3 / T * (1 + ‖v‖) := by
    rw [hfn_eq]; rw [show (fun v : Fin 3 → ℝ => ∑ j : Fin 3, -(v j * v j) / (2 * T)) =
      (fun v => ∑ j : Fin 3, ((-1 / (2 * T)) • fun v : Fin 3 → ℝ => v j * v j) v) from by
      ext w; congr 1; ext j; simp [Pi.smul_apply, smul_eq_mul]; ring]
    -- After distributing iteratedFDeriv through the sum
    conv => arg 1; rw [iteratedFDeriv_sum (fun j _ =>
      ((contDiff_apply ℝ ℝ j).mul (contDiff_apply ℝ ℝ j)).const_smul _|>.of_le le_top)]
    refine le_trans (norm_sum_le _ _) ?_
    -- Bound each component
    have habs : |(-1 : ℝ) / (2 * T)| = 1 / (2 * T) := by
      rw [abs_of_nonpos (by linarith)]; ring
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) ?_
    · rw [iteratedFDeriv_const_smul_apply
        (((contDiff_apply ℝ ℝ j).mul (contDiff_apply ℝ ℝ j)).contDiffAt.of_le le_top),
        norm_smul, Real.norm_eq_abs, habs]
      exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_proj_sq_le j i hi1 v)
        (by positivity)
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      ring_nf; linarith [norm_nonneg v]
  -- Step 2: (3/T)(1+‖v‖) ≤ c(1+‖v‖) ≤ (c(1+‖v‖))^i
  calc ‖iteratedFDeriv ℝ i (fun v => -(normSq v) / (2 * T)) v‖
      ≤ 3 / T * (1 + ‖v‖) := hbound
    _ ≤ c * (1 + ‖v‖) := by unfold_let c; nlinarith [norm_nonneg v]
    _ ≤ (c * (1 + ‖v‖)) ^ i := le_self_pow₀
        (by unfold_let c; nlinarith [norm_nonneg v] : 1 ≤ c * (1 + ‖v‖)) hi1

end VML
