import Aristotle.Landau.main.CoulombFlux

/-!
# PSD Helpers: Continuity and Pointwise Bounds for Coulomb

Proves the Landau quadratic form bound, continuity of the PSD integrand
(the Coulomb singularity cancels in the quadratic form), and pointwise bounds.
These are building blocks for the integrability and Fubini results in CoulombPSD.
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

lemma landau_bound (z u : Fin 3 → ℝ) :
    abs (dotProduct u (mulVec (landauMatrix coulombKernel z) u)) ≤
    (if eucNorm z = 0 then 0 else (eucNorm z)⁻¹) * (eucNorm u)^2 := by
      unfold landauMatrix eucNorm coulombKernel innerLandauMatrix normSq
      split_ifs <;> norm_cast <;> norm_num [ Matrix.vecMulVec ] at *
      · simp_all +decide [ Fin.sum_univ_three, dotProduct ]
        rw [ Real.sqrt_eq_zero' ] at *
        norm_num [ show z 0 = 0 by nlinarith, show z 1 = 0 by nlinarith,
                   show z 2 = 0 by nlinarith, Matrix.mulVec ]
      · exact False.elim <| ‹¬Real.sqrt (z ⬝ᵥ z) = 0› <| le_antisymm ‹_› <| Real.sqrt_nonneg _
      · rw [ Real.sqrt_eq_zero' ] at * ; linarith
      · suffices h_simp :
            abs ((Real.sqrt (dotProduct z z))⁻¹ ^ 3 *
              (dotProduct z z * dotProduct u u - (dotProduct z u) ^ 2)) ≤
            (Real.sqrt (dotProduct z z))⁻¹ * (Real.sqrt (dotProduct u u)) ^ 2 by
          convert h_simp using 2
          norm_num [ Matrix.mulVec, dotProduct ]
          ring
          norm_num [ Fin.sum_univ_three, Matrix.one_apply ] ; ring
        suffices h_cancel :
            abs (z ⬝ᵥ z * u ⬝ᵥ u - (z ⬝ᵥ u) ^ 2) ≤
            (Real.sqrt (z ⬝ᵥ z)) ^ 2 * (Real.sqrt (u ⬝ᵥ u)) ^ 2 by
          rw [ abs_mul, abs_of_nonneg (by positivity) ]
          field_simp
          exact h_cancel
        rw [ Real.sq_sqrt (by positivity),
             Real.sq_sqrt (by exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _) ]
        norm_num [ Fin.sum_univ_three, dotProduct ] at *
        exact abs_le.mpr
          ⟨ by nlinarith [ sq_nonneg (z 0 * u 1 - z 1 * u 0),
                           sq_nonneg (z 0 * u 2 - z 2 * u 0),
                           sq_nonneg (z 1 * u 2 - z 2 * u 1) ],
            by nlinarith [ sq_nonneg (z 0 * u 1 - z 1 * u 0),
                           sq_nonneg (z 0 * u 2 - z 2 * u 0),
                           sq_nonneg (z 1 * u 2 - z 2 * u 1) ] ⟩


lemma tendsto_landau_quadratic_diag
    (G : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hG : ContDiff ℝ 1 G)
    (x : Fin 3 → ℝ) :
    Filter.Tendsto (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      dotProduct (G p.1 - G p.2)
        (mulVec (landauMatrix coulombKernel (p.1 - p.2)) (G p.1 - G p.2)))
      (nhds (x, x)) (nhds 0) := by
        obtain ⟨U, hU⟩ : ∃ U : Set (Fin 3 → ℝ), IsOpen U ∧ x ∈ U ∧
            ∃ L : ℝ, ∀ u v : Fin 3 → ℝ,
              u ∈ U → v ∈ U → eucNorm (G u - G v) ≤ L * eucNorm (u - v) := by
          obtain ⟨U, hU⟩ : ∃ U : Set (Fin 3 → ℝ), IsOpen U ∧ x ∈ U ∧
              ∃ L : ℝ, ∀ u ∈ U, ∀ v ∈ U, ‖G u - G v‖ ≤ L * ‖u - v‖ := by
            have := hG.differentiable le_rfl
            obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ u ∈ Metric.closedBall x 1, ‖fderiv ℝ G u‖ ≤ K := by
              exact IsCompact.exists_bound_of_continuousOn
                (ProperSpace.isCompact_closedBall x 1)
                (hG.continuous_fderiv le_rfl |> Continuous.continuousOn)
            refine ⟨ Metric.ball x 1, Metric.isOpen_ball, Metric.mem_ball_self zero_lt_one, K, _ ⟩
            intro u hu v hv
            have h_mean_value : ∀ t ∈ Set.Icc (0 : ℝ) 1,
                ‖deriv (fun t => G (v + t • (u - v))) t‖ ≤ K * ‖u - v‖ := by
              intro t ht
              have h_mean_value :
                  ‖deriv (fun t => G (v + t • (u - v))) t‖ =
                  ‖(fderiv ℝ G (v + t • (u - v))) (u - v)‖ := by
                rw [ deriv ]
                erw [ fderiv_comp ] <;> norm_num [ this.differentiableAt, fderiv_deriv ]
                rw [ deriv_pi ] <;> norm_num [ Fin.forall_fin_succ ]
                rw [ ← map_sub ] ; rfl
              refine h_mean_value ▸ le_trans (ContinuousLinearMap.le_opNorm _ _)
                (mul_le_mul_of_nonneg_right (hK _ _) (norm_nonneg _) )
              simp_all +decide [ dist_eq_norm ]
              rw [ show v + t • (u - v) - x = (1 - t) • (v - x) + t • (u - x) by
                     ext i
                     simpa using by ring ]
              exact le_trans (norm_add_le _ _) (by
                rw [ norm_smul, norm_smul,
                     Real.norm_of_nonneg (by linarith : 0 ≤ 1 - t),
                     Real.norm_of_nonneg (by linarith : 0 ≤ t) ]
                nlinarith)
            have h_ftc : G u - G v = ∫ t in (0 : ℝ)..1, deriv (fun t => G (v + t • (u - v))) t := by
              rw [ intervalIntegral.integral_deriv_eq_sub ]
              · norm_num
              · exact fun t ht => this.differentiableAt.comp _
                  (DifferentiableAt.add (differentiableAt_const _)
                    (differentiableAt_id.smul_const _) )
              · apply_rules [ Continuous.intervalIntegrable ]
                apply_rules [ ContDiff.continuous_deriv ]
                exacts [ hG.comp (contDiff_const.add (contDiff_id.smul contDiff_const) ),
                         by norm_num ]
            rw [ h_ftc ]
            refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const _) _
            exacts [ K * ‖u - v‖,
                     fun t ht => h_mean_value t <| by
                       constructor <;> cases Set.mem_uIoc.mp ht <;> linarith,
                     by norm_num ]
          obtain ⟨ L, hL ⟩ := hU.2.2
          refine ⟨ U, hU.1, hU.2.1, 3 * L, fun u v hu hv => _ ⟩
          have h_euc_norm :
              eucNorm (G u - G v) ≤ Real.sqrt 3 * ‖G u - G v‖ ∧
              eucNorm (u - v) ≥ ‖u - v‖ := by
            unfold eucNorm
            norm_num [ normSq, Pi.norm_def ]
            constructor <;> norm_num [ Fin.sum_univ_three, dotProduct ] at * <;>
              ring_nf at * <;> norm_num at *
            · rw [ Real.sqrt_le_iff ]
              norm_num [ Fin.univ_succ ]
              ring_nf
              norm_num
              nlinarith only [
                abs_le.mp (show |G u 0 - G v 0| ≤
                    Max.max |G u 0 - G v 0| (Max.max |G u 1 - G v 1| |G u 2 - G v 2|)
                  by exact le_max_left _ _),
                abs_le.mp (show |G u 1 - G v 1| ≤
                    Max.max |G u 0 - G v 0| (Max.max |G u 1 - G v 1| |G u 2 - G v 2|)
                  by exact le_max_of_le_right (le_max_left _ _) ),
                abs_le.mp (show |G u 2 - G v 2| ≤
                    Max.max |G u 0 - G v 0| (Max.max |G u 1 - G v 1| |G u 2 - G v 2|)
                  by exact le_max_of_le_right (le_max_right _ _) ) ]
            · refine Real.le_sqrt_of_sq_le _
              norm_num [ Fin.univ_succ ]
              ring_nf
              (
              rw [ max_def, max_def ]
              split_ifs <;> nlinarith [ sq_nonneg (u 0 - v 0),
                                        sq_nonneg (u 1 - v 1),
                                        sq_nonneg (u 2 - v 2),
                                        abs_mul_abs_self (u 0 - v 0),
                                        abs_mul_abs_self (u 1 - v 1),
                                        abs_mul_abs_self (u 2 - v 2) ] )
          refine le_trans h_euc_norm.1 ?_
          refine le_trans (mul_le_mul_of_nonneg_left (hL u hu v hv) (Real.sqrt_nonneg _) ) ?_
          rw [ mul_assoc ]
          gcongr
          · exact le_trans (norm_nonneg _) (hL u hu v hv)
          · rw [ Real.sqrt_le_left ] <;> norm_num
          · contrapose! hL
            obtain ⟨u, hu, v, hv, huv⟩ : ∃ u ∈ U, ∃ v ∈ U, u ≠ v := by
              rcases Metric.isOpen_iff.mp hU.1 x hU.2.1 with ⟨ ε, εpos, hε ⟩
              exact ⟨ x, hε <| Metric.mem_ball_self εpos,
                      x + fun _ => ε / 2,
                      hε <| Metric.mem_ball.mpr <| by simpa [ abs_of_pos εpos ] using by linarith,
                      ne_of_apply_ne (fun u => u 0) <| by norm_num; linarith ⟩
            exact ⟨ u, hu, v, hv,
              lt_of_lt_of_le
                (mul_neg_of_neg_of_pos hL (norm_pos_iff.mpr (sub_ne_zero.mpr huv) ))
                (norm_nonneg _) ⟩
          · exact h_euc_norm.2
        obtain ⟨L, hL⟩ := hU.right.right
        have h_bound : ∀ᶠ p : (Fin 3 → ℝ) × (Fin 3 → ℝ) in nhds (x, x),
            abs ((G p.1 - G p.2) ⬝ᵥ landauMatrix coulombKernel (p.1 - p.2) *ᵥ (G p.1 - G p.2)) ≤
            (if eucNorm (p.1 - p.2) = 0 then 0 else (eucNorm (p.1 - p.2))⁻¹) *
            (L * eucNorm (p.1 - p.2))^2 := by
          have h_bound : ∀ᶠ p : (Fin 3 → ℝ) × (Fin 3 → ℝ) in nhds (x, x),
              eucNorm (G p.1 - G p.2) ≤ L * eucNorm (p.1 - p.2) := by
            exact Filter.eventually_of_mem
              (IsOpen.mem_nhds (hU.1.prod hU.1) (by aesop) )
              fun p hp => hL _ _ hp.1 hp.2
          filter_upwards [ h_bound ] with p hp
          refine le_trans (landau_bound _ _) _
          split_ifs <;> simp_all +decide [ mul_pow ]
          exact mul_le_mul_of_nonneg_left
            (by nlinarith [ show 0 ≤ eucNorm (G p.1 - G p.2) from Real.sqrt_nonneg _,
                            show 0 ≤ L * eucNorm (p.1 - p.2) from
                              le_trans (Real.sqrt_nonneg _) hp ])
            (inv_nonneg.2 (Real.sqrt_nonneg _) )
        have h_simplified_bound : ∀ᶠ p : (Fin 3 → ℝ) × (Fin 3 → ℝ) in nhds (x, x),
            abs ((G p.1 - G p.2) ⬝ᵥ landauMatrix coulombKernel (p.1 - p.2) *ᵥ
              (G p.1 - G p.2)) ≤ L^2 * eucNorm (p.1 - p.2) := by
          filter_upwards [ h_bound ] with p hp using le_trans hp
            (by split_ifs <;>
              simpa [ *, sq, mul_assoc, mul_comm, mul_left_comm ] using by ring_nf; norm_num)
        refine squeeze_zero_norm' h_simplified_bound _
        refine Continuous.tendsto' _ _ _ _ <;> norm_num [ eucNorm ]
        · exact Continuous.mul continuous_const <| Real.continuous_sqrt.comp <|
            Continuous.dotProduct
              (continuous_fst.sub continuous_snd)
              (continuous_fst.sub continuous_snd)
        · norm_num [ normSq ]


lemma continuous_landau_quadratic
    (G : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hG : ContDiff ℝ 1 G) :
    Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      dotProduct (G p.1 - G p.2)
        (mulVec (landauMatrix coulombKernel (p.1 - p.2)) (G p.1 - G p.2))) := by
        set F : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) → ℝ := fun p =>
          (G p.1 - G p.2) ⬝ᵥ landauMatrix coulombKernel (p.1 - p.2) *ᵥ (G p.1 - G p.2)
        have h_cont_away : ∀ p : (Fin 3 → ℝ) × (Fin 3 → ℝ), p.1 ≠ p.2 → ContinuousAt F p := by
          intro p hp_ne
          have h_cont_A : ContinuousAt (fun z => landauMatrix coulombKernel z) (p.1 - p.2) := by
            refine ContinuousAt.smul _ _ <;> norm_num [ ContinuousAt ]
            · have h_cont_eucNorm : ContinuousAt (fun z => eucNorm z) (p.1 - p.2) := by
                exact Continuous.continuousAt
                  (by exact Real.continuous_sqrt.comp <|
                    by exact Continuous.dotProduct continuous_id continuous_id)
              have h_pos : 0 < eucNorm (p.1 - p.2) := by
                unfold eucNorm
                unfold normSq; simp +decide [ sub_eq_zero, hp_ne ]
                simp_all +decide [ dotProduct, Fin.sum_univ_three ]
                exact not_le.mp fun h => hp_ne <| by
                  ext i; fin_cases i <;> nlinarith! [ sq_nonneg (p.1 0 - p.2 0),
                    sq_nonneg (p.1 1 - p.2 1), sq_nonneg (p.1 2 - p.2 2) ]
              have h_cont_coulomb :
                  ContinuousAt (fun z => coulombKernel z) (eucNorm (p.1 - p.2)) := by
                refine ContinuousAt.congr _ _
                use fun z => z ^ ( -3 : ℝ)
                · exact ContinuousAt.rpow continuousAt_id continuousAt_const <|
                    Or.inl <| ne_of_gt h_pos
                · filter_upwards [ lt_mem_nhds h_pos ] with z hz using by
                    unfold coulombKernel; split_ifs <;> linarith
              exact h_cont_coulomb.comp h_cont_eucNorm
            · refine Continuous.tendsto _ _
              exact Continuous.smul
                (show Continuous fun z : Fin 3 → ℝ => normSq z from
                  by exact Continuous.matrix_dotProduct (continuous_id') (continuous_id') )
                (continuous_const)
                |> Continuous.sub <| Continuous.matrix_vecMulVec (continuous_id') (continuous_id')
          have h_cont_G : ContinuousAt (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => G p.1 - G p.2) p := by
            exact ContinuousAt.sub
              (hG.continuous.continuousAt.comp continuousAt_fst)
              (hG.continuous.continuousAt.comp continuousAt_snd)
          have h_cont_F : ContinuousAt (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
              (G p.1 - G p.2) ⬝ᵥ
              (landauMatrix coulombKernel (p.1 - p.2)) *ᵥ (G p.1 - G p.2)) p := by
            fun_prop (disch := norm_num)
          exact h_cont_F
        refine continuous_iff_continuousAt.mpr fun p =>
          if hp : p.1 = p.2 then _ else h_cont_away p hp
        have h_tendsto : Filter.Tendsto F (nhds (p.1, p.1)) (nhds 0) := by
          convert tendsto_landau_quadratic_diag G hG p.1 using 1
        rw [ ContinuousAt ] ; aesop

/-- PSD integrand is jointly continuous for Coulomb kernel.
    Despite Ψ(r) = r⁻³ being singular, the score difference cancels the singularity.
    Proved by Aristotle (job 14300a69).
    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma psd_continuous_coulomb
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f) :
    Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      PSDIntegrand coulombKernel f p.1 p.2) := by
  refine Continuous.mul
    (Continuous.mul
      (hf_smooth.continuous.comp continuous_fst)
      (hf_smooth.continuous.comp continuous_snd) ) _
  set G := fun v => fderiv ℝ (Real.log ∘ f) v
  have h_log_smooth : ContDiff ℝ ⊤ (Real.log ∘ f) := by
    exact ContDiff.log hf_smooth fun v => ne_of_gt <| hf_pos v
  have h_G_smooth : ContDiff ℝ 1 G := by
    apply_rules [ ContDiff.fderiv, h_log_smooth ]
    exacts [ h_log_smooth.comp (contDiff_snd), contDiff_id, by norm_num ]
  convert continuous_landau_quadratic (fun v => (fun i => G v (Pi.single i 1) )) _ using 1
  exact contDiff_pi.mpr fun i => h_G_smooth.clm_apply (contDiff_const)


/-- Pointwise bound on PSD integrand for Coulomb kernel:
    |PSD(v,w)| ≤ 18Cg²f(v) * ((1+‖v‖)^{2Kg}·‖v-w‖⁻¹f(w) + ‖v-w‖⁻¹·(1+‖w‖)^{2Kg}f(w)) -/
lemma psd_pointwise_bound_coulomb
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v)
    {Cg : ℝ} {Kg : ℕ}
    (h_score : ∀ u i, |vGrad (Real.log ∘ f) u i| ≤ Cg * (1 + ‖u‖) ^ Kg)
    (v w : Fin 3 → ℝ) :
    |PSDIntegrand coulombKernel f v w| ≤
    18 * Cg ^ 2 * f v * ((1 + ‖v‖) ^ (2 * Kg) * (‖v - w‖⁻¹ * f w) +
                          ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w)) := by
  unfold PSDIntegrand
  set Δ := vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w
  rw [abs_mul, abs_mul, abs_of_pos (hf_pos v), abs_of_pos (hf_pos w)]
  by_cases hvw : v - w = 0
  · have hveqw : v = w := sub_eq_zero.mp hvw; subst hveqw
    simp only [Δ, sub_self, Pi.zero_apply, dotProduct, mulVec, Finset.sum_const_zero,
      mul_zero, abs_zero]; positivity
  · have h_entry : ∀ i j, |landauMatrix coulombKernel (v - w) i j| ≤ ‖v - w‖⁻¹ :=
      fun i j => coulomb_landauMatrix_entry_le_pi _ i j hvw
    have h_mulvec : ∀ i, |(mulVec (landauMatrix coulombKernel (v - w)) Δ) i| ≤
        ‖v - w‖⁻¹ * ∑ j : Fin 3, |Δ j| := by
      intro i; simp only [mulVec, dotProduct]
      calc |∑ j, landauMatrix coulombKernel (v - w) i j * Δ j|
          ≤ ∑ j, |landauMatrix coulombKernel (v - w) i j| * |Δ j| := by
            exact le_trans (Finset.abs_sum_le_sum_abs _ _)
              (Finset.sum_le_sum fun j _ => (abs_mul _ _).le)
        _ ≤ ∑ j, ‖v - w‖⁻¹ * |Δ j| :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_right (h_entry i j) (abs_nonneg _)
        _ = ‖v - w‖⁻¹ * ∑ j, |Δ j| := (Finset.mul_sum _ _ _).symm
    have h_quad : |dotProduct Δ (mulVec (landauMatrix coulombKernel (v - w)) Δ)| ≤
        ‖v - w‖⁻¹ * (∑ i : Fin 3, |Δ i|) ^ 2 := by
      simp only [dotProduct]
      calc |∑ i, Δ i * (mulVec (landauMatrix coulombKernel (v - w)) Δ) i|
          ≤ ∑ i, |Δ i| * |(mulVec (landauMatrix coulombKernel (v - w)) Δ) i| := by
            exact le_trans (Finset.abs_sum_le_sum_abs _ _)
              (Finset.sum_le_sum fun i _ => (abs_mul _ _).le)
        _ ≤ ∑ i, |Δ i| * (‖v - w‖⁻¹ * ∑ j, |Δ j|) :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (h_mulvec i) (abs_nonneg _)
        _ = ‖v - w‖⁻¹ * (∑ i : Fin 3, |Δ i|) ^ 2 := by
            rw [sq, ← Finset.sum_mul]; ring
    have h_delta_sum : ∑ i : Fin 3, |Δ i| ≤
        3 * Cg * ((1 + ‖v‖) ^ Kg + (1 + ‖w‖) ^ Kg) := by
      simp only [Δ, Pi.sub_apply]
      calc ∑ i : Fin 3, |vGrad (Real.log ∘ f) v i - vGrad (Real.log ∘ f) w i|
          ≤ ∑ i : Fin 3, (Cg * (1 + ‖v‖) ^ Kg + Cg * (1 + ‖w‖) ^ Kg) :=
            Finset.sum_le_sum fun i _ => by
              have := norm_sub_le (vGrad (Real.log ∘ f) v i) (vGrad (Real.log ∘ f) w i)
              rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at this
              linarith [h_score v i, h_score w i]
        _ = 3 * Cg * ((1 + ‖v‖) ^ Kg + (1 + ‖w‖) ^ Kg) := by
            simp [Fin.sum_univ_three]; ring
    have h_sq_bound : (∑ i : Fin 3, |Δ i|) ^ 2 ≤
        18 * Cg ^ 2 * ((1 + ‖v‖) ^ (2 * Kg) + (1 + ‖w‖) ^ (2 * Kg)) := by
      have h1 : (∑ i : Fin 3, |Δ i|) ^ 2 ≤
          9 * Cg ^ 2 * ((1 + ‖v‖) ^ Kg + (1 + ‖w‖) ^ Kg) ^ 2 := by
        calc _ ≤ (3 * Cg * ((1 + ‖v‖) ^ Kg + (1 + ‖w‖) ^ Kg)) ^ 2 :=
              sq_le_sq' (by linarith [Finset.sum_nonneg
                (s := Finset.univ) (fun (i : Fin 3) _ => abs_nonneg (Δ i))]) h_delta_sum
          _ = _ := by ring
      have h2 : ((1 + ‖v‖) ^ Kg + (1 + ‖w‖) ^ Kg) ^ 2 ≤
          2 * ((1 + ‖v‖) ^ (2 * Kg) + (1 + ‖w‖) ^ (2 * Kg)) := by
        rw [show 2 * Kg = Kg + Kg from by omega, pow_add, pow_add]
        nlinarith [sq_nonneg ((1 + ‖v‖) ^ Kg - (1 + ‖w‖) ^ Kg)]
      nlinarith
    calc f v * f w * |dotProduct Δ (mulVec (landauMatrix coulombKernel (v - w)) Δ)|
        ≤ f v * f w * (‖v - w‖⁻¹ *
            (18 * Cg ^ 2 * ((1 + ‖v‖) ^ (2 * Kg) + (1 + ‖w‖) ^ (2 * Kg)))) := by
          gcongr; exact le_trans h_quad (mul_le_mul_of_nonneg_left h_sq_bound
            (inv_nonneg.mpr (norm_nonneg _)))
      _ = 18 * Cg ^ 2 * f v * ((1 + ‖v‖) ^ (2 * Kg) * (‖v - w‖⁻¹ * f w) +
               ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w)) := by ring

end VML
end
