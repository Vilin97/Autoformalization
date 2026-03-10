import Aristotle.Landau.main.CoulombFlux

set_option linter.all false
open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

def PSDIntegrand' (f : (Fin 3 → ℝ) → ℝ) (v w : Fin 3 → ℝ) : ℝ :=
  f v * f w *
    dotProduct (vGrad' (Real.log ∘ f) v - vGrad' (Real.log ∘ f) w)
      (mulVec (landauMatrix' (v - w))
        (vGrad' (Real.log ∘ f) v - vGrad' (Real.log ∘ f) w))

lemma PSDIntegrand'_eq_PSDIntegrand (f : (Fin 3 → ℝ) → ℝ) (v w : Fin 3 → ℝ) :
    PSDIntegrand' f v w = PSDIntegrand coulombKernel f v w := rfl

set_option maxHeartbeats 800000 in
lemma landau_bound (z u : Fin 3 → ℝ) :
    abs (dotProduct u (mulVec (landauMatrix' z) u)) ≤
    (if eucNorm' z = 0 then 0 else (eucNorm' z)⁻¹) * (eucNorm' u)^2 := by
      unfold landauMatrix' eucNorm';
      unfold coulombKernel' innerLandauMatrix' normSq';
      split_ifs <;> norm_cast <;> norm_num [ Matrix.vecMulVec ] at *;
      · simp_all +decide [ Fin.sum_univ_three, dotProduct ];
        rw [ Real.sqrt_eq_zero' ] at *; norm_num [ show z 0 = 0 by nlinarith, show z 1 = 0 by nlinarith, show z 2 = 0 by nlinarith, Matrix.mulVec ] ;
      · exact False.elim <| ‹¬Real.sqrt ( z ⬝ᵥ z ) = 0› <| le_antisymm ‹_› <| Real.sqrt_nonneg _;
      · rw [ Real.sqrt_eq_zero' ] at * ; linarith;
      · suffices h_simp : abs ((Real.sqrt (dotProduct z z))⁻¹ ^ 3 * (dotProduct z z * dotProduct u u - (dotProduct z u) ^ 2)) ≤ (Real.sqrt (dotProduct z z))⁻¹ * (Real.sqrt (dotProduct u u)) ^ 2 by
          convert h_simp using 2 ; norm_num [ Matrix.mulVec, dotProduct ] ; ring;
          norm_num [ Fin.sum_univ_three, Matrix.one_apply ] ; ring;
        suffices h_cancel : abs (z ⬝ᵥ z * u ⬝ᵥ u - (z ⬝ᵥ u) ^ 2) ≤ (Real.sqrt (z ⬝ᵥ z)) ^ 2 * (Real.sqrt (u ⬝ᵥ u)) ^ 2 by
          rw [ abs_mul, abs_of_nonneg ( by positivity ) ];
          field_simp;
          exact h_cancel;
        rw [ Real.sq_sqrt ( by positivity ), Real.sq_sqrt ( by exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _ ) ];
        norm_num [ Fin.sum_univ_three, dotProduct ] at *;
        exact abs_le.mpr ⟨ by nlinarith [ sq_nonneg ( z 0 * u 1 - z 1 * u 0 ), sq_nonneg ( z 0 * u 2 - z 2 * u 0 ), sq_nonneg ( z 1 * u 2 - z 2 * u 1 ) ], by nlinarith [ sq_nonneg ( z 0 * u 1 - z 1 * u 0 ), sq_nonneg ( z 0 * u 2 - z 2 * u 0 ), sq_nonneg ( z 1 * u 2 - z 2 * u 1 ) ] ⟩

set_option maxHeartbeats 1600000 in
lemma tendsto_landau_quadratic_diag
    (G : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hG : ContDiff ℝ 1 G)
    (x : Fin 3 → ℝ) :
    Filter.Tendsto (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      dotProduct (G p.1 - G p.2) (mulVec (landauMatrix' (p.1 - p.2)) (G p.1 - G p.2))) (nhds (x, x)) (nhds 0) := by
        obtain ⟨U, hU⟩ : ∃ U : Set (Fin 3 → ℝ), IsOpen U ∧ x ∈ U ∧ ∃ L : ℝ, ∀ u v : Fin 3 → ℝ, u ∈ U → v ∈ U → eucNorm' (G u - G v) ≤ L * eucNorm' (u - v) := by
          obtain ⟨U, hU⟩ : ∃ U : Set (Fin 3 → ℝ), IsOpen U ∧ x ∈ U ∧ ∃ L : ℝ, ∀ u ∈ U, ∀ v ∈ U, ‖G u - G v‖ ≤ L * ‖u - v‖ := by
            have := hG.differentiable le_rfl;
            obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ u ∈ Metric.closedBall x 1, ‖fderiv ℝ G u‖ ≤ K := by
              exact IsCompact.exists_bound_of_continuousOn ( ProperSpace.isCompact_closedBall x 1 ) ( hG.continuous_fderiv le_rfl |> Continuous.continuousOn );
            refine' ⟨ Metric.ball x 1, Metric.isOpen_ball, Metric.mem_ball_self zero_lt_one, K, _ ⟩;
            intro u hu v hv
            have h_mean_value : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖deriv (fun t => G (v + t • (u - v))) t‖ ≤ K * ‖u - v‖ := by
              intro t ht
              have h_mean_value : ‖deriv (fun t => G (v + t • (u - v))) t‖ = ‖(fderiv ℝ G (v + t • (u - v))) (u - v)‖ := by
                rw [ deriv ];
                erw [ fderiv_comp ] <;> norm_num [ this.differentiableAt, fderiv_deriv ];
                rw [ deriv_pi ] <;> norm_num [ Fin.forall_fin_succ ];
                rw [ ← map_sub ] ; rfl;
              refine' h_mean_value ▸ le_trans ( ContinuousLinearMap.le_opNorm _ _ ) ( mul_le_mul_of_nonneg_right ( hK _ _ ) ( norm_nonneg _ ) );
              simp_all +decide [ dist_eq_norm ];
              rw [ show v + t • ( u - v ) - x = ( 1 - t ) • ( v - x ) + t • ( u - x ) by ext i; simpa using by ring ];
              exact le_trans ( norm_add_le _ _ ) ( by rw [ norm_smul, norm_smul, Real.norm_of_nonneg ( by linarith : 0 ≤ 1 - t ), Real.norm_of_nonneg ( by linarith : 0 ≤ t ) ] ; nlinarith );
            have h_ftc : G u - G v = ∫ t in (0 : ℝ)..1, deriv (fun t => G (v + t • (u - v))) t := by
              rw [ intervalIntegral.integral_deriv_eq_sub ];
              · norm_num;
              · exact fun t ht => this.differentiableAt.comp _ ( DifferentiableAt.add ( differentiableAt_const _ ) ( differentiableAt_id.smul_const _ ) );
              · apply_rules [ Continuous.intervalIntegrable ];
                apply_rules [ ContDiff.continuous_deriv ];
                exacts [ hG.comp ( contDiff_const.add ( contDiff_id.smul contDiff_const ) ), by norm_num ];
            rw [ h_ftc ];
            refine' le_trans ( intervalIntegral.norm_integral_le_of_norm_le_const _ ) _;
            exacts [ K * ‖u - v‖, fun t ht => h_mean_value t <| by constructor <;> cases Set.mem_uIoc.mp ht <;> linarith, by norm_num ];
          obtain ⟨ L, hL ⟩ := hU.2.2;
          refine' ⟨ U, hU.1, hU.2.1, 3 * L, fun u v hu hv => _ ⟩;
          have h_euc_norm : eucNorm' (G u - G v) ≤ Real.sqrt 3 * ‖G u - G v‖ ∧ eucNorm' (u - v) ≥ ‖u - v‖ := by
            unfold eucNorm';
            norm_num [ normSq', Pi.norm_def ];
            constructor <;> norm_num [ Fin.sum_univ_three, dotProduct ] at * <;> ring_nf at * <;> norm_num at *;
            · rw [ Real.sqrt_le_iff ] ; norm_num [ Fin.univ_succ ] ; ring_nf ; norm_num;
              nlinarith only [ abs_le.mp ( show |G u 0 - G v 0| ≤ Max.max |G u 0 - G v 0| ( Max.max |G u 1 - G v 1| |G u 2 - G v 2| ) by exact le_max_left _ _ ), abs_le.mp ( show |G u 1 - G v 1| ≤ Max.max |G u 0 - G v 0| ( Max.max |G u 1 - G v 1| |G u 2 - G v 2| ) by exact le_max_of_le_right ( le_max_left _ _ ) ), abs_le.mp ( show |G u 2 - G v 2| ≤ Max.max |G u 0 - G v 0| ( Max.max |G u 1 - G v 1| |G u 2 - G v 2| ) by exact le_max_of_le_right ( le_max_right _ _ ) ) ];
            · refine' Real.le_sqrt_of_sq_le _ ; norm_num [ Fin.univ_succ ] ; ring_nf ; (
              rw [ max_def, max_def ] ; split_ifs <;> nlinarith [ sq_nonneg ( u 0 - v 0 ), sq_nonneg ( u 1 - v 1 ), sq_nonneg ( u 2 - v 2 ), abs_mul_abs_self ( u 0 - v 0 ), abs_mul_abs_self ( u 1 - v 1 ), abs_mul_abs_self ( u 2 - v 2 ) ] ;);
          refine le_trans h_euc_norm.1 ?_;
          refine le_trans ( mul_le_mul_of_nonneg_left ( hL u hu v hv ) ( Real.sqrt_nonneg _ ) ) ?_;
          rw [ mul_assoc ];
          gcongr;
          · exact le_trans ( norm_nonneg _ ) ( hL u hu v hv );
          · rw [ Real.sqrt_le_left ] <;> norm_num;
          · contrapose! hL;
            obtain ⟨u, hu, v, hv, huv⟩ : ∃ u ∈ U, ∃ v ∈ U, u ≠ v := by
              rcases Metric.isOpen_iff.mp hU.1 x hU.2.1 with ⟨ ε, εpos, hε ⟩;
              exact ⟨ x, hε <| Metric.mem_ball_self εpos, x + fun _ => ε / 2, hε <| Metric.mem_ball.mpr <| by simpa [ abs_of_pos εpos ] using by linarith, ne_of_apply_ne ( fun u => u 0 ) <| by norm_num; linarith ⟩;
            exact ⟨ u, hu, v, hv, lt_of_lt_of_le ( mul_neg_of_neg_of_pos hL ( norm_pos_iff.mpr ( sub_ne_zero.mpr huv ) ) ) ( norm_nonneg _ ) ⟩;
          · exact h_euc_norm.2;
        obtain ⟨L, hL⟩ := hU.right.right;
        have h_bound : ∀ᶠ p : (Fin 3 → ℝ) × (Fin 3 → ℝ) in nhds (x, x), abs ((G p.1 - G p.2) ⬝ᵥ landauMatrix' (p.1 - p.2) *ᵥ (G p.1 - G p.2)) ≤ (if eucNorm' (p.1 - p.2) = 0 then 0 else (eucNorm' (p.1 - p.2))⁻¹) * (L * eucNorm' (p.1 - p.2))^2 := by
          have h_bound : ∀ᶠ p : (Fin 3 → ℝ) × (Fin 3 → ℝ) in nhds (x, x), eucNorm' (G p.1 - G p.2) ≤ L * eucNorm' (p.1 - p.2) := by
            exact Filter.eventually_of_mem ( IsOpen.mem_nhds ( hU.1.prod hU.1 ) ( by aesop ) ) fun p hp => hL _ _ hp.1 hp.2;
          filter_upwards [ h_bound ] with p hp;
          refine' le_trans ( landau_bound _ _ ) _;
          split_ifs <;> simp_all +decide [ mul_pow ];
          exact mul_le_mul_of_nonneg_left ( by nlinarith [ show 0 ≤ eucNorm' ( G p.1 - G p.2 ) from Real.sqrt_nonneg _, show 0 ≤ L * eucNorm' ( p.1 - p.2 ) from le_trans ( Real.sqrt_nonneg _ ) hp ] ) ( inv_nonneg.2 ( Real.sqrt_nonneg _ ) );
        have h_simplified_bound : ∀ᶠ p : (Fin 3 → ℝ) × (Fin 3 → ℝ) in nhds (x, x), abs ((G p.1 - G p.2) ⬝ᵥ landauMatrix' (p.1 - p.2) *ᵥ (G p.1 - G p.2)) ≤ L^2 * eucNorm' (p.1 - p.2) := by
          filter_upwards [ h_bound ] with p hp using le_trans hp ( by split_ifs <;> simpa [ *, sq, mul_assoc, mul_comm, mul_left_comm ] using by ring_nf; norm_num ) ;
        refine' squeeze_zero_norm' h_simplified_bound _;
        refine' Continuous.tendsto' _ _ _ _ <;> norm_num [ eucNorm' ];
        · exact Continuous.mul continuous_const <| Real.continuous_sqrt.comp <| Continuous.dotProduct ( continuous_fst.sub continuous_snd ) ( continuous_fst.sub continuous_snd );
        · norm_num [ normSq' ]

set_option maxHeartbeats 1600000 in
lemma continuous_landau_quadratic
    (G : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hG : ContDiff ℝ 1 G) :
    Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      dotProduct (G p.1 - G p.2) (mulVec (landauMatrix' (p.1 - p.2)) (G p.1 - G p.2))) := by
        set F : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) → ℝ := fun p => (G p.1 - G p.2) ⬝ᵥ landauMatrix' (p.1 - p.2) *ᵥ (G p.1 - G p.2);
        have h_cont_away : ∀ p : (Fin 3 → ℝ) × (Fin 3 → ℝ), p.1 ≠ p.2 → ContinuousAt F p := by
          intro p hp_ne
          have h_cont_A : ContinuousAt (fun z => landauMatrix' z) (p.1 - p.2) := by
            refine' ContinuousAt.smul _ _ <;> norm_num [ ContinuousAt ];
            · have h_cont_eucNorm : ContinuousAt (fun z => eucNorm' z) (p.1 - p.2) := by
                exact Continuous.continuousAt ( by exact Real.continuous_sqrt.comp <| by exact Continuous.dotProduct continuous_id continuous_id )
              have h_pos : 0 < eucNorm' (p.1 - p.2) := by
                unfold eucNorm' ;
                unfold normSq'; simp +decide [ sub_eq_zero, hp_ne ] ;
                simp_all +decide [ dotProduct, Fin.sum_univ_three ];
                exact not_le.mp fun h => hp_ne <| by ext i; fin_cases i <;> nlinarith! [ sq_nonneg ( p.1 0 - p.2 0 ), sq_nonneg ( p.1 1 - p.2 1 ), sq_nonneg ( p.1 2 - p.2 2 ) ] ;
              have h_cont_coulomb : ContinuousAt (fun z => coulombKernel' z) (eucNorm' (p.1 - p.2)) := by
                refine' ContinuousAt.congr _ _;
                use fun z => z ^ ( -3 : ℝ );
                · exact ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| ne_of_gt h_pos;
                · filter_upwards [ lt_mem_nhds h_pos ] with z hz using by unfold coulombKernel'; split_ifs <;> linarith;
              exact h_cont_coulomb.comp h_cont_eucNorm;
            · refine' Continuous.tendsto _ _;
              exact Continuous.smul ( show Continuous fun z : Fin 3 → ℝ => normSq' z from by exact Continuous.matrix_dotProduct ( continuous_id' ) ( continuous_id' ) ) ( continuous_const ) |> Continuous.sub <| Continuous.matrix_vecMulVec ( continuous_id' ) ( continuous_id' )
          have h_cont_G : ContinuousAt (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => G p.1 - G p.2) p := by
            exact ContinuousAt.sub ( hG.continuous.continuousAt.comp continuousAt_fst ) ( hG.continuous.continuousAt.comp continuousAt_snd )
          have h_cont_F : ContinuousAt (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => (G p.1 - G p.2) ⬝ᵥ (landauMatrix' (p.1 - p.2)) *ᵥ (G p.1 - G p.2)) p := by
            fun_prop (disch := norm_num)
          exact h_cont_F;
        refine' continuous_iff_continuousAt.mpr fun p => if hp : p.1 = p.2 then _ else h_cont_away p hp;
        have h_tendsto : Filter.Tendsto F (nhds (p.1, p.1)) (nhds 0) := by
          convert tendsto_landau_quadratic_diag G hG p.1 using 1;
        rw [ ContinuousAt ] ; aesop;

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
  -- Bridge: PSDIntegrand coulombKernel = PSDIntegrand' by rfl
  show Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => PSDIntegrand' f p.1 p.2)
  refine' Continuous.mul ( Continuous.mul ( hf_smooth.continuous.comp continuous_fst ) ( hf_smooth.continuous.comp continuous_snd ) ) _;
  set G := fun v => fderiv ℝ (Real.log ∘ f) v;
  have h_log_smooth : ContDiff ℝ ⊤ (Real.log ∘ f) := by
    exact ContDiff.log hf_smooth fun v => ne_of_gt <| hf_pos v;
  have h_G_smooth : ContDiff ℝ 1 G := by
    apply_rules [ ContDiff.fderiv, h_log_smooth ];
    exacts [ h_log_smooth.comp ( contDiff_snd ), contDiff_id, by norm_num ];
  convert continuous_landau_quadratic ( fun v => ( fun i => G v ( Pi.single i 1 ) ) ) _ using 1;
  exact contDiff_pi.mpr fun i => h_G_smooth.clm_apply ( contDiff_const )

set_option maxHeartbeats 1600000 in
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

set_option maxHeartbeats 3200000 in
/-- PSD integrand is integrable for Coulomb kernel (inner integral, fixing v).
    Uses element-wise Coulomb matrix bound |A_{ij}| ≤ ‖z‖⁻¹ combined with
    polynomial score bound and Newtonian potential of Schwartz functions. -/
lemma psd_inner_integrable_coulomb
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
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
    intro N; obtain ⟨C, hC, hb⟩ := hf_schwartz N 0
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

set_option maxHeartbeats 3200000 in
/-- PSD integrand is integrable for Coulomb kernel (outer integral).
    Uses pointwise bound + Newtonian uniform bounds + Schwartz decay. -/
lemma psd_outer_integrable_coulomb
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
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
    fun N => (hf_schwartz N 0).imp fun C ⟨hC, hb⟩ =>
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
    ((continuous_const.add continuous_norm).pow _ |>.mul hf_smooth.continuous).aestronglyMeasurable v
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

set_option maxHeartbeats 3200000 in
/-- The Fubini integrand (score · flux) is jointly integrable on the product space
    for the Coulomb kernel. Uses `integrable_prod_iff` with:
    - Joint measurability from measurability of each factor
    - Inner integrability from `landau_flux_integrable_coulomb`
    - Norm integral bound from PSD pointwise bound + Newtonian uniform bounds -/
lemma fubini_double_integrable_coulomb
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
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
    fun N => (hf_schwartz N 0).imp fun C ⟨hC, hb⟩ =>
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
    ((continuous_const.add continuous_norm).pow _ |>.mul hf_smooth.continuous).aestronglyMeasurable v
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
  -- |F(v,w)| ≤ 3 * Cg * (1+‖v‖)^Kg * ‖v-w‖⁻¹ * (3*Cg*(1+‖v‖)^Kg*f(w) + ... )
  -- But more directly: |F(v,w)| = |score(v) · (A·flux)(v,w)|
  -- ≤ (∑_i |score_i(v)|) * max_i |(A·flux)_i(v,w)|
  -- The bound on (A·flux)_i follows from |A_{ij}| ≤ ‖v-w‖⁻¹
  -- Overall: |F(v,w)| ≤ 3*Cg*(1+‖v‖)^Kg * ‖v-w‖⁻¹ * (3*Cg*(1+‖v‖)^Kg*f(w) + 3*f(v)*... )
  -- Actually, let's use a cleaner approach: bound via the PSD-style bound
  have h_norm_int : Integrable (fun v => ∫ w, ‖F (v, w)‖) := by
    -- Pointwise bound: |F(v,w)| ≤ 3Cg(1+‖v‖)^Kg * ‖v-w‖⁻¹ * 3 * (f(w)*3Cg(1+‖v‖)^Kg + f(v)*3Cg(1+‖w‖)^Kg)
    -- which simplifies to 9Cg²(1+‖v‖)^{2Kg} * ‖v-w‖⁻¹ * f(w) + 9Cg²(1+‖v‖)^Kg * f(v) * ‖v-w‖⁻¹ * (1+‖w‖)^Kg * ...
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
      intro j N; obtain ⟨C, hC, hb⟩ := hf_schwartz N 1
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
            congr 1; congr 1; ring
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
                    congr 1; ext j; rw [integral_mul_left]
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
set_option maxHeartbeats 1600000 in
lemma coulomb_entry_schwartz_integrable
    (g : (Fin 3 → ℝ) → ℝ) (hg_smooth : ContDiff ℝ ⊤ g)
    (hg_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k g v‖ * (1 + ‖v‖) ^ N ≤ C)
    (v : Fin 3 → ℝ) (i j : Fin 3) :
    Integrable (fun w => landauMatrix coulombKernel (v - w) i j * g w) := by
  have hg_decay : ∀ N : ℕ, ∃ C > 0, ∀ w, |g w| * (1 + ‖w‖) ^ N ≤ C := by
    intro N; obtain ⟨C, hC, hb⟩ := hg_schwartz N 0
    exact ⟨C, hC, fun w => by simpa [norm_iteratedFDeriv_zero] using hb w⟩
  show Integrable (fun w => landauMatrix' (v - w) i j * g w)
  refine (inv_norm_schwartz_integrable g hg_decay hg_smooth.continuous.aestronglyMeasurable v).mono
    ?_ (ae_of_all _ fun w => ?_)
  · -- AEStronglyMeasurable: matrix entry is measurable, g is continuous
    change AEStronglyMeasurable (fun w => coulombKernel' (eucNorm' (v - w)) *
        innerLandauMatrix' (v - w) i j * g w) volume
    exact ((((Measurable.ite measurableSet_Iic measurable_const
      (measurable_id.pow_const _)).comp ((Continuous.measurable (Continuous.dotProduct
        (continuous_const.sub continuous_id')
        (continuous_const.sub continuous_id'))).sqrt)).mul
      (by apply Continuous.measurable; unfold innerLandauMatrix'
          simp +decide [normSq', vecMulVec]; fun_prop (disch := norm_num)
      )).aestronglyMeasurable).mul hg_smooth.continuous.aestronglyMeasurable
  · -- Domination bound
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    by_cases hvw : v - w = 0
    · have : landauMatrix' 0 i j = 0 := by
        simp +decide [landauMatrix', innerLandauMatrix', normSq', eucNorm', coulombKernel',
          dotProduct, vecMulVec]
      simp [hvw, this]
    · exact mul_le_mul_of_nonneg_right
        (le_trans (le_of_eq (Real.norm_eq_abs _)) (coulomb_landauMatrix_entry_le_pi _ _ _ hvw))
        (norm_nonneg _)

/-- Convolution of a Coulomb kernel matrix entry with a Schwartz function is differentiable.
    After substituting u = v - w, the kernel A(u) doesn't depend on v, so differentiation
    under the integral sign applies via hasFDerivAt_integral_of_dominated_of_fderiv_le:
    the v-derivative acts only on g(v-u), giving a bound
    |A(u)_{ij}| * ‖fderiv g(v-u)‖ ≤ ‖u‖⁻¹ * C/(1+‖u‖)^4 which is integrable in ℝ³. -/
lemma coulomb_entry_conv_differentiable
    (g : (Fin 3 → ℝ) → ℝ) (hg_smooth : ContDiff ℝ ⊤ g)
    (hg_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k g v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i j : Fin 3) :
    Differentiable ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * g w) := by
  sorry

/-- The derivative of a Coulomb entry convolution with a Schwartz function has Schwartz decay.
    Since |A(u)_{ij}| ≤ ‖u‖⁻¹ and derivatives of g decay faster than any polynomial,
    the derivative ∫ A(u)_{ij} * fderiv(g)(v-u) du decays faster than any polynomial in v. -/
lemma coulomb_entry_conv_deriv_decay
    (g : (Fin 3 → ℝ) → ℝ) (hg_smooth : ContDiff ℝ ⊤ g)
    (hg_schwartz : ∀ N k, ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k g v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i j : Fin 3) (N : ℕ) :
    ∃ C > 0, ∀ v, ‖fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * g w) v‖ *
      (1 + ‖v‖) ^ N ≤ C := by
  sorry

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
        ext w; simp [vGrad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]; exact ((h_Af v j).const_mul _).sub ((h_Adf v j).const_mul _))]
    -- Step 4: for each j, expand and distribute the integral
    congr 1; ext j
    have h_eq : ∀ w, landauMatrix coulombKernel (v - w) i j *
        (f w • vGrad f v - f v • vGrad f w) j =
      fderiv ℝ f v (Pi.single j 1) * (landauMatrix coulombKernel (v - w) i j * f w) -
      f v * (landauMatrix coulombKernel (v - w) i j * fderiv ℝ f w (Pi.single j 1)) := by
      intro w; simp [vGrad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
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
      ext w; simp [vGrad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this]; exact ((h_Af j).const_mul _).sub ((h_Adf j).const_mul _))]
  congr 1; ext j
  have h_eq : ∀ w, landauMatrix coulombKernel (v - w) i j *
      (f w • vGrad f v - f v • vGrad f w) j =
    fderiv ℝ f v (Pi.single j 1) * (landauMatrix coulombKernel (v - w) i j * f w) -
    f v * (landauMatrix coulombKernel (v - w) i j * fderiv ℝ f w (Pi.single j 1)) := by
    intro w; simp [vGrad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
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
  -- Each convolution K_{ij}, L_{ij} has Schwartz derivative decay
  have hK_decay : ∀ j N, ∃ C > 0, ∀ v,
      ‖fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * f w) v‖ *
        (1 + ‖v‖) ^ N ≤ C :=
    fun j N => coulomb_entry_conv_deriv_decay f hf_smooth hf_schwartz i j N
  have hL_decay : ∀ j N, ∃ C > 0, ∀ v,
      ‖fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j *
        fderiv ℝ f w (Pi.single j 1)) v‖ * (1 + ‖v‖) ^ N ≤ C :=
    fun j N => coulomb_entry_conv_deriv_decay _ (hf_smooth.fderiv_right le_top |>.clm_apply
      contDiff_const) (hdf_schwartz j) i j N
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
              · simp [hvw, show landauMatrix' 0 i j = 0 from by
                  simp +decide [landauMatrix', innerLandauMatrix', normSq', eucNorm',
                    coulombKernel', dotProduct, vecMulVec]]
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
              · simp [hvw, show landauMatrix' 0 i j = 0 from by
                  simp +decide [landauMatrix', innerLandauMatrix', normSq', eucNorm',
                    coulombKernel', dotProduct, vecMulVec]]
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
    obtain ⟨Mdj, hMdj⟩ := hdf_sup j
    obtain ⟨Cdj, hCdj_pos, hCdj⟩ := schwartz_fderiv_component_schwartz f hf_smooth hf_schwartz j N 1
    obtain ⟨CKj, hCKj_pos, hCKj⟩ := hK_decay j N
    obtain ⟨CLj, hCLj_pos, hCLj⟩ := hL_decay j N
    refine ⟨Mdj * CKj + MK * Cdj + Mf * CLj + (ML + 1) * Cf + 1, by positivity, fun v => ?_⟩
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
      _ ≤ (Mdj * CKj + MK * Cdj + Mf * CLj + (ML + 1) * Cf) * 1 + 0 := by
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
          -- Each term: (bounded) × (decaying × P) ≤ bound₁ × bound₂
          have t1 := mul_le_mul (hMdj v) (hCKj v)
            (by positivity) (le_trans (abs_nonneg _) (hMdj v))
          have t2 := mul_le_mul (hK_sup j v) hCdj_v
            (by positivity) (le_trans (abs_nonneg _) (hK_sup j v))
          have t3 := mul_le_mul (hf_sup v) (hCLj v)
            (by positivity) (le_trans (abs_nonneg _) (hf_sup v))
          have t4 := mul_le_mul (hL_sup j v) hCf_v
            (by positivity) (le_trans (abs_nonneg _) (hL_sup j v))
          nlinarith [t1, t2, t3, t4]
      _ ≤ Mdj * CKj + MK * Cdj + Mf * CLj + (ML + 1) * Cf + 1 := by linarith
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
