/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1ba752be-d63d-478b-9620-9ea7a9260511

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma convolution_local_int_schwartz
    (g : (Fin 3 → ℝ) → ℝ)
    (hg_decay : ∀ N : ℕ, ∃ C > 0, ∀ w : Fin 3 → ℝ, |g w| * (1 + ‖w‖) ^ N ≤ C)
    (hg_meas : AEStronglyMeasurable g volume)
    (hK_local : IntegrableOn (fun z : Fin 3 → ℝ => ‖z‖⁻¹)
      (Metric.closedBall (0 : Fin 3 → ℝ) 1))
    (v : Fin 3 → ℝ) :
    Integrable (fun w => ‖v - w‖⁻¹ * g w)
-/

import Mathlib


set_option linter.all false

set_option maxHeartbeats 800000

open MeasureTheory Real

noncomputable section

-- Harmonic `generalize_proofs` tactic

/-- Convolution of a locally integrable kernel with a Schwartz function is integrable.
    Splits the integral at ‖v-w‖ = 1:
    - Near part (‖v-w‖ ≤ 1): K is locally integrable and g is bounded → product integrable
    - Far part (‖v-w‖ > 1): K ≤ 1 and g is integrable → product integrable -/
lemma convolution_local_int_schwartz
    (g : (Fin 3 → ℝ) → ℝ)
    (hg_decay : ∀ N : ℕ, ∃ C > 0, ∀ w : Fin 3 → ℝ, |g w| * (1 + ‖w‖) ^ N ≤ C)
    (hg_meas : AEStronglyMeasurable g volume)
    (hK_local : IntegrableOn (fun z : Fin 3 → ℝ => ‖z‖⁻¹)
      (Metric.closedBall (0 : Fin 3 → ℝ) 1))
    (v : Fin 3 → ℝ) :
    Integrable (fun w => ‖v - w‖⁻¹ * g w) := by
      have h_integrable : MeasureTheory.IntegrableOn (fun w => ‖v - w‖⁻¹ * g w) (Metric.closedBall v 1) ∧ MeasureTheory.IntegrableOn (fun w => ‖v - w‖⁻¹ * g w) (Set.univ \ Metric.closedBall v 1) := by
        field_simp;
        constructor;
        · -- Since $g$ is bounded on the compact set $Metric.closedBall v 1$, we can find a constant $M$ such that $|g(w)| \leq M$ for all $w \in Metric.closedBall v 1$.
          obtain ⟨M, hM⟩ : ∃ M > 0, ∀ w ∈ Metric.closedBall v 1, |g w| ≤ M := by
            obtain ⟨ C, hC₀, hC ⟩ := hg_decay 0 ; exact ⟨ C, hC₀, fun w hw => by simpa using hC w ⟩ ;
          -- Since $g$ is bounded on the compact set $Metric.closedBall v 1$, we can use the fact that the product of a bounded function and an integrable function is integrable.
          have h_prod_integrable : MeasureTheory.IntegrableOn (fun w => M / ‖v - w‖) (Metric.closedBall v 1) := by
            have h_integrable : MeasureTheory.IntegrableOn (fun w => ‖v - w‖⁻¹) (Metric.closedBall v 1) := by
              rw [ ← MeasureTheory.integrable_indicator_iff ( measurableSet_closedBall ) ] at *;
              convert hK_local.comp_sub_left v using 1;
              ext; simp [Set.indicator];
              simp +decide [ dist_eq_norm', norm_sub_rev ];
            simpa only [ div_eq_mul_inv ] using h_integrable.const_mul M;
          refine' h_prod_integrable.mono' _ _;
          · exact MeasureTheory.AEStronglyMeasurable.mul ( hg_meas.mono_measure <| MeasureTheory.Measure.restrict_le_self ) ( Measurable.aestronglyMeasurable <| by exact Measurable.inv <| measurable_norm.comp <| measurable_const.sub measurable_id' );
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_closedBall ] with w hw using by simpa [ abs_div ] using div_le_div_of_nonneg_right ( hM.2 w hw ) ( norm_nonneg _ ) ;
        · -- For the far part, we use the fact that $K \leq 1$ and $g$ is integrable.
          have h_far_integrable : MeasureTheory.IntegrableOn (fun w => g w) (Set.univ \ Metric.closedBall v 1) := by
            have h_integrable_g : MeasureTheory.Integrable g := by
              obtain ⟨ C, hC₀, hC ⟩ := hg_decay 4;
              -- Since $|g(w)| \leq \frac{C}{(1 + \|w\|)^4}$ and $\frac{C}{(1 + \|w\|)^4}$ is integrable, we can apply the comparison test.
              have h_integrable : MeasureTheory.Integrable (fun w : Fin 3 → ℝ => C / (1 + ‖w‖) ^ 4) MeasureTheory.MeasureSpace.volume := by
                have h_integrable : MeasureTheory.Integrable (fun w : Fin 3 → ℝ => (1 + ‖w‖) ^ (-4 : ℝ)) MeasureTheory.MeasureSpace.volume := by
                  have h_integrable : MeasureTheory.Integrable (fun w : Fin 3 → ℝ => (1 + ‖w‖) ^ (-4 : ℝ)) MeasureTheory.MeasureSpace.volume := by
                    have h_integrable : ∀ w : Fin 3 → ℝ, (1 + ‖w‖) ^ (-4 : ℝ) ≤ (1 + ‖w‖ ^ 2) ^ (-2 : ℝ) := by
                      intro w; rw [ Real.rpow_neg ( by positivity ), Real.rpow_neg ( by positivity ) ] ; norm_cast; norm_num; ring_nf; (
                      exact inv_anti₀ ( by positivity ) ( by nlinarith [ norm_nonneg w ] ));
                    have h_integrable : MeasureTheory.Integrable (fun w : Fin 3 → ℝ => (1 + ‖w‖ ^ 2) ^ (-2 : ℝ)) MeasureTheory.MeasureSpace.volume := by
                      have := @integrable_rpow_neg_one_add_norm_sq;
                      convert @this ( Fin 3 → ℝ ) _ _ _ _ _ ( MeasureTheory.MeasureSpace.volume ) _ 4 ( by norm_num ) using 1 ; norm_num [ div_eq_mul_inv ];
                    refine' h_integrable.mono' _ _;
                    · exact Measurable.aestronglyMeasurable ( by exact Measurable.pow_const ( by exact measurable_const.add ( measurable_norm ) ) _ );
                    · filter_upwards [ ] using fun w => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact ‹∀ w : Fin 3 → ℝ, ( 1 + ‖w‖ ) ^ ( -4 : ℝ ) ≤ ( 1 + ‖w‖ ^ 2 ) ^ ( -2 : ℝ ) › w;
                  exact h_integrable;
                norm_cast at * ; simpa using h_integrable.const_mul C;
              refine' h_integrable.mono' _ _;
              · exact hg_meas;
              · filter_upwards [ ] with w using by rw [ le_div_iff₀ ( by positivity ) ] ; exact hC w;
            exact h_integrable_g.integrableOn;
          refine' h_far_integrable.norm.mono' _ _;
          · exact MeasureTheory.AEStronglyMeasurable.mul ( h_far_integrable.aestronglyMeasurable ) ( Measurable.aestronglyMeasurable ( by exact Measurable.inv ( measurable_norm.comp ( measurable_const.sub measurable_id' ) ) ) );
          · simp +zetaDelta at *;
            filter_upwards [ MeasureTheory.ae_restrict_mem ( show MeasurableSet ( Set.univ \ Metric.closedBall v 1 ) from MeasurableSet.univ.diff ( measurableSet_closedBall ) ) ] with w hw using div_le_self ( abs_nonneg _ ) ( by rw [ norm_sub_rev ] ; exact le_of_not_gt fun h => hw.2 <| mem_closedBall_iff_norm.mpr <| by linarith );
      convert h_integrable.1.union h_integrable.2 using 1 ; aesop