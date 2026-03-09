/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3dc1b4dc-f2e7-4f33-9e4e-a6b01f802672

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma inv_norm_local_integrable (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun z : Fin 3 → ℝ => ‖z‖⁻¹)
      (Metric.closedBall (0 : Fin 3 → ℝ) R)
-/

import Mathlib


set_option linter.all false

set_option maxHeartbeats 800000

open MeasureTheory Real

noncomputable section

-- Harmonic `generalize_proofs` tactic

/-- ‖·‖⁻¹ is locally integrable in ℝ³ (finite-dimensional).
    The singularity at 0 is of order r⁻¹ in 3D, and in spherical coordinates
    ∫₀^R r⁻¹ · r² dr = R²/2 < ∞.

    Alternatively, by AM-GM: ‖z‖_∞ ≥ (|z₁|·|z₂|·|z₃|)^{1/3}, so
    ‖z‖⁻¹ ≤ |z₁|^{-1/3} · |z₂|^{-1/3} · |z₃|^{-1/3}.
    By Fubini, ∫ ∏ |zᵢ|^{-1/3} = (∫ |t|^{-1/3} dt)³ < ∞
    since |t|^{-1/3} has exponent -1/3 > -1, so is locally integrable in 1D. -/
lemma inv_norm_local_integrable (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun z : Fin 3 → ℝ => ‖z‖⁻¹)
      (Metric.closedBall (0 : Fin 3 → ℝ) R) := by
        have h_integrable : MeasureTheory.IntegrableOn (fun z : (Fin 3) → ℝ => (‖z‖)⁻¹) (Metric.closedBall 0 R \ {0}) := by
          have h_integrable : ∫⁻ (z : (Fin 3) → ℝ) in Metric.closedBall 0 R \ {0}, ENNReal.ofReal (‖z‖⁻¹) < ⊤ := by
            -- We'll use the fact that if the integral of $|f|$ is finite, then the integral of $f$ is also finite.
            have h_integrable : ∫⁻ (z : Fin 3 → ℝ) in Metric.closedBall 0 R \ {0}, ENNReal.ofReal (‖z‖⁻¹) ≤ ∑' (k : ℕ), ∫⁻ (z : Fin 3 → ℝ) in Metric.closedBall 0 (2^(-k : ℝ) * R) \ Metric.closedBall 0 (2^(-k-1 : ℝ) * R), ENNReal.ofReal (‖z‖⁻¹) := by
              rw [ ← MeasureTheory.lintegral_iUnion ];
              · refine' MeasureTheory.lintegral_mono_set _;
                intro x hx
                obtain ⟨k, hk⟩ : ∃ k : ℕ, 2^(-k-1 : ℝ) * R < ‖x‖ ∧ ‖x‖ ≤ 2^(-k : ℝ) * R := by
                  -- Taking the logarithm base 2 of both sides of the inequality $2^{-k-1}R < \|x\| \leq 2^{-k}R$, we get $-k-1 < \log_2(\|x\|/R) \leq -k$.
                  obtain ⟨k, hk⟩ : ∃ k : ℕ, -k - 1 < Real.logb 2 (‖x‖ / R) ∧ Real.logb 2 (‖x‖ / R) ≤ -k := by
                    use Nat.floor (-Real.logb 2 (‖x‖ / R));
                    constructor <;> linarith [ Nat.floor_le ( show 0 ≤ -Real.logb 2 ( ‖x‖ / R ) by exact neg_nonneg_of_nonpos ( Real.logb_nonpos ( by norm_num ) ( div_nonneg ( norm_nonneg x ) hR.le ) ( div_le_one_of_le₀ ( by simpa using hx.1.out ) hR.le ) ) ), Nat.lt_floor_add_one ( -Real.logb 2 ( ‖x‖ / R ) ) ];
                  rw [ Real.lt_logb_iff_rpow_lt, Real.logb_le_iff_le_rpow ] at hk <;> norm_num at * <;> try positivity;
                  · exact ⟨ k, by rw [ lt_div_iff₀ hR ] at hk; linarith, by rw [ div_le_iff₀ hR ] at hk; linarith ⟩;
                  · exact div_pos ( norm_pos_iff.mpr hx.2 ) hR;
                  · exact div_pos ( norm_pos_iff.mpr hx.2 ) hR;
                aesop;
              · exact fun i => MeasurableSet.diff ( measurableSet_closedBall ) ( measurableSet_closedBall );
              · intro k l hkl; simp_all +decide [ mul_comm, Real.rpow_add, Real.rpow_sub ] ; ring_nf; norm_num [ hR.ne' ] ;
                cases lt_or_gt_of_ne hkl <;> norm_num [ Set.disjoint_left ];
                · intro a ha₁ ha₂ ha₃; nlinarith [ show ( 1 / 2 : ℝ ) ^ l ≤ ( 1 / 2 : ℝ ) ^ k / 2 by exact le_trans ( pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) ( show l ≥ k + 1 by linarith ) ) ( by ring_nf; norm_num ) ] ;
                · intro a ha₁ ha₂ ha₃; nlinarith [ show ( 1 / 2 : ℝ ) ^ k ≤ ( 1 / 2 : ℝ ) ^ l * ( 1 / 2 ) by rw [ ← pow_succ ] ; exact pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) ( by linarith ) ] ;
            -- We'll use the fact that the integral of $|f|$ over a bounded set is finite if $f$ is bounded.
            have h_bounded : ∀ k : ℕ, ∫⁻ (z : Fin 3 → ℝ) in Metric.closedBall 0 (2^(-k : ℝ) * R) \ Metric.closedBall 0 (2^(-k-1 : ℝ) * R), ENNReal.ofReal (‖z‖⁻¹) ≤ ENNReal.ofReal ((2^(-k-1 : ℝ) * R)⁻¹ * (MeasureTheory.volume (Metric.closedBall (0 : Fin 3 → ℝ) (2^(-k : ℝ) * R))).toReal) := by
              intro k
              have h_bounded : ∀ z : Fin 3 → ℝ, z ∈ Metric.closedBall 0 (2^(-k : ℝ) * R) \ Metric.closedBall 0 (2^(-k-1 : ℝ) * R) → ‖z‖⁻¹ ≤ (2^(-k-1 : ℝ) * R)⁻¹ := by
                simp +zetaDelta at *;
                intro z hz₁ hz₂; rw [ ← mul_inv ] ; gcongr ; norm_num [ Real.rpow_sub ] at * ; linarith;
              refine' le_trans ( MeasureTheory.lintegral_mono_ae _ ) _;
              use fun z => ENNReal.ofReal ( ( 2 ^ ( - ( k : ℝ ) - 1 ) * R ) ⁻¹ );
              · filter_upwards [ MeasureTheory.ae_restrict_mem <| measurableSet_closedBall.diff measurableSet_closedBall ] with z hz using ENNReal.ofReal_le_ofReal <| h_bounded z hz;
              · simp +zetaDelta at *;
                rw [ ENNReal.ofReal_mul ( by positivity ) ];
                rw [ ENNReal.ofReal_mul ( by positivity ), ENNReal.ofReal_mul ( by positivity ) ];
                gcongr;
                refine' le_trans ( MeasureTheory.measure_mono _ ) _;
                exact Metric.closedBall 0 ( ( 2 ^ k ) ⁻¹ * R );
                · grind;
                · rw [ ENNReal.ofReal_toReal ];
                  exact ne_of_lt ( isCompact_closedBall _ _ |> IsCompact.measure_lt_top );
            -- We'll use the fact that the volume of the closed ball is finite.
            have h_volume : ∀ k : ℕ, (MeasureTheory.volume (Metric.closedBall (0 : Fin 3 → ℝ) (2^(-k : ℝ) * R))).toReal = (2^(-k : ℝ) * R)^3 * (MeasureTheory.volume (Metric.closedBall (0 : Fin 3 → ℝ) 1)).toReal := by
              intro k; rw [ MeasureTheory.Measure.addHaar_closedBall ] ; norm_num ; ring;
              · positivity;
              · positivity;
            -- We'll use the fact that the series $\sum_{k=0}^{\infty} (2^{-k-1} R)^{-1} (2^{-k} R)^3$ converges.
            have h_series : Summable (fun k : ℕ => (2^(-k-1 : ℝ) * R)⁻¹ * (2^(-k : ℝ) * R)^3) := by
              norm_num [ Real.rpow_sub ] ; ring_nf ; norm_num [ hR.ne' ];
              norm_num [ pow_mul', mul_assoc, hR.ne' ];
              norm_num only [ ← mul_assoc, ← mul_pow ] ; ring_nf ; norm_num [ hR.ne' ];
              exact Summable.mul_right _ ( Summable.mul_left _ ( summable_geometric_of_lt_one ( by norm_num ) ( by norm_num ) ) );
            refine lt_of_le_of_lt h_integrable <| lt_of_le_of_lt ( ENNReal.tsum_le_tsum h_bounded ) ?_;
            rw [ ← ENNReal.ofReal_tsum_of_nonneg ] <;> norm_num [ h_volume ];
            · exact fun k => by positivity;
            · convert h_series.mul_right ( ( MeasureTheory.volume ( Metric.closedBall ( 0 : Fin 3 → ℝ ) 1 ) |> ENNReal.toReal ) ) using 2 ; norm_num [ Real.rpow_add, Real.rpow_sub ] ; ring;
              convert congr_arg ( · * R⁻¹ * 2 ^ ‹_› * 2 ) ( h_volume ‹_› ) using 1 <;> norm_num [ Real.rpow_neg, Real.rpow_mul ] ; ring;
              · norm_num [ mul_comm ];
              · -- Let's simplify the expression.
                field_simp
                ring;
                norm_num [ ← mul_pow ];
          refine' ⟨ _, _ ⟩;
          · exact Measurable.aestronglyMeasurable ( by exact Measurable.inv ( measurable_norm ) );
          · rw [ MeasureTheory.hasFiniteIntegral_iff_norm ] ; aesop;
        rwa [ MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_congr_set ];
        rw [ MeasureTheory.ae_eq_set ] ; norm_num;
        exact MeasureTheory.measure_mono_null ( fun x hx => by aesop ) ( MeasureTheory.measure_singleton 0 )