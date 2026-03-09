/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 06cbe646-74a1-449a-a65b-6fbb2b3ec152

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma dotprod_schwartz_log_integrable
    (g : (Fin 3 → ℝ) → Fin 3 → ℝ) (h : (Fin 3 → ℝ) → ℝ)
    (hg_decay : ∀ (N : ℕ) (i : Fin 3), ∃ C > 0, ∀ (v : Fin 3 → ℝ),
      |g v i| * (1 + ‖v‖) ^ N ≤ C)
    (hh_bound : ∃ (C_h : ℝ) (K_h : ℕ), ∀ (v : Fin 3 → ℝ),
      |h v| ≤ C_h * (1 + ‖v‖) ^ K_h)
    (hg_meas : ∀ i, AEStronglyMeasurable (fun v => g v i) volume)
    (hh_meas : AEStronglyMeasurable h volume) :
    Integrable (fun v => dotProduct v (g v) * h v)
-/

import Mathlib


set_option linter.all false

set_option maxHeartbeats 800000

open MeasureTheory Real

noncomputable section

-- Harmonic `generalize_proofs` tactic

/-- If g : ℝ³ → ℝ³ has Schwartz-type component decay
    (|g(v)_i| * (1+‖v‖)^N ≤ C for all N, i)
    and h : ℝ³ → ℝ has polynomial growth
    (|h(v)| ≤ C_log * (1+‖v‖)^K_log),
    then v ↦ v · g(v) * h(v) is integrable on ℝ³.

    Proof idea: |v · g(v) * h(v)| ≤ Σᵢ ‖v‖ * |g(v)_i| * |h(v)|
    ≤ 3 * ‖v‖ * C/(1+‖v‖)^(K_log+5) * C_log*(1+‖v‖)^K_log
    = C' / (1+‖v‖)^4, integrable in ℝ³. -/
lemma dotprod_schwartz_log_integrable
    (g : (Fin 3 → ℝ) → Fin 3 → ℝ) (h : (Fin 3 → ℝ) → ℝ)
    (hg_decay : ∀ (N : ℕ) (i : Fin 3), ∃ C > 0, ∀ (v : Fin 3 → ℝ),
      |g v i| * (1 + ‖v‖) ^ N ≤ C)
    (hh_bound : ∃ (C_h : ℝ) (K_h : ℕ), ∀ (v : Fin 3 → ℝ),
      |h v| ≤ C_h * (1 + ‖v‖) ^ K_h)
    (hg_meas : ∀ i, AEStronglyMeasurable (fun v => g v i) volume)
    (hh_meas : AEStronglyMeasurable h volume) :
    Integrable (fun v => dotProduct v (g v) * h v) := by
      revert @hh_bound;
      intro hh_bound
      obtain ⟨C_h, K_h, hh_bound⟩ := hh_bound
      have h_integrable : ∀ N : ℕ, ∃ C > 0, ∀ v : Fin 3 → ℝ, abs (v ⬝ᵥ g v * h v) ≤ C / (1 + ‖v‖)^(N) := by
        intro N
        obtain ⟨C_g, hC_g_pos, hC_g⟩ : ∃ C_g > 0, ∀ v : Fin 3 → ℝ, ∀ i : Fin 3, abs (g v i) ≤ C_g / (1 + ‖v‖)^(N + K_h + 5) := by
          choose! C hC using hg_decay ( N + K_h + 5 );
          exact ⟨ ∑ i, C i, Finset.sum_pos ( fun i _ => hC i |>.1 ) ( Finset.univ_nonempty ), fun v i => by rw [ le_div_iff₀ ( by positivity ) ] ; exact le_trans ( hC i |>.2 v ) ( Finset.single_le_sum ( fun i _ => le_of_lt ( hC i |>.1 ) ) ( Finset.mem_univ i ) ) ⟩;
        -- Using the decay of $g$ and the bound on $h$, we get:
        have h_bound : ∀ v : Fin 3 → ℝ, abs (v ⬝ᵥ g v * h v) ≤ 3 * C_g * C_h * ‖v‖ / (1 + ‖v‖)^(N + 5) := by
          -- Applying the bounds from hC_g and hh_bound, we get:
          have h_bound : ∀ v : Fin 3 → ℝ, abs (v ⬝ᵥ g v) ≤ 3 * C_g * ‖v‖ / (1 + ‖v‖)^(N + K_h + 5) := by
            intro v
            have h_bound : abs (v ⬝ᵥ g v) ≤ ∑ i, abs (v i) * abs (g v i) := by
              simpa only [ ← abs_mul, dotProduct ] using Finset.abs_sum_le_sum_abs _ _;
            refine le_trans h_bound ?_;
            refine' le_trans ( Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ( hC_g v i ) ( abs_nonneg _ ) ) _ ; norm_num [ Fin.sum_univ_three ] ; ring_nf ; norm_num [ hC_g_pos ] ; (
            -- Since $|v_i| \leq \|v\|$ for all $i$, we can replace $|v_i|$ with $\|v\|$ in the inequality.
            have h_abs_le_norm : ∀ i : Fin 3, abs (v i) ≤ ‖v‖ := by
              exact fun i => norm_le_pi_norm v i |> le_trans ( by norm_num ) ;
            nlinarith [ h_abs_le_norm 0, h_abs_le_norm 1, h_abs_le_norm 2, show 0 ≤ C_g * ( ‖v‖ * ( 1 + ‖v‖ ) ^ N * ( 1 + ‖v‖ ) ^ K_h * 5 + ‖v‖ ^ 2 * ( 1 + ‖v‖ ) ^ N * ( 1 + ‖v‖ ) ^ K_h * 10 + ‖v‖ ^ 3 * ( 1 + ‖v‖ ) ^ N * ( 1 + ‖v‖ ) ^ K_h * 10 + ‖v‖ ^ 4 * ( 1 + ‖v‖ ) ^ N * ( 1 + ‖v‖ ) ^ K_h * 5 + ‖v‖ ^ 5 * ( 1 + ‖v‖ ) ^ N * ( 1 + ‖v‖ ) ^ K_h + ( 1 + ‖v‖ ) ^ N * ( 1 + ‖v‖ ) ^ K_h ) ⁻¹ by positivity ] ;);
          intro v; rw [ abs_mul ] ; convert mul_le_mul ( h_bound v ) ( hh_bound v ) ( by positivity ) ( by positivity ) using 1 ; ring;
          field_simp;
        refine' ⟨ 3 * C_g * C_h + 1, _, _ ⟩ <;> try positivity;
        · exact add_pos_of_nonneg_of_pos ( mul_nonneg ( mul_nonneg zero_le_three hC_g_pos.le ) ( show 0 ≤ C_h by exact le_trans ( abs_nonneg _ ) ( hh_bound 0 ) |> le_trans <| by norm_num ) ) zero_lt_one;
        · intro v
          specialize h_bound v
          have h_div : ‖v‖ / (1 + ‖v‖)^(N + 5) ≤ 1 / (1 + ‖v‖)^N := by
            rw [ div_le_div_iff₀ ] <;> first | positivity | ring_nf ; norm_cast ; norm_num;
            nlinarith [ show 0 ≤ ‖v‖ * ( 1 + ‖v‖ ) ^ N by positivity, show 0 ≤ ‖v‖ ^ 2 * ( 1 + ‖v‖ ) ^ N by positivity, show 0 ≤ ‖v‖ ^ 3 * ( 1 + ‖v‖ ) ^ N by positivity, show 0 ≤ ‖v‖ ^ 4 * ( 1 + ‖v‖ ) ^ N by positivity, show 0 ≤ ‖v‖ ^ 5 * ( 1 + ‖v‖ ) ^ N by positivity, show 0 ≤ ( 1 + ‖v‖ ) ^ N by positivity ]
          have h_final : 3 * C_g * C_h * ‖v‖ / (1 + ‖v‖)^(N + 5) ≤ (3 * C_g * C_h + 1) / (1 + ‖v‖)^N := by
            convert mul_le_mul_of_nonneg_left h_div ( show 0 ≤ 3 * C_g * C_h by exact mul_nonneg ( mul_nonneg zero_le_three hC_g_pos.le ) ( show 0 ≤ C_h by exact le_trans ( abs_nonneg _ ) ( hh_bound 0 ) |> le_trans <| by norm_num ) ) |> le_trans <| ?_ using 1 <;> ring_nf ; norm_num [ Nat.succ_eq_add_one ] at *;
            positivity
          exact le_trans h_bound h_final;
      obtain ⟨ C, hC_pos, hC ⟩ := h_integrable 4;
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun v => C / ( 1 + ‖v‖ ) ^ 4;
      · have h_integrable : MeasureTheory.IntegrableOn (fun v : Fin 3 → ℝ => (1 + ‖v‖) ^ (-4 : ℝ)) (Set.univ : Set (Fin 3 → ℝ)) := by
          have : ∀ v : Fin 3 → ℝ, (1 + ‖v‖) ^ (-4 : ℝ) ≤ (1 + ‖v‖ ^ 2) ^ (-2 : ℝ) := by
            intro v; rw [ Real.rpow_neg ( by positivity ), Real.rpow_neg ( by positivity ) ] ; norm_cast ; norm_num ; ring_nf ; (
            exact inv_anti₀ ( by positivity ) ( by nlinarith [ norm_nonneg v ] ));
          have h_p_integral : MeasureTheory.IntegrableOn (fun v : Fin 3 → ℝ => (1 + ‖v‖ ^ 2) ^ (-2 : ℝ)) (Set.univ : Set (Fin 3 → ℝ)) := by
            have := @integrable_rpow_neg_one_add_norm_sq;
            specialize @this ( Fin 3 → ℝ ) _ _ _ _ _ ( MeasureTheory.MeasureSpace.volume ) _ 4 ; norm_num at this;
            norm_cast ; aesop;
          refine' h_p_integral.mono' _ _;
          · exact Measurable.aestronglyMeasurable ( by exact Measurable.pow_const ( by exact measurable_const.add ( measurable_norm ) ) _ );
          · filter_upwards [ ] using fun v => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact this v;
        norm_cast at * ; simpa using h_integrable.const_mul C;
      · refine' MeasureTheory.AEStronglyMeasurable.mul _ hh_meas;
        simp_all +decide [ dotProduct, Fin.sum_univ_three ];
        exact MeasureTheory.AEStronglyMeasurable.add ( MeasureTheory.AEStronglyMeasurable.add ( MeasureTheory.AEStronglyMeasurable.mul ( measurable_pi_apply 0 |> Measurable.aestronglyMeasurable ) ( hg_meas 0 ) ) ( MeasureTheory.AEStronglyMeasurable.mul ( measurable_pi_apply 1 |> Measurable.aestronglyMeasurable ) ( hg_meas 1 ) ) ) ( MeasureTheory.AEStronglyMeasurable.mul ( measurable_pi_apply 2 |> Measurable.aestronglyMeasurable ) ( hg_meas 2 ) );
      · exact Filter.Eventually.of_forall hC