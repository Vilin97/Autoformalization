/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 97da955d-87fc-4609-abbc-45fbd4eb9b8b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma landau_ibp_df_g
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (hLogBound : ∃ (Cl : ℝ) (Kl : ℕ), ∀ v : Fin 3 → ℝ,
      |(Real.log ∘ f) v| ≤ Cl * (1 + ‖v‖) ^ Kl)
    (i : Fin 3) :
    Integrable (fun v =>
      fderiv ℝ (fun v' => (∫ w, mulVec (landauMatrix' (v' - w))
        (f w • vGrad' f v' - f v' • vGrad' f w)) i) v (Pi.single i 1) *
      (Real.log ∘ f) v)
-/

/-
Integrability of fderiv(flux_i) × log(f) for the Coulomb kernel.

The goal: show that v ↦ (∂/∂v_i Φ_i)(v) * log(f(v)) is integrable,
where Φ_i(v) = (∫ w, A(v-w) *ᵥ [f(w)∇f(v) - f(v)∇f(w)])_i
is the i-th component of the Landau collision flux.

Key idea: The flux derivative satisfies a Schwartz-type bound (admitted),
and log(f) grows at most polynomially. The product is then dominated
by a Schwartz function and hence integrable.

Building blocks: flux integrability, differentiability, and decay bounds admitted.
-/
import Mathlib


-- Harmonic `generalize_proofs` tactic

set_option linter.all false

set_option maxHeartbeats 800000

open MeasureTheory Real Matrix Finset BigOperators

noncomputable section

def vGrad' (f : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => fderiv ℝ f v (Pi.single i 1)

def normSq' (z : Fin 3 → ℝ) : ℝ := dotProduct z z

def eucNorm' (z : Fin 3 → ℝ) : ℝ := Real.sqrt (normSq' z)

def innerLandauMatrix' (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  normSq' z • (1 : Matrix (Fin 3) (Fin 3) ℝ) - vecMulVec z z

def coulombKernel' (r : ℝ) : ℝ := if r ≤ 0 then 1 else r ^ (-3 : ℝ)

def landauMatrix' (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  coulombKernel' (eucNorm' z) • innerLandauMatrix' z

/-- The flux integrand is integrable (proved separately). -/
lemma flux_integrable'
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (v : Fin 3 → ℝ) :
    Integrable (fun w =>
      mulVec (landauMatrix' (v - w))
        (f w • vGrad' f v - f v • vGrad' f w)) := by admit

/-- The flux component is differentiable (proved separately). -/
lemma flux_differentiable'
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i : Fin 3) :
    Differentiable ℝ (fun v =>
      (∫ w, mulVec (landauMatrix' (v - w))
        (f w • vGrad' f v - f v • vGrad' f w)) i) := by admit

/-- Schwartz function times polynomial power is integrable (proved separately). -/
lemma integrable_one_add_norm_pow_mul'
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_schwartz : ∀ (N : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      |f v| * (1 + ‖v‖) ^ N ≤ C)
    (M : ℕ) :
    Integrable (fun v => (1 + ‖v‖) ^ M * |f v|) := by admit

/-- The flux derivative has Schwartz-type decay (proved separately).
    |fderiv(flux_i)(v)(e_i)| ≤ C(1+‖v‖)^M * f(v) for some C, M. -/
lemma flux_deriv_schwartz_bound'
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i : Fin 3) :
    ∃ (C₁ : ℝ) (M₁ : ℕ), ∀ v : Fin 3 → ℝ,
      ‖fderiv ℝ (fun v' =>
        ∫ w, (mulVec (landauMatrix' (v' - w))
          (f w • vGrad' f v' - f v' • vGrad' f w)) i) v‖ ≤
      C₁ * (1 + ‖v‖) ^ M₁ * f v := by admit

/- The derivative of flux × log(f) is integrable for Coulomb kernel. -/
noncomputable section AristotleLemmas

/-
If g is bounded by polynomial * f, and h is bounded by polynomial, and f is Schwartz, then g * h is integrable.
-/
lemma integrable_of_decay_bound'
    (f g h : (Fin 3 → ℝ) → ℝ)
    (hf_schwartz : ∀ (N : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      |f v| * (1 + ‖v‖) ^ N ≤ C)
    (hg_bound : ∃ (Cg : ℝ) (Mg : ℕ), ∀ v, |g v| ≤ Cg * (1 + ‖v‖) ^ Mg * |f v|)
    (hh_bound : ∃ (Ch : ℝ) (Mh : ℕ), ∀ v, |h v| ≤ Ch * (1 + ‖v‖) ^ Mh)
    (hg_meas : AEStronglyMeasurable g volume)
    (hh_meas : AEStronglyMeasurable h volume) :
    Integrable (fun v => g v * h v) := by
      -- Using the given bounds for `g` and `h`, we can express `|g(v) * h(v)|` as `|Cg * (1 + ‖v‖)^Mg * |f(v)| * Ch * (1 + ‖v‖)^Mh|`.
      obtain ⟨Cg, Mg, hg⟩ := hg_bound
      obtain ⟨Ch, Mh, hh⟩ := hh_bound
      have h_bound : ∀ v, |g v * h v| ≤ Cg * Ch * (1 + ‖v‖) ^ (Mg + Mh) * |f v| := by
        intro v; rw [ abs_mul ] ; convert mul_le_mul ( hg v ) ( hh v ) ( by positivity ) ( by exact le_trans ( by positivity ) ( hg v ) ) using 1 ; ring;
      -- The function v ↦ Cg * Ch * (1 + ‖v‖)^(Mg + Mh) * |f v| is integrable by `integrable_one_add_norm_pow_mul'` (scaled by Cg * Ch).
      have h_integrable : MeasureTheory.Integrable (fun v => Cg * Ch * (1 + ‖v‖) ^ (Mg + Mh) * |f v|) MeasureTheory.MeasureSpace.volume := by
        convert MeasureTheory.Integrable.const_mul ( integrable_one_add_norm_pow_mul' f _ ( Mg + Mh ) ) ( Cg * Ch ) using 1 ; ring;
        exact hf_schwartz;
      refine' h_integrable.mono' _ _;
      · exact hg_meas.mul hh_meas;
      · exact Filter.Eventually.of_forall h_bound

/-
The derivative of the flux component is measurable.
-/
lemma flux_deriv_measurable'
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i : Fin 3) :
    Measurable (fun v =>
      fderiv ℝ (fun v' => (∫ w, mulVec (landauMatrix' (v' - w))
        (f w • vGrad' f v' - f v' • vGrad' f w)) i) v (Pi.single i 1)) := by
          apply_rules [ measurable_fderiv_apply_const ]

/-
The component of the flux derivative is bounded by a polynomial times f.
-/
lemma flux_deriv_component_bound
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i : Fin 3) :
    ∃ (C₁ : ℝ) (M₁ : ℕ), ∀ v : Fin 3 → ℝ,
      |fderiv ℝ (fun v' =>
        ∫ w, (mulVec (landauMatrix' (v' - w))
          (f w • vGrad' f v' - f v' • vGrad' f w)) i) v (Pi.single i 1)| ≤
      C₁ * (1 + ‖v‖) ^ M₁ * |f v| := by
        obtain ⟨ C₁, M₁, hC₁ ⟩ := flux_deriv_schwartz_bound' f hf_pos hf_smooth hf_schwartz i;
        refine' ⟨ C₁, M₁, fun v => le_trans ( _ ) ( le_trans ( hC₁ v ) _ ) ⟩ <;> norm_num [ Pi.norm_def ];
        · convert ( ContinuousLinearMap.le_opNorm ( fderiv ℝ ( fun v' => ∫ w, ( landauMatrix' ( v' - w ) *ᵥ ( f w • vGrad' f v' - f v' • vGrad' f w ) ) i ) v ) ( Pi.single i 1 ) ) using 1 ; norm_num [ Pi.norm_def ];
          fin_cases i <;> simp +decide [ Fin.univ_succ ];
        · rw [ abs_of_pos ( hf_pos v ) ]

end AristotleLemmas

lemma landau_ibp_df_g
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_schwartz : ∀ (N k : ℕ), ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (hLogBound : ∃ (Cl : ℝ) (Kl : ℕ), ∀ v : Fin 3 → ℝ,
      |(Real.log ∘ f) v| ≤ Cl * (1 + ‖v‖) ^ Kl)
    (i : Fin 3) :
    Integrable (fun v =>
      fderiv ℝ (fun v' => (∫ w, mulVec (landauMatrix' (v' - w))
        (f w • vGrad' f v' - f v' • vGrad' f w)) i) v (Pi.single i 1) *
      (Real.log ∘ f) v) := by
        -- Apply the integrable_of_decay_bound' lemma.
        have h_integrable : Integrable (fun v => (fderiv ℝ (fun v' => (∫ w, mulVec (landauMatrix' (v' - w)) (f w • vGrad' f v' - f v' • vGrad' f w)) i) v (Pi.single i 1)) * (Real.log ∘ f) v) := by
          have h_bound : ∃ C₁ M₁, ∀ v, |fderiv ℝ (fun v' => (∫ w, mulVec (landauMatrix' (v' - w)) (f w • vGrad' f v' - f v' • vGrad' f w)) i) v (Pi.single i 1)| ≤ C₁ * (1 + ‖v‖) ^ M₁ * |f v| := by
            convert flux_deriv_component_bound f hf_pos hf_smooth hf_schwartz i using 1;
            rw [ show ( fun v' => ∫ w, ( landauMatrix' ( v' - w ) *ᵥ ( f w • vGrad' f v' - f v' • vGrad' f w ) ) i ) = ( fun v' => ( ∫ w, landauMatrix' ( v' - w ) *ᵥ ( f w • vGrad' f v' - f v' • vGrad' f w ) ) i ) from funext fun v' => ?_ ];
            -- Apply the fact that the integral of a vector-valued function is the vector of integrals.
            have h_integral_pi : ∀ {g : (Fin 3 → ℝ) → Fin 3 → ℝ}, MeasureTheory.Integrable g MeasureTheory.volume → ∫ w, g w = fun i => ∫ w, g w i := by
              intro g hg; ext i; exact (by
              have h_integral_pi : ∀ {g : (Fin 3 → ℝ) → Fin 3 → ℝ}, MeasureTheory.Integrable g MeasureTheory.volume → ∫ w, g w = ∑ i, (∫ w, g w i) • (Pi.single i 1 : Fin 3 → ℝ) := by
                intro g hg; exact (by
                have h_integral_pi : ∀ {g : (Fin 3 → ℝ) → Fin 3 → ℝ}, MeasureTheory.Integrable g MeasureTheory.volume → ∫ w, g w = ∑ i, (∫ w, g w i • (Pi.single i 1 : Fin 3 → ℝ)) := by
                  intro g hg; rw [ ← MeasureTheory.integral_finset_sum ] ; congr; ext w; simp +decide [ Fin.sum_univ_three ] ;
                  · rename_i i; fin_cases i <;> simp +decide [ Pi.single_apply ] ;
                  · intro i _; exact (by
                    refine' MeasureTheory.Integrable.smul_const _ _;
                    refine' MeasureTheory.Integrable.mono' _ _ _;
                    exact fun w => ‖g w‖;
                    · exact hg.norm;
                    · exact ( measurable_pi_apply i |> Measurable.aestronglyMeasurable ) |> fun h => h.comp_aemeasurable hg.1.aemeasurable;
                    · exact Filter.Eventually.of_forall fun x => norm_le_pi_norm ( g x ) i);
                convert h_integral_pi hg using 2;
                rw [ integral_smul_const ]);
              rw [ h_integral_pi hg, Finset.sum_apply, Finset.sum_eq_single i ] <;> aesop);
            rw [ h_integral_pi ];
            convert flux_integrable' f hf_pos hf_smooth hf_schwartz v' using 1
          convert integrable_of_decay_bound' f _ _ _ _ _ _ _ using 1;
          · intro N; specialize hf_schwartz N 0; aesop;
          · exact h_bound;
          · exact hLogBound;
          · convert flux_deriv_measurable' f hf_pos hf_smooth hf_schwartz i |> Measurable.aestronglyMeasurable using 1;
          · exact Continuous.aestronglyMeasurable ( by exact Continuous.log ( hf_smooth.continuous ) fun x => ne_of_gt ( hf_pos x ) );
        convert h_integrable using 1