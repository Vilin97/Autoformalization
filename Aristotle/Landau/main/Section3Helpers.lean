import Aristotle.Landau.main.Defs
import Aristotle.Landau.main.Section2
import Aristotle.Landau.main.GaussianHelpers
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

/-- Flux factoring: f(w)∇f(v) - f(v)∇f(w) = f(v)f(w)(∇logf(v) - ∇logf(w)). -/
lemma analysis_fluxFactor
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) :
    ∀ v w, f w • vGrad f v - f v • vGrad f w =
    (f v * f w) • (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w) := by
  -- Proved by Aristotle (Harmonic)
  intro v w
  have h_log_grad : ∀ (v : (Fin 3) → ℝ),
      VML.vGrad (Real.log ∘ f) v =
      (1 / f v) • VML.vGrad f v := by
    intro v
    ext i
    by_cases H : DifferentiableAt ℝ f v <;> simp_all [VML.vGrad, fderiv_deriv]
    ring
    · erw [ fderiv_comp ] <;> norm_num [ H, ne_of_gt (hf_pos v) ]; ring
    · rw [ fderiv_zero_of_not_differentiableAt ]
      · rw [ fderiv_zero_of_not_differentiableAt H ] ; norm_num
      · exact fun h => H <| by
          simpa [ Real.exp_log (hf_pos _) ] using
            h.exp.congr_of_eventuallyEq
            (by filter_upwards [] using fun _ => by simp [Real.exp_log (hf_pos _)])
  simp only [h_log_grad, smul_sub]
  ext i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hfv := ne_of_gt (hf_pos v)
  have hfw := ne_of_gt (hf_pos w)
  field_simp

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
  intro v w; simp only [dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]; ring

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
    intro v w
    by_contra h_nonzero
    push_neg at h_nonzero
    obtain ⟨U, hU_open, hU_v, hU_nonzero⟩ :
        ∃ U : Set (Fin 3 → ℝ),
        IsOpen U ∧ v ∈ U ∧ ∀ u ∈ U, g u w ≠ 0 := by
      exact ⟨ { u | g u w ≠ 0 },
        isOpen_ne.preimage
          (show Continuous fun u => g u w from hcont.comp (continuous_id.prodMk continuous_const) ),
        h_nonzero, fun u hu => hu ⟩
    exact absurd h_zero_ae (ne_of_gt (lt_of_lt_of_le
      (by exact (hU_open.measure_pos
        (MeasureTheory.MeasureSpace.volume) ⟨ v, hU_v ⟩))
      (MeasureTheory.measure_mono
        (show U ⊆ { a : Fin 3 → ℝ | ¬∀ w : Fin 3 → ℝ, g a w = 0 }
          from fun u hu => fun h => hU_nonzero u hu <| h w))))
  · exact Filter.Eventually.of_forall fun v => MeasureTheory.integral_nonneg fun w => hnn v w
  · exact hint_outer

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
    convert h_poly_zero using 2
    ring
    simp +decide [ Fin.sum_univ_three ]
    ring
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
        · exact ⟨0, by rcases ht with rfl | rfl <;> simp⟩
        · obtain ⟨l, hl⟩ := hparallel (v + t • w) v (by simp_all)
          use l * t
          simp_all +decide [mul_comm, smul_smul]
      have h_lim : Filter.Tendsto
          (fun t : ℝ => (1 / t) • (g (v + t • w) - g v))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds ((fderiv ℝ g v) w)) := by
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
      exact Submodule.closed_of_finiteDimensional _
        |> fun h => h.mem_of_tendsto h_lim <|
          Filter.eventually_of_mem self_mem_nhdsWithin
            fun t ht => Submodule.smul_mem _ _ <|
            h_deriv_eq t
    have h_deriv_scalar : ∀ w : Fin 3 → ℝ, ∃ c : ℝ, (fderiv ℝ g v) w = c • w := by
      exact fun w => by simpa [eq_comm] using Submodule.mem_span_singleton.mp (h_deriv_eq w)
    choose c hc using h_deriv_scalar
    have h_c_const : ∀ i j : Fin 3, c (Pi.single i 1) = c (Pi.single j 1) := by
      intro i j
      have := hc (Pi.single i 1 + Pi.single j 1)
      simp_all +decide [funext_iff, Fin.forall_fin_succ]
      fin_cases i <;> fin_cases j <;> simp +decide at this ⊢ <;> linarith!
    use c (Pi.single 0 1)
    intro w
    rw [hc]
    ext i
    simp +decide [← h_c_const i 0]
    have h_c_const : ∀ w : Fin 3 → ℝ,
        (fderiv ℝ g v) w =
        ∑ i, w i • (fderiv ℝ g v) (Pi.single i 1) := by
      intro w; exact (by
      rw [show w = ∑ i, Pi.single i (w i) by ext i; simp +decide]
      simp +decide [Finset.sum_apply, Pi.single_apply]
      ring
      exact Finset.sum_congr rfl fun i _ => by
        rw [← map_smul]; congr; ext j
        fin_cases i <;> fin_cases j <;>
          simp +decide [Pi.single_apply])
    specialize h_c_const w
    rw [hc] at h_c_const
    simp +decide [Fin.sum_univ_three] at h_c_const
    replace h_c_const := congr_fun h_c_const i; fin_cases i <;> simp +decide [hc] at h_c_const ⊢
    · exact Classical.or_iff_not_imp_right.2 fun h => mul_left_cancel₀ h <| by linarith
    · exact Classical.or_iff_not_imp_right.2 fun h => mul_left_cancel₀ h <| by linarith
    · exact Classical.or_iff_not_imp_right.2 fun h => mul_left_cancel₀ h <| by linarith
  -- Step 2: c is constant (via symmetry of second derivatives)
  have h_const_deriv : ∃ c₀ : ℝ, ∀ v : Fin 3 → ℝ, ∀ w : Fin 3 → ℝ, (fderiv ℝ g v) w = c₀ • w := by
    choose c hc using h_deriv
    have h_const_c : ∀ v w : Fin 3 → ℝ, c v = c w := by
      have hc_partial : ∀ v : Fin 3 → ℝ, ∀ i j : Fin 3,
          (fderiv ℝ g v) (Pi.single j 1) i =
          c v * (if i = j then 1 else 0) := by
        intro v i j; simp only [hc, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      have h_diff_fderiv : ContDiff ℝ 1 (fderiv ℝ g) := hg_smooth.fderiv_right le_rfl
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
        · exact h_diff_fderiv.differentiable le_rfl v
        · exact differentiableAt_const _
        · exact h_diff_fderiv.differentiable le_rfl v
        · exact differentiableAt_const _
      have h_second_deriv : ∀ v : Fin 3 → ℝ,
          ∀ i j k : Fin 3,
          (fderiv ℝ (fun v =>
            (fderiv ℝ g v) (Pi.single j 1)) v)
            (Pi.single k 1) i =
          (fderiv ℝ c v) (Pi.single k 1) *
          (if i = j then 1 else 0) := by
        intro v i j k
        have hDiff_comp_j : ∀ i', DifferentiableAt ℝ
            (fun v => (fderiv ℝ g v) (Pi.single j 1) i') v :=
          fun i' => DifferentiableAt.comp v
            (differentiableAt_pi.1
              ((h_diff_fderiv.clm_apply contDiff_const).contDiffAt.differentiableAt le_rfl) i')
            differentiableAt_id
        have h_pi_comp : (fderiv ℝ (fun v => (fderiv ℝ g v) (Pi.single j 1)) v)
            (Pi.single k 1) i =
            (fderiv ℝ (fun v => (fderiv ℝ g v) (Pi.single j 1) i) v) (Pi.single k 1) := by
          rw [fderiv_pi hDiff_comp_j]; simp only [ContinuousLinearMap.pi_apply]
        rw [h_pi_comp]
        by_cases hij : i = j
        · subst hij
          simp only [ite_true, mul_one]
          have heq : (fun v => (fderiv ℝ g v) (Pi.single i 1) i) = c := by
            ext v; rw [hc_partial]; simp
          rw [heq]
        · simp only [hij, ite_false, mul_zero]
          have heq : (fun v => (fderiv ℝ g v) (Pi.single j 1) i) = fun _ => 0 := by
            ext v; rw [hc_partial]; simp [hij]
          rw [heq]; simp [fderiv_const]
      have h_zero_deriv : ∀ v : Fin 3 → ℝ, ∀ k : Fin 3, (fderiv ℝ c v) (Pi.single k 1) = 0 := by
        intro v k
        obtain ⟨i, hi⟩ : ∃ i : Fin 3, i ≠ k := by fin_cases k <;> trivial
        specialize h_symm_second_deriv v i i k; simp_all
      have h_const_c : ∀ v : Fin 3 → ℝ, (fderiv ℝ c v) = 0 := by
        intro v; ext w
        have : (fderiv ℝ c v) w =
            ∑ k : Fin 3, w k • (fderiv ℝ c v) (Pi.single k 1) := by
          conv_lhs => rw [show w = ∑ k, Pi.single k (w k) by ext i; simp +decide]
          simp only [map_sum, map_smul, smul_eq_mul]
          exact Finset.sum_congr rfl fun i _ => by
            have : Pi.single i (w i) = w i • (Pi.single i (1 : ℝ) : Fin 3 → ℝ) := by
              ext j; simp [Pi.single_apply, smul_eq_mul]
            rw [this, map_smul, smul_eq_mul]
        simp [this, h_zero_deriv]
      have h_diff_c : Differentiable ℝ c := by
        have : ContDiff ℝ 1 (fun v => (fderiv ℝ g v) (Pi.single 0 1) 0) :=
          (contDiff_apply ℝ ℝ 0).comp (h_diff_fderiv.clm_apply contDiff_const)
        convert this.differentiable le_rfl using 1
        funext v; simp [hc, smul_eq_mul]
      intro v w; exact is_const_of_fderiv_eq_zero h_diff_c h_const_c v w
    use c 0
    intro v w
    rw [hc, h_const_c v 0]
  -- Step 3: FTC to get g(v) = g(0) + c₀ v
  obtain ⟨c₀, hc₀⟩ := h_const_deriv
  have h_ftc : ∀ v : Fin 3 → ℝ, g v = g 0 + ∫ t in (0 : ℝ)..1, (fderiv ℝ g (t • v)) v := by
    intro v
    have h_integral_eq : ∀ a b : ℝ,
        ∫ t in a..b, (fderiv ℝ g (t • v)) v =
        g (b • v) - g (a • v) := by
      intro a b
      rw [intervalIntegral.integral_deriv_eq_sub']
      · ext t
        erw [deriv]
        erw [fderiv_comp] <;> norm_num [hg_smooth.contDiffAt.differentiableAt (by norm_num), hc₀]
        rw [deriv_pi] <;> norm_num [Fin.forall_fin_succ]
      · exact fun x hx => DifferentiableAt.comp x
          (hg_smooth.contDiffAt.differentiableAt (by norm_num))
          (differentiableAt_id.smul_const _)
      · exact Continuous.continuousOn (by continuity)
    simp +decide [h_integral_eq]
  use g 0, c₀ / 2
  intro v
  rw [h_ftc v]
  norm_num [hc₀]
  ring

/-- Gap 7: Antiderivative of an affine gradient.
    If ∇h(v) = b + 2c₀ v, then h(v) = h(0) + b · v + c₀|v|².
    Reference: Proof of Lemma 8 (lem:log_f_quadratic). -/
lemma affine_gradient_antiderivative (h : (Fin 3 → ℝ) → ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ)
    (hh_smooth : ContDiff ℝ 3 h)
    (hgrad : ∀ v, vGrad h v = b + (2 * c₀) • v) :
    ∀ v, h v = h 0 + dotProduct b v + c₀ * normSq v := by
  -- Proved by Aristotle (Harmonic). Full proof in gap07_aristotle.lean.
  have h_deriv : ∀ v : Fin 3 → ℝ, ∀ t : ℝ,
      deriv (fun t => h (t • v)) t =
      (b + 2 * c₀ • (t • v)) ⬝ᵥ v := by
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
      set L := fderiv ℝ h (t • v)
      have hv_decomp : v = ∑ i, v i • (Pi.single i (1 : ℝ) : Fin 3 → ℝ) := by
        ext i; simp [Pi.single_apply, Finset.sum_apply, smul_eq_mul]
      conv_rhs => rw [hv_decomp]
      simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
    simp_all +decide [two_mul]
    ring
  intros v
  have : ∫ t in (0 : ℝ)..1, deriv (fun t => h (t • v)) t = h v - h 0 := by
    have hint : IntervalIntegrable (deriv (fun t => h (t • v))) MeasureTheory.volume 0 1 :=
      Continuous.intervalIntegrable
        (by rw [show deriv (fun t => h (t • v)) = fun t => (b + 2 * c₀ • t • v) ⬝ᵥ v
              from funext fun t => h_deriv v t]
            continuity) 0 1
    have := intervalIntegral.integral_deriv_eq_sub
      (f := fun t => h (t • v))
      (fun t _ => DifferentiableAt.comp t
        (hh_smooth.contDiffAt.differentiableAt (by norm_num))
        (differentiableAt_id.smul_const _))
      hint
    simp at this; linarith
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
    intro v
    ext i
    rw [fderiv_exp]
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
    · apply_rules [DifferentiableAt.add,
        DifferentiableAt.mul, differentiableAt_id,
        differentiableAt_const]
      all_goals apply_rules [differentiableAt_pi.1, differentiableAt_id]
  intros v w
  simp [h_grad]
  convert congr_arg
    (fun x : Fin 3 → ℝ =>
      f w • f v • c₀ • (2 : ℝ) • x)
    (landauMatrix_mulVec_self Ψ (v - w)) using 1
  ext
  norm_num
  ring!
  · simp +decide [mul_assoc, mul_comm, mul_left_comm,
      Finset.mul_sum _ _ _, Matrix.mulVec, dotProduct]
    ring!
  · norm_num [Algebra.smul_def]

/-- Maxwellians are in the nullspace of the Landau operator: Q(f,f) = 0.
    The flux A(v-w)[f(w)∇f(v) - f(v)∇f(w)] vanishes pointwise (because
    ∇log f is affine, so the score difference is proportional to v-w,
    which is annihilated by A(v-w)), making the integral and its divergence zero. -/
lemma IsMaxwellian.landauOperator_eq_zero (Ψ : ℝ → ℝ)
    (hM : IsMaxwellian f) (v : Fin 3 → ℝ) :
    LandauOperator Ψ f v = 0 := by
  obtain ⟨a₀, b, c₀, _, hf⟩ := hM
  have hflux := maxwellian_landau_flux_zero Ψ f a₀ b c₀ hf
  unfold LandauOperator
  simp only [hflux, MeasureTheory.integral_zero, Pi.zero_apply]
  simp [vDiv, fderiv_const]

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

end VML
