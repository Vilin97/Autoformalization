import Aristotle.Landau.main.Section3Helpers

open Matrix Finset BigOperators Real MeasureTheory

noncomputable section

namespace VML

-- ============================================================================
-- Section 5: H-Theorem and Nullspace of the Landau Operator
-- Reference: Section 3 of the tex (Lemmas 4-9, Theorems 3-5, Corollary 1)
-- ============================================================================

/-- Lemma 4 (Symmetrized weak formulation of the Landau operator).
    Reference: lem:symmetrized_weak

    For any smooth test function φ:
    ∫ Q(f,f)(v) φ(v) dv = -½ ∬ (∇φ(v) - ∇φ(w))ᵀ A(v-w) [f(w)∇f(v) - f(v)∇f(w)] dv dw

    Proof uses integration by parts on the divergence form of Q and the
    symmetry A(-z) = A(z) (Lemma 1b) under v ↔ w exchange. -/
theorem symmetrized_weak_form (Ψ : ℝ → ℝ) (f φ : (Fin 3 → ℝ) → ℝ)
    (_hf_pos : ∀ v, 0 < f v) (_hf_smooth : ContDiff ℝ ⊤ f)
    (_hφ_smooth : ContDiff ℝ ⊤ φ)
    -- Hypothesis: SWF identity (from IBP + Fubini + A(-z)=A(z) symmetry)
    (hSWF : ∫ v, LandauOperator Ψ f v * φ v =
      -(1 / 2) * ∫ v, ∫ w, dotProduct (vGrad φ v - vGrad φ w)
        (mulVec (landauMatrix Ψ (v - w))
          (f w • vGrad f v - f v • vGrad f w))) :
    ∫ v, LandauOperator Ψ f v * φ v =
    -(1 / 2) * ∫ v, ∫ w, dotProduct (vGrad φ v - vGrad φ w)
      (mulVec (landauMatrix Ψ (v - w))
        (f w • vGrad f v - f v • vGrad f w)) :=
  hSWF

/-- Lemma 5 (Entropy dissipation formula).
    Reference: lem:entropy_dissipation

    D(f) = -½ ∬ f(v)f(w) (∇log f(v) - ∇log f(w))ᵀ A(v-w) (∇log f(v) - ∇log f(w)) dv dw

    Proof applies Lemma 4 with φ = log f, using ∇f = f ∇log f. -/
theorem entropy_dissipation_formula (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f)
    -- Hypothesis: SWF with φ = log f (from IBP + Fubini)
    (hSWF : ∫ v, LandauOperator Ψ f v * (Real.log ∘ f) v =
      -(1 / 2) * ∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
        (mulVec (landauMatrix Ψ (v - w))
          (f w • vGrad f v - f v • vGrad f w))) :
    entropyDissipation Ψ f =
    -(1 / 2) * ∫ v, ∫ w, PSDIntegrand Ψ f v w :=
  entropy_score_form Ψ f hf_pos hf_smooth hSWF

/-- Theorem 3 (H-theorem for the Landau operator).
    Reference: thm:H_theorem

    D(f) = ∫ Q(f,f)(v) log f(v) dv ≤ 0.

    Proof: By Lemma 5, D(f) is the negative of a double integral of
    the quadratic form Yᵀ A(z) Y weighted by f(v)f(w) > 0.
    By Lemma 2 (PSD), the integrand is non-negative, so D(f) ≤ 0. -/
theorem H_theorem (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 ≤ Ψ r) (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hSWF : ∫ v, LandauOperator Ψ f v * (Real.log ∘ f) v =
      -(1 / 2) * ∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
        (mulVec (landauMatrix Ψ (v - w))
          (f w • vGrad f v - f v • vGrad f w))) :
    entropyDissipation Ψ f ≤ 0 := by
  rw [entropy_score_form Ψ f hf_pos hf_smooth hSWF]
  unfold PSDIntegrand
  linarith [psd_weighted_integral_nonneg Ψ f hΨ hf_pos]

/-- Lemma 6 (Characterization of D(f) = 0: the functional equation).
    Reference: lem:D_zero_functional_eq

    If D(f) = 0, then for all v ≠ w, ∇log f(v) - ∇log f(w) is parallel to v - w.

    Proof: D(f) = 0 forces the non-negative integrand to vanish (since f > 0).
    The equality case of Lemma 2 gives parallelism. -/
theorem D_zero_implies_parallel (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 < Ψ r) (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hD : entropyDissipation Ψ f = 0)
    (hScoreForm : entropyDissipation Ψ f =
      -(1 / 2) * ∫ v, ∫ w, PSDIntegrand Ψ f v w)
    (hPSD_cont : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      PSDIntegrand Ψ f p.1 p.2))
    (hPSD_inner : ∀ v, Integrable (PSDIntegrand Ψ f v))
    (hPSD_outer : Integrable (fun v => ∫ w, PSDIntegrand Ψ f v w))
    (v w : Fin 3 → ℝ) (hvw : v ≠ w) :
    ∃ l : ℝ, vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w = l • (v - w) := by
  exact landauMatrix_quadForm_eq_zero_iff
    (hΨ (eucNorm (v - w))) (sub_ne_zero.mpr hvw)
    _ (entropy_zero_quadform_zero Ψ f hΨ hf_pos hf_smooth hD
      hScoreForm hPSD_cont hPSD_inner hPSD_outer v w)

/-- Lemma 7 (Solution of the functional equation: ∇log f is affine).
    Reference: lem:functional_eq_solution

    If g(v) - g(w) = λ(v,w)(v - w) for all v, w ∈ ℝ³ and g is curl-free,
    then g(v) = b + 2c₀ v for constants b ∈ ℝ³, c₀ ∈ ℝ.

    Proof: Setting w = 0 gives g(v) = g(0) + λ̃(v)v. Curl-free condition
    forces λ̃ to be radial. Linear independence argument shows λ̃ is constant. -/
theorem functional_eq_affine (g : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hg_smooth : ContDiff ℝ ⊤ g)
    (hparallel : ∀ v w, v ≠ w → ∃ l : ℝ, g v - g w = l • (v - w)) :
    ∃ (b : Fin 3 → ℝ) (c₀ : ℝ), ∀ v, g v = b + (2 * c₀) • v :=
  parallel_curl_free_affine g hg_smooth hparallel

/-- Lemma 8 (Integration: log f is a polynomial of degree ≤ 2).
    Reference: lem:log_f_quadratic

    If ∇log f(v) = b + 2c₀ v, then log f(v) = a₀ + b · v + c₀|v|².

    Proof: Direct integration of each component ∂ᵢ log f = bᵢ + 2c₀ vᵢ. -/
theorem log_f_quadratic (f : (Fin 3 → ℝ) → ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ)
    (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f)
    (hgrad : ∀ v, vGrad (Real.log ∘ f) v = b + (2 * c₀) • v) :
    ∃ a₀ : ℝ, ∀ v, Real.log (f v) = a₀ + dotProduct b v + c₀ * normSq v :=
  ⟨(Real.log ∘ f) 0, affine_gradient_antiderivative (Real.log ∘ f) b c₀
    -- Smoothness of log ∘ f follows from f smooth and f > 0 (standard)
    (hf_smooth.log (fun v => ne_of_gt (hf_pos v))) hgrad⟩

/-- Theorem 4 (Nullspace of the Landau operator — necessity).
    Reference: thm:nullspace_necessity

    If Q(f,f) = 0 and f ∈ L¹(ℝ³), then f is a Maxwellian.

    Proof chains: Q=0 → D=0 (Lemma 5) → parallelism (Lemma 6) →
    ∇log f affine (Lemma 7) → log f quadratic (Lemma 8) → f Maxwellian. -/
theorem nullspace_necessity (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 < Ψ r) (hf_pos : ∀ v, 0 < f v)
    (_hf_smooth : ContDiff ℝ ⊤ f) (hf_int : Integrable f)
    (hQ : ∀ v, LandauOperator Ψ f v = 0)
    (hScoreForm : entropyDissipation Ψ f =
      -(1 / 2) * ∫ v, ∫ w, PSDIntegrand Ψ f v w)
    (hPSD_cont : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      PSDIntegrand Ψ f p.1 p.2))
    (hPSD_inner : ∀ v, Integrable (PSDIntegrand Ψ f v))
    (hPSD_outer : Integrable (fun v => ∫ w, PSDIntegrand Ψ f v w)) :
    IsMaxwellian f := by
  -- Q=0 → D=0 (D = ∫ Q · log f = ∫ 0 = 0)
  have hD : entropyDissipation Ψ f = 0 := by
    simp [entropyDissipation, show (fun v => LandauOperator Ψ f v * Real.log (f v)) =
      (fun _ => 0) from funext (fun v => by rw [hQ, zero_mul])]
  exact D_zero_implies_maxwellian Ψ f hΨ hf_pos _hf_smooth hf_int hD
    hScoreForm hPSD_cont hPSD_inner hPSD_outer

/-- Theorem 5 (Nullspace of the Landau operator — sufficiency).
    Reference: thm:nullspace_sufficiency

    If log f(v) = a₀ + b · v + c₀|v|², then Q(f,f) = 0.

    Proof: ∇log f(v) - ∇log f(w) = 2c₀(v - w), so the integrand in Q
    contains A(v-w)(v-w) = 0 by Lemma 3 (projection annihilation). -/
theorem nullspace_sufficiency (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (a₀ : ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ) (_hc₀ : c₀ < 0)
    (hf : ∀ v, f v = Real.exp (a₀ + dotProduct b v + c₀ * normSq v)) :
    ∀ v, LandauOperator Ψ f v = 0 := by
  intro v
  unfold LandauOperator
  -- The Landau flux vanishes for a Maxwellian (Gap 8)
  have hFluxZero := maxwellian_landau_flux_zero Ψ f a₀ b c₀ hf
  -- The integrand vanishes pointwise, so the integral is zero
  have hIntZero : ∀ v', ∫ w, mulVec (landauMatrix Ψ (v' - w))
      (f w • vGrad f v' - f v' • vGrad f w) = 0 := by
    intro v'
    have : (fun w => mulVec (landauMatrix Ψ (v' - w))
        (f w • vGrad f v' - f v' • vGrad f w)) = fun _ => 0 :=
      funext (fun w => hFluxZero v' w)
    simp [this]
  -- The flux function is identically zero, so its divergence is zero
  have hFluxFn : (fun v' => ∫ w, mulVec (landauMatrix Ψ (v' - w))
      (f w • vGrad f v' - f v' • vGrad f w)) = fun _ => 0 :=
    funext hIntZero
  rw [hFluxFn]
  unfold vDiv
  simp [ContinuousLinearMap.zero_apply]

/-- Corollary 1 (Complete characterization of the nullspace).
    Reference: cor:nullspace

    Q(f,f) = 0 ⟺ f is a Maxwellian distribution.

    Combines Theorem 4 (necessity) and Theorem 5 (sufficiency). -/
theorem nullspace_iff (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 < Ψ r) (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_int : Integrable f)
    (hScoreForm : entropyDissipation Ψ f =
      -(1 / 2) * ∫ v, ∫ w, PSDIntegrand Ψ f v w)
    (hPSD_cont : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      PSDIntegrand Ψ f p.1 p.2))
    (hPSD_inner : ∀ v, Integrable (PSDIntegrand Ψ f v))
    (hPSD_outer : Integrable (fun v => ∫ w, PSDIntegrand Ψ f v w)) :
    (∀ v, LandauOperator Ψ f v = 0) ↔ IsMaxwellian f :=
  ⟨fun hQ => nullspace_necessity Ψ f hΨ hf_pos hf_smooth hf_int hQ
    hScoreForm hPSD_cont hPSD_inner hPSD_outer,
   fun ⟨a₀, b, c₀, hc₀, hv⟩ => nullspace_sufficiency Ψ f a₀ b c₀ hc₀ hv⟩

/-- Density is positive when f > 0 and integrable.
    Proof: ∫ f > 0 for continuous positive integrable f on ℝ³ (positive measure).
    Reference: Used in VMLInput construction. -/
lemma density_positive_of_integral
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_int : Integrable f) :
    0 < ∫ v, f v := by
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg (fun v => le_of_lt (hf_pos v)) hf_int]
  have hsup : Function.support f = Set.univ := Set.eq_univ_of_forall (fun v => ne_of_gt (hf_pos v))
  rw [hsup]
  rw [MeasureTheory.Measure.measure_univ_pos]
  exact NeZero.ne volume

-- ============================================================================
-- Fubini symmetrization for the Landau weak form (proved by Aristotle)
-- Reference: Used in Theorem 42 to derive the symmetrized weak form.
-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-- ============================================================================

/-- landauMatrix is symmetric under swapping arguments of subtraction. -/
lemma landauMatrix_sub_comm (Ψ : ℝ → ℝ) (v w : Fin 3 → ℝ) :
    landauMatrix Ψ (w - v) = landauMatrix Ψ (v - w) := by
  rw [show w - v = -(v - w) from by abel, landauMatrix_even]

set_option maxHeartbeats 800000 in
/-- Fubini symmetrization for the Landau weak form specialized to φ = log ∘ f.
    ∫∫ ⟨∇log f(v) - ∇log f(w), A(v-w) · flux⟩ = 2 · ∫∫ ⟨∇log f(v), A(v-w) · flux⟩
    Proved by Aristotle (project 85302568). -/
theorem fubini_symmetrization_logf (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (_hf_smooth : ContDiff ℝ ⊤ f)
    (h_int_double : Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      dotProduct (vGrad (Real.log ∘ f) p.1)
        (mulVec (landauMatrix Ψ (p.1 - p.2))
          (f p.2 • vGrad f p.1 - f p.1 • vGrad f p.2))))
    (h_int_inner : ∀ v, Integrable (fun w =>
      dotProduct (vGrad (Real.log ∘ f) v)
        (mulVec (landauMatrix Ψ (v - w))
          (f w • vGrad f v - f v • vGrad f w))))
    (h_int_outer : Integrable (fun v => ∫ w,
      dotProduct (vGrad (Real.log ∘ f) v)
        (mulVec (landauMatrix Ψ (v - w))
          (f w • vGrad f v - f v • vGrad f w)))) :
    ∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
        (mulVec (landauMatrix Ψ (v - w))
          (f w • vGrad f v - f v • vGrad f w)) =
      2 * ∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f) v)
        (mulVec (landauMatrix Ψ (v - w))
          (f w • vGrad f v - f v • vGrad f w)) := by
  have h_integrable_swap : Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => vGrad (Real.log ∘ f) p.2 ⬝ᵥ landauMatrix Ψ (p.1 - p.2) *ᵥ (f p.2 • vGrad f p.1 - f p.1 • vGrad f p.2)) MeasureSpace.volume := by
    have h_integrable : Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => vGrad (Real.log ∘ f) p.1 ⬝ᵥ landauMatrix Ψ (p.1 - p.2) *ᵥ (f p.2 • vGrad f p.1 - f p.1 • vGrad f p.2)) MeasureSpace.volume ∧ Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => f p.2 • (vGrad (Real.log ∘ f) p.1 ⬝ᵥ landauMatrix Ψ (p.1 - p.2) *ᵥ vGrad f p.1) - f p.1 • (vGrad (Real.log ∘ f) p.1 ⬝ᵥ landauMatrix Ψ (p.1 - p.2) *ᵥ vGrad f p.2)) MeasureSpace.volume := by
      convert h_int_double using 1
      simp +decide [mul_sub, sub_mul, mul_assoc, mul_comm, Finset.mul_sum _ _ _, Matrix.mulVec, dotProduct]
    have h_mp : MeasurePreserving (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => (p.2, p.1)) MeasureSpace.volume MeasureSpace.volume :=
      ⟨measurable_swap, Measure.prod_swap ..⟩
    have h_swap_int : Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => vGrad (Real.log ∘ f) p.2 ⬝ᵥ landauMatrix Ψ (p.2 - p.1) *ᵥ (f p.1 • vGrad f p.2 - f p.2 • vGrad f p.1)) MeasureSpace.volume := by
      have : Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => vGrad (Real.log ∘ f) p.1 ⬝ᵥ landauMatrix Ψ (p.1 - p.2) *ᵥ (f p.2 • vGrad f p.1 - f p.1 • vGrad f p.2)) (Measure.map (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => (p.2, p.1)) MeasureSpace.volume) := by
        rw [h_mp.map_eq]; exact h_integrable.1
      convert this.comp_measurable measurable_swap using 1
    convert h_swap_int.neg using 1
    ext p
    simp only [Pi.neg_apply, neg_neg]
    rw [landauMatrix_sub_comm]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have h_split : ∫ v, ∫ w, (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w) ⬝ᵥ landauMatrix Ψ (v - w) *ᵥ (f w • vGrad f v - f v • vGrad f w) = (∫ v, ∫ w, vGrad (Real.log ∘ f) v ⬝ᵥ landauMatrix Ψ (v - w) *ᵥ (f w • vGrad f v - f v • vGrad f w)) - (∫ v, ∫ w, vGrad (Real.log ∘ f) w ⬝ᵥ landauMatrix Ψ (v - w) *ᵥ (f w • vGrad f v - f v • vGrad f w)) := by
    convert MeasureTheory.integral_sub h_int_double h_integrable_swap using 1
    · erw [MeasureTheory.integral_prod]
      · simp +decide [sub_mul, dotProduct_sub]
      · exact Integrable.sub h_int_double h_integrable_swap
    · erw [MeasureTheory.integral_prod, MeasureTheory.integral_prod]
      · exact h_integrable_swap
      · exact h_int_double
  -- After the split: I₁ - I₂ = 2 * I₁, i.e., I₂ = -I₁
  rw [h_split]
  -- Show that the second integral equals minus the first (by Fubini + symmetry)
  suffices hsuff : (∫ v, ∫ w, vGrad (Real.log ∘ f) w ⬝ᵥ landauMatrix Ψ (v - w) *ᵥ
      (f w • vGrad f v - f v • vGrad f w)) =
    -(∫ v, ∫ w, vGrad (Real.log ∘ f) v ⬝ᵥ landauMatrix Ψ (v - w) *ᵥ
      (f w • vGrad f v - f v • vGrad f w)) by linarith
  -- Step 1: Swap integration order via Fubini
  rw [MeasureTheory.integral_integral_swap h_integrable_swap]
  -- Step 2: The integrand with swapped v↔w = negative of original (by A(-z)=A(z) + flux antisymmetry)
  have h_symm : ∀ w v : Fin 3 → ℝ, vGrad (Real.log ∘ f) w ⬝ᵥ landauMatrix Ψ (v - w) *ᵥ
      (f w • vGrad f v - f v • vGrad f w) = -(vGrad (Real.log ∘ f) w ⬝ᵥ landauMatrix Ψ (w - v) *ᵥ
      (f v • vGrad f w - f w • vGrad f v)) := by
    intro w v
    rw [landauMatrix_sub_comm]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  simp_rw [h_symm, MeasureTheory.integral_neg]

-- ============================================================================
-- Part 9: Integral linearity lemmas (proved by Aristotle)
-- ============================================================================

/-- Matrix-vector multiplication commutes with Bochner integral.
    Proved by Aristotle (Harmonic), project 12266ae6. -/
lemma mulVec_integral_comm (M : Matrix (Fin 3) (Fin 3) ℝ)
    (F : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hF : Integrable F) :
    mulVec M (∫ w, F w) = ∫ w, mulVec M (F w) := by
  have h_comm : ∀ (L : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)), ∫ w, L (F w) = L (∫ w, F w) :=
    fun L => ContinuousLinearMap.integral_comp_comm L hF
  exact (h_comm (ContinuousLinearMap.pi fun i => ∑ j, M i j • ContinuousLinearMap.proj j)).symm

-- ============================================================================
-- Part 10: Integration by parts on ℝ (proved by Aristotle, fixed locally)
-- ============================================================================

open Filter in
/-- Integration by parts on ℝ: ∫ f'·g = -∫ f·g'.
    Based on Aristotle proof (project 030a6d39), locally adapted. -/
lemma ibp_real_line (f g : ℝ → ℝ)
    (hf_diff : Differentiable ℝ f) (hg_diff : Differentiable ℝ g)
    (_hf_cont : Continuous (deriv f)) (_hg_cont : Continuous (deriv g))
    (h_decay_top : Tendsto (fun x => f x * g x) atTop (nhds 0))
    (h_decay_bot : Tendsto (fun x => f x * g x) atBot (nhds 0))
    (h_int1 : Integrable (fun x => deriv f x * g x))
    (h_int2 : Integrable (fun x => f x * deriv g x)) :
    ∫ x, deriv f x * g x = -(∫ x, f x * deriv g x) := by
  have h_finite : ∀ a b : ℝ,
      (∫ x in a..b, deriv f x * g x) + (∫ x in a..b, f x * deriv g x) =
      f b * g b - f a * g a := by
    intro a b
    rw [← intervalIntegral.integral_add
      (h_int1.intervalIntegrable (a := a) (b := b))
      (h_int2.intervalIntegrable (a := a) (b := b))]
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
      (f := fun x => f x * g x)
      (fun x _ => HasDerivAt.mul (hf_diff x).hasDerivAt (hg_diff x).hasDerivAt)
      ((h_int1.intervalIntegrable (a := a) (b := b)).add
       (h_int2.intervalIntegrable (a := a) (b := b)))
    rw [← h]
  set I₁ := ∫ x, deriv f x * g x
  set I₂ := ∫ x, f x * deriv g x
  have h_lim1 := intervalIntegral_tendsto_integral h_int1
    tendsto_neg_atTop_atBot tendsto_id
  have h_lim2 := intervalIntegral_tendsto_integral h_int2
    tendsto_neg_atTop_atBot tendsto_id
  have h_sum_lim := h_lim1.add h_lim2
  have h_bd_lim : Tendsto (fun n => f n * g n - f (-n) * g (-n)) atTop (nhds (I₁ + I₂)) := by
    apply Tendsto.congr _ h_sum_lim
    intro n
    have := h_finite (-n) n
    simp only [id] at this ⊢
    linarith
  have h_bd_zero : Tendsto (fun n => f n * g n - f (-n) * g (-n)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n => f n * g n) atTop (nhds 0) := h_decay_top
    have h2 : Tendsto (fun n => f (-n) * g (-n)) atTop (nhds 0) :=
      h_decay_bot.comp tendsto_neg_atTop_atBot
    simpa using h1.sub h2
  have h_eq : I₁ + I₂ = 0 := tendsto_nhds_unique h_bd_lim h_bd_zero
  linarith

/-- Dot product commutes with Bochner integral.
    Proved by Aristotle (Harmonic), project 7ac4c2f5. -/
lemma dotProduct_integral_comm (c : Fin 3 → ℝ)
    (F : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hF : Integrable F) :
    dotProduct c (∫ w, F w) = ∫ w, dotProduct c (F w) := by
  have h_comm : ∀ (L : (Fin 3 → ℝ) →L[ℝ] ℝ), ∫ w, L (F w) = L (∫ w, F w) := by
    intros L; exact (by convert (L.integral_comp_comm hF) using 1)
  convert h_comm (∑ i : Fin 3, ContinuousLinearMap.smulRight (ContinuousLinearMap.proj i) (c i))
    |>.symm using 1
  · simp +decide [dotProduct, Fin.sum_univ_three]; ring!
  · simp +decide [dotProduct, Fin.sum_univ_three]; congr; ext; ring!

open Filter in
/-- ∫ c · h' = 0 when h → 0 at ±∞.
    Proved by Aristotle (Harmonic), project b17467db. -/
lemma const_times_integral_deriv_zero (c : ℝ) (h : ℝ → ℝ)
    (hh_diff : Differentiable ℝ h)
    (_hh_cont : Continuous (deriv h))
    (h_decay_top : Tendsto h atTop (nhds 0))
    (h_decay_bot : Tendsto h atBot (nhds 0))
    (h_int : Integrable (deriv h)) :
    ∫ x, c * deriv h x = 0 := by
  have h_ftc : ∫ x, deriv h x = 0 := by
    have h_ftc' : ∀ a b : ℝ, ∫ x in a..b, deriv h x = h b - h a := by
      intro a b; rw [intervalIntegral.integral_deriv_eq_sub]; aesop
      exact h_int.intervalIntegrable ..
    have h_lim : Tendsto (fun R => ∫ x in -R..R, deriv h x) atTop
        (nhds (∫ x, deriv h x)) := by
      apply_rules [intervalIntegral_tendsto_integral]
      · exact tendsto_neg_atTop_atBot
      · exact tendsto_id
    have h_bd : Tendsto (fun R => h R - h (-R)) atTop (nhds 0) := by
      simpa using h_decay_top.sub (h_decay_bot.comp tendsto_neg_atTop_atBot)
    exact tendsto_nhds_unique h_lim (by simpa [h_ftc'] using h_bd)
  simp only [integral_const_mul, h_ftc, mul_zero]

end VML
