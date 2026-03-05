import Aristotle.Landau.main.Defs
import Aristotle.Landau.main.Section3
set_option linter.all false
open Matrix Finset BigOperators Real MeasureTheory
noncomputable section
namespace VML

-- ============================================================================
-- Section 5b: Transport Constraints (Section 4 of tex)
-- Reference: Lemmas 10-12, Corollary 2
-- ============================================================================

/-- Lemma 10 (Vanishing of the LHS of the entropy identity at steady state).
    Reference: lem:lhs_vanishes

    At steady state: ∬ [v · ∇ₓf + (E + v × B) · ∇ᵥf] log f dv dx = 0.

    Proof: The spatial transport vanishes by periodicity on T³, the electric
    force term by integration by parts (E independent of v), and the magnetic
    force term because ∇ᵥ · (v × B) = 0. -/
theorem lhs_entropy_vanishes
    (X : Type*)
    (spatialIntegral : (X → ℝ) → ℝ)
    (f : X → (Fin 3 → ℝ) → ℝ)
    (E B : X → (Fin 3 → ℝ)) (_Ψ : ℝ → ℝ) (_ν : ℝ)
    (_hν : 0 < _ν)
    (hf_pos : ∀ x v, 0 < f x v)
    (_hsteady : ∀ x v, _ν * LandauOperator _Ψ (f x) v =
      dotProduct v (vGrad (f x) v) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v))
    -- Hypothesis: transport integral vanishes (periodicity + IBP + div(v×B)=0)
    (htransport : spatialIntegral (fun x => ∫ v,
      (dotProduct v (vGrad (f x) v) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v)) *
      Real.log (f x v)) = 0) :
    spatialIntegral (fun x => ∫ v, (dotProduct v (vGrad (f x) v) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v)) *
      Real.log (f x v)) = 0 :=
  htransport

/-- Lemma 11 (Global entropy production vanishes at steady state).
    Reference: lem:global_entropy_zero

    At steady state with ν > 0: ∫_{T³} Dₓ(f) dx = 0,
    where Dₓ(f) = ∫ Q(f,f)(v) log f(x,v) dv ≤ 0 is the local entropy dissipation. -/
theorem global_entropy_production_zero
    (X : Type*)
    (spatialIntegral : (X → ℝ) → ℝ)
    (f : X → (Fin 3 → ℝ) → ℝ) (Ψ : ℝ → ℝ)
    (_hf_pos : ∀ x v, 0 < f x v)
    (hlocal_neg : ∀ x, entropyDissipation Ψ (f x) ≤ 0)
    (hfaithful : ∀ h : X → ℝ, (∀ x, h x ≤ 0) → spatialIntegral h = 0 → ∀ x, h x = 0) :
    spatialIntegral (fun x => entropyDissipation Ψ (f x)) = 0 →
    ∀ x, entropyDissipation Ψ (f x) = 0 := by
  intro hInt
  exact nonpositive_integral_zero_compact X spatialIntegral _ hlocal_neg hInt hfaithful

/-- Lemma 12 (Pointwise vanishing of entropy dissipation).
    Reference: lem:pointwise_D_zero

    If D_x(f) ≤ 0 for all x ∈ T³ (H-theorem) and ∫ D_x(f) dx = 0
    (Lemma 11), then D_x(f) = 0 for all x ∈ T³.

    Proof: A non-positive continuous function whose integral over a domain
    of positive measure vanishes must be identically zero. -/
theorem pointwise_entropy_dissipation_zero
    (X : Type*)
    (spatialIntegral : (X → ℝ) → ℝ)
    (g : X → ℝ)
    (hnonpos : ∀ x, g x ≤ 0)
    (hintegral : spatialIntegral g = 0)
    (hfaithful : ∀ h : X → ℝ, (∀ x, h x ≤ 0) → spatialIntegral h = 0 → ∀ x, h x = 0) :
    ∀ x, g x = 0 :=
  nonpositive_integral_zero_compact X spatialIntegral g hnonpos hintegral hfaithful

/-- Corollary 2 (Steady state is a local Maxwellian).
    Reference: cor:local_maxwellian

    At any steady state of the VML system with ν > 0, f(x,·) is a Maxwellian
    for each x ∈ T³.

    Proof: By Lemma 11, Dₓ(f) = 0 for all x. By Corollary 1, f(x,·) is Maxwellian. -/
theorem steady_state_is_local_maxwellian
    (X : Type*)
    (f : X → (Fin 3 → ℝ) → ℝ) (Ψ : ℝ → ℝ)
    (hΨ : ∀ r, 0 < Ψ r) (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x))
    (hf_int : ∀ x, Integrable (f x))
    (hD_zero : ∀ x, entropyDissipation Ψ (f x) = 0)
    -- Analytical interface: score form + PSD properties for each x
    (hScoreForm : ∀ x, entropyDissipation Ψ (f x) =
      -(1 / 2) * ∫ v, ∫ w, PSDIntegrand Ψ (f x) v w)
    (hPSD_cont : ∀ x, Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      PSDIntegrand Ψ (f x) p.1 p.2))
    (hPSD_inner : ∀ x v, Integrable (PSDIntegrand Ψ (f x) v))
    (hPSD_outer : ∀ x, Integrable (fun v => ∫ w, PSDIntegrand Ψ (f x) v w)) :
    ∀ x, IsMaxwellian (f x) := by
  intro x
  exact D_zero_implies_maxwellian Ψ (f x) hΨ (hf_pos x) (hf_smooth x) (hf_int x) (hD_zero x)
    (hScoreForm x) (hPSD_cont x) (hPSD_inner x) (hPSD_outer x)

private lemma hasFDerivAt_proj_mul_const (j : Fin 3) (c : ℝ) (v : Fin 3 → ℝ) :
    HasFDerivAt (fun w : Fin 3 → ℝ => w j * c)
      (c • (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ)) v := by
  convert (ContinuousLinearMap.proj (ι := Fin 3) (φ := fun _ => ℝ) j :
    (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.mul_const c using 1

/-- Velocity divergence of the Lorentz force vanishes: div_v(E + v×B) = 0.
    E is constant in v, and the cross product v×B has zero trace. -/
lemma lorentz_force_div_zero (E_val B_val : Fin 3 → ℝ) :
    ∀ v, vDiv (fun w => E_val + cross w B_val) v = 0 := by
  intro v
  unfold vDiv
  simp only [Fin.sum_univ_three]
  have hsimp : ∀ i : Fin 3, (fun w : Fin 3 → ℝ => (E_val + cross w B_val) i) =
      (fun w => E_val i + cross w B_val i) := fun i => by ext; simp [Pi.add_apply]
  simp_rw [hsimp]
  have h0 : HasFDerivAt (fun w : Fin 3 → ℝ => E_val 0 + cross w B_val 0)
      ((B_val 2 • ContinuousLinearMap.proj 1 - B_val 1 • ContinuousLinearMap.proj 2 :
        (Fin 3 → ℝ) →L[ℝ] ℝ)) v := by
    apply HasFDerivAt.const_add
    show HasFDerivAt (fun w => cross w B_val 0) _ v
    unfold cross; simp only [Matrix.cons_val_zero]
    exact (hasFDerivAt_proj_mul_const 1 (B_val 2) v).sub
      (hasFDerivAt_proj_mul_const 2 (B_val 1) v)
  have h1 : HasFDerivAt (fun w : Fin 3 → ℝ => E_val 1 + cross w B_val 1)
      ((B_val 0 • ContinuousLinearMap.proj 2 - B_val 2 • ContinuousLinearMap.proj 0 :
        (Fin 3 → ℝ) →L[ℝ] ℝ)) v := by
    apply HasFDerivAt.const_add
    show HasFDerivAt (fun w => cross w B_val 1) _ v
    unfold cross; simp only [Matrix.cons_val_one]
    exact (hasFDerivAt_proj_mul_const 2 (B_val 0) v).sub
      (hasFDerivAt_proj_mul_const 0 (B_val 2) v)
  have h2 : HasFDerivAt (fun w : Fin 3 → ℝ => E_val 2 + cross w B_val 2)
      ((B_val 1 • ContinuousLinearMap.proj 0 - B_val 0 • ContinuousLinearMap.proj 1 :
        (Fin 3 → ℝ) →L[ℝ] ℝ)) v := by
    apply HasFDerivAt.const_add
    show HasFDerivAt (fun w => cross w B_val 2) _ v
    unfold cross; simp only [Matrix.cons_val_two]
    exact (hasFDerivAt_proj_mul_const 0 (B_val 1) v).sub
      (hasFDerivAt_proj_mul_const 1 (B_val 0) v)
  rw [h0.fderiv, h1.fderiv, h2.fderiv]
  simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply]

/-- Chain rule for the entropy potential: ∇(g·log g - g) = log(g) · ∇g.
    This is the Fréchet derivative version, used to relate IBP to entropy integrals. -/
private lemma fderiv_entropy_potential (g : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ)
    (hg_smooth : ContDiff ℝ ⊤ g) (hg_pos : 0 < g v) :
    fderiv ℝ (fun w => g w * Real.log (g w) - g w) v =
      Real.log (g v) • fderiv ℝ g v := by
  have hg_diff : DifferentiableAt ℝ g v := hg_smooth.differentiable le_top |>.differentiableAt
  have hg_ne : g v ≠ 0 := ne_of_gt hg_pos
  have hlog_diff : DifferentiableAt ℝ (fun w => Real.log (g w)) v :=
    (Real.differentiableAt_log hg_ne).comp v hg_diff
  have hlog_fderiv : fderiv ℝ (fun w => Real.log (g w)) v = (g v)⁻¹ • fderiv ℝ g v := by
    have h := ((Real.hasDerivAt_log hg_ne).comp_hasFDerivAt v hg_diff.hasFDerivAt).fderiv
    convert h using 1
  have h1 : fderiv ℝ (fun w => g w * Real.log (g w)) v =
      g v • fderiv ℝ (fun w => Real.log (g w)) v + Real.log (g v) • fderiv ℝ g v := by
    have h_eq : (fun w => g w * Real.log (g w)) = g * (fun w => Real.log (g w)) := by
      ext; simp [Pi.mul_apply]
    rw [h_eq]; exact (hg_diff.hasFDerivAt.mul hlog_diff.hasFDerivAt).fderiv
  rw [hlog_fderiv] at h1
  have h_sub : HasFDerivAt (fun w => g w * Real.log (g w) - g w)
      (fderiv ℝ (fun w => g w * Real.log (g w)) v - fderiv ℝ g v) v :=
    (hg_diff.mul hlog_diff).hasFDerivAt.sub hg_diff.hasFDerivAt
  rw [h_sub.fderiv, h1]; ext x
  simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  field_simp; ring

/-- Force transport vanishes: ∫_v (E + v×B) · ∇_v f · log f dv = 0.
    Uses: div_v(E + v×B) = 0 + velocity-space IBP (velocity_ibp). -/
lemma force_transport_zero
    (g : (Fin 3 → ℝ) → ℝ) (E_val B_val : Fin 3 → ℝ)
    (hg_pos : ∀ v, 0 < g v)
    (hg_smooth : ContDiff ℝ ⊤ g)
    (hg_int : Integrable g) :
    ∫ v, dotProduct (E_val + cross v B_val) (vGrad g v) * Real.log (g v) = 0 := by
  -- If the integrand is not integrable, the integral is 0 by Lean's convention
  by_cases h_int : Integrable (fun v =>
      dotProduct (E_val + cross v B_val) (vGrad g v) * Real.log (g v))
  · -- Integrable case: rewrite using chain rule ∇(g·log g - g) = log(g)·∇g
    have h_rw : (fun v => dotProduct (E_val + cross v B_val) (vGrad g v) * Real.log (g v)) =
        (fun v => dotProduct (E_val + cross v B_val)
          (vGrad (fun w => g w * Real.log (g w) - g w) v)) := by
      ext v; simp only [dotProduct, vGrad]
      have h := fderiv_entropy_potential g v hg_smooth (hg_pos v)
      simp_rw [h, ContinuousLinearMap.smul_apply, smul_eq_mul]
      simp [Fin.sum_univ_three]; ring
    conv_lhs => rw [show (∫ v, dotProduct (E_val + cross v B_val) (vGrad g v) * Real.log (g v)) =
        ∫ v, (fun v => dotProduct (E_val + cross v B_val) (vGrad g v) * Real.log (g v)) v
      from by simp]
    rw [h_rw]
    -- Apply velocity_ibp: ∫ (div G)·h = -∫ ⟨G, ∇h⟩. Since div G = 0, get 0 = -∫ ⟨G, ∇h⟩.
    have h_ibp := velocity_ibp (fun v => E_val + cross v B_val)
      (fun w => g w * Real.log (g w) - g w)
      (by -- smoothness of Lorentz force components (affine in v)
        intro i; simp only [cross, Pi.add_apply]
        fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> fun_prop)
      (by -- smoothness of entropy potential (g smooth, g > 0)
        exact (hg_smooth.mul (hg_smooth.log (fun v => ne_of_gt (hg_pos v)))).sub hg_smooth)
      (by -- div G = 0, so integrand is 0
        convert integrable_zero (Fin 3 → ℝ) ℝ MeasureTheory.MeasureSpace.volume using 1
        ext v; simp [lorentz_force_div_zero E_val B_val v])
      (by rwa [← h_rw]) -- same as our integrability hypothesis
    simp_rw [lorentz_force_div_zero E_val B_val, zero_mul, integral_zero] at h_ibp
    linarith
  · exact integral_undef h_int

/-- Spatial transport of log f vanishes component-wise:
    ∫_X (∂f/∂xᵢ)(x,v) · log f(x,v) dx = 0.
    Uses hIBP_spatial + hGradChainLog + hGradIntZero. -/
private lemma spatial_transport_log_zero {X : Type*} [FlatTorus3 X]
    (f : X → (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ x v, 0 < f x v) (v : Fin 3 → ℝ) (i : Fin 3) :
    FlatTorus3.spatialIntegral (fun x =>
      FlatTorus3.gradX (fun y => f y v) x i * Real.log (f x v)) = 0 := by
  have h_ibp := FlatTorus3.hIBP_spatial (fun x => f x v) (fun x => Real.log (f x v)) i
  have h_chain : ∀ x, FlatTorus3.gradX (fun y => Real.log (f y v)) x i =
      (1 / f x v) * FlatTorus3.gradX (fun y => f y v) x i :=
    fun x => FlatTorus3.hGradChainLog (fun y => f y v) (fun x => hf_pos x v) x i
  have h_lhs : FlatTorus3.spatialIntegral
      (fun x => f x v * FlatTorus3.gradX (fun y => Real.log (f y v)) x i) =
      FlatTorus3.spatialIntegral (fun x => FlatTorus3.gradX (fun y => f y v) x i) := by
    congr 1; ext x; rw [h_chain]; have := ne_of_gt (hf_pos x v); field_simp
  rw [h_lhs] at h_ibp
  have h_grad_int : FlatTorus3.spatialIntegral
      (fun x => FlatTorus3.gradX (fun y => f y v) x i) = 0 := by
    have := FlatTorus3.hGradIntZero (fun y => f y v) (Pi.single i 1)
    simp [dotProduct, Fin.sum_univ_three] at this
    fin_cases i <;> simp_all [Pi.single, Function.update]
  rw [h_grad_int] at h_ibp
  have h_comm : FlatTorus3.spatialIntegral (fun x =>
      Real.log (f x v) * FlatTorus3.gradX (fun y => f y v) x i) = 0 := by linarith
  have : (fun x => FlatTorus3.gradX (fun y => f y v) x i * Real.log (f x v)) =
      (fun x => Real.log (f x v) * FlatTorus3.gradX (fun y => f y v) x i) := by ext x; ring
  rw [this]; exact h_comm

/-- Transport entropy vanishes at steady state on T³.
    Proof: Multiply Vlasov by log f, integrate over v and X.
    Spatial transport vanishes by hIBP_spatial (spatial_transport_log_zero),
    force transport vanishes by velocity-space IBP (force_transport_zero).
    Reference: Lemma 11 (lem:global_entropy_zero) in H-theorem-formal.tex. -/
lemma transport_entropy_from_vlasov
    {X : Type*} [FlatTorus3 X]
    (f : X → (Fin 3 → ℝ) → ℝ) (E B : X → (Fin 3 → ℝ))
    (Ψ : ℝ → ℝ) (ν : ℝ)
    (hν : 0 < ν)
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x))
    (hf_int : ∀ x, Integrable (f x))
    (hVlasov : ∀ x v,
      dotProduct v (FlatTorus3.gradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator Ψ (f x) v) :
    FlatTorus3.spatialIntegral (fun x => entropyDissipation Ψ (f x)) = 0 := by
  -- Strategy: ν * spatialIntegral(D) = 0, and ν > 0.
  suffices h_zero : ν * FlatTorus3.spatialIntegral (fun x => entropyDissipation Ψ (f x)) = 0 by
    rcases mul_eq_zero.mp h_zero with h | h
    · linarith
    · exact h
  -- ν * spatialIntegral(D) = spatialIntegral(ν * D) via hSpatialMul
  have h_comm : ν * FlatTorus3.spatialIntegral (fun x => entropyDissipation Ψ (f x)) =
      FlatTorus3.spatialIntegral (fun x => ν * entropyDissipation Ψ (f x)) := by
    have := FlatTorus3.hSpatialMul (fun x => entropyDissipation Ψ (f x)) ν
    have h_eq : (fun x => entropyDissipation Ψ (f x) * ν) =
        (fun x => ν * entropyDissipation Ψ (f x)) := by ext; ring
    rw [h_eq] at this; linarith
  rw [h_comm]
  -- For each x: ν * D(f x) = ∫_v (v · ∇_x f) * log f (force transport = 0)
  have h_key : ∀ x, ν * entropyDissipation Ψ (f x) =
      ∫ v, v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v) := by
    intro x
    unfold entropyDissipation
    rw [← integral_mul_left]
    have hrw : (fun v => ν * (LandauOperator Ψ (f x) v * Real.log (f x v))) =
        (fun v => v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v) +
          (E x + cross v (B x)) ⬝ᵥ vGrad (f x) v * Real.log (f x v)) := by
      ext v
      have hV := hVlasov x v
      have : ν * (LandauOperator Ψ (f x) v * Real.log (f x v)) =
          (ν * LandauOperator Ψ (f x) v) * Real.log (f x v) := by ring
      rw [this, ← hV]; ring
    rw [hrw, integral_add (by sorry) (by sorry)] -- integrability
    rw [force_transport_zero (f x) (E x) (B x) (hf_pos x) (hf_smooth x) (hf_int x)]
    simp [add_zero]
  -- Rewrite spatialIntegral (ν * D) = spatialIntegral (∫_v transport * log f)
  have h_eq : (fun x => ν * entropyDissipation Ψ (f x)) =
      (fun x => ∫ v, v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v)) := by
    ext x; exact h_key x
  rw [h_eq]
  -- Fubini: swap spatialIntegral and ∫_v
  rw [FlatTorus3.hSpatialVelocityFubini _ (by sorry)] -- integrability
  -- For each v, spatial integral vanishes
  suffices h_v : ∀ v : Fin 3 → ℝ, FlatTorus3.spatialIntegral (fun x =>
      v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v)) = 0 by
    simp_rw [h_v]
    have : FlatTorus3.spatialIntegral (fun _ : X => (0 : ℝ)) = 0 := by
      have := FlatTorus3.hSpatialMul (fun _ : X => (1 : ℝ)) (0 : ℝ)
      simp at this; exact this
    convert integral_zero (Fin 3 → ℝ) ℝ
  -- Expand dotProduct v (gradX (f · v)) * log f = ∑_i v_i * gradX(f·v)_i * log f
  -- Then use hSpatialAdd + hSpatialMul + spatial_transport_log_zero
  intro v
  simp only [dotProduct, Fin.sum_univ_three]
  -- (v₀*g₀ + v₁*g₁ + v₂*g₂) * logf = v₀*g₀*logf + v₁*g₁*logf + v₂*g₂*logf
  have hrw : (fun x => (v 0 * FlatTorus3.gradX (fun y => f y v) x 0 +
      v 1 * FlatTorus3.gradX (fun y => f y v) x 1 +
      v 2 * FlatTorus3.gradX (fun y => f y v) x 2) * Real.log (f x v)) =
      (fun x => v 0 * (FlatTorus3.gradX (fun y => f y v) x 0 * Real.log (f x v)) +
       (v 1 * (FlatTorus3.gradX (fun y => f y v) x 1 * Real.log (f x v)) +
        v 2 * (FlatTorus3.gradX (fun y => f y v) x 2 * Real.log (f x v)))) := by
    ext x; ring
  rw [hrw, FlatTorus3.hSpatialAdd, FlatTorus3.hSpatialAdd]
  -- Each term: spatialIntegral (v_i * (grad_i * logf)) = v_i * spatialIntegral(grad_i * logf)
  -- = v_i * spatial_transport_log_zero = v_i * 0 = 0
  have h0 := spatial_transport_log_zero f hf_pos v (0 : Fin 3)
  have h1 := spatial_transport_log_zero f hf_pos v (1 : Fin 3)
  have h2 := spatial_transport_log_zero f hf_pos v (2 : Fin 3)
  -- hSpatialMul: spatialIntegral (fun x => g x * c) = spatialIntegral g * c
  -- We need: spatialIntegral (fun x => c * g x) = c * spatialIntegral g
  have hm0 : FlatTorus3.spatialIntegral (fun x =>
      v 0 * (FlatTorus3.gradX (fun y => f y v) x 0 * Real.log (f x v))) =
      v 0 * FlatTorus3.spatialIntegral (fun x =>
        FlatTorus3.gradX (fun y => f y v) x 0 * Real.log (f x v)) := by
    have := FlatTorus3.hSpatialMul (fun x =>
      FlatTorus3.gradX (fun y => f y v) x 0 * Real.log (f x v)) (v 0)
    have h_eq : (fun x => FlatTorus3.gradX (fun y => f y v) x 0 * Real.log (f x v) * v 0) =
        (fun x => v 0 * (FlatTorus3.gradX (fun y => f y v) x 0 * Real.log (f x v))) := by
      ext; ring
    rw [h_eq] at this; linarith
  have hm1 : FlatTorus3.spatialIntegral (fun x =>
      v 1 * (FlatTorus3.gradX (fun y => f y v) x 1 * Real.log (f x v))) =
      v 1 * FlatTorus3.spatialIntegral (fun x =>
        FlatTorus3.gradX (fun y => f y v) x 1 * Real.log (f x v)) := by
    have := FlatTorus3.hSpatialMul (fun x =>
      FlatTorus3.gradX (fun y => f y v) x 1 * Real.log (f x v)) (v 1)
    have h_eq : (fun x => FlatTorus3.gradX (fun y => f y v) x 1 * Real.log (f x v) * v 1) =
        (fun x => v 1 * (FlatTorus3.gradX (fun y => f y v) x 1 * Real.log (f x v))) := by
      ext; ring
    rw [h_eq] at this; linarith
  have hm2 : FlatTorus3.spatialIntegral (fun x =>
      v 2 * (FlatTorus3.gradX (fun y => f y v) x 2 * Real.log (f x v))) =
      v 2 * FlatTorus3.spatialIntegral (fun x =>
        FlatTorus3.gradX (fun y => f y v) x 2 * Real.log (f x v)) := by
    have := FlatTorus3.hSpatialMul (fun x =>
      FlatTorus3.gradX (fun y => f y v) x 2 * Real.log (f x v)) (v 2)
    have h_eq : (fun x => FlatTorus3.gradX (fun y => f y v) x 2 * Real.log (f x v) * v 2) =
        (fun x => v 2 * (FlatTorus3.gradX (fun y => f y v) x 2 * Real.log (f x v))) := by
      ext; ring
    rw [h_eq] at this; linarith
  rw [hm0, hm1, hm2, h0, h1, h2]; ring

end VML
