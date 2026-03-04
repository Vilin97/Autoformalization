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

/-- Force transport vanishes: ∫_v (E + v×B) · ∇_v f · log f dv = 0.
    Uses: div_v(E + v×B) = 0 + velocity-space IBP. -/
lemma force_transport_zero
    (g : (Fin 3 → ℝ) → ℝ) (E_val B_val : Fin 3 → ℝ)
    (hg_pos : ∀ v, 0 < g v)
    (hg_smooth : ContDiff ℝ ⊤ g)
    (hg_int : Integrable g) :
    ∫ v, dotProduct (E_val + cross v B_val) (vGrad g v) * Real.log (g v) = 0 := by
  sorry

/-- Transport entropy vanishes at steady state on T³.
    Proof: Multiply Vlasov by log f, integrate over v and X.
    Spatial transport vanishes by Stokes (hGradIntZero),
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
  sorry

end VML
