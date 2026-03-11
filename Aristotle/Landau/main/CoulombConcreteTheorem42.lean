import Aristotle.Landau.main.CoulombSpatialTransport
import Aristotle.Landau.main.CoulombFlux
import Aristotle.Landau.main.CoulombPSD
import Aristotle.Landau.main.CoulombFluxDiff
import Aristotle.Landau.main.IteratedDerivHelpers

/-!
# Concrete Theorem 4.2 for Coulomb Collisions on T^3

Specializes the abstract `ConcreteTheorem42` to the Coulomb kernel Psi(r) = r^{-3},
the physically most important case in plasma physics. Verifies all 19 fields of
`VelocityDecayConditions` for Coulomb and states the main result: any smooth
steady state of the VML system with Coulomb collisions is a global Maxwellian
with E = 0 and B = const.
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

/-- **Coulomb Theorem 42.** Characterization of smooth steady states of the
    Vlasov–Maxwell–Landau system with Coulomb collisions on T³ = (ℝ/ℤ)³.

    This is the physically most important case: Coulomb interactions between
    charged particles in a plasma. The collision kernel Ψ(r) = r⁻³ is singular
    at r = 0 but the formalization handles this via the PSD continuity condition
    in VelocityDecayConditions (the singularity cancels in the quadratic form).

    **Hypotheses** (13 total):
    - 2 physical parameters (ν > 0, ρ_ion > 0)
    - 1 strict positivity (f > 0)
    - 3 smoothness (f smooth in v and x, B smooth)
    - 3 decay (Schwartz in v; stretched-exponential lower bound; polynomial score)
    - 4 equations (Vlasov, Ampère, Gauss, div B = 0)

    **Independence note:** Hypothesis 9 (hGradBound, polynomial score bound) is
    NOT derivable from hypotheses 7-8 alone. The ratio |∂f|/f equals
    |∂f| * exp(C(1+‖v‖)^K) in the worst case, which grows super-polynomially
    for K ≥ 1. Counterexample: f(v) = exp(-|v|²)(2 + sin(exp(⟨v⟩))) is Schwartz
    with stretched-exponential lower bound, but |∂f|/f grows like exp(⟨v⟩).
    The polynomial score bound is a genuine additional assumption, satisfied by
    physically relevant distributions (Maxwellians, perturbations thereof).

    **Scope:** Single species, non-relativistic, 3D flat torus, Coulomb kernel
    (Ψ(r) = r⁻³). Assumes existence of a smooth positive steady-state solution. -/
theorem CoulombConcreteTheorem42
    -- === Physical state at steady state ===
    (f : Torus3 → (Fin 3 → ℝ) → ℝ)
    (E B : Torus3 → Fin 3 → ℝ)
    (ν ρ_ion : ℝ)
    -- === Physical parameters ===
    (hν : 0 < ν)                                -- (1)
    (hρ_ion : 0 < ρ_ion)                        -- (2)
    (hf_pos : ∀ x v, 0 < f x v)                -- (3)
    -- === Smoothness ===
    (hf_smooth_v : ∀ x, ContDiff ℝ ⊤ (f x))                             -- (4)
    (hf_smooth_x : ∀ v, ContDiff ℝ ⊤ (periodicLift (fun x => f x v)))   -- (5)
    (hB_smooth : ∀ i, ContDiff ℝ ⊤ (periodicLift (fun x => B x i)))     -- (6)
    -- === Schwartz-class velocity decay, uniform in x ===
    (hSchwartz : UniformSchwartzDecay f)         -- (7)
    (hExpDecay : ∃ (C : ℝ) (K : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      Real.exp (-C * (1 + ‖v‖) ^ K) ≤ f x v)   -- (8)
    -- === Polynomial score bound (independent of hSchwartz + hExpDecay) ===
    -- This is NOT derivable from hSchwartz + hExpDecay: the ratio |∂f|/f can grow
    -- super-polynomially even for Schwartz f with exponential lower bound.
    -- Satisfied by Maxwellians and physically reasonable perturbations.
    (hGradBound : ∃ (Cg : ℝ) (Kg : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ) (i : Fin 3),
      |fderiv ℝ (f x) v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * f x v) -- (9)
    -- === Steady-state Vlasov equation with Coulomb kernel ===
    (hVlasov : ∀ x v,
      dotProduct v (torusGradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator coulombKernel (f x) v)  -- (10)
    -- === Steady-state Maxwell equations ===
    (hAmpere : ∀ x, torusCurlX B x = fun i => ∫ v, v i * f x v)       -- (11)
    (hGauss : ∀ x, torusDivX E x = (∫ v, f x v) - ρ_ion)              -- (12)
    (hDivB : ∀ x, torusDivX B x = 0)             -- (13)
    :
    -- === Conclusion ===
    ∃ (T_eq : ℝ) (B₀ : Fin 3 → ℝ), 0 < T_eq ∧
    (∀ x v, f x v = equilibriumMaxwellian ρ_ion T_eq v) ∧
    (∀ x, E x = 0) ∧
    (∀ x, B x = B₀) := by
  -- Derive log bound from Schwartz + ExpDecay (used by many fields)
  have hLogBound := schwartz_log_bound hf_pos hSchwartz hExpDecay
  -- Schwartz decay specialized to each x (used in many fields below)
  have hSchwartz_x : ∀ x, ∀ N k, ∃ C > 0, ∀ v,
      ‖iteratedFDeriv ℝ k (f x) v‖ * (1 + ‖v‖) ^ N ≤ C := fun x N k =>
    hSchwartz.hDecay N k |>.imp fun C hC => ⟨hC.1, fun v => hC.2 x v⟩
  -- Extract gradient bound components (used in multiple fields)
  obtain ⟨Cg, Kg, hCg⟩ := hGradBound
  -- Extract hIBP_f_dg: used for both hLandauIBP_f_dg and hFubini_outer
  have hIBP_f_dg : ∀ x i, Integrable (fun v =>
      (∫ w, mulVec (landauMatrix coulombKernel (v - w))
        (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) i *
      fderiv ℝ (Real.log ∘ f x) v (Pi.single i 1)) := by
    intro x i
    -- Step 1: Score bound |d(log f)/dv_i| ≤ Cg(1+‖v‖)^Kg
    -- (from chain rule: d(log∘f)/dv_i = (df/dv_i)/f,
    --  and hGradBound gives |df/dv_i| ≤ Cg(1+‖v‖)^Kg * f)
    have h_score : ∀ v, |fderiv ℝ (Real.log ∘ f x) v (Pi.single i 1)| ≤
        Cg * (1 + ‖v‖) ^ Kg := by
      intro v
      have hfv_pos := hf_pos x v
      have hfv_ne : f x v ≠ 0 := ne_of_gt hfv_pos
      have hf_diff : DifferentiableAt ℝ (f x) v :=
        ((hf_smooth_v x).differentiable le_top).differentiableAt
      rw [show Real.log ∘ f x = fun v => Real.log (f x v) from rfl,
          fderiv.log hf_diff hfv_ne]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul,
        abs_of_pos (inv_pos.mpr hfv_pos)]
      rw [inv_mul_le_iff₀ hfv_pos]
      linarith [hCg x v i]
    -- Step 2: Flux component bound
    -- |(∫ w, A(v-w)(f(w)∇f(v) - f(v)∇f(w)))_i| ≤ Cf * f(v) * (1+‖v‖)^Kg
    -- (uses |A(v-w)_{ij}| ≤ ‖v-w‖⁻¹, newtonian_schwartz_uniform_bound, hGradBound)
    have h_flux : ∃ Cf > 0, ∀ v,
        |(∫ w, mulVec (landauMatrix coulombKernel (v - w))
          (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) i| ≤
        Cf * f x v * (1 + ‖v‖) ^ Kg :=
      coulomb_flux_component_bound (f x) (hf_pos x) (hf_smooth_v x)
        (hSchwartz_x x)
        (fun v j => hCg x v j) i
    -- Step 3: Combine → product ≤ Cf*Cg * f(v) * (1+‖v‖)^{2Kg} → integrable
    obtain ⟨Cf, hCf_pos, hCf⟩ := h_flux
    apply ((hSchwartz.integrable_poly_mul hf_smooth_v x (2 * Kg)).const_mul (Cf * Cg)).mono'
    · -- Measurability: score is continuous (smooth log∘f), flux is parametric integral
      have h_score_meas : AEStronglyMeasurable
          (fun v => fderiv ℝ (Real.log ∘ f x) v (Pi.single i 1)) volume :=
        ((ContDiff.log (hf_smooth_v x) (fun v => ne_of_gt (hf_pos x v))).continuous_fderiv le_top
          |>.clm_apply continuous_const).aestronglyMeasurable
      exact AEStronglyMeasurable.mul
        (flux_component_aestronglyMeasurable (f x) (hf_smooth_v x)
          (fun v => landau_flux_integrable_coulomb (f x) (hf_pos x) (hf_smooth_v x)
            (hSchwartz_x x) v) i)
        h_score_meas
    · filter_upwards with v
      rw [Real.norm_eq_abs, abs_mul]
      have hCf_nn : (0 : ℝ) ≤ Cf * f x v * (1 + ‖v‖) ^ Kg :=
        mul_nonneg (mul_nonneg (le_of_lt hCf_pos) (le_of_lt (hf_pos x v)))
          (pow_nonneg (by linarith [norm_nonneg v]) _)
      calc |(∫ w, mulVec (landauMatrix coulombKernel (v - w))
              (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) i| *
            |fderiv ℝ (Real.log ∘ f x) v (Pi.single i 1)|
          ≤ (Cf * f x v * (1 + ‖v‖) ^ Kg) * (Cg * (1 + ‖v‖) ^ Kg) :=
            mul_le_mul (hCf v) (h_score v) (abs_nonneg _) hCf_nn
        _ = Cf * Cg * ((1 + ‖v‖) ^ (2 * Kg) * f x v) := by
            rw [show 2 * Kg = Kg + Kg from by omega, pow_add]; ring
  -- Extract hFluxInt for reuse
  have hFluxInt : ∀ x v, Integrable (fun w =>
      mulVec (landauMatrix coulombKernel (v - w))
        (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) := fun x v =>
    landau_flux_integrable_coulomb (f x) (hf_pos x) (hf_smooth_v x)
      (hSchwartz_x x) v
  have hDecay : VelocityDecayConditions coulombKernel f E B := {
    hPSD_inner_int := fun x v =>
      psd_inner_integrable_coulomb (f x) (hf_pos x) (hf_smooth_v x)
        (hSchwartz_x x) (fun v j => hCg x v j) v
    hPSD_outer_int := fun x =>
      psd_outer_integrable_coulomb (f x) (hf_pos x) (hf_smooth_v x)
        (hSchwartz_x x) (fun v j => hCg x v j)
    hFubini_double := fun x =>
      fubini_double_integrable_coulomb (f x) (hf_pos x) (hf_smooth_v x)
        (hSchwartz_x x) (fun v j => hCg x v j)
    hFubini_inner := by
      intro x v
      simp only [dotProduct]
      exact integrable_finset_sum _ fun i _ =>
        ((integrable_pi_iff.mp (hFluxInt x v) i).const_mul _)
    hFubini_outer := by
      intro x
      -- Step 1: pull dotProduct through ∫_w (score(v) is constant in w)
      have h_eq : ∀ v, (∫ w, dotProduct (vGrad (Real.log ∘ f x) v)
          (mulVec (landauMatrix coulombKernel (v - w))
            (f x w • vGrad (f x) v - f x v • vGrad (f x) w))) =
        dotProduct (vGrad (Real.log ∘ f x) v)
          (∫ w, mulVec (landauMatrix coulombKernel (v - w))
            (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) := by
        intro v
        simp only [dotProduct]
        rw [integral_finset_sum _ (fun i _ => ((hFluxInt x v).eval i).const_mul _)]
        congr 1; ext i
        rw [eval_integral (fun i => (hFluxInt x v).eval i), integral_const_mul]
      simp_rw [h_eq]
      -- Step 2: dotProduct score flux = ∑ i, score_i * flux_i, each integrable by hIBP_f_dg
      simp only [dotProduct, Fin.sum_univ_three, vGrad]
      have h := fun i => (hIBP_f_dg x i).congr (Filter.Eventually.of_forall
        fun v => show _ = _ from mul_comm _ _)
      exact (h 0).add (h 1) |>.add (h 2)
    hSpatialTransport_int := fun x =>
      spatial_transport_integrable hf_pos hf_smooth_v hf_smooth_x hSchwartz hLogBound x
    hForceTransport_int := fun x =>
      force_transport_integrable_coulomb E B hf_pos hf_smooth_v hSchwartz hLogBound x
    hLandauFluxDiff := by
      intro x i
      exact coulomb_flux_differentiable (f x) (hf_pos x) (hf_smooth_v x)
        (hSchwartz_x x) i
    hLandauIBP_df_g := by
      obtain ⟨C_log, K_log, hLB⟩ := hLogBound
      intro x i
      exact coulomb_ibp_df_g_integrable (f x) (hf_pos x) (hf_smooth_v x)
        (hSchwartz_x x)
        ⟨C_log, K_log, fun v => hLB x v⟩ i
    hLandauIBP_f_dg := hIBP_f_dg
    hLandauIBP_fg := fun x i =>
      flux_times_log_integrable_coulomb hf_pos hf_smooth_v hSchwartz hLogBound x i
    hLandauFluxInt := hFluxInt
    hForceIBP_f_dg := fun x i =>
      force_ibp_f_dg_integrable_coulomb E B hf_pos hf_smooth_v hSchwartz hLogBound x i
    hForceIBP_fg := fun x i =>
      force_ibp_fg_integrable_coulomb E B hf_pos hf_smooth_v hSchwartz hLogBound x i
    hSpatialTransport_joint :=
      spatial_transport_joint_integrable hf_pos hf_smooth_v hf_smooth_x hSchwartz hLogBound
    hSpatTransComp := by
      intro v i
      have hDiff_fv : FlatTorus3.IsSpatiallyDiff (fun x => f x v) := hf_smooth_x v
      have hcont_grad := FlatTorus3.hDiff_continuous _ (FlatTorus3.hDiff_grad _ i hDiff_fv)
      have hcont_log := FlatTorus3.hDiff_continuous _
        (FlatTorus3.hDiff_log _ hDiff_fv (fun x => hf_pos x v))
      exact (hcont_grad.mul hcont_log).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    hf_velocity_dominated := by
      obtain ⟨C, hC_pos, hbound⟩ := hSchwartz.hDecay 4 0
      refine ⟨fun v => C / (1 + ‖v‖) ^ 4, inverse_poly_integrable C, fun x v => ?_⟩
      have hb := hbound x v
      simp at hb
      have hv_pos : (0 : ℝ) < (1 + ‖v‖) ^ 4 := by positivity
      rw [abs_of_pos (hf_pos x v)] at hb
      rwa [le_div_iff₀ hv_pos]
    -- PSD continuity: the key Coulomb-specific condition.
    -- Despite Ψ(r) = r⁻³ being singular, the PSD integrand is continuous
    -- because the score difference Δ = O(|v-w|) cancels the singularity.
    hPSD_cont := fun x => psd_continuous_coulomb (f x) (hf_pos x) (hf_smooth_v x)
    hD_cont := by
      -- Express D(f x) using Vlasov: force transport vanishes, so D = ν⁻¹ * ∫ spatial*log
      obtain ⟨C_log, K_log, hLB⟩ := hLogBound
      have hLB' : ∃ C K, ∀ x v, |Real.log (f x v)| ≤ C * (1 + ‖v‖) ^ K :=
        ⟨C_log, K_log, hLB⟩
      have hST_int := fun x =>
        spatial_transport_integrable hf_pos hf_smooth_v hf_smooth_x hSchwartz hLB' x
      have hFT_int := fun x =>
        force_transport_integrable_coulomb E B hf_pos hf_smooth_v hSchwartz hLB' x
      -- Key identity: ν * D(f x) = ∫ spatial * log f
      have h_key : ∀ x, ν * entropyDissipation coulombKernel (f x) =
          ∫ v, v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v) := by
        intro x
        unfold entropyDissipation
        rw [← integral_mul_left]
        have hrw : (fun v => ν * (LandauOperator coulombKernel (f x) v * Real.log (f x v))) =
            (fun v => v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v) +
              (E x + cross v (B x)) ⬝ᵥ vGrad (f x) v * Real.log (f x v)) := by
          ext v; have hV := hVlasov x v
          have : ν * (LandauOperator coulombKernel (f x) v * Real.log (f x v)) =
              (ν * LandauOperator coulombKernel (f x) v) * Real.log (f x v) := by ring
          rw [this, ← hV]
          have : v ⬝ᵥ torusGradX (fun y => f y v) x =
              v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x := rfl
          rw [this]; ring
        rw [hrw, integral_add (hST_int x) (hFT_int x)]
        rw [force_transport_zero (f x) (E x) (B x) (hf_pos x) (hf_smooth_v x)
          ((hSchwartz.integrable hf_smooth_v) x)
          (fun i => force_ibp_f_dg_integrable_coulomb E B hf_pos hf_smooth_v hSchwartz hLB' x i)
          (fun i => force_ibp_fg_integrable_coulomb E B hf_pos hf_smooth_v hSchwartz hLB' x i)]
        simp [add_zero]
      -- So D(f x) = ν⁻¹ * ∫ spatial * log f
      have h_eq : (fun x => entropyDissipation coulombKernel (f x)) =
          (fun x => ν⁻¹ * ∫ v, v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x *
            Real.log (f x v)) := by
        ext x
        have := h_key x
        field_simp at this ⊢
        linarith
      rw [h_eq]
      exact continuous_const.mul
        (spatial_transport_continuous hf_pos hf_smooth_v hf_smooth_x hSchwartz hLB')
  }
  exact Theorem42 f E B coulombKernel ν ρ_ion
    hν hρ_ion coulombKernel_pos hf_pos (fun x => (hf_smooth_v x).of_le le_top)
    (hSchwartz.integrable hf_smooth_v)
    hAmpere hGauss hDivB hB_smooth hVlasov hf_smooth_x hDecay

/-- The equilibrium temperature T_eq is unique: any two temperatures giving the
    same Maxwellian with the same density must be equal. This follows from
    `CoulombConcreteTheorem42` and the injectivity of T ↦ equilibriumMaxwellian ρ T`. -/
theorem CoulombConcreteTheorem42_unique_T
    (f : Torus3 → (Fin 3 → ℝ) → ℝ) (E B : Torus3 → Fin 3 → ℝ) (ν ρ_ion : ℝ)
    (hν : 0 < ν) (hρ_ion : 0 < ρ_ion) (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth_v : ∀ x, ContDiff ℝ ⊤ (f x))
    (hf_smooth_x : ∀ v, ContDiff ℝ ⊤ (periodicLift (fun x => f x v)))
    (hB_smooth : ∀ i, ContDiff ℝ ⊤ (periodicLift (fun x => B x i)))
    (hSchwartz : UniformSchwartzDecay f)
    (hExpDecay : ∃ (C : ℝ) (K : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      Real.exp (-C * (1 + ‖v‖) ^ K) ≤ f x v)
    (hGradBound : ∃ (Cg : ℝ) (Kg : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ) (i : Fin 3),
      |fderiv ℝ (f x) v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * f x v)
    (hVlasov : ∀ x v,
      dotProduct v (torusGradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator coulombKernel (f x) v)
    (hAmpere : ∀ x, torusCurlX B x = fun i => ∫ v, v i * f x v)
    (hGauss : ∀ x, torusDivX E x = (∫ v, f x v) - ρ_ion)
    (hDivB : ∀ x, torusDivX B x = 0) :
    ∃ (T_eq : ℝ) (B₀ : Fin 3 → ℝ), 0 < T_eq ∧
    (∀ x v, f x v = equilibriumMaxwellian ρ_ion T_eq v) ∧
    (∀ x, E x = 0) ∧ (∀ x, B x = B₀) ∧
    (∀ T', 0 < T' → (∀ v, equilibriumMaxwellian ρ_ion T' v = equilibriumMaxwellian ρ_ion T_eq v) →
      T' = T_eq) := by
  obtain ⟨T_eq, B₀, hT_pos, hf_eq, hE_zero, hB_const⟩ :=
    CoulombConcreteTheorem42 f E B ν ρ_ion hν hρ_ion hf_pos hf_smooth_v hf_smooth_x hB_smooth
      hSchwartz hExpDecay hGradBound hVlasov hAmpere hGauss hDivB
  exact ⟨T_eq, B₀, hT_pos, hf_eq, hE_zero, hB_const,
    fun T' hT' h_eq => equilibriumMaxwellian_T_unique ρ_ion T' T_eq hρ_ion hT' hT_pos h_eq⟩

/-- The directional derivative of the equilibrium Maxwellian:
    ∂(eM)/∂vᵢ = -(vᵢ/T) · eM(v).
    Proof: eM = C · exp(-normSq/(2T)), chain rule gives
    fderiv(eM) v eᵢ = C · exp(…) · (-2vᵢ/(2T)) = eM(v) · (-vᵢ/T). -/
private lemma fderiv_equilibriumMaxwellian (ρ T : ℝ) (hT : 0 < T) (v : Fin 3 → ℝ) (i : Fin 3) :
    fderiv ℝ (equilibriumMaxwellian ρ T) v (Pi.single i 1) =
    -(v i / T) * equilibriumMaxwellian ρ T v := by
  simp [equilibriumMaxwellian, normSq, dotProduct]; ring

/-- Exponential decay lower bound for equilibrium Maxwellian:
    exp(-C(1+‖v‖)²) ≤ eM(v) for suitable C. Uses normSq v ≤ 3(1+‖v‖)² (sup norm). -/
private lemma equilibriumMaxwellian_exp_lower_bound (ρ T : ℝ) (hρ : 0 < ρ) (hT : 0 < T) :
    ∃ (C : ℝ) (K : ℕ), ∀ v : Fin 3 → ℝ,
    Real.exp (-C * (1 + ‖v‖) ^ (K : ℕ)) ≤ equilibriumMaxwellian ρ T v := by
  have hpf : 0 < ρ / (2 * π * T) ^ ((3 : ℝ) / 2) :=
    div_pos hρ (rpow_pos_of_pos (by positivity) _)
  refine ⟨3 / (2 * T) + max 0 (-Real.log (ρ / (2 * π * T) ^ ((3:ℝ)/2))), 2, fun v => ?_⟩
  unfold equilibriumMaxwellian
  set pf := ρ / (2 * π * T) ^ ((3 : ℝ) / 2)
  set M := max (0 : ℝ) (-Real.log pf)
  -- Key: normSq v ≤ 3(1+‖v‖)²
  have h_normSq : normSq v ≤ 3 * (1 + ‖v‖) ^ 2 := by
    unfold normSq dotProduct; simp only [Fin.sum_univ_three]
    have h : ∀ j : Fin 3, v j * v j ≤ ‖v‖ * ‖v‖ := fun j => by
      have : |v j| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v j
      calc v j * v j = |v j| * |v j| := (abs_mul_abs_self _).symm
        _ ≤ ‖v‖ * ‖v‖ := mul_self_le_mul_self (abs_nonneg _) this
    nlinarith [h 0, h 1, h 2, norm_nonneg v]
  have h_s1 : (1 : ℝ) ≤ (1 + ‖v‖) ^ 2 := by nlinarith [norm_nonneg v]
  have hM_nn : 0 ≤ M := le_max_left 0 _
  -- Factor: exp(-(3/(2T)+M)*s) = exp(-M*s) * exp(-3s/(2T))
  have h_split : -(3 / (2 * T) + M) * (1 + ‖v‖) ^ 2 =
      -M * (1 + ‖v‖) ^ 2 + -(3 * (1 + ‖v‖) ^ 2 / (2 * T)) := by ring
  rw [h_split, Real.exp_add]
  apply mul_le_mul
  -- exp(-M*s) ≤ pf: from M ≥ -log(pf) and s ≥ 1
  · rw [← Real.exp_log hpf]
    exact Real.exp_le_exp.mpr
      (by nlinarith [le_max_right (0:ℝ) (-Real.log pf), le_mul_of_one_le_right hM_nn h_s1])
  -- exp(-3s/(2T)) ≤ exp(-normSq/(2T)): from normSq ≤ 3s
  · apply Real.exp_le_exp.mpr
    linarith [div_le_div_of_nonneg_right h_normSq (show (0:ℝ) ≤ 2 * T by linarith)]
  · exact Real.exp_nonneg _
  · exact Real.exp_nonneg _

/-- Bound x^M * exp(-ax) ≤ M!/a^M via the Taylor expansion of exp. -/
private lemma pow_mul_exp_neg_le (M : ℕ) (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : 0 ≤ x) :
    x ^ M * Real.exp (-a * x) ≤ M.factorial / a ^ M := by
  have hax : 0 ≤ a * x := mul_nonneg ha.le hx
  have h1 : (a * x) ^ M / M.factorial ≤ Real.exp (a * x) := by
    have := Real.sum_le_exp_of_nonneg hax (M + 1)
    calc (a * x) ^ M / ↑M.factorial
        = ∑ i ∈ Finset.range (M + 1),
            if i = M then (a * x) ^ i / ↑i.factorial else 0 := by
          simp [Finset.sum_ite_eq']
      _ ≤ ∑ i ∈ Finset.range (M + 1), (a * x) ^ i / ↑i.factorial := by
          gcongr with i hi; split_ifs with h
          · exact le_refl _
          · exact div_nonneg (pow_nonneg hax _) (Nat.cast_nonneg _)
      _ ≤ Real.exp (a * x) := this
  have h2 : (a * x) ^ M ≤ M.factorial * Real.exp (a * x) := by
    have := (div_le_iff₀ (Nat.cast_pos.mpr M.factorial_pos)).mp h1; linarith
  have h3 : x ^ M * Real.exp (-a * x) * a ^ M ≤ M.factorial := by
    calc x ^ M * Real.exp (-a * x) * a ^ M
        = (a * x) ^ M * Real.exp (-a * x) := by rw [mul_pow]; ring
      _ ≤ M.factorial * Real.exp (a * x) * Real.exp (-a * x) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
      _ = M.factorial * (Real.exp (a * x) * Real.exp (-a * x)) := by ring
      _ = M.factorial * Real.exp (a * x + (-a * x)) := by rw [← Real.exp_add]
      _ = M.factorial := by simp
  rwa [le_div_iff₀ (pow_pos ha M)]

/-- Polynomial times Gaussian is bounded: (1+u)^M * exp(-au²) ≤ C for all u ≥ 0. -/
private lemma poly_mul_gaussian_le (M : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 ≤ u → (1 + u) ^ M * Real.exp (-a * u ^ 2) ≤ C := by
  refine ⟨2 ^ M * (1 + M.factorial / a ^ M), by positivity, fun u hu => ?_⟩
  by_cases h : u ≤ 1
  · calc (1 + u) ^ M * Real.exp (-a * u ^ 2)
        ≤ 2 ^ M * 1 := by
          apply mul_le_mul
          · exact pow_le_pow_left₀ (by linarith) (by linarith) M
          · rw [← Real.exp_zero]; exact Real.exp_le_exp_of_le (by nlinarith)
          · exact Real.exp_nonneg _
          · positivity
      _ ≤ 2 ^ M * (1 + M.factorial / a ^ M) := by
          gcongr
          linarith [div_nonneg (Nat.cast_nonneg M.factorial) (pow_nonneg ha.le M)]
  · push_neg at h
    have hu1 : 1 ≤ u := h.le
    have h_sq : u ≤ u ^ 2 := le_self_pow₀ hu1 two_ne_zero
    calc (1 + u) ^ M * Real.exp (-a * u ^ 2)
        ≤ (2 * u) ^ M * Real.exp (-a * u) := by
          apply mul_le_mul
          · exact pow_le_pow_left₀ (by linarith) (by linarith) M
          · exact Real.exp_le_exp_of_le (by nlinarith)
          · exact Real.exp_nonneg _
          · positivity
      _ = 2 ^ M * (u ^ M * Real.exp (-a * u)) := by ring_nf
      _ ≤ 2 ^ M * (M.factorial / a ^ M) := by
          gcongr; exact pow_mul_exp_neg_le M a ha u hu
      _ ≤ 2 ^ M * (1 + M.factorial / a ^ M) := by gcongr; linarith

/-- The equilibrium Maxwellian has Schwartz decay: all iterated velocity derivatives
    decay faster than any polynomial. Uses `norm_iteratedFDeriv_comp_le` (Faà di Bruno bound)
    with exp(q(v)) where q = -normSq/(2T) is quadratic, combined with the
    polynomial-times-Gaussian bound. -/
private lemma equilibriumMaxwellian_schwartz_decay (ρ T : ℝ) (hρ : 0 < ρ) (hT : 0 < T) :
    ∀ (N k : ℕ), ∃ C > 0, ∀ (v : Fin 3 → ℝ),
      ‖iteratedFDeriv ℝ k (equilibriumMaxwellian ρ T) v‖ * (1 + ‖v‖) ^ N ≤ C := by
  intro N k
  set pf := ρ / (2 * π * T) ^ ((3 : ℝ) / 2)
  set q := fun v : Fin 3 → ℝ => -(normSq v) / (2 * T)
  have hpf_pos : 0 < pf := div_pos hρ (rpow_pos_of_pos (by positivity) _)
  have hq_smooth : ContDiff ℝ ⊤ q := contDiff_negNormSq_div T
  have hexpq_smooth : ContDiff ℝ ⊤ (Real.exp ∘ q) := contDiff_exp.comp hq_smooth
  have heM_eq : equilibriumMaxwellian ρ T = fun v => pf * (Real.exp ∘ q) v := by
    ext w
    unfold equilibriumMaxwellian
    rfl
  -- Step 1: Pull constant pf out of iteratedFDeriv
  have h_norm : ∀ v, ‖iteratedFDeriv ℝ k (equilibriumMaxwellian ρ T) v‖ =
      pf * ‖iteratedFDeriv ℝ k (Real.exp ∘ q) v‖ := by
    intro v
    rw [heM_eq, show (fun v => pf * (Real.exp ∘ q) v) = pf • (Real.exp ∘ q) from by
      ext w; simp [Pi.smul_apply, smul_eq_mul]]
    rw [iteratedFDeriv_const_smul_apply (hexpq_smooth.contDiffAt.of_le le_top)]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpf_pos]
  -- Step 2: Derivative bound for q (quadratic form)
  obtain ⟨c, hc_pos, hc⟩ := quadratic_iteratedFDeriv_bound T hT k
  -- Step 3: Apply norm_iteratedFDeriv_comp_le (Faà di Bruno)
  have h_comp_bound : ∀ v, ‖iteratedFDeriv ℝ k (Real.exp ∘ q) v‖ ≤
      k.factorial * Real.exp (q v) * (c * (1 + ‖v‖)) ^ k := by
    intro v
    apply norm_iteratedFDeriv_comp_le contDiff_exp hq_smooth le_top v
    · -- exp derivatives: ‖iteratedFDeriv i exp y‖ = exp(y)
      intro i _
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        show Real.exp = fun s => Real.exp (1 * s) from by ext s; simp,
        iteratedDeriv_exp_const_mul]
      simp only [one_pow, one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact le_refl _
    · exact fun i hi1 hi2 => hc v i hi1 hi2
  -- Step 4: q(v) ≤ -‖v‖²/(2T) since normSq v ≥ ‖v‖²
  have h_q_ub : ∀ v, q v ≤ -(1/(2*T)) * ‖v‖ ^ 2 := by
    intro v; simp only [q]
    rw [show -(1 / (2 * T)) * ‖v‖ ^ 2 = -(‖v‖ ^ 2 / (2 * T)) from by ring, neg_div]
    exact neg_le_neg
      (div_le_div_of_nonneg_right (norm_sq_le_normSq v) (by positivity : (0:ℝ) ≤ 2*T))
  -- Step 5: Polynomial × Gaussian bound
  obtain ⟨Cg, hCg_pos, hCg⟩ := poly_mul_gaussian_le (k + N) (1/(2*T)) (by positivity)
  refine ⟨pf * k.factorial * c ^ k * Cg, by positivity, fun v => ?_⟩
  have hv_nn : 0 ≤ 1 + ‖v‖ := by linarith [norm_nonneg v]
  rw [h_norm v]
  -- Chain the inequalities
  have step1 : pf * ‖iteratedFDeriv ℝ k (Real.exp ∘ q) v‖ * (1 + ‖v‖) ^ N ≤
      pf * (k.factorial * Real.exp (q v) * (c * (1 + ‖v‖)) ^ k) * (1 + ‖v‖) ^ N := by
    gcongr; exact h_comp_bound v
  have step2 : pf * (k.factorial * Real.exp (q v) * (c * (1 + ‖v‖)) ^ k) *
      (1 + ‖v‖) ^ N =
      pf * k.factorial * c ^ k * (Real.exp (q v) * (1 + ‖v‖) ^ (k + N)) := by
    rw [mul_pow]; ring
  have step3 : Real.exp (q v) * (1 + ‖v‖) ^ (k + N) ≤
      (1 + ‖v‖) ^ (k + N) * Real.exp (-(1/(2*T)) * ‖v‖ ^ 2) :=
    calc Real.exp (q v) * (1 + ‖v‖) ^ (k + N)
        ≤ Real.exp (-(1/(2*T)) * ‖v‖ ^ 2) * (1 + ‖v‖) ^ (k + N) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp_of_le (h_q_ub v)) (pow_nonneg hv_nn _)
      _ = (1 + ‖v‖) ^ (k + N) * Real.exp (-(1/(2*T)) * ‖v‖ ^ 2) := by ring
  have step4 : (1 + ‖v‖) ^ (k + N) * Real.exp (-(1/(2*T)) * ‖v‖ ^ 2) ≤ Cg :=
    hCg ‖v‖ (norm_nonneg v)
  linarith [mul_le_mul_of_nonneg_left (le_trans step3 step4)
    (by positivity : (0:ℝ) ≤ pf * k.factorial * c ^ k)]

/-- **Non-vacuousness of CoulombConcreteTheorem42.**

    The equilibrium Maxwellian f(v) = ρ/(2πT)^{3/2} exp(-|v|²/(2T)) with
    E = 0, B = 0 satisfies all 13 hypotheses of the main theorem. This
    proves the theorem is non-vacuous: at least one instance exists.

    **Proof status: all 10 non-trivial goals fully proved. 0 sorry's.**

    Why each hypothesis holds for the equilibrium:
    - (3) hf_pos: ρ/(2πT)^{3/2} > 0 and exp > 0 ⇒ f > 0  ✓
    - (4) hf_smooth_v: composition of smooth functions (const, exp, polynomial)  ✓
    - (5) hf_smooth_x: f is spatially constant ⇒ periodicLift is constant ⇒ C^∞  ✓
    - (6) hB_smooth: B = 0, same argument as (5)  ✓
    - (7) hSchwartz: Gaussian is Schwartz class via Faà di Bruno + poly×Gaussian bound  ✓
    - (8) hExpDecay: normSq v ≤ 3(1+‖v‖)², choose C = 3/(2T)+max(0,-log prefix)  ✓
    - (9) hGradBound: ∂eM/∂vᵢ = -(vᵢ/T)·eM, bound |vᵢ| ≤ 1+‖v‖  ✓
    - (10) hVlasov: A(z)·z = 0 (projection annihilation) ⇒ integrand vanishes  ✓
    - (11) hAmpere: ∇×0 = 0, ∫ vᵢ eM dv = 0 by odd symmetry  ✓
    - (12) hGauss: ∇·0 = 0 = ∫eM - ρ_ion (simp closes)  ✓
    - (13) hDivB: ∇·0 = 0  ✓ -/
theorem CoulombConcreteTheorem42_nonvacuous (ν T ρ_ion : ℝ)
    (hν : 0 < ν) (hT : 0 < T) (hρ_ion : 0 < ρ_ion) :
    ∃ (f : Torus3 → (Fin 3 → ℝ) → ℝ) (E B : Torus3 → Fin 3 → ℝ),
    (∀ x v, 0 < f x v) ∧                                                  -- (3)
    (∀ x, ContDiff ℝ ⊤ (f x)) ∧                                           -- (4)
    (∀ v, ContDiff ℝ ⊤ (periodicLift (fun x => f x v))) ∧                 -- (5)
    (∀ i, ContDiff ℝ ⊤ (periodicLift (fun x => B x i))) ∧                 -- (6)
    UniformSchwartzDecay f ∧                                                -- (7)
    (∃ C K, ∀ x v, Real.exp (-C * (1 + ‖v‖) ^ K) ≤ f x v) ∧             -- (8)
    (∃ Cg Kg, ∀ x v i,
      |fderiv ℝ (f x) v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * f x v) ∧ -- (9)
    (∀ x v, dotProduct v (torusGradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator coulombKernel (f x) v) ∧                         -- (10)
    (∀ x, torusCurlX B x = fun i => ∫ v, v i * f x v) ∧                  -- (11)
    (∀ x, torusDivX E x = (∫ v, f x v) - ρ_ion) ∧                        -- (12)
    (∀ x, torusDivX B x = 0) := by                                        -- (13)
  refine ⟨fun _ => equilibriumMaxwellian ρ_ion T,
         fun _ => 0, fun _ => 0,
         fun _ v => equilibriumMaxwellian_pos ρ_ion T hρ_ion hT v,  -- (3) ✓
         ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (4) hf_smooth_v: equilibriumMaxwellian is C^∞
  · intro _
    unfold equilibriumMaxwellian
    apply ContDiff.mul contDiff_const
    apply ContDiff.exp
    apply ContDiff.div_const
    apply ContDiff.neg
    unfold normSq dotProduct
    exact ContDiff.sum fun i _ =>
      (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)
  -- (5) hf_smooth_x: periodicLift of constant is C^∞
  · intro v
    simp only [periodicLift, Function.comp]
    exact contDiff_const
  -- (6) hB_smooth: periodicLift of zero is C^∞
  · intro i
    simp only [periodicLift, Function.comp, Pi.zero_apply]
    exact contDiff_const
  -- (7) hSchwartz: Gaussian is UniformSchwartzDecay
  · constructor
    · -- hDecay: ‖iteratedFDeriv ℝ k eM v‖ * (1+‖v‖)^N ≤ C
      intro N k
      obtain ⟨C, hC, hbound⟩ :=
        equilibriumMaxwellian_schwartz_decay ρ_ion T hρ_ion hT N k
      exact ⟨C, hC, fun _ v => hbound v⟩
    · -- hGradDecay: spatial gradient of constant function is 0
      intro N i
      refine ⟨1, one_pos, fun x v => ?_⟩
      simp only [torusGradX, periodicLift, Function.comp]
      simp [fderiv_const, ContinuousLinearMap.zero_apply, mul_comm]
  -- (8) hExpDecay: exponential decay bound
  · obtain ⟨C, K, hCK⟩ := equilibriumMaxwellian_exp_lower_bound ρ_ion T hρ_ion hT
    exact ⟨C, K, fun _ => hCK⟩
  -- (9) hGradBound: |∂eM/∂vᵢ| = |vᵢ/T| · eM ≤ (1+‖v‖)/T · eM
  · refine ⟨1 / T, 1, fun _ v i => ?_⟩
    rw [fderiv_equilibriumMaxwellian ρ_ion T hT v i]
    have hpos := equilibriumMaxwellian_pos ρ_ion T hρ_ion hT v
    rw [abs_neg, abs_mul, abs_div, abs_of_pos hT, abs_of_pos hpos, pow_one]
    have hvi : |v i| ≤ 1 + ‖v‖ :=
      le_trans (norm_le_pi_norm v i) (le_add_of_nonneg_left one_nonneg)
    calc |v i| / T * equilibriumMaxwellian ρ_ion T v
        ≤ (1 + ‖v‖) / T * equilibriumMaxwellian ρ_ion T v := by
          apply mul_le_mul_of_nonneg_right
          · exact div_le_div_of_nonneg_right hvi hT
          · exact hpos.le
      _ = 1 / T * (1 + ‖v‖) * equilibriumMaxwellian ρ_ion T v := by ring
  -- (10) hVlasov: Vlasov equation (Maxwellian in kernel of Landau operator)
  · intro x v
    -- LHS: spatial gradient of constant is 0, E=B=0 so force term is 0
    simp only [torusGradX, periodicLift, Function.comp, Pi.zero_apply]
    simp only [fderiv_const, ContinuousLinearMap.zero_apply, dotProduct_zero, cross,
      mul_zero, sub_zero, zero_mul, sub_self, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, zero_add]
    -- RHS: LandauOperator eM v = 0 because integrand vanishes
    suffices h : LandauOperator coulombKernel (equilibriumMaxwellian ρ_ion T) v = 0 by
      simp [h]
    -- The integrand is 0 for all w: A(v-w) · (eM(w)·∇eM(v) - eM(v)·∇eM(w)) = 0
    -- because the vector argument is proportional to (v-w) and A(z)·z = 0
    unfold LandauOperator vDiv
    simp only [Pi.single_eq_same]
    -- Show the flux function is identically 0
    have hflux_zero : ∀ v', (∫ w, mulVec (landauMatrix coulombKernel (v' - w))
        (equilibriumMaxwellian ρ_ion T w • vGrad (equilibriumMaxwellian ρ_ion T) v' -
         equilibriumMaxwellian ρ_ion T v' • vGrad (equilibriumMaxwellian ρ_ion T) w)) = 0 := by
      intro v'
      -- Show integrand is 0 pointwise
      have h_integrand : ∀ w, mulVec (landauMatrix coulombKernel (v' - w))
          (equilibriumMaxwellian ρ_ion T w • vGrad (equilibriumMaxwellian ρ_ion T) v' -
           equilibriumMaxwellian ρ_ion T v' • vGrad (equilibriumMaxwellian ρ_ion T) w) = 0 := by
        intro w
        -- The bracket vector = (-eM(v')*eM(w)/T) • (v' - w)
        have hbracket : equilibriumMaxwellian ρ_ion T w • vGrad (equilibriumMaxwellian ρ_ion T) v' -
            equilibriumMaxwellian ρ_ion T v' • vGrad (equilibriumMaxwellian ρ_ion T) w =
            (-(equilibriumMaxwellian ρ_ion T v' * equilibriumMaxwellian ρ_ion T w / T)) •
              (v' - w) := by
          ext i
          simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, vGrad,
            fderiv_equilibriumMaxwellian ρ_ion T hT v' i,
            fderiv_equilibriumMaxwellian ρ_ion T hT w i]
          ring
        rw [hbracket, Matrix.mulVec_smul_assoc, landauMatrix_mulVec_self, smul_zero]
      simp [h_integrand]
    -- vDiv of zero function = 0
    have : ∀ i, fderiv ℝ (fun w => (0 : Fin 3 → ℝ) i) v (Pi.single i 1) = 0 := by
      intro i; simp [fderiv_const]
    conv => arg 2; rw [show (0:ℝ) = ν * 0 from by ring]
    congr 1
    simp only [hflux_zero]
    simp [fderiv_const, ContinuousLinearMap.zero_apply]
  -- (11) hAmpere: Ampere's law (curl 0 = ∫ vᵢ eM dv)
  · intro x
    ext i
    simp only [torusCurlX, periodicLift, Function.comp, Pi.zero_apply,
      fderiv_const, ContinuousLinearMap.zero_apply, sub_self]
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  -- (12) hGauss: Gauss's law
  · intro x
    simp [torusDivX, periodicLift, Function.comp, Pi.zero_apply,
      fderiv_const, ContinuousLinearMap.zero_apply]
  -- (13) hDivB: divergence of B = 0
  · intro x
    simp only [torusDivX, periodicLift, Function.comp, Pi.zero_apply]
    simp [fderiv_const, ContinuousLinearMap.zero_apply]

end VML
