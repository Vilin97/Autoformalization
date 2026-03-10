/-
  Concrete Theorem 42 for Coulomb collisions on T³ = (ℝ/ℤ)³.

  This specializes ConcreteTheorem42 to the physical Coulomb collision kernel
  Ψ(r) = r⁻³, the most important case in plasma physics. The Coulomb kernel
  is singular at r = 0 (NOT continuous), so it cannot satisfy `Continuous Ψ`.

  Key mathematical fact: even though the Landau matrix A(z) = Ψ(|z|)(|z|²I - zz^T)
  diverges as z → 0 for Coulomb, the PSD integrand is continuous because the score
  difference Δ = ∇log f(v) - ∇log f(w) = O(|v-w|) cancels the singularity:
    |PSDIntegrand(v,w)| ≤ C|v-w|^{γ+4} = C|v-w| → 0  (γ = -3).

  We define coulombKernel with value 1 at r ≤ 0 (instead of 0 or ∞) so that
  ∀ r, 0 < coulombKernel r. The value at 0 is irrelevant since
  landauMatrix Ψ 0 = 0 always (the projection |z|²I - zz^T vanishes at z = 0).

  Hypotheses (13 total, 12 independent + 1 likely derivable):
  - 2 physical parameters (ν > 0, ρ_ion > 0)
  - 1 strict positivity (f > 0)
  - 3 smoothness (f smooth in v and x, B smooth)
  - 3 decay (Schwartz in v; stretched-exponential lower bound; polynomial score)
  - 4 equations (Vlasov, Ampère, Gauss, div B = 0)
-/
import Aristotle.Landau.main.CoulombSpatialTransport
import Aristotle.Landau.main.CoulombFlux
import Aristotle.Landau.main.CoulombPSD
import Aristotle.Landau.main.CoulombFluxDiff

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

/-- **Coulomb Theorem 42.** Characterization of smooth steady states of the
    Vlasov–Maxwell–Landau system with Coulomb collisions on T³ = (ℝ/ℤ)³.

    This is the physically most important case: Coulomb interactions between
    charged particles in a plasma. The collision kernel Ψ(r) = r⁻³ is singular
    at r = 0 but the formalization handles this via the PSD continuity condition
    in VelocityDecayConditions (the singularity cancels in the quadratic form).

    **Hypotheses** (13 total, 12 independent + 1 likely derivable):
    - 2 physical parameters (ν > 0, ρ_ion > 0)
    - 1 strict positivity (f > 0)
    - 3 smoothness (f smooth in v and x, B smooth)
    - 3 decay (Schwartz in v; stretched-exponential lower bound; polynomial score)
    - 4 equations (Vlasov, Ampère, Gauss, div B = 0)

    **Non-minimality note:** Hypothesis 9 (hGradBound, polynomial score bound) is
    likely derivable from hypotheses 7-8 (Schwartz decay + stretched-exponential
    lower bound): Schwartz |∂f| decays faster than any polynomial, while the lower
    bound f ≥ exp(-C(1+‖v‖)^K) only decays sub-exponentially, so |∂f|/f grows at
    most polynomially. Formalizing this derivation in Lean is nontrivial, so the
    hypothesis is stated separately. The hypothesis list is not minimal. -/
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
    -- === Polynomial score bound (same as smooth kernel's hGradBound) ===
    -- NOTE: Likely derivable from hSchwartz + hExpDecay (Schwartz numerator /
    -- stretched-exponential denominator → polynomial growth), but proving this
    -- in Lean is nontrivial. Stated separately; the hypothesis list is not minimal.
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
    -- (from chain rule: d(log∘f)/dv_i = (df/dv_i)/f, and hGradBound gives |df/dv_i| ≤ Cg(1+‖v‖)^Kg * f)
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
        intro x; unfold entropyDissipation; rw [← integral_mul_left]
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
        ext x; have := h_key x; field_simp at this ⊢; linarith
      rw [h_eq]
      exact continuous_const.mul
        (spatial_transport_continuous hf_pos hf_smooth_v hf_smooth_x hSchwartz hLB')
  }
  exact Theorem42 f E B coulombKernel ν ρ_ion
    hν hρ_ion coulombKernel_pos hf_pos hf_smooth_v
    (hSchwartz.integrable hf_smooth_v)
    hAmpere hGauss hDivB hB_smooth hVlasov hf_smooth_x hDecay

end VML
