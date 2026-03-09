/-
  Exploration: Extending the VML formalization to Coulomb collisions.

  The current formalization requires:
    (1) Continuous Ψ           -- fails for Coulomb: Ψ(r) = r⁻³ → ∞ at r = 0
    (2) ∀ r, 0 < Ψ r          -- fails for Coulomb at r = 0
    (3) ContDiff ℝ 1 Ψ         -- fails for Coulomb at r = 0
    (4) ∃ C, ∀ r, |Ψ r| ≤ C   -- fails for Coulomb (unbounded)

  The physical Landau collision kernels for inverse-power potentials s ≥ 2:
    Ψ_γ(r) = r^γ,   γ = (s-5)/(s-1)  (in 3D)
    - s = 2 (Coulomb):  γ = -3,  Ψ(r) = r⁻³
    - s = 3:            γ = -1,  Ψ(r) = r⁻¹
    - s = 4:            γ = -1/3
    - s = 5 (Maxwell):  γ = 0,   Ψ(r) = 1
    - s > 5 (hard):     γ > 0,   Ψ(r) = r^γ

  KEY INSIGHT: The Landau matrix A(z) = Ψ(|z|) · (|z|²I - zz^T) has entries
  bounded by 2|z|^{γ+2}. For γ = -3 (Coulomb), entries are O(|z|⁻¹), which
  is LOCALLY INTEGRABLE in ℝ³. The singularity is "soft" enough.

  Moreover, the PSD integrand:
    PSDIntegrand(v,w) = f(v)f(w) · Δ^T A(v-w) Δ
  where Δ = ∇log f(v) - ∇log f(w) = O(|v-w|), satisfies:
    PSDIntegrand(v,w) = O(|v-w|^{γ+4}) near v = w.
  For Coulomb: O(|v-w|) → 0. So the PSD integrand IS CONTINUOUS even
  though the matrix itself is not.

  This file explores three approaches to include Coulomb:
    A. Weaken the abstract theorem hypotheses (minimal change)
    B. Power-law kernel structure (covers all physical cases)
    C. General singular kernel framework
-/
import Aristotle.Landau.main.Defs
import Aristotle.Landau.main.Section2
import Aristotle.Landau.main.Section3

set_option linter.all false
open Matrix Finset BigOperators Real MeasureTheory

noncomputable section
namespace VML

-- ============================================================================
-- Part 0: Analysis of where Ψ hypotheses are actually needed
-- ============================================================================

/-
  AUDIT of `Continuous Ψ` usage in the abstract proof chain:

  The ONLY place `Continuous Ψ` appears in Sections 2-9 is:
    PSDIntegrand_continuous (Section3.lean, line 37)

  All downstream lemmas take `hPSD_cont` as a hypothesis, never `hΨ_cont`.
  So replacing `hΨ_cont : Continuous Ψ` with a direct
    `hPSD_cont : ∀ x, Continuous (fun p => PSDIntegrand Ψ (f x) p.1 p.2)`
  in Theorem42 changes NOTHING in Sections 2-9.

  AUDIT of `∀ r, 0 < Ψ r` usage:
    - `psd_weighted_integral_nonneg`: uses `∀ r, 0 ≤ Ψ r` (weakened)
    - `landauMatrix_quadForm_eq_zero_iff`: uses `0 < Ψ (eucNorm z)` with z ≠ 0
    - `entropy_zero_quadform_zero`: chains the above
    - `D_zero_implies_parallel`, `D_zero_implies_maxwellian`, `nullspace_iff`:
      all use `hΨ (eucNorm (v - w))` guarded by `v ≠ w`, so `eucNorm(v-w) > 0`.

  CONCLUSION: The abstract proof only needs:
    (i)  ∀ r, 0 ≤ Ψ r          (for PSD non-negativity)
    (ii) ∀ r, 0 < r → 0 < Ψ r  (for nullspace characterization, always with z ≠ 0)
  NOT `∀ r, 0 < Ψ r`.
-/


-- ============================================================================
-- Part 1: Power-law kernels and the Coulomb kernel
-- ============================================================================

/-- Power-law Landau collision kernel: Ψ_γ(r) = r^γ for r > 0, extended to 0 at r = 0.
    This covers all inverse-power law interactions:
    - γ = -3: Coulomb
    - γ = -1: inverse-cube
    - γ = 0:  Maxwell molecules
    - γ > 0:  hard potentials -/
def powerLawKernel (γ : ℝ) (r : ℝ) : ℝ :=
  if r ≤ 0 then 0 else r ^ γ

/-- The Coulomb collision kernel: Ψ(r) = r⁻³ for r > 0, 0 at r = 0. -/
def coulombKernel : ℝ → ℝ := powerLawKernel (-3)

-- Basic properties of power-law kernels

lemma powerLawKernel_zero (γ : ℝ) : powerLawKernel γ 0 = 0 := by
  simp [powerLawKernel]

lemma powerLawKernel_pos {γ : ℝ} {r : ℝ} (hr : 0 < r) :
    0 < powerLawKernel γ r := by
  simp [powerLawKernel, not_le.mpr hr]
  exact rpow_pos_of_pos hr γ

lemma powerLawKernel_nonneg (γ : ℝ) (r : ℝ) :
    0 ≤ powerLawKernel γ r := by
  simp only [powerLawKernel]
  split
  · exact le_refl 0
  · exact le_of_lt (rpow_pos_of_pos (by linarith) γ)

/-- For γ ≥ 0, the power-law kernel is continuous everywhere. -/
lemma powerLawKernel_continuous_of_nonneg {γ : ℝ} (hγ : 0 ≤ γ) :
    Continuous (powerLawKernel γ) := by
  sorry -- follows from rpow continuous on [0, ∞) for γ ≥ 0

/-- For γ < 0, the power-law kernel is NOT continuous at 0 (it diverges). -/
lemma powerLawKernel_not_continuous_neg {γ : ℝ} (hγ : γ < 0) :
    ¬ Continuous (powerLawKernel γ) := by
  sorry -- Ψ_γ(r) = r^γ → ∞ as r → 0⁺ for γ < 0, but Ψ_γ(0) = 0

/-- The Coulomb kernel is NOT continuous (γ = -3 < 0). -/
lemma coulombKernel_not_continuous : ¬ Continuous coulombKernel :=
  powerLawKernel_not_continuous_neg (by norm_num : (-3 : ℝ) < 0)


-- ============================================================================
-- Part 2: The Landau matrix entries for power-law kernels
-- ============================================================================

/-
  For Ψ_γ, the Landau matrix entries are:
    A_{ij}(z) = Ψ_γ(|z|) · (|z|²δ_{ij} - z_i z_j)

  Entry bounds:
    |A_{ij}(z)| ≤ 2|z|^{γ+2}

  Key singularity analysis:
    γ = -3 (Coulomb): entries ~ |z|⁻¹, locally integrable in ℝ³ ✓
    γ = -1:           entries ~ |z|¹,  continuous at 0 ✓
    γ = 0  (Maxwell): entries ~ |z|²,  smooth ✓

  The matrix entries are O(|z|^{γ+2}) near z = 0.
  In ℝ³, |z|^α is locally integrable iff α > -3.
  So entries are locally integrable iff γ + 2 > -3, i.e., γ > -5.
  Coulomb (γ = -3) satisfies this. ✓

  CONTINUITY of the matrix at z = 0:
    A_{ij}(z) → 0 as z → 0 iff γ + 2 > 0, i.e., γ > -2.
    For Coulomb (γ = -3): entries diverge at z = 0. ✗
    The matrix function is NOT continuous for Coulomb.

  But the PSD INTEGRAND is continuous (see Part 3).
-/

/-- Bound on Landau matrix entries for power-law kernels.
    |A_{ij}(z)| ≤ 2 · |z|^{γ+2} for z ≠ 0. -/
lemma landauMatrix_entry_bound_powerlaw (γ : ℝ) (z : Fin 3 → ℝ) (hz : z ≠ 0)
    (i j : Fin 3) :
    |landauMatrix (powerLawKernel γ) z i j| ≤ 2 * eucNorm z ^ (γ + 2) := by
  sorry

/-- The Landau matrix at z = 0 is the zero matrix (regardless of Ψ). -/
lemma landauMatrix_at_zero (Ψ : ℝ → ℝ) :
    landauMatrix Ψ (0 : Fin 3 → ℝ) = 0 := by
  ext i j
  simp [landauMatrix, innerLandauMatrix, eucNorm, normSq]

/-- The inner Landau matrix at z = 0 is zero. -/
lemma innerLandauMatrix_zero :
    innerLandauMatrix (0 : Fin 3 → ℝ) = 0 := by
  ext i j
  simp [innerLandauMatrix, normSq]


-- ============================================================================
-- Part 3: PSD integrand continuity for singular kernels
-- ============================================================================

/-
  The PSD integrand near v = w (z = v - w → 0):

    PSDIntegrand(v,w) = f(v)·f(w) · Δᵀ A(z) Δ

  where Δ = ∇log f(v) - ∇log f(w).

  Taylor expansion: Δ = H·z + O(|z|²) where H = ∇²log f(v).

  The quadratic form: Δᵀ A(z) Δ = Ψ(|z|) · [|z|²|Δ|² - (z·Δ)²]

  By Cauchy-Schwarz: |z|²|Δ|² - (z·Δ)² = |z × Δ|² ≥ 0.

  Bound: |z|²|Δ|² - (z·Δ)² ≤ |z|² · |Δ|²

  With Δ = O(|z|) and Ψ(|z|) = |z|^γ:
    |PSDIntegrand(v,w)| ≤ C · |z|^γ · |z|² · |z|² = C · |z|^{γ+4}

  For γ > -4: this → 0 as z → 0. ✓
  For Coulomb (γ = -3): |PSDIntegrand| ≤ C · |z| → 0. ✓

  So the PSD integrand IS CONTINUOUS at the diagonal v = w,
  even though the matrix itself is discontinuous there.

  This is the key mathematical fact that makes the Coulomb extension possible.
-/

/-- For any smooth f > 0, the score difference Δ = ∇log f(v) - ∇log f(w)
    is Lipschitz (hence |Δ| ≤ C|v-w| locally). -/
lemma score_difference_lipschitz (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ ⊤ f)
    (K : Set (Fin 3 → ℝ)) (hK : IsCompact K) :
    ∃ C > 0, ∀ v ∈ K, ∀ w ∈ K,
      ‖vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w‖ ≤ C * ‖v - w‖ := by
  sorry -- follows from ContDiff ℝ ⊤ (log ∘ f), which gives Lipschitz vGrad on compact sets

/-- PSD integrand continuity for power-law kernels with γ > -4.
    The key lemma: even for Coulomb (γ = -3), the PSD integrand is continuous.

    Proof idea: Near the diagonal v = w, the score difference Δ = O(|v-w|),
    so |PSDIntegrand| ≤ C · |v-w|^{γ+4} → 0 for γ > -4.
    Away from the diagonal, continuity follows from continuity of Ψ on (0,∞). -/
lemma PSDIntegrand_continuous_powerlaw (γ : ℝ) (hγ : -4 < γ)
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ ⊤ f) :
    Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      PSDIntegrand (powerLawKernel γ) f p.1 p.2) := by
  sorry
  /-
    Proof sketch:
    1. Off the diagonal {(v,w) | v ≠ w}: standard composition of continuous functions,
       since Ψ_γ is continuous on (0,∞) and all other components are smooth.
    2. On the diagonal {(v,v)}: PSDIntegrand = 0 (score difference = 0).
       Need to show PSDIntegrand(v_n, w_n) → 0 when v_n → v, w_n → v.
       Use the bound: |PSDIntegrand(v_n, w_n)| ≤ C(v) · |v_n - w_n|^{γ+4}
       which → 0 since γ + 4 > 0.
    3. The constant C(v) depends on the Lipschitz constant of ∇log f near v,
       which is locally bounded by smoothness.
  -/


-- ============================================================================
-- Part 4: Approach A — Minimal changes to the abstract theorem
-- ============================================================================

/-
  APPROACH A: Change Theorem42 to not require `Continuous Ψ`.

  Current Theorem42 hypotheses on Ψ:
    (hΨ : ∀ r, 0 < Ψ r)
    (hΨ_cont : Continuous Ψ)

  Proposed replacement:
    (hΨ_nonneg : ∀ r, 0 ≤ Ψ r)
    (hΨ_pos : ∀ r, 0 < r → 0 < Ψ r)
    (hPSD_cont : ∀ x, Continuous (fun p => PSDIntegrand Ψ (f x) p.1 p.2))

  Changes needed:
  1. Theorem42.lean: Replace hypotheses, remove PSDIntegrand_continuous call
  2. Section3.lean: Already works — all lemmas take hPSD_cont, not hΨ_cont
  3. Section2.lean: `landauMatrix_posSemidef` already takes `0 ≤ Ψ(|z|)` ✓
                    `landauMatrix_quadForm_eq_zero_iff` takes `0 < Ψ(|z|)` with z ≠ 0 ✓
  4. Sections 4-9: Never use Ψ properties directly ✓

  This is a STRICTLY WEAKER set of hypotheses. Every Ψ satisfying the old
  hypotheses satisfies the new ones. But now Coulomb also satisfies them!

  The VelocityDecayConditions remain unchanged — they don't mention Continuous Ψ.
  The concrete instances (VelocityDecayInstance.lean) would need new proofs
  for Coulomb, but that's expected.
-/

-- Here we verify that the weakened positivity conditions suffice for the PSD proof chain.

/-- Weakened PSD non-negativity: only needs Ψ ≥ 0 (not Ψ > 0). -/
lemma psd_weighted_integral_nonneg' (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ_nonneg : ∀ r, 0 ≤ Ψ r)  -- weakened from 0 < Ψ r
    (hf_pos : ∀ v, 0 < f v) :
    0 ≤ ∫ v, ∫ w, PSDIntegrand Ψ f v w :=
  -- Exactly psd_weighted_integral_nonneg — it already takes ∀ r, 0 ≤ Ψ r
  psd_weighted_integral_nonneg Ψ f hΨ_nonneg hf_pos

/-- Weakened nullspace: only needs Ψ > 0 for r > 0. The z ≠ 0 guard means
    eucNorm z > 0, so we can use hΨ_pos. -/
lemma landauMatrix_quadForm_zero_of_pos_away (Ψ : ℝ → ℝ)
    (hΨ_pos : ∀ r, 0 < r → 0 < Ψ r)  -- weakened
    (z : Fin 3 → ℝ) (hz : z ≠ 0) (Y : Fin 3 → ℝ)
    (h : dotProduct Y (mulVec (landauMatrix Ψ z) Y) = 0) :
    ∃ l : ℝ, Y = l • z := by
  have henz : 0 < eucNorm z := Real.sqrt_pos_of_pos (normSq_pos hz)
  exact landauMatrix_quadForm_eq_zero_iff (hΨ_pos _ henz) hz Y h


-- ============================================================================
-- Part 5: Approach B — Power-law kernel structure
-- ============================================================================

/-- A power-law Landau kernel is characterized by its exponent γ ∈ (-4, ∞).
    The bound γ > -4 ensures the PSD integrand is continuous. -/
structure PowerLawLandauKernel where
  /-- The power-law exponent. γ = -3 for Coulomb, 0 for Maxwell. -/
  γ : ℝ
  /-- γ > -4 ensures PSD integrand continuity (|v-w|^{γ+4} → 0). -/
  hγ_lower : -4 < γ

/-- Convert a PowerLawLandauKernel to a kernel function Ψ : ℝ → ℝ. -/
def PowerLawLandauKernel.toKernel (k : PowerLawLandauKernel) : ℝ → ℝ :=
  powerLawKernel k.γ

/-- Standard physical kernels. -/
def coulombLandauKernel : PowerLawLandauKernel := ⟨-3, by norm_num⟩
def maxwellLandauKernel : PowerLawLandauKernel := ⟨0, by norm_num⟩

/-- All power-law kernels satisfy the weakened positivity conditions. -/
lemma PowerLawLandauKernel.nonneg (k : PowerLawLandauKernel) (r : ℝ) :
    0 ≤ k.toKernel r :=
  powerLawKernel_nonneg k.γ r

lemma PowerLawLandauKernel.pos (k : PowerLawLandauKernel) (r : ℝ) (hr : 0 < r) :
    0 < k.toKernel r :=
  powerLawKernel_pos hr


-- ============================================================================
-- Part 6: Approach C — General singular kernel framework
-- ============================================================================

/-- A (possibly singular) Landau collision kernel. This generalizes the
    current `Continuous Ψ` + `∀ r, 0 < Ψ r` to allow singularities at r = 0.

    The key requirements are:
    - Ψ ≥ 0 everywhere (for PSD non-negativity of the Landau matrix)
    - Ψ > 0 away from 0 (for the nullspace characterization)
    - The PSD integrand is continuous (for the measure-theoretic argument)
    - Continuity on (0,∞) (for other analytical arguments)

    These are satisfied by:
    - All continuous positive Ψ (current case)
    - Power-law kernels r^γ for γ > -4 (including Coulomb)
    - Regularized kernels Ψ_ε(r) = Ψ(max(r, ε))
    - Debye-screened Coulomb: Ψ(r) = e^{-r/λ_D} / r³ -/
structure LandauKernel (Ψ : ℝ → ℝ) : Prop where
  /-- Ψ is non-negative (for PSD property of the matrix). -/
  hΨ_nonneg : ∀ r, 0 ≤ Ψ r
  /-- Ψ is strictly positive away from r = 0 (for nullspace characterization). -/
  hΨ_pos : ∀ r, 0 < r → 0 < Ψ r
  /-- Ψ is continuous on (0, ∞) (for analytical arguments away from diagonal). -/
  hΨ_cont : ContinuousOn Ψ (Set.Ioi 0)

/-- Every continuous positive Ψ gives a LandauKernel (backwards compatibility). -/
lemma LandauKernel.of_continuous_pos (Ψ : ℝ → ℝ) (hΨ_pos : ∀ r, 0 < Ψ r)
    (hΨ_cont : Continuous Ψ) : LandauKernel Ψ where
  hΨ_nonneg := fun r => le_of_lt (hΨ_pos r)
  hΨ_pos := fun r _ => hΨ_pos r
  hΨ_cont := hΨ_cont.continuousOn

/-- Power-law kernels give LandauKernels. -/
lemma LandauKernel.of_powerlaw (k : PowerLawLandauKernel) :
    LandauKernel k.toKernel where
  hΨ_nonneg := fun r => k.nonneg r
  hΨ_pos := fun r hr => k.pos r hr
  hΨ_cont := by
    intro r hr
    have hr' : 0 < r := Set.mem_Ioi.mp hr
    have hcont : ContinuousAt (fun r => r ^ k.γ) r :=
      continuousAt_rpow_const r k.γ (Or.inl (ne_of_gt hr'))
    apply ContinuousAt.continuousWithinAt
    exact hcont.congr (Filter.eventually_of_mem (Ioi_mem_nhds hr') fun s (hs : 0 < s) => by
      simp [PowerLawLandauKernel.toKernel, powerLawKernel, not_le.mpr hs])


-- ============================================================================
-- Part 7: What a Coulomb-compatible Theorem42 would look like
-- ============================================================================

/-
  PROPOSED GENERALIZED THEOREM42:

  theorem Theorem42_general
    [FlatTorus3 X] (f : X → (Fin 3 → ℝ) → ℝ) (E B : X → Fin 3 → ℝ)
    (Ψ : ℝ → ℝ) (ν ρ_ion : ℝ)
    -- CHANGED: Weakened kernel hypotheses
    (hΨ_nonneg : ∀ r, 0 ≤ Ψ r)                              -- was: ∀ r, 0 < Ψ r
    (hΨ_pos : ∀ r, 0 < r → 0 < Ψ r)                         -- NEW (split from above)
    -- CHANGED: PSD continuity is now a hypothesis, not derived
    (hPSD_cont : ∀ x, Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      PSDIntegrand Ψ (f x) p.1 p.2))                         -- was: derived from Continuous Ψ
    -- Remaining hypotheses unchanged:
    (hν : 0 < ν) (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x))
    (hf_int : ∀ x, Integrable (f x))
    ... -- (all other hypotheses identical)
    :
    ∃ (T_eq : ℝ) (B₀ : Fin 3 → ℝ), 0 < T_eq ∧ ... := by
    sorry

  IMPACT ANALYSIS:
  - Sections 2-9: NO CHANGES needed. They already use hPSD_cont, not hΨ_cont.
  - Theorem42.lean: Change hypothesis list + remove PSDIntegrand_continuous call.
  - VMLInput/VMLSteadyState: Already use hPSD_cont. NO CHANGES.
  - VelocityDecayConditions: NO CHANGES (doesn't mention Continuous Ψ).
  - ConcreteTheorem42: Would need to prove hPSD_cont differently for Coulomb.
  - VelocityDecayInstance: Needs new Coulomb-specific instance. Significant work.
-/


-- ============================================================================
-- Part 8: VelocityDecayConditions for Coulomb — what changes
-- ============================================================================

/-
  The VelocityDecayConditions bundle has 18 conditions. For Coulomb, the main
  issues are in conditions that require the Landau matrix entries to be:
  (a) bounded — fails for Coulomb (entries ~ |z|⁻¹)
  (b) differentiable everywhere — fails at z = 0
  (c) have bounded derivatives — fails at z = 0

  AFFECTED CONDITIONS (6 of 18):

  1. hLandauFluxDiff: Differentiability of the Landau flux integral
     ∫ A(v-w) · (flux) dw as a function of v.
     Currently proved via Leibniz rule with bounded derivative (LandauMatrixDerivBound).
     For Coulomb: A entries ~ |z|⁻¹ are integrable, derivatives ~ |z|⁻² are also
     integrable in 3D. So Leibniz rule SHOULD still apply, but the domination
     argument needs the integral of the DERIVATIVE to converge.
     Derivative bound: O(|z|^{γ+1}) = O(|z|⁻²). In 3D: ∫ |z|⁻² dz < ∞. ✓
     STATUS: Provable for Coulomb with modified domination argument.

  2. hLandauIBP_df_g, hLandauIBP_f_dg, hLandauIBP_fg: IBP integrability
     These need ∫ |A(v-w) · f(w) · (something)| dw < ∞.
     For Schwartz f: the integrand decays like f(w) · |v-w|^{γ+2} · (derivatives of f).
     For Coulomb: f(w) · |v-w|⁻¹ · |∇f(w)|. Since f is Schwartz and |v-w|⁻¹ is
     locally integrable, this is integrable. ✓
     STATUS: Provable for Schwartz f with Coulomb kernel.

  3. hLandauFluxInt: Integrability of the Landau flux.
     Needs ∫ ‖A(v-w)‖ · |f(w)| · |∇f(w)| dw < ∞.
     Same analysis as above. ✓
     STATUS: Provable.

  4. hPSD_inner_int, hPSD_outer_int: Integrability of PSD integrand.
     PSDIntegrand(v,w) involves A(v-w) applied to score differences.
     For Coulomb, this is bounded by C · f(v) · f(w) · |v-w|^{γ+4} · (∇log f bounds).
     With Schwartz f, this is integrable. ✓
     STATUS: Provable.

  UNAFFECTED CONDITIONS (12 of 18):
  - hFubini_double/inner/outer: Fubini conditions (unchanged structure)
  - hSpatialTransport_int, hForceTransport_int: Transport terms (no Ψ dependence)
  - hForceIBP_f_dg, hForceIBP_fg: Force IBP (no Ψ dependence)
  - hSpatialTransport_joint, hSpatTransComp: Spatial transport (no Ψ dependence)
  - hf_velocity_dominated: Velocity domination (no Ψ dependence)
  - hD_cont: Entropy dissipation continuity (harder for Coulomb, but still true)

  SUMMARY: All 18 conditions are SATISFIABLE for Coulomb with Schwartz-class f.
  The proofs for 6 conditions need modification to handle the |z|⁻¹ singularity,
  but the singularity is always integrable in 3D, so no fundamental obstacles.
-/


-- ============================================================================
-- Part 9: Concrete experiments — verifying key properties
-- ============================================================================

/-- The euclidean norm is positive for nonzero vectors. -/
lemma eucNorm_pos {z : Fin 3 → ℝ} (hz : z ≠ 0) : 0 < eucNorm z :=
  Real.sqrt_pos_of_pos (normSq_pos hz)

/-- For the Coulomb kernel, the Landau matrix is PSD (using weakened positivity). -/
lemma coulomb_landauMatrix_posSemidef (z Y : Fin 3 → ℝ) :
    0 ≤ dotProduct Y (mulVec (landauMatrix coulombKernel z) Y) :=
  landauMatrix_posSemidef (powerLawKernel_nonneg _ _) Y

/-- For the Coulomb kernel, the nullspace characterization holds (z ≠ 0 → Ψ > 0). -/
lemma coulomb_nullspace (z : Fin 3 → ℝ) (hz : z ≠ 0) (Y : Fin 3 → ℝ)
    (h : dotProduct Y (mulVec (landauMatrix coulombKernel z) Y) = 0) :
    ∃ l : ℝ, Y = l • z :=
  landauMatrix_quadForm_eq_zero_iff (powerLawKernel_pos (eucNorm_pos hz)) hz Y h


-- ============================================================================
-- Part 10: The derivative bound for Coulomb — key for VelocityDecayConditions
-- ============================================================================

/-
  Current LandauMatrixDerivBound proves:
    ‖fderiv ℝ (fun z => landauMatrix Ψ z i j) z‖ ≤ C · (1 + ‖z‖)²
  assuming ContDiff ℝ 1 Ψ.

  For Coulomb, the matrix entries at z ≠ 0 are:
    A_{ij}(z) = |z|⁻³ · (|z|²δ_{ij} - z_iz_j) = |z|⁻¹δ_{ij} - |z|⁻³z_iz_j

  Derivatives:
    ∂A_{ij}/∂z_k = ∂/∂z_k [|z|⁻¹δ_{ij}] - ∂/∂z_k [|z|⁻³z_iz_j]

    ∂/∂z_k [|z|⁻¹] = -|z|⁻³ z_k

    ∂/∂z_k [|z|⁻³z_iz_j] = -3|z|⁻⁵ z_k z_i z_j + |z|⁻³(δ_{ik}z_j + z_iδ_{jk})

  So ∂A_{ij}/∂z_k has terms of order |z|⁻² (worst case).

  In 3D: ∫_{B(0,R)} |z|⁻² dz = 4π ∫_0^R r⁻² · r² dr = 4πR < ∞.

  For the Leibniz rule, we need:
    ∫_w |∂A_{ij}(v-w)/∂v_k| · |f(w)| · |stuff(w)| dw < ∞

  Since |∂A/∂v| ≤ C|v-w|⁻² and f is Schwartz, this is:
    ∫_w |v-w|⁻² · f(w) · |∇f(w)| dw

  Split into |w-v| < 1 and |w-v| ≥ 1:
    Near part: ∫_{|w-v|<1} |v-w|⁻² dw · sup|f·∇f| ≤ C₁ (integrable singularity)
    Far part: ∫_{|w-v|≥1} f(w) · |∇f(w)| dw ≤ C₂ (Schwartz decay)
  Total: finite. ✓

  So a Coulomb-specific derivative bound would be:
    ‖fderiv ℝ (fun z => landauMatrix Ψ_C z i j) z‖ ≤ C / ‖z‖²   (for z ≠ 0)
  which replaces the polynomial bound with a SINGULAR bound.
-/

/-- Derivative bound for Coulomb matrix entries: O(|z|⁻²) at z ≠ 0. -/
lemma coulomb_landauMatrix_deriv_bound (i j : Fin 3) :
    ∃ C > 0, ∀ z : Fin 3 → ℝ, z ≠ 0 →
      ‖fderiv ℝ (fun z' => landauMatrix coulombKernel z' i j) z‖ ≤
        C * eucNorm z ^ (-2 : ℝ) := by
  sorry

/-- The Coulomb matrix derivative singularity |z|⁻² is locally integrable in ℝ³. -/
lemma coulomb_deriv_locally_integrable :
    ∀ v : Fin 3 → ℝ, IntegrableOn
      (fun w => eucNorm (v - w) ^ (-2 : ℝ))
      (Metric.ball v 1) := by
  sorry -- ∫_{B(v,1)} |v-w|⁻² dw = 4π∫_0^1 r⁻² · r² dr = 4π


-- ============================================================================
-- Part 11: Summary and recommendations
-- ============================================================================

/-
  RECOMMENDATION: Extend the formalization to Coulomb in two phases.

  PHASE 1 (Minimal, high value):
  ─────────────────────────────────
  Change Theorem42 hypotheses:
    (hΨ : ∀ r, 0 < Ψ r)     →  (hΨ_nonneg : ∀ r, 0 ≤ Ψ r)
                                  (hΨ_pos : ∀ r, 0 < r → 0 < Ψ r)
    (hΨ_cont : Continuous Ψ) →  [REMOVE — absorbed into hPSD_cont below]

  Add to Theorem42 hypothesis list (or VelocityDecayConditions):
    (hPSD_cont_hyp : ∀ x, Continuous (fun p => PSDIntegrand Ψ (f x) p.1 p.2))

  This is a ~20 line change to Theorem42.lean. Zero changes to Sections 2-9.
  The existing `PSDIntegrand_continuous` lemma becomes ONE WAY to discharge
  `hPSD_cont_hyp` (for continuous Ψ). A new `PSDIntegrand_continuous_powerlaw`
  lemma provides ANOTHER WAY (for singular Ψ with γ > -4).

  Impact on ConcreteTheorem42:
    - Would take hPSD_cont as a hypothesis (user proves it for their kernel)
    - For Coulomb: proved by PSDIntegrand_continuous_powerlaw

  Impact on VelocityDecayInstance:
    - Existing instances unchanged (they use bounded continuous Ψ)
    - New Coulomb instance needed (substantial but doable)

  PHASE 2 (More work, completes the story):
  ────────────────────────────────────────────
  Create a CoulombVelocityDecayInstance:
    - Prove all 18 VelocityDecayConditions for Coulomb kernel + Schwartz f
    - Key challenge: Replace polynomial derivative bounds with integrable
      singularity bounds (|z|⁻² instead of C(1+|z|)²)
    - Requires modifying LandauMatrixDerivBound or creating a Coulomb-specific version

  Create CoulombConcreteTheorem42:
    - Same statement as ConcreteTheorem42 but with Ψ = coulombKernel
    - Drops: hΨ_cont, hΨ_smooth, hΨ_growth
    - Adds: nothing (all needed properties are automatic for power-law kernels)

  ESTIMATE: Phase 1 is ~1 day of work. Phase 2 is ~1-2 weeks (mainly
  the VelocityDecayConditions proofs with integrable singularities).

  SCOPE OF IMPROVEMENT:
  - Currently covers: γ ≥ 0 (Maxwell and hard potentials with smooth Ψ)
  - After Phase 1: γ > -4 (all physical potentials including Coulomb)
                    at the abstract level, with concrete instances for γ ≥ 0
  - After Phase 2: γ > -4 with concrete Coulomb instance
-/


-- ============================================================================
-- Part 12: Alternative — the "effective matrix" formulation
-- ============================================================================

/-
  An alternative approach: instead of parametrizing by Ψ : ℝ → ℝ, work with
  the collision matrix A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ directly.

  This is MORE GENERAL (allows non-rotationally-symmetric kernels) but requires
  a larger refactor (changing the type of landauMatrix everywhere).

  Required properties of A:
    (1) ∀ z, (A z)ᵀ = A z                   -- symmetric
    (2) A (-z) = A z                          -- even
    (3) ∀ z Y, 0 ≤ Yᵀ A(z) Y                -- PSD
    (4) ∀ z ≠ 0, Yᵀ A(z) Y = 0 → Y ∥ z     -- rank 2 (nullspace = span{z})
    (5) ∀ z, A(z) z = 0                       -- z is in the nullspace
    (6) Continuous (fun (v,w) => PSDIntegrand_A A f v w)  -- PSD integrand continuous

  Currently, all these are DERIVED from Ψ properties (Lemmas 1-3 in Section 2).
  With the effective matrix formulation, they become direct hypotheses.

  VERDICT: Too much refactoring for the benefit. The Phase 1 approach (weakening
  Ψ hypotheses) is strictly better — it covers Coulomb with minimal changes while
  keeping the clean Ψ-based formulation.
-/


-- ============================================================================
-- Part 13: What about the ConcreteTheorem42 with Coulomb?
-- ============================================================================

/-
  A Coulomb-specific concrete theorem would look like:

  theorem CoulombConcreteTheorem42
    (f : Torus3 → (Fin 3 → ℝ) → ℝ)
    (E B : Torus3 → Fin 3 → ℝ)
    (ν ρ_ion : ℝ)
    (hν : 0 < ν)
    (hρ_ion : 0 < ρ_ion)
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth_v : ∀ x, ContDiff ℝ ⊤ (f x))
    (hf_smooth_x : ∀ v, ContDiff ℝ ⊤ (periodicLift (fun x => f x v)))
    (hB_smooth : ∀ i, ContDiff ℝ ⊤ (periodicLift (fun x => B x i)))
    (hSchwartz : UniformSchwartzDecay f)
    (hLogGrowth : ∃ C K, ∀ x v, |Real.log (f x v)| ≤ C * (1 + ‖v‖) ^ K)
    -- Steady-state equations with COULOMB kernel
    (hVlasov : ∀ x v,
      dotProduct v (torusGradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator coulombKernel (f x) v)
    (hAmpere : ∀ x, torusCurlX B x = fun i => ∫ v, v i * f x v)
    (hGauss : ∀ x, torusDivX E x = (∫ v, f x v) - ρ_ion)
    (hDivB : ∀ x, torusDivX B x = 0)
    :
    ∃ (T_eq : ℝ) (B₀ : Fin 3 → ℝ), 0 < T_eq ∧
    (∀ x v, f x v = equilibriumMaxwellian ρ_ion T_eq v) ∧
    (∀ x, E x = 0) ∧
    (∀ x, B x = B₀) := by
  sorry
  -- Note: This has FEWER hypotheses than the general ConcreteTheorem42!
  -- We dropped: hΨ_pos, hΨ_cont, hΨ_smooth, hΨ_growth (4 hypotheses).
  -- The kernel is FIXED (coulombKernel), so its properties are provable, not assumed.
  -- Total hypotheses: 12 (down from 16 in ConcreteTheorem42).

  -- This is a strictly CLEANER theorem for the most physically important case.
-/


end VML
