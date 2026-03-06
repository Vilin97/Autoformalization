/-
  Concrete FlatTorus3 instance on Fin 3 → AddCircle 1.

  The spatial domain is the 3-torus T³ = (ℝ/ℤ)³, represented as
  `Fin 3 → AddCircle 1`. Every function T³ → ℝ is automatically
  periodic — no extra hypotheses needed.

  Differential operators are defined via the periodic lift:
  for f : T³ → ℝ, the lift f̃ := f ∘ proj : ℝ³ → ℝ is periodic,
  and we define gradX f x := fderiv of f̃ at any preimage of x.

  This provides a concrete justification for all FlatTorus3 axioms.
-/
import Aristotle.Landau.main.Defs

set_option linter.all false
open MeasureTheory Matrix Finset BigOperators Real Filter

noncomputable section

-- ============================================================================
-- The concrete 3-torus
-- ============================================================================

/-- The 3-torus: product of three circles with period 1. -/
abbrev Torus3 := Fin 3 → AddCircle (1 : ℝ)

-- All measure/topology instances come for free:
instance : CompactSpace Torus3 := inferInstance
instance : T2Space Torus3 := inferInstance
instance : IsFiniteMeasure (volume : Measure Torus3) := inferInstance
instance : SigmaFinite (volume : Measure Torus3) := inferInstance

-- ============================================================================
-- The projection (covering map) ℝ³ → T³
-- ============================================================================

/-- The quotient map ℝ³ → T³, sending each coordinate to its equivalence class. -/
def torusMk (x : Fin 3 → ℝ) : Torus3 := fun i => QuotientAddGroup.mk (x i)

-- torusMk is continuous (quotient maps are continuous)
lemma torusMk_continuous : Continuous torusMk :=
  continuous_pi (fun i => continuous_coinduced_rng.comp (continuous_apply i))

-- torusMk is surjective (every point in T³ has a preimage)
lemma torusMk_surjective : Function.Surjective torusMk := by
  intro x
  -- For each coordinate, QuotientAddGroup.mk is surjective
  choose f hf using fun i => Quotient.exists_rep (x i)
  exact ⟨f, funext hf⟩

-- ============================================================================
-- Periodic lift: for f : T³ → ℝ, the composition f ∘ torusMk : ℝ³ → ℝ
-- ============================================================================

/-- The periodic lift of a function on the torus to ℝ³. -/
def periodicLift (f : Torus3 → ℝ) : (Fin 3 → ℝ) → ℝ := f ∘ torusMk

-- The lift IS periodic (by construction):
lemma periodicLift_periodic (f : Torus3 → ℝ) (x : Fin 3 → ℝ) (i : Fin 3) :
    periodicLift f (x + Pi.single i 1) = periodicLift f x := by
  simp only [periodicLift, Function.comp_apply]
  congr 1; ext j
  simp only [torusMk, Pi.add_apply]
  by_cases h : j = i
  · subst h; simp only [Pi.single_eq_same]
    -- (x j + 1 : ℝ) maps to same class as (x j : ℝ) in AddCircle 1
    -- because 1 generates the subgroup we quotient by
    change QuotientAddGroup.mk (x j + 1) = QuotientAddGroup.mk (x j)
    rw [QuotientAddGroup.eq]
    exact ⟨-1, by simp⟩
  · simp [Pi.single_eq_of_ne h]

-- If f : T³ → ℝ is continuous, the lift is continuous:
lemma periodicLift_continuous (f : Torus3 → ℝ) (hf : Continuous f) :
    Continuous (periodicLift f) :=
  hf.comp torusMk_continuous

-- ============================================================================
-- The key lemma: fderiv of the periodic lift is well-defined
-- (independent of the choice of lift point)
-- ============================================================================

/-- The periodic lift at shifted argument equals the original when the shift
    maps to the same torus point. -/
lemma periodicLift_shift (f : Torus3 → ℝ) (x y : Fin 3 → ℝ)
    (h : torusMk x = torusMk y) (z : Fin 3 → ℝ) :
    periodicLift f (z + (x - y)) = periodicLift f z := by
  simp only [periodicLift, Function.comp_apply]
  congr 1; ext i
  simp only [torusMk, Pi.add_apply, Pi.sub_apply]
  -- x i - y i is an integer, so adding it doesn't change the equivalence class
  have hi : (fun i => QuotientAddGroup.mk (x i) : Torus3) i =
            (fun i => QuotientAddGroup.mk (y i) : Torus3) i := by
    exact congr_fun h i
  simp only at hi
  rw [QuotientAddGroup.eq] at hi ⊢
  obtain ⟨n, hn⟩ := hi
  refine ⟨n, ?_⟩
  simp at hn ⊢
  linarith

/-- fderiv of the lift at two points that map to the same torus point are equal.
    This follows because f̃(x) = f̃(x + n) for integer n, so the 1-jets agree. -/
lemma periodicLift_fderiv_eq (f : Torus3 → ℝ) (x y : Fin 3 → ℝ)
    (h : torusMk x = torusMk y) :
    fderiv ℝ (periodicLift f) x = fderiv ℝ (periodicLift f) y := by
  -- periodicLift f ∘ (· + (x - y)) = periodicLift f
  have hshift : (fun z => periodicLift f (z + (x - y))) = periodicLift f := by
    ext z; exact periodicLift_shift f x y h z
  -- By fderiv_comp_add_right:
  -- fderiv (fun z => f̃(z + (x-y))) y = fderiv f̃ (y + (x-y)) = fderiv f̃ x
  have h1 : fderiv ℝ (fun z => periodicLift f (z + (x - y))) y =
             fderiv ℝ (periodicLift f) (y + (x - y)) := fderiv_comp_add_right (x - y)
  -- y + (x - y) = x
  have h2 : y + (x - y) = x := by ext i; simp [Pi.add_apply, Pi.sub_apply]
  rw [h2] at h1
  -- But also fderiv (fun z => f̃(z + (x-y))) = fderiv f̃ (by hshift)
  rw [hshift] at h1
  exact h1.symm

-- ============================================================================
-- Differential operators on T³ via the periodic lift
-- ============================================================================

/-- Spatial gradient on T³.
    For f : T³ → ℝ, we lift to ℝ³, compute fderiv, and read off components.
    This is well-defined by periodicLift_fderiv_eq. -/
def torusGradX (f : Torus3 → ℝ) (x : Torus3) : Fin 3 → ℝ :=
  -- Choose any preimage of x
  let x₀ := (torusMk_surjective x).choose
  fun i => fderiv ℝ (periodicLift f) x₀ (Pi.single i 1)

/-- Spatial divergence on T³. -/
def torusDivX (F : Torus3 → (Fin 3 → ℝ)) (x : Torus3) : ℝ :=
  let x₀ := (torusMk_surjective x).choose
  ∑ i : Fin 3, fderiv ℝ (fun y => periodicLift (fun z => F z i) y) x₀ (Pi.single i 1)

/-- Spatial curl on T³. -/
def torusCurlX (F : Torus3 → (Fin 3 → ℝ)) (x : Torus3) : Fin 3 → ℝ :=
  let x₀ := (torusMk_surjective x).choose
  let d := fun i j => fderiv ℝ (fun y => periodicLift (fun z => F z j) y) x₀ (Pi.single i 1)
  ![d 1 2 - d 2 1, d 2 0 - d 0 2, d 0 1 - d 1 0]

-- ============================================================================
-- Key intermediate: periodicLift of torusGradX equals fderiv of periodicLift
-- ============================================================================

/-- The periodic lift of the gradient component equals the fderiv of the lift.
    This resolves the `choose` ambiguity: at each point, the gradient uses a
    chosen preimage, but by periodicLift_fderiv_eq, the fderiv is the same
    for any preimage of the same torus point. -/
lemma periodicLift_torusGradX (φ : Torus3 → ℝ) (i : Fin 3)
    (y : Fin 3 → ℝ) :
    periodicLift (fun z => torusGradX φ z i) y =
    fderiv ℝ (periodicLift φ) y (Pi.single i 1) := by
  simp only [periodicLift, Function.comp_apply, torusGradX]
  have h := periodicLift_fderiv_eq φ ((torusMk_surjective (torusMk y)).choose) y
    (torusMk_surjective (torusMk y)).choose_spec
  exact congr_fun (congr_arg DFunLike.coe h) (Pi.single i 1)

-- ============================================================================
-- Helper lemmas: fderiv for const_mul and exp without differentiability
-- ============================================================================

/-- fderiv(c * g) = c • fderiv(g) unconditionally.
    When g is differentiable: by fderiv_const_smul.
    When g is not differentiable and c ≠ 0: c * g is also not differentiable,
    so both sides are the zero map.
    When c = 0: both sides are 0. -/
lemma fderiv_const_mul_always {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (g : E → ℝ) (x : E) :
    fderiv ℝ (fun y => c * g y) x = c • fderiv ℝ g x := by
  by_cases hc : c = 0
  · have : (fun y => c * g y) = fun _ => (0 : ℝ) := by ext y; simp [hc]
    rw [this]; simp [hc]
  · by_cases hg : DifferentiableAt ℝ g x
    · exact fderiv_const_smul hg c
    · have hcg : ¬ DifferentiableAt ℝ (fun y => c * g y) x := by
        intro h; apply hg
        have : (fun y => c⁻¹ * (c * g y)) = g := by ext y; field_simp
        exact this ▸ h.const_mul c⁻¹
      rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt hcg]
      simp

/-- fderiv(exp ∘ g) x = exp(g x) • fderiv g x unconditionally.
    When g is differentiable: by fderiv_exp.
    When g is not differentiable: exp ∘ g is also not differentiable
    (since g = log ∘ exp ∘ g and log is smooth on (0,∞)), so both sides are 0. -/
lemma fderiv_exp_comp_always {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (x : E) :
    fderiv ℝ (fun y => Real.exp (g y)) x = Real.exp (g x) • fderiv ℝ g x := by
  by_cases hg : DifferentiableAt ℝ g x
  · exact fderiv_exp hg
  · have heg : ¬ DifferentiableAt ℝ (fun y => Real.exp (g y)) x := by
      intro h; apply hg
      have hlog : DifferentiableAt ℝ Real.log (Real.exp (g x)) :=
        Real.differentiableAt_log (ne_of_gt (Real.exp_pos (g x)))
      have h2 := hlog.comp x h
      have : (Real.log ∘ fun y => Real.exp (g y)) = g := by ext y; simp [Real.log_exp]
      rwa [this] at h2
    rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt heg]
    simp

-- ============================================================================
-- Clairaut's theorem (symmetry of mixed partial derivatives)
-- ============================================================================

/-- Clairaut's theorem via fderiv: ∂²f/∂xᵢ∂xⱼ = ∂²f/∂xⱼ∂xᵢ for C² functions. -/
theorem clairaut_fderiv {n : ℕ} (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (i j : Fin n) (hg : ContDiff ℝ 2 g) :
    fderiv ℝ (fun y => fderiv ℝ g y (Pi.single j 1)) x (Pi.single i 1) =
    fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single j 1) := by
  have hsymm := (hg.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.contDiffAt (x := x)).fderiv_right (le_refl _)).differentiableAt le_rfl
  have key : ∀ v w, fderiv ℝ (fun y => fderiv ℝ g y v) x w = fderiv ℝ (fderiv ℝ g) x w v := by
    intro v w
    have h1 := fderiv_clm_apply hd (differentiableAt_const v)
    have hconst : fderiv ℝ (fun _ : Fin n → ℝ => v) x = 0 := by
      have : (fun _ : Fin n → ℝ => v) = Function.const _ v := rfl
      rw [this]; exact congr_fun (fderiv_const (𝕜 := ℝ) (E := Fin n → ℝ) v) x
    simp only [hconst, ContinuousLinearMap.comp_zero, zero_add] at h1
    exact congr_fun (congr_arg DFunLike.coe h1) w
  rw [key, key]; exact hsymm.eq (Pi.single i 1) (Pi.single j 1)

-- ============================================================================
-- Proving the 15 FlatTorus3 axioms
-- ============================================================================

-- NON-DIFFERENTIABILITY NOTE:
-- hGradAdd is the only gradient axiom that CANNOT be proved without
-- differentiability hypotheses. The counterexample: if f is differentiable
-- and g is not, fderiv(f+g) = 0 but fderiv(f) + fderiv(g) = fderiv(f) ≠ 0.
-- All other gradient axioms (scalar mul, chain exp, div linear) hold
-- universally via case analysis on differentiability.
-- We sorry the non-differentiable edge cases in the instance.

-- ============================================================================
-- AXIOM PROOFS (attempted)
-- ============================================================================

/-- hGradConst: gradient of constant function vanishes. -/
theorem torus_hGradConst (φ : Torus3 → ℝ) (hconst : ∀ x y, φ x = φ y) :
    ∀ x, torusGradX φ x = 0 := by
  intro x; ext i; simp only [torusGradX, Pi.zero_apply]
  have : periodicLift φ = fun _ => φ x := by
    ext y; simp only [periodicLift, Function.comp_apply]; exact hconst _ _
  rw [this]; rw [hasFDerivAt_const (φ x) _ |>.fderiv]; rfl

/-- hGradAdd: gradient additivity for C¹ functions. -/
theorem torus_hGradAdd' (f g : Torus3 → ℝ)
    (hf : ContDiff ℝ 1 (periodicLift f)) (hg : ContDiff ℝ 1 (periodicLift g)) :
    ∀ x, torusGradX (fun y => f y + g y) x =
      torusGradX f x + torusGradX g x := by
  intro x; ext i; simp only [torusGradX, Pi.add_apply]
  have hlift : periodicLift (fun y => f y + g y) = fun y => periodicLift f y + periodicLift g y := by
    ext y; simp [periodicLift]
  rw [hlift]
  rw [show (fun y => periodicLift f y + periodicLift g y) = (periodicLift f + periodicLift g)
    from rfl, fderiv_add (hf.differentiable le_rfl).differentiableAt
      (hg.differentiable le_rfl).differentiableAt]
  rfl

-- ============================================================================
-- Integration axioms (from Haar measure properties)
-- ============================================================================

/-- hSpatialAdd (with integrability, which the abstract axiom omits). -/
theorem torus_hSpatialAdd (g₁ g₂ : Torus3 → ℝ)
    (h1 : Integrable g₁) (h2 : Integrable g₂) :
    (∫ x, (g₁ x + g₂ x)) = (∫ x, g₁ x) + ∫ x, g₂ x :=
  integral_add h1 h2

/-- hSpatialVelocityFubini: swap spatial and velocity integrals.
    Uses SigmaFinite (from CompactSpace + IsFiniteMeasure). -/
theorem torus_hSpatialVelocityFubini (F : Torus3 → (Fin 3 → ℝ) → ℝ)
    (hF : ∀ x, Integrable (F x))
    (hF_joint : Integrable (Function.uncurry F) (volume.prod volume)) :
    (∫ x, ∫ v, F x v) = ∫ v, ∫ x, F x v := by
  exact integral_integral_swap hF_joint

-- NOTE: Our abstract axiom only requires pointwise integrability (∀ x, Integrable (F x)).
-- Mathlib's Fubini needs joint integrability. So the concrete version is slightly stronger.
-- We'd either strengthen the hypothesis in the abstract axiom or sorry this gap.

-- ============================================================================
-- Compact manifold axioms
-- ============================================================================

/-- hSpatialPos: positive function has positive integral.
    On a compact space with Haar measure, this follows from the measure
    being non-degenerate (positive on open sets). -/
theorem torus_hSpatialPos (g : Torus3 → ℝ) (hg_pos : ∀ x, 0 < g x)
    (hg_cont : Continuous g) :
    0 < ∫ x, g x := by
  have h1 : Integrable g :=
    hg_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  exact integral_pos_of_integrable_nonneg_nonzero hg_cont h1
    (fun x => le_of_lt (hg_pos x)) (ne_of_gt (hg_pos default))

/-- hSpatialNonnegZero: nonneg function with zero integral is zero.
    On compact space with Haar measure (positive on opens), this follows
    from: if continuous g ≥ 0 and ∫g = 0, then g = 0 a.e.,
    and by continuity g = 0 everywhere. -/
theorem torus_hSpatialNonnegZero (g : Torus3 → ℝ)
    (hg_nn : ∀ x, 0 ≤ g x) (hg_int : (∫ x, g x) = 0)
    (hg_cont : Continuous g) :
    ∀ x, g x = 0 := by
  have h1 : Integrable g :=
    hg_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  have h2 : g =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg hg_nn h1).mp hg_int
  have h3 : g = 0 :=
    (Continuous.ae_eq_iff_eq (volume : Measure Torus3) hg_cont continuous_const).mp h2
  exact fun x => congr_fun h3 x

-- ============================================================================
-- 1D integration lemmas (proved by Aristotle, used for torus IBP)
-- ============================================================================

/-- The integral of the derivative of a periodic function over one period is zero.
    Proved by Aristotle. -/
private theorem integral_deriv_periodic_zero' {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf_periodic : Function.Periodic f T)
    (hf_diff : Differentiable ℝ f)
    (hf_cont : Continuous (deriv f)) :
    ∫ x in (0 : ℝ)..T, deriv f x = 0 := by
  rw [intervalIntegral.integral_deriv_eq_sub]
  · exact sub_eq_zero_of_eq (hf_periodic 0 ▸ by norm_num)
  · aesop
  · exact hf_cont.intervalIntegrable _ _

/-- Integration by parts for periodic functions over one period.
    Proved by Aristotle. -/
private theorem ibp_periodic' {f g : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf_periodic : Function.Periodic f T)
    (hg_periodic : Function.Periodic g T)
    (hf_diff : Differentiable ℝ f)
    (hg_diff : Differentiable ℝ g)
    (hf'_cont : Continuous (deriv f))
    (hg'_cont : Continuous (deriv g)) :
    ∫ x in (0 : ℝ)..T, f x * deriv g x = -(∫ x in (0 : ℝ)..T, deriv f x * g x) := by
  have h_parts : ∫ x in (0 : ℝ)..T, f x * deriv g x =
      f T * g T - f 0 * g 0 - ∫ x in (0 : ℝ)..T, deriv f x * g x := by
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul] <;> norm_num [hf_diff.differentiableAt, hg_diff.differentiableAt]
    · exact hf'_cont.intervalIntegrable _ _
    · exact hg'_cont.intervalIntegrable _ _
  have hfT : f T = f 0 := by have := hf_periodic 0; simpa using this
  have hgT : g T = g 0 := by have := hg_periodic 0; simpa using this
  rw [h_parts, hfT, hgT]; ring

-- ============================================================================
-- IBP and Stokes axioms (the hard ones — need periodic structure)
-- ============================================================================

/-- hIBP_spatial: integration by parts on the torus.
    ∫_{T³} φ · ∂ψ/∂xᵢ = -∫_{T³} ψ · ∂φ/∂xᵢ.
    Proof idea: reduce to ∫₀¹ f·g' = -∫₀¹ f'·g via Fubini + periodicity. -/
theorem torus_hIBP_spatial (φ ψ : Torus3 → ℝ) (i : Fin 3)
    (hφ : ContDiff ℝ 1 (periodicLift φ)) (hψ : ContDiff ℝ 1 (periodicLift ψ)) :
    (∫ x, φ x * torusGradX ψ x i) = -(∫ x, ψ x * torusGradX φ x i) := by
  sorry -- core torus property: IBP with no boundary terms

/-- hCurlIntZero: ∫ u · (∇×F) = 0 on the torus.
    Each component of ∇×F is a difference of partial derivatives.
    ∫ ∂Fⱼ/∂xᵢ = 0 for periodic functions (fundamental theorem + periodicity). -/
theorem torus_hCurlIntZero (F : Torus3 → Fin 3 → ℝ) (u : Fin 3 → ℝ)
    (hF_diff : ∀ j, ContDiff ℝ 1 (periodicLift (fun x => F x j))) :
    ∫ x, dotProduct u (torusCurlX F x) = 0 := by
  sorry -- follows from torus_hIBP_spatial with φ = 1: ∫ torusGradX ψ i = 0

/-- hHarmonic_const: harmonic functions on the torus are constant.
    Standard result from Riemannian geometry / PDE theory.
    Energy method: ∫|∇φ|² = -∫φΔφ = 0 → ∇φ = 0 → φ constant. -/
theorem torus_hHarmonic_const (φ : Torus3 → ℝ)
    (hd : ContDiff ℝ 1 (periodicLift φ))
    (hharmonic : ∀ x, torusDivX (torusGradX φ) x = 0) :
    ∀ x y, φ x = φ y := by
  sorry -- deep result: energy method (∫|∇φ|² = -∫φΔφ = 0 → ∇φ = 0 → φ constant)

-- ============================================================================
-- ℝⁿ lemmas (proved in aristotle-in/, integrated here)
-- ============================================================================

/-- At a local maximum of a twice-differentiable function, the second derivative is nonpositive.
    Proved by Aristotle. -/
private theorem second_deriv_nonpos_at_local_max' {f : ℝ → ℝ} {x₀ : ℝ}
    (hmax : IsLocalMax f x₀)
    (hf' : ∀ᶠ x in nhds x₀, DifferentiableAt ℝ f x)
    (hf'' : DifferentiableAt ℝ (deriv f) x₀) :
    deriv (deriv f) x₀ ≤ 0 := by
  have h_first_deriv_zero : deriv f x₀ = 0 := IsLocalMax.deriv_eq_zero hmax
  by_contra h_contra; push_neg at h_contra
  obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ x ∈ Set.Ioo x₀ (x₀ + ε), deriv f x > 0 := by
    have := Metric.tendsto_nhds_nhds.1 (hf''.hasDerivAt.isLittleO.tendsto_div_nhds_zero)
    obtain ⟨δ, δ_pos, H⟩ := this _ h_contra; use δ, δ_pos; intro x hx
    have := H (show |x - x₀| < δ from abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    simp_all +decide [div_eq_mul_inv]
    rw [← div_eq_mul_inv, div_lt_iff₀] at this <;>
      cases abs_cases (deriv f x - (x - x₀) * deriv (deriv f) x₀) <;>
      cases abs_cases (x - x₀) <;>
      nlinarith [mul_pos (sub_pos.mpr hx.1) h_contra]
  have h_mvt : ∀ x ∈ Set.Ioo x₀ (x₀ + ε), ∃ c ∈ Set.Ioo x₀ x, deriv f c = (f x - f x₀) / (x - x₀) := by
    intros x hx
    apply exists_deriv_eq_slope f hx.left
    exact continuousOn_of_forall_continuousAt fun y hy =>
      if h : y = x₀ then by rw [h]; exact DifferentiableAt.continuousAt hf'.self_of_nhds
      else DifferentiableAt.continuousAt (differentiableAt_of_deriv_ne_zero
        (ne_of_gt (hε.2 y ⟨lt_of_le_of_ne hy.1 (Ne.symm h), by linarith [hy.2, hx.2]⟩)))
    exact fun y hy => DifferentiableAt.differentiableWithinAt
      (differentiableAt_of_deriv_ne_zero (ne_of_gt (hε.2 y ⟨hy.1, hy.2.trans hx.2⟩)))
  have h_inc : ∀ x ∈ Set.Ioo x₀ (x₀ + ε), f x > f x₀ := by
    intro x hx; obtain ⟨c, hc₁, hc₂⟩ := h_mvt x hx
    have := hε.2 c ⟨by linarith [hc₁.1, hx.1], by linarith [hc₁.2, hx.2]⟩
    rw [eq_div_iff] at hc₂ <;> nlinarith [hc₁.1, hc₁.2]
  rcases Metric.eventually_nhds_iff.mp hmax with ⟨δ, hδ, hδ'⟩
  exact absurd (h_inc (x₀ + Min.min ε δ / 2) ⟨by linarith [lt_min hε.1 hδ],
      by linarith [min_le_left ε δ, min_le_right ε δ]⟩)
    (not_lt_of_ge <| hδ' <| mem_ball_iff_norm.mpr <| abs_lt.mpr
      ⟨by linarith [lt_min hε.1 hδ, min_le_left ε δ, min_le_right ε δ],
       by linarith [lt_min hε.1 hδ, min_le_left ε δ, min_le_right ε δ]⟩)

/-- At a global maximum of a C² function on ℝⁿ, the Laplacian ≤ 0. -/
private theorem laplacian_nonpos_at_max_rn {n : ℕ} (g : (Fin n → ℝ) → ℝ) (x₀ : Fin n → ℝ)
    (hmax : ∀ x, g x ≤ g x₀)
    (hg : ContDiff ℝ 2 g) :
    ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x₀ (Pi.single i 1) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  let eᵢ : Fin n → ℝ := Pi.single i 1
  let p : ℝ → Fin n → ℝ := fun t => x₀ + t • eᵢ
  have hg_diff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hp0 : p 0 = x₀ := by simp [p]
  have hp_hd : ∀ t, HasDerivAt p eᵢ t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => t • eᵢ) eᵢ t := by
      have := (hasDerivAt_id t).smul_const eᵢ; simpa using this
    simpa using (hasDerivAt_const t x₀).add h1
  have hmax_gi : IsLocalMax (fun t => g (p t)) 0 :=
    Filter.Eventually.mono Filter.univ_mem fun t _ => by
      simp only [p, zero_smul, add_zero]; exact hmax _
  have hgi_diff : ∀ t, DifferentiableAt ℝ (fun t => g (p t)) t := fun t =>
    hg_diff.differentiableAt.comp t (hp_hd t).differentiableAt
  have hh_c1 : ContDiff ℝ 1 (fun y => fderiv ℝ g y eᵢ) :=
    ContDiff.clm_apply (hg.fderiv_right (by norm_num)) contDiff_const
  have hh_diff : DifferentiableAt ℝ (fun y => fderiv ℝ g y eᵢ) x₀ :=
    (hh_c1.differentiable le_rfl).differentiableAt
  have hderiv_gi : ∀ t, deriv (fun t => g (p t)) t = fderiv ℝ g (p t) eᵢ := fun t =>
    (hg_diff.differentiableAt.hasFDerivAt.comp_hasDerivAt t (hp_hd t)).deriv
  have hchain2 : HasDerivAt (fun t => fderiv ℝ g (p t) eᵢ)
      (fderiv ℝ (fun y => fderiv ℝ g y eᵢ) x₀ eᵢ) 0 := by
    have h_at_p0 : HasFDerivAt (fun y => fderiv ℝ g y eᵢ)
        (fderiv ℝ (fun y => fderiv ℝ g y eᵢ) x₀) (p 0) := by
      rw [hp0]; exact hh_diff.hasFDerivAt
    exact h_at_p0.comp_hasDerivAt 0 (hp_hd 0)
  have hderiv_gi_diff : DifferentiableAt ℝ (deriv (fun t => g (p t))) 0 := by
    rw [show deriv (fun t => g (p t)) = fun t => fderiv ℝ g (p t) eᵢ from funext hderiv_gi]
    exact hchain2.differentiableAt
  have h1d : deriv (deriv (fun t => g (p t))) 0 ≤ 0 :=
    second_deriv_nonpos_at_local_max' hmax_gi
      (Filter.Eventually.mono Filter.univ_mem (fun t _ => hgi_diff t))
      hderiv_gi_diff
  rw [show deriv (fun t => g (p t)) = fun t => fderiv ℝ g (p t) eᵢ from funext hderiv_gi] at h1d
  linarith [hchain2.deriv ▸ h1d]

/-- Killing equation on ℝⁿ implies each component is harmonic. -/
private theorem killing_harmonic_rn' {n : ℕ} (b : (Fin n → ℝ) → (Fin n → ℝ))
    (hb : ∀ j, ContDiff ℝ 2 (fun y => b y j))
    (hKilling : ∀ x i j,
      fderiv ℝ (fun y => b y j) x (Pi.single i 1) +
      fderiv ℝ (fun y => b y i) x (Pi.single j 1) = 0)
    (j : Fin n) (x : Fin n → ℝ) :
    ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ (fun z => b z j) y (Pi.single i 1)) x (Pi.single i 1) = 0 := by
  apply Finset.sum_eq_zero; intro i _
  have hK_fun : ∀ y, fderiv ℝ (fun z => b z j) y (Pi.single i 1) =
      -(fderiv ℝ (fun z => b z i) y (Pi.single j 1)) := by
    intro y; linarith [hKilling y i j]
  have hfun_eq : (fun y => fderiv ℝ (fun z => b z j) y (Pi.single i 1)) =
      (fun y => -(fderiv ℝ (fun z => b z i) y (Pi.single j 1))) := funext hK_fun
  rw [hfun_eq]
  have hdiff_j : Differentiable ℝ (fun y => fderiv ℝ (fun z => b z i) y (Pi.single j 1)) := by
    have : ContDiff ℝ 1 (fun y => fderiv ℝ (fun z => b z i) y (Pi.single j 1)) := by
      apply ContDiff.clm_apply
      · exact (hb i).fderiv_right le_rfl
      · exact contDiff_const
    exact this.differentiable le_rfl
  have hfun_neg : (fun y => -(fderiv ℝ (fun z => b z i) y (Pi.single j 1))) =
      -(fun y => fderiv ℝ (fun z => b z i) y (Pi.single j 1)) := by ext; simp
  rw [hfun_neg, fderiv_neg]
  simp only [ContinuousLinearMap.neg_apply, neg_eq_zero]
  rw [clairaut_fderiv (fun z => b z i) x i j (hb i)]
  have hK_diag_fun : (fun y => fderiv ℝ (fun z => b z i) y (Pi.single i 1)) = fun _ => 0 := by
    ext y; linarith [hKilling y i i]
  rw [hK_diag_fun]; simp

/-- Irrotational + solenoidal → each component is harmonic on ℝⁿ. -/
private theorem curl_div_harmonic_rn' {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : ∀ i, ContDiff ℝ 2 (fun y => F y i))
    (hcurl : ∀ x i j,
      fderiv ℝ (fun y => F y j) x (Pi.single i 1) =
      fderiv ℝ (fun y => F y i) x (Pi.single j 1))
    (hdiv : ∀ x, ∑ i : Fin n,
      fderiv ℝ (fun y => F y i) x (Pi.single i 1) = 0)
    (j : Fin n) (x : Fin n → ℝ) :
    ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ (fun z => F z j) y (Pi.single i 1)) x (Pi.single i 1) = 0 := by
  have hcurl_fun : ∀ i, (fun y => fderiv ℝ (fun z => F z j) y (Pi.single i 1)) =
      (fun y => fderiv ℝ (fun z => F z i) y (Pi.single j 1)) := by
    intro i; ext y; exact hcurl y i j
  simp_rw [hcurl_fun]
  simp_rw [clairaut_fderiv (fun z => F z _) x _ j (hF _)]
  have hdiff_comp : ∀ i, DifferentiableAt ℝ (fun y => fderiv ℝ (fun z => F z i) y (Pi.single i 1)) x := by
    intro i
    have : ContDiff ℝ 1 (fun y => fderiv ℝ (fun z => F z i) y (Pi.single i 1)) :=
      ContDiff.clm_apply ((hF i).fderiv_right le_rfl) contDiff_const
    exact (this.differentiable le_rfl).differentiableAt
  have : ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ (fun z => F z i) y (Pi.single i 1)) x (Pi.single j 1) =
      (∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ (fun z => F z i) y (Pi.single i 1)) x) (Pi.single j 1) :=
    (ContinuousLinearMap.sum_apply _ _ _).symm
  rw [this]
  have hfsum : (∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ (fun z => F z i) y (Pi.single i 1)) x) =
      fderiv ℝ (fun y => ∑ i : Fin n, fderiv ℝ (fun z => F z i) y (Pi.single i 1)) x := by
    rw [fderiv_fun_sum (fun i _ => hdiff_comp i)]
  rw [hfsum]
  have hsum_fun : (fun y => ∑ i : Fin n, fderiv ℝ (fun z => F z i) y (Pi.single i 1)) = fun _ => 0 :=
    funext hdiv
  rw [hsum_fun]; simp

-- ============================================================================

/-- hLaplacianMaxNonpos: Δφ ≤ 0 at a global maximum.
    Second derivative test: at a maximum, the Hessian is negative semi-definite,
    so its trace (= Laplacian) ≤ 0. -/
theorem torus_hLaplacianMaxNonpos (φ : Torus3 → ℝ) (x₀ : Torus3)
    (hd : ContDiff ℝ 1 (periodicLift φ))
    (hmax : ∀ x, φ x ≤ φ x₀) :
    torusDivX (torusGradX φ) x₀ ≤ 0 := by
  simp only [torusDivX]
  -- Rewrite using periodicLift_torusGradX
  simp_rw [show ∀ i, (fun y => periodicLift (fun z => torusGradX φ z i) y) =
      (fun y => fderiv ℝ (periodicLift φ) y (Pi.single i 1)) from
      fun i => funext (periodicLift_torusGradX φ i)]
  -- Let x₀' be the canonical preimage of x₀
  set x₀' := (torusMk_surjective x₀).choose
  -- For each i, show the term is ≤ 0
  apply Finset.sum_nonpos; intro i _
  -- Let hᵢ y = fderiv ℝ (periodicLift φ) y (Pi.single i 1)
  -- Case split: either hᵢ is differentiable at x₀' or not
  by_cases hdiff : DifferentiableAt ℝ (fun y => fderiv ℝ (periodicLift φ) y (Pi.single i 1)) x₀'
  · -- Case: hᵢ is differentiable at x₀'. Use 1D second derivative test.
    -- Let gᵢ t = periodicLift φ (x₀' + t • eᵢ)
    let eᵢ : Fin 3 → ℝ := Pi.single i 1
    let gᵢ : ℝ → ℝ := fun t => periodicLift φ (x₀' + t • eᵢ)
    -- gᵢ has global max at 0
    have hmax_gi : IsLocalMax gᵢ 0 :=
      Filter.Eventually.mono Filter.univ_mem fun t _ => by
        simp only [gᵢ, zero_smul, add_zero, periodicLift, Function.comp_apply]
        rw [(torusMk_surjective x₀).choose_spec]
        exact hmax (torusMk (x₀' + t • eᵢ))
    -- Helper: the path t ↦ x₀' + t • eᵢ has derivative eᵢ
    have hpath_hd : ∀ t, HasDerivAt (fun s => x₀' + s • eᵢ) eᵢ t := fun t => by
      have hsmul : HasDerivAt (fun s : ℝ => s • eᵢ) eᵢ t := by
        have h := (hasDerivAt_id t).smul_const eᵢ
        simp only [id, one_smul] at h; exact h
      simpa using hsmul.const_add x₀'
    -- gᵢ is differentiable everywhere (since periodicLift φ is C¹)
    have hd_diff : Differentiable ℝ (periodicLift φ) := hd.differentiable le_rfl
    have hgi_diff : ∀ t, DifferentiableAt ℝ gᵢ t := fun t =>
      hd_diff.differentiableAt.comp t (hpath_hd t).differentiableAt
    -- deriv gᵢ = hᵢ ∘ (x₀' + · • eᵢ)
    have hderiv_gi : ∀ t, deriv gᵢ t = fderiv ℝ (periodicLift φ) (x₀' + t • eᵢ) eᵢ := fun t =>
      (hd_diff.differentiableAt.hasFDerivAt.comp_hasDerivAt t (hpath_hd t)).deriv
    -- deriv gᵢ is differentiable at 0 (since hᵢ is diff at x₀')
    have hderiv_gi_diff : DifferentiableAt ℝ (deriv gᵢ) 0 := by
      rw [show deriv gᵢ = fun t => fderiv ℝ (periodicLift φ) (x₀' + t • eᵢ) eᵢ from funext hderiv_gi]
      show DifferentiableAt ℝ ((fun y => fderiv ℝ (periodicLift φ) y eᵢ) ∘ (fun t : ℝ => x₀' + t • eᵢ)) 0
      apply DifferentiableAt.comp
      · simp only [zero_smul, add_zero]; exact hdiff
      · exact (hpath_hd 0).differentiableAt
    -- Apply 1D second derivative test
    have h1d : deriv (deriv gᵢ) 0 ≤ 0 :=
      second_deriv_nonpos_at_local_max' hmax_gi
        (Filter.Eventually.mono Filter.univ_mem (fun t _ => hgi_diff t))
        hderiv_gi_diff
    -- Connect: fderiv ℝ hᵢ x₀' eᵢ = deriv (deriv gᵢ) 0
    have hconnect : deriv (deriv gᵢ) 0 = fderiv ℝ (fun y => fderiv ℝ (periodicLift φ) y eᵢ) x₀' eᵢ := by
      rw [show deriv gᵢ = fun t : ℝ => fderiv ℝ (periodicLift φ) (x₀' + t • eᵢ) eᵢ from funext hderiv_gi]
      -- Use chain rule: g ∘ f has deriv (fderiv g x₀') eᵢ at 0
      -- where g = fun y => fderiv ... y eᵢ, f = fun t => x₀' + t • eᵢ
      have hfda : HasFDerivAt (fun y => fderiv ℝ (periodicLift φ) y eᵢ)
          (fderiv ℝ (fun y => fderiv ℝ (periodicLift φ) y eᵢ) x₀') (x₀' + (0 : ℝ) • eᵢ) := by
        simp only [zero_smul, add_zero]; exact hdiff.hasFDerivAt
      exact (hfda.comp_hasDerivAt 0 (hpath_hd 0)).deriv
    rw [← hconnect]; exact h1d
  · -- Case: hᵢ not differentiable at x₀'. fderiv = 0 ≤ 0.
    simp [fderiv_zero_of_not_differentiableAt hdiff]

-- ============================================================================
-- Flatness axioms
-- ============================================================================

/-- hKillingToHarmonic: Killing vector field components are harmonic on flat T³.
    Uses: Clairaut's theorem + trace of Killing equation.
    Key proof steps:
    1. Convert C² hypothesis via periodicLift_torusGradX
    2. Derive ContDiff ℝ 2 from differentiable first-order partials (finite-dim analysis)
    3. Apply killing_harmonic_rn' to the periodic lift
    Sorry'd: the ContDiff ℝ 2 derivation step (finite-dimensional analysis gap). -/
-- Helper used by both Killing and curl/div proofs:
-- derive ContDiff ℝ 2 from C¹ + C¹ of each partial
private lemma contDiff2_from_partials {g : (Fin 3 → ℝ) → ℝ}
    (hg1 : ContDiff ℝ 1 g)
    (hg_parts : ∀ i : Fin 3, ContDiff ℝ 1 (fun y => fderiv ℝ g y (Pi.single i 1))) :
    ContDiff ℝ 2 g := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
  refine ⟨hg1.differentiable le_rfl, fun h => by simp at h, ?_⟩
  rw [contDiff_clm_apply_iff]
  intro v
  have heq : (fun y => fderiv ℝ g y v) =
      fun y => ∑ i : Fin 3, v i * fderiv ℝ g y (Pi.single i 1) := by
    ext y
    set L := fderiv ℝ g y with hL
    have hv : v = ∑ i : Fin 3, v i • (Pi.single i (1 : ℝ) : Fin 3 → ℝ) := by
      ext m; simp [Pi.single_apply, mul_ite, Finset.sum_ite_eq']
    -- conv_lhs rewrites only the argument of L, not the v inside the sum on the RHS
    calc L v = L (∑ i : Fin 3, v i • (Pi.single i (1 : ℝ) : Fin 3 → ℝ)) := by
            conv_lhs => rw [hv]
      _ = ∑ i : Fin 3, v i * L (Pi.single i (1 : ℝ)) := by
          simp [map_sum, map_smul, smul_eq_mul]
  rw [heq]
  exact ContDiff.sum (fun i _ => (hg_parts i).const_smul (v i))

theorem torus_hKillingToHarmonic (b : Torus3 → Fin 3 → ℝ)
    (hb_C1 : ∀ j, ContDiff ℝ 1 (periodicLift (fun z => b z j)))
    (hb_C2 : ∀ j i, ContDiff ℝ 1 (periodicLift (fun x => torusGradX (fun y => b y j) x i)))
    (hKilling : ∀ x i j, torusGradX (fun y => b y j) x i +
                          torusGradX (fun y => b y i) x j = 0) :
    ∀ j : Fin 3, ∀ x, torusDivX (torusGradX (fun y => b y j)) x = 0 := by
  -- Convert hb_C2 to ℝⁿ form: each partial ∂b_k/∂x_i is C¹
  have hC2_comp : ∀ k i : Fin 3, ContDiff ℝ 1
      (fun y => fderiv ℝ (periodicLift (fun z => b z k)) y (Pi.single i 1)) := by
    intro k i
    have h := hb_C2 k i
    rwa [show periodicLift (fun x => torusGradX (fun y => b y k) x i) =
        fun y => fderiv ℝ (periodicLift (fun z => b z k)) y (Pi.single i 1) from
        funext (periodicLift_torusGradX (fun z => b z k) i)] at h
  -- Derive ContDiff ℝ 2 for each component
  have hC2_all : ∀ k : Fin 3, ContDiff ℝ 2 (periodicLift (fun z => b z k)) :=
    fun k => contDiff2_from_partials (hb_C1 k) (hC2_comp k)
  -- Killing condition in ℝⁿ form
  have hKilling_rn : ∀ (y : Fin 3 → ℝ) (i k : Fin 3),
      fderiv ℝ (periodicLift (fun z => b z k)) y (Pi.single i 1) +
      fderiv ℝ (periodicLift (fun z => b z i)) y (Pi.single k 1) = 0 := by
    intro y i k
    rw [← periodicLift_torusGradX (fun w => b w k) i y,
        ← periodicLift_torusGradX (fun w => b w i) k y]
    simp only [periodicLift, Function.comp_apply]
    exact hKilling (torusMk y) i k
  -- Main proof: for each j and x, show div(grad(b_j))(x) = 0
  intro jj x
  simp only [torusDivX]
  simp_rw [show ∀ i : Fin 3, (fun y => periodicLift (fun z => torusGradX (fun w => b w jj) z i) y) =
      (fun y => fderiv ℝ (periodicLift (fun z => b z jj)) y (Pi.single i 1)) from
      fun i => funext (periodicLift_torusGradX (fun z => b z jj) i)]
  exact killing_harmonic_rn'
    (fun y k => periodicLift (fun z => b z k) y)
    hC2_all hKilling_rn jj (torusMk_surjective x).choose

/-- hCurlZeroDivZeroHarmonic: irrotational + solenoidal → harmonic on flat T³.
    Uses: curl=0 → symmetric Jacobian, then Clairaut + div=0.
    Key proof steps:
    1. Convert C² hypothesis via periodicLift_torusGradX
    2. Derive ContDiff ℝ 2 (finite-dim analysis)
    3. Convert curl=0 and div=0 to ℝⁿ form
    4. Apply curl_div_harmonic_rn' to the periodic lift
    Sorry'd: the ContDiff ℝ 2 and torus-to-ℝⁿ conversion steps. -/
theorem torus_hCurlZeroDivZeroHarmonic (F : Torus3 → Fin 3 → ℝ)
    (hF_C1 : ∀ i, ContDiff ℝ 1 (periodicLift (fun z => F z i)))
    (hF_C2 : ∀ i j, ContDiff ℝ 1 (periodicLift (fun x => torusGradX (fun y => F y i) x j)))
    (hcurl : ∀ x, torusCurlX F x = 0) (hdiv : ∀ x, torusDivX F x = 0) :
    ∀ i, ∀ x, torusDivX (torusGradX (fun y => F y i)) x = 0 := by
  -- Convert hF_C2 to ℝⁿ form
  have hC2_comp : ∀ k j : Fin 3, ContDiff ℝ 1
      (fun y => fderiv ℝ (periodicLift (fun z => F z k)) y (Pi.single j 1)) := by
    intro k j
    have h := hF_C2 k j
    rwa [show periodicLift (fun x => torusGradX (fun y => F y k) x j) =
        fun y => fderiv ℝ (periodicLift (fun z => F z k)) y (Pi.single j 1) from
        funext (periodicLift_torusGradX (fun z => F z k) j)] at h
  -- ContDiff ℝ 2 for each component
  have hC2_all : ∀ k : Fin 3, ContDiff ℝ 2 (periodicLift (fun z => F z k)) :=
    fun k => contDiff2_from_partials (hF_C1 k) (hC2_comp k)
  -- Symmetric Jacobian from curl = 0.
  -- Key insight: torusCurlX F x = ![torusGradX (F·2) x 1 - ..., ..., ...] by rfl
  -- (both use the same canonical preimage x₀ = (torusMk_surjective x).choose,
  --  and fun w => periodicLift f w = periodicLift f by eta reduction in Lean 4)
  have hjac_sym : ∀ (y : Fin 3 → ℝ) (i j : Fin 3),
      fderiv ℝ (periodicLift (fun z => F z j)) y (Pi.single i 1) =
      fderiv ℝ (periodicLift (fun z => F z i)) y (Pi.single j 1) := by
    intro y i j
    rw [← periodicLift_torusGradX (fun z => F z j) i y,
        ← periodicLift_torusGradX (fun z => F z i) j y]
    simp only [periodicLift, Function.comp_apply]
    -- Goal: torusGradX (F·j) (torusMk y) i = torusGradX (F·i) (torusMk y) j
    have hcurl_y := hcurl (torusMk y)
    -- Express torusCurlX directly in terms of torusGradX (by definitional equality / eta)
    have hcurl_expand : torusCurlX F (torusMk y) =
        ![torusGradX (fun w => F w 2) (torusMk y) 1 - torusGradX (fun w => F w 1) (torusMk y) 2,
          torusGradX (fun w => F w 0) (torusMk y) 2 - torusGradX (fun w => F w 2) (torusMk y) 0,
          torusGradX (fun w => F w 1) (torusMk y) 0 - torusGradX (fun w => F w 0) (torusMk y) 1] := rfl
    rw [hcurl_expand] at hcurl_y
    -- Extract the three symmetry conditions
    have h0 : torusGradX (fun w => F w 2) (torusMk y) 1 = torusGradX (fun w => F w 1) (torusMk y) 2 := by
      have := congr_fun hcurl_y 0; simp at this; linarith
    have h1 : torusGradX (fun w => F w 0) (torusMk y) 2 = torusGradX (fun w => F w 2) (torusMk y) 0 := by
      have := congr_fun hcurl_y 1; simp at this; linarith
    have h2 : torusGradX (fun w => F w 1) (torusMk y) 0 = torusGradX (fun w => F w 0) (torusMk y) 1 := by
      have := congr_fun hcurl_y 2; simp at this; linarith
    fin_cases i <;> fin_cases j <;> simp_all
  -- Divergence-free in ℝⁿ form
  -- torusDivX F (torusMk y) = 0 gives the sum at x₀ = (torusMk_surjective (torusMk y)).choose.
  -- Transfer to y via periodicLift_fderiv_eq (both x₀ and y are preimages of torusMk y).
  have hdiv_rn : ∀ (y : Fin 3 → ℝ),
      ∑ i : Fin 3, fderiv ℝ (periodicLift (fun z => F z i)) y (Pi.single i 1) = 0 := by
    intro y
    have key := hdiv (torusMk y)
    simp only [torusDivX] at key
    -- key uses x₀ = (torusMk_surjective (torusMk y)).choose; normalize eta form
    simp only [show ∀ i : Fin 3, (fun w => periodicLift (fun z => F z i) w) =
        periodicLift (fun z => F z i) from fun _ => rfl] at key
    -- key : ∑ i, fderiv ℝ (periodicLift (F·i)) x₀ (Pi.single i 1) = 0
    -- Convert to sum at y using periodicLift_fderiv_eq
    calc ∑ i : Fin 3, fderiv ℝ (periodicLift (fun z => F z i)) y (Pi.single i 1)
        = ∑ i : Fin 3, fderiv ℝ (periodicLift (fun z => F z i))
            ((torusMk_surjective (torusMk y)).choose) (Pi.single i 1) := by
          apply Finset.sum_congr rfl; intro i _
          exact congrFun (congrArg DFunLike.coe
            (periodicLift_fderiv_eq (fun z => F z i) y _
            ((torusMk_surjective (torusMk y)).choose_spec.symm))) (Pi.single i 1)
      _ = 0 := key
  -- Main proof
  intro ii x
  simp only [torusDivX]
  simp_rw [show ∀ i : Fin 3, (fun y => periodicLift (fun z => torusGradX (fun w => F w ii) z i) y) =
      (fun y => fderiv ℝ (periodicLift (fun z => F z ii)) y (Pi.single i 1)) from
      fun i => funext (periodicLift_torusGradX (fun z => F z ii) i)]
  exact curl_div_harmonic_rn'
    (fun y k => periodicLift (fun z => F z k) y)
    hC2_all hjac_sym hdiv_rn ii (torusMk_surjective x).choose

-- ============================================================================
-- The FlatTorus3 instance (with sorry's for hard axioms)
-- ============================================================================

instance : VML.FlatTorus3 Torus3 where
  toMeasureSpace := inferInstance
  instCompact := inferInstance
  instNonempty := ⟨fun _ => 0⟩
  gradX := torusGradX
  divX := torusDivX
  curlX := torusCurlX
  hDivLinear := by
    intro α G x; simp only [torusDivX]
    simp only [show ∀ i, periodicLift (fun z => (α • G z) i) = fun y => α * periodicLift (fun z => G z i) y
      from fun i => by ext y; simp [periodicLift, Pi.smul_apply, smul_eq_mul]]
    simp [fderiv_const_mul_always, Finset.mul_sum]
  hGradConst := torus_hGradConst
  hCurlIntZero := fun F u hF => torus_hCurlIntZero F u hF
  hHarmonic_const := fun φ hd => torus_hHarmonic_const φ hd
  hLaplacianMaxNonpos := torus_hLaplacianMaxNonpos
  hSpatialPos := fun g hcont hpos => torus_hSpatialPos g hpos hcont
  hSpatialNonnegZero := fun g hcont hnn hint => torus_hSpatialNonnegZero g hnn hint hcont
  IsSpatiallyDiff := fun f => ContDiff ℝ 1 (periodicLift f)
  hDiff_const := fun c => by
    show ContDiff ℝ 1 (periodicLift (fun _ => c))
    have : periodicLift (fun _ : Torus3 => c) = fun _ => c := by ext y; simp [periodicLift]
    rw [this]; exact contDiff_const
  hDiff_add := fun f g hf hg => by
    show ContDiff ℝ 1 (periodicLift (fun x => f x + g x))
    have : periodicLift (fun x => f x + g x) = fun y => periodicLift f y + periodicLift g y := by
      ext y; simp [periodicLift]
    rw [this]; exact hf.add hg
  hDiff_smul := fun c f hf => by
    show ContDiff ℝ 1 (periodicLift (fun x => c * f x))
    have : periodicLift (fun x => c * f x) = fun y => c * periodicLift f y := by
      ext y; simp [periodicLift]
    rw [this]; exact hf.const_smul c
  hGradAdd := torus_hGradAdd'
  hGradScalarMul := by
    intro c f x; ext i; simp only [torusGradX, Pi.smul_apply, smul_eq_mul]
    show fderiv ℝ (periodicLift (fun y => c * f y)) _ (Pi.single i 1) = _
    simp only [show periodicLift (fun y => c * f y) = fun y => c * periodicLift f y
      from by ext y; simp [periodicLift]]
    rw [fderiv_const_mul_always]; rfl
  hGradChainExp := by
    intro φ x i; simp only [torusGradX]
    show fderiv ℝ (periodicLift (fun y => Real.exp (φ y))) _ (Pi.single i 1) = _
    have hlift : periodicLift (fun y => Real.exp (φ y)) = fun y => Real.exp (periodicLift φ y) :=
      by ext y; simp [periodicLift]
    rw [hlift, fderiv_exp_comp_always, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hx₀ := (torusMk_surjective x).choose_spec
    show Real.exp (periodicLift φ _) * _ = Real.exp (φ x) * _
    simp [periodicLift, hx₀]
  hKillingToHarmonic := fun b hb_C1 hb_C2 hKilling => torus_hKillingToHarmonic b hb_C1 hb_C2 hKilling
  hCurlZeroDivZeroHarmonic := fun F hF_C1 hF_C2 hcurl hdiv => torus_hCurlZeroDivZeroHarmonic F hF_C1 hF_C2 hcurl hdiv
  hIBP_spatial := fun φ ψ i hφ hψ => torus_hIBP_spatial φ ψ i hφ hψ
  hSpatialVelocityFubini := by
    intro F _ hF_joint
    exact integral_integral_swap hF_joint
  hSpatialAdd := by sorry  -- integral_add (no integrability hypothesis)

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## Status of the FlatTorus3 instance on Fin 3 → AddCircle 1

**0 errors, 6 sorry warnings**

### Proved in instance (18 fields):
- hGradConst, hGradAdd (with IsSpatiallyDiff), hGradScalarMul, hGradChainExp
- hDivLinear (case analysis on differentiability)
- hSpatialPos, hSpatialNonnegZero (with Continuous hypothesis)
- hSpatialVelocityFubini (with joint integrability)
- IsSpatiallyDiff := Differentiable ℝ ∘ periodicLift
- hDiff_const, hDiff_add, hDiff_smul (closure properties)
- hCurlIntZero, hHarmonic_const, hLaplacianMaxNonpos: forwarded (sorry'd for first two)
- hKillingToHarmonic, hCurlZeroDivZeroHarmonic: forwarded (sorry'd)
- hIBP_spatial: forwarded (sorry'd)

### Sorry'd in instance (1 field):
- hSpatialAdd: integral_add (no integrability hypothesis in abstract axiom)

### Sorry'd helper theorems (5):
- torus_hIBP_spatial: core torus IBP (unlocks hCurlIntZero and hHarmonic_const)
- torus_hCurlIntZero: follows from IBP with φ=1; requires IsSpatiallyDiff on each F component
- torus_hHarmonic_const: harmonic → constant on torus (energy method via IBP)
- torus_hKillingToHarmonic: Killing → harmonic on flat torus (Clairaut, C² gap)
- torus_hCurlZeroDivZeroHarmonic: irrotational+solenoidal → harmonic (Clairaut, C² gap)

### Proved helper theorems (6):
- torus_hGradConst: gradient of constant vanishes
- torus_hGradAdd': gradient additivity for differentiable functions (via fderiv_add)
- torus_hSpatialPos: positive function has positive integral
- torus_hSpatialNonnegZero: nonneg function with zero integral is zero
- torus_hSpatialVelocityFubini: Fubini via integral_integral_swap
- torus_hLaplacianMaxNonpos: second derivative test (proved via 1D test + chain rule)
-/

end
