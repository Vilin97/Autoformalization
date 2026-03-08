/-
  Concrete instantiation of VelocityDecayConditions for a spatially uniform
  isotropic Maxwellian with E = 0, B = 0.

  This shows the hypothesis set of Theorem42 is satisfiable: there exists
  at least one (f, E, B) satisfying all hypotheses including the 15
  velocity-space decay conditions.

  For f(x,v) = exp(a + c|v|²) with c < 0:
  - The Landau flux vanishes: A(v-w)(v-w) = 0 (projection annihilation)
  - All spatial gradients vanish (f is constant in x)
  - All force terms vanish (E = 0, B = 0)
  Therefore every integrand in VelocityDecayConditions is identically 0.
-/
import Aristotle.Landau.main.Theorem42

set_option linter.all false
open Matrix Finset BigOperators Real MeasureTheory

noncomputable section
namespace VML

-- ============================================================================
-- The concrete distribution: spatially uniform isotropic Maxwellian
-- ============================================================================

/-- Spatially uniform isotropic Maxwellian: f(x,v) = exp(a + c|v|²). -/
def uniformMaxwellian (a c : ℝ) {X : Type*} (_ : X) (v : Fin 3 → ℝ) : ℝ :=
  Real.exp (a + c * normSq v)

/-- Zero field. -/
def zeroField {X : Type*} (_ : X) : Fin 3 → ℝ := 0

-- ============================================================================
-- Core algebraic lemmas
-- ============================================================================

variable {X : Type*} [FlatTorus3 X]

/-- The Landau flux vanishes for the uniform Maxwellian.
    Follows from maxwellian_landau_flux_zero with b = 0. -/
lemma uniformMaxwellian_flux_zero (Ψ : ℝ → ℝ) (a c : ℝ) (x : X) :
    ∀ v w, mulVec (landauMatrix Ψ (v - w))
      (uniformMaxwellian a c x w • vGrad (uniformMaxwellian a c x) v -
       uniformMaxwellian a c x v • vGrad (uniformMaxwellian a c x) w) = 0 := by
  have hf : ∀ v, uniformMaxwellian a c x v =
      Real.exp (a + dotProduct 0 v + c * normSq v) := by
    intro v; simp [uniformMaxwellian, dotProduct, Fin.sum_univ_three, normSq]
  exact maxwellian_landau_flux_zero Ψ (uniformMaxwellian a c x) a 0 c hf

/-- The integral of the Landau flux is 0 (since the integrand is pointwise 0). -/
lemma uniformMaxwellian_flux_integral_zero (Ψ : ℝ → ℝ) (a c : ℝ) (x : X) :
    ∀ v, (∫ w, mulVec (landauMatrix Ψ (v - w))
      (uniformMaxwellian a c x w • vGrad (uniformMaxwellian a c x) v -
       uniformMaxwellian a c x v • vGrad (uniformMaxwellian a c x) w)) = 0 := by
  intro v
  have : (fun w => mulVec (landauMatrix Ψ (v - w))
      (uniformMaxwellian a c x w • vGrad (uniformMaxwellian a c x) v -
       uniformMaxwellian a c x v • vGrad (uniformMaxwellian a c x) w)) = fun _ => 0 :=
    funext (fun w => uniformMaxwellian_flux_zero Ψ a c x v w)
  simp [this]

/-- The i-th component of the flux integral is 0. -/
lemma uniformMaxwellian_flux_component_zero (Ψ : ℝ → ℝ) (a c : ℝ) (x : X) :
    ∀ v i, (∫ w, mulVec (landauMatrix Ψ (v - w))
      (uniformMaxwellian a c x w • vGrad (uniformMaxwellian a c x) v -
       uniformMaxwellian a c x v • vGrad (uniformMaxwellian a c x) w)) i = 0 := by
  intro v i; rw [uniformMaxwellian_flux_integral_zero]; simp

/-- PSD integrand is 0 for the uniform Maxwellian.
    Key: the flux inner term is proportional to (v-w), and A(v-w)(v-w) = 0.
    Therefore the quadratic form vanishes. -/
lemma uniformMaxwellian_psd_zero (Ψ : ℝ → ℝ) (a c : ℝ) (x : X) :
    ∀ v w, PSDIntegrand Ψ (uniformMaxwellian a c x) v w = 0 := by
  intro v w
  unfold PSDIntegrand
  -- Strategy: show A(v-w) *ᵥ (∇log f(v) - ∇log f(w)) = 0
  -- from the flux zero and flux factoring.
  have hf_pos : ∀ u, 0 < uniformMaxwellian a c x u := fun u => Real.exp_pos _
  have hflux := uniformMaxwellian_flux_zero Ψ a c x v w
  have hfactor := analysis_fluxFactor (uniformMaxwellian a c x) hf_pos v w
  -- hflux : A *ᵥ (fw•∇fv - fv•∇fw) = 0
  -- hfactor : fw•∇fv - fv•∇fw = (fv*fw) • (∇log fv - ∇log fw)
  rw [hfactor] at hflux
  -- hflux : A *ᵥ ((fv*fw) • Δ) = 0 where Δ = ∇log fv - ∇log fw
  -- Pull scalar through mulVec: M *ᵥ (r • v) = r • (M *ᵥ v) for commutative ring
  set Δ := vGrad (Real.log ∘ uniformMaxwellian a c x) v -
            vGrad (Real.log ∘ uniformMaxwellian a c x) w
  have hmulvec_smul : mulVec (landauMatrix Ψ (v - w))
      ((uniformMaxwellian a c x v * uniformMaxwellian a c x w) • Δ) =
      (uniformMaxwellian a c x v * uniformMaxwellian a c x w) •
        mulVec (landauMatrix Ψ (v - w)) Δ := by
    ext i; simp [mulVec, dotProduct, smul_eq_mul, Finset.mul_sum]
    congr 1; ext j; ring
  rw [hmulvec_smul] at hflux
  -- hflux : (fv*fw) • (A *ᵥ Δ) = 0
  have hfvfw_ne : uniformMaxwellian a c x v * uniformMaxwellian a c x w ≠ 0 :=
    mul_ne_zero (ne_of_gt (hf_pos v)) (ne_of_gt (hf_pos w))
  have hAΔ : mulVec (landauMatrix Ψ (v - w)) Δ = 0 :=
    (smul_eq_zero.mp hflux).resolve_left hfvfw_ne
  rw [hAΔ, dotProduct_zero, mul_zero]

/-- Spatial gradient of the uniform Maxwellian is 0 (constant in x). -/
lemma uniformMaxwellian_gradX_zero (a c : ℝ) :
    ∀ (v : Fin 3 → ℝ) (x : X),
    FlatTorus3.gradX (fun y => uniformMaxwellian a c y v) x = 0 :=
  fun v => FlatTorus3.hGradConst _ (fun _ _ => rfl)

/-- Cross product with zero second argument is zero. -/
private lemma cross_zero_right' (v : Fin 3 → ℝ) : cross v (0 : Fin 3 → ℝ) = 0 := by
  ext i; fin_cases i <;> simp [cross]

-- Helper: zero field + cross v (zero field) = 0
private lemma force_zero (x : X) (v : Fin 3 → ℝ) :
    zeroField x + cross v (zeroField (X := X) x) = 0 := by
  simp [zeroField, cross_zero_right']

-- Helper: the flux function v ↦ (∫ w, ...) i is identically 0
private lemma flux_fn_eq_zero (Ψ : ℝ → ℝ) (a c : ℝ) (x : X) (i : Fin 3) :
    (fun v => (∫ w, mulVec (landauMatrix Ψ (v - w))
      (uniformMaxwellian a c x w • vGrad (uniformMaxwellian a c x) v -
       uniformMaxwellian a c x v • vGrad (uniformMaxwellian a c x) w)) i) =
    fun _ => (0 : ℝ) := by
  ext v; exact uniformMaxwellian_flux_component_zero Ψ a c x v i

-- ============================================================================
-- VelocityDecayConditions instance
-- ============================================================================

/-- The uniform Maxwellian with E = 0, B = 0 satisfies all velocity decay conditions.
    Every integrand is identically 0, so integrability is trivial. -/
def uniformMaxwellianDecay (Ψ : ℝ → ℝ) (a c : ℝ) (hc : c < 0)
    (hf_int : Integrable (fun v => Real.exp (a + c * normSq v))) :
    VelocityDecayConditions (X := X) Ψ (uniformMaxwellian a c) zeroField zeroField where
  hPSD_inner_int := by
    intro x v
    have : PSDIntegrand Ψ (uniformMaxwellian a c x) v = fun _ => 0 :=
      funext (uniformMaxwellian_psd_zero Ψ a c x v)
    rw [this]; exact integrable_zero _ _ _
  hPSD_outer_int := by
    intro x
    have : (fun v => ∫ w, PSDIntegrand Ψ (uniformMaxwellian a c x) v w) = fun _ => 0 := by
      ext v; have h := funext (uniformMaxwellian_psd_zero Ψ a c x v); simp [h]
    rw [this]; exact integrable_zero _ _ _
  hFubini_double := by
    intro x
    have : (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
        dotProduct (vGrad (Real.log ∘ uniformMaxwellian a c x) p.1)
          (mulVec (landauMatrix Ψ (p.1 - p.2))
            (uniformMaxwellian a c x p.2 • vGrad (uniformMaxwellian a c x) p.1 -
             uniformMaxwellian a c x p.1 • vGrad (uniformMaxwellian a c x) p.2))) =
        fun _ => 0 := by
      ext ⟨v, w⟩; simp only
      rw [uniformMaxwellian_flux_zero Ψ a c x v w]; simp [dotProduct]
    rw [this]; exact integrable_zero _ _ _
  hFubini_inner := by
    intro x v
    have : (fun w =>
        dotProduct (vGrad (Real.log ∘ uniformMaxwellian a c x) v)
          (mulVec (landauMatrix Ψ (v - w))
            (uniformMaxwellian a c x w • vGrad (uniformMaxwellian a c x) v -
             uniformMaxwellian a c x v • vGrad (uniformMaxwellian a c x) w))) =
        fun _ => 0 := by
      ext w; rw [uniformMaxwellian_flux_zero Ψ a c x v w]; simp [dotProduct]
    rw [this]; exact integrable_zero _ _ _
  hFubini_outer := by
    intro x
    have : (fun v => ∫ w,
        dotProduct (vGrad (Real.log ∘ uniformMaxwellian a c x) v)
          (mulVec (landauMatrix Ψ (v - w))
            (uniformMaxwellian a c x w • vGrad (uniformMaxwellian a c x) v -
             uniformMaxwellian a c x v • vGrad (uniformMaxwellian a c x) w))) =
        fun _ => 0 := by
      ext v
      have : (fun w =>
          dotProduct (vGrad (Real.log ∘ uniformMaxwellian a c x) v)
            (mulVec (landauMatrix Ψ (v - w))
              (uniformMaxwellian a c x w • vGrad (uniformMaxwellian a c x) v -
               uniformMaxwellian a c x v • vGrad (uniformMaxwellian a c x) w))) =
          fun _ => 0 := by
        ext w; rw [uniformMaxwellian_flux_zero Ψ a c x v w]; simp [dotProduct]
      simp [this]
    rw [this]; exact integrable_zero _ _ _
  hSpatialTransport_int := by
    intro x
    have : (fun v => v ⬝ᵥ FlatTorus3.gradX (fun y => uniformMaxwellian a c y v) x *
        Real.log (uniformMaxwellian a c x v)) = fun _ => 0 := by
      ext v; rw [uniformMaxwellian_gradX_zero]; simp [dotProduct]
    rw [this]; exact integrable_zero _ _ _
  hForceTransport_int := by
    intro x
    have : (fun v => (zeroField (X := X) x + cross v (zeroField x)) ⬝ᵥ
        vGrad (uniformMaxwellian a c x) v * Real.log (uniformMaxwellian a c x v)) =
        fun _ => 0 := by
      ext v; rw [force_zero]; simp [dotProduct]
    rw [this]; exact integrable_zero _ _ _
  hLandauFluxDiff := by
    intro x i; rw [flux_fn_eq_zero]; exact differentiable_const 0
  hLandauIBP_df_g := by
    intro x i
    have : (fun v => fderiv ℝ (fun v' => (∫ w, mulVec (landauMatrix Ψ (v' - w))
        (uniformMaxwellian a c x w • vGrad (uniformMaxwellian a c x) v' -
         uniformMaxwellian a c x v' • vGrad (uniformMaxwellian a c x) w)) i) v
        (Pi.single i 1) * (Real.log ∘ uniformMaxwellian a c x) v) = fun _ => 0 := by
      ext v; rw [flux_fn_eq_zero Ψ a c x i]; simp
    rw [this]; exact integrable_zero _ _ _
  hLandauIBP_f_dg := by
    intro x i
    have : (fun v => (∫ w, mulVec (landauMatrix Ψ (v - w))
        (uniformMaxwellian a c x w • vGrad (uniformMaxwellian a c x) v -
         uniformMaxwellian a c x v • vGrad (uniformMaxwellian a c x) w)) i *
        fderiv ℝ (Real.log ∘ uniformMaxwellian a c x) v (Pi.single i 1)) = fun _ => 0 := by
      ext v
      have h := uniformMaxwellian_flux_component_zero Ψ a c x v i
      rw [h]; simp
    rw [this]; exact integrable_zero _ _ _
  hLandauIBP_fg := by
    intro x i
    have : (fun v => (∫ w, mulVec (landauMatrix Ψ (v - w))
        (uniformMaxwellian a c x w • vGrad (uniformMaxwellian a c x) v -
         uniformMaxwellian a c x v • vGrad (uniformMaxwellian a c x) w)) i *
        (Real.log ∘ uniformMaxwellian a c x) v) = fun _ => 0 := by
      ext v
      have h := uniformMaxwellian_flux_component_zero Ψ a c x v i
      rw [h]; simp
    rw [this]; exact integrable_zero _ _ _
  hLandauFluxInt := by
    intro x v
    have : (fun w => mulVec (landauMatrix Ψ (v - w))
        (uniformMaxwellian a c x w • vGrad (uniformMaxwellian a c x) v -
         uniformMaxwellian a c x v • vGrad (uniformMaxwellian a c x) w)) = fun _ => 0 :=
      funext (uniformMaxwellian_flux_zero Ψ a c x v)
    rw [this]; exact integrable_zero _ _ _
  hForceIBP_f_dg := by
    intro x i
    have : (fun v => (zeroField (X := X) x + cross v (zeroField x)) i *
        fderiv ℝ (fun w => uniformMaxwellian a c x w *
          Real.log (uniformMaxwellian a c x w) - uniformMaxwellian a c x w) v
          (Pi.single i 1)) = fun _ => 0 := by
      ext v; rw [force_zero]; simp
    rw [this]; exact integrable_zero _ _ _
  hForceIBP_fg := by
    intro x i
    have : (fun v => (zeroField (X := X) x + cross v (zeroField x)) i *
        (uniformMaxwellian a c x v * Real.log (uniformMaxwellian a c x v) -
         uniformMaxwellian a c x v)) = fun _ => 0 := by
      ext v; rw [force_zero]; simp
    rw [this]; exact integrable_zero _ _ _
  hSpatialTransport_joint := by
    have : (Function.uncurry (fun (x : X) (v : Fin 3 → ℝ) =>
        v ⬝ᵥ FlatTorus3.gradX (fun y => uniformMaxwellian a c y v) x *
        Real.log (uniformMaxwellian a c x v))) = fun _ => 0 := by
      ext ⟨x, v⟩; simp [Function.uncurry, uniformMaxwellian_gradX_zero, dotProduct]
    rw [this]; exact integrable_zero _ _ _
  hSpatTransComp := by
    intro v i
    have : (fun (x : X) => FlatTorus3.gradX (fun y => uniformMaxwellian a c y v) x i *
        Real.log (uniformMaxwellian a c x v)) = fun _ => 0 := by
      ext x; simp [uniformMaxwellian_gradX_zero]
    rw [this]; exact integrable_zero _ _ _
  hf_velocity_dominated := by
    -- f(x,v) = exp(a + c|v|²) is independent of x, so g = f
    exact ⟨fun v => Real.exp (a + c * normSq v), hf_int, fun _ _ => le_refl _⟩
  hD_cont := by
    show Continuous (fun (_ : X) => entropyDissipation Ψ (fun v => Real.exp (a + c * normSq v)))
    exact continuous_const

-- ============================================================================
-- Schwartz-class VelocityDecayConditions (non-circular)
--
-- For a positive smooth function φ with Schwartz-like decay, bounded Ψ,
-- and polynomial growth of ∇ log φ and log φ, all 15 velocity decay
-- conditions are satisfied. Unlike the Maxwellian instance above, the
-- Landau flux does NOT vanish for non-Maxwellian φ — the collision
-- integrands are genuinely non-zero.
-- ============================================================================

-- Helper lemmas: polynomial × Schwartz decay is integrable
-- Proved by Aristotle (Harmonic)

/-- If ‖v‖^k * |φ(v)| is integrable for every k, then (1+‖v‖)^K * |φ(v)| is too.
    Uses the binomial theorem to expand (1+‖v‖)^K as a finite sum. -/
private lemma integrable_one_add_norm_pow_mul
    {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    (K : ℕ) :
    Integrable (fun v => (1 + ‖v‖) ^ K * |φ v|) := by
  have h_binom : ∀ v : (Fin 3 → ℝ), (1 + ‖v‖) ^ K * |φ v| =
      ∑ k ∈ Finset.range (K + 1), Nat.choose K k * ‖v‖ ^ k * |φ v| := by
    simp +decide [add_comm (1 : ℝ), add_pow, mul_assoc, mul_comm, mul_left_comm,
      Finset.mul_sum _ _ _]
  simp_rw [h_binom]
  exact MeasureTheory.integrable_finset_sum _ fun k _ => by
    simpa only [mul_assoc] using MeasureTheory.Integrable.const_mul (hφ k) _

/-- If ‖v‖^k * |φ(v)| is integrable for every k, and ‖g(v)‖ ≤ C*(1+‖v‖)^K*|φ(v)|,
    then g is integrable. Core tool for Schwartz-dominance arguments. -/
private lemma integrable_of_schwartz_bound
    {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    {g : (Fin 3 → ℝ) → ℝ}
    (hg_meas : AEStronglyMeasurable g)
    {C : ℝ} (_ : 0 ≤ C) {K : ℕ}
    (hbound : ∀ v, ‖g v‖ ≤ C * (1 + ‖v‖) ^ K * |φ v|) :
    Integrable g := by
  have hdom : Integrable (fun v => C * ((1 + ‖v‖) ^ K * |φ v|)) :=
    (integrable_one_add_norm_pow_mul hφ K).const_mul C
  exact hdom.mono' hg_meas (by
    filter_upwards with v
    calc ‖g v‖ ≤ C * (1 + ‖v‖) ^ K * |φ v| := hbound v
    _ = C * ((1 + ‖v‖) ^ K * |φ v|) := by ring)

-- Helper lemmas for bounding collision integrands.
-- All proved by Aristotle (Harmonic); proofs to be ported.

/-- ‖α • a - β • b‖ ≤ |α| * ‖a‖ + |β| * ‖b‖. -/
private lemma norm_smul_sub_le_of_smul (a b : Fin 3 → ℝ) (α β : ℝ) :
    ‖α • a - β • b‖ ≤ |α| * ‖a‖ + |β| * ‖b‖ :=
  calc ‖α • a - β • b‖ ≤ ‖α • a‖ + ‖β • b‖ := norm_sub_le _ _
  _ = |α| * ‖a‖ + |β| * ‖b‖ := by simp [norm_smul]

/-- ‖M *ᵥ u‖ ≤ 3 * B * ‖u‖ when all |M i j| ≤ B (for 3×3 matrices). -/
private lemma norm_mulVec_le_of_entry_bound (M : Matrix (Fin 3) (Fin 3) ℝ)
    (u : Fin 3 → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hM : ∀ i j, |M i j| ≤ B) :
    ‖mulVec M u‖ ≤ 3 * B * ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  simp only [mulVec, dotProduct]
  calc |∑ j : Fin 3, M i j * u j|
      ≤ ∑ j : Fin 3, |M i j * u j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, B * ‖u‖ := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul (hM i j) (norm_le_pi_norm u j) (abs_nonneg _) hB
    _ = 3 * B * ‖u‖ := by simp [Fin.sum_univ_three]; ring

/-- Each entry of innerLandauMatrix z is bounded by normSq z. -/
private lemma innerLandauMatrix_entry_le (z : Fin 3 → ℝ) (i j : Fin 3) :
    |innerLandauMatrix z i j| ≤ normSq z := by
  rw [innerLandauMatrix_apply]
  have hns : normSq z = ∑ k : Fin 3, z k * z k := by
    simp [normSq, dotProduct, Fin.sum_univ_three]
  split_ifs with hij
  · -- diagonal: |normSq z - zᵢ * zᵢ| ≤ normSq z
    subst hij
    rw [hns]; simp only [Fin.sum_univ_three]
    fin_cases i <;> simp <;> (rw [abs_of_nonneg (by nlinarith [mul_self_nonneg (z 0), mul_self_nonneg (z 1), mul_self_nonneg (z 2)])]; nlinarith [mul_self_nonneg (z 0), mul_self_nonneg (z 1), mul_self_nonneg (z 2)])
  · -- off-diagonal: |0 - zᵢ * zⱼ| ≤ normSq z
    simp only [zero_sub, abs_neg]
    rw [hns]; simp only [Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp_all <;>
      nlinarith [sq_nonneg (|z 0| - |z 1|), sq_nonneg (|z 0| - |z 2|),
        sq_nonneg (|z 1| - |z 2|),
        abs_mul_abs_self (z 0), abs_mul_abs_self (z 1), abs_mul_abs_self (z 2)]

/-- Bound on landauMatrix entries: |A(z)_{ij}| ≤ CΨ * normSq z. -/
private lemma landauMatrix_entry_le (Ψ : ℝ → ℝ) {CΨ : ℝ} (hΨ : ∀ r, |Ψ r| ≤ CΨ)
    (z : Fin 3 → ℝ) (i j : Fin 3) :
    |landauMatrix Ψ z i j| ≤ CΨ * normSq z := by
  simp only [landauMatrix, smul_apply, smul_eq_mul]
  calc |Ψ (eucNorm z) * innerLandauMatrix z i j|
      = |Ψ (eucNorm z)| * |innerLandauMatrix z i j| := abs_mul _ _
    _ ≤ CΨ * normSq z := by
        exact mul_le_mul (hΨ _) (innerLandauMatrix_entry_le z i j)
          (abs_nonneg _) (le_trans (abs_nonneg _) (hΨ 0))

/-- Vector-valued Schwartz bound: if ‖v‖^k * |φ(v)| is integrable for every k,
    and ‖g(v)‖ ≤ C * (1+‖v‖)^K * |φ(v)|, then g is integrable. -/
private lemma integrable_of_schwartz_bound_vec
    {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    {m : ℕ} {g : (Fin 3 → ℝ) → (Fin m → ℝ)}
    (hg_meas : AEStronglyMeasurable g)
    {C : ℝ} (hC : 0 ≤ C) {K : ℕ}
    (hbound : ∀ v, ‖g v‖ ≤ C * (1 + ‖v‖) ^ K * |φ v|) :
    Integrable g := by
  refine' MeasureTheory.Integrable.mono' _ hg_meas _
  refine' fun v => C * (∑ k ∈ Finset.range (K + 1), Nat.choose K k * ‖v‖ ^ k) * |φ v|
  · simp +decide only [Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc]
    exact MeasureTheory.integrable_finset_sum _ fun i _ =>
      MeasureTheory.Integrable.const_mul (MeasureTheory.Integrable.const_mul (hφ i) _) _
  · filter_upwards with v using le_trans (hbound v) (by
      rw [add_comm, add_pow]
      simp +decide [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _])

/-- Product-space integrability from Schwartz decay:
    if |g(v,w)| ≤ C * (1+‖v‖)^K₁ * |φ(v)| * (1+‖w‖)^K₂ * |φ(w)|,
    then g is integrable on the product space. -/
private lemma integrable_prod_schwartz_bound
    {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    {g : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ}
    (hg_meas : AEStronglyMeasurable g (volume.prod volume))
    {C : ℝ} (hC : 0 ≤ C) {K₁ K₂ : ℕ}
    (hbound : ∀ v w, |g (v, w)| ≤ C * ((1 + ‖v‖) ^ K₁ * |φ v|) *
      ((1 + ‖w‖) ^ K₂ * |φ w|)) :
    Integrable g (volume.prod volume) := by
  have h_integrable : Integrable (fun (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) =>
      C * ((1 + ‖p.1‖) ^ K₁ * |φ p.1|) * ((1 + ‖p.2‖) ^ K₂ * |φ p.2|))
      (volume.prod volume) := by
    suffices h : Integrable (fun v => (1 + ‖v‖) ^ K₁ * |φ v|) ∧
        Integrable (fun w => (1 + ‖w‖) ^ K₂ * |φ w|) by
      convert h.1.prod_mul h.2 |> fun h => h.const_mul C using 1; ring!
    exact ⟨integrable_one_add_norm_pow_mul hφ K₁, integrable_one_add_norm_pow_mul hφ K₂⟩
  exact h_integrable.mono' hg_meas (Filter.Eventually.of_forall fun p => hbound p.1 p.2)

/-- Product-space integrability (vector-valued) from Schwartz decay.
    Proved by Aristotle (Harmonic). -/
private lemma integrable_prod_schwartz_bound_vec
    {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    {m : ℕ} {g : (Fin 3 → ℝ) × (Fin 3 → ℝ) → (Fin m → ℝ)}
    (hg_meas : AEStronglyMeasurable g (volume.prod volume))
    {C : ℝ} (hC : 0 ≤ C) {K₁ K₂ : ℕ}
    (hbound : ∀ v w, ‖g (v, w)‖ ≤ C * ((1 + ‖v‖) ^ K₁ * |φ v|) *
      ((1 + ‖w‖) ^ K₂ * |φ w|)) :
    Integrable g (volume.prod volume) := by
  have h_integrable_prod : Integrable (fun (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) =>
      C * ((1 + ‖p.1‖) ^ K₁ * |φ p.1|) * ((1 + ‖p.2‖) ^ K₂ * |φ p.2|))
      (volume.prod volume) := by
    suffices h : Integrable (fun v => (1 + ‖v‖) ^ K₁ * |φ v|) ∧
        Integrable (fun w => (1 + ‖w‖) ^ K₂ * |φ w|) by
      convert h.1.prod_mul h.2 |> fun h => h.const_mul C using 1; ring!
    exact ⟨integrable_one_add_norm_pow_mul hφ K₁, integrable_one_add_norm_pow_mul hφ K₂⟩
  refine' h_integrable_prod.mono' hg_meas _
  exact Filter.Eventually.of_forall fun p => hbound p.1 p.2

/-- Integrability of iterated integral from Schwartz decay.
    Proved by Aristotle (Harmonic). -/
private lemma integrable_integral_schwartz
    {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    {g : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ}
    (hg_int : ∀ v, Integrable (g v))
    (hg_meas : AEStronglyMeasurable (fun v => ∫ w, g v w))
    {C : ℝ} (hC : 0 ≤ C) {K₁ K₂ : ℕ}
    (hbound : ∀ v w, |g v w| ≤ C * ((1 + ‖v‖) ^ K₁ * |φ v|) *
      ((1 + ‖w‖) ^ K₂ * |φ w|)) :
    Integrable (fun v => ∫ w, g v w) := by
  refine' (((integrable_one_add_norm_pow_mul hφ K₁).const_mul C).mul_const
    (∫ w, (1 + ‖w‖) ^ K₂ * |φ w|)).mono' hg_meas _
  filter_upwards with v
  exact le_trans (norm_integral_le_integral_norm _) (by
    rw [← integral_const_mul]
    exact integral_mono (hg_int v).norm
      ((integrable_one_add_norm_pow_mul hφ K₂).const_mul _)
      (fun w => by
        rw [Real.norm_eq_abs]
        exact le_trans (hbound v w) (by ring_nf; rfl)))

/-- Differentiation under the integral sign for Schwartz-dominated integrands.
    Uses `hasFDerivAt_integral_of_dominated_of_fderiv_le` from Mathlib. -/
private lemma differentiable_integral_of_schwartz_dominated
    {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    {g : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ}
    (hg_diff : ∀ w, Differentiable ℝ (fun v => g v w))
    (hg_int : ∀ v, Integrable (g v))
    {C : ℝ} {K : ℕ}
    (hderiv_bound : ∀ v w, ‖fderiv ℝ (fun v' => g v' w) v‖ ≤
      C * (1 + ‖w‖) ^ K * |φ w|)
    (hderiv_int : ∀ v, Integrable (fun w => fderiv ℝ (fun v' => g v' w) v)) :
    Differentiable ℝ (fun v => ∫ w, g v w) := by
  intro v₀
  have hbound_int : Integrable (fun w => C * (1 + ‖w‖) ^ K * |φ w|) := by
    convert (integrable_one_add_norm_pow_mul hφ K).const_mul C using 1; ext; ring
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun v w => fderiv ℝ (fun v' => g v' w) v)
    (ε := 1) one_pos
    (Filter.Eventually.of_forall fun v => (hg_int v).aestronglyMeasurable)
    (hg_int v₀)
    (hderiv_int v₀).aestronglyMeasurable
    (ae_of_all _ fun w v _ => hderiv_bound v w)
    hbound_int
    (ae_of_all _ fun w v _ => (hg_diff w).differentiableAt.hasFDerivAt)).differentiableAt

/-- Differentiation under the integral sign with product-form bound.

    Unlike `differentiable_integral_of_schwartz_dominated`, this allows the derivative
    bound to depend on v: ‖D_v g(v,w)‖ ≤ P(v) * Q(w) where P is continuous and
    Q is integrable. The proof localizes to a compact ball around each v₀ where
    P is bounded. -/
private lemma differentiable_integral_of_product_dominated
    {g : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ}
    (hg_diff : ∀ w, Differentiable ℝ (fun v => g v w))
    (hg_int : ∀ v, Integrable (g v))
    {P : (Fin 3 → ℝ) → ℝ} (hP : Continuous P)
    {Q : (Fin 3 → ℝ) → ℝ} (hQ_int : Integrable Q) (hQ_nn : ∀ w, 0 ≤ Q w)
    (hderiv_bound : ∀ v w, ‖fderiv ℝ (fun v' => g v' w) v‖ ≤ P v * Q w)
    (hderiv_int : ∀ v, Integrable (fun w => fderiv ℝ (fun v' => g v' w) v)) :
    Differentiable ℝ (fun v => ∫ w, g v w) := by
  intro v₀
  -- P is continuous → bounded on compact ball
  have hP_bound : ∃ M, ∀ v ∈ Metric.closedBall v₀ 1, P v ≤ M := by
    have := isCompact_closedBall (x := v₀) (α := Fin 3 → ℝ) 1
    exact ⟨sSup (P '' Metric.closedBall v₀ 1),
      fun v hv => le_csSup (this.image hP).bddAbove ⟨v, hv, rfl⟩⟩
  obtain ⟨M, hM⟩ := hP_bound
  -- Bound in ball: ‖D_v g(v,w)‖ ≤ M * Q(w)
  have hball_bound : ∀ w, ∀ v ∈ Metric.ball v₀ 1,
      ‖fderiv ℝ (fun v' => g v' w) v‖ ≤ M * Q w := fun w v hv => by
    exact le_trans (hderiv_bound v w) (mul_le_mul_of_nonneg_right
      (hM v (Metric.ball_subset_closedBall hv)) (hQ_nn w))
  have hdom_int : Integrable (fun w => M * Q w) := hQ_int.const_mul M
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun v w => fderiv ℝ (fun v' => g v' w) v)
    (ε := 1) one_pos
    (Filter.Eventually.of_forall fun v => (hg_int v).aestronglyMeasurable)
    (hg_int v₀)
    (hderiv_int v₀).aestronglyMeasurable
    (ae_of_all _ fun w v hv => hball_bound w v hv)
    hdom_int
    (ae_of_all _ fun w v _ => (hg_diff w).differentiableAt.hasFDerivAt)).differentiableAt

/-- ∂(log ∘ φ)/∂vᵢ = (∂φ/∂vᵢ) / φ(v) when φ is differentiable and positive. -/
private lemma vGrad_log_eq_div {φ : (Fin 3 → ℝ) → ℝ}
    (hφ_diff : Differentiable ℝ φ) (hφ_pos : ∀ v, 0 < φ v)
    (v : Fin 3 → ℝ) (i : Fin 3) :
    fderiv ℝ (Real.log ∘ φ) v (Pi.single i 1) =
      fderiv ℝ φ v (Pi.single i 1) / φ v := by
  erw [fderiv_comp] <;> norm_num [hφ_diff.differentiableAt, hφ_pos, ne_of_gt]; ring!

/-- ‖v - w‖² ≤ 2 * (‖v‖² + ‖w‖²). -/
private lemma norm_sub_sq_le_two_mul (v w : Fin 3 → ℝ) :
    ‖v - w‖ ^ 2 ≤ 2 * (‖v‖ ^ 2 + ‖w‖ ^ 2) :=
  le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le v w) 2)
    (by linarith [sq_nonneg (‖v‖ - ‖w‖)])

/-- normSq z ≤ 3 * ‖z‖² (dotProduct z z ≤ n * sup_norm²). -/
private lemma normSq_le_three_mul_sq_norm (z : Fin 3 → ℝ) :
    normSq z ≤ 3 * ‖z‖ ^ 2 := by
  simp [normSq, dotProduct, Fin.sum_univ_three]
  have h : ∀ i : Fin 3, z i * z i ≤ ‖z‖ ^ 2 := fun i =>
    calc z i * z i = |z i| * |z i| := (abs_mul_abs_self (z i)).symm
    _ ≤ ‖z‖ * ‖z‖ := mul_le_mul (norm_le_pi_norm z i) (norm_le_pi_norm z i)
        (abs_nonneg _) (norm_nonneg _)
    _ = ‖z‖ ^ 2 := (sq ‖z‖).symm
  linarith [h 0, h 1, h 2]

/-- The pi norm of vGrad φ is bounded by C*(1+‖v‖)^K*φ(v) when we have a per-component bound. -/
private lemma vGrad_norm_le {φ : (Fin 3 → ℝ) → ℝ} {C : ℝ} {K : ℕ}
    (hbound : ∀ v i, |fderiv ℝ φ v (Pi.single i 1)| ≤ C * (1 + ‖v‖) ^ K * φ v)
    (v : Fin 3 → ℝ) :
    ‖vGrad φ v‖ ≤ C * (1 + ‖v‖) ^ K * φ v := by
  apply (pi_norm_le_iff_of_nonneg (le_trans (abs_nonneg _) (hbound v 0))).2
  intro i; exact hbound v i

/-- Pointwise norm bound on the Landau flux integrand:
  ‖A(v-w)(φ(w)∇φ(v) - φ(v)∇φ(w))‖ ≤ 18CΨCg(1+‖v‖)^{Kg+2}φ(v)(1+‖w‖)^{Kg+2}φ(w). -/
private lemma landau_flux_pointwise_bound
    {Ψ : ℝ → ℝ} {φ : (Fin 3 → ℝ) → ℝ}
    {CΨ : ℝ} (hCΨ : ∀ r, |Ψ r| ≤ CΨ) (hCΨ_nn : 0 ≤ CΨ)
    {Cg : ℝ} {Kg : ℕ}
    (hCg : ∀ v i, |fderiv ℝ φ v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * φ v)
    (hCg_nn : 0 ≤ Cg) (hφ_pos : ∀ v, 0 < φ v)
    (v w : Fin 3 → ℝ) :
    ‖landauMatrix Ψ (v - w) *ᵥ (φ w • vGrad φ v - φ v • vGrad φ w)‖ ≤
      18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v *
        ((1 + ‖w‖) ^ (Kg + 2) * φ w) := by
  have h1 := norm_mulVec_le_of_entry_bound (landauMatrix Ψ (v - w))
    (φ w • vGrad φ v - φ v • vGrad φ w)
    (mul_nonneg hCΨ_nn (normSq_nonneg _)) (landauMatrix_entry_le Ψ hCΨ (v - w))
  have h2 := normSq_le_three_mul_sq_norm (v - w)
  have h3 := norm_smul_sub_le_of_smul (vGrad φ v) (vGrad φ w) (φ w) (φ v)
  rw [abs_of_pos (hφ_pos w), abs_of_pos (hφ_pos v)] at h3
  have h4 := vGrad_norm_le hCg v
  have h5 := vGrad_norm_le hCg w
  have h6 : ‖v - w‖ ^ 2 ≤ (1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ 2 := by
    have : ‖v - w‖ ≤ (1 + ‖v‖) * (1 + ‖w‖) :=
      le_trans (norm_sub_le v w) (by nlinarith [norm_nonneg v, norm_nonneg w])
    calc ‖v - w‖ ^ 2 ≤ ((1 + ‖v‖) * (1 + ‖w‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := by ring
  have h_ns : normSq (v - w) ≤ 3 * ((1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ 2) :=
    le_trans h2 (by linarith)
  have h_u : ‖φ w • vGrad φ v - φ v • vGrad φ w‖ ≤
      Cg * φ v * φ w * ((1 + ‖v‖) ^ Kg + (1 + ‖w‖) ^ Kg) := by
    calc _ ≤ φ w * (Cg * (1 + ‖v‖) ^ Kg * φ v) +
             φ v * (Cg * (1 + ‖w‖) ^ Kg * φ w) :=
          le_trans h3 (add_le_add
            (mul_le_mul_of_nonneg_left h4 (le_of_lt (hφ_pos w)))
            (mul_le_mul_of_nonneg_left h5 (le_of_lt (hφ_pos v))))
      _ = _ := by ring
  have h7 : (1 + ‖w‖) ^ 2 ≤ (1 + ‖w‖) ^ (Kg + 2) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg w]) (by omega)
  have h8 : (1 + ‖v‖) ^ 2 ≤ (1 + ‖v‖) ^ (Kg + 2) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg v]) (by omega)
  have hpv : (1 + ‖v‖) ^ (Kg + 2) = (1 + ‖v‖) ^ 2 * (1 + ‖v‖) ^ Kg := by ring
  have hpw : (1 + ‖w‖) ^ (Kg + 2) = (1 + ‖w‖) ^ 2 * (1 + ‖w‖) ^ Kg := by ring
  have hcross1 : (1 + ‖v‖) ^ (Kg + 2) * (1 + ‖w‖) ^ 2 ≤
      (1 + ‖v‖) ^ (Kg + 2) * (1 + ‖w‖) ^ (Kg + 2) :=
    mul_le_mul_of_nonneg_left h7 (pow_nonneg (by linarith [norm_nonneg v]) _)
  have hcross2 : (1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ (Kg + 2) ≤
      (1 + ‖v‖) ^ (Kg + 2) * (1 + ‖w‖) ^ (Kg + 2) :=
    mul_le_mul_of_nonneg_right h8 (pow_nonneg (by linarith [norm_nonneg w]) _)
  calc ‖landauMatrix Ψ (v - w) *ᵥ (φ w • vGrad φ v - φ v • vGrad φ w)‖
      ≤ 3 * (CΨ * normSq (v - w)) * ‖φ w • vGrad φ v - φ v • vGrad φ w‖ := h1
    _ ≤ 3 * (CΨ * (3 * ((1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ 2))) *
          (Cg * φ v * φ w * ((1 + ‖v‖) ^ Kg + (1 + ‖w‖) ^ Kg)) := by gcongr
    _ = 9 * CΨ * Cg * φ v * φ w *
          ((1 + ‖v‖) ^ 2 * (1 + ‖v‖) ^ Kg * (1 + ‖w‖) ^ 2 +
           (1 + ‖v‖) ^ 2 * ((1 + ‖w‖) ^ 2 * (1 + ‖w‖) ^ Kg)) := by ring
    _ = 9 * CΨ * Cg * φ v * φ w *
          ((1 + ‖v‖) ^ (Kg + 2) * (1 + ‖w‖) ^ 2 +
           (1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ (Kg + 2)) := by rw [hpv, hpw]
    _ ≤ 9 * CΨ * Cg * φ v * φ w *
          ((1 + ‖v‖) ^ (Kg + 2) * (1 + ‖w‖) ^ (Kg + 2) +
           (1 + ‖v‖) ^ (Kg + 2) * (1 + ‖w‖) ^ (Kg + 2)) := by
        have : 0 ≤ 9 * CΨ * Cg * φ v * φ w := by
          apply mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hCΨ_nn) hCg_nn)
            (le_of_lt (hφ_pos v))) (le_of_lt (hφ_pos w))
        gcongr
    _ = 18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v *
          ((1 + ‖w‖) ^ (Kg + 2) * φ w) := by ring

/-- Continuity of the Landau flux integrand in w. -/
private lemma landau_flux_continuous_w
    {Ψ : ℝ → ℝ} (hΨ_cts : Continuous Ψ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ_smooth : ContDiff ℝ ⊤ φ)
    (v : Fin 3 → ℝ) :
    Continuous (fun w => landauMatrix Ψ (v - w) *ᵥ
      (φ w • vGrad φ v - φ v • vGrad φ w)) := by
  have hcsub : Continuous (fun w => v - w) := continuous_const.sub continuous_id
  apply Continuous.matrix_mulVec
  · simp only [landauMatrix]
    apply Continuous.smul
    · simp only [eucNorm]
      exact hΨ_cts.comp (Real.continuous_sqrt.comp (Continuous.dotProduct hcsub hcsub))
    · simp only [innerLandauMatrix]
      exact ((Continuous.dotProduct hcsub hcsub).smul continuous_const).sub
        (Continuous.matrix_vecMulVec hcsub hcsub)
  · apply Continuous.sub
    · exact hφ_smooth.continuous.smul continuous_const
    · exact continuous_const.smul (continuous_pi fun i =>
        (ContDiff.continuous_fderiv (hφ_smooth.of_le le_top) le_rfl).clm_apply continuous_const)

/-- Joint continuity of the Landau flux integrand in (v,w). -/
private lemma landau_flux_continuous_joint
    {Ψ : ℝ → ℝ} (hΨ_cts : Continuous Ψ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ_smooth : ContDiff ℝ ⊤ φ) :
    Continuous (fun (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) =>
      landauMatrix Ψ (p.1 - p.2) *ᵥ
        (φ p.2 • vGrad φ p.1 - φ p.1 • vGrad φ p.2)) := by
  have hcsub : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 - p.2) :=
    continuous_fst.sub continuous_snd
  apply Continuous.matrix_mulVec
  · simp only [landauMatrix]
    apply Continuous.smul
    · simp only [eucNorm]
      exact hΨ_cts.comp (Real.continuous_sqrt.comp (Continuous.dotProduct hcsub hcsub))
    · simp only [innerLandauMatrix]
      exact ((Continuous.dotProduct hcsub hcsub).smul continuous_const).sub
        (Continuous.matrix_vecMulVec hcsub hcsub)
  · apply Continuous.sub
    · exact (hφ_smooth.continuous.comp continuous_snd).smul
        (continuous_pi fun i =>
          (ContDiff.continuous_fderiv (hφ_smooth.of_le le_top) le_rfl).comp continuous_fst
            |>.clm_apply continuous_const)
    · exact (hφ_smooth.continuous.comp continuous_fst).smul
        (continuous_pi fun i =>
          (ContDiff.continuous_fderiv (hφ_smooth.of_le le_top) le_rfl).comp continuous_snd
            |>.clm_apply continuous_const)

/-- AEStronglyMeasurable for the Landau flux integral as a function of v. -/
private lemma landau_flux_integral_aestronglyMeasurable
    {Ψ : ℝ → ℝ} (hΨ_cts : Continuous Ψ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ_smooth : ContDiff ℝ ⊤ φ) :
    AEStronglyMeasurable (fun v => ∫ w, landauMatrix Ψ (v - w) *ᵥ
      (φ w • vGrad φ v - φ v • vGrad φ w)) volume :=
  (landau_flux_continuous_joint hΨ_cts hφ_smooth).aestronglyMeasurable.integral_prod_right'

/-- Spatial gradient of any spatially-constant function is 0. -/
private lemma gradX_const_fun (g : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) (x : X) :
    FlatTorus3.gradX (fun (_ : X) => g v) x = 0 :=
  FlatTorus3.hGradConst _ (fun _ _ => rfl) x

/-- Grad-log bound: ‖∇(log∘φ)(v)‖ ≤ Cg*(1+‖v‖)^Kg from grad/value bound. -/
private lemma vGrad_log_norm_le {φ : (Fin 3 → ℝ) → ℝ}
    (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_pos : ∀ v, 0 < φ v)
    {Cg : ℝ} {Kg : ℕ} (hCg_nn : 0 ≤ Cg)
    (hCg : ∀ v i, |fderiv ℝ φ v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * φ v)
    (v : Fin 3 → ℝ) :
    ‖vGrad (Real.log ∘ φ) v‖ ≤ Cg * (1 + ‖v‖) ^ Kg := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hCg_nn
    (pow_nonneg (by linarith [norm_nonneg v]) _))).2
  intro i
  simp only [vGrad]
  rw [vGrad_log_eq_div (hφ_smooth.differentiable le_top) hφ_pos v i,
      Real.norm_eq_abs, abs_div, abs_of_pos (hφ_pos v)]
  exact div_le_of_le_mul₀ (le_of_lt (hφ_pos v))
    (mul_nonneg hCg_nn (pow_nonneg (by linarith [norm_nonneg v]) _)) (hCg v i)

/-- Flux integrability for Schwartz-class φ. -/
private lemma schwartz_flux_integrable
    {Ψ : ℝ → ℝ} (hΨ : ∃ CΨ, ∀ r, |Ψ r| ≤ CΨ) (hΨ_cts : Continuous Ψ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ_pos : ∀ v, 0 < φ v) (hφ_smooth : ContDiff ℝ ⊤ φ)
    (hφ_decay : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    (hGradBound : ∃ C K, ∀ v i,
      |fderiv ℝ φ v (Pi.single i 1)| ≤ C * (1 + ‖v‖) ^ K * φ v)
    (v : Fin 3 → ℝ) :
    Integrable (fun w => landauMatrix Ψ (v - w) *ᵥ
      (φ w • vGrad φ v - φ v • vGrad φ w)) := by
  obtain ⟨CΨ, hCΨ⟩ := hΨ
  obtain ⟨Cg, Kg, hCg⟩ := hGradBound
  have hCΨ_nn : 0 ≤ CΨ := le_trans (abs_nonneg _) (hCΨ 0)
  have hCg_nn : 0 ≤ Cg := by
    have h := hCg 0 0; simp only [norm_zero, add_zero, one_pow] at h
    nlinarith [abs_nonneg (fderiv ℝ φ 0 (Pi.single 0 1)), hφ_pos 0]
  set C0 := 18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v
  have hdom : Integrable (fun w => C0 * ((1 + ‖w‖) ^ (Kg + 2) * |φ w|)) :=
    (integrable_one_add_norm_pow_mul hφ_decay (Kg + 2)).const_mul C0
  refine hdom.mono' (landau_flux_continuous_w hΨ_cts hφ_smooth v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [abs_of_pos (hφ_pos w)]
  exact landau_flux_pointwise_bound hCΨ hCΨ_nn hCg hCg_nn hφ_pos v w

/-- Flux integral norm bound: ‖∫ w, flux(v,w)‖ ≤ Cf*(1+‖v‖)^(Kg+2)*φ(v). -/
private lemma schwartz_flux_integral_bound
    {Ψ : ℝ → ℝ} (hΨ_cts : Continuous Ψ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ_pos : ∀ v, 0 < φ v) (hφ_smooth : ContDiff ℝ ⊤ φ)
    (hφ_decay : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    {CΨ Cg : ℝ} {Kg : ℕ}
    (hCΨ : ∀ r, |Ψ r| ≤ CΨ)
    (hCg : ∀ v i, |fderiv ℝ φ v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * φ v)
    (hCΨ_nn : 0 ≤ CΨ)
    (hCg_nn : 0 ≤ Cg)
    (v : Fin 3 → ℝ) :
    ‖∫ w, landauMatrix Ψ (v - w) *ᵥ
      (φ w • vGrad φ v - φ v • vGrad φ w)‖ ≤
    (18 * CΨ * Cg * (∫ w, (1 + ‖w‖) ^ (Kg + 2) * |φ w|)) *
      (1 + ‖v‖) ^ (Kg + 2) * φ v := by
  calc ‖∫ w, landauMatrix Ψ (v - w) *ᵥ
          (φ w • vGrad φ v - φ v • vGrad φ w)‖
      ≤ ∫ w, ‖landauMatrix Ψ (v - w) *ᵥ
          (φ w • vGrad φ v - φ v • vGrad φ w)‖ :=
        norm_integral_le_integral_norm (μ := volume) _
    _ ≤ ∫ w, (18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v *
          ((1 + ‖w‖) ^ (Kg + 2) * |φ w|)) := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun w => norm_nonneg _)
          ((integrable_one_add_norm_pow_mul hφ_decay (Kg + 2)).const_mul _)
          (Filter.Eventually.of_forall fun w =>
            le_trans (landau_flux_pointwise_bound hCΨ hCΨ_nn hCg hCg_nn hφ_pos v w)
              (by apply mul_le_mul_of_nonneg_left
                  · exact mul_le_mul_of_nonneg_left (le_abs_self _)
                      (pow_nonneg (by linarith [norm_nonneg w]) _)
                  · apply mul_nonneg _ (le_of_lt (hφ_pos v))
                    apply mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hCΨ_nn) hCg_nn)
                      (pow_nonneg (by linarith [norm_nonneg v]) _)))
    _ = 18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v *
          (∫ w, (1 + ‖w‖) ^ (Kg + 2) * |φ w|) := integral_mul_left _ _
    _ = _ := by ring

/-- Dot product bound: |⟨c, u⟩| ≤ 3*‖c‖*‖u‖ for Fin 3 → ℝ (sup norm). -/
private lemma abs_dotProduct_le (c u : Fin 3 → ℝ) :
    |dotProduct c u| ≤ 3 * ‖c‖ * ‖u‖ := by
  simp only [dotProduct]
  rw [← Real.norm_eq_abs]
  calc ‖∑ i : Fin 3, c i * u i‖
      ≤ ∑ i : Fin 3, ‖c i * u i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖c‖ * ‖u‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_mul]; exact mul_le_mul (norm_le_pi_norm c i) (norm_le_pi_norm u i)
          (norm_nonneg _) (norm_nonneg _)
    _ = 3 * ‖c‖ * ‖u‖ := by simp [Fin.sum_univ_three]; ring

/-- Fubini integrand pointwise bound. Combines dotProduct bound + flux bound + grad-log bound. -/
private lemma fubini_integrand_bound
    {Ψ : ℝ → ℝ} {φ : (Fin 3 → ℝ) → ℝ}
    (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_pos : ∀ v, 0 < φ v)
    {CΨ : ℝ} (hCΨ : ∀ r, |Ψ r| ≤ CΨ) (hCΨ_nn : 0 ≤ CΨ)
    {Cg : ℝ} {Kg : ℕ}
    (hCg : ∀ v i, |fderiv ℝ φ v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * φ v)
    (hCg_nn : 0 ≤ Cg)
    (v w : Fin 3 → ℝ) :
    |dotProduct (vGrad (Real.log ∘ φ) v)
      (landauMatrix Ψ (v - w) *ᵥ
        (φ w • vGrad φ v - φ v • vGrad φ w))| ≤
    (54 * CΨ * Cg ^ 2) * ((1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|) *
      ((1 + ‖w‖) ^ (Kg + 2) * |φ w|) := by
  calc |dotProduct (vGrad (Real.log ∘ φ) v)
        (landauMatrix Ψ (v - w) *ᵥ (φ w • vGrad φ v - φ v • vGrad φ w))|
      ≤ 3 * ‖vGrad (Real.log ∘ φ) v‖ *
        ‖landauMatrix Ψ (v - w) *ᵥ (φ w • vGrad φ v - φ v • vGrad φ w)‖ :=
      abs_dotProduct_le _ _
    _ ≤ 3 * (Cg * (1 + ‖v‖) ^ Kg) *
        (18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v *
          ((1 + ‖w‖) ^ (Kg + 2) * φ w)) := by
      gcongr
      · exact vGrad_log_norm_le hφ_smooth hφ_pos hCg_nn hCg v
      · exact landau_flux_pointwise_bound hCΨ hCΨ_nn hCg hCg_nn hφ_pos v w
    _ = (54 * CΨ * Cg ^ 2) * ((1 + ‖v‖) ^ (2 * Kg + 2) * φ v) *
        ((1 + ‖w‖) ^ (Kg + 2) * φ w) := by
      rw [show 2 * Kg + 2 = Kg + (Kg + 2) from by omega, pow_add]; ring
    _ ≤ (54 * CΨ * Cg ^ 2) * ((1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|) *
        ((1 + ‖w‖) ^ (Kg + 2) * |φ w|) := by
      rw [abs_of_pos (hφ_pos v), abs_of_pos (hφ_pos w)]

/-- Continuity of vGrad in the v argument. -/
private lemma continuous_vGrad {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ ⊤ f) (i : Fin 3) :
    Continuous (fun v => vGrad f v i) := by
  simp only [vGrad]
  exact (ContDiff.continuous_fderiv (hf.of_le le_top) le_rfl).clm_apply continuous_const

/-- Joint continuity of the Fubini integrand ⟨∇logφ(v), flux(v,w)⟩. -/
private lemma fubini_integrand_continuous
    {Ψ : ℝ → ℝ} (hΨ_cts : Continuous Ψ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_pos : ∀ v, 0 < φ v) :
    Continuous (fun (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) =>
      dotProduct (vGrad (Real.log ∘ φ) p.1)
        (landauMatrix Ψ (p.1 - p.2) *ᵥ
          (φ p.2 • vGrad φ p.1 - φ p.1 • vGrad φ p.2))) := by
  simp only [dotProduct, Fin.sum_univ_three]
  refine Continuous.add (Continuous.add ?_ ?_) ?_ <;>
    exact ((continuous_vGrad (hφ_smooth.log (fun v => ne_of_gt (hφ_pos v))) _).comp
      continuous_fst).mul
      ((continuous_apply _).comp (landau_flux_continuous_joint hΨ_cts hφ_smooth))

/-- Joint continuity of the PSD integrand in (v, w). -/
private lemma psd_integrand_continuous_joint
    {Ψ : ℝ → ℝ} (hΨ_cts : Continuous Ψ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_pos : ∀ v, 0 < φ v) :
    Continuous (fun (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) => PSDIntegrand Ψ φ p.1 p.2) := by
  unfold PSDIntegrand
  have h_log_smooth := hφ_smooth.log (fun v => ne_of_gt (hφ_pos v))
  have hΔ : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      vGrad (Real.log ∘ φ) p.1 - vGrad (Real.log ∘ φ) p.2) :=
    (continuous_pi fun i => (continuous_vGrad h_log_smooth i).comp continuous_fst).sub
      (continuous_pi fun i => (continuous_vGrad h_log_smooth i).comp continuous_snd)
  have hcsub : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 - p.2) :=
    continuous_fst.sub continuous_snd
  have hA : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => landauMatrix Ψ (p.1 - p.2)) := by
    simp only [landauMatrix]; apply Continuous.smul
    · simp only [eucNorm]
      exact hΨ_cts.comp (Real.continuous_sqrt.comp (Continuous.dotProduct hcsub hcsub))
    · simp only [innerLandauMatrix]
      exact ((Continuous.dotProduct hcsub hcsub).smul continuous_const).sub
        (Continuous.matrix_vecMulVec hcsub hcsub)
  exact ((hφ_smooth.continuous.comp continuous_fst).mul (hφ_smooth.continuous.comp continuous_snd)).mul
    (Continuous.dotProduct hΔ (hA.matrix_mulVec hΔ))

/-- PSD integrand pointwise bound. -/
private lemma psd_integrand_bound
    {Ψ : ℝ → ℝ} {φ : (Fin 3 → ℝ) → ℝ}
    (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_pos : ∀ v, 0 < φ v)
    {CΨ : ℝ} (hCΨ : ∀ r, |Ψ r| ≤ CΨ) (hCΨ_nn : 0 ≤ CΨ)
    {Cg : ℝ} {Kg : ℕ}
    (hCg : ∀ v i, |fderiv ℝ φ v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * φ v)
    (hCg_nn : 0 ≤ Cg)
    (v w : Fin 3 → ℝ) :
    |PSDIntegrand Ψ φ v w| ≤
    (108 * CΨ * Cg ^ 2) * ((1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|) *
      ((1 + ‖w‖) ^ (2 * Kg + 2) * |φ w|) := by
  unfold PSDIntegrand
  set Δ := vGrad (Real.log ∘ φ) v - vGrad (Real.log ∘ φ) w
  rw [abs_mul, abs_mul, abs_of_pos (hφ_pos v), abs_of_pos (hφ_pos w)]
  -- Step 1: |⟨Δ, AΔ⟩| ≤ 9*CΨ*normSq(v-w)*‖Δ‖²
  have h_dot : |dotProduct Δ (landauMatrix Ψ (v - w) *ᵥ Δ)| ≤
      9 * CΨ * normSq (v - w) * ‖Δ‖ ^ 2 := by
    calc _ ≤ 3 * ‖Δ‖ * ‖landauMatrix Ψ (v - w) *ᵥ Δ‖ := abs_dotProduct_le _ _
      _ ≤ 3 * ‖Δ‖ * (3 * (CΨ * normSq (v - w)) * ‖Δ‖) := by
        gcongr; exact norm_mulVec_le_of_entry_bound _ _
          (mul_nonneg hCΨ_nn (normSq_nonneg _)) (landauMatrix_entry_le _ hCΨ _)
      _ = _ := by ring
  -- Step 2: normSq(v-w) ≤ 3*(1+‖v‖)²*(1+‖w‖)²
  have h_nsq : normSq (v - w) ≤ 3 * (1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ 2 := by
    calc normSq (v - w) ≤ 3 * ‖v - w‖ ^ 2 := normSq_le_three_mul_sq_norm _
      _ ≤ 3 * ((1 + ‖v‖) * (1 + ‖w‖)) ^ 2 := by
        gcongr; exact le_trans (norm_sub_le v w)
          (by nlinarith [norm_nonneg v, norm_nonneg w])
      _ = _ := by ring
  -- Step 3: ‖Δ‖ ≤ 2*Cg*(1+‖v‖)^Kg*(1+‖w‖)^Kg
  have h_delta : ‖Δ‖ ≤ 2 * Cg * (1 + ‖v‖) ^ Kg * (1 + ‖w‖) ^ Kg := by
    have hv := vGrad_log_norm_le hφ_smooth hφ_pos hCg_nn hCg v
    have hw := vGrad_log_norm_le hφ_smooth hφ_pos hCg_nn hCg w
    have hv1 : 1 ≤ (1 + ‖v‖) ^ Kg :=
      one_le_pow₀ (by linarith [norm_nonneg v])
    have hw1 : 1 ≤ (1 + ‖w‖) ^ Kg :=
      one_le_pow₀ (by linarith [norm_nonneg w])
    calc ‖Δ‖ ≤ ‖vGrad (Real.log ∘ φ) v‖ + ‖vGrad (Real.log ∘ φ) w‖ := norm_sub_le _ _
      _ ≤ Cg * (1 + ‖v‖) ^ Kg + Cg * (1 + ‖w‖) ^ Kg := add_le_add hv hw
      _ ≤ Cg * (1 + ‖v‖) ^ Kg * (1 + ‖w‖) ^ Kg +
          Cg * (1 + ‖v‖) ^ Kg * (1 + ‖w‖) ^ Kg := by
        apply add_le_add
        · exact le_mul_of_one_le_right (mul_nonneg hCg_nn (pow_nonneg (by linarith [norm_nonneg v]) _)) hw1
        · calc Cg * (1 + ‖w‖) ^ Kg = Cg * 1 * (1 + ‖w‖) ^ Kg := by ring
            _ ≤ Cg * (1 + ‖v‖) ^ Kg * (1 + ‖w‖) ^ Kg := by
              gcongr
      _ = _ := by ring
  -- Combine: |PSD| ≤ φv * φw * 9*CΨ * 3*(1+‖v‖)²*(1+‖w‖)² * (2*Cg*(1+‖v‖)^Kg*(1+‖w‖)^Kg)²
  --               = 108*CΨ*Cg² * (1+‖v‖)^(2Kg+2)*φv * (1+‖w‖)^(2Kg+2)*φw
  have h_Δ_sq : ‖Δ‖ ^ 2 ≤ 4 * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg) * (1 + ‖w‖) ^ (2 * Kg) := by
    calc ‖Δ‖ ^ 2 ≤ (2 * Cg * (1 + ‖v‖) ^ Kg * (1 + ‖w‖) ^ Kg) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h_delta 2
      _ = 4 * Cg ^ 2 * ((1 + ‖v‖) ^ Kg) ^ 2 * ((1 + ‖w‖) ^ Kg) ^ 2 := by ring
      _ = 4 * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg) * (1 + ‖w‖) ^ (2 * Kg) := by
        simp only [← pow_mul]; ring
  -- Bound |⟨Δ,AΔ⟩| independently
  have h_mid : |dotProduct Δ (landauMatrix Ψ (v - w) *ᵥ Δ)| ≤
      108 * CΨ * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg + 2) * (1 + ‖w‖) ^ (2 * Kg + 2) := by
    calc _ ≤ 9 * CΨ * normSq (v - w) * ‖Δ‖ ^ 2 := h_dot
      _ ≤ 9 * CΨ * (3 * (1 + ‖v‖) ^ 2 * (1 + ‖w‖) ^ 2) *
          (4 * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg) * (1 + ‖w‖) ^ (2 * Kg)) := by
        gcongr
      _ = _ := by
        rw [show 2 * Kg + 2 = 2 + 2 * Kg from by omega]; simp only [pow_add]; ring
  -- Multiply by φ v * φ w (left-associated from abs_mul)
  calc φ v * φ w * |dotProduct Δ (landauMatrix Ψ (v - w) *ᵥ Δ)|
      ≤ φ v * φ w * (108 * CΨ * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg + 2) *
          (1 + ‖w‖) ^ (2 * Kg + 2)) :=
        mul_le_mul_of_nonneg_left h_mid
          (mul_nonneg (le_of_lt (hφ_pos v)) (le_of_lt (hφ_pos w)))
    _ = (108 * CΨ * Cg ^ 2) * ((1 + ‖v‖) ^ (2 * Kg + 2) * φ v) *
        ((1 + ‖w‖) ^ (2 * Kg + 2) * φ w) := by ring


set_option maxHeartbeats 800000 in
/-- Each entry of the Landau matrix A_{ij}(v-w) is differentiable in v.
    At z ≠ 0: composition of C¹ functions (Ψ ∘ ‖·‖ smooth, polynomial smooth).
    At z = 0: A_{ij}(0) = 0 and |A_{ij}(z)| ≤ CΨ·2‖z‖², giving hasFDerivAt 0.
    Proved by Aristotle. -/
private lemma landauMatrix_entry_differentiable
    {Ψ : ℝ → ℝ} (hΨ_diff : ContDiff ℝ 1 Ψ) (hΨ_bound : ∃ CΨ, ∀ r, |Ψ r| ≤ CΨ)
    (w : Fin 3 → ℝ) (i j : Fin 3) :
    Differentiable ℝ (fun v => landauMatrix Ψ (v - w) i j) := by
  -- Proved by Aristotle (job 648b5b5b).
  unfold landauMatrix eucNorm normSq
  have h_combined : Differentiable ℝ (fun v : (Fin 3) → ℝ => Ψ (Real.sqrt ((v - w) ⬝ᵥ (v - w))) * (Real.sqrt ((v - w) ⬝ᵥ (v - w))^2 * (if i = j then 1 else 0) - (v - w) i * (v - w) j)) := by
    intro v
    by_cases hv : v = w
    · refine' ⟨ _, hasFDerivAt_iff_isLittleO_nhds_zero.mpr _ ⟩
      exact 0
      have h_bound : ∀ h : Fin 3 → ℝ, abs (Ψ (Real.sqrt ((h ⬝ᵥ h))) * ((Real.sqrt ((h ⬝ᵥ h)) ^ 2 * (if i = j then 1 else 0) - h i * h j))) ≤ hΨ_bound.choose * 2 * (‖h‖ ^ 2) := by
        intro h
        have h_bound : abs ((Real.sqrt ((h ⬝ᵥ h)) ^ 2 * (if i = j then 1 else 0) - h i * h j)) ≤ 2 * (‖h‖ ^ 2) := by
          split_ifs <;> norm_num [ Real.sq_sqrt ( show 0 ≤ h ⬝ᵥ h by exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _ ) ]
          · simp_all +decide [ dotProduct, Fin.sum_univ_three ]
            fin_cases j <;> norm_num [ Norm.norm ] <;> ring_nf <;> norm_num [ abs_le ]
            · norm_num [ Fin.univ_succ ]
              constructor <;> nlinarith only [ abs_le.mp ( show |h 0| ≤ Max.max |h 0| ( Max.max |h 1| |h 2| ) by exact le_max_left _ _ ), abs_le.mp ( show |h 1| ≤ Max.max |h 0| ( Max.max |h 1| |h 2| ) by exact le_max_of_le_right ( le_max_left _ _ ) ), abs_le.mp ( show |h 2| ≤ Max.max |h 0| ( Max.max |h 1| |h 2| ) by exact le_max_of_le_right ( le_max_right _ _ ) ) ]
            · norm_num [ Fin.univ_succ ]
              constructor <;> nlinarith only [ abs_le.mp ( show |h 0| ≤ Max.max |h 0| ( Max.max |h 1| |h 2| ) by exact le_max_left _ _ ), abs_le.mp ( show |h 1| ≤ Max.max |h 0| ( Max.max |h 1| |h 2| ) by exact le_max_of_le_right ( le_max_left _ _ ) ), abs_le.mp ( show |h 2| ≤ Max.max |h 0| ( Max.max |h 1| |h 2| ) by exact le_max_of_le_right ( le_max_right _ _ ) ) ]
            · norm_num [ Fin.univ_succ ]
              constructor <;> nlinarith! [ abs_le.mp ( le_max_left |h 0| ( Max.max |h 1| |h 2| ) ), abs_le.mp ( le_max_right |h 0| ( Max.max |h 1| |h 2| ) |> le_trans ( le_max_left |h 1| |h 2| ) ), abs_le.mp ( le_max_right |h 0| ( Max.max |h 1| |h 2| ) |> le_trans ( le_max_right |h 1| |h 2| ) ) ]
          · nlinarith only [ abs_nonneg ( h i ), abs_nonneg ( h j ), show |h i| ≤ ‖h‖ from by simpa using norm_le_pi_norm h i, show |h j| ≤ ‖h‖ from by simpa using norm_le_pi_norm h j ]
        simpa only [ mul_assoc, abs_mul ] using mul_le_mul ( hΨ_bound.choose_spec _ ) h_bound ( by positivity ) ( by linarith [ abs_le.mp ( hΨ_bound.choose_spec ( Real.sqrt ( h ⬝ᵥ h ) ) ) ] )
      rw [ Asymptotics.isLittleO_iff ]
      intro ε ε_pos; filter_upwards [ Metric.ball_mem_nhds _ ( show 0 < ε / ( hΨ_bound.choose * 2 + 1 ) by exact div_pos ε_pos ( by linarith [ show 0 ≤ hΨ_bound.choose by exact le_trans ( abs_nonneg _ ) ( hΨ_bound.choose_spec 0 ) ] ) ) ] with x hx; simp_all +decide [ abs_mul, abs_of_nonneg, add_nonneg ]
      rw [ lt_div_iff₀ ] at hx <;> nlinarith [ h_bound x, show 0 ≤ hΨ_bound.choose by exact le_trans ( abs_nonneg _ ) ( hΨ_bound.choose_spec 0 ), norm_nonneg x ]
    · refine' DifferentiableAt.mul _ _
      · refine' DifferentiableAt.comp v ( hΨ_diff.contDiffAt.differentiableAt ( by norm_num ) ) _
        refine' DifferentiableAt.sqrt _ _ <;> norm_num [ hv, dotProduct ]
        · fun_prop (disch := norm_num)
        · exact fun h => hv <| by ext x; fin_cases x <;> norm_num [ Fin.sum_univ_three ] at * <;> nlinarith!
      · refine' DifferentiableAt.sub _ _
        · refine' DifferentiableAt.mul _ _
          · refine' DifferentiableAt.pow _ _
            refine' DifferentiableAt.sqrt _ _ <;> norm_num [ dotProduct ]
            · fun_prop (disch := norm_num)
            · exact fun h => hv <| by ext x; fin_cases x <;> norm_num [ Fin.sum_univ_three ] at * <;> nlinarith!
          · norm_num
        · fun_prop
  convert h_combined using 1 ; norm_num [ innerLandauMatrix, Matrix.mulVec, dotProduct ] ; ring!
  ext; norm_num [ Matrix.vecMulVec, normSq ] ; ring
  rw [ Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => by nlinarith only [ sq_nonneg ( ( ‹Fin 3 → ℝ› ) ‹_› - w ‹_› ) ] ) ] ; simp +decide [ Fin.sum_univ_three, dotProduct ] ; ring
  fin_cases i <;> fin_cases j <;> simp +decide [ Matrix.one_apply ] <;> ring!

/-- The Landau flux integrand component is differentiable in v with a product-form bound.

    This is the key analysis lemma for flux differentiability. For each fixed w:
    - g_i(v,w) = (A(v-w) *ᵥ (φ(w)·∇φ(v) - φ(v)·∇φ(w)))_i is differentiable in v
    - ‖D_v g_i(v,w)‖ ≤ C · (1+‖v‖)^M · φ(v) · (1+‖w‖)^M · |φ(w)|

    The differentiability follows from:
    - Away from v = w: Ψ ∘ ‖·‖ is C¹ (since ‖·‖ smooth for z ≠ 0 and Ψ is C¹)
    - At v = w: A(0) *ᵥ Δ(w,w) = 0 and the integrand is O(‖v-w‖³) (bounded Ψ × vanishing A × vanishing Δ)
    - The bound combines the Landau matrix bound (O(‖v-w‖²)), gradient bounds, and Schwartz decay. -/
private lemma landau_flux_component_diff_with_bound
    {Ψ : ℝ → ℝ} (hΨ : ∃ CΨ, ∀ r, |Ψ r| ≤ CΨ) (hΨ_cts : Continuous Ψ)
    (hΨ_diff : ContDiff ℝ 1 Ψ) (hΨ'_bound : ∃ CΨ', ∀ r, |deriv Ψ r| ≤ CΨ')
    {φ : (Fin 3 → ℝ) → ℝ} (hφ_pos : ∀ v, 0 < φ v) (hφ_smooth : ContDiff ℝ ⊤ φ)
    (hφ_decay : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    -- Pointwise second derivative bound: |∂²φ/∂vⱼ∂vₖ(v)| ≤ C₂(1+‖v‖)^K₂ × φ(v)
    -- Natural for Schwartz-class functions (e.g. exp(-|v|⁴) gives K₂ = 6)
    (hφ_deriv2_bound : ∃ C₂ K₂, ∀ v (j : Fin 3),
      ‖fderiv ℝ (fun v' => fderiv ℝ φ v' (Pi.single j 1)) v‖ ≤ C₂ * (1 + ‖v‖) ^ K₂ * φ v)
    (hGradBound : ∃ C K, ∀ v i,
      |fderiv ℝ φ v (Pi.single i 1)| ≤ C * (1 + ‖v‖) ^ K * φ v)
    (i : Fin 3) :
    -- (1) Differentiable in v for each w
    (∀ w, Differentiable ℝ (fun v =>
      (landauMatrix Ψ (v - w) *ᵥ (φ w • vGrad φ v - φ v • vGrad φ w)) i)) ∧
    -- (2) Product-form derivative bound
    (∃ C₀ M, ∀ v w, ‖fderiv ℝ (fun v' =>
      (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v‖ ≤
      C₀ * ((1 + ‖v‖) ^ M * φ v) * ((1 + ‖w‖) ^ M * |φ w|)) ∧
    -- (3) Derivative integrable for each v
    (∀ v, Integrable (fun w => fderiv ℝ (fun v' =>
      (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v)) ∧
    -- (4) Flux integral derivative has Schwartz bound (for IBP integrability)
    (∃ C₁ M₁, ∀ v, ‖fderiv ℝ (fun v' =>
      ∫ w, (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v‖ ≤
      C₁ * (1 + ‖v‖) ^ M₁ * φ v) := by
  obtain ⟨CΨ, hCΨ⟩ := hΨ
  obtain ⟨CΨ', hCΨ'⟩ := hΨ'_bound
  obtain ⟨Cg, Kg, hCg⟩ := hGradBound
  obtain ⟨C₂, K₂, hC₂⟩ := hφ_deriv2_bound
  have hCΨ_nn : 0 ≤ CΨ := le_trans (abs_nonneg _) (hCΨ 0)
  have hCg_nn : 0 ≤ Cg := by
    have h := hCg 0 0; simp only [norm_zero, add_zero, one_pow] at h
    nlinarith [abs_nonneg (fderiv ℝ φ 0 (Pi.single 0 1)), hφ_pos 0]
  have hC₂_nn : 0 ≤ C₂ := by
    have h := hC₂ 0 0; simp only [norm_zero, add_zero, one_pow] at h
    nlinarith [norm_nonneg (fderiv ℝ (fun v' => fderiv ℝ φ v' (Pi.single 0 1)) 0), hφ_pos 0]
  -- Helper: ∂_j φ is differentiable (φ is C^∞)
  have hφ_deriv_diff : ∀ j : Fin 3,
      Differentiable ℝ (fun v => fderiv ℝ φ v (Pi.single j 1)) :=
    fun j => ((contDiff_succ_iff_fderiv_apply.mp
      (hφ_smooth.of_le le_top : ContDiff ℝ (1 + 1) φ)).2.2
      (Pi.single j 1)).differentiable le_rfl
  -- Helper: the flux integrand component as a finite sum
  have hsum_eq : ∀ v w, (landauMatrix Ψ (v - w) *ᵥ
      (φ w • vGrad φ v - φ v • vGrad φ w)) i =
    ∑ j : Fin 3, landauMatrix Ψ (v - w) i j *
      (φ w * fderiv ℝ φ v (Pi.single j 1) - φ v * fderiv ℝ φ w (Pi.single j 1)) := by
    intro v w
    simp only [Matrix.mulVec, dotProduct, vGrad, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  -- Part 1: Differentiable in v for each w
  -- Each A_{ij}(v-w) differentiable by landauMatrix_entry_differentiable,
  -- each D_j(v,w) differentiable since φ is C^∞, so (A *ᵥ D)_i = ∑ A_{ij}*D_j is diff.
  have hpart1 : ∀ w, Differentiable ℝ (fun v =>
      (landauMatrix Ψ (v - w) *ᵥ (φ w • vGrad φ v - φ v • vGrad φ w)) i) := by
    intro w v
    show DifferentiableAt ℝ (fun v => (landauMatrix Ψ (v - w) *ᵥ
        (φ w • vGrad φ v - φ v • vGrad φ w)) i) v
    simp only [Matrix.mulVec, dotProduct, vGrad, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Fin.sum_univ_three]
    have hmul : ∀ j : Fin 3, DifferentiableAt ℝ (fun v =>
        landauMatrix Ψ (v - w) i j *
          (φ w * fderiv ℝ φ v (Pi.single j 1) - φ v * fderiv ℝ φ w (Pi.single j 1))) v :=
      fun j => (landauMatrix_entry_differentiable hΨ_diff ⟨CΨ, hCΨ⟩ w i j v).mul
        (((hφ_deriv_diff j v).const_mul (φ w)).sub
          ((hφ_smooth.differentiable le_top v).mul_const (fderiv ℝ φ w (Pi.single j 1))))
    exact ((hmul 0).add (hmul 1)).add (hmul 2)
  -- Parts 2-4: Product-form derivative bound, integrability, and integral interchange.
  -- These follow from: (a) product rule for fderiv of A_{ij} × (φ·∇φ) terms,
  -- (b) quadratic bound ‖D A_{ij}(z)‖ ≤ C(1+‖z‖)² (submitted to Aristotle),
  -- (c) AEStronglyMeasurable of fderiv (continuity in w of the explicit product-rule expression),
  -- (d) hasFDerivAt_integral_of_dominated_of_fderiv_le (Mathlib parametric differentiation).
  have hparts234 :
      (∃ C₀ M, ∀ v w, ‖fderiv ℝ (fun v' =>
        (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v‖ ≤
        C₀ * ((1 + ‖v‖) ^ M * φ v) * ((1 + ‖w‖) ^ M * |φ w|)) ∧
      (∀ v, Integrable (fun w => fderiv ℝ (fun v' =>
        (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v)) ∧
      (∃ C₁ M₁, ∀ v, ‖fderiv ℝ (fun v' =>
        ∫ w, (landauMatrix Ψ (v' - w) *ᵥ (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v‖ ≤
        C₁ * (1 + ‖v‖) ^ M₁ * φ v) := by
    sorry
  exact ⟨hpart1, hparts234.1, hparts234.2.1, hparts234.2.2⟩

/-- **VelocityDecayConditions for Schwartz-class distributions.**

    Demonstrates the velocity decay conditions are satisfiable by a broad
    class of positive smooth functions with sufficient decay — not just
    Maxwellians. The hypotheses are standard in kinetic theory:

    - φ > 0, smooth, with ‖v‖^k × |φ(v)| integrable for all k (Schwartz decay)
    - Ψ bounded (finite-range interaction kernel)
    - |∂φ/∂vᵢ| ≤ C(1+‖v‖)^K × φ (gradient-to-value bound)
    - |log φ| ≤ C(1+‖v‖)^K (φ doesn't decay super-exponentially)

    For non-Maxwellian φ (e.g. φ(v) = exp(-|v|⁴)), the collision integrands
    are genuinely non-zero. Integrability follows from the general principle:
    Schwartz decay × polynomial growth = integrable. -/
def schwartzDecayConditions {X : Type*} [FlatTorus3 X]
    (Ψ : ℝ → ℝ) (hΨ : ∃ CΨ, ∀ r, |Ψ r| ≤ CΨ) (hΨ_cts : Continuous Ψ)
    -- Ψ is C¹ with bounded derivative (needed for flux differentiability)
    (hΨ_diff : ContDiff ℝ 1 Ψ) (hΨ'_bound : ∃ CΨ', ∀ r, |deriv Ψ r| ≤ CΨ')
    (φ : (Fin 3 → ℝ) → ℝ)
    (hφ_pos : ∀ v, 0 < φ v)
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    -- Schwartz decay: polynomial × |φ| and polynomial × |∂φ| integrable
    (hφ_decay : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    (hφ_deriv_decay : ∀ (k : ℕ) (i : Fin 3),
      Integrable (fun v => ‖v‖ ^ k * |fderiv ℝ φ v (Pi.single i 1)|))
    -- Second derivative bound: |∂²φ/∂vⱼ∂vₖ| ≤ C₂(1+‖v‖)^K₂ × φ(v)
    (hφ_deriv2_bound : ∃ C₂ K₂, ∀ v (j : Fin 3),
      ‖fderiv ℝ (fun v' => fderiv ℝ φ v' (Pi.single j 1)) v‖ ≤ C₂ * (1 + ‖v‖) ^ K₂ * φ v)
    -- Gradient bound: |∂φ/∂vᵢ| ≤ C(1+‖v‖)^K × φ (equiv: ∇ log φ polynomial)
    (hGradBound : ∃ C K, ∀ v i,
      |fderiv ℝ φ v (Pi.single i 1)| ≤ C * (1 + ‖v‖) ^ K * φ v)
    -- Log bound: |log φ| ≤ C(1+‖v‖)^K (equiv: φ ≥ exp(-polynomial))
    (hLogBound : ∃ C K, ∀ v, |Real.log (φ v)| ≤ C * (1 + ‖v‖) ^ K) :
    VelocityDecayConditions (X := X) Ψ (fun _ => φ) zeroField zeroField where
  -- ===== Collision conditions (non-trivial: Schwartz decay dominates) =====
  -- Each integrand is bounded by C × (1+‖v‖)^K × φ(v) × (1+‖w‖)^K × φ(w),
  -- integrable by hφ_decay (polynomial × Schwartz is integrable).
  -- PSD: φ(v)φ(w)⟨Δ,A(v-w)Δ⟩ where Δ = ∇log φ(v) - ∇log φ(w)
  -- |Δ| ≤ C(1+‖v‖)^K + C(1+‖w‖)^K by hGradBound
  -- |A| ≤ CΨ‖v-w‖² by hΨ
  hPSD_inner_int := fun _ v => by
    obtain ⟨CΨ, hCΨ⟩ := hΨ
    obtain ⟨Cg, Kg, hCg⟩ := hGradBound
    have hCΨ_nn : 0 ≤ CΨ := le_trans (abs_nonneg _) (hCΨ 0)
    have hCg_nn : 0 ≤ Cg := by
      have h := hCg 0 0; simp only [norm_zero, add_zero, one_pow] at h
      nlinarith [abs_nonneg (fderiv ℝ φ 0 (Pi.single 0 1)), hφ_pos 0]
    have h_cts : Continuous (PSDIntegrand Ψ φ v) :=
      (psd_integrand_continuous_joint hΨ_cts hφ_smooth hφ_pos).comp
        (continuous_const.prod_mk continuous_id')
    exact integrable_of_schwartz_bound hφ_decay h_cts.aestronglyMeasurable
      (C := 108 * CΨ * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|)
      (K := 2 * Kg + 2)
      (by positivity)
      fun w => by
        rw [show ‖PSDIntegrand Ψ φ v w‖ = |PSDIntegrand Ψ φ v w| from Real.norm_eq_abs _]
        calc |PSDIntegrand Ψ φ v w|
            ≤ (108 * CΨ * Cg ^ 2) * ((1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|) *
              ((1 + ‖w‖) ^ (2 * Kg + 2) * |φ w|) :=
            psd_integrand_bound hφ_smooth hφ_pos hCΨ hCΨ_nn hCg hCg_nn v w
          _ = (108 * CΨ * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|) *
              (1 + ‖w‖) ^ (2 * Kg + 2) * |φ w| := by ring
  hPSD_outer_int := fun _ => by
    obtain ⟨CΨ, hCΨ⟩ := hΨ
    obtain ⟨Cg, Kg, hCg⟩ := hGradBound
    have hCΨ_nn : 0 ≤ CΨ := le_trans (abs_nonneg _) (hCΨ 0)
    have hCg_nn : 0 ≤ Cg := by
      have h := hCg 0 0; simp only [norm_zero, add_zero, one_pow] at h
      nlinarith [abs_nonneg (fderiv ℝ φ 0 (Pi.single 0 1)), hφ_pos 0]
    refine integrable_integral_schwartz hφ_decay ?_ ?_ ?_
      (psd_integrand_bound hφ_smooth hφ_pos hCΨ hCΨ_nn hCg hCg_nn)
    · intro v
      exact integrable_of_schwartz_bound hφ_decay
        ((psd_integrand_continuous_joint hΨ_cts hφ_smooth hφ_pos).comp
          (continuous_const.prod_mk continuous_id')).aestronglyMeasurable
        (C := 108 * CΨ * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|)
        (K := 2 * Kg + 2)
        (by positivity)
        fun w => by
          rw [show ‖PSDIntegrand Ψ φ v w‖ = |PSDIntegrand Ψ φ v w| from Real.norm_eq_abs _]
          calc |PSDIntegrand Ψ φ v w|
              ≤ (108 * CΨ * Cg ^ 2) * ((1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|) *
                ((1 + ‖w‖) ^ (2 * Kg + 2) * |φ w|) :=
              psd_integrand_bound hφ_smooth hφ_pos hCΨ hCΨ_nn hCg hCg_nn v w
            _ = (108 * CΨ * Cg ^ 2 * (1 + ‖v‖) ^ (2 * Kg + 2) * |φ v|) *
                (1 + ‖w‖) ^ (2 * Kg + 2) * |φ w| := by ring
    · exact (psd_integrand_continuous_joint hΨ_cts hφ_smooth hφ_pos).aestronglyMeasurable.integral_prod_right'
    · nlinarith [sq_nonneg Cg]
  hFubini_double := fun _ => by
    obtain ⟨CΨ, hCΨ⟩ := hΨ
    obtain ⟨Cg, Kg, hCg⟩ := hGradBound
    have hCΨ_nn : 0 ≤ CΨ := le_trans (abs_nonneg _) (hCΨ 0)
    have hCg_nn : 0 ≤ Cg := by
      have h := hCg 0 0; simp only [norm_zero, add_zero, one_pow] at h
      nlinarith [abs_nonneg (fderiv ℝ φ 0 (Pi.single 0 1)), hφ_pos 0]
    exact integrable_prod_schwartz_bound hφ_decay
      (fubini_integrand_continuous hΨ_cts hφ_smooth hφ_pos).aestronglyMeasurable
      (by nlinarith [sq_nonneg Cg])
      (fubini_integrand_bound hφ_smooth hφ_pos hCΨ hCΨ_nn hCg hCg_nn)
  hFubini_inner := fun _ v => by
    -- Integrand = ⟨∇logφ(v), flux(v,w)⟩ where ∇logφ(v) is constant in w
    -- Since flux is integrable (vec-valued), dot product with constant is integrable
    have hflux := schwartz_flux_integrable hΨ hΨ_cts hφ_pos hφ_smooth hφ_decay hGradBound v
    -- Each component of the flux is integrable (projection of integrable vector function)
    have hcomp : ∀ i : Fin 3, Integrable (fun w => (landauMatrix Ψ (v - w) *ᵥ
        (φ w • vGrad φ v - φ v • vGrad φ w)) i) := fun i =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).integrable_comp hflux
    -- dotProduct c u = ∑ i, c_i * u_i = c₀*u₀ + c₁*u₁ + c₂*u₂
    simp only [dotProduct, Fin.sum_univ_three]
    exact ((hcomp 0).const_mul _).add ((hcomp 1).const_mul _) |>.add ((hcomp 2).const_mul _)
  hFubini_outer := fun _ => by
    obtain ⟨CΨ, hCΨ⟩ := hΨ
    obtain ⟨Cg, Kg, hCg⟩ := hGradBound
    have hCΨ_nn : 0 ≤ CΨ := le_trans (abs_nonneg _) (hCΨ 0)
    have hCg_nn : 0 ≤ Cg := by
      have h := hCg 0 0; simp only [norm_zero, add_zero, one_pow] at h
      nlinarith [abs_nonneg (fderiv ℝ φ 0 (Pi.single 0 1)), hφ_pos 0]
    refine integrable_integral_schwartz hφ_decay ?_ ?_ ?_
      (fubini_integrand_bound hφ_smooth hφ_pos hCΨ hCΨ_nn hCg hCg_nn)
    · -- ∀ v, Integrable (g v)
      intro v
      have hflux := schwartz_flux_integrable ⟨CΨ, hCΨ⟩ hΨ_cts hφ_pos hφ_smooth hφ_decay
        ⟨Cg, Kg, hCg⟩ v
      have hcomp := fun i =>
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).integrable_comp hflux
      simp only [dotProduct, Fin.sum_univ_three]
      exact ((hcomp 0).const_mul _).add ((hcomp 1).const_mul _) |>.add ((hcomp 2).const_mul _)
    · exact (fubini_integrand_continuous hΨ_cts hφ_smooth hφ_pos).aestronglyMeasurable.integral_prod_right'
    · nlinarith [sq_nonneg Cg]
  -- Flux differentiability: differentiation under the integral sign
  hLandauFluxDiff := fun _ i => by
    obtain ⟨CΨ, hCΨ⟩ := hΨ
    obtain ⟨Cg, Kg, hCg⟩ := hGradBound
    have hlfc := landau_flux_component_diff_with_bound ⟨CΨ, hCΨ⟩ hΨ_cts hΨ_diff hΨ'_bound
        hφ_pos hφ_smooth hφ_decay hφ_deriv2_bound ⟨Cg, Kg, hCg⟩ i
    obtain ⟨hg_diff, ⟨C₀, M, hbound⟩, hderiv_int, _⟩ := hlfc
    have hg_int : ∀ v, Integrable (fun w =>
        (landauMatrix Ψ (v - w) *ᵥ
          (φ w • vGrad φ v - φ v • vGrad φ w)) i) := fun v =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).integrable_comp
        (schwartz_flux_integrable ⟨CΨ, hCΨ⟩ hΨ_cts hφ_pos hφ_smooth hφ_decay ⟨Cg, Kg, hCg⟩ v)
    have hflux_int := fun v => schwartz_flux_integrable ⟨CΨ, hCΨ⟩ hΨ_cts hφ_pos hφ_smooth
      hφ_decay ⟨Cg, Kg, hCg⟩ v
    have heq : (fun v => (∫ w, landauMatrix Ψ (v - w) *ᵥ
        (φ w • vGrad φ v - φ v • vGrad φ w)) i) =
      fun v => ∫ w, (landauMatrix Ψ (v - w) *ᵥ
        (φ w • vGrad φ v - φ v • vGrad φ w)) i :=
      funext fun v => ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).integral_comp_comm
        (hflux_int v)).symm
    rw [heq]
    exact differentiable_integral_of_product_dominated hg_diff hg_int
      (continuous_const.mul (((continuous_const.add continuous_norm).pow M).mul hφ_smooth.continuous))
      (integrable_one_add_norm_pow_mul hφ_decay M)
      (fun w => mul_nonneg (pow_nonneg (by linarith [norm_nonneg w]) _) (abs_nonneg _))
      (fun v w => hbound v w)
      hderiv_int
  -- Derivative-of-flux × log integrability: follows from flux derivative Schwartz bound
  -- |d/dv_i flux_i(v)| ≤ C₁(1+‖v‖)^M₁ φ(v) and |log φ(v)| ≤ Cl(1+‖v‖)^Kl
  -- so product ≤ C₁*Cl*(1+‖v‖)^(M₁+Kl)*φ(v), integrable by Schwartz decay
  hLandauIBP_df_g := fun _ i => by
    obtain ⟨CΨ, hCΨ⟩ := hΨ
    obtain ⟨Cg, Kg, hCg⟩ := hGradBound
    obtain ⟨Cl, Kl, hCl⟩ := hLogBound
    have hlfc := landau_flux_component_diff_with_bound ⟨CΨ, hCΨ⟩ hΨ_cts hΨ_diff hΨ'_bound
        hφ_pos hφ_smooth hφ_decay hφ_deriv2_bound ⟨Cg, Kg, hCg⟩ i
    obtain ⟨_, _, _, ⟨C₁, M₁, hflux_bound⟩⟩ := hlfc
    -- Rewrite goal: (∫ w, F v w) i = ∫ w, (F v w) i
    have hflux_int := fun v => schwartz_flux_integrable ⟨CΨ, hCΨ⟩ hΨ_cts hφ_pos hφ_smooth
      hφ_decay ⟨Cg, Kg, hCg⟩ v
    have heq : ∀ v, (∫ w, landauMatrix Ψ (v - w) *ᵥ
        (φ w • vGrad φ v - φ v • vGrad φ w)) i =
      ∫ w, (landauMatrix Ψ (v - w) *ᵥ
        (φ w • vGrad φ v - φ v • vGrad φ w)) i :=
      fun v => ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).integral_comp_comm
        (hflux_int v)).symm
    simp_rw [heq]
    -- Now goal has ∫ w, (F v w) i and the bound from hlfc applies
    -- |fderiv(...) v (Pi.single i 1)| ≤ ‖fderiv(...) v‖ ≤ C₁(1+‖v‖)^M₁ φ(v)
    -- |log φ v| ≤ Cl(1+‖v‖)^Kl
    -- Product ≤ C₁*Cl*(1+‖v‖)^(M₁+Kl) * φ(v) ≤ C₁*Cl*(1+‖v‖)^(M₁+Kl) * |φ(v)|
    have hCl_nn : 0 ≤ Cl := by
      have h := hCl 0; simp only [norm_zero, add_zero, one_pow, mul_one] at h
      exact le_trans (abs_nonneg _) h
    have hC₁_nn : 0 ≤ C₁ := by
      have h := hflux_bound 0
      simp only [norm_zero, add_zero, one_pow, mul_one] at h
      nlinarith [norm_nonneg (fderiv ℝ (fun v' => ∫ w, (landauMatrix Ψ (v' - w) *ᵥ
        (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) 0), hφ_pos 0]
    have hdom : Integrable (fun v => C₁ * Cl * ((1 + ‖v‖) ^ (M₁ + Kl) * |φ v|)) :=
      (integrable_one_add_norm_pow_mul hφ_decay (M₁ + Kl)).const_mul _
    apply hdom.mono'
    · exact (measurable_fderiv_apply_const ℝ _ (Pi.single i 1)).aestronglyMeasurable.mul
        ((hφ_smooth.log (fun v => ne_of_gt (hφ_pos v))).continuous.aestronglyMeasurable)
    · filter_upwards with v
      rw [Real.norm_eq_abs, abs_mul]
      have hpi_norm : ‖(Pi.single i (1:ℝ) : Fin 3 → ℝ)‖ ≤ 1 := by
        simp [Pi.norm_def, Pi.single_apply, Finset.sup_le_iff]; intro j; split <;> simp
      set L := fderiv ℝ (fun v' => ∫ w, (landauMatrix Ψ (v' - w) *ᵥ
          (φ w • vGrad φ v' - φ v' • vGrad φ w)) i) v
      have h1 : |L (Pi.single i 1)| ≤ ‖L‖ := by
        calc |L (Pi.single i 1)| = ‖L (Pi.single i 1)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖L‖ * ‖(Pi.single i (1:ℝ) : Fin 3 → ℝ)‖ := L.le_opNorm _
          _ ≤ ‖L‖ * 1 := by gcongr
          _ = ‖L‖ := mul_one _
      have hCl_v : |(Real.log ∘ φ) v| ≤ Cl * (1 + ‖v‖) ^ Kl := hCl v
      have hflux_v := hflux_bound v
      have h1v : 0 ≤ 1 + ‖v‖ := by linarith [norm_nonneg v]
      calc |L (Pi.single i 1)| * |(Real.log ∘ φ) v|
          ≤ ‖L‖ * |(Real.log ∘ φ) v| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ ≤ ‖L‖ * (Cl * (1 + ‖v‖) ^ Kl) :=
            mul_le_mul_of_nonneg_left hCl_v (norm_nonneg _)
        _ ≤ (C₁ * (1 + ‖v‖) ^ M₁ * φ v) * (Cl * (1 + ‖v‖) ^ Kl) :=
            mul_le_mul_of_nonneg_right hflux_v (mul_nonneg hCl_nn (pow_nonneg h1v _))
        _ = C₁ * Cl * ((1 + ‖v‖) ^ (M₁ + Kl) * φ v) := by rw [pow_add]; ring
        _ ≤ C₁ * Cl * ((1 + ‖v‖) ^ (M₁ + Kl) * |φ v|) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self _)
              (pow_nonneg h1v _)) (mul_nonneg hC₁_nn hCl_nn)
  hLandauIBP_f_dg := by
    intro _ i
    obtain ⟨CΨ, hCΨ⟩ := hΨ
    obtain ⟨Cg, Kg, hCg⟩ := hGradBound
    have hCΨ_nn : 0 ≤ CΨ := le_trans (abs_nonneg _) (hCΨ 0)
    have hCg_nn : 0 ≤ Cg := by
      have h := hCg 0 0; simp only [norm_zero, add_zero, one_pow] at h
      nlinarith [abs_nonneg (fderiv ℝ φ 0 (Pi.single 0 1)), hφ_pos 0]
    set I := ∫ w, (1 + ‖w‖) ^ (Kg + 2) * |φ w|
    have hI_nn : 0 ≤ I := integral_nonneg fun w => mul_nonneg
      (pow_nonneg (by linarith [norm_nonneg w]) _) (abs_nonneg _)
    set Cf := 18 * CΨ * Cg * I
    set M := 2 * Kg + 2
    have hCf_nn : 0 ≤ Cf := mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hCΨ_nn) hCg_nn) hI_nn
    have hdom : Integrable (fun v => Cf * Cg * ((1 + ‖v‖) ^ M * |φ v|)) :=
      (integrable_one_add_norm_pow_mul hφ_decay M).const_mul _
    apply hdom.mono'
    · -- Measurability: flux integral component × fderiv(log ∘ φ)
      exact (((continuous_apply i).comp_aestronglyMeasurable
        (landau_flux_integral_aestronglyMeasurable hΨ_cts hφ_smooth)).aemeasurable.mul
        ((ContDiff.continuous_fderiv
          ((hφ_smooth.log (fun v => ne_of_gt (hφ_pos v))).of_le le_top) le_rfl).clm_apply
          continuous_const).aemeasurable).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_mul]
        set flux_v := ∫ w, landauMatrix Ψ (v - w) *ᵥ
            (φ w • vGrad φ v - φ v • vGrad φ w)
        have h_flux_bound : |flux_v i| ≤ Cf * (1 + ‖v‖) ^ (Kg + 2) * φ v := by
          calc |flux_v i|
              ≤ ‖flux_v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i
            _ ≤ ∫ w, ‖landauMatrix Ψ (v - w) *ᵥ
                  (φ w • vGrad φ v - φ v • vGrad φ w)‖ :=
                norm_integral_le_integral_norm (μ := volume) _
            _ ≤ ∫ w, (18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v *
                  ((1 + ‖w‖) ^ (Kg + 2) * |φ w|)) := by
                apply integral_mono_of_nonneg
                  (Filter.Eventually.of_forall fun w => norm_nonneg _)
                  ((integrable_one_add_norm_pow_mul hφ_decay (Kg + 2)).const_mul _)
                  (Filter.Eventually.of_forall fun w =>
                    le_trans (landau_flux_pointwise_bound hCΨ hCΨ_nn hCg hCg_nn hφ_pos v w)
                      (by apply mul_le_mul_of_nonneg_left
                          · exact mul_le_mul_of_nonneg_left (le_abs_self _)
                              (pow_nonneg (by linarith [norm_nonneg w]) _)
                          · apply mul_nonneg _ (le_of_lt (hφ_pos v))
                            apply mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hCΨ_nn) hCg_nn)
                              (pow_nonneg (by linarith [norm_nonneg v]) _)))
            _ = 18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v * I := integral_mul_left _ _
            _ = Cf * (1 + ‖v‖) ^ (Kg + 2) * φ v := by ring
        -- |∂(log∘φ)/∂vi| = |∂φ/∂vi|/φ(v) ≤ Cg * (1+‖v‖)^Kg
        have h_dlog : |fderiv ℝ (Real.log ∘ φ) v (Pi.single i 1)| ≤
            Cg * (1 + ‖v‖) ^ Kg := by
          rw [vGrad_log_eq_div (hφ_smooth.differentiable le_top) hφ_pos v i, abs_div,
              abs_of_pos (hφ_pos v)]
          exact div_le_of_le_mul₀ (le_of_lt (hφ_pos v))
            (mul_nonneg hCg_nn (pow_nonneg (by linarith [norm_nonneg v]) _))
            (hCg v i)
        calc |flux_v i| * |fderiv ℝ (Real.log ∘ φ) v (Pi.single i 1)|
            ≤ (Cf * (1 + ‖v‖) ^ (Kg + 2) * φ v) *
                (Cg * (1 + ‖v‖) ^ Kg) := mul_le_mul h_flux_bound h_dlog
              (abs_nonneg _)
              (mul_nonneg (mul_nonneg hCf_nn (pow_nonneg (by linarith [norm_nonneg v]) _))
                (le_of_lt (hφ_pos v)))
          _ = Cf * Cg * ((1 + ‖v‖) ^ M * φ v) := by
              simp only [M]; rw [show 2 * Kg + 2 = Kg + 2 + Kg from by omega, pow_add]; ring
          _ ≤ Cf * Cg * ((1 + ‖v‖) ^ M * |φ v|) := by
              gcongr; exact le_abs_self _
  hLandauIBP_fg := by
    intro _ i
    obtain ⟨CΨ, hCΨ⟩ := hΨ
    obtain ⟨Cg, Kg, hCg⟩ := hGradBound
    obtain ⟨Clog, Klog, hlog⟩ := hLogBound
    have hCΨ_nn : 0 ≤ CΨ := le_trans (abs_nonneg _) (hCΨ 0)
    have hCg_nn : 0 ≤ Cg := by
      have h := hCg 0 0; simp only [norm_zero, add_zero, one_pow] at h
      nlinarith [abs_nonneg (fderiv ℝ φ 0 (Pi.single 0 1)), hφ_pos 0]
    -- I = ∫ (1+‖w‖)^(Kg+2) * |φ(w)| (finite by Schwartz decay)
    set I := ∫ w, (1 + ‖w‖) ^ (Kg + 2) * |φ w|
    have hI_nn : 0 ≤ I := integral_nonneg fun w => mul_nonneg
      (pow_nonneg (by linarith [norm_nonneg w]) _) (abs_nonneg _)
    -- Total constant and power
    set Cf := 18 * CΨ * Cg * I
    set M := Kg + 2 + Klog
    have hCf_nn : 0 ≤ Cf := mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hCΨ_nn) hCg_nn) hI_nn
    have hClog_nn : 0 ≤ |Clog| := abs_nonneg _
    -- Dominator: Cf * |Clog| * (1+‖v‖)^M * |φ(v)|
    have hdom : Integrable (fun v => Cf * |Clog| * ((1 + ‖v‖) ^ M * |φ v|)) :=
      (integrable_one_add_norm_pow_mul hφ_decay M).const_mul _
    apply hdom.mono'
    · -- Measurability: flux integral component × log φ
      exact (((continuous_apply i).comp_aestronglyMeasurable
        (landau_flux_integral_aestronglyMeasurable hΨ_cts hφ_smooth)).aemeasurable.mul
        (hφ_smooth.continuous.log (fun v => ne_of_gt (hφ_pos v))).aemeasurable).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_mul]
        -- Key: bound ‖∫ w, flux(v,w)‖ using pointwise bound + integral monotonicity
        -- Abbreviate the flux integral for readability
        set flux_v := ∫ w, landauMatrix Ψ (v - w) *ᵥ
            (φ w • vGrad φ v - φ v • vGrad φ w)
        have h_flux_bound : |flux_v i| ≤ Cf * (1 + ‖v‖) ^ (Kg + 2) * φ v := by
          calc |flux_v i|
              ≤ ‖flux_v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i
            _ ≤ ∫ w, ‖landauMatrix Ψ (v - w) *ᵥ
                  (φ w • vGrad φ v - φ v • vGrad φ w)‖ :=
                norm_integral_le_integral_norm (μ := volume) _
            _ ≤ ∫ w, (18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v *
                  ((1 + ‖w‖) ^ (Kg + 2) * |φ w|)) := by
                apply integral_mono_of_nonneg
                  (Filter.Eventually.of_forall fun w => norm_nonneg _)
                  ((integrable_one_add_norm_pow_mul hφ_decay (Kg + 2)).const_mul _)
                  (Filter.Eventually.of_forall fun w =>
                    le_trans (landau_flux_pointwise_bound hCΨ hCΨ_nn hCg hCg_nn hφ_pos v w)
                      (by apply mul_le_mul_of_nonneg_left
                          · exact mul_le_mul_of_nonneg_left (le_abs_self _)
                              (pow_nonneg (by linarith [norm_nonneg w]) _)
                          · apply mul_nonneg _ (le_of_lt (hφ_pos v))
                            apply mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hCΨ_nn) hCg_nn)
                              (pow_nonneg (by linarith [norm_nonneg v]) _)))
            _ = 18 * CΨ * Cg * (1 + ‖v‖) ^ (Kg + 2) * φ v * I := integral_mul_left _ _
            _ = Cf * (1 + ‖v‖) ^ (Kg + 2) * φ v := by ring
        calc |flux_v i| * |(Real.log ∘ φ) v|
            ≤ (Cf * (1 + ‖v‖) ^ (Kg + 2) * φ v) *
                (|Clog| * (1 + ‖v‖) ^ Klog) := by
              apply mul_le_mul h_flux_bound
              · exact le_trans (hlog v) (mul_le_mul_of_nonneg_right (le_abs_self _)
                  (pow_nonneg (by linarith [norm_nonneg v]) _))
              · exact abs_nonneg _
              · exact mul_nonneg (mul_nonneg hCf_nn (pow_nonneg (by linarith [norm_nonneg v]) _))
                  (le_of_lt (hφ_pos v))
          _ = Cf * |Clog| * ((1 + ‖v‖) ^ M * φ v) := by
              simp only [M]; rw [pow_add]; ring
          _ ≤ Cf * |Clog| * ((1 + ‖v‖) ^ M * |φ v|) := by
              gcongr; exact le_abs_self _
  hLandauFluxInt := fun _ v =>
    schwartz_flux_integrable hΨ hΨ_cts hφ_pos hφ_smooth hφ_decay hGradBound v
  -- ===== Transport/force conditions (trivially 0) =====
  -- gradX of spatially-constant function = 0; E = B = 0.
  hSpatialTransport_int := by
    intro x
    have : (fun v => v ⬝ᵥ FlatTorus3.gradX (fun _ => φ v) x *
        Real.log (φ v)) = fun _ => 0 := by
      ext v; simp [gradX_const_fun φ v x, dotProduct]
    rw [this]; exact integrable_zero _ _ _
  hForceTransport_int := by
    intro x
    have : (fun v => (zeroField (X := X) x + cross v (zeroField x)) ⬝ᵥ
        vGrad φ v * Real.log (φ v)) = fun _ => 0 := by
      ext v; rw [force_zero]; simp [dotProduct]
    rw [this]; exact integrable_zero _ _ _
  hForceIBP_f_dg := by
    intro x i
    have : (fun v => (zeroField (X := X) x + cross v (zeroField x)) i *
        fderiv ℝ (fun w => φ w * Real.log (φ w) - φ w) v
          (Pi.single i 1)) = fun _ => 0 := by
      ext v; rw [force_zero]; simp
    rw [this]; exact integrable_zero _ _ _
  hForceIBP_fg := by
    intro x i
    have : (fun v => (zeroField (X := X) x + cross v (zeroField x)) i *
        (φ v * Real.log (φ v) - φ v)) = fun _ => 0 := by
      ext v; rw [force_zero]; simp
    rw [this]; exact integrable_zero _ _ _
  hSpatialTransport_joint := by
    have : (Function.uncurry (fun (x : X) (v : Fin 3 → ℝ) =>
        v ⬝ᵥ FlatTorus3.gradX (fun _ => φ v) x *
        Real.log (φ v))) = fun _ => 0 := by
      ext ⟨x, v⟩
      simp only [Function.uncurry]
      simp [gradX_const_fun φ v x, dotProduct]
    rw [this]; exact integrable_zero _ _ _
  hSpatTransComp := by
    intro v i
    have : (fun (x : X) => FlatTorus3.gradX (fun _ => φ v) x i *
        Real.log (φ v)) = fun _ => 0 := by
      ext x; simp [gradX_const_fun φ v x]
    rw [this]; exact integrable_zero _ _ _
  hf_velocity_dominated := by
    -- f(x,v) = φ(v) is independent of x, so g = |φ|
    refine ⟨fun v => |φ v|, ?_, fun _ v => le_abs_self _⟩
    exact (hφ_decay 0).congr (.of_forall fun v => by simp)
  hD_cont := continuous_const

end VML
