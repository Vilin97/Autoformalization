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
def uniformMaxwellianDecay (Ψ : ℝ → ℝ) (a c : ℝ) (hc : c < 0) :
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

end VML
