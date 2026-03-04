/-
  Definitions for the VML steady-state formalization.

  Extracted from Aristotle/Landau/landau-steady-state.lean.
  Contains all `def`, `noncomputable def`, structures, `@[simp]` unfolding lemmas,
  and small auxiliary lemmas about definitions.
-/

import Mathlib

set_option linter.all false
set_option linter.unusedSimpArgs false

open Matrix Finset BigOperators Real MeasureTheory

noncomputable section

namespace VML

-- ============================================================================
-- Section 1: Vector and Matrix Basics for ℝ³
-- ============================================================================

/-- Squared Euclidean norm: ‖z‖² = z · z = ∑ᵢ zᵢ² -/
def normSq (z : Fin 3 → ℝ) : ℝ := dotProduct z z

@[simp]
lemma normSq_zero : normSq (0 : Fin 3 → ℝ) = 0 := by
  simp [normSq, dotProduct]

lemma normSq_nonneg (z : Fin 3 → ℝ) : 0 ≤ normSq z := by
  unfold normSq dotProduct
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (a := z i)

lemma normSq_eq_zero {z : Fin 3 → ℝ} : normSq z = 0 ↔ z = 0 := by
  constructor
  · intro h
    unfold normSq dotProduct at h
    ext i
    have hsq : ∀ i ∈ Finset.univ, (0 : ℝ) ≤ z i * z i :=
      fun i _ => mul_self_nonneg (a := z i)
    have := (Finset.sum_eq_zero_iff_of_nonneg hsq).mp h i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp this
  · rintro rfl; simp [normSq, dotProduct]

lemma normSq_pos {z : Fin 3 → ℝ} (hz : z ≠ 0) : 0 < normSq z :=
  lt_of_le_of_ne (normSq_nonneg z) (fun h => hz (normSq_eq_zero.mp h.symm))

lemma normSq_neg (z : Fin 3 → ℝ) : normSq (-z) = normSq z := by
  simp [normSq, dotProduct, Pi.neg_apply]

/-- Euclidean norm: |z| = √(z · z) -/
def eucNorm (z : Fin 3 → ℝ) : ℝ := Real.sqrt (normSq z)

lemma eucNorm_nonneg (z : Fin 3 → ℝ) : 0 ≤ eucNorm z := Real.sqrt_nonneg _

lemma eucNorm_neg (z : Fin 3 → ℝ) : eucNorm (-z) = eucNorm z := by
  simp [eucNorm, normSq_neg]

lemma eucNorm_sq (z : Fin 3 → ℝ) : eucNorm z ^ 2 = normSq z := by
  simp [eucNorm, sq_sqrt (normSq_nonneg z)]

-- ============================================================================
-- Section 2: The Landau Collision Matrix
-- ============================================================================

/-- The inner part of the Landau matrix: B(z) = |z|² I₃ - z zᵀ.
    This is the matrix that appears inside the scalar factor Ψ(|z|). -/
def innerLandauMatrix (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  normSq z • (1 : Matrix (Fin 3) (Fin 3) ℝ) - vecMulVec z z

/-- The Landau collision matrix: A(z) = Ψ(|z|) · (|z|² I₃ - z zᵀ).
    Reference: Definition 2 (def:landau_matrix) -/
def landauMatrix (Ψ : ℝ → ℝ) (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Ψ (eucNorm z) • innerLandauMatrix z

lemma innerLandauMatrix_apply (z : Fin 3 → ℝ) (i j : Fin 3) :
    innerLandauMatrix z i j = (if i = j then normSq z else 0) - z i * z j := by
  simp [innerLandauMatrix, sub_apply, smul_apply, one_apply, vecMulVec_apply, smul_eq_mul]

-- ============================================================================
-- Section 3: Maxwellian Distributions
-- ============================================================================

/-- A function f : ℝ³ → ℝ has log-quadratic form if log f is an affine-quadratic
    polynomial in v. This is the characterization of Maxwellians.
    Specifically: ∃ a₀ b c₀, f(v) = exp(a₀ + b · v + c₀ |v|²) -/
def IsLogQuadratic (f : (Fin 3 → ℝ) → ℝ) : Prop :=
  ∃ (a₀ : ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ),
    ∀ v, f v = Real.exp (a₀ + dotProduct b v + c₀ * normSq v)

/-- A Maxwellian distribution: log-quadratic with c₀ < 0 (ensuring integrability). -/
def IsMaxwellian (f : (Fin 3 → ℝ) → ℝ) : Prop :=
  ∃ (a₀ : ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ),
    c₀ < 0 ∧ ∀ v, f v = Real.exp (a₀ + dotProduct b v + c₀ * normSq v)

lemma IsMaxwellian.isLogQuadratic {f : (Fin 3 → ℝ) → ℝ} (hf : IsMaxwellian f) :
    IsLogQuadratic f := by
  obtain ⟨a₀, b, c₀, _, hv⟩ := hf
  exact ⟨a₀, b, c₀, hv⟩

/-- The equilibrium Maxwellian (zero drift, density = ρ_ion):
    f∞(v) = ρ_ion/(2πT∞)^(3/2) · exp(-|v|²/(2T∞)) -/
def equilibriumMaxwellian (ρ_ion T : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  ρ_ion / (2 * π * T) ^ ((3 : ℝ) / 2) *
    Real.exp (-(normSq v) / (2 * T))

-- ============================================================================
-- Section 3b: Velocity Calculus
-- ============================================================================

/-- Velocity gradient: ∇ᵥf(v), the vector of partial derivatives of f at v.
    Uses Fréchet derivative from Mathlib. -/
def vGrad (f : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => fderiv ℝ f v (Pi.single i 1)

/-- Velocity divergence: ∇ᵥ · F(v) = ∑ᵢ ∂Fᵢ/∂vᵢ -/
def vDiv (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (v : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun w => F w i) v (Pi.single i 1)

/-- Cross product in ℝ³: a × b -/
def cross (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

-- ============================================================================
-- Section 4: Landau Collision Operator
-- ============================================================================

/-- The Landau collision operator Q(f,f)(v).
    Reference: Definition 3 (def:landau_operator)

    Q(f,f)(v) = ∇ᵥ · ∫_{ℝ³} A(v-w) [f(w)∇ᵥf(v) - f(v)∇_wf(w)] dw -/
def LandauOperator (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  vDiv (fun v' =>
    ∫ w, mulVec (landauMatrix Ψ (v' - w))
      (f w • vGrad f v' - f v' • vGrad f w)) v

/-- The entropy dissipation functional: D(f) = ∫ Q(f,f)(v) log f(v) dv.
    Reference: Definition in Lemma 5 (lem:entropy_dissipation) -/
def entropyDissipation (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ) : ℝ :=
  ∫ v, LandauOperator Ψ f v * Real.log (f v)

/-- The PSD integrand: g(v,w) = f(v)·f(w)·⟨Δ(v,w), A(v-w) Δ(v,w)⟩
    where Δ(v,w) = ∇log f(v) - ∇log f(w).
    This appears in the entropy dissipation formula (Lemma 5). -/
def PSDIntegrand (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ) (v w : Fin 3 → ℝ) : ℝ :=
  f v * f w *
    dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
      (mulVec (landauMatrix Ψ (v - w))
        (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w))

-- ============================================================================
-- Small helper lemmas about definitions
-- ============================================================================

/-- Cross product antisymmetry: -cross a b = cross b a. -/
lemma neg_cross (a b : Fin 3 → ℝ) : -cross a b = cross b a := by
  ext i; fin_cases i <;> simp +decide [cross, Pi.neg_apply] <;> ring

lemma cross_smul_left (c : ℝ) (a b : Fin 3 → ℝ) :
    cross (c • a) b = c • cross a b := by
  ext i; fin_cases i <;> simp +decide [cross, Pi.smul_apply, smul_eq_mul, mul_sub] <;> ring

/-- Helper: dotProduct with scalar multiplication -/
private lemma dotProduct_smul_self (c : ℝ) (v : Fin 3 → ℝ) :
    dotProduct v (c • v) = c * normSq v := by
  unfold normSq dotProduct
  simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

/-- Helper: cross product with zero first argument -/
lemma cross_zero_left (b : Fin 3 → ℝ) : cross (0 : Fin 3 → ℝ) b = 0 := by
  ext i; fin_cases i <;> simp [cross]

/-- Helper: (vecMulVec z z) *ᵥ w = (z · w) • z -/
lemma vecMulVec_self_mulVec (z w : Fin 3 → ℝ) :
    mulVec (vecMulVec z z) w = dotProduct z w • z := by
  ext i
  simp only [mulVec, vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, mul_comm]

-- ============================================================================
-- Section 6: VML Steady State Structure
-- ============================================================================

/-- Bundle representing a steady state of the VML system on T³ × ℝ³.

    Encodes:
    - The VML equations at steady state (Vlasov, Ampère, Gauss, div B = 0)
    - Analytical results from the H-theorem chain (Sections 3-4 of tex):
      f is a local Maxwellian with explicit parameters
    - Analytical results from polynomial matching (Section 5 of tex):
      temperature and drift velocity are spatially constant
    - Torus-specific properties (Stokes, harmonic → constant)
    - Maximum principle conclusion (density constant) -/
structure VMLSteadyState where
  X : Type*
  x₀ : X
  f : X → (Fin 3 → ℝ) → ℝ
  E : X → (Fin 3 → ℝ)
  B : X → (Fin 3 → ℝ)
  ν : ℝ
  ρ_ion : ℝ
  Ψ : ℝ → ℝ
  hν : 0 < ν
  hρ_ion : 0 < ρ_ion
  hΨ : ∀ r, 0 < Ψ r
  hf_pos : ∀ x v, 0 < f x v
  ρ : X → ℝ
  hρ_pos : ∀ x, 0 < ρ x
  J : X → (Fin 3 → ℝ)
  -- Spatial calculus operators on T³
  gradX : (X → ℝ) → X → (Fin 3 → ℝ)
  divX : (X → (Fin 3 → ℝ)) → X → ℝ
  curlX : (X → (Fin 3 → ℝ)) → X → (Fin 3 → ℝ)
  spatialIntegral : (X → ℝ) → ℝ
  vol : ℝ
  hvol : 0 < vol
  -- Torus topology: ∫ div F dx = 0 (Stokes)
  hStokes : ∀ F : X → (Fin 3 → ℝ), spatialIntegral (divX F) = 0
  -- Harmonic functions on compact torus are constant
  hHarmonic_const : ∀ φ : X → ℝ, (∀ x, divX (gradX φ) x = 0) → ∀ x y, φ x = φ y
  -- Maxwell equations at steady state
  hAmpere : ∀ x, curlX B x = J x
  hGauss : ∀ x, divX E x = ρ x - ρ_ion
  hDivB : ∀ x, divX B x = 0
  -- === H-theorem chain results (Sections 3-4 of tex) ===
  -- Local Maxwellian parameters a(x), b(x), c(x) with c < 0
  a_loc : X → ℝ
  b_loc : X → (Fin 3 → ℝ)
  c_loc : X → ℝ
  hc_neg : ∀ x, c_loc x < 0
  hMaxwellianForm : ∀ x v,
    f x v = Real.exp (a_loc x + dotProduct (b_loc x) v + c_loc x * normSq v)
  -- === Polynomial matching results (Section 5 of tex) ===
  -- Lemma 14: c is constant (from O(|v|³) terms)
  c₀ : ℝ
  hc₀_neg : c₀ < 0
  hc_const : ∀ x, c_loc x = c₀
  -- Lemma 15: Drift velocity b₀ is constant (Killing's equation on T³)
  -- Here b₀ represents the drift velocity u∞
  b₀ : Fin 3 → ℝ
  hb_const : ∀ x, b_loc x = (-2 * c₀) • b₀
  -- Lemma 16: Force balance ∇a = -2c₀(E + u∞ × B)
  hForceBalance : ∀ x,
    gradX a_loc x = -(2 * c₀) • (E x + cross b₀ (B x))
  -- Current density J = ρ u∞
  hJ_def : ∀ x, J x = (ρ x) • b₀
  -- === Vector calculus on T³ ===
  -- ∫ u · (∇×B) dx = 0 for constant u (Stokes + vector identity)
  hCurlDotConst : ∀ (u : Fin 3 → ℝ),
    spatialIntegral (fun x => dotProduct u (curlX B x)) = 0
  -- curl F = 0 ∧ div F = 0 ⟹ each component is harmonic
  hCurlZeroDivZeroHarmonic : ∀ F : X → (Fin 3 → ℝ),
    (∀ x, curlX F x = 0) → (∀ x, divX F x = 0) →
    ∀ i, ∀ x, divX (gradX (fun y => F y i)) x = 0
  -- === Integration properties ===
  hSpatialMul : ∀ (g : X → ℝ) (c : ℝ),
    spatialIntegral (fun x => g x * c) = spatialIntegral g * c
  hSpatialPos : ∀ g : X → ℝ, (∀ x, 0 < g x) → 0 < spatialIntegral g
  -- === Maximum principle (Section 7 of tex) ===
  -- Lemma 21: Density is constant (Poisson-Boltzmann + max principle on T³)
  hDensityConst : ∀ x, ρ x = ρ_ion
  -- Gradient of a vanishes when ρ is constant and drift is zero
  hGradA_zero : b₀ = 0 → (∀ x, ρ x = ρ_ion) → ∀ x, gradX a_loc x = 0
  -- === Normalization (Gaussian integral) ===
  hNormalization : b₀ = 0 → (∀ x, ρ x = ρ_ion) →
    ∀ x v, f x v = equilibriumMaxwellian ρ_ion (-1 / (2 * c₀)) v

-- ============================================================================
-- The equilibrium configuration of a VML steady state.
-- ============================================================================

/-- The equilibrium configuration of a VML steady state. -/
structure VMLEquilibrium where
  T : ℝ
  B₀ : Fin 3 → ℝ
  hT : 0 < T

-- ============================================================================
-- Minimal physical input for the VML steady state problem.
-- ============================================================================

/-- Minimal physical input for the VML steady state problem.

    Contains:
    - The physical state (f, E, B) on a spatial domain X × ℝ³
    - Physical parameters (ν, ρ_ion, Ψ)
    - Abstract spatial operators (grad, div, curl, ∫) for the torus T³
    - Torus-specific properties (Stokes, harmonic → constant)
    - Maxwell equations at steady state
    - Entropy dissipation vanishes (from H-theorem chain)
    - Analytical interface hypotheses (polynomial identity, Gaussian integrals)

    The key distinction from VMLSteadyState: this structure does NOT include
    the Maxwellian parameters (a, b, c), temperature/drift constancy, or
    density constancy — those are DERIVED in toSteadyState. -/
structure VMLInput where
  X : Type*
  inst_ne : Nonempty X
  x₀ : X
  -- Physical state
  f : X → (Fin 3 → ℝ) → ℝ
  E : X → (Fin 3 → ℝ)
  B : X → (Fin 3 → ℝ)
  ν : ℝ
  ρ_ion : ℝ
  Ψ : ℝ → ℝ
  -- Positivity
  hν : 0 < ν
  hρ_ion : 0 < ρ_ion
  hΨ : ∀ r, 0 < Ψ r
  hf_pos : ∀ x v, 0 < f x v
  -- Smoothness
  hf_smooth : ∀ x, ContDiff ℝ ⊤ (f x)
  -- Integrability (f(x,·) ∈ L¹(ℝ³) for each x)
  hf_int : ∀ x, Integrable (f x)
  -- Derived densities
  ρ : X → ℝ
  hρ_pos : ∀ x, 0 < ρ x
  J : X → (Fin 3 → ℝ)
  -- Spatial calculus operators on T³
  gradX : (X → ℝ) → X → (Fin 3 → ℝ)
  divX : (X → (Fin 3 → ℝ)) → X → ℝ
  curlX : (X → (Fin 3 → ℝ)) → X → (Fin 3 → ℝ)
  spatialIntegral : (X → ℝ) → ℝ
  vol : ℝ
  hvol : 0 < vol
  -- Torus topology: ∫ div F dx = 0 (Stokes)
  hStokes : ∀ F : X → (Fin 3 → ℝ), spatialIntegral (divX F) = 0
  -- Harmonic functions on compact torus are constant
  hHarmonic_const : ∀ φ : X → ℝ, (∀ x, divX (gradX φ) x = 0) → ∀ x y, φ x = φ y
  -- Maxwell equations at steady state
  hAmpere : ∀ x, curlX B x = J x
  hGauss : ∀ x, divX E x = ρ x - ρ_ion
  hDivB : ∀ x, divX B x = 0
  -- === Derived from H-theorem chain ===
  -- Entropy dissipation vanishes at each spatial point
  hD_zero : ∀ x, entropyDissipation Ψ (f x) = 0
  -- Score form identity (from IBP + Fubini + score substitution)
  hScoreForm : ∀ x, entropyDissipation Ψ (f x) =
    -(1 / 2) * ∫ v, ∫ w, PSDIntegrand Ψ (f x) v w
  -- Continuity of the PSD integrand
  hPSD_cont : ∀ x, Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
    PSDIntegrand Ψ (f x) p.1 p.2)
  -- Inner integrability of the PSD integrand
  hPSD_inner : ∀ x v, Integrable (PSDIntegrand Ψ (f x) v)
  -- Outer integrability of the PSD integrand
  hPSD_outer : ∀ x, Integrable (fun v => ∫ w, PSDIntegrand Ψ (f x) v w)
  -- === Analytical interface hypotheses ===
  -- These connect the abstract spatial operators to the Maxwellian structure.
  -- They represent genuine mathematical facts but are hard to prove in Lean/Mathlib.

  -- Polynomial identity: after substituting f = exp(a + b·v + c|v|²) into
  -- the steady-state Vlasov equation, we get a polynomial in v that must vanish.
  hPolynomialIdentity : ∀ (a : X → ℝ) (b : X → Fin 3 → ℝ) (c : X → ℝ),
    (∀ x v, f x v = Real.exp (a x + dotProduct (b x) v + c x * normSq v)) →
    ∀ x v,
      dotProduct v (gradX c x) * normSq v +
      (∑ i : Fin 3, ∑ j : Fin 3, v i * v j * (gradX (fun y => b y j) x i)) +
      dotProduct v (gradX a x) +
      dotProduct (E x) (b x) +
      dotProduct v ((2 * c x) • E x + cross (B x) (b x)) = 0
  -- Killing equation + harmonic → each component of b is harmonic
  hKillingToHarmonic : ∀ (b : X → Fin 3 → ℝ),
    (∀ x i j, gradX (fun y => b y j) x i + gradX (fun y => b y i) x j = 0) →
    ∀ j : Fin 3, ∀ x, divX (gradX (fun y => b y j)) x = 0
  -- Gradient zero → spatially constant (for scalar fields)
  hGradZeroConst : ∀ (φ : X → ℝ),
    (∀ x, gradX φ x = 0) → ∀ x y, φ x = φ y
  -- Spatially constant → gradient zero (converse of above)
  hGradConst : ∀ (φ : X → ℝ),
    (∀ x y, φ x = φ y) → ∀ x, gradX φ x = 0
  -- Current from Maxwellian: J = ρ · drift
  hJ_from_maxwellian : ∀ (b : X → Fin 3 → ℝ) (c₀ : ℝ),
    (∀ x, ∃ a₀, ∀ v, f x v = Real.exp (a₀ + dotProduct (b x) v + c₀ * normSq v)) →
    ∀ x, J x = ρ x • ((-1 / (2 * c₀)) • b x)
  -- Divergence linearity (for Poisson-Boltzmann)
  hDivLinear : ∀ (α : ℝ) (G : X → (Fin 3 → ℝ)),
    ∀ x, divX (fun y => α • G y) x = α * divX G x
  -- Maximum principle inputs (compactness of T³)
  x_max : X
  hmax : ∀ x, ρ x ≤ ρ x_max
  x_min : X
  hmin : ∀ x, ρ x_min ≤ ρ x
  -- Laplacian sign at extrema (second derivative test on compact domain)
  hmax_lapl : divX (gradX (Real.log ∘ ρ)) x_max ≤ 0
  hmin_lapl : 0 ≤ divX (gradX (Real.log ∘ ρ)) x_min
  -- ∫ u · (∇×B) dx = 0 for constant u (Stokes + vector identity)
  hCurlDotConst : ∀ (u : Fin 3 → ℝ),
    spatialIntegral (fun x => dotProduct u (curlX B x)) = 0
  -- curl F = 0 ∧ div F = 0 ⟹ each component is harmonic
  hCurlZeroDivZeroHarmonic : ∀ F : X → (Fin 3 → ℝ),
    (∀ x, curlX F x = 0) → (∀ x, divX F x = 0) →
    ∀ i, ∀ x, divX (gradX (fun y => F y i)) x = 0
  -- Integration properties
  hSpatialMul : ∀ (g : X → ℝ) (c : ℝ),
    spatialIntegral (fun x => g x * c) = spatialIntegral g * c
  hSpatialPos : ∀ g : X → ℝ, (∀ x, 0 < g x) → 0 < spatialIntegral g
  -- Poisson-Boltzmann equation: T Δ(log ρ) = ρ - ρ_ion
  hPB_eq : ∀ (c₀ : ℝ), c₀ < 0 →
    (∀ x, ∃ a₀ b₀, ∀ v, f x v = Real.exp (a₀ + dotProduct b₀ v + c₀ * normSq v)) →
    ∀ x, (-1 / (2 * c₀)) * divX (gradX (Real.log ∘ ρ)) x = ρ x - ρ_ion
  -- Normalization: Gaussian integral yields equilibriumMaxwellian
  hNormalization : ∀ a₀ c₀,
    c₀ < 0 →
    (∀ x v, f x v = Real.exp (a₀ + c₀ * normSq v)) →
    (∀ x, ρ x = ρ_ion) →
    ∀ x v, f x v = equilibriumMaxwellian ρ_ion (-1 / (2 * c₀)) v

end VML
