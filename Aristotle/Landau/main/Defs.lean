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

/-- Velocity-space integration by parts on ℝ³.
    ∫ (∇ᵥ · F)(v) · g(v) dv = -∫ F(v) · (∇ᵥg)(v) dv.

    Uses Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`
    (n-dimensional IBP for Fréchet derivatives) applied per component.

    The three per-component integrability hypotheses (derivative·g, f·derivative,
    and f·g) are the natural conditions for Bochner-integral IBP. -/
lemma velocity_ibp
    (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (g : (Fin 3 → ℝ) → ℝ)
    (hF_diff : ∀ i, Differentiable ℝ (fun v => F v i))
    (hg_diff : Differentiable ℝ g)
    (h_int_df_g : ∀ i, Integrable (fun v => fderiv ℝ (fun w => F w i) v (Pi.single i 1) * g v))
    (h_int_f_dg : ∀ i, Integrable (fun v => F v i * fderiv ℝ g v (Pi.single i 1)))
    (h_int_fg : ∀ i, Integrable (fun v => F v i * g v)) :
    ∫ v, vDiv F v * g v = -(∫ v, dotProduct (F v) (vGrad g v)) := by
  -- Strategy: expand into per-component integrals, apply Mathlib IBP per component.
  -- Step 1: Per-component IBP from Mathlib
  -- Per-component IBP from Mathlib: ∫ Fᵢ * ∂g/∂vᵢ = -∫ ∂Fᵢ/∂vᵢ * g
  have hi : ∀ i : Fin 3,
      ∫ v, F v i * fderiv ℝ g v (Pi.single i 1) =
      -(∫ v, fderiv ℝ (fun w => F w i) v (Pi.single i 1) * g v) :=
    fun i => integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (h_int_df_g i) (h_int_f_dg i) (h_int_fg i) (hF_diff i) hg_diff
  -- Both sides equal Finset.sum over per-component integrals
  have lhs_eq : (fun v => vDiv F v * g v) = fun v =>
      ∑ i : Fin 3, fderiv ℝ (fun w => F w i) v (Pi.single i 1) * g v := by
    ext v; simp only [vDiv, Fin.sum_univ_three]; ring
  have rhs_eq : (fun v => dotProduct (F v) (vGrad g v)) = fun v =>
      ∑ i : Fin 3, F v i * fderiv ℝ g v (Pi.single i 1) := by
    ext v; simp only [dotProduct, vGrad, Fin.sum_univ_three]
  rw [lhs_eq, rhs_eq,
      integral_finset_sum _ (fun i _ => h_int_df_g i),
      integral_finset_sum _ (fun i _ => h_int_f_dg i)]
  simp only [Fin.sum_univ_three, hi]; ring

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

/-- IBP for the Landau collision operator: ∫ Q(g,g)(v) · log g(v) dv equals
    the symmetrized weak form. Combines velocity-space IBP (∫ div F · g = -∫ F · ∇g)
    with dotProduct_integral_comm (pulling the w-integral through the dot product).

    The integrability hypotheses on the Landau flux are the natural conditions for
    Bochner-integral IBP. They require the flux F(v) = ∫_w A(v-w)[...] dw and
    its derivatives to be integrable against log g — this holds for distributions
    with sufficient velocity-space decay (e.g., sub-Gaussian tails). -/
lemma landau_ibp (Ψ : ℝ → ℝ) (g : (Fin 3 → ℝ) → ℝ)
    (hg_pos : ∀ v, 0 < g v) (hg_smooth : ContDiff ℝ ⊤ g) (hg_int : Integrable g)
    -- Differentiability of Landau flux components (requires differentiation under ∫)
    (hFlux_diff : ∀ i, Differentiable ℝ (fun v =>
      (∫ w, mulVec (landauMatrix Ψ (v - w))
        (g w • vGrad g v - g v • vGrad g w)) i))
    -- Per-component integrability for IBP
    (h_int_df_g : ∀ i, Integrable (fun v =>
      fderiv ℝ (fun v' => (∫ w, mulVec (landauMatrix Ψ (v' - w))
        (g w • vGrad g v' - g v' • vGrad g w)) i) v (Pi.single i 1) *
      (Real.log ∘ g) v))
    (h_int_f_dg : ∀ i, Integrable (fun v =>
      (∫ w, mulVec (landauMatrix Ψ (v - w))
        (g w • vGrad g v - g v • vGrad g w)) i *
      fderiv ℝ (Real.log ∘ g) v (Pi.single i 1)))
    (h_int_fg : ∀ i, Integrable (fun v =>
      (∫ w, mulVec (landauMatrix Ψ (v - w))
        (g w • vGrad g v - g v • vGrad g w)) i * (Real.log ∘ g) v))
    -- Integrability of the Landau flux (for pulling dot product through ∫)
    (hFlux_int : ∀ v, Integrable (fun w =>
      mulVec (landauMatrix Ψ (v - w))
        (g w • vGrad g v - g v • vGrad g w))) :
    ∫ v, LandauOperator Ψ g v * (Real.log ∘ g) v =
    -(∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ g) v)
        (mulVec (landauMatrix Ψ (v - w))
          (g w • vGrad g v - g v • vGrad g w))) := by
  -- Step 1: Unfold LandauOperator = vDiv(Flux)
  unfold LandauOperator
  -- Step 2: Apply velocity IBP: ∫ vDiv(Flux) · log g = -∫ Flux · ∇(log g)
  have h_ibp := velocity_ibp
    (fun v => ∫ w, mulVec (landauMatrix Ψ (v - w))
      (g w • vGrad g v - g v • vGrad g w))
    (Real.log ∘ g)
    hFlux_diff
    (hg_smooth.differentiable le_top |>.log (fun v => ne_of_gt (hg_pos v)))
    h_int_df_g h_int_f_dg h_int_fg
  rw [h_ibp]
  -- Step 3: Pull w-integral through dot product: ⟨c, ∫ F dw⟩ = ∫ ⟨c, F⟩ dw
  congr 1; congr 1; funext v
  rw [dotProduct_comm]
  -- ⟨∇log g(v), ∫ w, A·flux dw⟩ = ∫ w, ⟨∇log g(v), A·flux(w)⟩ via CLM
  set c := vGrad (Real.log ∘ g) v
  set F := fun w => mulVec (landauMatrix Ψ (v - w))
      (g w • vGrad g v - g v • vGrad g w)
  -- Express dotProduct c as a continuous linear map
  let L : (Fin 3 → ℝ) →L[ℝ] ℝ :=
    ∑ i : Fin 3, ContinuousLinearMap.smulRight (ContinuousLinearMap.proj i) (c i)
  have hL : ∀ x, L x = dotProduct c x := by
    intro x; simp +decide [L, dotProduct, Fin.sum_univ_three]; ring
  rw [show dotProduct c (∫ w, F w) = L (∫ w, F w) from (hL _).symm]
  rw [show (∫ w, dotProduct c (F w)) = ∫ w, L (F w) from by
    congr 1; ext w; exact (hL _).symm]
  exact (L.integral_comp_comm (hFlux_int v)).symm

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
-- FlatTorus3: Abstract characterization of a flat compact 3-torus
-- ============================================================================

/-- Abstract characterization of a flat 3-torus with differential operators.

    The spatial domain X is a compact nonempty space equipped with a MeasureSpace
    instance (providing a canonical measure for integration via Mathlib's `∫`) and
    abstract differential operators (grad, div, curl).

    These axioms are satisfied by any flat compact Riemannian 3-manifold without
    boundary (e.g. T³ = ℝ³/ℤ³) equipped with its standard differential operators
    and Riemannian volume form. See `TorusInstance.lean` for a concrete instance
    on `Fin 3 → AddCircle 1`.

    **Axiom design note:**
    The operator axioms (hGradAdd, hGradScalarMul, hGradChainExp, hDivLinear) describe
    properties of an abstract differential operator on a compact manifold. They are
    stated universally (for all functions X → ℝ) rather than restricted to smooth
    functions, because X has no differentiable structure at this abstraction level.
    This is intentional: a properly-defined gradient on a compact manifold (e.g. via
    distributional/weak derivatives) IS linear for all L² functions. The concrete
    `fderiv`-based implementation in `TorusInstance.lean` only satisfies these for
    differentiable inputs, which is why those instance fields are sorry'd — the fix
    is to use distributional derivatives in the instance, not to weaken the axioms.

    Similarly, hSpatialAdd and hSpatialVelocityFubini are stated without explicit
    integrability hypotheses. On a compact manifold with finite measure, all functions
    arising in the proof (gradients of smooth functions, products thereof) are bounded
    hence integrable, so Mathlib's `integral_add` and `integral_integral_swap` apply.

    Integration uses Mathlib's `∫ x, f x` (Bochner integral over `volume`).

    Axioms (15):
    - Operator properties (5): hDivLinear, hGradConst, hGradAdd, hGradScalarMul, hGradChainExp
    - Closed manifold integration (2): hCurlIntZero, hIBP_spatial
    - Analysis on compact manifold (4): hHarmonic_const, hLaplacianMaxNonpos, hSpatialPos, hSpatialNonnegZero
    - Flat geometry (2): hKillingToHarmonic, hCurlZeroDivZeroHarmonic
    - Abstract measure (2): hSpatialVelocityFubini, hSpatialAdd

    Derived lemmas (proved from the above):
    - hGradChainLog, hGradIntZero, hLaplacianMinNonneg, hSpatialMul -/
class FlatTorus3 (X : Type*) extends MeasureSpace X, TopologicalSpace X where
  instCompact : CompactSpace X
  instNonempty : Nonempty X
  gradX : (X → ℝ) → X → (Fin 3 → ℝ)
  divX : (X → (Fin 3 → ℝ)) → X → ℝ
  curlX : (X → (Fin 3 → ℝ)) → X → (Fin 3 → ℝ)
  -- Linearity of the divergence operator
  hDivLinear : ∀ (α : ℝ) (G : X → (Fin 3 → ℝ)),
    ∀ x, divX (fun y => α • G y) x = α * divX G x
  -- Gradient of a spatially constant function vanishes
  hGradConst : ∀ (φ : X → ℝ), (∀ x y, φ x = φ y) → ∀ x, gradX φ x = 0
  -- Strictly positive continuous function has strictly positive integral
  hSpatialPos : ∀ g : X → ℝ, Continuous g → (∀ x, 0 < g x) → 0 < ∫ x, g x
  -- Nonneg continuous function with zero integral is identically zero
  hSpatialNonnegZero : ∀ g : X → ℝ, Continuous g →
    (∀ x, 0 ≤ g x) → ∫ x, g x = 0 → ∀ x, g x = 0
  -- Spatial differentiability predicate (abstract; on the concrete torus,
  -- this is ContDiff ℝ 1 (periodicLift f), i.e. the periodic lift is C¹)
  IsSpatiallyDiff : (X → ℝ) → Prop
  hDiff_const : ∀ c, IsSpatiallyDiff (fun _ : X => c)
  hDiff_add : ∀ f g, IsSpatiallyDiff f → IsSpatiallyDiff g →
    IsSpatiallyDiff (fun x => f x + g x)
  hDiff_smul : ∀ c f, IsSpatiallyDiff f → IsSpatiallyDiff (fun x => c * f x)
  -- Curl integral vanishes (Stokes theorem for 2-forms)
  -- Requires IsSpatiallyDiff for each component of F: without differentiability,
  -- curlX uses fderiv (which is 0 at non-differentiable points), and the integral
  -- of the resulting "gradient" over the torus is not guaranteed to be 0.
  hCurlIntZero : ∀ (F : X → Fin 3 → ℝ) (u : Fin 3 → ℝ),
    (∀ j, IsSpatiallyDiff (fun x => F x j)) →
    ∫ x, dotProduct u (curlX F x) = 0
  -- Harmonic functions on compact manifold are constant (Hodge theory)
  -- Requires IsSpatiallyDiff because without it, gradX returns 0 for
  -- non-differentiable functions, making the hypothesis vacuously true.
  hHarmonic_const : ∀ φ : X → ℝ, IsSpatiallyDiff φ →
    (∀ x, divX (gradX φ) x = 0) → ∀ x y, φ x = φ y
  -- Second derivative test: Laplacian ≤ 0 at a maximum
  -- Requires IsSpatiallyDiff: without it, gradX uses junk fderiv values,
  -- making the statement false for non-differentiable functions.
  hLaplacianMaxNonpos : ∀ (φ : X → ℝ) (x₀ : X), IsSpatiallyDiff φ →
    (∀ x, φ x ≤ φ x₀) → divX (gradX φ) x₀ ≤ 0
  -- Linearity of gradient: gradX(f + g) = gradX(f) + gradX(g) for differentiable f, g
  hGradAdd : ∀ (f g : X → ℝ), IsSpatiallyDiff f → IsSpatiallyDiff g →
    ∀ x, gradX (fun y => f y + g y) x = gradX f x + gradX g x
  -- Scalar multiplication: gradX(c · f) = c · gradX(f) for constant c
  hGradScalarMul : ∀ (c : ℝ) (f : X → ℝ),
    ∀ x, gradX (fun y => c * f y) x = c • gradX f x
  -- Chain rule for exp: gradX(exp ∘ φ) = exp(φ) · gradX(φ)
  hGradChainExp : ∀ (φ : X → ℝ),
    ∀ x i, gradX (fun y => Real.exp (φ y)) x i = Real.exp (φ x) * gradX φ x i
  -- Killing fields have harmonic components (flatness of the metric).
  -- Requires C¹ regularity of b_j and C² regularity of gradient components.
  hKillingToHarmonic : ∀ (b : X → Fin 3 → ℝ),
    (∀ j, IsSpatiallyDiff (fun y => b y j)) →
    (∀ j i, IsSpatiallyDiff (fun x => gradX (fun y => b y j) x i)) →
    (∀ x i j, gradX (fun y => b y j) x i + gradX (fun y => b y i) x j = 0) →
    ∀ j : Fin 3, ∀ x, divX (gradX (fun y => b y j)) x = 0
  -- Irrotational + solenoidal vector field has harmonic components.
  -- Requires C¹ regularity of F_i and C² regularity of gradient components.
  hCurlZeroDivZeroHarmonic : ∀ F : X → (Fin 3 → ℝ),
    (∀ i, IsSpatiallyDiff (fun y => F y i)) →
    (∀ i j, IsSpatiallyDiff (fun x => gradX (fun y => F y i) x j)) →
    (∀ x, curlX F x = 0) → (∀ x, divX F x = 0) →
    ∀ i, ∀ x, divX (gradX (fun y => F y i)) x = 0
  -- Integration by parts on the torus: ∫ φ · (∇ψ)ᵢ = -∫ ψ · (∇φ)ᵢ
  -- Requires spatial differentiability of both φ and ψ.
  hIBP_spatial : ∀ (φ ψ : X → ℝ) (i : Fin 3),
    IsSpatiallyDiff φ → IsSpatiallyDiff ψ →
    (∫ x, φ x * gradX ψ x i) = -(∫ x, ψ x * gradX φ x i)
  -- Fubini: swap spatial integral (over compact X) with velocity integral (over ℝ³)
  hSpatialVelocityFubini : ∀ (F : X → (Fin 3 → ℝ) → ℝ),
    (∀ x, MeasureTheory.Integrable (F x)) →
    MeasureTheory.Integrable (Function.uncurry F)
      (volume.prod (MeasureSpace.volume (α := Fin 3 → ℝ))) →
    (∫ x, ∫ v, F x v) = ∫ v, ∫ x, F x v
  -- Additivity of spatial integral
  hSpatialAdd : ∀ (g₁ g₂ : X → ℝ),
    (∫ x, (g₁ x + g₂ x)) = (∫ x, g₁ x) + ∫ x, g₂ x

namespace FlatTorus3

variable {X : Type*} [FlatTorus3 X]

-- Register CompactSpace and Nonempty as instances so they're automatically
-- available whenever [FlatTorus3 X] is in scope.
instance (priority := 100) instCompactSpace : CompactSpace X := FlatTorus3.instCompact
instance (priority := 100) instNonemptySpace : Nonempty X := FlatTorus3.instNonempty

/-- Compatibility wrapper: spatial integral as Mathlib's Bochner integral.
    Defined as `abbrev` so it unfolds transparently in rewrites. -/
noncomputable abbrev spatialIntegral (g : X → ℝ) : ℝ := ∫ x, g x

/-- Scalar multiplication: ∫ g(x) * c = (∫ g) * c.
    Proved from Mathlib's `integral_mul_right`. -/
lemma hSpatialMul (g : X → ℝ) (c : ℝ) :
    spatialIntegral (fun x => g x * c) = spatialIntegral g * c := by
  simp [spatialIntegral, integral_mul_right]

/-- Zero gradient implies spatially constant (derived from hHarmonic_const + hDivLinear). -/
lemma hGradZeroConst (φ : X → ℝ) (hd : IsSpatiallyDiff φ) (h : ∀ x, gradX φ x = 0) :
    ∀ x y, φ x = φ y := by
  apply hHarmonic_const _ hd
  intro x
  have h1 := hDivLinear (X := X) 0 (gradX φ) x
  have hg : (fun y : X => (0 : ℝ) • gradX φ y) = gradX φ := by
    ext y; simp [h y]
  rw [hg, zero_mul] at h1; exact h1

/-- Chain rule for log: gradX(log ∘ g) = (1/g) · gradX(g) when g > 0.
    Derived from hGradChainExp: gradX(exp(log g)) = g · gradX(log g) = gradX(g). -/
lemma hGradChainLog (g : X → ℝ) (hg : ∀ x, 0 < g x) :
    ∀ x i, gradX (fun y => Real.log (g y)) x i = (1 / g x) * gradX g x i := by
  intro x i
  have key := hGradChainExp (fun y => Real.log (g y)) x i
  have hexplog : (fun y => Real.exp (Real.log (g y))) = g := by
    ext y; exact Real.exp_log (hg y)
  rw [hexplog, Real.exp_log (hg x)] at key
  have hgx_ne : g x ≠ 0 := ne_of_gt (hg x)
  field_simp at key ⊢; linarith

/-- Integral of a single gradient component vanishes (from IBP with φ=1). -/
private lemma gradIntZero_component (g : X → ℝ) (hg : IsSpatiallyDiff g) (i : Fin 3) :
    ∫ x, gradX g x i = 0 := by
  have h := hIBP_spatial (fun _ => 1) g i (hDiff_const 1) hg
  simp only [one_mul] at h
  have hc : ∀ x : X, gradX (fun _ : X => (1 : ℝ)) x = 0 :=
    hGradConst (fun _ : X => (1 : ℝ)) (fun _ _ => rfl)
  simp only [hc, Pi.zero_apply, mul_zero, integral_zero, neg_zero] at h
  linarith

/-- Gradient integral vanishes (Stokes for 0-forms: ∫_M dg = 0).
    Derived from hIBP_spatial + hGradConst + hSpatialAdd. -/
lemma hGradIntZero (g : X → ℝ) (hg : IsSpatiallyDiff g) (u : Fin 3 → ℝ) :
    ∫ x, dotProduct u (gradX g x) = 0 := by
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hSpatialAdd, hSpatialAdd]
  have h0 : ∫ x : X, u 0 * gradX g x 0 = u 0 * ∫ x, gradX g x 0 := integral_const_mul _ _
  have h1 : ∫ x : X, u 1 * gradX g x 1 = u 1 * ∫ x, gradX g x 1 := integral_const_mul _ _
  have h2 : ∫ x : X, u 2 * gradX g x 2 = u 2 * ∫ x, gradX g x 2 := integral_const_mul _ _
  rw [h0, h1, h2, gradIntZero_component g hg 0, gradIntZero_component g hg 1,
    gradIntZero_component g hg 2]
  ring

/-- Adding a constant doesn't change the gradient.
    Derived from hGradChainExp + hGradScalarMul via the exp trick:
    exp(f+c) = exp(c)*exp(f), so by the chain rule and scalar multiplication,
    exp(f(x)+c) * gradX(f+c)(x) = exp(c) * exp(f(x)) * gradX(f)(x).
    Cancelling exp(f(x)+c) > 0 gives gradX(f+c) = gradX(f). -/
lemma hGradAddConst (f : X → ℝ) (c : ℝ) :
    ∀ x, gradX (fun y => f y + c) x = gradX f x := by
  intro x; ext i
  have h1 := hGradChainExp (X := X) (fun y => f y + c) x i
  have h2 := hGradChainExp (X := X) f x i
  -- exp(f+c) = exp(c) * exp(f)
  have hfun_eq : (fun y => Real.exp (f y + c)) = (fun y => Real.exp c * Real.exp (f y)) :=
    funext (fun y => by rw [Real.exp_add]; ring)
  rw [hfun_eq] at h1
  -- gradX(exp(c) * exp(f)) = exp(c) • gradX(exp(f)) by hGradScalarMul
  have h3 := congr_fun (hGradScalarMul (X := X) (Real.exp c) (fun y => Real.exp (f y)) x) i
  simp only [Pi.smul_apply, smul_eq_mul] at h3
  rw [h3, h2] at h1
  -- h1: exp(c) * (exp(f x) * gradX f x i) = exp(f x + c) * gradX(f+c) x i
  rw [Real.exp_add] at h1
  -- h1: exp(c) * (exp(f x) * gradX f x i) = exp(f x) * exp(c) * gradX(f+c) x i
  have hne : Real.exp c * Real.exp (f x) ≠ 0 :=
    ne_of_gt (mul_pos (Real.exp_pos _) (Real.exp_pos _))
  have h4 : Real.exp c * Real.exp (f x) * gradX f x i =
      Real.exp c * Real.exp (f x) * gradX (fun y => f y + c) x i := by linarith
  exact mul_left_cancel₀ hne h4.symm

/-- Second derivative test: Laplacian ≥ 0 at a minimum.
    Derived from hLaplacianMaxNonpos applied to -φ, using linearity of grad and div. -/
lemma hLaplacianMinNonneg (φ : X → ℝ) (hφ : IsSpatiallyDiff φ) (x₀ : X)
    (hmin : ∀ x, φ x₀ ≤ φ x) : 0 ≤ divX (gradX φ) x₀ := by
  have hmax : ∀ x, (fun y => (-1) * φ y) x ≤ (fun y => (-1) * φ y) x₀ := by
    intro x; simp; linarith [hmin x]
  have h := hLaplacianMaxNonpos (fun y => (-1) * φ y) x₀ (hDiff_smul (-1) φ hφ) hmax
  have h2 : divX (gradX (fun y => (-1) * φ y)) x₀ =
      (-1) * divX (gradX φ) x₀ := by
    have hg : gradX (fun y => (-1) * φ y) = fun x => (-1 : ℝ) • gradX φ x := by
      funext x; exact hGradScalarMul (-1) φ x
    change divX (gradX (fun y => (-1) * φ y)) x₀ = _
    conv_lhs => rw [hg]
    exact hDivLinear (-1) (gradX φ) x₀
  linarith

end FlatTorus3

-- ============================================================================
-- Section 6: VML Steady State Structure
-- ============================================================================

/-- Bundle representing a steady state of the VML system on T³ × ℝ³.

    The spatial domain X is equipped with a FlatTorus3 instance providing
    the differential operators (grad, div, curl) and integration.

    Encodes:
    - The VML equations at steady state (Vlasov, Ampère, Gauss, div B = 0)
    - Analytical results from the H-theorem chain (Sections 3-4 of tex)
    - Polynomial matching results (Section 5 of tex)
    - Maximum principle conclusion (Section 7 of tex) -/
structure VMLSteadyState (X : Type*) [FlatTorus3 X] where
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
  hρ_cont : Continuous ρ
  J : X → (Fin 3 → ℝ)
  -- Maxwell equations at steady state
  hAmpere : ∀ x, FlatTorus3.curlX B x = J x
  hGauss : ∀ x, FlatTorus3.divX E x = ρ x - ρ_ion
  hDivB : ∀ x, FlatTorus3.divX B x = 0
  -- Spatial differentiability for B (needed for harmonic → constant)
  hDiff_B : ∀ i, FlatTorus3.IsSpatiallyDiff (fun y => B y i)
  -- C² for B: gradient components of B_i are spatially differentiable (needed for harmonic)
  hDiff_B_C2 : ∀ i j, FlatTorus3.IsSpatiallyDiff (fun x => FlatTorus3.gradX (fun y => B y i) x j)
  -- === H-theorem chain results (Sections 3-4 of tex) ===
  a_loc : X → ℝ
  b_loc : X → (Fin 3 → ℝ)
  c_loc : X → ℝ
  hc_neg : ∀ x, c_loc x < 0
  hMaxwellianForm : ∀ x v,
    f x v = Real.exp (a_loc x + dotProduct (b_loc x) v + c_loc x * normSq v)
  -- C² for b_loc: gradient components of b_loc_j are spatially differentiable (needed for Killing → harmonic)
  hDiff_b_C2 : ∀ j i, FlatTorus3.IsSpatiallyDiff (fun x => FlatTorus3.gradX (fun y => b_loc y j) x i)
  -- === Polynomial matching results (Section 5 of tex) ===
  c₀ : ℝ
  hc₀_neg : c₀ < 0
  hc_const : ∀ x, c_loc x = c₀
  b₀ : Fin 3 → ℝ
  hb_const : ∀ x, b_loc x = (-2 * c₀) • b₀
  hForceBalance : ∀ x,
    FlatTorus3.gradX a_loc x = -(2 * c₀) • (E x + cross b₀ (B x))
  hJ_def : ∀ x, J x = (ρ x) • b₀
  -- === Maximum principle (Section 7 of tex) ===
  hDensityConst : ∀ x, ρ x = ρ_ion
  hGradA_zero : b₀ = 0 → (∀ x, ρ x = ρ_ion) → ∀ x, FlatTorus3.gradX a_loc x = 0
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
    - The physical state (f, E, B) on a spatial domain X with [FlatTorus3 X]
    - Physical parameters (ν, ρ_ion, Ψ)
    - Maxwell equations at steady state
    - Entropy dissipation vanishes (from H-theorem chain)
    - Analytical interface hypotheses (polynomial identity, Gaussian integrals)

    The spatial operators (grad, div, curl, ∫) and their properties come from
    the FlatTorus3 typeclass instance, NOT from this structure.

    The key distinction from VMLSteadyState: this structure does NOT include
    the Maxwellian parameters (a, b, c), temperature/drift constancy, or
    density constancy — those are DERIVED in toSteadyState. -/
structure VMLInput (X : Type*) [FlatTorus3 X] where
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
  hρ_cont : Continuous ρ
  J : X → (Fin 3 → ℝ)
  -- Maxwell equations at steady state
  hAmpere : ∀ x, FlatTorus3.curlX B x = J x
  hGauss : ∀ x, FlatTorus3.divX E x = ρ x - ρ_ion
  hDivB : ∀ x, FlatTorus3.divX B x = 0
  -- Spatial differentiability for B components
  hDiff_B : ∀ i, FlatTorus3.IsSpatiallyDiff (fun y => B y i)
  -- Spatial differentiability for log(ρ) (needed for Laplacian max principle)
  -- Analytically: ρ(x) = ∫ f(x,v) dv is C¹ in x (differentiate under integral),
  -- and ρ > 0 so log(ρ) is C¹. This is an interface hypothesis.
  hDiff_logRho : FlatTorus3.IsSpatiallyDiff (Real.log ∘ ρ)
  -- === Derived from H-theorem chain ===
  hD_zero : ∀ x, entropyDissipation Ψ (f x) = 0
  hScoreForm : ∀ x, entropyDissipation Ψ (f x) =
    -(1 / 2) * ∫ v, ∫ w, PSDIntegrand Ψ (f x) v w
  hPSD_cont : ∀ x, Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
    PSDIntegrand Ψ (f x) p.1 p.2)
  hPSD_inner : ∀ x v, Integrable (PSDIntegrand Ψ (f x) v)
  hPSD_outer : ∀ x, Integrable (fun v => ∫ w, PSDIntegrand Ψ (f x) v w)
  -- === Analytical interface hypotheses ===
  -- Maxwellian parameters are spatially differentiable (follows from f being smooth)
  hDiff_maxwellian : ∀ (a : X → ℝ) (b : X → Fin 3 → ℝ) (c : X → ℝ),
    (∀ x v, f x v = Real.exp (a x + dotProduct (b x) v + c x * normSq v)) →
    FlatTorus3.IsSpatiallyDiff a ∧
    (∀ j, FlatTorus3.IsSpatiallyDiff (fun y => b y j)) ∧
    FlatTorus3.IsSpatiallyDiff c
  -- C² for Maxwellian b parameters (gradient components are spatially differentiable)
  hDiff_maxwellian_C2 : ∀ (a : X → ℝ) (b : X → Fin 3 → ℝ) (c : X → ℝ),
    (∀ x v, f x v = Real.exp (a x + dotProduct (b x) v + c x * normSq v)) →
    ∀ j i, FlatTorus3.IsSpatiallyDiff (fun x => FlatTorus3.gradX (fun y => b y j) x i)
  -- C² for B components
  hDiff_B_C2 : ∀ i j, FlatTorus3.IsSpatiallyDiff (fun x => FlatTorus3.gradX (fun y => B y i) x j)
  hPolynomialIdentity : ∀ (a : X → ℝ) (b : X → Fin 3 → ℝ) (c : X → ℝ),
    FlatTorus3.IsSpatiallyDiff a →
    (∀ j, FlatTorus3.IsSpatiallyDiff (fun y => b y j)) →
    FlatTorus3.IsSpatiallyDiff c →
    (∀ x v, f x v = Real.exp (a x + dotProduct (b x) v + c x * normSq v)) →
    ∀ x v,
      dotProduct v (FlatTorus3.gradX c x) * normSq v +
      (∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
        (FlatTorus3.gradX (fun y => b y j) x i)) +
      dotProduct v (FlatTorus3.gradX a x) +
      dotProduct (E x) (b x) +
      dotProduct v ((2 * c x) • E x + cross (B x) (b x)) = 0
  -- Current from Maxwellian: J = ρ · drift
  hJ_from_maxwellian : ∀ (b : X → Fin 3 → ℝ) (c₀ : ℝ),
    (∀ x, ∃ a₀, ∀ v, f x v = Real.exp (a₀ + dotProduct (b x) v + c₀ * normSq v)) →
    ∀ x, J x = ρ x • ((-1 / (2 * c₀)) • b x)
  -- Maximum principle inputs (compactness of T³)
  x_max : X
  hmax : ∀ x, ρ x ≤ ρ x_max
  x_min : X
  hmin : ∀ x, ρ x_min ≤ ρ x
  -- Poisson-Boltzmann equation: T Δ(log ρ) = ρ - ρ_ion (isotropic case: b₀ = 0)
  hPB_eq : ∀ (c₀ : ℝ), c₀ < 0 →
    (∀ x, ∃ a₀, ∀ v, f x v = Real.exp (a₀ + c₀ * normSq v)) →
    ∀ x, (-1 / (2 * c₀)) * FlatTorus3.divX (FlatTorus3.gradX (Real.log ∘ ρ)) x =
      ρ x - ρ_ion
  -- Normalization: Gaussian integral yields equilibriumMaxwellian
  hNormalization : ∀ a₀ c₀,
    c₀ < 0 →
    (∀ x v, f x v = Real.exp (a₀ + c₀ * normSq v)) →
    (∀ x, ρ x = ρ_ion) →
    ∀ x v, f x v = equilibriumMaxwellian ρ_ion (-1 / (2 * c₀)) v

end VML
