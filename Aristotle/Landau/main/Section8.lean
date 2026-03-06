import Aristotle.Landau.main.Defs
import Aristotle.Landau.main.Section6
set_option linter.all false
open Matrix Finset BigOperators Real MeasureTheory
noncomputable section
namespace VML

-- ============================================================================
-- Section 5e: Magnetic Field and Compatibility (Section 8 of tex)
-- Reference: Lemma 23
-- ============================================================================

/-- Lemma 23 (Uniform magnetic field is compatible with Maxwellian equilibrium).
    Reference: lem:B_compatible

    For any constant B∞ and any isotropic Maxwellian f∞(v) ∝ exp(-|v|²/(2T∞)):
    (v × B∞) · ∇ᵥf∞ = 0 for all v.

    Proof: ∇ᵥf∞ = -(v/T∞)f∞, so (v × B∞) · ∇ᵥf∞ ∝ (v × B∞) · v = 0
    since v × B∞ ⊥ v. -/
theorem B_compatible_maxwellian (B_infty : Fin 3 → ℝ) :
    ∀ v : Fin 3 → ℝ, dotProduct (cross v B_infty) v = 0 := by
  intro v
  have h0 : cross v B_infty 0 = v 1 * B_infty 2 - v 2 * B_infty 1 := by
    simp [cross]
  have h1 : cross v B_infty 1 = v 2 * B_infty 0 - v 0 * B_infty 2 := by
    simp [cross]
  have h2 : cross v B_infty 2 = v 0 * B_infty 1 - v 1 * B_infty 0 := by
    simp [cross]
  simp only [dotProduct, Fin.sum_univ_three, h0, h1, h2]
  ring

/-- Lemma 22: Magnetic field is spatially constant.
    Reference: lem:B_constant

    With u∞ = 0, J = 0 so ∇×B = 0. Combined with ∇·B = 0,
    each Bᵢ is harmonic on T³, hence constant. -/
theorem magnetic_field_constant {X : Type*} [FlatTorus3 X] (ss : VMLSteadyState X) :
    ∃ B₀ : Fin 3 → ℝ, ∀ x, ss.B x = B₀ := by
  have hb0 := bulk_velocity_zero ss
  -- Step 1: J = 0
  have hJ_zero : ∀ x, ss.J x = 0 := by
    intro x; rw [ss.hJ_def, hb0, smul_zero]
  -- Step 2: curl B = 0
  have hcurl_zero : ∀ x, FlatTorus3.curlX ss.B x = 0 := by
    intro x; rw [ss.hAmpere]; exact hJ_zero x
  -- Step 3: Each component is harmonic
  have hBi_harmonic := FlatTorus3.hCurlZeroDivZeroHarmonic ss.B ss.hDiff_B ss.hDiff_B_C2 hcurl_zero ss.hDivB
  -- Step 4: Each component is constant
  have hBi_const : ∀ i, ∀ x y, ss.B x i = ss.B y i := by
    intro i; exact FlatTorus3.hHarmonic_const (fun y => ss.B y i) (ss.hDiff_B i) (hBi_harmonic i)
  -- Extract the constant value from x₀
  exact ⟨fun i => ss.B ss.x₀ i, fun x => funext (fun i => hBi_const i x ss.x₀)⟩

end VML
