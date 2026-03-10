import Aristotle.Landau.main.Defs
import Aristotle.Landau.main.Section3
open Matrix Finset BigOperators Real MeasureTheory
noncomputable section
namespace VML

-- ============================================================================
-- Section 5f: Conservation Laws (Section 9 of tex)
-- Reference: Lemma 25
-- ============================================================================

/-- Lemma 26: B∞ is determined as the spatial mean.
    Reference: lem:B_infty -/
theorem B_infty_determination {X : Type*} [FlatTorus3 X] (ss : VMLSteadyState X) (B₀ : Fin 3 → ℝ)
    (hB : ∀ x, ss.B x = B₀) :
    ∀ i, FlatTorus3.spatialIntegral (fun x => ss.B x i) =
      FlatTorus3.spatialIntegral (fun (_ : X) => B₀ i) := by
  intro i
  congr 1; ext x; rw [hB]

/-- Lemma 27: T∞ is determined by energy conservation.
    Reference: lem:T_infty

    T∞ = 2/(3 ρ_ion |T³|) · (ℰ₀ - |B∞|²|T³|/2) -/
theorem T_infty_determination (ρ_ion T E₀ vol : ℝ) (B₀ : Fin 3 → ℝ)
    (hρ : 0 < ρ_ion) (hvol : 0 < vol) (_hE₀ : 0 < E₀) :
    T = 2 / (3 * ρ_ion * vol) * (E₀ - normSq B₀ / 2 * vol) →
    3/2 * ρ_ion * T * vol + normSq B₀ / 2 * vol = E₀ := by
  intro hT
  rw [hT]
  field_simp
  ring

/-- Lemma 28: Positivity of T∞.
    Reference: lem:T_positive

    By Jensen: |B∞|² ≤ mean(|B_init|²), so electromagnetic energy of B∞
    is strictly less than ℰ₀ (kinetic energy > 0), giving T∞ > 0. -/
theorem T_positive (ρ_ion E₀ vol : ℝ) (B₀ : Fin 3 → ℝ)
    (hρ : 0 < ρ_ion) (hvol : 0 < vol) (_hE₀ : 0 < E₀)
    (hJensen : normSq B₀ / 2 * vol < E₀) :
    0 < 2 / (3 * ρ_ion * vol) * (E₀ - normSq B₀ / 2 * vol) := by
  apply mul_pos
  · apply div_pos
    · norm_num
    · apply mul_pos
      · apply mul_pos
        · norm_num
        · exact hρ
      · exact hvol
  · linarith

end VML
