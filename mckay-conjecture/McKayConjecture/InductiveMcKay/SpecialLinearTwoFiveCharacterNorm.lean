/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveCharacterOrthogonality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.FinGroupCharZero

/-!
# From the symbolic `SL(2, 𝔽₅)` table to representation norms

Once a concrete finite-dimensional representation has the prescribed
values on the nine class representatives, the executable class
decomposition and symbolic orthogonality calculation give its character
norm immediately.  The norm-one criterion then proves simplicity.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CategoryTheory GroupTheory

/-- A concrete representation realizing one symbolic row has unnormalized
character norm `120`. -/
theorem specialLinearTwoFiveFDRep_character_norm
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (r : SpecialLinearTwoFiveCharacterRow)
    (V : FDRep ℂ SpecialLinearTwoFive)
    (hvalues :
      ∀ c : SpecialLinearTwoFiveConjugacyClass,
        V.character
            (specialLinearTwoFiveConjugacyRepresentative c) =
          specialLinearTwoFiveCharacterTableValue t r c) :
    (∑ x : SpecialLinearTwoFive,
      V.character x * V.character x⁻¹) = 120 := by
  rw [specialLinearTwoFive_sum_by_conjugacyClasses
    (fun x : SpecialLinearTwoFive =>
      V.character x * V.character x⁻¹)]
  · calc
      (∑ c : SpecialLinearTwoFiveConjugacyClass,
          specialLinearTwoFiveConjugacyClassSize c •
            (V.character
                (specialLinearTwoFiveConjugacyRepresentative c) *
              V.character
                (specialLinearTwoFiveConjugacyRepresentative c)⁻¹)) =
          specialLinearTwoFiveCharacterTableWeightedPairing t r r := by
            apply Finset.sum_congr rfl
            intro c _
            have hinv :
                V.character
                    (specialLinearTwoFiveConjugacyRepresentative c)⁻¹ =
                  V.character
                    (specialLinearTwoFiveConjugacyRepresentative c) := by
              obtain ⟨z, hz⟩ :=
                (isConj_iff.mp
                  (specialLinearTwoFiveConjugacyRepresentative_isConj_inv c))
              rw [← hz]
              exact
                FDRep.char_conj V
                  (specialLinearTwoFiveConjugacyRepresentative c) z
            rw [hinv, hvalues c]
            simp [nsmul_eq_mul, mul_assoc]
      _ = 120 := by
        rw [specialLinearTwoFiveCharacterTableWeightedPairing_eq
          t ht r r]
        simp
  · intro x y hxy
    obtain ⟨z, rfl⟩ := isConj_iff.mp hxy
    symm
    rw [FDRep.char_conj V x z]
    have hinv :
        (z * x * z⁻¹)⁻¹ = z * x⁻¹ * z⁻¹ := by
      group
    rw [hinv, FDRep.char_conj V x⁻¹ z]

/-- A concrete row with the prescribed values is simple. -/
theorem specialLinearTwoFiveFDRep_simple
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (r : SpecialLinearTwoFiveCharacterRow)
    (V : FDRep ℂ SpecialLinearTwoFive)
    (hvalues :
      ∀ c : SpecialLinearTwoFiveConjugacyClass,
        V.character
            (specialLinearTwoFiveConjugacyRepresentative c) =
          specialLinearTwoFiveCharacterTableValue t r c) :
    Simple V := by
  rw [FDRep.simple_iff_char_is_norm_one]
  rw [GroupTheory.natCard_specialLinearTwoFive]
  exact
    specialLinearTwoFiveFDRep_character_norm
      t ht r V hvalues

end InductiveMcKay
end McKayConjecture
