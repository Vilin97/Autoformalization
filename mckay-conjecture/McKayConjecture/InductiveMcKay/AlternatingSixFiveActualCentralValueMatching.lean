/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixFiveActualNormalizerCentralCharacter
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCentralBlockRowBridgeEquivariance

/-!
# Actual normalized central-value matching for the five-local `A₆` rows

The existing ambient calculation and concrete central-block row bijection
give the advertised central scalar on the ambient side.  The
actual-normalizer transport gives the same scalar on the local side.  This
file composes precisely those two results.

The cross-multiplied theorem is the division-free form of equality of
normalized character values; the following theorem records the literal
quotient equality as well.  Neither statement asserts full character-table,
stabilizer, factor-set, or projective compatibility.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveActualCentralValueMatchingFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- Under the explicit five-local row bijection, the actual ambient and
actual-normalizer characters have the same normalized central value,
expressed without division. -/
theorem alternatingSixFiveCentralBlockRowMatching_actualCentralCross
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (r : AlternatingSixAmbientPPrimeRowIndex 5) :
    (alternatingSixAmbientPPrimeCharacterEquiv T 5 r).1.values
          alternatingSixAmbientCanonicalCentralGenerator *
        ((alternatingSixFiveActualNormalizerPPrimeCharacterEquiv
              (alternatingSixAmbientFivePPrimeCentralBlockRowEquiv r)).1.degree :
          ℂ) =
      (alternatingSixFiveActualNormalizerPPrimeCharacterEquiv
            (alternatingSixAmbientFivePPrimeCentralBlockRowEquiv r)).1.values
          alternatingSixFiveActualNormalizerCentralGenerator *
        ((alternatingSixAmbientPPrimeCharacterEquiv T 5 r).1.degree : ℂ) := by
  rw [
    alternatingSixFiveCentralBlockRowMatching_ambientCentralValue,
    alternatingSixFiveActualNormalizerPPrimeCharacterEquiv_values_centralGenerator
  ]
  ring

/-- Literal equality of the two normalized central-generator values under
the explicit five-local row bijection. -/
theorem
    alternatingSixFiveCentralBlockRowMatching_normalizedActualCentralValue
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (r : AlternatingSixAmbientPPrimeRowIndex 5) :
    (alternatingSixAmbientPPrimeCharacterEquiv T 5 r).1.values
          alternatingSixAmbientCanonicalCentralGenerator /
        ((alternatingSixAmbientPPrimeCharacterEquiv T 5 r).1.degree : ℂ) =
      (alternatingSixFiveActualNormalizerPPrimeCharacterEquiv
            (alternatingSixAmbientFivePPrimeCentralBlockRowEquiv r)).1.values
          alternatingSixFiveActualNormalizerCentralGenerator /
        ((alternatingSixFiveActualNormalizerPPrimeCharacterEquiv
              (alternatingSixAmbientFivePPrimeCentralBlockRowEquiv r)).1.degree :
          ℂ) := by
  have hambientDegree :
      ((alternatingSixAmbientPPrimeCharacterEquiv T 5 r).1.degree : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (alternatingSixAmbientPPrimeCharacterEquiv T 5 r).1.degree_ne_zero
  have hlocalDegree :
      ((alternatingSixFiveActualNormalizerPPrimeCharacterEquiv
            (alternatingSixAmbientFivePPrimeCentralBlockRowEquiv r)).1.degree :
          ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (alternatingSixFiveActualNormalizerPPrimeCharacterEquiv
          (alternatingSixAmbientFivePPrimeCentralBlockRowEquiv r)).1.degree_ne_zero
  rw [
    alternatingSixFiveCentralBlockRowMatching_ambientCentralValue,
    alternatingSixFiveActualNormalizerPPrimeCharacterEquiv_values_centralGenerator
  ]
  field_simp

end InductiveMcKay
end McKayConjecture
