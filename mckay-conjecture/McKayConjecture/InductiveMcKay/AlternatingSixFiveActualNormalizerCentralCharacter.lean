/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.AlternatingSixFiveNormalizerCentralCharacter
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverFiveNormalizerCentralGenerator
import McKayConjecture.InductiveMcKay.AlternatingSixFiveConcreteFiniteTable

/-!
# Central-character values on the actual five-normalizer of `6.A₆`

The concrete `C₃ × (C₅ ⋊ C₄)` table evaluates all twenty-four local rows
at its distinguished central generator.  The group-theoretic transport
identifies that generator with a specified central element of the fixed
Sylow-five normalizer in the canonical universal cover.

This file combines those two facts.  Its final theorem concerns the actual
normalizer characters used by the inductive-McKay table interface.  It does
not assert compatibility with any ambient character or proposed McKay row
matching.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory
open AlternatingSixFiveNormalizerSemidirectCharacterTable

local instance alternatingSixFiveActualNormalizerCentralCharacterFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- Values of the actual-normalizer enumeration on elements transported
from the concrete semidirect-product model. -/
@[simp]
theorem alternatingSixFiveActualNormalizerPPrimeCharacterEquiv_values
    (r : AlternatingSixFiveConcreteNormalizerRow)
    (g : AlternatingSixFiveNormalizerSemidirect) :
    (alternatingSixFiveActualNormalizerPPrimeCharacterEquiv r).1.values
        (alternatingSixFiveNormalizerSemidirectEquivUniversalCoverNormalizer
          g) =
      (alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv r).1.values
        g := by
  change
    ((alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv r).1.comap
        alternatingSixFiveNormalizerSemidirectEquivUniversalCoverNormalizer.symm).values
          (alternatingSixFiveNormalizerSemidirectEquivUniversalCoverNormalizer
            g) =
      (alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv r).1.values
        g
  simp

/-- Transport to the actual normalizer preserves the degree of every
enumerated local row. -/
@[simp]
theorem alternatingSixFiveActualNormalizerPPrimeCharacterEquiv_degree
    (r : AlternatingSixFiveConcreteNormalizerRow) :
    (alternatingSixFiveActualNormalizerPPrimeCharacterEquiv r).1.degree =
      (alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv r).1.degree :=
  rfl

/-- Exact value of every enumerated `5'`-character of the actual fixed
normalizer at its distinguished central generator. -/
theorem
    alternatingSixFiveActualNormalizerPPrimeCharacterEquiv_values_centralGenerator
    (r : AlternatingSixFiveConcreteNormalizerRow) :
    (alternatingSixFiveActualNormalizerPPrimeCharacterEquiv r).1.values
        alternatingSixFiveActualNormalizerCentralGenerator =
      ((alternatingSixFiveActualNormalizerPPrimeCharacterEquiv r).1.degree :
          ℂ) *
        AlternatingSixFiveNormalizerSemidirectCharacterTable.centralScalar r := by
  calc
    (alternatingSixFiveActualNormalizerPPrimeCharacterEquiv r).1.values
          alternatingSixFiveActualNormalizerCentralGenerator =
        (alternatingSixFiveActualNormalizerPPrimeCharacterEquiv r).1.values
          (alternatingSixFiveNormalizerSemidirectEquivUniversalCoverNormalizer
            alternatingSixFiveNormalizerSemidirectCentralGenerator) := by
      rw [
        alternatingSixFiveNormalizerSemidirectEquivUniversalCoverNormalizer_centralGenerator
      ]
    _ =
        (alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv r).1.values
          alternatingSixFiveNormalizerSemidirectCentralGenerator :=
      alternatingSixFiveActualNormalizerPPrimeCharacterEquiv_values _ _
    _ =
        ((alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv r).1.degree :
            ℂ) *
          AlternatingSixFiveNormalizerSemidirectCharacterTable.centralScalar r := by
      change
        (AlternatingSixFiveNormalizerSemidirectCharacterTable.pPrimeCharacterEquiv
            r).1.values
              alternatingSixFiveNormalizerSemidirectCentralGenerator =
          ((AlternatingSixFiveNormalizerSemidirectCharacterTable.pPrimeCharacterEquiv
              r).1.degree : ℂ) *
            AlternatingSixFiveNormalizerSemidirectCharacterTable.centralScalar r
      exact
        pPrimeCharacterEquiv_values_centralGenerator r
    _ =
        ((alternatingSixFiveActualNormalizerPPrimeCharacterEquiv r).1.degree :
            ℂ) *
          AlternatingSixFiveNormalizerSemidirectCharacterTable.centralScalar r := by
      rw [alternatingSixFiveActualNormalizerPPrimeCharacterEquiv_degree]

end InductiveMcKay
end McKayConjecture
