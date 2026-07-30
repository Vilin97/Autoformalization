/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixFiveInnerInertia
import McKayConjecture.InductiveMcKay.AlternatingSixFiveInnerProjectiveRowReduction

/-!
# Complete projective data for outer-free five-local `A₆` rows

Combining the four-coset inertia criterion with the central-generator
projective reduction removes the abstract surjectivity premise for every
ambient row on which the outer automorphism group acts freely.

The CT-position specialization remains conditional on a proposed semantic
position identification and its two ambient generator bridges.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveOuterFreeProjectiveRowsFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- A central-block row moved by both audited generators and their product
has complete exact-normalizer projective data. -/
def alternatingSixFiveInnerProjectiveRowDataOfGeneratorsMoved
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : AlternatingSixFiveCentralBlockRowMatchingEquivariant T)
    (r : AlternatingSixAmbientPPrimeRowIndex 5)
    (hAlphaOne :
      alternatingSixAmbientPPrimeAlphaOneRowPermutation T 5 r ≠ r)
    (hAlphaTwo :
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation T 5 r ≠ r)
    (hAlphaOneAlphaTwo :
      alternatingSixAmbientPPrimeAlphaOneRowPermutation T 5
          (alternatingSixAmbientPPrimeAlphaTwoRowPermutation T 5 r) ≠
        r) :
    ExactNormalizerProjectiveRowData
      (alternatingSixFiveCentralBlockConcreteCharacterTableCertificate
        T h).toEquivariantMcKayEquiv
      (alternatingSixAmbientPPrimeCharacterEquiv T 5 r) :=
  alternatingSixFiveInnerProjectiveRowData T h r
    (alternatingSixFiveInnerCharacterStabilizer_surjective_of_generatorsMoved
      T r hAlphaOne hAlphaTwo hAlphaOneAlphaTwo)

namespace AlternatingSixFiveCTblLibRowIdentification

/-- Under a semantic ambient CT-position identification and the two
generator bridges, every one of the twelve audited free-orbit positions
has complete central-block projective data. -/
def outerFreeInnerProjectiveRowData
    (identification : AlternatingSixFiveCTblLibRowIdentification)
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : AlternatingSixFiveCentralBlockRowMatchingEquivariant T)
    (hAlphaOne :
      identification.AmbientCorrectedAlphaOneBridge T)
    (hAlphaTwo :
      identification.AmbientCorrectedAlphaTwoBridge T)
    (i : Fin 24)
    (hi : AlternatingSixFiveOuterFreeCTPosition i) :
    ExactNormalizerProjectiveRowData
      (alternatingSixFiveCentralBlockConcreteCharacterTableCertificate
        T h).toEquivariantMcKayEquiv
      (alternatingSixAmbientPPrimeCharacterEquiv T 5
        (identification.ambientPositionEquiv i)) :=
  alternatingSixFiveInnerProjectiveRowData T h
    (identification.ambientPositionEquiv i)
    (identification.innerCharacterStabilizer_surjective_of_outerFreePosition
      T hAlphaOne hAlphaTwo i hi)

end AlternatingSixFiveCTblLibRowIdentification

end InductiveMcKay
end McKayConjecture
