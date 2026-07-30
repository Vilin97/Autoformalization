/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAutomorphismStabilizerGeneration
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCTblLibInvariantSafeRowIdentification
import McKayConjecture.InductiveMcKay.AlternatingSixFiveOuterFreeProjectiveRows

/-!
# Twelve invariant-safe five-local projective rows for `A₆`

The invariant-safe position orientation transports the audited finite
candidate back to the existing central-block row matching.  Hence its four
semantic generator bridges, together with the unconditional stabilizer
generation theorem, imply ordinary equivariance of that matching.

For the twelve audited positions with free outer orbit, the two ambient
bridges also force character inertia to be entirely normalizer-inner.  The
central-generator reduction then supplies complete exact-normalizer
projective data.  Thus the endpoint below has only the four honest semantic
bridge obligations; it has no independent inertia, factor-set, or central
scalar premise.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveInvariantSafeOuterFreeFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The four semantic bridges for the invariant-safe orientation imply
ordinary equivariance of the existing central-block row matching. -/
theorem alternatingSixFiveInvariantSafeCentralBlockRowMatchingEquivariant
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hBridges :
      alternatingSixFiveCTblLibInvariantSafeRowIdentification
        |>.GeneratorActionBridges T) :
    AlternatingSixFiveCentralBlockRowMatchingEquivariant T := by
  have hEquivariant :=
    alternatingSixFiveCTblLibInvariantSafeRowIdentification
      |>.equivariant_of_generatorActionBridges_of_generation
        T hBridges alternatingSixFiveSylowAutStabilizerGeneration
  unfold AlternatingSixFiveCTblLibRowIdentification.Equivariant at hEquivariant
  rw [
    alternatingSixFiveCTblLibInvariantSafeRowIdentification_candidate
  ] at hEquivariant
  exact hEquivariant

/-- Any audited free-orbit position in the invariant-safe orientation has a
complete projective row from the four semantic bridge obligations alone. -/
def alternatingSixFiveInvariantSafeOuterFreeProjectiveRowData
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hBridges :
      alternatingSixFiveCTblLibInvariantSafeRowIdentification
        |>.GeneratorActionBridges T)
    (i : Fin 24)
    (hi : AlternatingSixFiveOuterFreeCTPosition i) :
    ExactNormalizerProjectiveRowData
      (alternatingSixFiveCentralBlockConcreteCharacterTableCertificate
        T
        (alternatingSixFiveInvariantSafeCentralBlockRowMatchingEquivariant
          T hBridges)).toEquivariantMcKayEquiv
      (alternatingSixAmbientPPrimeCharacterEquiv T 5
        (alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv i)) :=
  alternatingSixFiveCTblLibInvariantSafeRowIdentification
    |>.outerFreeInnerProjectiveRowData
      T
      (alternatingSixFiveInvariantSafeCentralBlockRowMatchingEquivariant
        T hBridges)
      hBridges.ambientAlphaOne hBridges.ambientAlphaTwo i hi

/-- The twelve free positions are packaged as a `Fin 12` family of complete
projective rows.  Their exact ambient row names are recorded by
`alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv_outerFree`. -/
def alternatingSixFiveInvariantSafeTwelveProjectiveRowData
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hBridges :
      alternatingSixFiveCTblLibInvariantSafeRowIdentification
        |>.GeneratorActionBridges T)
    (i : Fin 12) :
    ExactNormalizerProjectiveRowData
      (alternatingSixFiveCentralBlockConcreteCharacterTableCertificate
        T
        (alternatingSixFiveInvariantSafeCentralBlockRowMatchingEquivariant
          T hBridges)).toEquivariantMcKayEquiv
      (alternatingSixAmbientPPrimeCharacterEquiv T 5
        (alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv
          (alternatingSixFiveCTblLibInvariantSafeOuterFreePositionEquiv i).1)) :=
  alternatingSixFiveInvariantSafeOuterFreeProjectiveRowData
    T hBridges
    (alternatingSixFiveCTblLibInvariantSafeOuterFreePositionEquiv i).1
    (alternatingSixFiveCTblLibInvariantSafeOuterFreePositionEquiv i).2

end InductiveMcKay
end McKayConjecture
