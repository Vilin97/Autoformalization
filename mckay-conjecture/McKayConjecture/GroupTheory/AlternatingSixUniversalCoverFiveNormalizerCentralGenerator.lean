/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurFiveNormalizerCentralGenerator
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverFiveNormalizerSemidirect

/-!
# The central generator in the fixed five-normalizer of `6.A₆`

The concrete five-normalizer calculation identifies its distinguished
element with the central generator of the presented Schur cover.  This file
tracks that element through the canonical equivalence of universal central
extensions and through the final Sylow conjugation used to reach the fixed
Sylow-five subgroup.

The Sylow conjugator does not alter the transported generator: the latter is
central in the canonical universal cover.  Thus the result below identifies
the concrete element with a specified element of the *actual fixed*
normalizer, rather than merely with an element of a conjugate normalizer.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

local instance alternatingSixUniversalCoverFiveCentralGeneratorFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The distinguished order-six central generator in the canonical
universal cover, transported from the presented Schur cover. -/
def alternatingSixUniversalCoverCentralGenerator :
    AlternatingSixUniversalCover :=
  alternatingSixSchurEquivUniversalCover
    alternatingSixSchurFiveCentral

/-- The distinguished generator remains central after transport to the
canonical universal cover. -/
theorem alternatingSixUniversalCoverCentralGenerator_mem_center :
    alternatingSixUniversalCoverCentralGenerator ∈
      Subgroup.center AlternatingSixUniversalCover :=
  MulEquivClass.apply_mem_center
    alternatingSixSchurEquivUniversalCover
    alternatingSixSchurFiveCentral_mem_center

/-- The distinguished central generator, regarded as an element of the
normalizer of the fixed Sylow-five subgroup. -/
def alternatingSixFiveActualNormalizerCentralGenerator :
    SylowNormalizer (alternatingSixUniversalCoverSylow 5) :=
  ⟨alternatingSixUniversalCoverCentralGenerator,
    Subgroup.center_le_normalizer
      (alternatingSixUniversalCoverSylow 5 :
        Set AlternatingSixUniversalCover)
      alternatingSixUniversalCoverCentralGenerator_mem_center⟩

/-- The semidirect-product central generator maps to the distinguished
central element of the actual fixed Sylow-five normalizer.

The last leg of the normalizer equivalence is conjugation by
`alternatingSixSchurFiveSylowConjugator`; centrality is what removes that
otherwise noncanonical conjugation from the value of this element. -/
@[simp]
theorem
    alternatingSixFiveNormalizerSemidirectEquivUniversalCoverNormalizer_centralGenerator :
    alternatingSixFiveNormalizerSemidirectEquivUniversalCoverNormalizer
        alternatingSixFiveNormalizerSemidirectCentralGenerator =
      alternatingSixFiveActualNormalizerCentralGenerator := by
  apply Subtype.ext
  change
    alternatingSixSchurFiveSylowConjugator *
          alternatingSixSchurEquivUniversalCover
            (((cyclicThreeTimesCyclicFiveInversionSemidirectEquivSchurFiveNormalizer
                alternatingSixFiveNormalizerSemidirectCentralGenerator :
              SylowNormalizer alternatingSixSchurFiveSylow) :
              AlternatingSixSchurPresentedGroup)) *
        alternatingSixSchurFiveSylowConjugator⁻¹ =
      alternatingSixUniversalCoverCentralGenerator
  rw [
    cyclicThreeTimesCyclicFiveInversionSemidirectEquivSchurFiveNormalizer_centralGenerator
  ]
  change
    alternatingSixSchurFiveSylowConjugator *
          alternatingSixUniversalCoverCentralGenerator *
        alternatingSixSchurFiveSylowConjugator⁻¹ =
      alternatingSixUniversalCoverCentralGenerator
  rw [
    (Subgroup.mem_center_iff.mp
      alternatingSixUniversalCoverCentralGenerator_mem_center
      alternatingSixSchurFiveSylowConjugator),
    mul_assoc,
    mul_inv_cancel,
    mul_one
  ]

end GroupTheory
end McKayConjecture
