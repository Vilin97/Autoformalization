/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurFiveNormalizerProduct
import McKayConjecture.GroupTheory.CyclicFiveInversionSemidirect

/-!
# Semidirect-product model of the presented-cover five-normalizer

Combining the exact normalizer calculation with the concrete dicyclic
presentation identifies the normalizer as
`C₃ × (C₅ ⋊ C₄)`, where the generator of `C₄` acts by inversion.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- The exact normalizer in the presented sixfold cover, expressed as
`C₃ × (C₅ ⋊ C₄)` with the inversion action. -/
def cyclicThreeTimesCyclicFiveInversionSemidirectEquivSchurFiveNormalizer :
    Multiplicative (ZMod 3) × CyclicFiveInversionSemidirect ≃*
      Subgroup.normalizer
        (alternatingSixSchurFiveSylow :
          Set AlternatingSixSchurPresentedGroup) :=
  (MulEquiv.prodCongr
      (MulEquiv.refl (Multiplicative (ZMod 3)))
      quaternionFiveEquivCyclicFiveInversionSemidirect.symm).trans
    cyclicThreeTimesQuaternionFiveEquivSchurFiveNormalizer

/-- The normalizer has order sixty in the semidirect-product model. -/
theorem natCard_alternatingSixSchurFiveNormalizer_semidirect :
    Nat.card
        (Subgroup.normalizer
          (alternatingSixSchurFiveSylow :
            Set AlternatingSixSchurPresentedGroup)) =
      60 := by
  exact natCard_normalizer_alternatingSixSchurFiveSylow

end GroupTheory
end McKayConjecture
