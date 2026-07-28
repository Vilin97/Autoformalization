/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixThreeNormalizerCommutingPairs
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverThreeNormalizerSemidirect

/-!
# Conjugacy classes of the three-normalizer in `6.A₆`

The exact normalizer has a computable coordinate model of order `216`.
Its `6048` commuting ordered pairs give exactly `28` conjugacy classes.
The result is then transported to the fixed Sylow normalizer in the
canonical universal cover.
-/

namespace McKayConjecture
namespace GroupTheory

/-- A group equivalence induces an equivalence of conjugacy-class
types. -/
noncomputable def conjClassesEquivOfMulEquiv
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    ConjClasses G ≃ ConjClasses H where
  toFun := ConjClasses.map e.toMonoidHom
  invFun := ConjClasses.map e.symm.toMonoidHom
  left_inv x := by
    refine Quotient.inductionOn x ?_
    intro g
    change ConjClasses.mk (e.symm (e g)) = ConjClasses.mk g
    exact congrArg ConjClasses.mk (e.left_inv g)
  right_inv x := by
    refine Quotient.inductionOn x ?_
    intro h
    change ConjClasses.mk (e (e.symm h)) = ConjClasses.mk h
    exact congrArg ConjClasses.mk (e.right_inv h)

/-- The coordinate model of the exact three-normalizer has twenty-eight
conjugacy classes. -/
theorem natCard_conjClasses_alternatingSixThreeNormalizerCoordinates :
    Nat.card (ConjClasses AlternatingSixThreeNormalizerCoordinates) = 28 := by
  have h :=
    card_comm_eq_card_conjClasses_mul_card
      AlternatingSixThreeNormalizerCoordinates
  rw [show
      Nat.card
          {p : AlternatingSixThreeNormalizerCoordinates ×
              AlternatingSixThreeNormalizerCoordinates //
            Commute p.1 p.2} =
        6048 by
      exact natCard_alternatingSixThreeNormalizerCommutingPairs,
    natCard_alternatingSixThreeNormalizerCoordinates] at h
  omega

/-- The coordinate normalizer is the fixed Sylow-three normalizer in
the canonical universal cover. -/
noncomputable def
    alternatingSixThreeNormalizerCoordinatesEquivUniversalCoverNormalizer :
    AlternatingSixThreeNormalizerCoordinates ≃*
      AlternatingSixUniversalCoverThreeNormalizer :=
  alternatingSixThreeNormalizerCoordinatesEquivHeisenbergSemidirect.trans
    alternatingSixThreeHeisenbergCyclicEightEquivUniversalCoverNormalizer

/-- Conjugacy classes transported from the computable coordinate model
to the actual fixed normalizer. -/
noncomputable def
    alternatingSixThreeNormalizerConjClassesEquivUniversalCoverNormalizer :
    ConjClasses AlternatingSixThreeNormalizerCoordinates ≃
      ConjClasses AlternatingSixUniversalCoverThreeNormalizer :=
  conjClassesEquivOfMulEquiv
    alternatingSixThreeNormalizerCoordinatesEquivUniversalCoverNormalizer

/-- The actual fixed Sylow-three normalizer in the canonical universal
cover has twenty-eight conjugacy classes. -/
theorem
    natCard_conjClasses_alternatingSixUniversalCoverThreeNormalizer :
    Nat.card
        (ConjClasses AlternatingSixUniversalCoverThreeNormalizer) =
      28 := by
  calc
    Nat.card
        (ConjClasses AlternatingSixUniversalCoverThreeNormalizer) =
        Nat.card
          (ConjClasses AlternatingSixThreeNormalizerCoordinates) :=
      Nat.card_congr
        alternatingSixThreeNormalizerConjClassesEquivUniversalCoverNormalizer.symm
    _ = 28 :=
      natCard_conjClasses_alternatingSixThreeNormalizerCoordinates

end GroupTheory
end McKayConjecture
