/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientConcreteLocalRowIndexData
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientPPrimeRowIndexData

/-!
# Arbitrary ambient/local row-index alignments for the sixfold cover of `A₆`

The ambient and concrete local row-index types have matching cardinalities
at `p = 2`, `3`, and `5`.  This file composes their explicitly chosen
orders to record bare finite-set bijections.

These arbitrary alignments are not proposed McKay row matchings.  They do
not assert character correspondence, completeness, Sylow-stabilizer
equivariance, or projective compatibility.  In particular, they must not
be used as the `indexEquiv` field of a concrete character-table certificate
without an independent character comparison and equivariance proof.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Arbitrary order-based index alignment between the twelve
odd-dimensional ambient rows and the twelve concrete two-normalizer rows.

This is not a proposed McKay row matching. -/
def alternatingSixAmbientTwoPPrimeRowArbitraryIndexEquivConcreteNormalizerRow :
    AlternatingSixAmbientPPrimeRowIndex 2 ≃
      AlternatingSixTwoConcreteNormalizerRow :=
  alternatingSixAmbientTwoPPrimeRowIndexEquiv.symm.trans
    alternatingSixTwoConcreteNormalizerRowIndexEquiv

/-- Arbitrary order-based index alignment between the twelve
prime-to-three ambient rows and the twelve concrete three-normalizer rows.

This is not a proposed McKay row matching. -/
def alternatingSixAmbientThreePPrimeRowArbitraryIndexEquivConcreteNormalizerRow :
    AlternatingSixAmbientPPrimeRowIndex 3 ≃
      AlternatingSixThreeConcreteNormalizerRow :=
  alternatingSixAmbientThreePPrimeRowIndexEquiv.symm.trans
    alternatingSixThreeConcreteNormalizerRowIndexEquiv

/-- Arbitrary order-based index alignment between the twenty-four
prime-to-five ambient rows and the twenty-four concrete
five-normalizer rows.

This is not a proposed McKay row matching. -/
def alternatingSixAmbientFivePPrimeRowArbitraryIndexEquivConcreteNormalizerRow :
    AlternatingSixAmbientPPrimeRowIndex 5 ≃
      AlternatingSixFiveConcreteNormalizerRow :=
  alternatingSixAmbientFivePPrimeRowIndexEquiv.symm.trans
    alternatingSixFiveConcreteNormalizerRowIndexEquiv

end InductiveMcKay
end McKayConjecture
