/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixFiveConcreteFiniteTable
import McKayConjecture.InductiveMcKay.AlternatingSixThreeConcreteFiniteTable
import McKayConjecture.InductiveMcKay.AlternatingSixTwoConcreteFiniteTable

/-!
# Concrete local row-index data for the sixfold cover of `A₆`

This file chooses explicit orders for the concrete local row-index types at
`p = 2`, `3`, and `5`.  Together with the separate arithmetic ambient-row
enumerations, these are neutral finite combinatorial index data.

This file does not pair an ambient row with a local row.  It carries no
character completeness, Sylow-stabilizer equivariance, or projective
compatibility claim.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Lexicographic enumeration of the twelve concrete two-normalizer row
indices. -/
def alternatingSixTwoConcreteNormalizerRowIndexEquiv :
    Fin 12 ≃ AlternatingSixTwoConcreteNormalizerRow :=
  Equiv.ofBijective
    ![(0, (0, 0)),
      (0, (0, 1)),
      (0, (1, 0)),
      (0, (1, 1)),
      (1, (0, 0)),
      (1, (0, 1)),
      (1, (1, 0)),
      (1, (1, 1)),
      (2, (0, 0)),
      (2, (0, 1)),
      (2, (1, 0)),
      (2, (1, 1))]
    (by decide)

/-- Enumeration of the twelve concrete three-normalizer row indices:
the eight linear indices followed by the four degree-four coordinate
indices. -/
def alternatingSixThreeConcreteNormalizerRowIndexEquiv :
    Fin 12 ≃ AlternatingSixThreeConcreteNormalizerRow :=
  Equiv.ofBijective
    ![Sum.inl 0,
      Sum.inl 1,
      Sum.inl 2,
      Sum.inl 3,
      Sum.inl 4,
      Sum.inl 5,
      Sum.inl 6,
      Sum.inl 7,
      Sum.inr (0, 0),
      Sum.inr (0, 1),
      Sum.inr (1, 0),
      Sum.inr (1, 1)]
    (by decide)

/-- Lexicographic enumeration of the twenty-four concrete
five-normalizer row indices, with linear rows preceding two-dimensional
rows inside each cyclic-three coordinate. -/
def alternatingSixFiveConcreteNormalizerRowIndexEquiv :
    Fin 24 ≃ AlternatingSixFiveConcreteNormalizerRow :=
  Equiv.ofBijective
    ![(0, CyclicFiveInversionSemidirect.CharacterRow.linear 0),
      (0, CyclicFiveInversionSemidirect.CharacterRow.linear 1),
      (0, CyclicFiveInversionSemidirect.CharacterRow.linear 2),
      (0, CyclicFiveInversionSemidirect.CharacterRow.linear 3),
      (0, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 0),
      (0, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 1),
      (0, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 2),
      (0, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 3),
      (1, CyclicFiveInversionSemidirect.CharacterRow.linear 0),
      (1, CyclicFiveInversionSemidirect.CharacterRow.linear 1),
      (1, CyclicFiveInversionSemidirect.CharacterRow.linear 2),
      (1, CyclicFiveInversionSemidirect.CharacterRow.linear 3),
      (1, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 0),
      (1, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 1),
      (1, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 2),
      (1, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 3),
      (2, CyclicFiveInversionSemidirect.CharacterRow.linear 0),
      (2, CyclicFiveInversionSemidirect.CharacterRow.linear 1),
      (2, CyclicFiveInversionSemidirect.CharacterRow.linear 2),
      (2, CyclicFiveInversionSemidirect.CharacterRow.linear 3),
      (2, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 0),
      (2, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 1),
      (2, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 2),
      (2, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 3)]
    (by decide)

end InductiveMcKay
end McKayConjecture
