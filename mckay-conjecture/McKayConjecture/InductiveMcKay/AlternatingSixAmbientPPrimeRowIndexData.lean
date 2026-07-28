/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientPPrimeRows

/-!
# Combinatorial prime-to-`p` row indices for the sixfold cover of `A₆`

This file gives ordered finite enumerations of the arithmetic row
subtypes in the existing thirty-one-row ambient matrix corpus.  It records
only names, dimensions, divisibility tests, and finite bijections.

In particular, none of the equivalences below enumerates irreducible
characters or asserts character completeness, stabilizer equivariance, or
projective compatibility.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- A name emphasizing the purely combinatorial role of the existing
thirty-one-row matrix-corpus index. -/
abbrev AlternatingSixAmbientRowIndex :=
  AlternatingSixAmbientOrdinaryRow

/-- The existing canonical ordering of the thirty-one ambient row
indices. -/
def alternatingSixAmbientRowIndexEquivFin :
    AlternatingSixAmbientRowIndex ≃ Fin 31 :=
  AlternatingSixAmbientOrdinaryRow.equivFin

/-- A row-index name for the existing arithmetic prime-to-`p` subtype. -/
abbrev AlternatingSixAmbientPPrimeRowIndex (p : ℕ) :=
  AlternatingSixAmbientPPrimeRow p

/-- Ordered enumeration of the twelve odd-dimensional ambient row
indices. -/
def alternatingSixAmbientTwoPPrimeRowIndexEquiv :
    Fin 12 ≃ AlternatingSixAmbientPPrimeRowIndex 2 :=
  Equiv.ofBijective
    ![⟨.row01, by decide⟩,
      ⟨.row02, by decide⟩,
      ⟨.row03, by decide⟩,
      ⟨.row04, by decide⟩,
      ⟨.row05, by decide⟩,
      ⟨.row08, by decide⟩,
      ⟨.row09, by decide⟩,
      ⟨.row20, by decide⟩,
      ⟨.row21, by decide⟩,
      ⟨.row22, by decide⟩,
      ⟨.row30, by decide⟩,
      ⟨.row31, by decide⟩]
    (by decide)

/-- Ordered enumeration of the twelve ambient row indices whose
dimensions are prime to three. -/
def alternatingSixAmbientThreePPrimeRowIndexEquiv :
    Fin 12 ≃ AlternatingSixAmbientPPrimeRowIndex 3 :=
  Equiv.ofBijective
    ![⟨.row01, by decide⟩,
      ⟨.row06, by decide⟩,
      ⟨.row07, by decide⟩,
      ⟨.row08, by decide⟩,
      ⟨.row09, by decide⟩,
      ⟨.row16, by decide⟩,
      ⟨.row17, by decide⟩,
      ⟨.row18, by decide⟩,
      ⟨.row19, by decide⟩,
      ⟨.row23, by decide⟩,
      ⟨.row24, by decide⟩,
      ⟨.row25, by decide⟩]
    (by decide)

/-- Ordered enumeration of the twenty-four ambient row indices whose
dimensions are prime to five. -/
def alternatingSixAmbientFivePPrimeRowIndexEquiv :
    Fin 24 ≃ AlternatingSixAmbientPPrimeRowIndex 5 :=
  Equiv.ofBijective
    ![⟨.row01, by decide⟩,
      ⟨.row02, by decide⟩,
      ⟨.row03, by decide⟩,
      ⟨.row04, by decide⟩,
      ⟨.row05, by decide⟩,
      ⟨.row06, by decide⟩,
      ⟨.row07, by decide⟩,
      ⟨.row10, by decide⟩,
      ⟨.row11, by decide⟩,
      ⟨.row12, by decide⟩,
      ⟨.row13, by decide⟩,
      ⟨.row14, by decide⟩,
      ⟨.row15, by decide⟩,
      ⟨.row16, by decide⟩,
      ⟨.row17, by decide⟩,
      ⟨.row18, by decide⟩,
      ⟨.row19, by decide⟩,
      ⟨.row20, by decide⟩,
      ⟨.row21, by decide⟩,
      ⟨.row22, by decide⟩,
      ⟨.atlasTwelvePowerOne, by decide⟩,
      ⟨.atlasTwelvePowerTwo, by decide⟩,
      ⟨.atlasTwelvePowerSeven, by decide⟩,
      ⟨.atlasTwelvePowerEleven, by decide⟩]
    (by decide)

/-- The ordered enumeration recovers the existing odd-row count. -/
theorem natCard_alternatingSixAmbientPPrimeRowIndex_two :
    Nat.card (AlternatingSixAmbientPPrimeRowIndex 2) = 12 :=
  natCard_alternatingSixAmbientPPrimeRow_two

/-- The ordered enumeration recovers the existing prime-to-three row
count. -/
theorem natCard_alternatingSixAmbientPPrimeRowIndex_three :
    Nat.card (AlternatingSixAmbientPPrimeRowIndex 3) = 12 :=
  natCard_alternatingSixAmbientPPrimeRow_three

/-- The ordered enumeration recovers the existing prime-to-five row
count. -/
theorem natCard_alternatingSixAmbientPPrimeRowIndex_five :
    Nat.card (AlternatingSixAmbientPPrimeRowIndex 5) = 24 :=
  natCard_alternatingSixAmbientPPrimeRow_five

end InductiveMcKay
end McKayConjecture
