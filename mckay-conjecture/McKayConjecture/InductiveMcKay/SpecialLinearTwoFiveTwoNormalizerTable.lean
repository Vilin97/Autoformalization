/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.FiniteIndexProjectiveTable
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveTwoNormalizerRepresentations

/-!
# The `2'`-character table of the Sylow-two normalizer in `SL(2, 𝔽₅)`

This file exposes the four odd-degree rows of the exact binary-tetrahedral
normalizer and fixes the standard four-row McKay matching:

* the ambient trivial row matches the trivial normalizer row;
* the two ambient degree-three rows match the two nontrivial linear rows;
* the ambient degree-five row matches the normalizer degree-three row.

As in the corresponding `p = 3` and `p = 5` files, the final structures
separate the ordinary row-equivariance check from the projective comparison
rows.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeTwoForNormalizerTable :
    Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- There are exactly four odd-degree irreducible characters of the exact
Sylow-two normalizer. -/
theorem natCard_specialLinearTwoFiveTwoNormalizerPPrimeCharacter :
    Nat.card
        (PPrimeIrreducibleCharacter
          (SylowNormalizer specialLinearTwoFiveSylowTwo) 2) =
      4 := by
  calc
    Nat.card
          (PPrimeIrreducibleCharacter
            (SylowNormalizer specialLinearTwoFiveSylowTwo) 2) =
        Nat.card
          SpecialLinearTwoFiveTwoNormalizerPPrimeCharacterRow :=
      Nat.card_congr
        specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv.symm
    _ = 4 :=
      natCard_specialLinearTwoFiveTwoNormalizerPPrimeCharacterRow

@[simp]
theorem specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv_degree
    (r : SpecialLinearTwoFiveTwoNormalizerPPrimeCharacterRow) :
    (specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv r).1.degree =
      specialLinearTwoFiveTwoNormalizerCharacterRowDegree r.1 :=
  specialLinearTwoFiveTwoNormalizerIrreducibleCharacter_degree r.1

/-- The concrete four-row matching before it is bundled as an equivalence. -/
def specialLinearTwoFiveTwoMcKayRowMatch
    (r : SpecialLinearTwoFivePPrimeCharacterRow 2) :
    SpecialLinearTwoFiveTwoNormalizerPPrimeCharacterRow :=
  match r with
  | ⟨.trivial, _⟩ =>
      ⟨.linear 0, by
        norm_num [
          specialLinearTwoFiveTwoNormalizerCharacterRowDegree]⟩
  | ⟨.faithful k, h⟩ =>
      False.elim <| h <| by
        simp [specialLinearTwoFiveCharacterRowDegree]
  | ⟨.symmetricSquare k, _⟩ =>
      ⟨.linear ((k.val + 1 : ℕ) : ZMod 3), by
        norm_num [
          specialLinearTwoFiveTwoNormalizerCharacterRowDegree]⟩
  | ⟨.symmetricCube, h⟩ =>
      False.elim <| h <| by
        simp [specialLinearTwoFiveCharacterRowDegree]
  | ⟨.tensor, h⟩ =>
      False.elim <| h <| by
        simp [specialLinearTwoFiveCharacterRowDegree]
  | ⟨.symmetricFourthPower, _⟩ =>
      ⟨.threeDimensional, by
        norm_num [
          specialLinearTwoFiveTwoNormalizerCharacterRowDegree]⟩
  | ⟨.symmetricFifthPower, h⟩ =>
      False.elim <| h <| by
        simp [specialLinearTwoFiveCharacterRowDegree]

theorem specialLinearTwoFiveTwoMcKayRowMatch_bijective :
    Function.Bijective specialLinearTwoFiveTwoMcKayRowMatch := by
  decide

/-- The standard four-row McKay matching at `p = 2`. -/
def specialLinearTwoFiveTwoMcKayRowEquiv :
    SpecialLinearTwoFivePPrimeCharacterRow 2 ≃
      SpecialLinearTwoFiveTwoNormalizerPPrimeCharacterRow :=
  Equiv.ofBijective
    specialLinearTwoFiveTwoMcKayRowMatch
    specialLinearTwoFiveTwoMcKayRowMatch_bijective

@[simp]
theorem specialLinearTwoFiveTwoMcKayRowEquiv_apply
    (r : SpecialLinearTwoFivePPrimeCharacterRow 2) :
    specialLinearTwoFiveTwoMcKayRowEquiv r =
      specialLinearTwoFiveTwoMcKayRowMatch r :=
  rfl

/-- The ambient enumeration of the four odd-degree rows. -/
abbrev specialLinearTwoFiveTwoPPrimeCharacterEquiv :
    SpecialLinearTwoFivePPrimeCharacterRow 2 ≃
      PPrimeIrreducibleCharacter SpecialLinearTwoFive 2 :=
  specialLinearTwoFivePPrimeCharacterEquiv 2

/-- The concrete group has exactly four irreducible characters of odd
degree. -/
theorem natCard_specialLinearTwoFiveTwoPPrimeIrreducibleCharacter :
    Nat.card
        (PPrimeIrreducibleCharacter
          SpecialLinearTwoFive 2) =
      4 := by
  rw [← Nat.card_congr
    specialLinearTwoFiveTwoPPrimeCharacterEquiv]
  exact
    natCard_specialLinearTwoFiveTwoPPrimeCharacterRow

/-- Remaining ordinary-table data after both complete four-row
enumerations and their standard matching have been fixed. -/
structure SpecialLinearTwoFiveTwoCharacterTableCompletion where
  /-- Equivariance of the standard four-row matching under automorphisms
  stabilizing the chosen Sylow-two subgroup. -/
  indexEquivariance :
    ∀ (a :
        SylowAutStabilizer specialLinearTwoFiveSylowTwo)
      (i : SpecialLinearTwoFivePPrimeCharacterRow 2),
      specialLinearTwoFiveTwoMcKayRowEquiv
          (specialLinearTwoFiveTwoPPrimeCharacterEquiv.symm
            (a • specialLinearTwoFiveTwoPPrimeCharacterEquiv i)) =
        specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv.symm
          (a •
            specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv
              (specialLinearTwoFiveTwoMcKayRowEquiv i))

namespace SpecialLinearTwoFiveTwoCharacterTableCompletion

/-- Insert the two exact tables and the standard row matching into the
generic finite-index certificate. -/
def toFiniteIndexMcKayEquivCertificate
    (d : SpecialLinearTwoFiveTwoCharacterTableCompletion) :
    FiniteIndexMcKayEquivCertificate
      specialLinearTwoFiveSylowTwo
      (SpecialLinearTwoFivePPrimeCharacterRow 2)
      SpecialLinearTwoFiveTwoNormalizerPPrimeCharacterRow where
  ambientEnumeration :=
    specialLinearTwoFiveTwoPPrimeCharacterEquiv
  normalizerEnumeration :=
    specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv
  indexEquiv :=
    specialLinearTwoFiveTwoMcKayRowEquiv
  indexEquivariance :=
    d.indexEquivariance

/-- The resulting character-level equivariant McKay equivalence. -/
def toEquivariantMcKayEquiv
    (d : SpecialLinearTwoFiveTwoCharacterTableCompletion) :
    EquivariantMcKayEquiv specialLinearTwoFiveSylowTwo :=
  d.toFiniteIndexMcKayEquivCertificate.toEquivariantMcKayEquiv

@[simp]
theorem toEquivariantMcKayEquiv_apply_enumerated
    (d : SpecialLinearTwoFiveTwoCharacterTableCompletion)
    (i : SpecialLinearTwoFivePPrimeCharacterRow 2) :
    d.toEquivariantMcKayEquiv
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv i) =
      specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv
        (specialLinearTwoFiveTwoMcKayRowEquiv i) :=
  d.toFiniteIndexMcKayEquivCertificate
    |>.toEquivariantMcKayEquiv_apply_enumerated i

end SpecialLinearTwoFiveTwoCharacterTableCompletion

/-- Remaining projective rows after the ordinary tables and standard
matching are fixed. -/
structure SpecialLinearTwoFiveTwoProjectiveTableCompletion where
  /-- The automorphism-equivariant ordinary table. -/
  characterTable :
    SpecialLinearTwoFiveTwoCharacterTableCompletion
  /-- The projective comparison calculation for every ambient odd-degree
  row. -/
  projectiveRow :
    ∀ i : SpecialLinearTwoFivePPrimeCharacterRow 2,
      ExactNormalizerProjectiveRowData
        characterTable.toEquivariantMcKayEquiv
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv i)

namespace SpecialLinearTwoFiveTwoProjectiveTableCompletion

def toFiniteIndexExactNormalizerProjectiveTableCertificate
    (d : SpecialLinearTwoFiveTwoProjectiveTableCompletion) :
    FiniteIndexExactNormalizerProjectiveTableCertificate
      specialLinearTwoFiveSylowTwo
      (SpecialLinearTwoFivePPrimeCharacterRow 2)
      SpecialLinearTwoFiveTwoNormalizerPPrimeCharacterRow where
  characterCertificate :=
    d.characterTable.toFiniteIndexMcKayEquivCertificate
  projectiveRow :=
    d.projectiveRow

/-- A completed four-row projective table gives the full local inductive
McKay datum for `SL(2, 𝔽₅)` at `p = 2`. -/
def toLocalInductiveMcKayData
    (d : SpecialLinearTwoFiveTwoProjectiveTableCompletion) :
    LocalInductiveMcKayData specialLinearTwoFiveSylowTwo :=
  d.toFiniteIndexExactNormalizerProjectiveTableCertificate
    |>.toLocalInductiveMcKayData

end SpecialLinearTwoFiveTwoProjectiveTableCompletion

end InductiveMcKay
end McKayConjecture
