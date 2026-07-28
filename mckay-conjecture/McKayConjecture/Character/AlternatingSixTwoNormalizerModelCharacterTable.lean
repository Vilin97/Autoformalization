/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CyclicThreeCharacterTable
import McKayConjecture.Character.DirectProductCorrespondence
import McKayConjecture.Character.QuaternionGroupFourCharacterTable

/-!
# Character table of the `C₃ × Q₁₆` two-normalizer model

The complete ordinary table has 21 rows: three cyclic twists of each of the
seven quaternion rows.  Its `2'`-part has 12 rows: three cyclic twists of
each of the four linear quaternion rows.

Both enumerations are obtained from the direct-product classification
theorem, and their values are exposed in factorized form on both dicyclic
normal forms.
-/

noncomputable section

namespace McKayConjecture
namespace AlternatingSixTwoNormalizerModelCharacterTable

/-- The concrete order-forty-eight normalizer model. -/
abbrev Group :=
  CyclicThree.Group × QuaternionGroup 4

/-- The 21 ordinary row indices. -/
abbrev OrdinaryCharacterRow :=
  Fin 3 × QuaternionGroupFour.CharacterRow

/-- Complete ordinary character enumeration. -/
def irreducibleCharacterEquiv :
    OrdinaryCharacterRow ≃ IrreducibleCharacter Group :=
  (Equiv.prodCongr
      CyclicThree.irreducibleCharacterEquiv
      QuaternionGroupFour.irreducibleCharacterEquiv).trans
    IrreducibleCharacter.directProductEquiv

@[simp]
theorem irreducibleCharacterEquiv_apply
    (r : OrdinaryCharacterRow) :
    irreducibleCharacterEquiv r =
      IrreducibleCharacter.externalTensor
        (CyclicThree.irreducibleCharacterEquiv r.1)
        (QuaternionGroupFour.irreducibleCharacterEquiv r.2) :=
  rfl

@[simp]
theorem irreducibleCharacterEquiv_degree_linear
    (j : Fin 3) (r : QuaternionGroupFour.LinearIndex) :
    (irreducibleCharacterEquiv (j, .inl r)).degree = 1 := by
  rw [irreducibleCharacterEquiv_apply,
    IrreducibleCharacter.externalTensor_degree,
    CyclicThree.irreducibleCharacterEquiv_apply,
    QuaternionGroupFour.irreducibleCharacterEquiv_apply,
    CyclicThree.linearCharacter_degree,
    QuaternionGroupFour.character_degree_linear]

@[simp]
theorem irreducibleCharacterEquiv_degree_twoDimensional
    (j : Fin 3) (k : Fin 3) :
    (irreducibleCharacterEquiv (j, .inr k)).degree = 2 := by
  rw [irreducibleCharacterEquiv_apply,
    IrreducibleCharacter.externalTensor_degree,
    CyclicThree.irreducibleCharacterEquiv_apply,
    QuaternionGroupFour.irreducibleCharacterEquiv_apply,
    CyclicThree.linearCharacter_degree,
    QuaternionGroupFour.character_degree_twoDimensional]

@[simp]
theorem irreducibleCharacterEquiv_values_linear_a
    (j : Fin 3)
    (r : QuaternionGroupFour.LinearIndex)
    (z : CyclicThree.Group) (m : ℕ) :
    (irreducibleCharacterEquiv (j, .inl r)).values
        (z, QuaternionGroup.a (m : ZMod 8)) =
      (CyclicThree.linearHom j z : ℂ) *
        (QuaternionGroupFour.signParameter r.1 ^ m : ℂˣ) := by
  rw [irreducibleCharacterEquiv_apply,
    IrreducibleCharacter.externalTensor_values,
    CyclicThree.irreducibleCharacterEquiv_apply,
    QuaternionGroupFour.irreducibleCharacterEquiv_apply,
    CyclicThree.linearCharacter,
    IrreducibleCharacter.linear_values,
    QuaternionGroupFour.character_values_linear_a]

@[simp]
theorem irreducibleCharacterEquiv_values_linear_xa
    (j : Fin 3)
    (r : QuaternionGroupFour.LinearIndex)
    (z : CyclicThree.Group) (m : ℕ) :
    (irreducibleCharacterEquiv (j, .inl r)).values
        (z, QuaternionGroup.xa (m : ZMod 8)) =
      (CyclicThree.linearHom j z : ℂ) *
        (QuaternionGroupFour.signParameter r.2 *
          QuaternionGroupFour.signParameter r.1 ^ m : ℂˣ) := by
  rw [irreducibleCharacterEquiv_apply,
    IrreducibleCharacter.externalTensor_values,
    CyclicThree.irreducibleCharacterEquiv_apply,
    QuaternionGroupFour.irreducibleCharacterEquiv_apply,
    CyclicThree.linearCharacter,
    IrreducibleCharacter.linear_values,
    QuaternionGroupFour.character_values_linear_xa]

@[simp]
theorem irreducibleCharacterEquiv_values_twoDimensional_a
    (j k : Fin 3)
    (z : CyclicThree.Group) (m : ℕ) :
    (irreducibleCharacterEquiv (j, .inr k)).values
        (z, QuaternionGroup.a (m : ZMod 8)) =
      (CyclicThree.linearHom j z : ℂ) *
        (QuaternionGroupFour.twoDimensionalParameter k ^ m +
          (QuaternionGroupFour.twoDimensionalParameter k)⁻¹ ^ m) := by
  rw [irreducibleCharacterEquiv_apply,
    IrreducibleCharacter.externalTensor_values,
    CyclicThree.irreducibleCharacterEquiv_apply,
    QuaternionGroupFour.irreducibleCharacterEquiv_apply,
    CyclicThree.linearCharacter,
    IrreducibleCharacter.linear_values,
    QuaternionGroupFour.character_values_twoDimensional_a]

@[simp]
theorem irreducibleCharacterEquiv_values_twoDimensional_xa
    (j k : Fin 3)
    (z : CyclicThree.Group) (i : ZMod 8) :
    (irreducibleCharacterEquiv (j, .inr k)).values
        (z, QuaternionGroup.xa i) = 0 := by
  rw [irreducibleCharacterEquiv_apply,
    IrreducibleCharacter.externalTensor_values,
    QuaternionGroupFour.irreducibleCharacterEquiv_apply,
    QuaternionGroupFour.character_values_twoDimensional_xa,
    mul_zero]

/-- There are exactly 21 ordinary irreducible characters. -/
@[simp]
theorem natCard_irreducibleCharacter :
    Nat.card (IrreducibleCharacter Group) = 21 := by
  calc
    Nat.card (IrreducibleCharacter Group) =
        Nat.card OrdinaryCharacterRow :=
      Nat.card_congr irreducibleCharacterEquiv.symm
    _ = 21 := by
      simp [OrdinaryCharacterRow,
        QuaternionGroupFour.CharacterRow]

local instance alternatingSixTwoNormalizerModelCharacterTableFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- A cyclic row packaged with its odd-degree proof. -/
def cyclicThreePPrimeCharacter (j : Fin 3) :
    PPrimeIrreducibleCharacter CyclicThree.Group 2 :=
  ⟨CyclicThree.linearCharacter j,
    IrreducibleCharacter.linear_isPPrimeDegree
      (CyclicThree.linearHom j) 2⟩

/-- Complete odd-degree enumeration of the cyclic factor. -/
def cyclicThreePPrimeCharacterEquiv :
    Fin 3 ≃ PPrimeIrreducibleCharacter CyclicThree.Group 2 :=
  CyclicThree.linearHomEquiv.trans
    (IrreducibleCharacter.commutativePPrimeLinearEquiv 2).symm

@[simp]
theorem cyclicThreePPrimeCharacterEquiv_apply (j : Fin 3) :
    cyclicThreePPrimeCharacterEquiv j =
      cyclicThreePPrimeCharacter j := by
  apply Subtype.ext
  change
    IrreducibleCharacter.linear
        (CyclicThree.linearHomEquiv j) =
      IrreducibleCharacter.linear (CyclicThree.linearHom j)
  rw [CyclicThree.linearHomEquiv_apply]

@[simp]
theorem cyclicThreePPrimeCharacter_degree (j : Fin 3) :
    (cyclicThreePPrimeCharacter j).1.degree = 1 :=
  CyclicThree.linearCharacter_degree j

/-- The 12 odd-degree row indices. -/
abbrev CharacterRow :=
  Fin 3 × QuaternionGroupFour.LinearIndex

/-- Complete `2'`-degree enumeration of the model normalizer. -/
def pPrimeCharacterEquiv :
    CharacterRow ≃ PPrimeIrreducibleCharacter Group 2 :=
  (Equiv.prodCongr
      cyclicThreePPrimeCharacterEquiv
      QuaternionGroupFour.pPrimeCharacterEquiv).trans
    (IrreducibleCharacter.directProductPPrimeEquiv 2)

@[simp]
theorem pPrimeCharacterEquiv_apply
    (r : CharacterRow) :
    pPrimeCharacterEquiv r =
      IrreducibleCharacter.externalTensorPPrime 2
        (cyclicThreePPrimeCharacterEquiv r.1)
        (QuaternionGroupFour.pPrimeCharacterEquiv r.2) :=
  rfl

@[simp]
theorem pPrimeCharacterEquiv_degree
    (r : CharacterRow) :
    (pPrimeCharacterEquiv r).1.degree = 1 := by
  rw [pPrimeCharacterEquiv_apply,
    IrreducibleCharacter.externalTensorPPrime_coe,
    IrreducibleCharacter.externalTensor_degree,
    cyclicThreePPrimeCharacterEquiv_apply,
    QuaternionGroupFour.pPrimeCharacterEquiv_apply]
  change
    (CyclicThree.linearCharacter r.1).degree *
        (QuaternionGroupFour.linearPPrimeCharacter r.2).1.degree =
      1
  rw [CyclicThree.linearCharacter_degree,
    QuaternionGroupFour.linearPPrimeCharacter_degree]

@[simp]
theorem pPrimeCharacterEquiv_values
    (r : CharacterRow)
    (z : CyclicThree.Group) (g : QuaternionGroup 4) :
    (pPrimeCharacterEquiv r).1.values (z, g) =
      (cyclicThreePPrimeCharacterEquiv r.1).1.values z *
        (QuaternionGroupFour.pPrimeCharacterEquiv r.2).1.values g := by
  rw [pPrimeCharacterEquiv_apply,
    IrreducibleCharacter.externalTensorPPrime_coe,
    IrreducibleCharacter.externalTensor_values]

@[simp]
theorem pPrimeCharacterEquiv_values_a
    (r : CharacterRow)
    (z : CyclicThree.Group) (m : ℕ) :
    (pPrimeCharacterEquiv r).1.values
        (z, QuaternionGroup.a (m : ZMod 8)) =
      (CyclicThree.linearHom r.1 z : ℂ) *
        (QuaternionGroupFour.signParameter r.2.1 ^ m : ℂˣ) := by
  rw [pPrimeCharacterEquiv_values,
    cyclicThreePPrimeCharacterEquiv_apply,
    QuaternionGroupFour.pPrimeCharacterEquiv_apply,
    QuaternionGroupFour.linearPPrimeCharacter_values_a]
  change
    (CyclicThree.linearCharacter r.1).values z * _ = _
  rw [CyclicThree.linearCharacter,
    IrreducibleCharacter.linear_values]

@[simp]
theorem pPrimeCharacterEquiv_values_xa
    (r : CharacterRow)
    (z : CyclicThree.Group) (m : ℕ) :
    (pPrimeCharacterEquiv r).1.values
        (z, QuaternionGroup.xa (m : ZMod 8)) =
      (CyclicThree.linearHom r.1 z : ℂ) *
        (QuaternionGroupFour.signParameter r.2.2 *
          QuaternionGroupFour.signParameter r.2.1 ^ m : ℂˣ) := by
  rw [pPrimeCharacterEquiv_values,
    cyclicThreePPrimeCharacterEquiv_apply,
    QuaternionGroupFour.pPrimeCharacterEquiv_apply,
    QuaternionGroupFour.linearPPrimeCharacter_values_xa]
  change
    (CyclicThree.linearCharacter r.1).values z * _ = _
  rw [CyclicThree.linearCharacter,
    IrreducibleCharacter.linear_values]

/-- There are exactly 12 odd-degree irreducible characters. -/
@[simp]
theorem natCard_pPrimeIrreducibleCharacter :
    Nat.card
        (PPrimeIrreducibleCharacter Group 2) =
      12 := by
  calc
    Nat.card
        (PPrimeIrreducibleCharacter Group 2) =
        Nat.card CharacterRow :=
      Nat.card_congr pPrimeCharacterEquiv.symm
    _ = 12 := by
      simp [CharacterRow, QuaternionGroupFour.LinearIndex]

end AlternatingSixTwoNormalizerModelCharacterTable
end McKayConjecture
