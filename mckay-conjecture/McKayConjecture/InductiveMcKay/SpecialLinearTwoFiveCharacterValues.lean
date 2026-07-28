/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveConjugacyClasses

/-!
# The symbolic ordinary character table of `SL(2, 𝔽₅)`

The two faithful degree-two characters of the binary icosahedral group are
Galois conjugate.  If `t² = t + 1`, their values are obtained by using the
two roots `t` and `1 - t`.  Every other row needed for the ordinary table
is obtained from the low symmetric-power character polynomials or from the
product of the two faithful rows.

This file contains only the symbolic table.  The representation-theoretic
realization and the orthogonality calculation are kept in separate files.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- Nine rows of the ordinary binary-icosahedral character table. -/
inductive SpecialLinearTwoFiveCharacterRow
  | trivial
  | faithful (k : Fin 2)
  | symmetricSquare (k : Fin 2)
  | symmetricCube
  | tensor
  | symmetricFourthPower
  | symmetricFifthPower
  deriving DecidableEq, Fintype

/-- The two Galois-conjugate golden roots, starting from one root `t`. -/
def binaryIcosahedralGoldenRootChoice
    (t : ℂ) : Fin 2 → ℂ
  | 0 => t
  | 1 => 1 - t

@[simp]
theorem binaryIcosahedralGoldenRootChoice_zero
    (t : ℂ) :
    binaryIcosahedralGoldenRootChoice t 0 = t :=
  rfl

@[simp]
theorem binaryIcosahedralGoldenRootChoice_one
    (t : ℂ) :
    binaryIcosahedralGoldenRootChoice t 1 = 1 - t :=
  rfl

theorem binaryIcosahedralGoldenRootChoice_sq
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (k : Fin 2) :
    binaryIcosahedralGoldenRootChoice t k ^ 2 =
      binaryIcosahedralGoldenRootChoice t k + 1 := by
  fin_cases k
  · exact ht
  · change (1 - t) ^ 2 = (1 - t) + 1
    linear_combination ht

/-- Trace of the defining two-dimensional representation with golden
parameter `t` on the nine fixed conjugacy-class representatives. -/
def binaryIcosahedralDefiningTrace
    (t : ℂ) :
    SpecialLinearTwoFiveConjugacyClass → ℂ
  | 0 => 2
  | 1 => -2
  | 2 => 0
  | 3 => 1
  | 4 => -1
  | 5 => t
  | 6 => 1 - t
  | 7 => t - 1
  | 8 => -t

/-- Character polynomial for a symmetric square of an `SL₂`
representation. -/
def binaryIcosahedralSymmetricSquareValue
    (t : ℂ)
    (c : SpecialLinearTwoFiveConjugacyClass) : ℂ :=
  binaryIcosahedralDefiningTrace t c ^ 2 - 1

/-- Character polynomial for a symmetric cube of an `SL₂`
representation. -/
def binaryIcosahedralSymmetricCubeValue
    (t : ℂ)
    (c : SpecialLinearTwoFiveConjugacyClass) : ℂ :=
  binaryIcosahedralDefiningTrace t c ^ 3 -
    2 * binaryIcosahedralDefiningTrace t c

/-- Character polynomial for a fourth symmetric power of an `SL₂`
representation. -/
def binaryIcosahedralSymmetricFourthPowerValue
    (t : ℂ)
    (c : SpecialLinearTwoFiveConjugacyClass) : ℂ :=
  binaryIcosahedralDefiningTrace t c ^ 4 -
    3 * binaryIcosahedralDefiningTrace t c ^ 2 + 1

/-- Character polynomial for a fifth symmetric power of an `SL₂`
representation. -/
def binaryIcosahedralSymmetricFifthPowerValue
    (t : ℂ)
    (c : SpecialLinearTwoFiveConjugacyClass) : ℂ :=
  binaryIcosahedralDefiningTrace t c ^ 5 -
    4 * binaryIcosahedralDefiningTrace t c ^ 3 +
      3 * binaryIcosahedralDefiningTrace t c

/-- Symbolic value of any of the nine ordinary character rows. -/
def specialLinearTwoFiveCharacterTableValue
    (t : ℂ) :
    SpecialLinearTwoFiveCharacterRow →
      SpecialLinearTwoFiveConjugacyClass → ℂ
  | .trivial, _ => 1
  | .faithful k, c =>
      binaryIcosahedralDefiningTrace
        (binaryIcosahedralGoldenRootChoice t k) c
  | .symmetricSquare k, c =>
      binaryIcosahedralSymmetricSquareValue
        (binaryIcosahedralGoldenRootChoice t k) c
  | .symmetricCube, c =>
      binaryIcosahedralSymmetricCubeValue t c
  | .tensor, c =>
      binaryIcosahedralDefiningTrace t c *
        binaryIcosahedralDefiningTrace (1 - t) c
  | .symmetricFourthPower, c =>
      binaryIcosahedralSymmetricFourthPowerValue t c
  | .symmetricFifthPower, c =>
      binaryIcosahedralSymmetricFifthPowerValue t c

/-- Degree of each symbolic row. -/
def specialLinearTwoFiveCharacterRowDegree :
    SpecialLinearTwoFiveCharacterRow → ℕ
  | .trivial => 1
  | .faithful _ => 2
  | .symmetricSquare _ => 3
  | .symmetricCube => 4
  | .tensor => 4
  | .symmetricFourthPower => 5
  | .symmetricFifthPower => 6

/-- Rows whose displayed degree is prime to `p`. -/
abbrev SpecialLinearTwoFivePPrimeCharacterRow (p : ℕ) :=
  {r : SpecialLinearTwoFiveCharacterRow //
    ¬p ∣ specialLinearTwoFiveCharacterRowDegree r}

/-- There are nine rows in the full symbolic table. -/
theorem natCard_specialLinearTwoFiveCharacterRow :
    Nat.card SpecialLinearTwoFiveCharacterRow = 9 := by
  rw [Nat.card_eq_fintype_card]
  native_decide

/-- The four odd-degree rows. -/
theorem natCard_specialLinearTwoFiveTwoPPrimeCharacterRow :
    Nat.card (SpecialLinearTwoFivePPrimeCharacterRow 2) = 4 := by
  rw [Nat.card_eq_fintype_card]
  native_decide

/-- The six rows of degree prime to three. -/
theorem natCard_specialLinearTwoFiveThreePPrimeCharacterRow :
    Nat.card (SpecialLinearTwoFivePPrimeCharacterRow 3) = 6 := by
  rw [Nat.card_eq_fintype_card]
  native_decide

/-- The eight rows of degree prime to five. -/
theorem natCard_specialLinearTwoFiveFivePPrimeCharacterRow :
    Nat.card (SpecialLinearTwoFivePPrimeCharacterRow 5) = 8 := by
  rw [Nat.card_eq_fintype_card]
  native_decide

@[simp]
theorem specialLinearTwoFiveCharacterTableValue_identity
    (t : ℂ) (r : SpecialLinearTwoFiveCharacterRow) :
    specialLinearTwoFiveCharacterTableValue t r 0 =
      specialLinearTwoFiveCharacterRowDegree r := by
  rcases r with _ | k | k | _ | _ | _ | _
  · norm_num [specialLinearTwoFiveCharacterTableValue,
      specialLinearTwoFiveCharacterRowDegree]
  · fin_cases k <;>
      norm_num [specialLinearTwoFiveCharacterTableValue,
        specialLinearTwoFiveCharacterRowDegree,
        binaryIcosahedralDefiningTrace]
  · fin_cases k <;>
      norm_num [specialLinearTwoFiveCharacterTableValue,
        specialLinearTwoFiveCharacterRowDegree,
        binaryIcosahedralSymmetricSquareValue,
        binaryIcosahedralDefiningTrace]
  · norm_num [specialLinearTwoFiveCharacterTableValue,
      specialLinearTwoFiveCharacterRowDegree,
      binaryIcosahedralSymmetricCubeValue,
      binaryIcosahedralDefiningTrace]
  · norm_num [specialLinearTwoFiveCharacterTableValue,
      specialLinearTwoFiveCharacterRowDegree,
      binaryIcosahedralDefiningTrace]
  · norm_num [specialLinearTwoFiveCharacterTableValue,
      specialLinearTwoFiveCharacterRowDegree,
      binaryIcosahedralSymmetricFourthPowerValue,
      binaryIcosahedralDefiningTrace]
  · norm_num [specialLinearTwoFiveCharacterTableValue,
      specialLinearTwoFiveCharacterRowDegree,
      binaryIcosahedralSymmetricFifthPowerValue,
      binaryIcosahedralDefiningTrace]

/-- Weighted bilinear pairing of two symbolic rows.  All table values are
real for the two actual golden roots, so this is the ordinary character
inner product before division by the group order. -/
def specialLinearTwoFiveCharacterTableWeightedPairing
    (t : ℂ)
    (r s : SpecialLinearTwoFiveCharacterRow) : ℂ :=
  ∑ c : SpecialLinearTwoFiveConjugacyClass,
    (specialLinearTwoFiveConjugacyClassSize c : ℂ) *
      specialLinearTwoFiveCharacterTableValue t r c *
        specialLinearTwoFiveCharacterTableValue t s c

end InductiveMcKay
end McKayConjecture
