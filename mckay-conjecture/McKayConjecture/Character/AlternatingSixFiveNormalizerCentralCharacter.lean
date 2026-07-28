/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.AlternatingSixFiveNormalizerSemidirectCharacterTable
import McKayConjecture.GroupTheory.AlternatingSixSchurFiveNormalizerCentralGenerator

/-!
# Central characters in the concrete five-normalizer table

This file evaluates every explicit row of
`C₃ × (C₅ ⋊ C₄)` at the element representing the distinguished central
generator of `6.A₆`.

The cyclic-three contribution is the square of the selected third root.
For the dicyclic factor, a linear row contributes the square of its fourth
root, while a two-dimensional row contributes the fifth power of its
tenth-root parameter.  The resulting character value is the row degree
times this scalar.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture

open GroupTheory

namespace AlternatingSixFiveNormalizerSemidirectCharacterTable

/-- The scalar by which the dicyclic central involution acts on an
explicit row. -/
def dicyclicCentralScalar :
    CyclicFiveInversionSemidirect.CharacterRow → ℂ
  | .linear k =>
      (QuaternionGroupFive.fourthRootParameter k : ℂ) ^ 2
  | .twoDimensional k =>
      QuaternionGroupFive.twoDimensionalParameter k ^ 5

/-- The scalar by which the distinguished order-six central generator
acts on an explicit product row. -/
def centralScalar (r : CharacterRow) : ℂ :=
  (CyclicThree.thirdRootParameter r.1 : ℂ) ^ 2 *
    dicyclicCentralScalar r.2

/-- Degree of an explicit product row, expressed directly on its finite
index. -/
def rowDegree : CharacterRow → ℕ
  | (_, .linear _) => 1
  | (_, .twoDimensional _) => 2

/-- Evaluation of a cyclic-three row at the element `2`. -/
theorem cyclicThree_linearHom_ofAdd_two (j : Fin 3) :
    (CyclicThree.linearHom j (Multiplicative.ofAdd 2) : ℂ) =
      (CyclicThree.thirdRootParameter j : ℂ) ^ 2 := by
  have hinput :
      (Multiplicative.ofAdd 2 : Multiplicative (ZMod 3)) =
        (Multiplicative.ofAdd 1) ^ 2 := by
    decide
  rw [
    hinput,
    map_pow,
    CyclicThree.linearHom_generator
  ]
  rfl

/-- A linear dicyclic row evaluates at the central involution as the
square of its fourth-root parameter. -/
theorem dicyclic_rowFDRep_character_generator_sq_linear
    (k : Fin 4) :
    (CyclicFiveInversionSemidirect.rowFDRep
        (.linear k)).character
          (cyclicFourSemidirectGenerator ^ 2) =
      (QuaternionGroupFive.fourthRootParameter k : ℂ) ^ 2 := by
  rw [
    CyclicFiveInversionSemidirect.rowFDRep_character,
    quaternionFiveEquivCyclicFiveInversionSemidirect_symm_generator_sq
  ]
  change
    (IrreducibleCharacter.linearFDRep
        (QuaternionGroupFive.linearHom k)).character
          (QuaternionGroup.a (5 : ZMod 10)) =
      _
  rw [IrreducibleCharacter.linearFDRep_character]
  change
    (QuaternionGroupFive.linearHom k
        (QuaternionGroup.a (5 : ZMod 10)) : ℂ) =
      _
  rw [
    show (5 : ZMod 10) = ((5 : ℕ) : ZMod 10) by rfl,
    ← QuaternionGroup.xa_sq (n := 5) (0 : ZMod 10),
    map_pow,
    QuaternionGroupFive.linearHom_apply_reflectionGenerator
  ]
  rfl

/-- A two-dimensional dicyclic row evaluates at the central involution as
twice the fifth power of its tenth-root parameter. -/
theorem dicyclic_rowFDRep_character_generator_sq_twoDimensional
    (k : Fin 4) :
    (CyclicFiveInversionSemidirect.rowFDRep
        (.twoDimensional k)).character
          (cyclicFourSemidirectGenerator ^ 2) =
      2 * QuaternionGroupFive.twoDimensionalParameter k ^ 5 := by
  rw [
    CyclicFiveInversionSemidirect.rowFDRep_character,
    quaternionFiveEquivCyclicFiveInversionSemidirect_symm_generator_sq
  ]
  change
    (QuaternionGroupFive.twoDimensionalCharacter k).values
        (QuaternionGroup.a (5 : ZMod 10)) =
      _
  rw [
    show (5 : ZMod 10) = ((5 : ℕ) : ZMod 10) by rfl,
    QuaternionGroupFive.twoDimensionalCharacter_values_a_natCast
  ]
  have hself :
      (QuaternionGroupFive.twoDimensionalParameter k ^ 5)⁻¹ =
        QuaternionGroupFive.twoDimensionalParameter k ^ 5 := by
    apply inv_eq_of_mul_eq_one_right
    calc
      QuaternionGroupFive.twoDimensionalParameter k ^ 5 *
            QuaternionGroupFive.twoDimensionalParameter k ^ 5 =
          QuaternionGroupFive.twoDimensionalParameter k ^ 10 := by
        ring
      _ = 1 :=
        QuaternionGroupFive.twoDimensionalParameter_pow_ten k
  rw [inv_pow, hself]
  ring

/-- Exact central-character evaluation of the representation attached to
any concrete product row. -/
theorem rowFDRep_character_centralGenerator
    (r : CharacterRow) :
    (rowFDRep r).character
        alternatingSixFiveNormalizerSemidirectCentralGenerator =
      (rowDegree r : ℂ) * centralScalar r := by
  rcases r with ⟨j, r⟩
  rcases r with k | k
  · change
      (rowFDRep (j, .linear k)).character
          (Multiplicative.ofAdd 2, cyclicFourSemidirectGenerator ^ 2) =
        _
    rw [rowFDRep_character,
      cyclicThree_linearHom_ofAdd_two,
      dicyclic_rowFDRep_character_generator_sq_linear]
    simp [rowDegree, centralScalar, dicyclicCentralScalar]
  · change
      (rowFDRep (j, .twoDimensional k)).character
          (Multiplicative.ofAdd 2, cyclicFourSemidirectGenerator ^ 2) =
        _
    rw [rowFDRep_character,
      cyclicThree_linearHom_ofAdd_two,
      dicyclic_rowFDRep_character_generator_sq_twoDimensional]
    simp [rowDegree, centralScalar, dicyclicCentralScalar]
    ring

/-- The finite row degree agrees with the degree of the enumerated
irreducible character. -/
@[simp]
theorem pPrimeCharacterEquiv_degree_eq_rowDegree
    (r : CharacterRow) :
    (pPrimeCharacterEquiv r).1.degree = rowDegree r := by
  rcases r with ⟨j, r⟩
  rcases r with k | k
  · exact pPrimeCharacterEquiv_degree_linear j k
  · exact pPrimeCharacterEquiv_degree_twoDimensional j k

/-- Exact central-character evaluation of every enumerated `5'`
irreducible character. -/
theorem pPrimeCharacterEquiv_values_centralGenerator
    (r : CharacterRow) :
    (pPrimeCharacterEquiv r).1.values
        alternatingSixFiveNormalizerSemidirectCentralGenerator =
      ((pPrimeCharacterEquiv r).1.degree : ℂ) *
        centralScalar r := by
  change
    (irreducibleCharacterEquiv r).values
        alternatingSixFiveNormalizerSemidirectCentralGenerator =
      _
  rw [
    ← rowCertificate_irreducibleCharacter r,
    (rowCertificate r).irreducibleCharacter_values_apply
  ]
  change
    (rowFDRep r).character
        alternatingSixFiveNormalizerSemidirectCentralGenerator =
      _
  rw [
    rowFDRep_character_centralGenerator,
    pPrimeCharacterEquiv_degree_eq_rowDegree
  ]

end AlternatingSixFiveNormalizerSemidirectCharacterTable
end McKayConjecture
