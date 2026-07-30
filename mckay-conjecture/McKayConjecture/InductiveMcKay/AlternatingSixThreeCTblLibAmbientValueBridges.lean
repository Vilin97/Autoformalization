/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAutomorphismClassValues
import McKayConjecture.InductiveMcKay.AlternatingSixThreeCTblLibAmbientPositionBlocks

/-!
# Completed ambient value bridges for the three-local `A₆` table

The invariant-safe three-local ambient positions consist of two singleton
blocks and five pairs.  The singleton bridges are already automatic.  This
file uses the completed character table's exact class values to settle the
two pairs for which full value vectors have already been formalized:
`row18`/`row19` and `row24`/`row25`.

For either ATLAS-aligned orientation and either audited generator, these
value vectors first reduce the full ambient bridge from ten non-singleton
positions to the six positions occupied by `row08`/`row09`,
`row16`/`row17`, and `row06`/`row07`.  A certified separator value then
shows that the first generator fixes the degree-four and degree-five pairs,
while central-scalar values show that the second generator fixes the
degree-eight pair.  An additional exact `AB²` trace proves that the first
generator interchanges the degree-eight pair, closing its bridge completely.
Finally, exact traces at the positive representative of class 30 prove that
the second generator interchanges the degree-four and degree-five pairs.
Thus both audited ambient generator bridges are proved in full.

The two possible `row24`/`row25` orientations agree with the semantic
action, because the first generator interchanges those rows while the second
fixes both.

The concrete position equivalences remain proposed CTblLib identifications:
the theorems below verify semantic automorphism actions on constructed rows,
but do not independently prove CTblLib's stored row order.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory
open AlternatingSixSchurCoordinates

local instance alternatingSixThreeAmbientValueBridgesFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-! ### Exact completed-table values -/

private theorem completed_row19_value
    (j : Fin 31) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row19).values
        (alternatingSixUniversalCoverClassRepresentative j) =
      alternatingSixAmbientRow19ClassValue j := by
  change
    (alternatingSixAmbientCompletedOrdinaryRow .row19
        |>.characterRowCertificate.irreducibleCharacter).values
        (alternatingSixUniversalCoverClassRepresentative j) =
      alternatingSixAmbientRow19ClassValue j
  rw [
    (alternatingSixAmbientCompletedOrdinaryRow .row19)
      |>.characterRowCertificate.irreducibleCharacter_values_apply
  ]
  exact alternatingSixAmbientRow19_character_classRepresentative j

private theorem completed_row24_value
    (j : Fin 31) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row24).values
        (alternatingSixUniversalCoverClassRepresentative j) =
      alternatingSixAmbientRow24ClassValue j := by
  change
    (alternatingSixAmbientCompletedOrdinaryRow .row24
        |>.characterRowCertificate.irreducibleCharacter).values
        (alternatingSixUniversalCoverClassRepresentative j) =
      alternatingSixAmbientRow24ClassValue j
  rw [
    (alternatingSixAmbientCompletedOrdinaryRow .row24)
      |>.characterRowCertificate.irreducibleCharacter_values_apply
  ]
  exact alternatingSixAmbientRow24_character_classRepresentative j

private theorem completed_row25_value
    (j : Fin 31) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row25).values
        (alternatingSixUniversalCoverClassRepresentative j) =
      alternatingSixAmbientRow25ClassValue j := by
  change
    (alternatingSixAmbientCompletedOrdinaryRow .row25
        |>.characterRowCertificate.irreducibleCharacter).values
        (alternatingSixUniversalCoverClassRepresentative j) =
      alternatingSixAmbientRow25ClassValue j
  rw [
    (alternatingSixAmbientCompletedOrdinaryRow .row25)
      |>.characterRowCertificate.irreducibleCharacter_values_apply
  ]
  exact alternatingSixAmbientRow25_character_classRepresentative j

/-! ### Finite value-vector calculations -/

private theorem alphaOneClassPermutation_symm_eq_vector
    (j : Fin 31) :
    alternatingSixAlphaOneConjugacyClassPermutation.symm j =
      alternatingSixAlphaOneConjugacyClassVector j := by
  apply alternatingSixAlphaOneConjugacyClassPermutation.injective
  rw [
    alternatingSixAlphaOneConjugacyClassPermutation.apply_symm_apply,
    alternatingSixAlphaOneConjugacyClassPermutation_eq_vector
  ]
  fin_cases j <;> rfl

private theorem alphaTwoClassPermutation_symm_eq_vector
    (j : Fin 31) :
    alternatingSixAlphaTwoConjugacyClassPermutation.symm j =
      alternatingSixAlphaTwoConjugacyClassVector j := by
  apply alternatingSixAlphaTwoConjugacyClassPermutation.injective
  rw [
    alternatingSixAlphaTwoConjugacyClassPermutation.apply_symm_apply,
    alternatingSixAlphaTwoConjugacyClassPermutation_eq_vector
  ]
  fin_cases j <;> rfl

private theorem row24Gamma_eq_neg_row25Gamma :
    alternatingSixAmbientRow24Gamma =
      -alternatingSixAmbientRow25Gamma := by
  simp [
    alternatingSixAmbientRow24Gamma,
    alternatingSixAmbientRow25Gamma,
    alternatingSixCyclotomicValue
  ]
  ring

private theorem row25Gamma_eq_neg_row24Gamma :
    alternatingSixAmbientRow25Gamma =
      -alternatingSixAmbientRow24Gamma := by
  rw [row24Gamma_eq_neg_row25Gamma]
  ring

private theorem row24Gamma_ne_row25Gamma :
    alternatingSixAmbientRow24Gamma ≠
      alternatingSixAmbientRow25Gamma := by
  intro h
  apply alternatingSixAmbientRow24_matrixB_trace_ne_row25_matrixB_trace
  rw [alternatingSixAmbientRow24_matrixB_trace,
    alternatingSixAmbientRow25_matrixB_trace]
  exact h

private theorem universalCoverClassRepresentative_one_eq_centralGenerator :
    alternatingSixUniversalCoverClassRepresentative 1 =
      alternatingSixAmbientCanonicalCentralGenerator := by
  rw [
    alternatingSixUniversalCoverClassRepresentative,
    alternatingSixAmbientCanonicalCentralGenerator,
    alternatingSixAmbientCanonicalGeneratorA
  ]
  change
    alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurClassRepresentative 1) =
      (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurAuditedPresentationGeneratorCoordinates 0)) ^ 2
  rw [← map_pow]
  congr 1

private theorem universalCoverClassRepresentative_five_eq_one_inv :
    alternatingSixUniversalCoverClassRepresentative 5 =
      (alternatingSixUniversalCoverClassRepresentative 1)⁻¹ := by
  change
    alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurClassRepresentative 5) =
      (alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurClassRepresentative 1))⁻¹
  rw [← map_inv]
  congr 1

private theorem universalCoverClassRepresentative_fifteen_eq_generatorAB :
    alternatingSixUniversalCoverClassRepresentative 15 =
      alternatingSixAmbientCanonicalGeneratorAB := by
  rw [
    alternatingSixUniversalCoverClassRepresentative,
    alternatingSixAmbientCanonicalGeneratorAB,
    alternatingSixAmbientCanonicalGeneratorA,
    alternatingSixAmbientCanonicalGeneratorB
  ]
  change
    alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurClassRepresentative 15) =
      alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurAuditedPresentationGeneratorCoordinates 0) *
        alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurAuditedPresentationGeneratorCoordinates 1)
  rw [← map_mul]
  congr 1

private def alternatingSixAmbientCanonicalGeneratorABSquared :
    AlternatingSixUniversalCover :=
  alternatingSixAmbientCanonicalGeneratorA *
    alternatingSixAmbientCanonicalGeneratorB *
    alternatingSixAmbientCanonicalGeneratorB

private theorem
    universalCoverClassRepresentative_twentyOne_eq_generatorABSquared :
    alternatingSixUniversalCoverClassRepresentative 21 =
      alternatingSixAmbientCanonicalGeneratorABSquared := by
  rw [
    alternatingSixUniversalCoverClassRepresentative,
    alternatingSixAmbientCanonicalGeneratorABSquared,
    alternatingSixAmbientCanonicalGeneratorA,
    alternatingSixAmbientCanonicalGeneratorB
  ]
  change
    alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurClassRepresentative 21) =
      alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurAuditedPresentationGeneratorCoordinates 0) *
        alternatingSixSchurCoordinatesEquivUniversalCover
            (alternatingSixSchurAuditedPresentationGeneratorCoordinates 1) *
          alternatingSixSchurCoordinatesEquivUniversalCover
            (alternatingSixSchurAuditedPresentationGeneratorCoordinates 1)
  rw [← map_mul, ← map_mul]
  congr 1

private theorem character_generatorABSquared
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (C : AlternatingSixSchurMatrixRowCertificate n) :
    (FDRep.of C.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalGeneratorABSquared =
      (C.matrixA * C.matrixB * C.matrixB).trace :=
  C.universalCoverRepresentation_character_eq_trace_of_action_eq
    alternatingSixAmbientCanonicalGeneratorABSquared
    (C.matrixA * C.matrixB * C.matrixB)
    (by
      simp only [
        alternatingSixAmbientCanonicalGeneratorABSquared,
        map_mul,
        C.universalCoverRepresentation_generatorA,
        C.universalCoverRepresentation_generatorB,
        Module.End.mul_eq_comp,
        Matrix.toLin'_mul
      ])

private theorem universalCoverClassRepresentative_nineteen_eq_fifteen_mul_central :
    alternatingSixUniversalCoverClassRepresentative 19 =
      alternatingSixUniversalCoverClassRepresentative 15 *
        alternatingSixAmbientCanonicalCentralGenerator ^ 4 := by
  rw [
    alternatingSixUniversalCoverClassRepresentative,
    ← universalCoverClassRepresentative_one_eq_centralGenerator,
    alternatingSixUniversalCoverClassRepresentative
  ]
  change
    alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurClassRepresentative 19) =
      alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative 15) *
        alternatingSixSchurCoordinatesEquivUniversalCover
            (alternatingSixSchurClassRepresentative 1) ^ 4
  rw [← map_pow, ← map_mul]
  congr 1

private theorem completed_trivial_value_nineteen_eq_fifteen
    (row : AlternatingSixAmbientOrdinaryRow)
    (hrow : row.scalarPattern = .trivial) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character row).values
        (alternatingSixUniversalCoverClassRepresentative 19) =
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character row).values
        (alternatingSixUniversalCoverClassRepresentative 15) := by
  letI : Nonempty (Fin row.dimension) :=
    Fin.pos_iff_nonempty.mp row.dimension_pos
  let C := alternatingSixAmbientCompletedOrdinaryRow row
  have hcentral :
      C.matrixRow.universalCoverRepresentation
          alternatingSixAmbientCanonicalCentralGenerator = 1 := by
    rw [C.matrixRow.universalCoverRepresentation_centralGenerator,
      C.matrixRow.matrixA_sq,
      C.relatorScalar_eq_scalarPattern,
      hrow,
      AlternatingSixAmbientScalarPattern.exponent]
    simp
    rfl
  rw [
    alternatingSixAmbientOrdinaryCharacterTableCertificate
      |>.toFiniteCharacterTableCertificate.character_values_apply,
    alternatingSixAmbientOrdinaryCharacterTableCertificate
      |>.toFiniteCharacterTableCertificate.character_values_apply,
    universalCoverClassRepresentative_nineteen_eq_fifteen_mul_central
  ]
  change
    (FDRep.of C.matrixRow.universalCoverRepresentation).character
        (alternatingSixUniversalCoverClassRepresentative 15 *
          alternatingSixAmbientCanonicalCentralGenerator ^ 4) =
      (FDRep.of C.matrixRow.universalCoverRepresentation).character
        (alternatingSixUniversalCoverClassRepresentative 15)
  change
    LinearMap.trace ℂ _
      (C.matrixRow.universalCoverRepresentation
        (alternatingSixUniversalCoverClassRepresentative 15 *
          alternatingSixAmbientCanonicalCentralGenerator ^ 4)) =
      LinearMap.trace ℂ _
        (C.matrixRow.universalCoverRepresentation
          (alternatingSixUniversalCoverClassRepresentative 15))
  rw [map_mul, map_pow, hcentral]
  simp

private theorem alternatingSixComplexCyclotomicRoot_pow_sixty_eq_neg_one :
    alternatingSixComplexCyclotomicRoot ^ 60 = -1 := by
  rw [alternatingSixComplexCyclotomicRoot, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 1
  all_goals ring_nf

private theorem completed_orderTwo_centralValue
    (row : AlternatingSixAmbientOrdinaryRow)
    (hrow : row.scalarPattern = .orderTwo) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character row).values
        (alternatingSixUniversalCoverClassRepresentative 1) =
      -(row.dimension : ℂ) := by
  rw [universalCoverClassRepresentative_one_eq_centralGenerator]
  rw [
    alternatingSixAmbientOrdinaryCharacterTableCertificate
      |>.character_values_centralGenerator,
    hrow,
    AlternatingSixAmbientScalarPattern.exponent
  ]
  change
    (row.dimension : ℂ) * alternatingSixComplexCyclotomicRoot ^ 60 =
      -(row.dimension : ℂ)
  rw [alternatingSixComplexCyclotomicRoot_pow_sixty_eq_neg_one]
  ring

private theorem completed_orderTwo_inverseCentralValue
    (row : AlternatingSixAmbientOrdinaryRow)
    (hrow : row.scalarPattern = .orderTwo) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character row).values
        (alternatingSixUniversalCoverClassRepresentative 5) =
      -(row.dimension : ℂ) := by
  rw [universalCoverClassRepresentative_five_eq_one_inv,
    IrreducibleCharacter.value_inv_eq_conj,
    completed_orderTwo_centralValue row hrow]
  simp

private theorem completed_row18_value_fifteen :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row18).values
        (alternatingSixUniversalCoverClassRepresentative 15) =
      alternatingSixAmbientRow19Beta := by
  letI :
      Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row18.dimension) :=
    ⟨⟨0, by norm_num [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩
  change
    (alternatingSixAmbientCompletedOrdinaryRow .row18
        |>.characterRowCertificate.irreducibleCharacter).values
        (alternatingSixUniversalCoverClassRepresentative 15) =
      alternatingSixAmbientRow19Beta
  rw [
    (alternatingSixAmbientCompletedOrdinaryRow .row18)
      |>.characterRowCertificate.irreducibleCharacter_values_apply,
    universalCoverClassRepresentative_fifteen_eq_generatorAB
  ]
  change
    (FDRep.of
      alternatingSixAmbientRow18MatrixCertificate.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalGeneratorAB =
      alternatingSixAmbientRow19Beta
  rw [
    alternatingSixAmbientRow18MatrixCertificate
      |>.universalCoverRepresentation_character_generatorAB
  ]
  change
    (alternatingSixFiveAmbient_row18_matrixA *
      alternatingSixFiveAmbient_row18_matrixB).trace =
        alternatingSixAmbientRow19Beta
  rw [alternatingSixAmbientRow18_matrixAB_trace]
  rfl

private theorem completed_row16_value_fifteen :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row16).values
        (alternatingSixUniversalCoverClassRepresentative 15) =
      alternatingSixCyclotomicValue
        [(1, 0), (-1, 8), (-1, 12), (1, 28)] := by
  change
    (alternatingSixAmbientCompletedOrdinaryRow .row16
        |>.characterRowCertificate.irreducibleCharacter).values
        (alternatingSixUniversalCoverClassRepresentative 15) =
      alternatingSixCyclotomicValue
        [(1, 0), (-1, 8), (-1, 12), (1, 28)]
  rw [
    (alternatingSixAmbientCompletedOrdinaryRow .row16)
      |>.characterRowCertificate.irreducibleCharacter_values_apply,
    universalCoverClassRepresentative_fifteen_eq_generatorAB
  ]
  exact alternatingSixAmbientRow16_character_generatorAB

private theorem completed_row17_value_fifteen :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row17).values
        (alternatingSixUniversalCoverClassRepresentative 15) =
      alternatingSixCyclotomicValue
        [(1, 8), (1, 12), (-1, 28)] := by
  change
    (alternatingSixAmbientCompletedOrdinaryRow .row17
        |>.characterRowCertificate.irreducibleCharacter).values
        (alternatingSixUniversalCoverClassRepresentative 15) =
      alternatingSixCyclotomicValue
        [(1, 8), (1, 12), (-1, 28)]
  rw [
    (alternatingSixAmbientCompletedOrdinaryRow .row17)
      |>.characterRowCertificate.irreducibleCharacter_values_apply,
    universalCoverClassRepresentative_fifteen_eq_generatorAB
  ]
  exact alternatingSixAmbientRow17_character_generatorAB

/-- The row-16 `AB²` trace is the row-17 `AB` trace. -/
theorem alternatingSixAmbientRow16_matrixABSquared_trace :
    (alternatingSixFiveAmbient_row16_matrixA *
          alternatingSixFiveAmbient_row16_matrixB *
          alternatingSixFiveAmbient_row16_matrixB).trace =
      alternatingSixCyclotomicValue
        [(1, 8), (1, 12), (-1, 28)] := by
  change
    (∑ i : Fin 8,
      (alternatingSixFiveAmbient_row16_matrixA *
          alternatingSixFiveAmbient_row16_matrixB *
          alternatingSixFiveAmbient_row16_matrixB) i i) =
      alternatingSixCyclotomicValue
        [(1, 8), (1, 12), (-1, 28)]
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row16_matrixA,
    alternatingSixFiveAmbient_row16_matrixB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  linear_combination
    ((517 / 25 : ℂ) - (517 / 25 : ℂ) *
          alternatingSixComplexCyclotomicRoot ^ 4 -
        (23 / 25 : ℂ) * alternatingSixComplexCyclotomicRoot ^ 8 +
        19 * alternatingSixComplexCyclotomicRoot ^ 12 +
        (71 / 25 : ℂ) * alternatingSixComplexCyclotomicRoot ^ 16 -
        (8 / 25 : ℂ) * alternatingSixComplexCyclotomicRoot ^ 20 +
        (52 / 25 : ℂ) * alternatingSixComplexCyclotomicRoot ^ 24 +
        (291 / 25 : ℂ) * alternatingSixComplexCyclotomicRoot ^ 28 -
        (482 / 25 : ℂ) * alternatingSixComplexCyclotomicRoot ^ 32 -
        (329 / 25 : ℂ) * alternatingSixComplexCyclotomicRoot ^ 36 +
        (293 / 25 : ℂ) * alternatingSixComplexCyclotomicRoot ^ 40 -
        (44 / 5 : ℂ) * alternatingSixComplexCyclotomicRoot ^ 44 -
        (57 / 5 : ℂ) * alternatingSixComplexCyclotomicRoot ^ 48 +
        (452 / 25 : ℂ) * alternatingSixComplexCyclotomicRoot ^ 52) *
      alternatingSixComplexCyclotomicRoot_relation

private theorem completed_row16_value_twentyOne :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row16).values
        (alternatingSixUniversalCoverClassRepresentative 21) =
      alternatingSixCyclotomicValue
        [(1, 8), (1, 12), (-1, 28)] := by
  letI :
      Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row16.dimension) :=
    ⟨⟨0, by norm_num [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩
  change
    (alternatingSixAmbientCompletedOrdinaryRow .row16
        |>.characterRowCertificate.irreducibleCharacter).values
        (alternatingSixUniversalCoverClassRepresentative 21) =
      alternatingSixCyclotomicValue
        [(1, 8), (1, 12), (-1, 28)]
  rw [
    (alternatingSixAmbientCompletedOrdinaryRow .row16)
      |>.characterRowCertificate.irreducibleCharacter_values_apply,
    universalCoverClassRepresentative_twentyOne_eq_generatorABSquared
  ]
  change
    (FDRep.of
      alternatingSixAmbientRow16MatrixCertificate.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalGeneratorABSquared =
      alternatingSixCyclotomicValue
        [(1, 8), (1, 12), (-1, 28)]
  rw [character_generatorABSquared]
  change
    (alternatingSixFiveAmbient_row16_matrixA *
          alternatingSixFiveAmbient_row16_matrixB *
          alternatingSixFiveAmbient_row16_matrixB).trace =
      alternatingSixCyclotomicValue
        [(1, 8), (1, 12), (-1, 28)]
  exact alternatingSixAmbientRow16_matrixABSquared_trace

private theorem completed_row16_value_nineteen :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row16).values
        (alternatingSixUniversalCoverClassRepresentative 19) =
      alternatingSixCyclotomicValue
        [(1, 0), (-1, 8), (-1, 12), (1, 28)] := by
  rw [completed_trivial_value_nineteen_eq_fifteen .row16 (by rfl),
    completed_row16_value_fifteen]

private theorem completed_row17_value_nineteen :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row17).values
        (alternatingSixUniversalCoverClassRepresentative 19) =
      alternatingSixCyclotomicValue
        [(1, 8), (1, 12), (-1, 28)] := by
  rw [completed_trivial_value_nineteen_eq_fifteen .row17 (by rfl),
    completed_row17_value_fifteen]

private theorem row16FifteenValue_ne_row17FifteenValue :
    alternatingSixCyclotomicValue
        [(1, 0), (-1, 8), (-1, 12), (1, 28)] ≠
      alternatingSixCyclotomicValue
        [(1, 8), (1, 12), (-1, 28)] := by
  intro hequal
  apply alternatingSixAmbientRow16Row17DifferencePolynomial_ne_zero
  rw [← sub_eq_zero.mpr hequal]
  simp [
    alternatingSixAmbientRow16Row17DifferencePolynomial,
    alternatingSixCyclotomicValue
  ]
  ring

private theorem row19Alpha_ne_row19Beta :
    alternatingSixAmbientRow19Alpha ≠
      alternatingSixAmbientRow19Beta := by
  intro h
  apply alternatingSixAmbientRow18_matrixAB_trace_ne_row19_matrixAB_trace
  rw [alternatingSixAmbientRow18_matrixAB_trace,
    alternatingSixAmbientRow19_matrixAB_trace]
  simpa only [
    alternatingSixAmbientRow19Alpha,
    alternatingSixAmbientRow19Beta
  ] using h.symm

private theorem ambientAlphaOne_orderTwo_centralValue
    (r : AlternatingSixAmbientPPrimeRowIndex 3)
    (hr : r.1.scalarPattern = .orderTwo) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character
          (alternatingSixAmbientPPrimeAlphaOneRowPermutation
            alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r).1).values
        (alternatingSixUniversalCoverClassRepresentative 1) =
      -(r.1.dimension : ℂ) := by
  calc
    _ =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
            |>.toFiniteCharacterTableCertificate.character r.1).values
          (alternatingSixUniversalCoverClassRepresentative
            (alternatingSixAlphaOneConjugacyClassPermutation.symm 1)) :=
      alternatingSixAmbientPPrimeAlphaOneRowPermutation_values_classRepresentative
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r 1
    _ =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
            |>.toFiniteCharacterTableCertificate.character r.1).values
          (alternatingSixUniversalCoverClassRepresentative 5) := by
      rw [alphaOneClassPermutation_symm_eq_vector]
      rfl
    _ = -(r.1.dimension : ℂ) :=
      completed_orderTwo_inverseCentralValue r.1 hr

private theorem ambientAlphaTwo_orderTwo_centralValue
    (r : AlternatingSixAmbientPPrimeRowIndex 3)
    (hr : r.1.scalarPattern = .orderTwo) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character
          (alternatingSixAmbientPPrimeAlphaTwoRowPermutation
            alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r).1).values
        (alternatingSixUniversalCoverClassRepresentative 1) =
      -(r.1.dimension : ℂ) := by
  calc
    _ =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
            |>.toFiniteCharacterTableCertificate.character r.1).values
          (alternatingSixUniversalCoverClassRepresentative
            (alternatingSixAlphaTwoConjugacyClassPermutation.symm 1)) :=
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation_values_classRepresentative
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r 1
    _ =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
            |>.toFiniteCharacterTableCertificate.character r.1).values
          (alternatingSixUniversalCoverClassRepresentative 5) := by
      rw [alphaTwoClassPermutation_symm_eq_vector]
      rfl
    _ = -(r.1.dimension : ℂ) :=
      completed_orderTwo_inverseCentralValue r.1 hr

private theorem completed_trivial_centralValue
    (row : AlternatingSixAmbientOrdinaryRow)
    (hrow : row.scalarPattern = .trivial) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character row).values
        (alternatingSixUniversalCoverClassRepresentative 1) =
      (row.dimension : ℂ) := by
  rw [universalCoverClassRepresentative_one_eq_centralGenerator]
  rw [
    alternatingSixAmbientOrdinaryCharacterTableCertificate
      |>.character_values_centralGenerator,
    hrow,
    AlternatingSixAmbientScalarPattern.exponent
  ]
  simp

private theorem completed_trivial_inverseCentralValue
    (row : AlternatingSixAmbientOrdinaryRow)
    (hrow : row.scalarPattern = .trivial) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character row).values
        (alternatingSixUniversalCoverClassRepresentative 5) =
      (row.dimension : ℂ) := by
  rw [universalCoverClassRepresentative_five_eq_one_inv,
    IrreducibleCharacter.value_inv_eq_conj,
    completed_trivial_centralValue row hrow]
  simp

private theorem ambientAlphaOne_trivial_centralValue
    (r : AlternatingSixAmbientPPrimeRowIndex 3)
    (hr : r.1.scalarPattern = .trivial) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character
          (alternatingSixAmbientPPrimeAlphaOneRowPermutation
            alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r).1).values
        (alternatingSixUniversalCoverClassRepresentative 1) =
      (r.1.dimension : ℂ) := by
  calc
    _ =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
            |>.toFiniteCharacterTableCertificate.character r.1).values
          (alternatingSixUniversalCoverClassRepresentative
            (alternatingSixAlphaOneConjugacyClassPermutation.symm 1)) :=
      alternatingSixAmbientPPrimeAlphaOneRowPermutation_values_classRepresentative
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r 1
    _ =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
            |>.toFiniteCharacterTableCertificate.character r.1).values
          (alternatingSixUniversalCoverClassRepresentative 5) := by
      rw [alphaOneClassPermutation_symm_eq_vector]
      rfl
    _ = (r.1.dimension : ℂ) :=
      completed_trivial_inverseCentralValue r.1 hr

private theorem ambientAlphaTwo_trivial_centralValue
    (r : AlternatingSixAmbientPPrimeRowIndex 3)
    (hr : r.1.scalarPattern = .trivial) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character
          (alternatingSixAmbientPPrimeAlphaTwoRowPermutation
            alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r).1).values
        (alternatingSixUniversalCoverClassRepresentative 1) =
      (r.1.dimension : ℂ) := by
  calc
    _ =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
            |>.toFiniteCharacterTableCertificate.character r.1).values
          (alternatingSixUniversalCoverClassRepresentative
            (alternatingSixAlphaTwoConjugacyClassPermutation.symm 1)) :=
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation_values_classRepresentative
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r 1
    _ =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
            |>.toFiniteCharacterTableCertificate.character r.1).values
          (alternatingSixUniversalCoverClassRepresentative 5) := by
      rw [alphaTwoClassPermutation_symm_eq_vector]
      rfl
    _ = (r.1.dimension : ℂ) :=
      completed_trivial_inverseCentralValue r.1 hr

private theorem pPrimeRow_eq_row18_or_row19_of_dimension_centralValue
    (r : AlternatingSixAmbientPPrimeRowIndex 3)
    (hdimension : r.1.dimension = 8)
    (hcentral :
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character r.1).values
          (alternatingSixUniversalCoverClassRepresentative 1) =
        (-8 : ℂ)) :
    r.1 = .row18 ∨ r.1 = .row19 := by
  have hadvertised :=
    alternatingSixAmbientOrdinaryCharacterTableCertificate
      |>.character_values_centralGenerator r.1
  rw [← universalCoverClassRepresentative_one_eq_centralGenerator,
    hcentral] at hadvertised
  rcases r with ⟨row, hrow⟩
  cases row <;>
    simp_all [
      AlternatingSixAmbientOrdinaryRow.dimension,
      AlternatingSixAmbientOrdinaryRow.scalarPattern,
      AlternatingSixAmbientScalarPattern.exponent
    ] <;>
    norm_num at hadvertised

private theorem pPrimeRow_eq_row16_or_row17_of_dimension_centralValue
    (r : AlternatingSixAmbientPPrimeRowIndex 3)
    (hdimension : r.1.dimension = 8)
    (hcentral :
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character r.1).values
          (alternatingSixUniversalCoverClassRepresentative 1) =
        (8 : ℂ)) :
    r.1 = .row16 ∨ r.1 = .row17 := by
  rcases r with ⟨row, hrow⟩
  have hcases :
      row = .row16 ∨ row = .row17 ∨ row = .row18 ∨ row = .row19 := by
    cases row <;>
      simp_all [AlternatingSixAmbientOrdinaryRow.dimension]
  rcases hcases with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · have hnegative :=
      completed_orderTwo_centralValue .row18 (by rfl)
    rw [hcentral] at hnegative
    norm_num [AlternatingSixAmbientOrdinaryRow.dimension] at hnegative
  · have hnegative :=
      completed_orderTwo_centralValue .row19 (by rfl)
    rw [hcentral] at hnegative
    norm_num [AlternatingSixAmbientOrdinaryRow.dimension] at hnegative

private theorem pPrimeRow_eq_row24_or_row25_of_dimension_centralValue
    (r : AlternatingSixAmbientPPrimeRowIndex 3)
    (hdimension : r.1.dimension = 10)
    (hcentral :
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character r.1).values
          (alternatingSixUniversalCoverClassRepresentative 1) =
        (-10 : ℂ)) :
    r.1 = .row24 ∨ r.1 = .row25 := by
  have hadvertised :=
    alternatingSixAmbientOrdinaryCharacterTableCertificate
      |>.character_values_centralGenerator r.1
  rw [← universalCoverClassRepresentative_one_eq_centralGenerator,
    hcentral] at hadvertised
  rcases r with ⟨row, hrow⟩
  cases row <;>
    simp_all [
      AlternatingSixAmbientOrdinaryRow.dimension,
      AlternatingSixAmbientOrdinaryRow.scalarPattern,
      AlternatingSixAmbientScalarPattern.exponent
    ]
  all_goals
    norm_num at hadvertised

/-! ### The previously certified separator class -/

private def alternatingSixAmbientSeparatorCoordinate :
    AlternatingSixSchurCoordinates :=
  alternatingSixSchurAuditedPresentationGeneratorCoordinates 0 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1

private theorem alternatingSixAmbientSeparatorCoordinate_classIndex :
    alternatingSixSchurClassIndex alternatingSixAmbientSeparatorCoordinate =
      28 := by
  rfl

private theorem
    alternatingSixSchurCoordinatesEquivUniversalCover_generatorA :
    alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurAuditedPresentationGeneratorCoordinates 0) =
      alternatingSixAmbientCanonicalGeneratorA := by
  change
    (alternatingSixSchurUniversalCentralExtension.sourceEquiv
      alternatingSixUniversalCentralExtension)
        (mulEquivPresentedGroup
          (alternatingSixSchurAuditedPresentationGeneratorCoordinates 0)) =
      (alternatingSixSchurUniversalCentralExtension.sourceEquiv
        alternatingSixUniversalCentralExtension)
          alternatingSixSchurPresentedA
  congr 1

private theorem
    alternatingSixSchurCoordinatesEquivUniversalCover_generatorB :
    alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurAuditedPresentationGeneratorCoordinates 1) =
      alternatingSixAmbientCanonicalGeneratorB := by
  change
    (alternatingSixSchurUniversalCentralExtension.sourceEquiv
      alternatingSixUniversalCentralExtension)
        (mulEquivPresentedGroup
          (alternatingSixSchurAuditedPresentationGeneratorCoordinates 1)) =
      (alternatingSixSchurUniversalCentralExtension.sourceEquiv
        alternatingSixUniversalCentralExtension)
          alternatingSixSchurPresentedB
  congr 1

private theorem alternatingSixAmbientSeparatorCoordinate_universalCover :
    alternatingSixSchurCoordinatesEquivUniversalCover
        alternatingSixAmbientSeparatorCoordinate =
      alternatingSixAmbientCanonicalSeparator := by
  simp only [
    alternatingSixAmbientSeparatorCoordinate,
    alternatingSixAmbientCanonicalSeparator,
    map_mul
  ]
  rw [
    alternatingSixSchurCoordinatesEquivUniversalCover_generatorA,
    alternatingSixSchurCoordinatesEquivUniversalCover_generatorB
  ]

private theorem completed_value_classTwentyEight_eq_separator
    (row : AlternatingSixAmbientOrdinaryRow) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character row).values
        (alternatingSixUniversalCoverClassRepresentative 28) =
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character row).values
        alternatingSixAmbientCanonicalSeparator := by
  rw [
    alternatingSixAmbientOrdinaryCharacterTableCertificate
      |>.toFiniteCharacterTableCertificate.character_values_apply,
    alternatingSixAmbientOrdinaryCharacterTableCertificate
      |>.toFiniteCharacterTableCertificate.character_values_apply
  ]
  have h :=
    alternatingSixAmbient_character_coordinate_eq_representative
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.row row).representation
      alternatingSixAmbientSeparatorCoordinate
  rw [
    alternatingSixAmbientSeparatorCoordinate_classIndex,
    alternatingSixAmbientSeparatorCoordinate_universalCover
  ] at h
  exact h.symm

private theorem completed_row06_value_twentyEight :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row06).values
        (alternatingSixUniversalCoverClassRepresentative 28) =
      1 := by
  rw [completed_value_classTwentyEight_eq_separator]
  change
    (alternatingSixAmbientCompletedOrdinaryRow .row06
        |>.characterRowCertificate.irreducibleCharacter).values
        alternatingSixAmbientCanonicalSeparator = 1
  rw [
    (alternatingSixAmbientCompletedOrdinaryRow .row06)
      |>.characterRowCertificate.irreducibleCharacter_values_apply
  ]
  exact alternatingSixAmbientRow06_character_separator

private theorem completed_row07_value_twentyEight :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row07).values
        (alternatingSixUniversalCoverClassRepresentative 28) =
      -2 := by
  rw [completed_value_classTwentyEight_eq_separator]
  change
    (alternatingSixAmbientCompletedOrdinaryRow .row07
        |>.characterRowCertificate.irreducibleCharacter).values
        alternatingSixAmbientCanonicalSeparator = -2
  rw [
    (alternatingSixAmbientCompletedOrdinaryRow .row07)
      |>.characterRowCertificate.irreducibleCharacter_values_apply
  ]
  exact alternatingSixAmbientRow07_character_separator

private theorem completed_row08_value_twentyEight :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row08).values
        (alternatingSixUniversalCoverClassRepresentative 28) =
      2 := by
  rw [completed_value_classTwentyEight_eq_separator]
  change
    (alternatingSixAmbientCompletedOrdinaryRow .row08
        |>.characterRowCertificate.irreducibleCharacter).values
        alternatingSixAmbientCanonicalSeparator = 2
  rw [
    (alternatingSixAmbientCompletedOrdinaryRow .row08)
      |>.characterRowCertificate.irreducibleCharacter_values_apply
  ]
  exact alternatingSixAmbientRow08_character_separator

private theorem completed_row09_value_twentyEight :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row09).values
        (alternatingSixUniversalCoverClassRepresentative 28) =
      -1 := by
  rw [completed_value_classTwentyEight_eq_separator]
  change
    (alternatingSixAmbientCompletedOrdinaryRow .row09
        |>.characterRowCertificate.irreducibleCharacter).values
        alternatingSixAmbientCanonicalSeparator = -1
  rw [
    (alternatingSixAmbientCompletedOrdinaryRow .row09)
      |>.characterRowCertificate.irreducibleCharacter_values_apply
  ]
  exact alternatingSixAmbientRow09_character_separator

/-! ### The second-generator image of the separator class -/

private def alternatingSixAmbientCanonicalState79Positive :
    AlternatingSixUniversalCover :=
  alternatingSixAmbientCanonicalGeneratorA *
    alternatingSixAmbientCanonicalGeneratorB *
    alternatingSixAmbientCanonicalGeneratorA *
    alternatingSixAmbientCanonicalGeneratorB *
    alternatingSixAmbientCanonicalGeneratorB *
    alternatingSixAmbientCanonicalGeneratorB *
    alternatingSixAmbientCanonicalGeneratorA *
    alternatingSixAmbientCanonicalGeneratorB *
    alternatingSixAmbientCanonicalGeneratorB

private def alternatingSixAmbientState79PositiveCoordinate :
    AlternatingSixSchurCoordinates :=
  alternatingSixSchurAuditedPresentationGeneratorCoordinates 0 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1 *
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1

private theorem alternatingSixAmbientState79PositiveCoordinate_classIndex :
    alternatingSixSchurClassIndex
        alternatingSixAmbientState79PositiveCoordinate =
      30 := by
  rfl

private theorem
    alternatingSixAmbientState79PositiveCoordinate_universalCover :
    alternatingSixSchurCoordinatesEquivUniversalCover
        alternatingSixAmbientState79PositiveCoordinate =
      alternatingSixAmbientCanonicalState79Positive := by
  simp only [
    alternatingSixAmbientState79PositiveCoordinate,
    alternatingSixAmbientCanonicalState79Positive,
    map_mul
  ]
  rw [
    alternatingSixSchurCoordinatesEquivUniversalCover_generatorA,
    alternatingSixSchurCoordinatesEquivUniversalCover_generatorB
  ]

private theorem character_state79Positive
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (C : AlternatingSixSchurMatrixRowCertificate n) :
    (FDRep.of C.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalState79Positive =
      (C.matrixA * C.matrixB * C.matrixA *
        C.matrixB * C.matrixB * C.matrixB * C.matrixA *
        C.matrixB * C.matrixB).trace :=
  C.universalCoverRepresentation_character_eq_trace_of_action_eq
    alternatingSixAmbientCanonicalState79Positive
    (C.matrixA * C.matrixB * C.matrixA *
      C.matrixB * C.matrixB * C.matrixB * C.matrixA *
      C.matrixB * C.matrixB)
    (by
      simp only [
        alternatingSixAmbientCanonicalState79Positive,
        map_mul,
        C.universalCoverRepresentation_generatorA,
        C.universalCoverRepresentation_generatorB,
        Module.End.mul_eq_comp,
        Matrix.toLin'_mul
      ])

private theorem completed_value_classThirty_eq_state79Positive
    (row : AlternatingSixAmbientOrdinaryRow) :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character row).values
        (alternatingSixUniversalCoverClassRepresentative 30) =
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character row).values
        alternatingSixAmbientCanonicalState79Positive := by
  rw [
    alternatingSixAmbientOrdinaryCharacterTableCertificate
      |>.toFiniteCharacterTableCertificate.character_values_apply,
    alternatingSixAmbientOrdinaryCharacterTableCertificate
      |>.toFiniteCharacterTableCertificate.character_values_apply
  ]
  have h :=
    alternatingSixAmbient_character_coordinate_eq_representative
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.row row).representation
      alternatingSixAmbientState79PositiveCoordinate
  rw [
    alternatingSixAmbientState79PositiveCoordinate_classIndex,
    alternatingSixAmbientState79PositiveCoordinate_universalCover
  ] at h
  exact h.symm

/-- The positive class-30 word has value `-1` in row 08. -/
theorem alternatingSixAmbientRow08_state79Positive_trace :
    (alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB).trace =
      -1 := by
  change
    (∑ i : Fin 5,
      (alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB) i i) = -1
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row08_matrixA,
    alternatingSixFiveAmbient_row08_matrixB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]

private theorem state79DegreeFourRoot_orderSixRelation :
    alternatingSixComplexCyclotomicRoot ^ 40 -
          alternatingSixComplexCyclotomicRoot ^ 20 + 1 = 0 := by
  have h :=
    congrArg alternatingSixCyclotomicEmbedding
      alternatingSixCyclotomicRoot_orderSixRelation
  simpa only [
    map_sub,
    map_add,
    map_pow,
    map_one,
    map_zero,
    alternatingSixCyclotomicEmbedding_root
  ] using h

private theorem state79DegreeFourRoot_pow_forty :
    alternatingSixComplexCyclotomicRoot ^ 40 =
      alternatingSixComplexCyclotomicRoot ^ 20 - 1 := by
  linear_combination state79DegreeFourRoot_orderSixRelation

private def alternatingSixAmbientRow06State79MatrixAB :
    Matrix (Fin 4) (Fin 4) ℂ :=
  let ω := alternatingSixComplexCyclotomicRoot ^ 20
  ![
      ![-ω, 0, 1, -ω],
      ![1 - ω, ω, ω, 1 - ω],
      ![0, -1, -1 + ω, 2 - ω],
      ![1, -1 + ω, -1 + ω, 2 - ω]
    ]

private def alternatingSixAmbientRow06State79MatrixABB :
    Matrix (Fin 4) (Fin 4) ℂ :=
  let ω := alternatingSixComplexCyclotomicRoot ^ 20
  ![
      ![ω, -1, -1 + ω, 1],
      ![-1 + ω, 1 - ω, -ω, -1 + 2 * ω],
      ![ω, -1, -ω, ω],
      ![0, 0, -ω, ω]
    ]

private def alternatingSixAmbientRow06State79MatrixABBB :
    Matrix (Fin 4) (Fin 4) ℂ :=
  let ω := alternatingSixComplexCyclotomicRoot ^ 20
  ![
      ![0, 0, -ω, -1 + ω],
      ![0, 1 - ω, 1 - ω, -1 + ω],
      ![1 - ω, -1 + ω, ω, 1 - ω],
      ![0, 0, 1, 0]
    ]

private theorem alternatingSixAmbientRow06State79MatrixAB_eq :
    alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixFiveAmbient_row06_matrixB =
      alternatingSixAmbientRow06State79MatrixAB := by
  ext i j
  fin_cases i <;> fin_cases j <;> rw [Matrix.mul_apply] <;>
    simp [
      alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06State79MatrixAB,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ
    ]
  all_goals try ring_nf
  all_goals
    rw [state79DegreeFourRoot_pow_forty]
    ring

private theorem alternatingSixAmbientRow06State79MatrixABB_eq :
    (alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB) *
        alternatingSixFiveAmbient_row06_matrixB =
      alternatingSixAmbientRow06State79MatrixABB := by
  rw [alternatingSixAmbientRow06State79MatrixAB_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> rw [Matrix.mul_apply] <;>
    simp [
      alternatingSixAmbientRow06State79MatrixAB,
      alternatingSixAmbientRow06State79MatrixABB,
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ
    ]
  all_goals try ring_nf
  all_goals
    rw [state79DegreeFourRoot_pow_forty]
    ring

private theorem alternatingSixAmbientRow06State79MatrixABBB_eq :
    ((alternatingSixFiveAmbient_row06_matrixA *
            alternatingSixFiveAmbient_row06_matrixB) *
          alternatingSixFiveAmbient_row06_matrixB) *
        alternatingSixFiveAmbient_row06_matrixB =
      alternatingSixAmbientRow06State79MatrixABBB := by
  rw [alternatingSixAmbientRow06State79MatrixABB_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> rw [Matrix.mul_apply] <;>
    simp [
      alternatingSixAmbientRow06State79MatrixABB,
      alternatingSixAmbientRow06State79MatrixABBB,
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ
    ]
  all_goals try ring_nf
  all_goals
    rw [state79DegreeFourRoot_pow_forty]
    ring

/-- The positive class-30 word has value `-2` in row 06. -/
theorem alternatingSixAmbientRow06_state79Positive_trace :
    (alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB).trace =
      -2 := by
  rw [show
    alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB =
        (alternatingSixFiveAmbient_row06_matrixA *
            alternatingSixFiveAmbient_row06_matrixB) *
          (alternatingSixFiveAmbient_row06_matrixA *
            alternatingSixFiveAmbient_row06_matrixB *
            alternatingSixFiveAmbient_row06_matrixB *
            alternatingSixFiveAmbient_row06_matrixB) *
          (alternatingSixFiveAmbient_row06_matrixA *
            alternatingSixFiveAmbient_row06_matrixB *
            alternatingSixFiveAmbient_row06_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [
    alternatingSixAmbientRow06State79MatrixABBB_eq,
    alternatingSixAmbientRow06State79MatrixABB_eq,
    alternatingSixAmbientRow06State79MatrixAB_eq
  ]
  change
    (∑ i : Fin 4,
      (alternatingSixAmbientRow06State79MatrixAB *
          alternatingSixAmbientRow06State79MatrixABBB *
          alternatingSixAmbientRow06State79MatrixABB) i i) = -2
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow06State79MatrixAB,
    alternatingSixAmbientRow06State79MatrixABBB,
    alternatingSixAmbientRow06State79MatrixABB,
    Fin.sum_univ_succ
  ]
  ring_nf
  rw [state79DegreeFourRoot_pow_forty]
  ring_nf
  rw [alternatingSixComplexCyclotomicRoot_pow_sixty_eq_neg_one]
  norm_num

private theorem completed_row08_value_thirty :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row08).values
        (alternatingSixUniversalCoverClassRepresentative 30) =
      -1 := by
  letI :
      Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row08.dimension) :=
    ⟨⟨0, by norm_num [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩
  rw [completed_value_classThirty_eq_state79Positive]
  change
    (alternatingSixAmbientCompletedOrdinaryRow .row08
        |>.characterRowCertificate.irreducibleCharacter).values
        alternatingSixAmbientCanonicalState79Positive = -1
  rw [
    (alternatingSixAmbientCompletedOrdinaryRow .row08)
      |>.characterRowCertificate.irreducibleCharacter_values_apply
  ]
  change
    (FDRep.of
      alternatingSixAmbientRow08MatrixCertificate.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalState79Positive = -1
  rw [character_state79Positive]
  change
    (alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB).trace =
      -1
  exact alternatingSixAmbientRow08_state79Positive_trace

private theorem completed_row06_value_thirty :
    (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character .row06).values
        (alternatingSixUniversalCoverClassRepresentative 30) =
      -2 := by
  letI :
      Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row06.dimension) :=
    ⟨⟨0, by norm_num [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩
  rw [completed_value_classThirty_eq_state79Positive]
  change
    (alternatingSixAmbientCompletedOrdinaryRow .row06
        |>.characterRowCertificate.irreducibleCharacter).values
        alternatingSixAmbientCanonicalState79Positive = -2
  rw [
    (alternatingSixAmbientCompletedOrdinaryRow .row06)
      |>.characterRowCertificate.irreducibleCharacter_values_apply
  ]
  change
    (FDRep.of
      alternatingSixAmbientRow06MatrixCertificate.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalState79Positive = -2
  rw [character_state79Positive]
  change
    (alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB).trace =
      -2
  exact alternatingSixAmbientRow06_state79Positive_trace

private theorem pPrimeRow_eq_row06_or_row07_of_dimension
    (r : AlternatingSixAmbientPPrimeRowIndex 3)
    (hdimension : r.1.dimension = 4) :
    r.1 = .row06 ∨ r.1 = .row07 := by
  rcases r with ⟨row, hrow⟩
  cases row <;>
    simp_all [AlternatingSixAmbientOrdinaryRow.dimension]

private theorem pPrimeRow_eq_row08_or_row09_of_dimension
    (r : AlternatingSixAmbientPPrimeRowIndex 3)
    (hdimension : r.1.dimension = 5) :
    r.1 = .row08 ∨ r.1 = .row09 := by
  rcases r with ⟨row, hrow⟩
  cases row <;>
    simp_all [AlternatingSixAmbientOrdinaryRow.dimension]

/-! ### Semantic actions on the two completed value blocks -/

@[simp]
theorem alternatingSixThreeAmbientAlphaOneRow19_eq_row18 :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row19, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row18, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row19, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 8 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaOneRowPermutation,
      r, AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaOne r
  have hcentral :
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 1) =
        (-8 : ℂ) := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaOneRowPermutation,
      r, AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      ambientAlphaOne_orderTwo_centralValue r (by rfl)
  rcases
      pPrimeRow_eq_row18_or_row19_of_dimension_centralValue
        s hdimension hcentral with hrow18 | hrow19
  · exact Subtype.ext hrow18
  · exfalso
    have hvalue :=
      alternatingSixAmbientPPrimeAlphaOneRowPermutation_values_classRepresentative
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r 15
    change
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 15) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character .row19).values
          (alternatingSixUniversalCoverClassRepresentative
            (alternatingSixAlphaOneConjugacyClassPermutation.symm 15))
      at hvalue
    rw [hrow19, completed_row19_value,
      completed_row19_value,
      alphaOneClassPermutation_symm_eq_vector] at hvalue
    change
      alternatingSixAmbientRow19Alpha =
        alternatingSixAmbientRow19Beta at hvalue
    exact row19Alpha_ne_row19Beta hvalue

@[simp]
theorem alternatingSixThreeAmbientAlphaTwoRow19_fixed :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row19, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row19, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row19, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 8 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation,
      r, AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaTwo r
  have hcentral :
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 1) =
        (-8 : ℂ) := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation,
      r, AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      ambientAlphaTwo_orderTwo_centralValue r (by rfl)
  rcases
      pPrimeRow_eq_row18_or_row19_of_dimension_centralValue
        s hdimension hcentral with hrow18 | hrow19
  · exfalso
    have hvalue :=
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation_values_classRepresentative
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r 15
    change
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 15) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character .row19).values
          (alternatingSixUniversalCoverClassRepresentative
            (alternatingSixAlphaTwoConjugacyClassPermutation.symm 15))
      at hvalue
    rw [hrow18, completed_row18_value_fifteen,
      completed_row19_value,
      alphaTwoClassPermutation_symm_eq_vector] at hvalue
    change
      alternatingSixAmbientRow19Beta =
        alternatingSixAmbientRow19Alpha at hvalue
    exact row19Alpha_ne_row19Beta hvalue.symm
  · exact Subtype.ext hrow19

@[simp]
theorem alternatingSixThreeAmbientAlphaOneRow18_eq_row19 :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row18, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row19, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row18, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 8 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaOneRowPermutation,
      r, AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaOne r
  have hcentral :
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 1) =
        (-8 : ℂ) := by
    dsimp only [s]
    simpa [r, AlternatingSixAmbientOrdinaryRow.dimension] using
      ambientAlphaOne_orderTwo_centralValue r (by rfl)
  rcases
      pPrimeRow_eq_row18_or_row19_of_dimension_centralValue
        s hdimension hcentral with hrow18 | hrow19
  · exfalso
    have hs :
        s =
          alternatingSixAmbientPPrimeAlphaOneRowPermutation
            alternatingSixAmbientOrdinaryCharacterTableCertificate 3
            (⟨.row19, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) := by
      calc
        s = (⟨.row18, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) :=
          Subtype.ext hrow18
        _ =
            alternatingSixAmbientPPrimeAlphaOneRowPermutation
              alternatingSixAmbientOrdinaryCharacterTableCertificate 3
              (⟨.row19, by decide⟩ :
                AlternatingSixAmbientPPrimeRowIndex 3) :=
          alternatingSixThreeAmbientAlphaOneRow19_eq_row18.symm
    have hsource :=
      (alternatingSixAmbientPPrimeAlphaOneRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate 3).injective hs
    have hval := congrArg Subtype.val hsource
    simp [r] at hval
  · exact Subtype.ext hrow19

@[simp]
theorem alternatingSixThreeAmbientAlphaTwoRow18_fixed :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row18, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row18, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row18, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 8 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation,
      r, AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaTwo r
  have hcentral :
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 1) =
        (-8 : ℂ) := by
    dsimp only [s]
    simpa [r, AlternatingSixAmbientOrdinaryRow.dimension] using
      ambientAlphaTwo_orderTwo_centralValue r (by rfl)
  rcases
      pPrimeRow_eq_row18_or_row19_of_dimension_centralValue
        s hdimension hcentral with hrow18 | hrow19
  · exact Subtype.ext hrow18
  · exfalso
    have hs :
        s =
          alternatingSixAmbientPPrimeAlphaTwoRowPermutation
            alternatingSixAmbientOrdinaryCharacterTableCertificate 3
            (⟨.row19, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) := by
      calc
        s = (⟨.row19, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) :=
          Subtype.ext hrow19
        _ =
            alternatingSixAmbientPPrimeAlphaTwoRowPermutation
              alternatingSixAmbientOrdinaryCharacterTableCertificate 3
              (⟨.row19, by decide⟩ :
                AlternatingSixAmbientPPrimeRowIndex 3) :=
          alternatingSixThreeAmbientAlphaTwoRow19_fixed.symm
    have hsource :=
      (alternatingSixAmbientPPrimeAlphaTwoRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate 3).injective hs
    have hval := congrArg Subtype.val hsource
    simp [r] at hval

@[simp]
theorem alternatingSixThreeAmbientAlphaOneRow24_eq_row25 :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row24, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row25, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row24, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 10 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaOneRowPermutation,
      r, AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaOne r
  have hcentral :
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 1) =
        (-10 : ℂ) := by
    dsimp only [s]
    simpa [r, AlternatingSixAmbientOrdinaryRow.dimension] using
      ambientAlphaOne_orderTwo_centralValue r (by rfl)
  rcases
      pPrimeRow_eq_row24_or_row25_of_dimension_centralValue
        s hdimension hcentral with hrow24 | hrow25
  · exfalso
    have hvalue :=
      alternatingSixAmbientPPrimeAlphaOneRowPermutation_values_classRepresentative
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r 9
    change
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 9) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character .row24).values
          (alternatingSixUniversalCoverClassRepresentative
            (alternatingSixAlphaOneConjugacyClassPermutation.symm 9))
      at hvalue
    rw [hrow24, completed_row24_value,
      completed_row24_value,
      alphaOneClassPermutation_symm_eq_vector] at hvalue
    change
      alternatingSixAmbientRow24Gamma =
        -alternatingSixAmbientRow24Gamma at hvalue
    apply row24Gamma_ne_row25Gamma
    rw [row25Gamma_eq_neg_row24Gamma]
    exact hvalue
  · exact Subtype.ext hrow25

@[simp]
theorem alternatingSixThreeAmbientAlphaTwoRow24_fixed :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row24, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row24, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row24, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 10 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation,
      r, AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaTwo r
  have hcentral :
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 1) =
        (-10 : ℂ) := by
    dsimp only [s]
    simpa [r, AlternatingSixAmbientOrdinaryRow.dimension] using
      ambientAlphaTwo_orderTwo_centralValue r (by rfl)
  rcases
      pPrimeRow_eq_row24_or_row25_of_dimension_centralValue
        s hdimension hcentral with hrow24 | hrow25
  · exact Subtype.ext hrow24
  · exfalso
    have hvalue :=
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation_values_classRepresentative
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r 9
    change
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 9) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character .row24).values
          (alternatingSixUniversalCoverClassRepresentative
            (alternatingSixAlphaTwoConjugacyClassPermutation.symm 9))
      at hvalue
    rw [hrow25, completed_row25_value,
      completed_row24_value,
      alphaTwoClassPermutation_symm_eq_vector] at hvalue
    change
      alternatingSixAmbientRow25Gamma =
        alternatingSixAmbientRow24Gamma at hvalue
    exact row24Gamma_ne_row25Gamma hvalue.symm

@[simp]
theorem alternatingSixThreeAmbientAlphaOneRow25_eq_row24 :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row25, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row24, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row25, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 10 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaOneRowPermutation,
      r, AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaOne r
  have hcentral :
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 1) =
        (-10 : ℂ) := by
    dsimp only [s]
    simpa [r, AlternatingSixAmbientOrdinaryRow.dimension] using
      ambientAlphaOne_orderTwo_centralValue r (by rfl)
  rcases
      pPrimeRow_eq_row24_or_row25_of_dimension_centralValue
        s hdimension hcentral with hrow24 | hrow25
  · exact Subtype.ext hrow24
  · exfalso
    have hs :
        s =
          alternatingSixAmbientPPrimeAlphaOneRowPermutation
            alternatingSixAmbientOrdinaryCharacterTableCertificate 3
            (⟨.row24, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) := by
      calc
        s = (⟨.row25, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) :=
          Subtype.ext hrow25
        _ =
            alternatingSixAmbientPPrimeAlphaOneRowPermutation
              alternatingSixAmbientOrdinaryCharacterTableCertificate 3
              (⟨.row24, by decide⟩ :
                AlternatingSixAmbientPPrimeRowIndex 3) :=
          alternatingSixThreeAmbientAlphaOneRow24_eq_row25.symm
    have hsource :=
      (alternatingSixAmbientPPrimeAlphaOneRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate 3).injective hs
    have hval := congrArg Subtype.val hsource
    simp [r] at hval

@[simp]
theorem alternatingSixThreeAmbientAlphaTwoRow25_fixed :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row25, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row25, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row25, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 10 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation,
      r, AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaTwo r
  have hcentral :
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 1) =
        (-10 : ℂ) := by
    dsimp only [s]
    simpa [r, AlternatingSixAmbientOrdinaryRow.dimension] using
      ambientAlphaTwo_orderTwo_centralValue r (by rfl)
  rcases
      pPrimeRow_eq_row24_or_row25_of_dimension_centralValue
        s hdimension hcentral with hrow24 | hrow25
  · exfalso
    have hs :
        s =
          alternatingSixAmbientPPrimeAlphaTwoRowPermutation
            alternatingSixAmbientOrdinaryCharacterTableCertificate 3
            (⟨.row24, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) := by
      calc
        s = (⟨.row24, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) :=
          Subtype.ext hrow24
        _ =
            alternatingSixAmbientPPrimeAlphaTwoRowPermutation
              alternatingSixAmbientOrdinaryCharacterTableCertificate 3
              (⟨.row24, by decide⟩ :
                AlternatingSixAmbientPPrimeRowIndex 3) :=
          alternatingSixThreeAmbientAlphaTwoRow24_fixed.symm
    have hsource :=
      (alternatingSixAmbientPPrimeAlphaTwoRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate 3).injective hs
    have hval := congrArg Subtype.val hsource
    simp [r] at hval
  · exact Subtype.ext hrow25

@[simp]
theorem alternatingSixThreeAmbientAlphaTwoRow16_fixed :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row16, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row16, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row16, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 8 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation,
      r, AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaTwo r
  have hcentral :
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 1) =
        (8 : ℂ) := by
    dsimp only [s]
    simpa [r, AlternatingSixAmbientOrdinaryRow.dimension] using
      ambientAlphaTwo_trivial_centralValue r (by rfl)
  rcases
      pPrimeRow_eq_row16_or_row17_of_dimension_centralValue
        s hdimension hcentral with hrow16 | hrow17
  · exact Subtype.ext hrow16
  · exfalso
    have hvalue :=
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation_values_classRepresentative
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r 15
    change
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 15) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character .row16).values
          (alternatingSixUniversalCoverClassRepresentative
            (alternatingSixAlphaTwoConjugacyClassPermutation.symm 15))
      at hvalue
    rw [hrow17, completed_row17_value_fifteen,
      alphaTwoClassPermutation_symm_eq_vector] at hvalue
    change
      alternatingSixCyclotomicValue
          [(1, 8), (1, 12), (-1, 28)] =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character .row16).values
          (alternatingSixUniversalCoverClassRepresentative 19) at hvalue
    rw [completed_row16_value_nineteen] at hvalue
    exact row16FifteenValue_ne_row17FifteenValue hvalue.symm

@[simp]
theorem alternatingSixThreeAmbientAlphaTwoRow17_fixed :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row17, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row17, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row17, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 8 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation,
      r, AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaTwo r
  have hcentral :
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 1) =
        (8 : ℂ) := by
    dsimp only [s]
    simpa [r, AlternatingSixAmbientOrdinaryRow.dimension] using
      ambientAlphaTwo_trivial_centralValue r (by rfl)
  rcases
      pPrimeRow_eq_row16_or_row17_of_dimension_centralValue
        s hdimension hcentral with hrow16 | hrow17
  · exfalso
    have hs :
        s =
          alternatingSixAmbientPPrimeAlphaTwoRowPermutation
            alternatingSixAmbientOrdinaryCharacterTableCertificate 3
            (⟨.row16, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) := by
      calc
        s = (⟨.row16, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) :=
          Subtype.ext hrow16
        _ =
            alternatingSixAmbientPPrimeAlphaTwoRowPermutation
              alternatingSixAmbientOrdinaryCharacterTableCertificate 3
              (⟨.row16, by decide⟩ :
                AlternatingSixAmbientPPrimeRowIndex 3) :=
          alternatingSixThreeAmbientAlphaTwoRow16_fixed.symm
    have hsource :=
      (alternatingSixAmbientPPrimeAlphaTwoRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate 3).injective hs
    have hval := congrArg Subtype.val hsource
    simp [r] at hval
  · exact Subtype.ext hrow17

@[simp]
theorem alternatingSixThreeAmbientAlphaOneRow16_eq_row17 :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row16, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row17, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row16, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 8 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaOneRowPermutation,
      r,
      AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaOne r
  have hcentral :
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 1) =
        (8 : ℂ) := by
    dsimp only [s]
    simpa [r, AlternatingSixAmbientOrdinaryRow.dimension] using
      ambientAlphaOne_trivial_centralValue r (by rfl)
  rcases
      pPrimeRow_eq_row16_or_row17_of_dimension_centralValue
        s hdimension hcentral with hrow16 | hrow17
  · exfalso
    have hvalue :=
      alternatingSixAmbientPPrimeAlphaOneRowPermutation_values_classRepresentative
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r 15
    change
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 15) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character .row16).values
          (alternatingSixUniversalCoverClassRepresentative
            (alternatingSixAlphaOneConjugacyClassPermutation.symm 15))
      at hvalue
    rw [
      hrow16,
      completed_row16_value_fifteen,
      alphaOneClassPermutation_symm_eq_vector
    ] at hvalue
    change
      alternatingSixCyclotomicValue
          [(1, 0), (-1, 8), (-1, 12), (1, 28)] =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character .row16).values
          (alternatingSixUniversalCoverClassRepresentative 21)
      at hvalue
    rw [completed_row16_value_twentyOne] at hvalue
    exact row16FifteenValue_ne_row17FifteenValue hvalue
  · exact Subtype.ext hrow17

@[simp]
theorem alternatingSixThreeAmbientAlphaOneRow17_eq_row16 :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row17, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row16, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row17, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 8 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaOneRowPermutation,
      r,
      AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaOne r
  have hcentral :
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 1) =
        (8 : ℂ) := by
    dsimp only [s]
    simpa [r, AlternatingSixAmbientOrdinaryRow.dimension] using
      ambientAlphaOne_trivial_centralValue r (by rfl)
  rcases
      pPrimeRow_eq_row16_or_row17_of_dimension_centralValue
        s hdimension hcentral with hrow16 | hrow17
  · exact Subtype.ext hrow16
  · exfalso
    have hs :
        s =
          alternatingSixAmbientPPrimeAlphaOneRowPermutation
            alternatingSixAmbientOrdinaryCharacterTableCertificate 3
            (⟨.row16, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) := by
      calc
        s = (⟨.row17, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) :=
          Subtype.ext hrow17
        _ =
            alternatingSixAmbientPPrimeAlphaOneRowPermutation
              alternatingSixAmbientOrdinaryCharacterTableCertificate 3
              (⟨.row16, by decide⟩ :
                AlternatingSixAmbientPPrimeRowIndex 3) :=
          alternatingSixThreeAmbientAlphaOneRow16_eq_row17.symm
    have hsource :=
      (alternatingSixAmbientPPrimeAlphaOneRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate 3).injective hs
    have hval := congrArg Subtype.val hsource
    simp [r] at hval

@[simp]
theorem alternatingSixThreeAmbientAlphaOneRow06_fixed :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row06, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row06, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row06, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 4 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaOneRowPermutation,
      r, AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaOne r
  rcases
      pPrimeRow_eq_row06_or_row07_of_dimension s hdimension with
    hrow06 | hrow07
  · exact Subtype.ext hrow06
  · exfalso
    have hvalue :=
      alternatingSixAmbientPPrimeAlphaOneRowPermutation_values_classRepresentative
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r 28
    change
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 28) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character .row06).values
          (alternatingSixUniversalCoverClassRepresentative
            (alternatingSixAlphaOneConjugacyClassPermutation.symm 28))
      at hvalue
    rw [hrow07, completed_row07_value_twentyEight,
      alphaOneClassPermutation_symm_eq_vector] at hvalue
    change
      (-2 : ℂ) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character .row06).values
          (alternatingSixUniversalCoverClassRepresentative 28) at hvalue
    rw [completed_row06_value_twentyEight] at hvalue
    norm_num at hvalue

@[simp]
theorem alternatingSixThreeAmbientAlphaOneRow07_fixed :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row07, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row07, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row07, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 4 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaOneRowPermutation,
      r, AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaOne r
  rcases
      pPrimeRow_eq_row06_or_row07_of_dimension s hdimension with
    hrow06 | hrow07
  · exfalso
    have hs :
        s =
          alternatingSixAmbientPPrimeAlphaOneRowPermutation
            alternatingSixAmbientOrdinaryCharacterTableCertificate 3
            (⟨.row06, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) := by
      calc
        s = (⟨.row06, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) :=
          Subtype.ext hrow06
        _ =
            alternatingSixAmbientPPrimeAlphaOneRowPermutation
              alternatingSixAmbientOrdinaryCharacterTableCertificate 3
              (⟨.row06, by decide⟩ :
                AlternatingSixAmbientPPrimeRowIndex 3) :=
          alternatingSixThreeAmbientAlphaOneRow06_fixed.symm
    have hsource :=
      (alternatingSixAmbientPPrimeAlphaOneRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate 3).injective hs
    have hval := congrArg Subtype.val hsource
    simp [r] at hval
  · exact Subtype.ext hrow07

@[simp]
theorem alternatingSixThreeAmbientAlphaOneRow08_fixed :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row08, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row08, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row08, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 5 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaOneRowPermutation,
      r, AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaOne r
  rcases
      pPrimeRow_eq_row08_or_row09_of_dimension s hdimension with
    hrow08 | hrow09
  · exact Subtype.ext hrow08
  · exfalso
    have hvalue :=
      alternatingSixAmbientPPrimeAlphaOneRowPermutation_values_classRepresentative
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r 28
    change
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 28) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character .row08).values
          (alternatingSixUniversalCoverClassRepresentative
            (alternatingSixAlphaOneConjugacyClassPermutation.symm 28))
      at hvalue
    rw [hrow09, completed_row09_value_twentyEight,
      alphaOneClassPermutation_symm_eq_vector] at hvalue
    change
      (-1 : ℂ) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character .row08).values
          (alternatingSixUniversalCoverClassRepresentative 28) at hvalue
    rw [completed_row08_value_twentyEight] at hvalue
    norm_num at hvalue

@[simp]
theorem alternatingSixThreeAmbientAlphaOneRow09_fixed :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row09, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row09, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row09, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 5 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaOneRowPermutation,
      r, AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaOne r
  rcases
      pPrimeRow_eq_row08_or_row09_of_dimension s hdimension with
    hrow08 | hrow09
  · exfalso
    have hs :
        s =
          alternatingSixAmbientPPrimeAlphaOneRowPermutation
            alternatingSixAmbientOrdinaryCharacterTableCertificate 3
            (⟨.row08, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) := by
      calc
        s = (⟨.row08, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) :=
          Subtype.ext hrow08
        _ =
            alternatingSixAmbientPPrimeAlphaOneRowPermutation
              alternatingSixAmbientOrdinaryCharacterTableCertificate 3
              (⟨.row08, by decide⟩ :
                AlternatingSixAmbientPPrimeRowIndex 3) :=
          alternatingSixThreeAmbientAlphaOneRow08_fixed.symm
    have hsource :=
      (alternatingSixAmbientPPrimeAlphaOneRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate 3).injective hs
    have hval := congrArg Subtype.val hsource
    simp [r] at hval
  · exact Subtype.ext hrow09

@[simp]
theorem alternatingSixThreeAmbientAlphaTwoRow06_eq_row07 :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row06, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row07, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row06, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 4 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation,
      r,
      AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaTwo r
  rcases
      pPrimeRow_eq_row06_or_row07_of_dimension s hdimension with
    hrow06 | hrow07
  · exfalso
    have hvalue :=
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation_values_classRepresentative
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r 28
    change
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 28) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character .row06).values
          (alternatingSixUniversalCoverClassRepresentative
            (alternatingSixAlphaTwoConjugacyClassPermutation.symm 28))
      at hvalue
    rw [
      hrow06,
      completed_row06_value_twentyEight,
      alphaTwoClassPermutation_symm_eq_vector
    ] at hvalue
    change
      (1 : ℂ) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character .row06).values
          (alternatingSixUniversalCoverClassRepresentative 30)
      at hvalue
    rw [completed_row06_value_thirty] at hvalue
    norm_num at hvalue
  · exact Subtype.ext hrow07

@[simp]
theorem alternatingSixThreeAmbientAlphaTwoRow07_eq_row06 :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row07, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row06, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row07, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 4 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation,
      r,
      AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaTwo r
  rcases
      pPrimeRow_eq_row06_or_row07_of_dimension s hdimension with
    hrow06 | hrow07
  · exact Subtype.ext hrow06
  · exfalso
    have hs :
        s =
          alternatingSixAmbientPPrimeAlphaTwoRowPermutation
            alternatingSixAmbientOrdinaryCharacterTableCertificate 3
            (⟨.row06, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) := by
      calc
        s = (⟨.row07, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) :=
          Subtype.ext hrow07
        _ =
            alternatingSixAmbientPPrimeAlphaTwoRowPermutation
              alternatingSixAmbientOrdinaryCharacterTableCertificate 3
              (⟨.row06, by decide⟩ :
                AlternatingSixAmbientPPrimeRowIndex 3) :=
          alternatingSixThreeAmbientAlphaTwoRow06_eq_row07.symm
    have hsource :=
      (alternatingSixAmbientPPrimeAlphaTwoRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate 3).injective hs
    have hval := congrArg Subtype.val hsource
    simp [r] at hval

@[simp]
theorem alternatingSixThreeAmbientAlphaTwoRow08_eq_row09 :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row08, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row09, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row08, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 5 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation,
      r,
      AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaTwo r
  rcases
      pPrimeRow_eq_row08_or_row09_of_dimension s hdimension with
    hrow08 | hrow09
  · exfalso
    have hvalue :=
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation_values_classRepresentative
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r 28
    change
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character s.1).values
          (alternatingSixUniversalCoverClassRepresentative 28) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character .row08).values
          (alternatingSixUniversalCoverClassRepresentative
            (alternatingSixAlphaTwoConjugacyClassPermutation.symm 28))
      at hvalue
    rw [
      hrow08,
      completed_row08_value_twentyEight,
      alphaTwoClassPermutation_symm_eq_vector
    ] at hvalue
    change
      (2 : ℂ) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character .row08).values
          (alternatingSixUniversalCoverClassRepresentative 30)
      at hvalue
    rw [completed_row08_value_thirty] at hvalue
    norm_num at hvalue
  · exact Subtype.ext hrow09

@[simp]
theorem alternatingSixThreeAmbientAlphaTwoRow09_eq_row08 :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        (⟨.row09, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row08, by decide⟩ := by
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row09, by decide⟩
  let s :=
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3 r
  have hdimension : s.1.dimension = 5 := by
    dsimp only [s]
    simpa [
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation,
      r,
      AlternatingSixAmbientOrdinaryRow.dimension
    ] using
      alternatingSixAmbientPPrimeRowPermutation_dimension
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixUniversalCoverTransportedAlphaTwo r
  rcases
      pPrimeRow_eq_row08_or_row09_of_dimension s hdimension with
    hrow08 | hrow09
  · exact Subtype.ext hrow08
  · exfalso
    have hs :
        s =
          alternatingSixAmbientPPrimeAlphaTwoRowPermutation
            alternatingSixAmbientOrdinaryCharacterTableCertificate 3
            (⟨.row08, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) := by
      calc
        s = (⟨.row09, by decide⟩ :
              AlternatingSixAmbientPPrimeRowIndex 3) :=
          Subtype.ext hrow09
        _ =
            alternatingSixAmbientPPrimeAlphaTwoRowPermutation
              alternatingSixAmbientOrdinaryCharacterTableCertificate 3
              (⟨.row08, by decide⟩ :
                AlternatingSixAmbientPPrimeRowIndex 3) :=
          alternatingSixThreeAmbientAlphaTwoRow08_eq_row09.symm
    have hsource :=
      (alternatingSixAmbientPPrimeAlphaTwoRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate 3).injective hs
    have hval := congrArg Subtype.val hsource
    simp [r] at hval

/-! ### Exact six-position residual seams -/

/-- The six CT positions whose three paired constructed rows still lack
completed semantic value bridges. -/
def AlternatingSixThreeUnresolvedAmbientValuePosition
    (i : Fin 12) : Prop :=
  i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 7

/-- The complementary six positions are the two invariant singletons and
the two paired blocks settled by the completed class-value calculations. -/
def AlternatingSixThreeResolvedAmbientValuePosition
    (i : Fin 12) : Prop :=
  i = 0 ∨ i = 5 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11

theorem alternatingSixThree_unresolved_or_resolvedAmbientValuePosition
    (i : Fin 12) :
    AlternatingSixThreeUnresolvedAmbientValuePosition i ∨
      AlternatingSixThreeResolvedAmbientValuePosition i := by
  fin_cases i <;>
    simp [
      AlternatingSixThreeUnresolvedAmbientValuePosition,
      AlternatingSixThreeResolvedAmbientValuePosition
    ]

namespace AlternatingSixThreeCTblLibRowIdentification

variable
  (identification : AlternatingSixThreeCTblLibRowIdentification)

/-- First-generator bridge restricted to the exact six positions not yet
settled by invariant singleton or completed value-vector arguments. -/
def AmbientCorrectedAlphaOneBridgeOnUnresolvedValuePositions : Prop :=
  ∀ i : Fin 12,
    AlternatingSixThreeUnresolvedAmbientValuePosition i →
      alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 3)
          (identification.ambientPositionEquiv i) =
        identification.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne i)

/-- Second-generator bridge restricted to the exact six positions not yet
settled by invariant singleton or completed value-vector arguments. -/
def AmbientCorrectedAlphaTwoBridgeOnUnresolvedValuePositions : Prop :=
  ∀ i : Fin 12,
    AlternatingSixThreeUnresolvedAmbientValuePosition i →
      alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 3)
          (identification.ambientPositionEquiv i) =
        identification.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaTwo i)

end AlternatingSixThreeCTblLibRowIdentification

private theorem atlasAligned_ambientAlphaOneBridge_resolved
    (i : Fin 12)
    (hi : AlternatingSixThreeResolvedAmbientValuePosition i) :
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 3)
        (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
          |>.ambientPositionEquiv i) =
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne i)) := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.ambientCorrectedAlphaOneBridge_zero
          alternatingSixThreeAtlasAlignedCTblLibRowIdentification_hasTrivial
  · exact
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.ambientCorrectedAlphaOneBridge_five
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
            |>.hasSemanticAmbientRow23Position_of_signatureCompatible
              alternatingSixThreeAtlasAlignedAmbientPositionEquiv_signatureCompatible)
  all_goals
    simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification,
      alternatingSixThreeAtlasAlignedAmbientPositionEquiv,
      alternatingSixCTblLibThreePPrimeActionData
    ]

private theorem atlasAligned_ambientAlphaTwoBridge_resolved
    (i : Fin 12)
    (hi : AlternatingSixThreeResolvedAmbientValuePosition i) :
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 3)
        (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
          |>.ambientPositionEquiv i) =
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaTwo i)) := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.ambientCorrectedAlphaTwoBridge_zero
          alternatingSixThreeAtlasAlignedCTblLibRowIdentification_hasTrivial
  · exact
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.ambientCorrectedAlphaTwoBridge_five
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
            |>.hasSemanticAmbientRow23Position_of_signatureCompatible
              alternatingSixThreeAtlasAlignedAmbientPositionEquiv_signatureCompatible)
  all_goals
    simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification,
      alternatingSixThreeAtlasAlignedAmbientPositionEquiv,
      alternatingSixCTblLibThreePPrimeActionData
    ]

private theorem atlasAlignedAlternate_ambientAlphaOneBridge_resolved
    (i : Fin 12)
    (hi : AlternatingSixThreeResolvedAmbientValuePosition i) :
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 3)
        (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
          |>.ambientPositionEquiv i) =
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne i)) := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.ambientCorrectedAlphaOneBridge_zero
          alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate_hasTrivial
  · exact
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.ambientCorrectedAlphaOneBridge_five
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
            |>.hasSemanticAmbientRow23Position_of_signatureCompatible
              alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate_signatureCompatible)
  all_goals
    simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate,
      alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate,
      alternatingSixCTblLibThreePPrimeActionData
    ]

private theorem atlasAlignedAlternate_ambientAlphaTwoBridge_resolved
    (i : Fin 12)
    (hi : AlternatingSixThreeResolvedAmbientValuePosition i) :
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 3)
        (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
          |>.ambientPositionEquiv i) =
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaTwo i)) := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.ambientCorrectedAlphaTwoBridge_zero
          alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate_hasTrivial
  · exact
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.ambientCorrectedAlphaTwoBridge_five
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
            |>.hasSemanticAmbientRow23Position_of_signatureCompatible
              alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate_signatureCompatible)
  all_goals
    simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate,
      alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate,
      alternatingSixCTblLibThreePPrimeActionData
    ]

/-- For the first ATLAS-aligned orientation, the first full ambient bridge
is equivalent to the six positions occupied by rows 8/9, 16/17, and 6/7. -/
theorem
    alternatingSixThreeAtlasAligned_ambientAlphaOneBridge_iff_sixValuePositions :
    (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
      |>.AmbientCorrectedAlphaOneBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate) ↔
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.AmbientCorrectedAlphaOneBridgeOnUnresolvedValuePositions) := by
  constructor
  · intro h i _
    exact h i
  · intro h i
    rcases
        alternatingSixThree_unresolved_or_resolvedAmbientValuePosition i with
      hi | hi
    · exact h i hi
    · exact atlasAligned_ambientAlphaOneBridge_resolved i hi

/-- For the first ATLAS-aligned orientation, the second full ambient bridge
is equivalent to the same six unresolved positions. -/
theorem
    alternatingSixThreeAtlasAligned_ambientAlphaTwoBridge_iff_sixValuePositions :
    (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
      |>.AmbientCorrectedAlphaTwoBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate) ↔
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.AmbientCorrectedAlphaTwoBridgeOnUnresolvedValuePositions) := by
  constructor
  · intro h i _
    exact h i
  · intro h i
    rcases
        alternatingSixThree_unresolved_or_resolvedAmbientValuePosition i with
      hi | hi
    · exact h i hi
    · exact atlasAligned_ambientAlphaTwoBridge_resolved i hi

/-- Swapping the unresolved row-24/row-25 orientation does not change the
first generator's six-position residual seam. -/
theorem
    alternatingSixThreeAtlasAlignedAlternate_ambientAlphaOneBridge_iff_sixValuePositions :
    (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
      |>.AmbientCorrectedAlphaOneBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate) ↔
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.AmbientCorrectedAlphaOneBridgeOnUnresolvedValuePositions) := by
  constructor
  · intro h i _
    exact h i
  · intro h i
    rcases
        alternatingSixThree_unresolved_or_resolvedAmbientValuePosition i with
      hi | hi
    · exact h i hi
    · exact atlasAlignedAlternate_ambientAlphaOneBridge_resolved i hi

/-- Swapping the unresolved row-24/row-25 orientation does not change the
second generator's six-position residual seam. -/
theorem
    alternatingSixThreeAtlasAlignedAlternate_ambientAlphaTwoBridge_iff_sixValuePositions :
    (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
      |>.AmbientCorrectedAlphaTwoBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate) ↔
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.AmbientCorrectedAlphaTwoBridgeOnUnresolvedValuePositions) := by
  constructor
  · intro h i _
    exact h i
  · intro h i
    rcases
        alternatingSixThree_unresolved_or_resolvedAmbientValuePosition i with
      hi | hi
    · exact h i hi
    · exact atlasAlignedAlternate_ambientAlphaTwoBridge_resolved i hi

/-! ### Generator-specific last residual seams -/

/-- The two-position seam left for the first audited generator after the
separator-value calculation and before the final `AB²` trace calculation. -/
def AlternatingSixThreeAlphaOneRemainingAmbientValuePosition
    (i : Fin 12) : Prop :=
  i = 3 ∨ i = 4

/-- The four-position seam left for the second audited generator before the
final class-30 trace calculations. -/
def AlternatingSixThreeAlphaTwoRemainingAmbientValuePosition
    (i : Fin 12) : Prop :=
  i = 1 ∨ i = 2 ∨ i = 6 ∨ i = 7

private def AlternatingSixThreeAlphaOneResolvedAmbientValuePosition
    (i : Fin 12) : Prop :=
  i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
    i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11

private def AlternatingSixThreeAlphaTwoResolvedAmbientValuePosition
    (i : Fin 12) : Prop :=
  i = 0 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
    i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11

private theorem alternatingSixThree_alphaOneRemaining_or_resolved
    (i : Fin 12) :
    AlternatingSixThreeAlphaOneRemainingAmbientValuePosition i ∨
      AlternatingSixThreeAlphaOneResolvedAmbientValuePosition i := by
  fin_cases i <;>
    simp [
      AlternatingSixThreeAlphaOneRemainingAmbientValuePosition,
      AlternatingSixThreeAlphaOneResolvedAmbientValuePosition
    ]

private theorem alternatingSixThree_alphaTwoRemaining_or_resolved
    (i : Fin 12) :
    AlternatingSixThreeAlphaTwoRemainingAmbientValuePosition i ∨
      AlternatingSixThreeAlphaTwoResolvedAmbientValuePosition i := by
  fin_cases i <;>
    simp [
      AlternatingSixThreeAlphaTwoRemainingAmbientValuePosition,
      AlternatingSixThreeAlphaTwoResolvedAmbientValuePosition
    ]

namespace AlternatingSixThreeCTblLibRowIdentification

variable
  (identification : AlternatingSixThreeCTblLibRowIdentification)

/-- Exact first-generator bridge restricted to the unresolved row16/17
pair. -/
def AmbientCorrectedAlphaOneBridgeOnRemainingValuePositions : Prop :=
  ∀ i : Fin 12,
    AlternatingSixThreeAlphaOneRemainingAmbientValuePosition i →
      alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 3)
          (identification.ambientPositionEquiv i) =
        identification.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne i)

/-- Exact second-generator bridge restricted to the unresolved row08/09
and row06/07 pairs. -/
def AmbientCorrectedAlphaTwoBridgeOnRemainingValuePositions : Prop :=
  ∀ i : Fin 12,
    AlternatingSixThreeAlphaTwoRemainingAmbientValuePosition i →
      alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 3)
          (identification.ambientPositionEquiv i) =
        identification.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaTwo i)

end AlternatingSixThreeCTblLibRowIdentification

private theorem atlasAligned_ambientAlphaOneBridge_resolvedFinal
    (i : Fin 12)
    (hi : AlternatingSixThreeAlphaOneResolvedAmbientValuePosition i) :
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 3)
        (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
          |>.ambientPositionEquiv i) =
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne i)) := by
  rcases hi with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.ambientCorrectedAlphaOneBridge_zero
          alternatingSixThreeAtlasAlignedCTblLibRowIdentification_hasTrivial
  · simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification,
      alternatingSixThreeAtlasAlignedAmbientPositionEquiv,
      alternatingSixCTblLibThreePPrimeActionData
    ]
  · simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification,
      alternatingSixThreeAtlasAlignedAmbientPositionEquiv,
      alternatingSixCTblLibThreePPrimeActionData
    ]
  · exact
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.ambientCorrectedAlphaOneBridge_five
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
            |>.hasSemanticAmbientRow23Position_of_signatureCompatible
              alternatingSixThreeAtlasAlignedAmbientPositionEquiv_signatureCompatible)
  all_goals
    simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification,
      alternatingSixThreeAtlasAlignedAmbientPositionEquiv,
      alternatingSixCTblLibThreePPrimeActionData
    ]

private theorem atlasAligned_ambientAlphaTwoBridge_resolvedFinal
    (i : Fin 12)
    (hi : AlternatingSixThreeAlphaTwoResolvedAmbientValuePosition i) :
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 3)
        (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
          |>.ambientPositionEquiv i) =
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaTwo i)) := by
  rcases hi with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.ambientCorrectedAlphaTwoBridge_zero
          alternatingSixThreeAtlasAlignedCTblLibRowIdentification_hasTrivial
  · simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification,
      alternatingSixThreeAtlasAlignedAmbientPositionEquiv,
      alternatingSixCTblLibThreePPrimeActionData
    ]
  · simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification,
      alternatingSixThreeAtlasAlignedAmbientPositionEquiv,
      alternatingSixCTblLibThreePPrimeActionData
    ]
  · exact
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.ambientCorrectedAlphaTwoBridge_five
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
            |>.hasSemanticAmbientRow23Position_of_signatureCompatible
              alternatingSixThreeAtlasAlignedAmbientPositionEquiv_signatureCompatible)
  all_goals
    simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification,
      alternatingSixThreeAtlasAlignedAmbientPositionEquiv,
      alternatingSixCTblLibThreePPrimeActionData
    ]

private theorem atlasAlignedAlternate_ambientAlphaOneBridge_resolvedFinal
    (i : Fin 12)
    (hi : AlternatingSixThreeAlphaOneResolvedAmbientValuePosition i) :
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 3)
        (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
          |>.ambientPositionEquiv i) =
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne i)) := by
  rcases hi with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.ambientCorrectedAlphaOneBridge_zero
          alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate_hasTrivial
  · simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate,
      alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate,
      alternatingSixCTblLibThreePPrimeActionData
    ]
  · simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate,
      alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate,
      alternatingSixCTblLibThreePPrimeActionData
    ]
  · exact
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.ambientCorrectedAlphaOneBridge_five
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
            |>.hasSemanticAmbientRow23Position_of_signatureCompatible
              alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate_signatureCompatible)
  all_goals
    simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate,
      alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate,
      alternatingSixCTblLibThreePPrimeActionData
    ]

private theorem atlasAlignedAlternate_ambientAlphaTwoBridge_resolvedFinal
    (i : Fin 12)
    (hi : AlternatingSixThreeAlphaTwoResolvedAmbientValuePosition i) :
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 3)
        (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
          |>.ambientPositionEquiv i) =
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaTwo i)) := by
  rcases hi with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.ambientCorrectedAlphaTwoBridge_zero
          alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate_hasTrivial
  · simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate,
      alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate,
      alternatingSixCTblLibThreePPrimeActionData
    ]
  · simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate,
      alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate,
      alternatingSixCTblLibThreePPrimeActionData
    ]
  · exact
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.ambientCorrectedAlphaTwoBridge_five
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
            |>.hasSemanticAmbientRow23Position_of_signatureCompatible
              alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate_signatureCompatible)
  all_goals
    simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate,
      alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate,
      alternatingSixCTblLibThreePPrimeActionData
    ]

/-- Intermediate exact reduction of the first ATLAS-aligned first-generator
bridge to the row16/17 position equalities. -/
theorem
    alternatingSixThreeAtlasAligned_ambientAlphaOneBridge_iff_twoRemainingValuePositions :
    (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
      |>.AmbientCorrectedAlphaOneBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate) ↔
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.AmbientCorrectedAlphaOneBridgeOnRemainingValuePositions) := by
  constructor
  · intro h i _
    exact h i
  · intro h i
    rcases alternatingSixThree_alphaOneRemaining_or_resolved i with hi | hi
    · exact h i hi
    · exact atlasAligned_ambientAlphaOneBridge_resolvedFinal i hi

/-- Intermediate exact reduction of the first ATLAS-aligned
second-generator bridge to the row08/09 and row06/07 equalities. -/
theorem
    alternatingSixThreeAtlasAligned_ambientAlphaTwoBridge_iff_fourRemainingValuePositions :
    (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
      |>.AmbientCorrectedAlphaTwoBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate) ↔
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.AmbientCorrectedAlphaTwoBridgeOnRemainingValuePositions) := by
  constructor
  · intro h i _
    exact h i
  · intro h i
    rcases alternatingSixThree_alphaTwoRemaining_or_resolved i with hi | hi
    · exact h i hi
    · exact atlasAligned_ambientAlphaTwoBridge_resolvedFinal i hi

/-- The alternate row24/25 orientation has the same intermediate
two-position first-generator reduction. -/
theorem
    alternatingSixThreeAtlasAlignedAlternate_ambientAlphaOneBridge_iff_twoRemainingValuePositions :
    (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
      |>.AmbientCorrectedAlphaOneBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate) ↔
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.AmbientCorrectedAlphaOneBridgeOnRemainingValuePositions) := by
  constructor
  · intro h i _
    exact h i
  · intro h i
    rcases alternatingSixThree_alphaOneRemaining_or_resolved i with hi | hi
    · exact h i hi
    · exact atlasAlignedAlternate_ambientAlphaOneBridge_resolvedFinal i hi

/-- The alternate row24/25 orientation has the same intermediate
four-position second-generator reduction. -/
theorem
    alternatingSixThreeAtlasAlignedAlternate_ambientAlphaTwoBridge_iff_fourRemainingValuePositions :
    (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
      |>.AmbientCorrectedAlphaTwoBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate) ↔
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.AmbientCorrectedAlphaTwoBridgeOnRemainingValuePositions) := by
  constructor
  · intro h i _
    exact h i
  · intro h i
    rcases alternatingSixThree_alphaTwoRemaining_or_resolved i with hi | hi
    · exact h i hi
    · exact atlasAlignedAlternate_ambientAlphaTwoBridge_resolvedFinal i hi

/-- The `AB²` trace calculation discharges the last two positions in the
first ATLAS-aligned first-generator bridge. -/
theorem
    alternatingSixThreeAtlasAligned_ambientAlphaOneBridge :
    alternatingSixThreeAtlasAlignedCTblLibRowIdentification
      |>.AmbientCorrectedAlphaOneBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate := by
  rw [
    alternatingSixThreeAtlasAligned_ambientAlphaOneBridge_iff_twoRemainingValuePositions
  ]
  intro i hi
  rcases hi with rfl | rfl <;>
    simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification,
      alternatingSixThreeAtlasAlignedAmbientPositionEquiv,
      alternatingSixCTblLibThreePPrimeActionData
    ]

/-- The alternate row24/25 orientation satisfies the same complete
first-generator bridge. -/
theorem
    alternatingSixThreeAtlasAlignedAlternate_ambientAlphaOneBridge :
    alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
      |>.AmbientCorrectedAlphaOneBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate := by
  rw [
    alternatingSixThreeAtlasAlignedAlternate_ambientAlphaOneBridge_iff_twoRemainingValuePositions
  ]
  intro i hi
  rcases hi with rfl | rfl <;>
    simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate,
      alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate,
      alternatingSixCTblLibThreePPrimeActionData
    ]

/-- The class-30 trace calculations discharge the last four positions in
the first ATLAS-aligned second-generator bridge. -/
theorem
    alternatingSixThreeAtlasAligned_ambientAlphaTwoBridge :
    alternatingSixThreeAtlasAlignedCTblLibRowIdentification
      |>.AmbientCorrectedAlphaTwoBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate := by
  rw [
    alternatingSixThreeAtlasAligned_ambientAlphaTwoBridge_iff_fourRemainingValuePositions
  ]
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification,
      alternatingSixThreeAtlasAlignedAmbientPositionEquiv,
      alternatingSixCTblLibThreePPrimeActionData
    ]

/-- The alternate row24/25 orientation satisfies the same complete
second-generator bridge. -/
theorem
    alternatingSixThreeAtlasAlignedAlternate_ambientAlphaTwoBridge :
    alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
      |>.AmbientCorrectedAlphaTwoBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate := by
  rw [
    alternatingSixThreeAtlasAlignedAlternate_ambientAlphaTwoBridge_iff_fourRemainingValuePositions
  ]
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate,
      alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate,
      alternatingSixCTblLibThreePPrimeActionData
    ]

end InductiveMcKay
end McKayConjecture
