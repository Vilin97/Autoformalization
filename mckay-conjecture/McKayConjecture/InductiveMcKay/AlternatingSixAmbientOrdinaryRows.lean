/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern

/-!
# Ordinary character-row indices for the sixfold cover of `A₆`

The ordinary character table of the canonical sixfold cover has thirty-one
rows.  Dixon's construction labels twenty-seven of the matrix rows by their
ordinary table positions; the four degree-twelve rows use the Galois powers
of the sparse characteristic-zero ATLAS representation.

This file records only the finite dependent index and its dimensions.  It
does not assert irreducibility or completeness.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- The thirty-one rows in the generated ordinary matrix corpus. -/
inductive AlternatingSixAmbientOrdinaryRow
  | row01 | row02 | row03 | row04 | row05
  | row06 | row07 | row08 | row09 | row10
  | row11 | row12 | row13 | row14 | row15
  | row16 | row17 | row18 | row19 | row20
  | row21 | row22 | row23 | row24 | row25
  | row30 | row31
  | atlasTwelvePowerOne
  | atlasTwelvePowerTwo
  | atlasTwelvePowerSeven
  | atlasTwelvePowerEleven
  deriving DecidableEq

namespace AlternatingSixAmbientOrdinaryRow

/-- Numeric position in the generated thirty-one-row corpus. -/
def index : AlternatingSixAmbientOrdinaryRow → Fin 31
  | .row01 => 0
  | .row02 => 1
  | .row03 => 2
  | .row04 => 3
  | .row05 => 4
  | .row06 => 5
  | .row07 => 6
  | .row08 => 7
  | .row09 => 8
  | .row10 => 9
  | .row11 => 10
  | .row12 => 11
  | .row13 => 12
  | .row14 => 13
  | .row15 => 14
  | .row16 => 15
  | .row17 => 16
  | .row18 => 17
  | .row19 => 18
  | .row20 => 19
  | .row21 => 20
  | .row22 => 21
  | .row23 => 22
  | .row24 => 23
  | .row25 => 24
  | .row30 => 25
  | .row31 => 26
  | .atlasTwelvePowerOne => 27
  | .atlasTwelvePowerTwo => 28
  | .atlasTwelvePowerSeven => 29
  | .atlasTwelvePowerEleven => 30

/-- The generated row at a numeric position. -/
def ofIndex : Fin 31 → AlternatingSixAmbientOrdinaryRow :=
  ![.row01, .row02, .row03, .row04, .row05,
    .row06, .row07, .row08, .row09, .row10,
    .row11, .row12, .row13, .row14, .row15,
    .row16, .row17, .row18, .row19, .row20,
    .row21, .row22, .row23, .row24, .row25,
    .row30, .row31, .atlasTwelvePowerOne,
    .atlasTwelvePowerTwo, .atlasTwelvePowerSeven,
    .atlasTwelvePowerEleven]

/-- The named ordinary rows are canonically equivalent to `Fin 31`. -/
def equivFin : AlternatingSixAmbientOrdinaryRow ≃ Fin 31 where
  toFun := index
  invFun := ofIndex
  left_inv row := by cases row <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype AlternatingSixAmbientOrdinaryRow :=
  Fintype.ofEquiv (Fin 31) equivFin.symm

@[simp]
theorem natCard :
    Nat.card AlternatingSixAmbientOrdinaryRow = 31 := by
  rw [Nat.card_congr equivFin, Nat.card_fin]

/-- The degree, and hence matrix dimension, of an ordinary row. -/
def dimension : AlternatingSixAmbientOrdinaryRow → ℕ
  | .row01 => 1
  | .row02 | .row03 | .row04 | .row05 => 3
  | .row06 | .row07 => 4
  | .row08 | .row09 => 5
  | .row10 | .row11 | .row12 | .row13 | .row14 | .row15 => 6
  | .row16 | .row17 | .row18 | .row19 => 8
  | .row20 | .row21 | .row22 => 9
  | .row23 | .row24 | .row25 => 10
  | .row30 | .row31 => 15
  | .atlasTwelvePowerOne | .atlasTwelvePowerTwo
  | .atlasTwelvePowerSeven | .atlasTwelvePowerEleven => 12

/-- Every ordinary matrix row has positive dimension. -/
theorem dimension_pos (row : AlternatingSixAmbientOrdinaryRow) :
    0 < row.dimension := by
  cases row <;> decide

/-- Central-scalar pattern of an ordinary matrix row. -/
def scalarPattern :
    AlternatingSixAmbientOrdinaryRow →
      AlternatingSixAmbientScalarPattern
  | .row01 | .row08 | .row09 | .row16 | .row17
  | .row20 | .row23 => .trivial
  | .row02 | .row03 | .row10 | .row21 | .row30 =>
      .orderThreePositive
  | .row04 | .row05 | .row11 | .row22 | .row31 =>
      .orderThreeNegative
  | .row06 | .row07 | .row18 | .row19 | .row24
  | .row25 => .orderTwo
  | .row12 | .row13 | .atlasTwelvePowerOne
  | .atlasTwelvePowerSeven => .orderSixPositive
  | .row14 | .row15 | .atlasTwelvePowerTwo
  | .atlasTwelvePowerEleven => .orderSixNegative

end AlternatingSixAmbientOrdinaryRow

/-- The exact presentation certificate required at one ordinary row. -/
abbrev AlternatingSixAmbientOrdinaryMatrixRowCertificate
    (row : AlternatingSixAmbientOrdinaryRow) :=
  AlternatingSixSchurMatrixRowCertificate (Fin row.dimension)

/-- Exact generator matrices and presentation proofs for all ordinary rows. -/
structure AlternatingSixAmbientOrdinaryRelationTableCertificate where
  /-- The relation-checked matrix row at every generated index. -/
  row :
    ∀ row : AlternatingSixAmbientOrdinaryRow,
      AlternatingSixAmbientOrdinaryMatrixRowCertificate row

namespace AlternatingSixAmbientOrdinaryRelationTableCertificate

variable (T : AlternatingSixAmbientOrdinaryRelationTableCertificate)

/-- The canonical-cover representation afforded by an ordinary row. -/
def universalCoverRepresentation
    (row : AlternatingSixAmbientOrdinaryRow) :
    Representation ℂ GroupTheory.AlternatingSixUniversalCover
      (Fin row.dimension → ℂ) :=
  (T.row row).universalCoverRepresentation

end AlternatingSixAmbientOrdinaryRelationTableCertificate
end InductiveMcKay
end McKayConjecture
