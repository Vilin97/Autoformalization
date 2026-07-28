/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientMatrixRepresentation

/-!
# Row indices for the ambient `5'`-table of `6.A₆`

The ordinary table of the sixfold cover has exactly twenty-four rows of
degree prime to five.  The GAP/Dixon matrix calculation labels twenty of
them by ordinary table indices and four degree-twelve Galois conjugates by
their ATLAS exponents.

This file fixes a typed index for those rows and the dependent completion
interface for their matrix-relation certificates.  The row dimension is part
of the index, so matrices of different sizes can coexist in one table without
casts or an artificially large common representation space.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- The twenty-four ambient irreducible-character rows of degree prime to
five in the fixed `6.A₆` calculation. -/
inductive AlternatingSixFiveAmbientRow
  | row01
  | row02
  | row03
  | row04
  | row05
  | row06
  | row07
  | row10
  | row11
  | row12
  | row13
  | row14
  | row15
  | row16
  | row17
  | row18
  | row19
  | row20
  | row21
  | row22
  | atlasTwelveOne
  | atlasTwelveTwo
  | atlasTwelveSeven
  | atlasTwelveEleven
  deriving DecidableEq

namespace AlternatingSixFiveAmbientRow

/-- Numeric position of an ambient row in the fixed twenty-four-row list. -/
def index : AlternatingSixFiveAmbientRow → Fin 24
  | .row01 => 0
  | .row02 => 1
  | .row03 => 2
  | .row04 => 3
  | .row05 => 4
  | .row06 => 5
  | .row07 => 6
  | .row10 => 7
  | .row11 => 8
  | .row12 => 9
  | .row13 => 10
  | .row14 => 11
  | .row15 => 12
  | .row16 => 13
  | .row17 => 14
  | .row18 => 15
  | .row19 => 16
  | .row20 => 17
  | .row21 => 18
  | .row22 => 19
  | .atlasTwelveOne => 20
  | .atlasTwelveTwo => 21
  | .atlasTwelveSeven => 22
  | .atlasTwelveEleven => 23

/-- The ambient row at a numeric position in the fixed list. -/
def ofIndex : Fin 24 → AlternatingSixFiveAmbientRow :=
  ![.row01, .row02, .row03, .row04, .row05, .row06,
    .row07, .row10, .row11, .row12, .row13, .row14,
    .row15, .row16, .row17, .row18, .row19, .row20,
    .row21, .row22, .atlasTwelveOne, .atlasTwelveTwo,
    .atlasTwelveSeven, .atlasTwelveEleven]

/-- The named ambient rows are canonically equivalent to `Fin 24`. -/
def equivFin : AlternatingSixFiveAmbientRow ≃ Fin 24 where
  toFun := index
  invFun := ofIndex
  left_inv r := by cases r <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype AlternatingSixFiveAmbientRow :=
  Fintype.ofEquiv (Fin 24) equivFin.symm

/-- There are exactly twenty-four indexed ambient rows. -/
@[simp]
theorem natCard :
    Nat.card AlternatingSixFiveAmbientRow = 24 := by
  rw [Nat.card_congr equivFin, Nat.card_fin]

/-- The degree, and hence matrix dimension, of an ambient row. -/
def dimension : AlternatingSixFiveAmbientRow → ℕ
  | .row01 => 1
  | .row02 | .row03 | .row04 | .row05 => 3
  | .row06 | .row07 => 4
  | .row10 | .row11 | .row12 | .row13 | .row14 | .row15 => 6
  | .row16 | .row17 | .row18 | .row19 => 8
  | .row20 | .row21 | .row22 => 9
  | .atlasTwelveOne | .atlasTwelveTwo
  | .atlasTwelveSeven | .atlasTwelveEleven => 12

/-- Every indexed row has degree prime to five. -/
theorem five_not_dvd_dimension
    (r : AlternatingSixFiveAmbientRow) :
    ¬5 ∣ r.dimension := by
  cases r <;> norm_num [dimension]

end AlternatingSixFiveAmbientRow

/-- The exact presentation-relation certificate required at one indexed
ambient row. -/
abbrev AlternatingSixFiveAmbientMatrixRowCertificate
    (r : AlternatingSixFiveAmbientRow) :=
  AlternatingSixSchurMatrixRowCertificate (Fin r.dimension)

/-- Completion of the matrix-relation stage for all twenty-four ambient
`5'`-rows.  Generated relation files supply the fields of this structure one
row at a time. -/
structure AlternatingSixFiveAmbientRelationTableCertificate where
  /-- The exact generator matrices and presentation proof at every row. -/
  row :
    ∀ r : AlternatingSixFiveAmbientRow,
      AlternatingSixFiveAmbientMatrixRowCertificate r

namespace AlternatingSixFiveAmbientRelationTableCertificate

variable (T : AlternatingSixFiveAmbientRelationTableCertificate)

/-- The canonical-cover representation afforded by a completed relation
table row. -/
def universalCoverRepresentation
    (r : AlternatingSixFiveAmbientRow) :
    Representation ℂ GroupTheory.AlternatingSixUniversalCover
      (Fin r.dimension → ℂ) :=
  (T.row r).universalCoverRepresentation

end AlternatingSixFiveAmbientRelationTableCertificate
end InductiveMcKay
end McKayConjecture
