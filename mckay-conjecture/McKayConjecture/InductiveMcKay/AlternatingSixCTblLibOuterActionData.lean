/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Data.Fin.Tuple.Reflection

/-!
# Audited CTblLib outer-action data for the sixfold cover of `A₆`

This file records the prime-to-`p` row permutations obtained by the
reproducible GAP audit `scripts/a6_outer_action_audit.g`.  CTblLib row
numbers are stored zero-based: a value `r : Fin n` denotes CTblLib row
number `r.val + 1`.

The central scalar exponent `e : Fin 6` means that the normalized value
on the chosen central class is `ζ₆ ^ e`.  The chosen ambient class is
class 2 of `6.A6`; each stored local table has a unique class fusing to
that class.

## Honesty boundary

These are independently checked finite table data.  This file does not
identify CTblLib rows with the project's constructed character rows, and
it does not claim that the displayed permutations are induced by a Lean
automorphism of the Schur-cover coordinate group.  Those are separate
bridge obligations.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Finite CTblLib data for one prime.  The `Fin n` source is the ordered
ambient prime-to-`p` display, while the `Fin n` target of `candidate` is
the ordered local prime-to-`p` display. -/
structure AlternatingSixCTblLibPPrimeActionData
    (n localRowCount : ℕ) where
  /-- CTblLib ambient row numbers, in display order. -/
  ambientRows : Fin n → Fin 31
  /-- CTblLib local row numbers, in display order. -/
  localRows : Fin n → Fin localRowCount
  /-- First genuine outer generator on the ambient display. -/
  ambientAlphaOne : Equiv.Perm (Fin n)
  /-- Second genuine outer generator on the ambient display. -/
  ambientAlphaTwo : Equiv.Perm (Fin n)
  /-- First genuine outer generator on the local display. -/
  localAlphaOne : Equiv.Perm (Fin n)
  /-- Second genuine outer generator on the local display. -/
  localAlphaTwo : Equiv.Perm (Fin n)
  /-- Audited candidate bijection from ambient to local display positions. -/
  candidate : Fin n ≃ Fin n
  /-- Ambient central scalar exponents in display order. -/
  ambientCentralExponent : Fin n → Fin 6
  /-- Local central scalar exponents in display order. -/
  localCentralExponent : Fin n → Fin 6

namespace AlternatingSixCTblLibPPrimeActionData

/-- The candidate intertwines both audited outer generators. -/
def GeneratorEquivariant
    {n localRowCount : ℕ}
    (data : AlternatingSixCTblLibPPrimeActionData n localRowCount) :
    Prop :=
  (∀ i, data.candidate (data.ambientAlphaOne i) =
      data.localAlphaOne (data.candidate i)) ∧
    ∀ i, data.candidate (data.ambientAlphaTwo i) =
      data.localAlphaTwo (data.candidate i)

/-- The candidate preserves the normalized scalar on the chosen central
class. -/
def CentralScalarPreserving
    {n localRowCount : ℕ}
    (data : AlternatingSixCTblLibPPrimeActionData n localRowCount) :
    Prop :=
  ∀ i, data.localCentralExponent (data.candidate i) =
    data.ambientCentralExponent i

end AlternatingSixCTblLibPPrimeActionData

/-- CTblLib data for `p = 2`.  The ambient rows are
`[1,2,3,6,14,15,16,17,20,21,22,23]`; all twelve displayed local rows
are rows `1` through `12` of `6.A6N2`. -/
def alternatingSixCTblLibTwoPPrimeActionData :
    AlternatingSixCTblLibPPrimeActionData 12 21 where
  ambientRows :=
    ![0, 1, 2, 5, 13, 14, 15, 16, 19, 20, 21, 22]
  localRows :=
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  ambientAlphaOne :=
    Equiv.ofBijective
      ![0, 1, 2, 3, 7, 6, 5, 4, 9, 8, 11, 10]
      (by decide)
  ambientAlphaTwo :=
    Equiv.ofBijective
      ![0, 2, 1, 3, 5, 4, 7, 6, 9, 8, 11, 10]
      (by decide)
  localAlphaOne :=
    Equiv.ofBijective
      ![0, 1, 2, 3, 5, 4, 7, 6, 9, 8, 11, 10]
      (by decide)
  localAlphaTwo :=
    Equiv.ofBijective
      ![0, 2, 1, 3, 7, 6, 5, 4, 9, 8, 11, 10]
      (by decide)
  candidate :=
    Equiv.ofBijective
      ![0, 1, 2, 3, 5, 6, 7, 4, 9, 8, 11, 10]
      (by decide)
  ambientCentralExponent :=
    ![0, 0, 0, 0, 2, 4, 2, 4, 2, 4, 2, 4]
  localCentralExponent :=
    ![0, 0, 0, 0, 4, 2, 4, 2, 4, 2, 4, 2]

/-- The `p = 2` candidate intertwines both genuine generator
permutations. -/
theorem alternatingSixCTblLibTwo_generatorEquivariant :
    alternatingSixCTblLibTwoPPrimeActionData.GeneratorEquivariant := by
  unfold AlternatingSixCTblLibPPrimeActionData.GeneratorEquivariant
  decide

/-- The `p = 2` candidate preserves the central scalar exponent. -/
theorem alternatingSixCTblLibTwo_centralScalarPreserving :
    alternatingSixCTblLibTwoPPrimeActionData.CentralScalarPreserving := by
  unfold AlternatingSixCTblLibPPrimeActionData.CentralScalarPreserving
  decide

/-- CTblLib data for `p = 3`.  The ambient rows are
`[1,2,3,4,5,7,8,9,10,11,12,13]`; the local rows of `6.A6M3` are
`[1,2,3,4,5,6,7,8,25,26,27,28]`. -/
def alternatingSixCTblLibThreePPrimeActionData :
    AlternatingSixCTblLibPPrimeActionData 12 28 where
  ambientRows :=
    ![0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12]
  localRows :=
    ![0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27]
  ambientAlphaOne :=
    Equiv.ofBijective
      ![0, 1, 2, 4, 3, 5, 6, 7, 9, 8, 11, 10]
      (by decide)
  ambientAlphaTwo :=
    Equiv.ofBijective
      ![0, 2, 1, 3, 4, 5, 7, 6, 8, 9, 10, 11]
      (by decide)
  localAlphaOne :=
    Equiv.ofBijective
      ![0, 1, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11]
      (by decide)
  localAlphaTwo :=
    Equiv.ofBijective
      ![0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9]
      (by decide)
  candidate :=
    Equiv.ofBijective
      ![0, 8, 10, 2, 3, 1, 9, 11, 4, 5, 6, 7]
      (by decide)
  ambientCentralExponent :=
    ![0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 3, 3]
  localCentralExponent :=
    ![0, 0, 0, 0, 3, 3, 3, 3, 0, 3, 0, 3]

/-- The `p = 3` candidate intertwines both genuine generator
permutations. -/
theorem alternatingSixCTblLibThree_generatorEquivariant :
    alternatingSixCTblLibThreePPrimeActionData.GeneratorEquivariant := by
  unfold AlternatingSixCTblLibPPrimeActionData.GeneratorEquivariant
  decide

/-- The `p = 3` candidate preserves the central scalar exponent. -/
theorem alternatingSixCTblLibThree_centralScalarPreserving :
    alternatingSixCTblLibThreePPrimeActionData.CentralScalarPreserving := by
  unfold AlternatingSixCTblLibPPrimeActionData.CentralScalarPreserving
  decide

/-- CTblLib data for `p = 5`.  The ambient rows are
`[1,4,5,6,8,9,10,11,14,15,16,17,18,19,20,21,24,25,26,27,28,29,30,31]`;
all twenty-four rows of `3x2.D10` are prime to five. -/
def alternatingSixCTblLibFivePPrimeActionData :
    AlternatingSixCTblLibPPrimeActionData 24 24 where
  ambientRows :=
    ![0, 3, 4, 5, 7, 8, 9, 10, 13, 14, 15, 16,
      17, 18, 19, 20, 23, 24, 25, 26, 27, 28, 29, 30]
  localRows :=
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
      12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  ambientAlphaOne :=
    Equiv.ofBijective
      ![0, 2, 1, 3, 4, 5, 7, 6, 11, 10, 9, 8,
        13, 12, 15, 14, 19, 18, 17, 16, 23, 22, 21, 20]
      (by decide)
  ambientAlphaTwo :=
    Equiv.ofBijective
      ![0, 1, 2, 3, 5, 4, 6, 7, 9, 8, 11, 10,
        13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22]
      (by decide)
  localAlphaOne :=
    Equiv.ofBijective
      ![0, 2, 1, 3, 5, 4, 6, 8, 7, 9, 11, 10,
        21, 23, 22, 18, 20, 19, 15, 17, 16, 12, 14, 13]
      (by decide)
  localAlphaTwo :=
    Equiv.ofBijective
      ![0, 2, 1, 3, 5, 4, 9, 11, 10, 6, 8, 7,
        12, 14, 13, 15, 17, 16, 18, 20, 19, 21, 23, 22]
      (by decide)
  candidate :=
    Equiv.ofBijective
      ![0, 15, 18, 3, 6, 9, 12, 21, 16, 17, 19, 20,
        1, 2, 4, 5, 7, 11, 10, 8, 13, 14, 22, 23]
      (by decide)
  ambientCentralExponent :=
    ![0, 0, 0, 0, 3, 3, 3, 3, 2, 4, 2, 4,
      2, 4, 2, 4, 5, 1, 5, 1, 5, 1, 5, 1]
  localCentralExponent :=
    ![0, 2, 4, 0, 2, 4, 3, 5, 1, 3, 5, 1,
      3, 5, 1, 0, 2, 4, 0, 2, 4, 3, 5, 1]

/-- The `p = 5` candidate intertwines both genuine generator
permutations. -/
theorem alternatingSixCTblLibFive_generatorEquivariant :
    alternatingSixCTblLibFivePPrimeActionData.GeneratorEquivariant := by
  unfold AlternatingSixCTblLibPPrimeActionData.GeneratorEquivariant
  decide

/-- The `p = 5` candidate preserves the central scalar exponent. -/
theorem alternatingSixCTblLibFive_centralScalarPreserving :
    alternatingSixCTblLibFivePPrimeActionData.CentralScalarPreserving := by
  unfold AlternatingSixCTblLibPPrimeActionData.CentralScalarPreserving
  decide

end InductiveMcKay
end McKayConjecture
