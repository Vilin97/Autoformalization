/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientMatrixRepresentation
import McKayConjecture.InductiveMcKay.AlternatingSixCyclotomicField

/-!
# Central scalar patterns in the ordinary `6.A₆` matrix table

All thirty-one generated rows use one of six tuples of powers of the fixed
primitive 120th root.  This file checks the two relation-module identities
once for each tuple and supplies a reusable constructor for matrix rows.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The six central-scalar tuples occurring in the generated ordinary table. -/
inductive AlternatingSixAmbientScalarPattern
  | trivial
  | orderThreePositive
  | orderThreeNegative
  | orderTwo
  | orderSixPositive
  | orderSixNegative
  deriving DecidableEq

namespace AlternatingSixAmbientScalarPattern

/-- Exponents of `ζ` for `a²`, `b⁴`, `(ab)⁵`, and `(ab²)⁵`. -/
def exponent :
    AlternatingSixAmbientScalarPattern → Fin 4 → ℕ
  | .trivial => ![0, 0, 0, 0]
  | .orderThreePositive => ![80, 0, 40, 80]
  | .orderThreeNegative => ![40, 0, 80, 40]
  | .orderTwo => ![60, 60, 60, 60]
  | .orderSixPositive => ![20, 60, 100, 20]
  | .orderSixNegative => ![100, 60, 20, 100]

private theorem root_pow_one :
    ζ ^ 120 = 1 :=
  alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one

private theorem root_ne_zero :
    ζ ≠ 0 :=
  alternatingSixComplexCyclotomicRoot_isPrimitive.ne_zero (by norm_num)

/-- Every advertised central scalar is a 120th root of unity. -/
theorem scalar_pow_one
    (pattern : AlternatingSixAmbientScalarPattern)
    (i : Fin 4) :
    (ζ ^ pattern.exponent i) ^ 120 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, root_pow_one, one_pow]

/-- The first relation-module row for every scalar pattern. -/
theorem lattice_one
    (pattern : AlternatingSixAmbientScalarPattern) :
    (ζ ^ pattern.exponent 0) ^ 3 *
          (ζ ^ pattern.exponent 2) ^ (-2 : ℤ) *
        ζ ^ pattern.exponent 3 =
      1 := by
  cases pattern
  · simp [exponent]
  · change (ζ ^ 80) ^ 3 * (ζ ^ 40) ^ (-2 : ℤ) * ζ ^ 80 = 1
    calc
      (ζ ^ 80) ^ 3 * (ζ ^ 40) ^ (-2 : ℤ) * ζ ^ 80 =
          (ζ ^ 120) ^ 2 := by
        field_simp [root_ne_zero]
      _ = 1 := by rw [root_pow_one, one_pow]
  · change (ζ ^ 40) ^ 3 * (ζ ^ 80) ^ (-2 : ℤ) * ζ ^ 40 = 1
    field_simp [root_ne_zero]
  · change (ζ ^ 60) ^ 3 * (ζ ^ 60) ^ (-2 : ℤ) * ζ ^ 60 = 1
    calc
      (ζ ^ 60) ^ 3 * (ζ ^ 60) ^ (-2 : ℤ) * ζ ^ 60 =
          ζ ^ 120 := by
        field_simp [root_ne_zero]
      _ = 1 := root_pow_one
  · change (ζ ^ 20) ^ 3 * (ζ ^ 100) ^ (-2 : ℤ) * ζ ^ 20 = 1
    calc
      (ζ ^ 20) ^ 3 * (ζ ^ 100) ^ (-2 : ℤ) * ζ ^ 20 =
          (ζ ^ 120)⁻¹ := by
        field_simp [root_ne_zero]
      _ = 1 := by rw [root_pow_one, inv_one]
  · change (ζ ^ 100) ^ 3 * (ζ ^ 20) ^ (-2 : ℤ) * ζ ^ 100 = 1
    calc
      (ζ ^ 100) ^ 3 * (ζ ^ 20) ^ (-2 : ℤ) * ζ ^ 100 =
          (ζ ^ 120) ^ 3 := by
        field_simp [root_ne_zero]
      _ = 1 := by rw [root_pow_one, one_pow]

/-- The second relation-module row for every scalar pattern. -/
theorem lattice_two
    (pattern : AlternatingSixAmbientScalarPattern) :
    (ζ ^ pattern.exponent 1) ^ 4 *
          (ζ ^ pattern.exponent 2) ^ 3 *
        (ζ ^ pattern.exponent 3) ^ (-3 : ℤ) =
      1 := by
  cases pattern
  · simp [exponent]
  · change
      (ζ ^ 0) ^ 4 * (ζ ^ 40) ^ 3 *
          (ζ ^ 80) ^ (-3 : ℤ) = 1
    calc
      (ζ ^ 0) ^ 4 * (ζ ^ 40) ^ 3 *
            (ζ ^ 80) ^ (-3 : ℤ) =
          (ζ ^ 120)⁻¹ := by
        field_simp [root_ne_zero]
      _ = 1 := by rw [root_pow_one, inv_one]
  · change
      (ζ ^ 0) ^ 4 * (ζ ^ 80) ^ 3 *
          (ζ ^ 40) ^ (-3 : ℤ) = 1
    calc
      (ζ ^ 0) ^ 4 * (ζ ^ 80) ^ 3 *
            (ζ ^ 40) ^ (-3 : ℤ) =
          ζ ^ 120 := by
        field_simp [root_ne_zero]
      _ = 1 := root_pow_one
  · change
      (ζ ^ 60) ^ 4 * (ζ ^ 60) ^ 3 *
          (ζ ^ 60) ^ (-3 : ℤ) = 1
    calc
      (ζ ^ 60) ^ 4 * (ζ ^ 60) ^ 3 *
            (ζ ^ 60) ^ (-3 : ℤ) =
          (ζ ^ 120) ^ 2 := by
        field_simp [root_ne_zero]
      _ = 1 := by rw [root_pow_one, one_pow]
  · change
      (ζ ^ 60) ^ 4 * (ζ ^ 100) ^ 3 *
          (ζ ^ 20) ^ (-3 : ℤ) = 1
    calc
      (ζ ^ 60) ^ 4 * (ζ ^ 100) ^ 3 *
            (ζ ^ 20) ^ (-3 : ℤ) =
          (ζ ^ 120) ^ 4 := by
        field_simp [root_ne_zero]
      _ = 1 := by rw [root_pow_one, one_pow]
  · change
      (ζ ^ 60) ^ 4 * (ζ ^ 20) ^ 3 *
          (ζ ^ 100) ^ (-3 : ℤ) = 1
    field_simp [root_ne_zero]

end AlternatingSixAmbientScalarPattern

/-- Build a complete presentation row from four exact matrix relations and
one of the six checked scalar patterns. -/
def alternatingSixAmbientMatrixRowCertificate
    {n : Type} [Fintype n] [DecidableEq n]
    (pattern : AlternatingSixAmbientScalarPattern)
    (matrixA matrixB : Matrix n n ℂ)
    (matrixA_sq :
      matrixA ^ 2 =
        (ζ ^ pattern.exponent 0) • (1 : Matrix n n ℂ))
    (matrixB_fourth :
      matrixB ^ 4 =
        (ζ ^ pattern.exponent 1) • (1 : Matrix n n ℂ))
    (matrixAB_fifth :
      (matrixA * matrixB) ^ 5 =
        (ζ ^ pattern.exponent 2) • (1 : Matrix n n ℂ))
    (matrixABSquared_fifth :
      (matrixA * matrixB ^ 2) ^ 5 =
        (ζ ^ pattern.exponent 3) • (1 : Matrix n n ℂ)) :
    AlternatingSixSchurMatrixRowCertificate n where
  matrixA := matrixA
  matrixB := matrixB
  relatorScalar i := ζ ^ pattern.exponent i
  relatorScalar_pow_one := pattern.scalar_pow_one
  matrixA_sq := matrixA_sq
  matrixB_fourth := matrixB_fourth
  matrixAB_fifth := matrixAB_fifth
  matrixABSquared_fifth := matrixABSquared_fifth
  lattice_one := pattern.lattice_one
  lattice_two := pattern.lattice_two

end InductiveMcKay
end McKayConjecture
