#!/usr/bin/env python3
"""Generate checked eigenbasis data for the remaining degree-three rows.

This script reads the already generated Lean matrix-data file.  It performs
exact arithmetic in Q[X]/(Phi_120), computes an eigenbasis for the second
generator with eigenvalues 1, zeta^30, -zeta^30, and emits only new
commutant-certificate modules.  It never rewrites matrix data or relation
files.
"""

from __future__ import annotations

import importlib.util
import re
import sys
from fractions import Fraction
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
BASE_GENERATOR_PATH = ROOT / "scripts" / "a6_character_matrices_to_lean.py"
SPEC = importlib.util.spec_from_file_location(
    "a6_character_matrices_to_lean", BASE_GENERATOR_PATH
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("could not load the ambient matrix generator")
BASE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = BASE
SPEC.loader.exec_module(BASE)

Polynomial = BASE.Polynomial
PHI = BASE.PHI

DATA_PATH = (
    ROOT
    / "McKayConjecture"
    / "InductiveMcKay"
    / "AlternatingSixFiveAmbientMatrixDataDegreeOneThree.lean"
)
OUTPUT_DIRECTORY = ROOT / "McKayConjecture" / "InductiveMcKay"
ROWS = ("03", "04", "05")


def parse_lean_matrix(row: str, generator: str) -> list[list[Polynomial]]:
    """Parse one sparse matrix definition from the generated Lean data."""

    text = DATA_PATH.read_text(encoding="utf-8")
    name = f"def alternatingSixFiveAmbient_row{row}_matrix{generator}"
    start = text.index(name)
    end = text.find("/--", start)
    block = text[start : end if end >= 0 else None]
    entries: list[Polynomial] = []
    for body in re.findall(
        r"alternatingSixCyclotomicValue\s*\[(.*?)\]", block, re.S
    ):
        coefficients: dict[int, Fraction] = {}
        for coefficient_source, exponent_source in re.findall(
            r"\(\s*(\([^()]*\)|-?\d+)\s*,\s*(\d+)\s*\)", body
        ):
            coefficient = Fraction(
                coefficient_source.strip("() ").replace(" ", "")
            )
            exponent = int(exponent_source)
            coefficients[exponent] = (
                coefficients.get(exponent, Fraction(0)) + coefficient
            )
        entries.append(Polynomial.from_dict(coefficients))
    dimension = int(len(entries) ** 0.5)
    if dimension != 3 or dimension * dimension != len(entries):
        raise ValueError(
            f"expected a 3 by 3 matrix for row {row}, found {len(entries)} entries"
        )
    return [
        entries[index * dimension : (index + 1) * dimension]
        for index in range(dimension)
    ]


def trim(polynomial: Iterable[Fraction]) -> list[Fraction]:
    result = list(polynomial)
    while result and result[-1] == 0:
        result.pop()
    return result


def raw_add(
    left: list[Fraction], right: list[Fraction]
) -> list[Fraction]:
    result = [Fraction(0)] * max(len(left), len(right))
    for index, coefficient in enumerate(left):
        result[index] += coefficient
    for index, coefficient in enumerate(right):
        result[index] += coefficient
    return trim(result)


def raw_neg(polynomial: list[Fraction]) -> list[Fraction]:
    return [-coefficient for coefficient in polynomial]


def raw_sub(
    left: list[Fraction], right: list[Fraction]
) -> list[Fraction]:
    return raw_add(left, raw_neg(right))


def raw_mul(
    left: list[Fraction], right: list[Fraction]
) -> list[Fraction]:
    if not left or not right:
        return []
    result = [Fraction(0)] * (len(left) + len(right) - 1)
    for left_index, left_coefficient in enumerate(left):
        for right_index, right_coefficient in enumerate(right):
            result[left_index + right_index] += (
                left_coefficient * right_coefficient
            )
    return trim(result)


def raw_scale(
    polynomial: list[Fraction], scalar: Fraction
) -> list[Fraction]:
    return trim([scalar * coefficient for coefficient in polynomial])


def raw_divmod(
    dividend: list[Fraction], divisor: list[Fraction]
) -> tuple[list[Fraction], list[Fraction]]:
    remainder = trim(dividend)
    divisor = trim(divisor)
    quotient = [Fraction(0)] * max(0, len(remainder) - len(divisor) + 1)
    while remainder and len(remainder) >= len(divisor):
        shift = len(remainder) - len(divisor)
        coefficient = remainder[-1] / divisor[-1]
        quotient[shift] += coefficient
        remainder = raw_sub(
            remainder,
            [Fraction(0)] * shift
            + raw_scale(divisor, coefficient),
        )
    return trim(quotient), remainder


def extended_gcd(
    left: list[Fraction], right: list[Fraction]
) -> tuple[list[Fraction], list[Fraction], list[Fraction]]:
    old_remainder, remainder = trim(left), trim(right)
    old_left, current_left = [Fraction(1)], []
    old_right, current_right = [], [Fraction(1)]
    while remainder:
        quotient, next_remainder = raw_divmod(old_remainder, remainder)
        old_remainder, remainder = remainder, next_remainder
        old_left, current_left = (
            current_left,
            raw_sub(old_left, raw_mul(quotient, current_left)),
        )
        old_right, current_right = (
            current_right,
            raw_sub(old_right, raw_mul(quotient, current_right)),
        )
    leading = old_remainder[-1]
    return (
        raw_scale(old_remainder, Fraction(1) / leading),
        raw_scale(old_left, Fraction(1) / leading),
        raw_scale(old_right, Fraction(1) / leading),
    )


PHI_LIST = [Fraction(0)] * 33
for degree, coefficient in PHI.items():
    PHI_LIST[degree] = coefficient


class CyclotomicElement:
    """An exact element of Q[X]/(Phi_120)."""

    def __init__(self, value: object = 0):
        if isinstance(value, CyclotomicElement):
            self.polynomial = value.polynomial
        elif isinstance(value, Polynomial):
            self.polynomial = value.reduce()
        else:
            self.polynomial = Polynomial.constant(value)

    def __add__(self, other: object) -> "CyclotomicElement":
        return CyclotomicElement(
            self.polynomial + CyclotomicElement(other).polynomial
        )

    __radd__ = __add__

    def __neg__(self) -> "CyclotomicElement":
        return CyclotomicElement(-self.polynomial)

    def __sub__(self, other: object) -> "CyclotomicElement":
        return self + -CyclotomicElement(other)

    def __rsub__(self, other: object) -> "CyclotomicElement":
        return CyclotomicElement(other) - self

    def __mul__(self, other: object) -> "CyclotomicElement":
        return CyclotomicElement(
            (
                self.polynomial
                * CyclotomicElement(other).polynomial
            ).reduce()
        )

    __rmul__ = __mul__

    def __eq__(self, other: object) -> bool:
        return self.polynomial == CyclotomicElement(other).polynomial

    def inverse(self) -> "CyclotomicElement":
        coefficients = [Fraction(0)] * 32
        for degree, coefficient in self.polynomial.coefficients:
            coefficients[degree] = coefficient
        gcd, bezout, _ = extended_gcd(trim(coefficients), trim(PHI_LIST))
        if gcd != [Fraction(1)]:
            raise ZeroDivisionError("nonunit in the cyclotomic field")
        _, reduced_bezout = raw_divmod(bezout, PHI_LIST)
        return CyclotomicElement(
            Polynomial.from_dict(
                {
                    degree: coefficient
                    for degree, coefficient in enumerate(reduced_bezout)
                    if coefficient
                }
            )
        )

    def __truediv__(self, other: object) -> "CyclotomicElement":
        return self * CyclotomicElement(other).inverse()


def rref(
    matrix: list[list[CyclotomicElement]],
) -> tuple[list[list[CyclotomicElement]], list[int]]:
    result = [[CyclotomicElement(entry) for entry in row] for row in matrix]
    row_count = len(result)
    column_count = len(result[0])
    pivot_columns: list[int] = []
    pivot_row = 0
    for column in range(column_count):
        selected = next(
            (
                row
                for row in range(pivot_row, row_count)
                if result[row][column] != 0
            ),
            None,
        )
        if selected is None:
            continue
        result[pivot_row], result[selected] = (
            result[selected],
            result[pivot_row],
        )
        inverse = result[pivot_row][column].inverse()
        result[pivot_row] = [
            inverse * entry for entry in result[pivot_row]
        ]
        for row in range(row_count):
            if row == pivot_row or result[row][column] == 0:
                continue
            coefficient = result[row][column]
            result[row] = [
                entry - coefficient * pivot_entry
                for entry, pivot_entry in zip(
                    result[row], result[pivot_row], strict=True
                )
            ]
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == row_count:
            break
    return result, pivot_columns


def null_vector(
    matrix: list[list[CyclotomicElement]],
) -> list[CyclotomicElement]:
    reduced, pivots = rref(matrix)
    free = [
        column
        for column in range(len(matrix[0]))
        if column not in pivots
    ]
    if len(free) != 1:
        raise ValueError(f"expected a one-dimensional kernel, found {free}")
    free_column = free[0]
    vector = [CyclotomicElement(0) for _ in matrix[0]]
    vector[free_column] = CyclotomicElement(1)
    for row, pivot in enumerate(pivots):
        vector[pivot] = -reduced[row][free_column]
    return vector


def matrix_inverse(
    matrix: list[list[CyclotomicElement]],
) -> list[list[CyclotomicElement]]:
    dimension = len(matrix)
    augmented = [
        [
            *row,
            *[
                CyclotomicElement(1 if row_index == column else 0)
                for column in range(dimension)
            ],
        ]
        for row_index, row in enumerate(matrix)
    ]
    reduced, pivots = rref(augmented)
    if pivots[:dimension] != list(range(dimension)):
        raise ValueError("computed eigenbasis is singular")
    return [row[dimension:] for row in reduced]


def exact_eigenbasis(
    matrix_b: list[list[Polynomial]],
) -> tuple[list[list[Polynomial]], list[list[Polynomial]]]:
    matrix = [
        [CyclotomicElement(entry) for entry in row] for row in matrix_b
    ]
    zeta_thirty = CyclotomicElement(Polynomial.monomial(30))
    eigenvalues = (
        CyclotomicElement(1),
        zeta_thirty,
        -zeta_thirty,
    )
    columns: list[list[CyclotomicElement]] = []
    for eigenvalue in eigenvalues:
        kernel_matrix = [
            [
                matrix[row][column]
                - (eigenvalue if row == column else 0)
                for column in range(3)
            ]
            for row in range(3)
        ]
        columns.append(null_vector(kernel_matrix))
    basis_elements = [
        [columns[column][row] for column in range(3)]
        for row in range(3)
    ]
    inverse_elements = matrix_inverse(basis_elements)
    return (
        [
            [entry.polynomial for entry in row]
            for row in basis_elements
        ],
        [
            [entry.polynomial for entry in row]
            for row in inverse_elements
        ],
    )


def raw_matrix_subtract(
    left: list[list[Polynomial]], right: list[list[Polynomial]]
) -> list[list[Polynomial]]:
    return [
        [
            left[row][column] - right[row][column]
            for column in range(3)
        ]
        for row in range(3)
    ]


def quotient_of_zero(polynomial: Polynomial) -> Polynomial:
    quotient, remainder = polynomial.divmod_monic(PHI)
    if remainder != Polynomial.constant(0):
        raise ValueError(
            f"purported identity has remainder {remainder.coefficients}"
        )
    return quotient


def identity_matrix() -> list[list[Polynomial]]:
    return [
        [
            Polynomial.constant(1 if row == column else 0)
            for column in range(3)
        ]
        for row in range(3)
    ]


def diagonal_matrix() -> list[list[Polynomial]]:
    eigenvalues = (
        Polynomial.constant(1),
        Polynomial.monomial(30),
        -Polynomial.monomial(30),
    )
    return [
        [
            eigenvalues[row]
            if row == column
            else Polynomial.constant(0)
            for column in range(3)
        ]
        for row in range(3)
    ]


def quotient_matrix(
    expression: list[list[Polynomial]],
) -> list[list[Polynomial]]:
    return [
        [quotient_of_zero(entry) for entry in row]
        for row in expression
    ]


def lean_matrix(matrix: list[list[Polynomial]]) -> str:
    rows = []
    for row in matrix:
        entries = ",\n      ".join(
            BASE.polynomial_to_lean(entry) for entry in row
        )
        rows.append(f"![{entries}]")
    return "![\n    " + ",\n    ".join(rows) + "\n  ]"


def lean_complex_expression(polynomial: Polynomial) -> str:
    return BASE.polynomial_expression_to_lean(polynomial)


def lean_rational(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"({value.numerator} / {value.denominator})"


def lean_rational_polynomial(polynomial: Polynomial) -> str:
    if not polynomial.coefficients:
        return "0"
    terms = []
    for degree, coefficient in polynomial.coefficients:
        coefficient_source = lean_rational(coefficient)
        if degree == 0:
            terms.append(f"Polynomial.C ({coefficient_source} : ℚ)")
        else:
            terms.append(
                f"Polynomial.C ({coefficient_source} : ℚ) * X ^ {degree}"
            )
    return " + ".join(terms)


def render_row_proof(
    theorem_name: str,
    row: str,
    left_name: str,
    right_name: str,
    quotients: list[list[Polynomial]],
    target: str,
) -> str:
    chunks = []
    for row_index in range(3):
        chunks.append(
            f"""private theorem {theorem_name}_row{row_index}
    (j : Fin 3) :
    ({left_name} * {right_name}) {row_index} j =
      {target} {row_index} j := by
  rw [Matrix.mul_apply]
  fin_cases j
"""
        )
        for column in range(3):
            quotient = lean_complex_expression(
                quotients[row_index][column]
            )
            chunks.append(
                f"""  {'·' if column == 0 else '·'} simp [
      alternatingSixAmbientRow{row}Eigenbasis,
      alternatingSixAmbientRow{row}EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    close_cyclotomic {quotient}
"""
            )
    return "".join(chunks)


def render_basis_inverse_proofs(
    row: str,
    basis: list[list[Polynomial]],
    inverse: list[list[Polynomial]],
) -> str:
    product = BASE.matrix_multiply_raw(inverse, basis)
    differences = raw_matrix_subtract(product, identity_matrix())
    quotients = quotient_matrix(differences)
    chunks = []
    for row_index in range(3):
        chunks.append(
            f"""private theorem row{row}_eigenbasisInverse_mul_row{row_index}
    (j : Fin 3) :
    (alternatingSixAmbientRow{row}EigenbasisInverse *
        alternatingSixAmbientRow{row}Eigenbasis) {row_index} j =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) {row_index} j := by
  rw [Matrix.mul_apply]
  fin_cases j
"""
        )
        for column in range(3):
            chunks.append(
                f"""  · simp [
      alternatingSixAmbientRow{row}Eigenbasis,
      alternatingSixAmbientRow{row}EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row{row} {lean_complex_expression(quotients[row_index][column])}
"""
            )
    chunks.append(
        f"""/-- The displayed inverse is a left inverse of the row {row} eigenbasis. -/
theorem alternatingSixAmbientRow{row}EigenbasisInverse_mul :
    alternatingSixAmbientRow{row}EigenbasisInverse *
        alternatingSixAmbientRow{row}Eigenbasis =
      1 := by
  ext i j
  fin_cases i
  · exact row{row}_eigenbasisInverse_mul_row0 j
  · exact row{row}_eigenbasisInverse_mul_row1 j
  · exact row{row}_eigenbasisInverse_mul_row2 j

/-- The displayed inverse is also a right inverse. -/
theorem alternatingSixAmbientRow{row}Eigenbasis_mul_inverse :
    alternatingSixAmbientRow{row}Eigenbasis *
        alternatingSixAmbientRow{row}EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixAmbientRow{row}EigenbasisInverse_mul

"""
    )
    return "".join(chunks)


def render_diagonalization_proofs(
    row: str,
    matrix_b: list[list[Polynomial]],
    basis: list[list[Polynomial]],
) -> str:
    left = BASE.matrix_multiply_raw(matrix_b, basis)
    right = BASE.matrix_multiply_raw(basis, diagonal_matrix())
    quotients = quotient_matrix(raw_matrix_subtract(left, right))
    chunks = []
    for row_index in range(3):
        chunks.append(
            f"""private theorem row{row}_generatorB_mul_eigenbasis_row{row_index}
    (j : Fin 3) :
    (alternatingSixFiveAmbient_row{row}_matrixB *
        alternatingSixAmbientRow{row}Eigenbasis) {row_index} j =
      (alternatingSixAmbientRow{row}Eigenbasis *
        Matrix.diagonal
          alternatingSixDegreeThreeGeneratorBEigenvalue) {row_index} j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases j
"""
        )
        for column in range(3):
            chunks.append(
                f"""  · simp [
      alternatingSixFiveAmbient_row{row}_matrixB,
      alternatingSixAmbientRow{row}Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row{row} {lean_complex_expression(quotients[row_index][column])}
"""
            )
    chunks.append(
        f"""/-- The checked row {row} basis diagonalizes the second generator. -/
theorem alternatingSixAmbientRow{row}GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row{row}_matrixB *
        alternatingSixAmbientRow{row}Eigenbasis =
      alternatingSixAmbientRow{row}Eigenbasis *
        Matrix.diagonal
          alternatingSixDegreeThreeGeneratorBEigenvalue := by
  ext i j
  fin_cases i
  · exact row{row}_generatorB_mul_eigenbasis_row0 j
  · exact row{row}_generatorB_mul_eigenbasis_row1 j
  · exact row{row}_generatorB_mul_eigenbasis_row2 j

"""
    )
    return "".join(chunks)


def render_connecting_entry(
    row: str,
    column: int,
    polynomial: Polynomial,
    quotient: Polynomial,
) -> str:
    suffix = f"0{column}"
    return f"""/-- Rational polynomial for the row {row} connecting entry `{suffix}`. -/
def alternatingSixAmbientRow{row}Connecting{suffix}Polynomial : ℚ[X] :=
  {lean_rational_polynomial(polynomial)}

/-- The row {row} connecting entry `{suffix}`. -/
def alternatingSixAmbientRow{row}Connecting{suffix} : ℂ :=
  Polynomial.eval₂ (algebraMap ℚ ℂ) ζ
    alternatingSixAmbientRow{row}Connecting{suffix}Polynomial

/-- Exact value of the transformed row {row} entry `{suffix}`. -/
theorem alternatingSixAmbientRow{row}TransformedGeneratorA_entry{suffix} :
    alternatingSixAmbientRow{row}TransformedGeneratorA 0 {column} =
      alternatingSixAmbientRow{row}Connecting{suffix} := by
  unfold alternatingSixAmbientRow{row}TransformedGeneratorA
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow{row}Connecting{suffix},
    alternatingSixAmbientRow{row}Connecting{suffix}Polynomial,
    alternatingSixAmbientRow{row}Eigenbasis,
    alternatingSixAmbientRow{row}EigenbasisInverse,
    alternatingSixFiveAmbient_row{row}_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_cyclotomic_row{row} {lean_complex_expression(quotient)}

/-- The transformed row {row} entry `{suffix}` is nonzero. -/
theorem alternatingSixAmbientRow{row}Connecting{suffix}_ne_zero :
    alternatingSixAmbientRow{row}Connecting{suffix} ≠ 0 := by
  unfold alternatingSixAmbientRow{row}Connecting{suffix}
  apply alternatingSixComplexPolynomial_eval₂_ne_zero
  · intro hzero
    have hvalue :=
      congrArg (Polynomial.eval (2 : ℚ)) hzero
    norm_num [
      alternatingSixAmbientRow{row}Connecting{suffix}Polynomial] at hvalue
  · dsimp [alternatingSixAmbientRow{row}Connecting{suffix}Polynomial]
    compute_degree <;> norm_num

"""


def render_row(row: str) -> str:
    matrix_a = parse_lean_matrix(row, "A")
    matrix_b = parse_lean_matrix(row, "B")
    basis, inverse = exact_eigenbasis(matrix_b)
    transformed_a = BASE.matrix_multiply_raw(
        BASE.matrix_multiply_raw(inverse, matrix_a), basis
    )
    connecting_polynomials = (
        transformed_a[0][1].reduce(),
        transformed_a[0][2].reduce(),
    )
    connecting_quotients = []
    for column, target in zip((1, 2), connecting_polynomials, strict=True):
        difference = transformed_a[0][column] - target
        connecting_quotients.append(quotient_of_zero(difference))

    header = f"""/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixCyclotomicNonzero
import McKayConjecture.InductiveMcKay.AlternatingSixDegreeThreeEigenvalues
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow{row}

/-!
# Checked commutant data for ambient row {row}

This generated certificate contains only exact cyclotomic linear algebra:
an eigenbasis and inverse, diagonalization of the second generator, and two
nonzero connecting entries of the transformed first generator.
-/

noncomputable section

set_option linter.style.longLine false

open Polynomial

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Eigenbasis for the row {row} second generator. -/
def alternatingSixAmbientRow{row}Eigenbasis :
    Matrix (Fin 3) (Fin 3) ℂ :=
  {lean_matrix(basis)}

/-- Explicit inverse of the row {row} eigenbasis. -/
def alternatingSixAmbientRow{row}EigenbasisInverse :
    Matrix (Fin 3) (Fin 3) ℂ :=
  {lean_matrix(inverse)}

macro "close_cyclotomic_row{row}" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

"""
    transformed_definition = f"""/-- The row {row} first generator in the checked eigenbasis. -/
def alternatingSixAmbientRow{row}TransformedGeneratorA :
    Matrix (Fin 3) (Fin 3) ℂ :=
  alternatingSixAmbientRow{row}EigenbasisInverse *
    alternatingSixFiveAmbient_row{row}_matrixA *
    alternatingSixAmbientRow{row}Eigenbasis

"""
    footer = """end InductiveMcKay
end McKayConjecture
"""
    return (
        header
        + render_basis_inverse_proofs(row, basis, inverse)
        + render_diagonalization_proofs(row, matrix_b, basis)
        + transformed_definition
        + render_connecting_entry(
            row,
            1,
            connecting_polynomials[0],
            connecting_quotients[0],
        )
        + render_connecting_entry(
            row,
            2,
            connecting_polynomials[1],
            connecting_quotients[1],
        )
        + footer
    )


def main() -> None:
    for row in ROWS:
        output = (
            OUTPUT_DIRECTORY
            / f"AlternatingSixAmbientRow{row}CommutantData.lean"
        )
        output.write_text(render_row(row), encoding="utf-8")


if __name__ == "__main__":
    main()
