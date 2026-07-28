#!/usr/bin/env python3
"""Generate diagonal-basis commutant certificates in degrees four and six.

The script reads the existing degree-four/six matrix-data module and performs
exact arithmetic in Q[X]/(Phi_120).  For each row it computes:

* an eigenbasis for the second generator and its inverse;
* the first generator in that basis;
* a small row-reduction certificate on the block diagonal commutant.

Only new diagonal-data and scalar-commutant modules are written.  Existing
matrix and relation data are never modified.
"""

from __future__ import annotations

import importlib.util
import re
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEGREE_THREE_GENERATOR = (
    ROOT / "scripts" / "a6_degree_three_commutant_to_lean.py"
)
SPEC = importlib.util.spec_from_file_location(
    "a6_degree_three_commutant_to_lean",
    DEGREE_THREE_GENERATOR,
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("could not load the degree-three certificate generator")
DEGREE_THREE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = DEGREE_THREE
SPEC.loader.exec_module(DEGREE_THREE)

Polynomial = DEGREE_THREE.Polynomial
CyclotomicElement = DEGREE_THREE.CyclotomicElement
BASE = DEGREE_THREE.BASE
PHI = DEGREE_THREE.PHI

DATA_PATH = (
    ROOT
    / "McKayConjecture"
    / "InductiveMcKay"
    / "AlternatingSixFiveAmbientMatrixDataDegreeFourSix.lean"
)
OUTPUT_DIRECTORY = ROOT / "McKayConjecture" / "InductiveMcKay"


@dataclass(frozen=True)
class RowMetadata:
    row: str
    dimension: int
    eigenvalue_exponents: tuple[int, int, int, int]
    base_eigenvalue: str
    base_injectivity: str


ROWS = (
    RowMetadata(
        "06",
        4,
        (15, 45, 75, 105),
        "alternatingSixOrderEightOddEigenvalue",
        "alternatingSixOrderEightOddEigenvalue_injective",
    ),
    RowMetadata(
        "07",
        4,
        (15, 45, 75, 105),
        "alternatingSixOrderEightOddEigenvalue",
        "alternatingSixOrderEightOddEigenvalue_injective",
    ),
    RowMetadata(
        "10",
        6,
        (0, 30, 60, 90),
        "alternatingSixOrderFourEigenvalue",
        "alternatingSixOrderFourEigenvalue_injective",
    ),
    RowMetadata(
        "11",
        6,
        (0, 30, 60, 90),
        "alternatingSixOrderFourEigenvalue",
        "alternatingSixOrderFourEigenvalue_injective",
    ),
    RowMetadata(
        "12",
        6,
        (15, 45, 75, 105),
        "alternatingSixOrderEightOddEigenvalue",
        "alternatingSixOrderEightOddEigenvalue_injective",
    ),
    RowMetadata(
        "13",
        6,
        (15, 45, 75, 105),
        "alternatingSixOrderEightOddEigenvalue",
        "alternatingSixOrderEightOddEigenvalue_injective",
    ),
    RowMetadata(
        "14",
        6,
        (15, 45, 75, 105),
        "alternatingSixOrderEightOddEigenvalue",
        "alternatingSixOrderEightOddEigenvalue_injective",
    ),
    RowMetadata(
        "15",
        6,
        (15, 45, 75, 105),
        "alternatingSixOrderEightOddEigenvalue",
        "alternatingSixOrderEightOddEigenvalue_injective",
    ),
)


def parse_lean_matrix(
    metadata: RowMetadata, generator: str
) -> list[list[Polynomial]]:
    """Parse one existing sparse matrix definition."""

    text = DATA_PATH.read_text(encoding="utf-8")
    name = (
        f"def alternatingSixFiveAmbient_row{metadata.row}"
        f"_matrix{generator}"
    )
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
    dimension = metadata.dimension
    if len(entries) != dimension * dimension:
        raise ValueError(
            f"row {metadata.row} matrix {generator} has "
            f"{len(entries)} entries, expected {dimension * dimension}"
        )
    return [
        entries[index * dimension : (index + 1) * dimension]
        for index in range(dimension)
    ]


def element_matrix(
    matrix: list[list[Polynomial]],
) -> list[list[CyclotomicElement]]:
    return [
        [CyclotomicElement(entry) for entry in row]
        for row in matrix
    ]


def polynomial_matrix(
    matrix: list[list[CyclotomicElement]],
) -> list[list[Polynomial]]:
    return [[entry.polynomial for entry in row] for row in matrix]


def matrix_multiply(
    left: list[list[CyclotomicElement]],
    right: list[list[CyclotomicElement]],
) -> list[list[CyclotomicElement]]:
    return [
        [
            sum(
                (
                    left[row][middle] * right[middle][column]
                    for middle in range(len(right))
                ),
                CyclotomicElement(0),
            )
            for column in range(len(right[0]))
        ]
        for row in range(len(left))
    ]


def nullspace_basis(
    matrix: list[list[CyclotomicElement]],
) -> list[list[CyclotomicElement]]:
    reduced, pivots = DEGREE_THREE.rref(matrix)
    free_columns = [
        column
        for column in range(len(matrix[0]))
        if column not in pivots
    ]
    basis: list[list[CyclotomicElement]] = []
    for free_column in free_columns:
        vector = [
            CyclotomicElement(0)
            for _ in range(len(matrix[0]))
        ]
        vector[free_column] = CyclotomicElement(1)
        for row, pivot in enumerate(pivots):
            vector[pivot] = -reduced[row][free_column]
        basis.append(vector)
    return basis


@dataclass
class DiagonalData:
    matrix_a: list[list[Polynomial]]
    matrix_b: list[list[Polynomial]]
    eigenbasis: list[list[Polynomial]]
    eigenbasis_inverse: list[list[Polynomial]]
    transformed_a: list[list[Polynomial]]
    labels: list[int]
    eigenvalue_exponents: list[int]


def compute_diagonal_data(metadata: RowMetadata) -> DiagonalData:
    matrix_a = parse_lean_matrix(metadata, "A")
    matrix_b = parse_lean_matrix(metadata, "B")
    matrix_b_elements = element_matrix(matrix_b)
    columns: list[list[CyclotomicElement]] = []
    labels: list[int] = []
    exponents: list[int] = []
    for label, exponent in enumerate(metadata.eigenvalue_exponents):
        eigenvalue = CyclotomicElement(Polynomial.monomial(exponent))
        kernel_matrix = [
            [
                matrix_b_elements[row][column]
                - (
                    eigenvalue
                    if row == column
                    else CyclotomicElement(0)
                )
                for column in range(metadata.dimension)
            ]
            for row in range(metadata.dimension)
        ]
        vectors = nullspace_basis(kernel_matrix)
        columns.extend(vectors)
        labels.extend([label] * len(vectors))
        exponents.extend([exponent] * len(vectors))
    if len(columns) != metadata.dimension:
        raise ValueError(
            f"row {metadata.row} produced {len(columns)} eigenvectors"
        )
    eigenbasis_elements = [
        [
            columns[column][row]
            for column in range(metadata.dimension)
        ]
        for row in range(metadata.dimension)
    ]
    inverse_elements = DEGREE_THREE.matrix_inverse(
        eigenbasis_elements
    )
    transformed_elements = matrix_multiply(
        matrix_multiply(inverse_elements, element_matrix(matrix_a)),
        eigenbasis_elements,
    )
    return DiagonalData(
        matrix_a,
        matrix_b,
        polynomial_matrix(eigenbasis_elements),
        polynomial_matrix(inverse_elements),
        polynomial_matrix(transformed_elements),
        labels,
        exponents,
    )


def zero_polynomial() -> Polynomial:
    return Polynomial.constant(0)


def identity_matrix(dimension: int) -> list[list[Polynomial]]:
    return [
        [
            Polynomial.constant(1 if row == column else 0)
            for column in range(dimension)
        ]
        for row in range(dimension)
    ]


def diagonal_matrix(
    exponents: list[int],
) -> list[list[Polynomial]]:
    dimension = len(exponents)
    return [
        [
            (
                Polynomial.monomial(exponents[row])
                if row == column
                else zero_polynomial()
            )
            for column in range(dimension)
        ]
        for row in range(dimension)
    ]


def raw_matrix_subtract(
    left: list[list[Polynomial]],
    right: list[list[Polynomial]],
) -> list[list[Polynomial]]:
    return [
        [
            left[row][column] - right[row][column]
            for column in range(len(left[0]))
        ]
        for row in range(len(left))
    ]


def quotient_of_zero(polynomial: Polynomial) -> Polynomial:
    quotient, remainder = polynomial.divmod_monic(PHI)
    if remainder != zero_polynomial():
        raise ValueError(
            f"identity remainder is {remainder.coefficients}"
        )
    return quotient


def quotient_matrix(
    matrix: list[list[Polynomial]],
) -> list[list[Polynomial]]:
    return [
        [quotient_of_zero(entry) for entry in row]
        for row in matrix
    ]


def lean_matrix(matrix: list[list[Polynomial]]) -> str:
    return DEGREE_THREE.lean_matrix(matrix)


def lean_complex(polynomial: Polynomial) -> str:
    return DEGREE_THREE.lean_complex_expression(polynomial)


def close_macro(row: str) -> str:
    return f"""macro "close_cyclotomic_row{row}" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

"""


def proof_bullets(
    row: str,
    quotients: list[Polynomial],
    simp_names: list[str],
) -> str:
    names = ",\n      ".join(simp_names)
    chunks: list[str] = []
    for quotient in quotients:
        chunks.append(
            f"""  · simp [
      {names}]
    try close_cyclotomic_row{row} {lean_complex(quotient)}
"""
        )
    return "".join(chunks)


def render_cell_proof(
    row: str,
    quotient: Polynomial,
    simp_names: list[str],
) -> str:
    names = ",\n      ".join(simp_names)
    return f"""  simp [
      {names}]
  try close_cyclotomic_row{row} {lean_complex(quotient)}
"""


def render_inverse_proof(
    metadata: RowMetadata, data: DiagonalData
) -> str:
    row = metadata.row
    dimension = metadata.dimension
    product = BASE.matrix_multiply_raw(
        data.eigenbasis_inverse, data.eigenbasis
    )
    quotients = quotient_matrix(
        raw_matrix_subtract(product, identity_matrix(dimension))
    )
    chunks: list[str] = []
    for row_index in range(dimension):
        for column_index in range(dimension):
            chunks.append(
                f"""private theorem row{row}_eigenbasisInverse_mul_{row_index}_{column_index} :
    (alternatingSixAmbientRow{row}EigenbasisInverse *
        alternatingSixAmbientRow{row}Eigenbasis)
        {row_index} {column_index} =
      (1 : Matrix (Fin {dimension}) (Fin {dimension}) ℂ)
        {row_index} {column_index} := by
  rw [Matrix.mul_apply]
"""
            )
            chunks.append(
                render_cell_proof(
                    row,
                    quotients[row_index][column_index],
                    [
                        f"alternatingSixAmbientRow{row}Eigenbasis",
                        f"alternatingSixAmbientRow{row}EigenbasisInverse",
                        "alternatingSixCyclotomicValue",
                        "Matrix.one_apply",
                        "Fin.sum_univ_succ",
                    ],
                )
            )
    exact_cells = "\n".join(
        f"  · exact row{row}_eigenbasisInverse_mul_{row_index}_{column_index}"
        for row_index in range(dimension)
        for column_index in range(dimension)
    )
    chunks.append(
        f"""/-- The displayed row {row} matrix is a left inverse of its
eigenbasis. -/
theorem alternatingSixAmbientRow{row}EigenbasisInverse_mul :
    alternatingSixAmbientRow{row}EigenbasisInverse *
        alternatingSixAmbientRow{row}Eigenbasis =
      1 := by
  ext i j
  fin_cases i <;> fin_cases j
{exact_cells}

/-- The displayed row {row} inverse is also a right inverse. -/
theorem alternatingSixAmbientRow{row}Eigenbasis_mul_inverse :
    alternatingSixAmbientRow{row}Eigenbasis *
        alternatingSixAmbientRow{row}EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixAmbientRow{row}EigenbasisInverse_mul

"""
    )
    return "".join(chunks)


def render_diagonalization_proof(
    metadata: RowMetadata, data: DiagonalData
) -> str:
    row = metadata.row
    dimension = metadata.dimension
    left = BASE.matrix_multiply_raw(
        data.matrix_b, data.eigenbasis
    )
    right = BASE.matrix_multiply_raw(
        data.eigenbasis,
        diagonal_matrix(data.eigenvalue_exponents),
    )
    quotients = quotient_matrix(raw_matrix_subtract(left, right))
    chunks: list[str] = []
    for row_index in range(dimension):
        for column_index in range(dimension):
            chunks.append(
                f"""private theorem row{row}_generatorB_mul_eigenbasis_{row_index}_{column_index} :
    (alternatingSixFiveAmbient_row{row}_matrixB *
        alternatingSixAmbientRow{row}Eigenbasis)
        {row_index} {column_index} =
      (alternatingSixAmbientRow{row}Eigenbasis *
        alternatingSixAmbientRow{row}GeneratorBDiagonal)
        {row_index} {column_index} := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
"""
            )
            chunks.append(
                render_cell_proof(
                    row,
                    quotients[row_index][column_index],
                    [
                        f"alternatingSixFiveAmbient_row{row}_matrixB",
                        f"alternatingSixAmbientRow{row}Eigenbasis",
                        f"alternatingSixAmbientRow{row}GeneratorBDiagonal",
                        f"alternatingSixAmbientRow{row}GeneratorBEigenvalue",
                        f"alternatingSixAmbientRow{row}EigenvalueLabel",
                        metadata.base_eigenvalue,
                        (
                            "alternatingSixOrderFourEigenvalueExponent"
                            if metadata.eigenvalue_exponents[0] == 0
                            else
                            "alternatingSixOrderEightOddEigenvalueExponent"
                        ),
                        "alternatingSixCyclotomicValue",
                        "Fin.sum_univ_succ",
                    ],
                )
            )
    exact_cells = "\n".join(
        f"  · exact row{row}_generatorB_mul_eigenbasis_{row_index}_{column_index}"
        for row_index in range(dimension)
        for column_index in range(dimension)
    )
    chunks.append(
        f"""/-- The checked row {row} basis diagonalizes the second
generator. -/
theorem alternatingSixAmbientRow{row}GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row{row}_matrixB *
        alternatingSixAmbientRow{row}Eigenbasis =
      alternatingSixAmbientRow{row}Eigenbasis *
        alternatingSixAmbientRow{row}GeneratorBDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j
{exact_cells}

"""
    )
    return "".join(chunks)


def render_transformed_a_proof(
    metadata: RowMetadata, data: DiagonalData
) -> str:
    row = metadata.row
    dimension = metadata.dimension
    left = BASE.matrix_multiply_raw(
        BASE.matrix_multiply_raw(
            data.eigenbasis_inverse, data.matrix_a
        ),
        data.eigenbasis,
    )
    quotients = quotient_matrix(
        raw_matrix_subtract(left, data.transformed_a)
    )
    chunks: list[str] = []
    for row_index in range(dimension):
        for column_index in range(dimension):
            chunks.append(
                f"""private theorem row{row}_transformedGeneratorA_{row_index}_{column_index} :
    (alternatingSixAmbientRow{row}EigenbasisInverse *
        alternatingSixFiveAmbient_row{row}_matrixA *
        alternatingSixAmbientRow{row}Eigenbasis)
        {row_index} {column_index} =
      alternatingSixAmbientRow{row}TransformedGeneratorA
        {row_index} {column_index} := by
  simp_rw [Matrix.mul_apply]
"""
            )
            chunks.append(
                render_cell_proof(
                    row,
                    quotients[row_index][column_index],
                    [
                        f"alternatingSixAmbientRow{row}Eigenbasis",
                        f"alternatingSixAmbientRow{row}EigenbasisInverse",
                        f"alternatingSixFiveAmbient_row{row}_matrixA",
                        f"alternatingSixAmbientRow{row}TransformedGeneratorA",
                        "alternatingSixCyclotomicValue",
                        "Fin.sum_univ_succ",
                    ],
                )
            )
    exact_cells = "\n".join(
        f"  · exact row{row}_transformedGeneratorA_{row_index}_{column_index}"
        for row_index in range(dimension)
        for column_index in range(dimension)
    )
    chunks.append(
        f"""/-- Exact conjugation formula for the row {row} first
generator. -/
theorem alternatingSixAmbientRow{row}TransformedGeneratorA_eq :
    alternatingSixAmbientRow{row}EigenbasisInverse *
        alternatingSixFiveAmbient_row{row}_matrixA *
        alternatingSixAmbientRow{row}Eigenbasis =
      alternatingSixAmbientRow{row}TransformedGeneratorA := by
  ext i j
  fin_cases i <;> fin_cases j
{exact_cells}

"""
    )
    return "".join(chunks)


def render_data_module(
    metadata: RowMetadata, data: DiagonalData
) -> str:
    row = metadata.row
    dimension = metadata.dimension
    label_entries = ", ".join(str(label) for label in data.labels)
    return f"""/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixDegreeFourSixEigenvalues
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixDataDegreeFourSix

/-!
# Checked diagonal data for ambient row {row}

This generated module records an exact eigenbasis for the second generator
and the first generator in that basis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Eigenvalue block labels for row {row}. -/
def alternatingSixAmbientRow{row}EigenvalueLabel :
    Fin {dimension} → Fin 4 :=
  ![{label_entries}]

/-- Second-generator eigenvalues, including their multiplicities. -/
def alternatingSixAmbientRow{row}GeneratorBEigenvalue :
    Fin {dimension} → ℂ :=
  fun i ↦
    {metadata.base_eigenvalue}
      (alternatingSixAmbientRow{row}EigenvalueLabel i)

/-- Diagonal form of the row {row} second generator. -/
def alternatingSixAmbientRow{row}GeneratorBDiagonal :
    Matrix (Fin {dimension}) (Fin {dimension}) ℂ :=
  Matrix.diagonal
    alternatingSixAmbientRow{row}GeneratorBEigenvalue

/-- Checked eigenbasis for the row {row} second generator. -/
def alternatingSixAmbientRow{row}Eigenbasis :
    Matrix (Fin {dimension}) (Fin {dimension}) ℂ :=
  {lean_matrix(data.eigenbasis)}

/-- Checked inverse of the row {row} eigenbasis. -/
def alternatingSixAmbientRow{row}EigenbasisInverse :
    Matrix (Fin {dimension}) (Fin {dimension}) ℂ :=
  {lean_matrix(data.eigenbasis_inverse)}

/-- The row {row} first generator in the checked diagonal basis. -/
def alternatingSixAmbientRow{row}TransformedGeneratorA :
    Matrix (Fin {dimension}) (Fin {dimension}) ℂ :=
  {lean_matrix(data.transformed_a)}

{close_macro(row)}
{render_inverse_proof(metadata, data)}
{render_diagonalization_proof(metadata, data)}
{render_transformed_a_proof(metadata, data)}
end InductiveMcKay
end McKayConjecture
"""


def restricted_commutator_rows(
    transformed_a: list[list[Polynomial]],
    allowed_pairs: list[tuple[int, int]],
) -> list[list[CyclotomicElement]]:
    dimension = len(transformed_a)
    matrix = element_matrix(transformed_a)
    rows: list[list[CyclotomicElement]] = []
    for output_row in range(dimension):
        for output_column in range(dimension):
            equation = [
                CyclotomicElement(0)
                for _ in allowed_pairs
            ]
            for variable, (row, column) in enumerate(allowed_pairs):
                if row == output_row:
                    equation[variable] += matrix[column][output_column]
                if column == output_column:
                    equation[variable] -= matrix[output_row][row]
            rows.append(equation)
    return rows


@dataclass
class ReductionData:
    allowed_pairs: list[tuple[int, int]]
    reduced_rows: list[list[CyclotomicElement]]
    combinations: list[list[CyclotomicElement]]
    pivots: list[int]


def row_reduce_commutator(data: DiagonalData) -> ReductionData:
    dimension = len(data.transformed_a)
    allowed_pairs = [
        (row, column)
        for row in range(dimension)
        for column in range(dimension)
        if data.labels[row] == data.labels[column]
    ]
    equations = restricted_commutator_rows(
        data.transformed_a, allowed_pairs
    )
    equation_count = dimension * dimension
    combinations = [
        [
            CyclotomicElement(1 if row == column else 0)
            for column in range(equation_count)
        ]
        for row in range(equation_count)
    ]
    pivot_row = 0
    pivots: list[int] = []
    for column in range(len(allowed_pairs)):
        selected = next(
            (
                row
                for row in range(pivot_row, equation_count)
                if equations[row][column] != 0
            ),
            None,
        )
        if selected is None:
            continue
        equations[pivot_row], equations[selected] = (
            equations[selected],
            equations[pivot_row],
        )
        combinations[pivot_row], combinations[selected] = (
            combinations[selected],
            combinations[pivot_row],
        )
        inverse = equations[pivot_row][column].inverse()
        equations[pivot_row] = [
            inverse * entry for entry in equations[pivot_row]
        ]
        combinations[pivot_row] = [
            inverse * entry
            for entry in combinations[pivot_row]
        ]
        for row in range(equation_count):
            if row == pivot_row or equations[row][column] == 0:
                continue
            coefficient = equations[row][column]
            equations[row] = [
                entry - coefficient * pivot_entry
                for entry, pivot_entry in zip(
                    equations[row],
                    equations[pivot_row],
                    strict=True,
                )
            ]
            combinations[row] = [
                entry - coefficient * pivot_entry
                for entry, pivot_entry in zip(
                    combinations[row],
                    combinations[pivot_row],
                    strict=True,
                )
            ]
        pivots.append(column)
        pivot_row += 1
    if pivot_row != len(allowed_pairs) - 1:
        raise ValueError(
            f"commutant has dimension {len(allowed_pairs) - pivot_row}, "
            "expected one"
        )
    free = [
        column
        for column in range(len(allowed_pairs))
        if column not in pivots
    ]
    expected_free = (dimension - 1, dimension - 1)
    if free != [allowed_pairs.index(expected_free)]:
        raise ValueError(
            f"unexpected free commutant coordinates: "
            f"{[allowed_pairs[index] for index in free]}"
        )
    return ReductionData(
        allowed_pairs,
        equations[:pivot_row],
        combinations[:pivot_row],
        pivots,
    )


def off_block_name(row: int, column: int) -> str:
    return f"hY{row}{column}"


def equation_name(dimension: int, index: int) -> str:
    return f"commutesA{index // dimension}{index % dimension}"


def render_equation_hypotheses(
    metadata: RowMetadata,
    data: DiagonalData,
    reduction: ReductionData,
    off_block_names: list[str],
    support: list[int] | None = None,
) -> tuple[str, list[int]]:
    if support is None:
        support = sorted(
            {
                index
                for row in reduction.combinations
                for index, coefficient in enumerate(row)
                if coefficient != 0
            }
        )
    chunks: list[str] = []
    off_block_source = ",\n      ".join(off_block_names)
    for index in support:
        output_row, output_column = divmod(
            index, metadata.dimension
        )
        name = equation_name(metadata.dimension, index)
        chunks.append(
            f"""  have {name} :=
    congrFun (congrFun commutesA
      ({output_row} : Fin {metadata.dimension}))
      ({output_column} : Fin {metadata.dimension})
  rw [Matrix.mul_apply, Matrix.mul_apply] at {name}
  simp only [Fin.sum_univ_succ] at {name}
  simp [
      alternatingSixAmbientRow{metadata.row}TransformedGeneratorA,
      alternatingSixCyclotomicValue] at {name}
"""
        )
        if off_block_names:
            chunks.append(
                f"""  simp only [
      {off_block_source}] at {name}
"""
            )
    return "".join(chunks), support


def raw_combination_coefficients(
    data: DiagonalData,
    reduction: ReductionData,
    reduction_row: int,
) -> list[Polynomial]:
    equations = restricted_commutator_rows(
        data.transformed_a, reduction.allowed_pairs
    )
    result = [
        zero_polynomial()
        for _ in reduction.allowed_pairs
    ]
    for equation_index, coefficient in enumerate(
        reduction.combinations[reduction_row]
    ):
        if coefficient == 0:
            continue
        for variable, entry in enumerate(equations[equation_index]):
            result[variable] = (
                result[variable]
                + coefficient.polynomial * entry.polynomial
            )
    return result


def target_coefficients(
    reduction: ReductionData, reduction_row: int
) -> list[Polynomial]:
    return [
        entry.polynomial
        for entry in reduction.reduced_rows[reduction_row]
    ]


def quotient_linear_form(
    data: DiagonalData,
    reduction: ReductionData,
    reduction_row: int,
) -> list[Polynomial]:
    combination = raw_combination_coefficients(
        data, reduction, reduction_row
    )
    target = target_coefficients(reduction, reduction_row)
    return [
        quotient_of_zero(left - right)
        for left, right in zip(combination, target, strict=True)
    ]


def render_linear_combination(
    metadata: RowMetadata,
    data: DiagonalData,
    reduction: ReductionData,
    reduction_row: int,
) -> str:
    terms: list[str] = []
    for equation_index, coefficient in enumerate(
        reduction.combinations[reduction_row]
    ):
        if coefficient == 0:
            continue
        terms.append(
            f"({lean_complex(coefficient.polynomial)}) * "
            f"{equation_name(metadata.dimension, equation_index)}"
        )
    quotients = quotient_linear_form(
        data, reduction, reduction_row
    )
    quotient_terms: list[str] = []
    for quotient, (row, column) in zip(
        quotients, reduction.allowed_pairs, strict=True
    ):
        if quotient == zero_polynomial():
            continue
        quotient_terms.append(
            f"({lean_complex(quotient)}) * Y {row} {column}"
        )
    combination = "\n      + ".join(terms)
    if quotient_terms:
        quotient_expression = "\n        + ".join(quotient_terms)
        combination += (
            "\n      - (\n        "
            + quotient_expression
            + ")\n        * "
            "alternatingSixComplexCyclotomicRoot_relation"
        )
    return combination


def render_reduced_relations(
    metadata: RowMetadata,
    data: DiagonalData,
    reduction: ReductionData,
) -> tuple[str, list[str]]:
    dimension = metadata.dimension
    free_pair = (dimension - 1, dimension - 1)
    chunks: list[str] = []
    names: list[str] = []
    for reduction_row, pivot in enumerate(reduction.pivots):
        pair = reduction.allowed_pairs[pivot]
        reduced = reduction.reduced_rows[reduction_row]
        for column, entry in enumerate(reduced):
            expected = CyclotomicElement(
                1 if column == pivot else 0
            )
            if pair[0] == pair[1] and column == len(
                reduction.allowed_pairs
            ) - 1:
                expected = CyclotomicElement(-1)
            if entry != expected:
                raise ValueError(
                    f"unexpected reduced row {reduction_row}: "
                    f"{[x.polynomial.coefficients for x in reduced]}"
                )
        row, column = pair
        name = f"reducedY{row}{column}"
        names.append(name)
        if row == column:
            goal = (
                f"Y {row} {column} = "
                f"Y {free_pair[0]} {free_pair[1]}"
            )
        else:
            goal = f"Y {row} {column} = 0"
        chunks.append(
            f"""  have {name} : {goal} := by
    linear_combination
      {render_linear_combination(metadata, data, reduction, reduction_row)}
"""
        )
    return "".join(chunks), names


def relevant_off_blocks(
    metadata: RowMetadata,
    data: DiagonalData,
    support: list[int],
) -> list[tuple[int, int]]:
    result: set[tuple[int, int]] = set()
    for equation_index in support:
        output_row, output_column = divmod(
            equation_index, metadata.dimension
        )
        for middle in range(metadata.dimension):
            left_pair = (output_row, middle)
            right_pair = (middle, output_column)
            if data.labels[left_pair[0]] != data.labels[left_pair[1]]:
                result.add(left_pair)
            if data.labels[right_pair[0]] != data.labels[right_pair[1]]:
                result.add(right_pair)
    return sorted(result)


def reduced_relation_goal(
    metadata: RowMetadata,
    reduction: ReductionData,
    reduction_row: int,
) -> tuple[tuple[int, int], str, str]:
    dimension = metadata.dimension
    pivot = reduction.pivots[reduction_row]
    pair = reduction.allowed_pairs[pivot]
    reduced = reduction.reduced_rows[reduction_row]
    for column, entry in enumerate(reduced):
        expected = CyclotomicElement(1 if column == pivot else 0)
        if pair[0] == pair[1] and column == len(
            reduction.allowed_pairs
        ) - 1:
            expected = CyclotomicElement(-1)
        if entry != expected:
            raise ValueError(
                f"unexpected reduced row {reduction_row}: "
                f"{[x.polynomial.coefficients for x in reduced]}"
            )
    row, column = pair
    name = f"reducedY{row}{column}"
    if row == column:
        goal = (
            f"Y {row} {column} = "
            f"Y {dimension - 1} {dimension - 1}"
        )
    else:
        goal = f"Y {row} {column} = 0"
    return pair, name, goal


def render_reduced_relation_helpers(
    metadata: RowMetadata,
    data: DiagonalData,
    reduction: ReductionData,
) -> tuple[str, str, list[str]]:
    chunks: list[str] = []
    applications: list[str] = []
    names: list[str] = []
    for reduction_row in range(len(reduction.pivots)):
        pair, name, goal = reduced_relation_goal(
            metadata, reduction, reduction_row
        )
        names.append(name)
        support = [
            index
            for index, coefficient in enumerate(
                reduction.combinations[reduction_row]
            )
            if coefficient != 0
        ]
        off_blocks = relevant_off_blocks(
            metadata, data, support
        )
        off_names = [
            off_block_name(row, column)
            for row, column in off_blocks
        ]
        off_proofs = "".join(
            f"""  have {off_block_name(row, column)} :
      Y {row} {column} = 0 :=
    alternatingSixAmbientRow{metadata.row}_off_block
      Y commutesDiagonal {row} {column} (by decide)
"""
            for row, column in off_blocks
        )
        equation_hypotheses, _ = render_equation_hypotheses(
            metadata,
            data,
            reduction,
            off_names,
            support,
        )
        chunks.append(
            f"""private theorem row{metadata.row}_{name}
    (Y : Matrix (Fin {metadata.dimension})
      (Fin {metadata.dimension}) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow{metadata.row}TransformedGeneratorA =
        alternatingSixAmbientRow{metadata.row}TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow{metadata.row}GeneratorBDiagonal =
        alternatingSixAmbientRow{metadata.row}GeneratorBDiagonal * Y) :
    {goal} := by
{off_proofs}
{equation_hypotheses}
  linear_combination
    {render_linear_combination(metadata, data, reduction, reduction_row)}

"""
        )
        applications.append(
            f"""  have {name} : {goal} :=
    row{metadata.row}_{name} Y commutesA commutesDiagonal
"""
        )
    return "".join(chunks), "".join(applications), names


def render_commutant_module(
    metadata: RowMetadata, data: DiagonalData
) -> str:
    row = metadata.row
    dimension = metadata.dimension
    reduction = row_reduce_commutator(data)
    off_blocks = [
        (output_row, output_column)
        for output_row in range(dimension)
        for output_column in range(dimension)
        if data.labels[output_row] != data.labels[output_column]
    ]
    off_names = [
        off_block_name(output_row, output_column)
        for output_row, output_column in off_blocks
    ]
    off_proofs = "".join(
        f"""  have {off_block_name(output_row, output_column)} :
      Y {output_row} {output_column} = 0 :=
    alternatingSixAmbientRow{row}_off_block
      Y commutesDiagonal {output_row} {output_column} (by decide)
"""
        for output_row, output_column in off_blocks
    )
    (
        reduced_helpers,
        reduced_applications,
        reduced_names,
    ) = render_reduced_relation_helpers(
        metadata, data, reduction
    )
    final_simp_names = ",\n      ".join(off_names + reduced_names)
    return f"""/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DiagonalBasisMatrixCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow{row}DiagonalData

/-!
# Scalar common commutant for ambient row {row}

The second generator is diagonal in the checked basis.  Its repeated
eigenspaces leave only {len(reduction.allowed_pairs)} possible matrix
coordinates, and the generated exact row reduction for the transformed first
generator reduces those coordinates to a single scalar.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Entries between distinct second-generator eigenspaces vanish in its
commutant. -/
private theorem alternatingSixAmbientRow{row}_off_block
    (Y : Matrix (Fin {dimension}) (Fin {dimension}) ℂ)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow{row}GeneratorBDiagonal =
        alternatingSixAmbientRow{row}GeneratorBDiagonal * Y)
    (i j : Fin {dimension})
    (different :
      alternatingSixAmbientRow{row}EigenvalueLabel i ≠
        alternatingSixAmbientRow{row}EigenvalueLabel j) :
    Y i j = 0 := by
  apply Matrix.entry_eq_zero_of_mul_diagonal_eq_diagonal_mul
    Y alternatingSixAmbientRow{row}GeneratorBEigenvalue
  · exact commutesDiagonal
  · intro equalEigenvalues
    apply different
    apply {metadata.base_injectivity}
    simpa [
      alternatingSixAmbientRow{row}GeneratorBEigenvalue] using
      equalEigenvalues.symm

{reduced_helpers}
/-- A matrix commuting with both transformed row {row} generators is
scalar. -/
theorem alternatingSixAmbientRow{row}Transformed_scalar_commutant
    (Y : Matrix (Fin {dimension}) (Fin {dimension}) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow{row}TransformedGeneratorA =
        alternatingSixAmbientRow{row}TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow{row}GeneratorBDiagonal =
        alternatingSixAmbientRow{row}GeneratorBDiagonal * Y) :
    ∃ c : ℂ,
      Y = c • (1 : Matrix (Fin {dimension}) (Fin {dimension}) ℂ) := by
{off_proofs}
{reduced_applications}
  refine ⟨Y {dimension - 1} {dimension - 1}, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [
      {final_simp_names}]

/-- Every matrix commuting with both original row {row} presentation
generators is scalar. -/
theorem alternatingSixAmbientRow{row}_scalar_commutant
    (X : Matrix (Fin {dimension}) (Fin {dimension}) ℂ)
    (commutesA :
      X * alternatingSixFiveAmbient_row{row}_matrixA =
        alternatingSixFiveAmbient_row{row}_matrixA * X)
    (commutesB :
      X * alternatingSixFiveAmbient_row{row}_matrixB =
        alternatingSixFiveAmbient_row{row}_matrixB * X) :
    ∃ c : ℂ,
      X = c • (1 : Matrix (Fin {dimension}) (Fin {dimension}) ℂ) := by
  apply Matrix.scalar_commutant_of_diagonal_basis
    alternatingSixFiveAmbient_row{row}_matrixA
    alternatingSixFiveAmbient_row{row}_matrixB
    alternatingSixAmbientRow{row}Eigenbasis
    alternatingSixAmbientRow{row}EigenbasisInverse
    alternatingSixAmbientRow{row}TransformedGeneratorA
    alternatingSixAmbientRow{row}GeneratorBEigenvalue
    alternatingSixAmbientRow{row}EigenbasisInverse_mul
    alternatingSixAmbientRow{row}Eigenbasis_mul_inverse
    alternatingSixAmbientRow{row}GeneratorB_mul_eigenbasis
    alternatingSixAmbientRow{row}TransformedGeneratorA_eq
    alternatingSixAmbientRow{row}Transformed_scalar_commutant
    X commutesA commutesB

end InductiveMcKay
end McKayConjecture
"""


def main() -> None:
    for metadata in ROWS:
        data = compute_diagonal_data(metadata)
        data_path = (
            OUTPUT_DIRECTORY
            / f"AlternatingSixAmbientRow{metadata.row}DiagonalData.lean"
        )
        commutant_path = (
            OUTPUT_DIRECTORY
            / f"AlternatingSixAmbientRow{metadata.row}DiagonalCommutant.lean"
        )
        data_path.write_text(
            render_data_module(metadata, data),
            encoding="utf-8",
        )
        commutant_path.write_text(
            render_commutant_module(metadata, data),
            encoding="utf-8",
        )
        print(
            f"wrote {data_path.relative_to(ROOT)} and "
            f"{commutant_path.relative_to(ROOT)}"
        )


if __name__ == "__main__":
    main()
