#!/usr/bin/env python3
"""Translate the checked GAP `6.A6` matrices into split Lean data files.

The input is the plain output of `scripts/a6_character_matrices.g`.
Cyclotomic expressions are reduced modulo

    Phi_120(X) = X^32 + X^28 - X^20 - X^16 - X^12 + X^4 + 1.

The generated files contain data only.  Subsequent Lean certificate files
recheck the presentation relations and character norms; neither GAP nor
this translator belongs to the trusted proof.
"""

from __future__ import annotations

import argparse
import ast
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import re
from typing import Iterable, TypeAlias


ORDER = 120
PHI: dict[int, Fraction] = {
    32: Fraction(1),
    28: Fraction(1),
    20: Fraction(-1),
    16: Fraction(-1),
    12: Fraction(-1),
    4: Fraction(1),
    0: Fraction(1),
}


@dataclass(frozen=True)
class Polynomial:
    """A sparse rational polynomial."""

    coefficients: tuple[tuple[int, Fraction], ...]

    @staticmethod
    def from_dict(coefficients: dict[int, Fraction]) -> "Polynomial":
        return Polynomial(
            tuple(
                sorted(
                    (degree, coefficient)
                    for degree, coefficient in coefficients.items()
                    if coefficient
                )
            )
        )

    @staticmethod
    def constant(value: int | Fraction) -> "Polynomial":
        coefficient = Fraction(value)
        return Polynomial.from_dict({0: coefficient})

    @staticmethod
    def monomial(degree: int, coefficient: int | Fraction = 1) -> "Polynomial":
        return Polynomial.from_dict({degree: Fraction(coefficient)})

    def as_dict(self) -> dict[int, Fraction]:
        return dict(self.coefficients)

    def __add__(self, other: object) -> "Polynomial":
        right = ensure_polynomial(other)
        result = self.as_dict()
        for degree, coefficient in right.coefficients:
            result[degree] = result.get(degree, Fraction(0)) + coefficient
        return Polynomial.from_dict(result)

    def __radd__(self, other: object) -> "Polynomial":
        return ensure_polynomial(other) + self

    def __neg__(self) -> "Polynomial":
        return Polynomial.from_dict(
            {degree: -coefficient for degree, coefficient in self.coefficients}
        )

    def __sub__(self, other: object) -> "Polynomial":
        return self + -ensure_polynomial(other)

    def __rsub__(self, other: object) -> "Polynomial":
        return ensure_polynomial(other) - self

    def __mul__(self, other: object) -> "Polynomial":
        right = ensure_polynomial(other)
        result: dict[int, Fraction] = {}
        for left_degree, left_coefficient in self.coefficients:
            for right_degree, right_coefficient in right.coefficients:
                degree = left_degree + right_degree
                result[degree] = (
                    result.get(degree, Fraction(0))
                    + left_coefficient * right_coefficient
                )
        return Polynomial.from_dict(result)

    def __rmul__(self, other: object) -> "Polynomial":
        return ensure_polynomial(other) * self

    def __truediv__(self, other: object) -> "Polynomial":
        denominator = Fraction(other)
        if denominator == 0:
            raise ZeroDivisionError
        return Polynomial.from_dict(
            {
                degree: coefficient / denominator
                for degree, coefficient in self.coefficients
            }
        )

    def __pow__(self, exponent: int) -> "Polynomial":
        if exponent < 0:
            raise ValueError("negative polynomial exponent")
        result = Polynomial.constant(1)
        base = self
        power = exponent
        while power:
            if power & 1:
                result = result * base
            base = base * base
            power //= 2
        return result

    def divmod_monic(
        self, divisor: dict[int, Fraction]
    ) -> tuple["Polynomial", "Polynomial"]:
        divisor_degree = max(divisor)
        if divisor[divisor_degree] != 1:
            raise ValueError("divisor must be monic")
        quotient: dict[int, Fraction] = {}
        remainder = self.as_dict()
        while remainder and max(remainder) >= divisor_degree:
            top_degree = max(remainder)
            top_coefficient = remainder[top_degree]
            shift = top_degree - divisor_degree
            quotient[shift] = quotient.get(shift, Fraction(0)) + top_coefficient
            for degree, coefficient in divisor.items():
                target = degree + shift
                remainder[target] = (
                    remainder.get(target, Fraction(0))
                    - top_coefficient * coefficient
                )
                if remainder[target] == 0:
                    del remainder[target]
        return Polynomial.from_dict(quotient), Polynomial.from_dict(remainder)

    def reduce(self) -> "Polynomial":
        return self.divmod_monic(PHI)[1]


def ensure_polynomial(value: object) -> Polynomial:
    if isinstance(value, Polynomial):
        return value
    if isinstance(value, (int, Fraction)):
        return Polynomial.constant(value)
    raise TypeError(f"cannot use {value!r} as a polynomial")


def evaluate_expression(node: ast.AST, roots: dict[str, Polynomial]) -> Polynomial:
    if isinstance(node, ast.Expression):
        return evaluate_expression(node.body, roots)
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return Polynomial.constant(node.value)
    if isinstance(node, ast.Name):
        try:
            return roots[node.id]
        except KeyError as error:
            raise ValueError(f"unexpected name {node.id}") from error
    if isinstance(node, ast.UnaryOp):
        value = evaluate_expression(node.operand, roots)
        if isinstance(node.op, ast.USub):
            return -value
        if isinstance(node.op, ast.UAdd):
            return value
    if isinstance(node, ast.BinOp):
        left = evaluate_expression(node.left, roots)
        if isinstance(node.op, ast.Pow):
            if not isinstance(node.right, ast.Constant) or not isinstance(
                node.right.value, int
            ):
                raise ValueError("nonconstant exponent")
            return left ** node.right.value
        right = evaluate_expression(node.right, roots)
        if isinstance(node.op, ast.Add):
            return left + right
        if isinstance(node.op, ast.Sub):
            return left - right
        if isinstance(node.op, ast.Mult):
            return left * right
        if isinstance(node.op, ast.Div):
            if len(right.coefficients) != 1 or right.coefficients[0][0] != 0:
                raise ValueError("nonconstant denominator")
            return left / right.coefficients[0][1]
    raise ValueError(f"unsupported expression: {ast.dump(node)}")


ROOT_PATTERN = re.compile(r"E\((\d+)\)")


def parse_cyclotomic_expression(source: str) -> Polynomial:
    roots: dict[str, Polynomial] = {}

    def replace_root(match: re.Match[str]) -> str:
        order = int(match.group(1))
        if ORDER % order:
            raise ValueError(f"E({order}) does not lie in Q(zeta_{ORDER})")
        name = f"e{order}"
        roots[name] = Polynomial.monomial(ORDER // order)
        return name

    python_source = ROOT_PATTERN.sub(replace_root, source).replace("^", "**")
    parsed = ast.parse(python_source, mode="eval")
    return evaluate_expression(parsed, roots).reduce()


def parse_matrix(source: str) -> list[list[Polynomial]]:
    roots: dict[str, Polynomial] = {}

    def replace_root(match: re.Match[str]) -> str:
        order = int(match.group(1))
        if ORDER % order:
            raise ValueError(f"E({order}) does not lie in Q(zeta_{ORDER})")
        name = f"e{order}"
        roots[name] = Polynomial.monomial(ORDER // order)
        return name

    python_source = ROOT_PATTERN.sub(replace_root, source).replace("^", "**")
    parsed = ast.parse(python_source, mode="eval")
    if not isinstance(parsed.body, ast.List):
        raise ValueError("matrix must be a list of rows")
    rows: list[list[Polynomial]] = []
    for row_node in parsed.body.elts:
        if not isinstance(row_node, ast.List):
            raise ValueError("matrix row must be a list")
        row: list[Polynomial] = []
        for entry_node in row_node.elts:
            row.append(evaluate_expression(entry_node, roots).reduce())
        rows.append(row)
    if not rows or any(len(row) != len(rows) for row in rows):
        raise ValueError("matrix must be nonempty and square")
    return rows


@dataclass(frozen=True)
class CharacterRow:
    label: str
    degree: int
    matrix_a: list[list[Polynomial]]
    matrix_b: list[list[Polynomial]]
    relator_scalar_exponents: tuple[int, int, int, int]


PolynomialMatrix: TypeAlias = list[list[Polynomial]]


def matrix_identity(dimension: int) -> PolynomialMatrix:
    return [
        [
            Polynomial.constant(1 if row_index == column_index else 0)
            for column_index in range(dimension)
        ]
        for row_index in range(dimension)
    ]


def matrix_scalar(dimension: int, scalar: Polynomial) -> PolynomialMatrix:
    return [
        [
            scalar if row_index == column_index else Polynomial.constant(0)
            for column_index in range(dimension)
        ]
        for row_index in range(dimension)
    ]


def matrix_multiply(
    left: PolynomialMatrix, right: PolynomialMatrix
) -> PolynomialMatrix:
    dimension = len(left)
    if (
        not left
        or len(right) != dimension
        or any(len(row) != dimension for row in left)
        or any(len(row) != dimension for row in right)
    ):
        raise ValueError("matrix dimensions do not agree")
    return [
        [
            sum(
                (
                    left[row_index][middle_index]
                    * right[middle_index][column_index]
                    for middle_index in range(dimension)
                ),
                Polynomial.constant(0),
            ).reduce()
            for column_index in range(dimension)
        ]
        for row_index in range(dimension)
    ]


def matrix_multiply_raw(
    left: PolynomialMatrix, right: PolynomialMatrix
) -> PolynomialMatrix:
    """Multiply without reducing the entries modulo Phi_120."""

    dimension = len(left)
    if (
        not left
        or len(right) != dimension
        or any(len(row) != dimension for row in left)
        or any(len(row) != dimension for row in right)
    ):
        raise ValueError("matrix dimensions do not agree")
    return [
        [
            sum(
                (
                    left[row_index][middle_index]
                    * right[middle_index][column_index]
                    for middle_index in range(dimension)
                ),
                Polynomial.constant(0),
            )
            for column_index in range(dimension)
        ]
        for row_index in range(dimension)
    ]


def matrix_multiply_certificate(
    left: PolynomialMatrix,
    right: PolynomialMatrix,
    target: PolynomialMatrix | None = None,
) -> tuple[PolynomialMatrix, PolynomialMatrix]:
    """Return a target and quotient certifying `left * right` modulo Phi.

    The returned matrices satisfy the exact polynomial identity

        left * right = target + quotient * Phi_120

    entrywise.  If no target is supplied, the canonical remainders are
    used.
    """

    raw_product = matrix_multiply_raw(left, right)
    if target is None:
        target = [
            [entry.reduce() for entry in row]
            for row in raw_product
        ]
    if len(target) != len(raw_product):
        raise ValueError("certificate target dimension does not agree")
    quotient: PolynomialMatrix = []
    for row_index, raw_row in enumerate(raw_product):
        quotient_row: list[Polynomial] = []
        if len(target[row_index]) != len(raw_row):
            raise ValueError("certificate target dimension does not agree")
        for column_index, raw_entry in enumerate(raw_row):
            difference = raw_entry - target[row_index][column_index]
            entry_quotient, remainder = difference.divmod_monic(PHI)
            if remainder != Polynomial.constant(0):
                raise ValueError(
                    "target is not congruent to matrix product modulo Phi_120"
                )
            quotient_row.append(entry_quotient)
        quotient.append(quotient_row)
    return target, quotient


def matrix_power(matrix: PolynomialMatrix, exponent: int) -> PolynomialMatrix:
    if exponent < 0:
        raise ValueError("negative matrix exponent")
    result = matrix_identity(len(matrix))
    base = matrix
    power = exponent
    while power:
        if power & 1:
            result = matrix_multiply(result, base)
        base = matrix_multiply(base, base)
        power //= 2
    return result


def matrices_equal(left: PolynomialMatrix, right: PolynomialMatrix) -> bool:
    return left == right


def scalar_matrix_root_exponent(matrix: PolynomialMatrix) -> int:
    """Recover `k` from an exact scalar matrix `zeta_120^k I`."""

    dimension = len(matrix)
    zero = Polynomial.constant(0)
    scalar = matrix[0][0].reduce()
    for row_index in range(dimension):
        for column_index in range(dimension):
            expected = scalar if row_index == column_index else zero
            if matrix[row_index][column_index].reduce() != expected:
                raise ValueError("presentation relator is not scalar")
    root = Polynomial.monomial(1)
    for exponent in range(ORDER):
        if (root ** exponent).reduce() == scalar:
            return exponent
    raise ValueError("scalar relator is not a 120th root of unity")


def derive_relator_scalar_exponents(
    matrix_a: PolynomialMatrix,
    matrix_b: PolynomialMatrix,
) -> tuple[int, int, int, int]:
    """Derive all four central scalar exponents by exact arithmetic."""

    matrix_b2 = matrix_power(matrix_b, 2)
    matrix_ab = matrix_multiply(matrix_a, matrix_b)
    matrix_ab2 = matrix_multiply(matrix_a, matrix_b2)
    return (
        scalar_matrix_root_exponent(matrix_power(matrix_a, 2)),
        scalar_matrix_root_exponent(matrix_power(matrix_b, 4)),
        scalar_matrix_root_exponent(matrix_power(matrix_ab, 5)),
        scalar_matrix_root_exponent(matrix_power(matrix_ab2, 5)),
    )


def verify_presentation_relations(rows: list[CharacterRow]) -> None:
    """Recheck every corrected matrix relation in exact Q[zeta_120]."""

    root = Polynomial.monomial(1)
    for row in rows:
        exponent_a2, exponent_b4, exponent_ab5, exponent_ab25 = (
            row.relator_scalar_exponents
        )
        dimension = row.degree
        matrix_a2 = matrix_power(row.matrix_a, 2)
        matrix_b2 = matrix_power(row.matrix_b, 2)
        matrix_b4 = matrix_multiply(matrix_b2, matrix_b2)
        matrix_ab = matrix_multiply(row.matrix_a, row.matrix_b)
        matrix_ab5 = matrix_power(matrix_ab, 5)
        matrix_ab2 = matrix_multiply(row.matrix_a, matrix_b2)
        matrix_ab25 = matrix_power(matrix_ab2, 5)
        checks = (
            (
                "A^2",
                matrix_a2,
                matrix_scalar(dimension, (root ** exponent_a2).reduce()),
            ),
            (
                "B^4",
                matrix_b4,
                matrix_scalar(dimension, (root ** exponent_b4).reduce()),
            ),
            (
                "(A B)^5",
                matrix_ab5,
                matrix_scalar(dimension, (root ** exponent_ab5).reduce()),
            ),
            (
                "(A B^2)^5",
                matrix_ab25,
                matrix_scalar(dimension, (root ** exponent_ab25).reduce()),
            ),
        )
        for relation_name, actual, expected in checks:
            if not matrices_equal(actual, expected):
                raise ValueError(
                    f"failed exact relation {relation_name} in row {row.label}"
                )


def read_rows(path: Path) -> list[CharacterRow]:
    # GAP inserts a backslash-newline only when the configured screen width
    # is exceeded.  Treat it as a lexical continuation.
    text = path.read_text(encoding="utf-8").replace("\\\n", "")
    lines = text.splitlines()
    rows: list[CharacterRow] = []
    index = 0
    while index < len(lines):
        line = lines[index]
        if not line.startswith("ROW "):
            index += 1
            continue
        label = line.removeprefix("ROW ").strip()
        degree = int(lines[index + 1].removeprefix("DEGREE ").strip())
        cursor = index + 2
        matrix_a_source: str | None = None
        matrix_b_source: str | None = None
        while cursor < len(lines) and lines[cursor] != "END_ROW":
            if lines[cursor].startswith("GENERATOR_A "):
                matrix_a_source = lines[cursor].removeprefix("GENERATOR_A ")
            elif lines[cursor].startswith("GENERATOR_B "):
                matrix_b_source = lines[cursor].removeprefix("GENERATOR_B ")
            cursor += 1
        if cursor == len(lines):
            raise ValueError(f"unterminated row {label}")
        if matrix_a_source is None or matrix_b_source is None:
            raise ValueError(f"missing generator matrix in row {label}")
        matrix_a = parse_matrix(matrix_a_source)
        matrix_b = parse_matrix(matrix_b_source)
        if len(matrix_a) != degree or len(matrix_b) != degree:
            raise ValueError(f"degree mismatch in row {label}")
        rows.append(
            CharacterRow(
                label,
                degree,
                matrix_a,
                matrix_b,
                derive_relator_scalar_exponents(matrix_a, matrix_b),
            )
        )
        index = cursor + 1
    if len(rows) != 31:
        raise ValueError(f"expected 31 ordinary rows, found {len(rows)}")
    return rows


def lean_rational(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"({value.numerator} / {value.denominator})"


def polynomial_to_lean(polynomial: Polynomial, root_name: str = "ζ") -> str:
    del root_name
    rendered_terms = [
        f"({lean_rational(coefficient)}, {degree})"
        for degree, coefficient in polynomial.coefficients
    ]
    source = (
        "alternatingSixCyclotomicValue ["
        + ", ".join(rendered_terms)
        + "]"
    )
    if len(source) <= 68:
        return source
    return (
        "alternatingSixCyclotomicValue\n"
        "          [\n"
        "            "
        + ",\n            ".join(rendered_terms)
        + "\n          ]"
    )


def polynomial_expression_to_lean(
    polynomial: Polynomial, root_name: str = "ζ"
) -> str:
    """Render a polynomial as a complex ring expression."""

    if not polynomial.coefficients:
        return "0"
    rendered_terms: list[tuple[int, str]] = []
    for degree, coefficient in polynomial.coefficients:
        sign = -1 if coefficient < 0 else 1
        absolute_coefficient = abs(coefficient)
        if degree == 0:
            term = f"({lean_rational(absolute_coefficient)} : ℂ)"
        elif absolute_coefficient == 1:
            term = f"{root_name} ^ {degree}"
        else:
            term = (
                f"({lean_rational(absolute_coefficient)} : ℂ) * "
                f"{root_name} ^ {degree}"
            )
        rendered_terms.append((sign, term))
    first_sign, first_term = rendered_terms[0]
    source = f"-{first_term}" if first_sign < 0 else first_term
    for sign, term in rendered_terms[1:]:
        source += f" {'-' if sign < 0 else '+'} {term}"
    if len(source) <= 68:
        return f"({source})"
    lines = [
        "(",
        f"        {'-' if first_sign < 0 else ''}{first_term}",
    ]
    for sign, term in rendered_terms[1:]:
        lines.append(f"          {'-' if sign < 0 else '+'} {term}")
    lines.append("      )")
    return "\n".join(lines)


def matrix_to_lean_with(
    matrix: PolynomialMatrix,
    render_entry,
) -> str:
    row_sources = []
    for row in matrix:
        entries = ",\n        ".join(render_entry(entry) for entry in row)
        row_sources.append(f"![{entries}]")
    return "![\n      " + ",\n      ".join(row_sources) + "\n    ]"


def matrix_to_lean(matrix: PolynomialMatrix) -> str:
    return matrix_to_lean_with(matrix, polynomial_to_lean)


def lean_label(label: str) -> str:
    if label.isdigit():
        return f"row{int(label):02d}"
    if label.startswith("ATLAS12_"):
        return f"atlas12Power{label.removeprefix('ATLAS12_')}"
    return label.lower().replace("_", "")


def upper_initial(name: str) -> str:
    return name[:1].upper() + name[1:]


def definition_name(row: CharacterRow, generator: str) -> str:
    return (
        "alternatingSixFiveAmbient_"
        f"{lean_label(row.label)}_matrix{generator}"
    )


def file_bucket(row: CharacterRow) -> str:
    if row.degree in {1, 3}:
        return "DegreeOneThree"
    if row.degree in {4, 6}:
        return "DegreeFourSix"
    if row.degree in {5, 10, 15}:
        return "DegreeFiveTenFifteen"
    if row.degree in {8, 9}:
        return "DegreeEightNine"
    if row.degree == 12:
        return "DegreeTwelve"
    raise ValueError(f"unexpected degree {row.degree}")


HEADER = """/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import McKayConjecture.InductiveMcKay.AlternatingSixCyclotomicField

/-!
# Generated `6.A₆` ambient matrix data

This file is generated by `scripts/a6_character_matrices_to_lean.py`
from the relation-checked output of `scripts/a6_character_matrices.g`.
The entries are reduced modulo `Φ₁₂₀`.  Later files prove all presentation
relations and character-table certificates inside Lean.
-/

noncomputable section

set_option linter.style.longLine false

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

"""


FOOTER = """
end InductiveMcKay
end McKayConjecture
"""


def render_bucket(rows: Iterable[CharacterRow]) -> str:
    chunks = [HEADER]
    for row in rows:
        chunks.append(
            f"/-- Corrected first generator matrix for GAP row `{row.label}`. -/\n"
            f"def {definition_name(row, 'A')} :\n"
            f"    Matrix (Fin {row.degree}) (Fin {row.degree}) ℂ :=\n"
            f"  {matrix_to_lean(row.matrix_a)}\n\n"
            f"/-- Corrected second generator matrix for GAP row `{row.label}`. -/\n"
            f"def {definition_name(row, 'B')} :\n"
            f"    Matrix (Fin {row.degree}) (Fin {row.degree}) ℂ :=\n"
            f"  {matrix_to_lean(row.matrix_b)}\n\n"
        )
    chunks.append(FOOTER)
    return "".join(chunks)


def write_data_files(rows: list[CharacterRow], output_directory: Path) -> None:
    buckets = [
        "DegreeOneThree",
        "DegreeFourSix",
        "DegreeFiveTenFifteen",
        "DegreeEightNine",
        "DegreeTwelve",
    ]
    for bucket in buckets:
        selected = [row for row in rows if file_bucket(row) == bucket]
        path = output_directory / (
            f"AlternatingSixFiveAmbientMatrixData{bucket}.lean"
        )
        path.write_text(render_bucket(selected), encoding="utf-8")


@dataclass(frozen=True)
class MatrixMultiplicationStage:
    """One exact multiplication step in a presentation certificate."""

    name: str
    left_name: str
    right_name: str
    target_name: str
    left: PolynomialMatrix
    right: PolynomialMatrix
    target: PolynomialMatrix
    quotient: PolynomialMatrix
    scalar_exponent: int | None = None
    is_final_relation: bool = False


@dataclass(frozen=True)
class RelationPart:
    """One independently compiled part of a row's presentation proof."""

    file_suffix: str
    title: str
    stage_suffixes: tuple[str, ...]
    public_relation: str


RELATION_PARTS: tuple[RelationPart, ...] = (
    RelationPart(
        "ASquare",
        "square of the first generator",
        ("matrixA_sq",),
        "matrixA_sq",
    ),
    RelationPart(
        "BFourth",
        "fourth power of the second generator",
        ("matrixB_sq", "matrixB_fourth"),
        "matrixB_fourth",
    ),
    RelationPart(
        "ABFifth",
        "fifth power of the generator product",
        ("matrixAB", "matrixAB_sq", "matrixAB_fourth", "matrixAB_fifth"),
        "matrixAB_fifth",
    ),
    RelationPart(
        "ABSquaredFifth",
        "fifth power of the `A B²` product",
        (
            "matrixB_sq",
            "matrixABSquared",
            "matrixABSquared_sq",
            "matrixABSquared_fourth",
            "matrixABSquared_fifth",
        ),
        "matrixABSquared_fifth",
    ),
)


def build_matrix_multiplication_stages(
    row: CharacterRow,
) -> list[MatrixMultiplicationStage]:
    row_name = f"alternatingSixFiveAmbient_{lean_label(row.label)}"
    root = Polynomial.monomial(1)
    exponent_a2, exponent_b4, exponent_ab5, exponent_ab25 = (
        row.relator_scalar_exponents
    )
    stages: list[MatrixMultiplicationStage] = []

    def add_stage(
        name: str,
        left_name: str,
        right_name: str,
        left: PolynomialMatrix,
        right: PolynomialMatrix,
        target_name: str,
        scalar_exponent: int | None = None,
        is_final_relation: bool = False,
    ) -> PolynomialMatrix:
        target = (
            matrix_scalar(
                row.degree,
                root ** scalar_exponent,
            )
            if scalar_exponent is not None
            else None
        )
        certified_target, quotient = matrix_multiply_certificate(
            left, right, target
        )
        stages.append(
            MatrixMultiplicationStage(
                name=f"{row_name}_{name}",
                left_name=left_name,
                right_name=right_name,
                target_name=target_name,
                left=left,
                right=right,
                target=certified_target,
                quotient=quotient,
                scalar_exponent=scalar_exponent,
                is_final_relation=is_final_relation,
            )
        )
        return certified_target

    matrix_a_name = f"{row_name}_matrixA"
    matrix_b_name = f"{row_name}_matrixB"
    add_stage(
        "matrixA_sq",
        matrix_a_name,
        matrix_a_name,
        row.matrix_a,
        row.matrix_a,
        f"{row_name}_matrixA_sqTarget",
        exponent_a2,
        True,
    )
    matrix_b2_name = f"{row_name}_matrixB_sqValue"
    matrix_b2 = add_stage(
        "matrixB_sq",
        matrix_b_name,
        matrix_b_name,
        row.matrix_b,
        row.matrix_b,
        matrix_b2_name,
    )
    add_stage(
        "matrixB_fourth",
        matrix_b2_name,
        matrix_b2_name,
        matrix_b2,
        matrix_b2,
        f"{row_name}_matrixB_fourthTarget",
        exponent_b4,
        True,
    )
    matrix_ab_name = f"{row_name}_matrixABValue"
    matrix_ab = add_stage(
        "matrixAB",
        matrix_a_name,
        matrix_b_name,
        row.matrix_a,
        row.matrix_b,
        matrix_ab_name,
    )
    matrix_ab2_name = f"{row_name}_matrixAB_sqValue"
    matrix_ab2 = add_stage(
        "matrixAB_sq",
        matrix_ab_name,
        matrix_ab_name,
        matrix_ab,
        matrix_ab,
        matrix_ab2_name,
    )
    matrix_ab4_name = f"{row_name}_matrixAB_fourthValue"
    matrix_ab4 = add_stage(
        "matrixAB_fourth",
        matrix_ab2_name,
        matrix_ab2_name,
        matrix_ab2,
        matrix_ab2,
        matrix_ab4_name,
    )
    add_stage(
        "matrixAB_fifth",
        matrix_ab4_name,
        matrix_ab_name,
        matrix_ab4,
        matrix_ab,
        f"{row_name}_matrixAB_fifthTarget",
        exponent_ab5,
        True,
    )
    matrix_ab_squared_name = f"{row_name}_matrixABSquaredValue"
    matrix_ab_squared = add_stage(
        "matrixABSquared",
        matrix_a_name,
        matrix_b2_name,
        row.matrix_a,
        matrix_b2,
        matrix_ab_squared_name,
    )
    matrix_ab_squared2_name = f"{row_name}_matrixABSquared_sqValue"
    matrix_ab_squared2 = add_stage(
        "matrixABSquared_sq",
        matrix_ab_squared_name,
        matrix_ab_squared_name,
        matrix_ab_squared,
        matrix_ab_squared,
        matrix_ab_squared2_name,
    )
    matrix_ab_squared4_name = f"{row_name}_matrixABSquared_fourthValue"
    matrix_ab_squared4 = add_stage(
        "matrixABSquared_fourth",
        matrix_ab_squared2_name,
        matrix_ab_squared2_name,
        matrix_ab_squared2,
        matrix_ab_squared2,
        matrix_ab_squared4_name,
    )
    add_stage(
        "matrixABSquared_fifth",
        matrix_ab_squared4_name,
        matrix_ab_squared_name,
        matrix_ab_squared4,
        matrix_ab_squared,
        f"{row_name}_matrixABSquared_fifthTarget",
        exponent_ab25,
        True,
    )
    return stages


def data_import_for_row(row: CharacterRow) -> str:
    return (
        "McKayConjecture.InductiveMcKay."
        f"AlternatingSixFiveAmbientMatrixData{file_bucket(row)}"
    )


def render_complex_stage_target(
    stage: MatrixMultiplicationStage,
    dimension: int,
) -> str:
    if stage.scalar_exponent is not None:
        return (
            f"(ζ ^ {stage.scalar_exponent}) •\n"
            f"    (1 : Matrix (Fin {dimension}) (Fin {dimension}) ℂ)"
        )
    return matrix_to_lean(stage.target)


def render_stage_entry_tactic(
    quotient: Polynomial,
    indent: str = "    ",
) -> str:
    if not quotient.coefficients:
        return ""
    expression = polynomial_expression_to_lean(quotient)
    return (
        f"{indent}first\n"
        f"{indent}| linear_combination\n"
        f"{indent}    {expression} *\n"
        f"{indent}      alternatingSixComplexCyclotomicRoot_relation\n"
        f"{indent}| linear_combination\n"
        f"{indent}    (-{expression}) *\n"
        f"{indent}      alternatingSixComplexCyclotomicRoot_relation\n"
    )


def render_stage_proof(
    stage: MatrixMultiplicationStage,
    dimension: int,
) -> str:
    chunks: list[str] = []
    finite_sum_simp = ", Fin.sum_univ_succ" if dimension > 1 else ""
    if dimension >= 6:
        for row_index in range(dimension):
            for column_index in range(dimension):
                entry_lemma = (
                    f"{stage.name}_entry"
                    f"{row_index:02d}_{column_index:02d}"
                )
                quotient = stage.quotient[row_index][column_index]
                if quotient.coefficients:
                    chunks.append(
                        "-- Cyclotomic reduction uses a generated "
                        "fallback with the opposite sign.\n"
                        "set_option linter.flexible false in\n"
                        "set_option linter.unusedTactic false in\n"
                        "set_option linter.unreachableTactic false in\n"
                    )
                else:
                    chunks.append(
                        "-- `simp` may close before the zero-goal-safe "
                        "`all_goals ring` fallback runs.\n"
                        "set_option linter.unusedTactic false in\n"
                        "set_option linter.unreachableTactic false in\n"
                    )
                chunks.append(
                    f"private theorem {entry_lemma} :\n"
                    f"    ({stage.left_name}\n"
                    f"        * {stage.right_name})\n"
                    f"          ({row_index} : Fin {dimension}) "
                    f"({column_index} : Fin {dimension}) =\n"
                    f"      {stage.target_name}\n"
                    "        "
                    f"({row_index} : Fin {dimension}) "
                    f"({column_index} : Fin {dimension}) := by\n"
                    f"  rw [Matrix.mul_apply]\n"
                    "  simp [\n"
                    f"    {stage.left_name},\n"
                    f"    {stage.right_name},\n"
                    f"    {stage.target_name},\n"
                    "    alternatingSixCyclotomicValue"
                    f"{finite_sum_simp}\n"
                    "  ]"
                )
                if not quotient.coefficients:
                    chunks.append("\n  all_goals ring\n")
                else:
                    chunks.append("\n")
                    chunks.append(
                        render_stage_entry_tactic(quotient, indent="  ")
                    )
                chunks.append("\n")
        chunks.append(
            f"private theorem {stage.name}_mul :\n"
            f"    {stage.left_name} *\n"
            f"        {stage.right_name} =\n"
            f"      {stage.target_name} := by\n"
            f"  ext i j\n"
            f"  fin_cases i <;> fin_cases j\n"
        )
        for row_index in range(dimension):
            for column_index in range(dimension):
                chunks.append(
                    f"  · exact {stage.name}_entry"
                    f"{row_index:02d}_{column_index:02d}\n"
                )
        chunks.append("\n")
        return "".join(chunks)
    for row_index in range(dimension):
        row_lemma = f"{stage.name}_row{row_index:02d}"
        chunks.append(
            f"private theorem {row_lemma}\n"
            f"    (j : Fin {dimension}) :\n"
            f"    ({stage.left_name} * {stage.right_name})\n"
            f"          ({row_index} : Fin {dimension}) j =\n"
            f"      {stage.target_name} ({row_index} : Fin {dimension}) j := by\n"
            f"  rw [Matrix.mul_apply]\n"
            f"  fin_cases j\n"
        )
        for column_index in range(dimension):
            quotient = stage.quotient[row_index][column_index]
            closing_tactic = (
                " <;>\n    ring"
                if not quotient.coefficients
                else ""
            )
            chunks.append(
                "  · simp ["
                f"{stage.left_name}, {stage.right_name}, "
                f"{stage.target_name}, "
                "alternatingSixCyclotomicValue"
                f"{finite_sum_simp}]{closing_tactic}\n"
            )
            chunks.append(render_stage_entry_tactic(quotient))
        chunks.append("\n")
    chunks.append(
        f"private theorem {stage.name}_mul :\n"
        f"    {stage.left_name} * {stage.right_name} =\n"
        f"      {stage.target_name} := by\n"
        f"  ext i j\n"
        f"  fin_cases i\n"
    )
    for row_index in range(dimension):
        chunks.append(
            f"  · exact {stage.name}_row{row_index:02d} j\n"
        )
    chunks.append("\n")
    return "".join(chunks)


def render_row_public_relation_part(
    row: CharacterRow,
    public_relation: str,
) -> str:
    """Render exactly one of the four public presentation relations."""

    row_name = f"alternatingSixFiveAmbient_{lean_label(row.label)}"
    dimension = row.degree
    exponent_a2, exponent_b4, exponent_ab5, exponent_ab25 = (
        row.relator_scalar_exponents
    )
    matrix_a = f"{row_name}_matrixA"
    matrix_b = f"{row_name}_matrixB"
    matrix_b2 = f"{row_name}_matrixB_sqValue"
    matrix_ab = f"{row_name}_matrixABValue"
    matrix_ab2 = f"{row_name}_matrixAB_sqValue"
    matrix_ab4 = f"{row_name}_matrixAB_fourthValue"
    matrix_c = f"{row_name}_matrixABSquaredValue"
    matrix_c2 = f"{row_name}_matrixABSquared_sqValue"
    matrix_c4 = f"{row_name}_matrixABSquared_fourthValue"
    identity = f"(1 : Matrix (Fin {dimension}) (Fin {dimension}) ℂ)"
    if public_relation == "matrixA_sq":
        return f"""/-- The corrected first generator has the required central
square in ambient row `{row.label}`. -/
theorem {row_name}_matrixA_sq :
    {matrix_a} ^ 2 =
      (ζ ^ {exponent_a2}) • {identity} := by
  simpa [pow_two, {row_name}_matrixA_sqTarget] using
    {row_name}_matrixA_sq_mul

"""
    if public_relation == "matrixB_fourth":
        return f"""/-- The corrected second generator has the required central fourth
power in ambient row `{row.label}`. -/
theorem {row_name}_matrixB_fourth :
    {matrix_b} ^ 4 =
      (ζ ^ {exponent_b4}) • {identity} := by
  have hB2 :
      {matrix_b} ^ 2 = {matrix_b2} := by
    simpa [pow_two] using {row_name}_matrixB_sq_mul
  calc
    {matrix_b} ^ 4 = ({matrix_b} ^ 2) ^ 2 := by
      simpa using
        (pow_mul {matrix_b} 2 2)
    _ = {matrix_b2} ^ 2 := by rw [hB2]
    _ = {matrix_b2} * {matrix_b2} := by rw [pow_two]
    _ = {row_name}_matrixB_fourthTarget :=
      {row_name}_matrixB_fourth_mul
    _ = (ζ ^ {exponent_b4}) • {identity} := by
      rfl

"""
    if public_relation == "matrixAB_fifth":
        return f"""/-- The corrected product of generators has the required central fifth
power in ambient row `{row.label}`. -/
theorem {row_name}_matrixAB_fifth :
    ({matrix_a} * {matrix_b}) ^ 5 =
      (ζ ^ {exponent_ab5}) • {identity} := by
  have hAB :
      {matrix_a} * {matrix_b} = {matrix_ab} :=
    {row_name}_matrixAB_mul
  have hAB2 :
      {matrix_ab} ^ 2 = {matrix_ab2} := by
    simpa [pow_two] using {row_name}_matrixAB_sq_mul
  have hAB4 :
      {matrix_ab2} ^ 2 = {matrix_ab4} := by
    simpa [pow_two] using {row_name}_matrixAB_fourth_mul
  calc
    ({matrix_a} * {matrix_b}) ^ 5 =
        ({matrix_a} * {matrix_b}) ^ 4 *
          ({matrix_a} * {matrix_b}) := by
      simpa using
        (pow_succ ({matrix_a} * {matrix_b}) 4)
    _ =
        (({matrix_a} * {matrix_b}) ^ 2) ^ 2 *
          ({matrix_a} * {matrix_b}) := by
      rw [show
        ({matrix_a} * {matrix_b}) ^ 4 =
          (({matrix_a} * {matrix_b}) ^ 2) ^ 2 by
            simpa using
              (pow_mul ({matrix_a} * {matrix_b}) 2 2)]
    _ = ({matrix_ab} ^ 2) ^ 2 * {matrix_ab} := by
      rw [hAB]
    _ = {matrix_ab2} ^ 2 * {matrix_ab} := by
      rw [hAB2]
    _ = {matrix_ab4} * {matrix_ab} := by
      rw [hAB4]
    _ = {row_name}_matrixAB_fifthTarget :=
      {row_name}_matrixAB_fifth_mul
    _ = (ζ ^ {exponent_ab5}) • {identity} := by
      rfl

"""
    if public_relation == "matrixABSquared_fifth":
        return f"""/-- The corrected `A B²` product has the required central fifth power
in ambient row `{row.label}`. -/
theorem {row_name}_matrixABSquared_fifth :
    ({matrix_a} * {matrix_b} ^ 2) ^ 5 =
      (ζ ^ {exponent_ab25}) • {identity} := by
  have hB2 :
      {matrix_b} ^ 2 = {matrix_b2} := by
    simpa [pow_two] using {row_name}_matrixB_sq_mul
  have hC :
      {matrix_a} * {matrix_b2} = {matrix_c} :=
    {row_name}_matrixABSquared_mul
  have hC2 :
      {matrix_c} ^ 2 = {matrix_c2} := by
    simpa [pow_two] using {row_name}_matrixABSquared_sq_mul
  have hC4 :
      {matrix_c2} ^ 2 = {matrix_c4} := by
    simpa [pow_two] using {row_name}_matrixABSquared_fourth_mul
  calc
    ({matrix_a} * {matrix_b} ^ 2) ^ 5 =
        ({matrix_a} * {matrix_b} ^ 2) ^ 4 *
          ({matrix_a} * {matrix_b} ^ 2) := by
      simpa using
        (pow_succ ({matrix_a} * {matrix_b} ^ 2) 4)
    _ =
        (({matrix_a} * {matrix_b} ^ 2) ^ 2) ^ 2 *
          ({matrix_a} * {matrix_b} ^ 2) := by
      rw [show
        ({matrix_a} * {matrix_b} ^ 2) ^ 4 =
          (({matrix_a} * {matrix_b} ^ 2) ^ 2) ^ 2 by
            simpa using
              (pow_mul ({matrix_a} * {matrix_b} ^ 2) 2 2)]
    _ = (({matrix_a} * {matrix_b2}) ^ 2) ^ 2 *
          ({matrix_a} * {matrix_b2}) := by
      rw [hB2]
    _ = (({matrix_c} ^ 2) ^ 2) * {matrix_c} := by
      rw [hC]
    _ = {matrix_c2} ^ 2 * {matrix_c} := by
      rw [hC2]
    _ = {matrix_c4} * {matrix_c} := by
      rw [hC4]
    _ = {row_name}_matrixABSquared_fifthTarget :=
      {row_name}_matrixABSquared_fifth_mul
    _ = (ζ ^ {exponent_ab25}) • {identity} := by
      rfl

"""
    raise ValueError(f"unexpected public relation {public_relation}")


def row_relation_module_stem(row: CharacterRow) -> str:
    return (
        "AlternatingSixFiveAmbientMatrixRelations"
        f"{upper_initial(lean_label(row.label))}"
    )


def render_row_complex_relation_part(
    row: CharacterRow,
    part: RelationPart,
    all_stages: list[MatrixMultiplicationStage],
) -> str:
    row_name = f"alternatingSixFiveAmbient_{lean_label(row.label)}"
    stages_by_suffix = {
        stage.name.removeprefix(row_name + "_"): stage
        for stage in all_stages
    }
    stages = [stages_by_suffix[suffix] for suffix in part.stage_suffixes]
    header = f"""/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import {data_import_for_row(row)}

/-!
# The {part.title} in ambient row `{row.label}`

This file is generated by `scripts/a6_character_matrices_to_lean.py`.
Each multiplication is split by matrix row or entry and checked with an
explicit quotient by `Φ₁₂₀`, keeping every command below the default
heartbeat limit.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

"""
    chunks = [header]
    for stage in stages:
        chunks.append(
            f"/-- Exact target matrix for the `{stage.name.removeprefix(row_name + '_')}` "
            f"multiplication step. -/\n"
            f"private def {stage.target_name} :\n"
            f"    Matrix (Fin {row.degree}) (Fin {row.degree}) ℂ :=\n"
            f"  {render_complex_stage_target(stage, row.degree)}\n\n"
        )
    for stage in stages:
        chunks.append(render_stage_proof(stage, row.degree))
    chunks.append(
        render_row_public_relation_part(row, part.public_relation)
    )
    chunks.append(FOOTER)
    return "".join(chunks)


def render_row_complex_relations_aggregate(row: CharacterRow) -> str:
    module_stem = row_relation_module_stem(row)
    imports = "\n".join(
        "import McKayConjecture.InductiveMcKay."
        f"{module_stem}{part.file_suffix}"
        for part in RELATION_PARTS
    )
    return f"""/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
{imports}

/-!
# Exact presentation relations for ambient row `{row.label}`

This generated compatibility module collects the four independently
compiled presentation-relation certificates for ambient row `{row.label}`.
-/
"""


def write_row_complex_relations(
    rows: list[CharacterRow],
    output_directory: Path,
    requested_label: str,
) -> None:
    selected = [row for row in rows if row.label == requested_label]
    if len(selected) != 1:
        raise ValueError(f"could not uniquely select row {requested_label}")
    row = selected[0]
    all_stages = build_matrix_multiplication_stages(row)
    module_stem = row_relation_module_stem(row)
    for part in RELATION_PARTS:
        path = output_directory / f"{module_stem}{part.file_suffix}.lean"
        path.write_text(
            render_row_complex_relation_part(row, part, all_stages),
            encoding="utf-8",
        )
    aggregate_path = output_directory / f"{module_stem}.lean"
    aggregate_path.write_text(
        render_row_complex_relations_aggregate(row),
        encoding="utf-8",
    )


def write_all_complex_relations(
    rows: list[CharacterRow],
    output_directory: Path,
) -> None:
    for row in rows:
        write_row_complex_relations(rows, output_directory, row.label)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output_directory", type=Path)
    parser.add_argument(
        "--relation-row",
        help=(
            "also generate the four exact presentation-relation parts "
            "and aggregate for one row"
        ),
    )
    parser.add_argument(
        "--all-relations",
        action="store_true",
        help=(
            "also generate the four exact presentation-relation parts "
            "and aggregates for every row"
        ),
    )
    arguments = parser.parse_args()
    rows = read_rows(arguments.input)
    verify_presentation_relations(rows)
    arguments.output_directory.mkdir(parents=True, exist_ok=True)
    write_data_files(rows, arguments.output_directory)
    if arguments.relation_row is not None:
        write_row_complex_relations(
            rows,
            arguments.output_directory,
            arguments.relation_row,
        )
    if arguments.all_relations:
        write_all_complex_relations(rows, arguments.output_directory)


if __name__ == "__main__":
    main()
