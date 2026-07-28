#!/usr/bin/env python3
"""Compute class-representative traces for ambient rows 19 and 20.

The trusted Lean proof rechecks every emitted identity.  This script only
extracts the already generated exact matrices and performs arithmetic in
`Q[zeta_120] / (Phi_120)`.  Generated matrix calculations are split into
independently compilable modules and wrapped to the Lean style width.
"""

from __future__ import annotations

import ast
import argparse
import importlib.util
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
BASE_GENERATOR_PATH = ROOT / "scripts" / "a6_character_matrices_to_lean.py"
MATRIX_DATA_PATH = (
    ROOT
    / "McKayConjecture"
    / "InductiveMcKay"
    / "AlternatingSixFiveAmbientMatrixDataDegreeEightNine.lean"
)

spec = importlib.util.spec_from_file_location(
    "a6_character_matrices_to_lean", BASE_GENERATOR_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("could not load the ambient matrix generator")
base = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = base
spec.loader.exec_module(base)


def parse_lean_cyclotomic_value(source: str) -> base.Polynomial:
    parsed = ast.parse(f"[{source}]", mode="eval")
    coefficients: dict[int, object] = {}
    for term in parsed.body.elts:
        if not isinstance(term, ast.Tuple) or len(term.elts) != 2:
            raise ValueError(f"invalid cyclotomic term: {ast.dump(term)}")
        coefficient = base.evaluate_expression(term.elts[0], {})
        if (
            len(coefficient.coefficients) > 1
            or (
                coefficient.coefficients
                and coefficient.coefficients[0][0] != 0
            )
        ):
            raise ValueError("cyclotomic coefficient is not rational")
        rational = (
            coefficient.coefficients[0][1]
            if coefficient.coefficients
            else 0
        )
        degree = ast.literal_eval(term.elts[1])
        coefficients[degree] = coefficients.get(degree, 0) + rational
    return base.Polynomial.from_dict(coefficients).reduce()


def extract_matrix(name: str) -> base.PolynomialMatrix:
    source = MATRIX_DATA_PATH.read_text()
    declaration = source.index(f"def {name} ")
    assignment = source.index(":=", declaration)
    start = source.index("![", assignment)
    cursor = start
    depth = 0
    while cursor < len(source):
        if source[cursor] == "[":
            depth += 1
            cursor += 1
            continue
        if source[cursor] == "]":
            depth -= 1
            cursor += 1
            if depth == 0:
                break
            continue
        cursor += 1
    if depth != 0:
        raise ValueError(f"unterminated matrix declaration {name}")
    matrix_source = source[start:cursor]
    values: list[base.Polynomial] = []

    def replace_value(match: re.Match[str]) -> str:
        values.append(parse_lean_cyclotomic_value(match.group(1)))
        return f"p{len(values) - 1}"

    python_source = re.sub(
        r"alternatingSixCyclotomicValue \[(.*?)\]",
        replace_value,
        matrix_source,
        flags=re.DOTALL,
    ).replace("![", "[")
    parsed = ast.parse(python_source, mode="eval")
    if not isinstance(parsed.body, ast.List):
        raise ValueError(f"{name} is not a matrix")
    matrix: base.PolynomialMatrix = []
    for row in parsed.body.elts:
        if not isinstance(row, ast.List):
            raise ValueError(f"{name} has a non-list row")
        parsed_row: list[base.Polynomial] = []
        for entry in row.elts:
            if not isinstance(entry, ast.Name) or not entry.id.startswith("p"):
                raise ValueError(f"unexpected matrix entry: {ast.dump(entry)}")
            parsed_row.append(values[int(entry.id[1:])])
        matrix.append(parsed_row)
    if not matrix or any(len(row) != len(matrix) for row in matrix):
        raise ValueError(f"{name} is not a nonempty square matrix")
    return matrix


def scalar_multiply(
    scalar: base.Polynomial, matrix: base.PolynomialMatrix
) -> base.PolynomialMatrix:
    return [
        [(scalar * entry).reduce() for entry in row]
        for row in matrix
    ]


def trace(matrix: base.PolynomialMatrix) -> base.Polynomial:
    return sum(
        (matrix[i][i] for i in range(len(matrix))),
        base.Polynomial.constant(0),
    ).reduce()


def trace_raw(matrix: base.PolynomialMatrix) -> base.Polynomial:
    return sum(
        (matrix[i][i] for i in range(len(matrix))),
        base.Polynomial.constant(0),
    )


def product(
    matrices: list[base.PolynomialMatrix],
    dimension: int,
) -> base.PolynomialMatrix:
    result = base.matrix_identity(dimension)
    for matrix in matrices:
        result = base.matrix_multiply(result, matrix)
    return result


def product_raw(
    matrices: list[base.PolynomialMatrix],
    dimension: int,
) -> base.PolynomialMatrix:
    result = base.matrix_identity(dimension)
    for matrix in matrices:
        result = base.matrix_multiply_raw(result, matrix)
    return result


def reduction_quotient(
    raw: base.Polynomial, target: base.Polynomial
) -> base.Polynomial:
    quotient, remainder = (raw - target).divmod_monic(base.PHI)
    if remainder != base.Polynomial.constant(0):
        raise ValueError("claimed trace is not a cyclotomic reduction")
    return quotient


def lean_polynomial_value(polynomial: base.Polynomial) -> str:
    """Render small rational constants without a cyclotomic wrapper."""

    coefficients = polynomial.coefficients
    if not coefficients:
        return "0"
    if len(coefficients) == 1 and coefficients[0][0] == 0:
        coefficient = coefficients[0][1]
        if coefficient.denominator == 1:
            return str(coefficient.numerator)
    return base.polynomial_to_lean(polynomial)


def lean_product(factors: list[str], indent: str) -> str:
    """Wrap a left-associated Lean product at multiplication signs."""

    return (f" *\n{indent}").join(factors)


def inverse_word(
    word: list[tuple[str, bool]],
    generators: dict[tuple[str, bool], base.PolynomialMatrix],
    dimension: int,
) -> base.PolynomialMatrix:
    return product(
        [generators[(name, not positive)] for name, positive in reversed(word)],
        dimension,
    )


LEAN_HEADER = """/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
"""

LEAN_NAMESPACE_OPEN = """
noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

"""

LEAN_NAMESPACE_CLOSE = """end InductiveMcKay
end McKayConjecture
"""


def write_long_word_certificates(
    row_number: int,
    matrix_a: base.PolynomialMatrix,
    matrix_b: base.PolynomialMatrix,
) -> None:
    output_directory = ROOT / "McKayConjecture" / "InductiveMcKay"
    dimension = len(matrix_a)
    row_label = f"row{row_number:02d}"
    lean_stem = f"alternatingSixAmbientRow{row_number:02d}"
    module_stem = f"AlternatingSixAmbientRow{row_number:02d}"
    a_name = f"alternatingSixFiveAmbient_{row_label}_matrixA"
    b_name = f"alternatingSixFiveAmbient_{row_label}_matrixB"
    target_names = {
        "ab": f"{lean_stem}LongMatrixAB",
        "abb": f"{lean_stem}LongMatrixABB",
        "abbb": f"{lean_stem}LongMatrixABBB",
        "prefix77": f"{lean_stem}LongPrefix77",
        "prefix79": f"{lean_stem}LongPrefix79",
    }
    targets: dict[str, base.PolynomialMatrix] = {}
    stages: list[tuple[str, base.MatrixMultiplicationStage]] = []

    def add_stage(
        key: str,
        file_suffix: str,
        theorem_stem: str,
        left_name: str,
        right_name: str,
        left: base.PolynomialMatrix,
        right: base.PolynomialMatrix,
    ) -> base.PolynomialMatrix:
        target, quotient = base.matrix_multiply_certificate(left, right)
        targets[key] = target
        stage = base.MatrixMultiplicationStage(
            name=theorem_stem,
            left_name=left_name,
            right_name=right_name,
            target_name=target_names[key],
            left=left,
            right=right,
            target=target,
            quotient=quotient,
        )
        stages.append((file_suffix, stage))
        return target

    matrix_ab = add_stage(
        "ab",
        "AB",
        f"{lean_stem}_longMatrixAB",
        a_name,
        b_name,
        matrix_a,
        matrix_b,
    )
    matrix_abb = add_stage(
        "abb",
        "ABB",
        f"{lean_stem}_longMatrixABB",
        target_names["ab"],
        b_name,
        matrix_ab,
        matrix_b,
    )
    matrix_abbb = add_stage(
        "abbb",
        "ABBB",
        f"{lean_stem}_longMatrixABBB",
        target_names["abb"],
        b_name,
        matrix_abb,
        matrix_b,
    )
    prefix77 = add_stage(
        "prefix77",
        "Prefix77",
        f"{lean_stem}_longPrefix77",
        target_names["ab"],
        target_names["abb"],
        matrix_ab,
        matrix_abb,
    )
    prefix79 = add_stage(
        "prefix79",
        "Prefix79",
        f"{lean_stem}_longPrefix79",
        target_names["ab"],
        target_names["abbb"],
        matrix_ab,
        matrix_abbb,
    )

    data_chunks = [
        LEAN_HEADER,
        "import McKayConjecture.InductiveMcKay."
        "AlternatingSixFiveAmbientMatrixDataDegreeEightNine\n",
        f"\n/-!\n# Reduced matrix data for the two long row-{row_number} "
        "class words\n\n"
        "This file is generated by `scripts/a6_row19_representative_traces.py`.\n"
        "Lean separately checks every multiplication producing these matrices.\n"
        "-/\n",
        LEAN_NAMESPACE_OPEN,
    ]
    descriptions = {
        "ab": f"Reduced row-{row_number} matrix for `ab`.",
        "abb": f"Reduced row-{row_number} matrix for `ab²`.",
        "abbb": f"Reduced row-{row_number} matrix for `ab³`.",
        "prefix77": "Reduced product `(ab)(ab²)`.",
        "prefix79": "Reduced product `(ab)(ab³)`.",
    }
    for key in ("ab", "abb", "abbb", "prefix77", "prefix79"):
        data_chunks.extend(
            [
                f"/-- {descriptions[key]} -/\n",
                f"def {target_names[key]} :\n",
                f"    Matrix (Fin {dimension}) (Fin {dimension}) ℂ :=\n",
                f"  {base.matrix_to_lean(targets[key])}\n\n",
            ]
        )
    data_chunks.append(LEAN_NAMESPACE_CLOSE)
    (
        output_directory
        / f"{module_stem}LongWordData.lean"
    ).write_text("".join(data_chunks), encoding="utf-8")

    proof_modules: list[str] = []
    for file_suffix, stage in stages:
        module_name = f"{module_stem}LongWordProduct{file_suffix}"
        proof_modules.append(module_name)
        proof = base.render_stage_proof(stage, dimension)
        proof = proof.replace(
            f"private theorem {stage.name}_mul",
            f"theorem {stage.name}_mul",
        )
        content = "".join(
            [
                LEAN_HEADER,
                "import Mathlib.Tactic.LinearCombination\n",
                "import McKayConjecture.InductiveMcKay."
                f"{module_stem}LongWordData\n",
                f"\n/-!\n# One checked row-{row_number} long-word "
                "multiplication\n\n"
                f"This split generated module keeps each {dimension} by "
                f"{dimension} multiplication\n"
                "independently compilable under the default resource limits.\n"
                "-/\n",
                LEAN_NAMESPACE_OPEN,
                proof,
                LEAN_NAMESPACE_CLOSE,
            ]
        )
        (output_directory / f"{module_name}.lean").write_text(
            content, encoding="utf-8"
        )

    aggregate_chunks = [LEAN_HEADER]
    for module_name in proof_modules:
        aggregate_chunks.append(
            "import McKayConjecture.InductiveMcKay."
            f"{module_name}\n"
        )
    aggregate_chunks.extend(
        [
            f"\n/-!\n# Checked products for the two long row-{row_number} "
            "class words\n-/\n",
            LEAN_NAMESPACE_OPEN,
            f"/-- The original row-{row_number} matrices multiply to the "
            "reduced `ab` "
            "matrix. -/\n",
            f"theorem {lean_stem}_longMatrixAB_eq :\n",
            f"    {a_name} *\n",
            f"        {b_name} =\n",
            f"      {target_names['ab']} :=\n",
            f"  {lean_stem}_longMatrixAB_mul\n\n",
            "/-- Reduced matrix for the left-associated word `ab²`. -/\n",
            f"theorem {lean_stem}_longMatrixABB_eq :\n",
            f"    ({a_name} *\n",
            f"      {b_name}) *\n",
            f"      {b_name} =\n",
            f"      {target_names['abb']} := by\n",
            f"  rw [{lean_stem}_longMatrixAB_eq,\n",
            f"    {lean_stem}_longMatrixABB_mul]\n\n",
            "/-- Reduced matrix for the left-associated word `ab³`. -/\n",
            f"theorem {lean_stem}_longMatrixABBB_eq :\n",
            f"    (({a_name} *\n",
            f"        {b_name}) *\n",
            f"      {b_name}) *\n",
            f"      {b_name} =\n",
            f"      {target_names['abbb']} := by\n",
            f"  rw [{lean_stem}_longMatrixABB_eq,\n",
            f"    {lean_stem}_longMatrixABBB_mul]\n\n",
            LEAN_NAMESPACE_CLOSE,
        ]
    )
    (
        output_directory
        / f"{module_stem}LongWordProducts.lean"
    ).write_text("".join(aggregate_chunks), encoding="utf-8")

    trace77 = trace(base.matrix_multiply(prefix77, matrix_abbb))
    trace79 = trace(base.matrix_multiply(prefix79, matrix_abb))

    def trace_certificate(
        theorem_name: str,
        left_name: str,
        right_name: str,
        left: base.PolynomialMatrix,
        right: base.PolynomialMatrix,
        target: base.Polynomial,
    ) -> str:
        raw_trace = trace_raw(base.matrix_multiply_raw(left, right))
        quotient = reduction_quotient(raw_trace, target)
        quotient_expression = base.polynomial_expression_to_lean(quotient)
        target_source = lean_polynomial_value(target)
        chunks = []
        if quotient.coefficients:
            chunks.extend(
                [
                    "-- Cyclotomic reduction uses a generated fallback "
                    "with the opposite sign.\n",
                    "set_option linter.flexible false in\n",
                    "set_option linter.unusedTactic false in\n",
                    "set_option linter.unreachableTactic false in\n",
                ]
            )
        chunks.extend([
            f"theorem {theorem_name} :\n",
            f"    ({left_name} *\n",
            f"      {right_name}).trace =\n",
            f"      {target_source} := by\n",
            "  change\n",
            f"    (∑ i : Fin {dimension},\n",
            f"      ({left_name} *\n",
            f"        {right_name}) i i) =\n",
            f"      {target_source}\n",
            "  simp_rw [Matrix.mul_apply]\n",
            "  simp [\n",
            f"    {left_name},\n",
            f"    {right_name},\n",
            "    alternatingSixCyclotomicValue,\n",
            "    Fin.sum_univ_succ\n",
            "  ]",
        ])
        if not quotient.coefficients:
            chunks.extend(["; ring\n\n"])
            return "".join(chunks)
        chunks.extend(
            [
                "\n",
                "  first\n",
                "  | linear_combination\n",
                f"      {quotient_expression} *\n",
                "        alternatingSixComplexCyclotomicRoot_relation\n",
                "  | linear_combination\n",
                f"      (-({quotient_expression})) *\n",
                "        alternatingSixComplexCyclotomicRoot_relation\n\n",
            ]
        )
        return "".join(chunks)

    positive77_factors = [
        a_name, b_name, a_name, b_name, b_name,
        a_name, b_name, b_name, b_name,
    ]
    positive79_factors = [
        a_name, b_name, a_name, b_name, b_name,
        b_name, a_name, b_name, b_name,
    ]
    ab_group = f"({a_name} *\n          {b_name})"
    abb_group = (
        f"(({a_name} *\n"
        f"            {b_name}) *\n"
        f"          {b_name})"
    )
    abbb_group = (
        f"((({a_name} *\n"
        f"              {b_name}) *\n"
        f"            {b_name}) *\n"
        f"          {b_name})"
    )
    trace77_source = lean_polynomial_value(trace77)
    trace79_source = lean_polynomial_value(trace79)
    trace_chunks = [
        LEAN_HEADER,
        "import Mathlib.Tactic.LinearCombination\n",
        "import McKayConjecture.InductiveMcKay."
        f"{module_stem}LongWordProducts\n",
        f"\n/-!\n# Exact traces of the two long positive row-{row_number} "
        "words\n-/\n",
        LEAN_NAMESPACE_OPEN,
        trace_certificate(
            f"{lean_stem}_longState77Reduced_trace",
            target_names["prefix77"],
            target_names["abbb"],
            prefix77,
            matrix_abbb,
            trace77,
        ),
        trace_certificate(
            f"{lean_stem}_longState79Reduced_trace",
            target_names["prefix79"],
            target_names["abb"],
            prefix79,
            matrix_abb,
            trace79,
        ),
        "/-- Trace of the positive word `ababbabbb`. -/\n",
        f"theorem {lean_stem}_positiveState77_trace :\n",
        "    (",
        lean_product(positive77_factors, "      "),
        ").trace =\n",
        f"      {trace77_source} := by\n",
        "  rw [show\n",
        "    ",
        lean_product(positive77_factors, "      "),
        " =\n",
        f"        {ab_group} *\n",
        f"        {abb_group} *\n",
        f"        {abbb_group} by\n",
        "      simp only [Matrix.mul_assoc]]\n",
        f"  rw [{lean_stem}_longMatrixABBB_eq,\n",
        f"    {lean_stem}_longMatrixABB_eq,\n",
        f"    {lean_stem}_longMatrixAB_eq,\n",
        f"    {lean_stem}_longPrefix77_mul]\n",
        f"  exact {lean_stem}_longState77Reduced_trace\n\n",
        "/-- Trace of the positive word `ababbbabb`. -/\n",
        f"theorem {lean_stem}_positiveState79_trace :\n",
        "    (",
        lean_product(positive79_factors, "      "),
        ").trace =\n",
        f"      {trace79_source} := by\n",
        "  rw [show\n",
        "    ",
        lean_product(positive79_factors, "      "),
        " =\n",
        f"        {ab_group} *\n",
        f"        {abbb_group} *\n",
        f"        {abb_group} by\n",
        "      simp only [Matrix.mul_assoc]]\n",
        f"  rw [{lean_stem}_longMatrixABBB_eq,\n",
        f"    {lean_stem}_longMatrixABB_eq,\n",
        f"    {lean_stem}_longMatrixAB_eq,\n",
        f"    {lean_stem}_longPrefix79_mul]\n",
        f"  exact {lean_stem}_longState79Reduced_trace\n\n",
        LEAN_NAMESPACE_CLOSE,
    ]
    (
        output_directory
        / f"{module_stem}LongWordTraces.lean"
    ).write_text("".join(trace_chunks), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--row",
        type=int,
        choices=(19, 20),
        default=19,
        help="ambient ordinary row to evaluate (default: 19)",
    )
    parser.add_argument(
        "--write-lean",
        action="store_true",
        help="write the split kernel-checked long-word certificate modules",
    )
    arguments = parser.parse_args()
    row_label = f"row{arguments.row:02d}"
    matrix_a = extract_matrix(
        f"alternatingSixFiveAmbient_{row_label}_matrixA"
    )
    matrix_b = extract_matrix(
        f"alternatingSixFiveAmbient_{row_label}_matrixB"
    )
    dimension = len(matrix_a)
    if arguments.write_lean:
        write_long_word_certificates(arguments.row, matrix_a, matrix_b)
    central_scalar = base.Polynomial.constant(
        -1 if arguments.row == 19 else 1
    )
    matrix_a_inverse = scalar_multiply(central_scalar, matrix_a)
    matrix_b_inverse = scalar_multiply(
        central_scalar, base.matrix_power(matrix_b, 3)
    )
    generators = {
        ("a", True): matrix_a,
        ("a", False): matrix_a_inverse,
        ("b", True): matrix_b,
        ("b", False): matrix_b_inverse,
    }
    words: list[tuple[str, list[tuple[str, bool]]]] = [
        ("identity", []),
        ("a", [("a", True)]),
        ("b", [("b", True)]),
        ("ab", [("a", True), ("b", True)]),
        ("abb", [("a", True), ("b", True), ("b", True)]),
        (
            "state77",
            [
                ("a", True),
                ("b", True),
                ("a", True),
                ("b", True),
                ("b", True),
                ("a", True),
                ("b", False),
            ],
        ),
        (
            "state79",
            [
                ("a", True),
                ("b", True),
                ("a", True),
                ("b", False),
                ("a", True),
                ("b", True),
                ("b", True),
            ],
        ),
    ]
    weights = [6, 270, 540, 432, 432, 240, 240]
    norm = base.Polynomial.constant(0)
    trace_values: dict[str, base.Polynomial] = {}
    inverse_trace_values: dict[str, base.Polynomial] = {}
    pairing_values: dict[str, base.Polynomial] = {}
    for (name, word), weight in zip(words, weights, strict=True):
        matrices = [generators[letter] for letter in word]
        value = trace(product(matrices, dimension))
        trace_values[name] = value
        raw_value = trace_raw(product_raw(matrices, dimension))
        quotient = reduction_quotient(raw_value, value)
        inverse_value = trace(inverse_word(word, generators, dimension))
        inverse_trace_values[name] = inverse_value
        pairing = (value * inverse_value).reduce()
        pairing_values[name] = pairing
        norm = (norm + weight * pairing).reduce()
        print(f"{name}_trace = {base.polynomial_to_lean(value)}")
        print(
            f"{name}_trace_quotient = "
            f"{base.polynomial_expression_to_lean(quotient)}"
        )
        print(
            f"{name}_inverse_trace = "
            f"{base.polynomial_to_lean(inverse_value)}"
        )
        print(f"{name}_pairing = {base.polynomial_to_lean(pairing)}")
    noncentral_pairing_sum = (
        pairing_values["ab"] + pairing_values["abb"]
    ).reduce()
    noncentral_pairing_quotient = reduction_quotient(
        trace_values["ab"] * inverse_trace_values["ab"]
        + trace_values["abb"] * inverse_trace_values["abb"],
        noncentral_pairing_sum,
    )
    print(
        "noncentral_pairing_sum = "
        f"{base.polynomial_to_lean(noncentral_pairing_sum)}"
    )
    print(
        "noncentral_pairing_quotient = "
        f"{base.polynomial_expression_to_lean(noncentral_pairing_quotient)}"
    )
    print(f"weighted_norm = {base.polynomial_to_lean(norm)}")


if __name__ == "__main__":
    main()
