#!/usr/bin/env python3
"""Emit split class-representative trace certificates for ATLAS power 2.

The two final long-word products are materialized as reduced matrices and
certified in their own modules.  Their traces then inspect only twelve
diagonal entries instead of expanding a full matrix product inside a trace.

The final audit computes all seven base-word traces and inverse pairings in
`Q[zeta_120] / (Phi_120)`.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
HELPER_PATH = ROOT / "scripts" / "a6_row19_representative_traces.py"
MATRIX_DATA_MODULE = "AlternatingSixFiveAmbientMatrixDataDegreeTwelve"
MODULE_STEM = "AlternatingSixAmbientAtlasTwelvePowerTwo"
LEAN_STEM = "alternatingSixAmbientAtlasTwelvePowerTwo"
MATRIX_STEM = "alternatingSixFiveAmbient_atlas12Power2"

spec = importlib.util.spec_from_file_location(
    "a6_row19_representative_traces", HELPER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("could not load the class-trace generator")
helper = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = helper
spec.loader.exec_module(helper)
base = helper.base
helper.MATRIX_DATA_PATH = (
    ROOT
    / "McKayConjecture"
    / "InductiveMcKay"
    / f"{MATRIX_DATA_MODULE}.lean"
)


def write_long_word_certificates(
    matrix_a: base.PolynomialMatrix,
    matrix_b: base.PolynomialMatrix,
) -> None:
    """Write seven independently checked multiplication stages and traces."""

    output_directory = ROOT / "McKayConjecture" / "InductiveMcKay"
    dimension = len(matrix_a)
    a_name = f"{MATRIX_STEM}_matrixA"
    b_name = f"{MATRIX_STEM}_matrixB"
    target_names = {
        key: f"{LEAN_STEM}{suffix}"
        for key, suffix in {
            "ab": "LongMatrixAB",
            "abb": "LongMatrixABB",
            "abbb": "LongMatrixABBB",
            "prefix77": "LongPrefix77",
            "prefix79": "LongPrefix79",
            "state77": "LongState77",
            "state79": "LongState79",
        }.items()
    }
    targets: dict[str, base.PolynomialMatrix] = {}
    stages: list[tuple[str, base.MatrixMultiplicationStage]] = []

    def add_stage(
        key: str,
        file_suffix: str,
        theorem_suffix: str,
        left_name: str,
        right_name: str,
        left: base.PolynomialMatrix,
        right: base.PolynomialMatrix,
    ) -> base.PolynomialMatrix:
        target, quotient = base.matrix_multiply_certificate(left, right)
        targets[key] = target
        stages.append(
            (
                file_suffix,
                base.MatrixMultiplicationStage(
                    name=f"{LEAN_STEM}_{theorem_suffix}",
                    left_name=left_name,
                    right_name=right_name,
                    target_name=target_names[key],
                    left=left,
                    right=right,
                    target=target,
                    quotient=quotient,
                ),
            )
        )
        return target

    matrix_ab = add_stage(
        "ab", "AB", "longMatrixAB", a_name, b_name, matrix_a, matrix_b
    )
    matrix_abb = add_stage(
        "abb",
        "ABB",
        "longMatrixABB",
        target_names["ab"],
        b_name,
        matrix_ab,
        matrix_b,
    )
    matrix_abbb = add_stage(
        "abbb",
        "ABBB",
        "longMatrixABBB",
        target_names["abb"],
        b_name,
        matrix_abb,
        matrix_b,
    )
    prefix77 = add_stage(
        "prefix77",
        "P77",
        "longPrefix77",
        target_names["ab"],
        target_names["abb"],
        matrix_ab,
        matrix_abb,
    )
    prefix79 = add_stage(
        "prefix79",
        "P79",
        "longPrefix79",
        target_names["ab"],
        target_names["abbb"],
        matrix_ab,
        matrix_abbb,
    )
    state77 = add_stage(
        "state77",
        "State77",
        "longState77",
        target_names["prefix77"],
        target_names["abbb"],
        prefix77,
        matrix_abbb,
    )
    state79 = add_stage(
        "state79",
        "State79",
        "longState79",
        target_names["prefix79"],
        target_names["abb"],
        prefix79,
        matrix_abb,
    )

    descriptions = {
        "ab": "Reduced matrix for `ab`.",
        "abb": "Reduced matrix for `ab²`.",
        "abbb": "Reduced matrix for `ab³`.",
        "prefix77": "Reduced product `(ab)(ab²)`.",
        "prefix79": "Reduced product `(ab)(ab³)`.",
        "state77": "Reduced matrix for the positive state-77 word.",
        "state79": "Reduced matrix for the positive state-79 word.",
    }
    data_chunks = [
        helper.LEAN_HEADER,
        "import McKayConjecture.InductiveMcKay."
        f"{MATRIX_DATA_MODULE}\n",
        "\n/-!\n# Reduced matrix data for the ATLAS power-2 long words\n\n",
        "Every multiplication producing these matrices is checked in a "
        "separate module.\n-/\n",
        helper.LEAN_NAMESPACE_OPEN,
    ]
    for key in (
        "ab",
        "abb",
        "abbb",
        "prefix77",
        "prefix79",
        "state77",
        "state79",
    ):
        data_chunks.extend(
            [
                f"/-- {descriptions[key]} -/\n",
                f"def {target_names[key]} :\n",
                f"    Matrix (Fin {dimension}) (Fin {dimension}) ℂ :=\n",
                f"  {base.matrix_to_lean(targets[key])}\n\n",
            ]
        )
    data_chunks.append(helper.LEAN_NAMESPACE_CLOSE)
    (output_directory / f"{MODULE_STEM}LongWordData.lean").write_text(
        "".join(data_chunks), encoding="utf-8"
    )

    proof_modules: list[str] = []
    for file_suffix, stage in stages:
        module_name = f"{MODULE_STEM}LongWordProduct{file_suffix}"
        proof_modules.append(module_name)
        proof = base.render_stage_proof(stage, dimension)
        proof = proof.replace(
            f"private theorem {stage.name}_mul",
            f"theorem {stage.name}_mul",
        )
        content = "".join(
            [
                helper.LEAN_HEADER,
                "import Mathlib.Tactic.LinearCombination\n",
                "import McKayConjecture.InductiveMcKay."
                f"{MODULE_STEM}LongWordData\n",
                "\n/-!\n# One checked ATLAS power-2 long-word "
                "multiplication\n\n",
                "This split module is independently compilable under the "
                "default limits.\n-/\n",
                helper.LEAN_NAMESPACE_OPEN,
                proof,
                helper.LEAN_NAMESPACE_CLOSE,
            ]
        )
        (output_directory / f"{module_name}.lean").write_text(
            content, encoding="utf-8"
        )

    aggregate_chunks = [helper.LEAN_HEADER]
    for module_name in proof_modules:
        aggregate_chunks.append(
            "import McKayConjecture.InductiveMcKay."
            f"{module_name}\n"
        )
    aggregate_chunks.extend(
        [
            "\n/-!\n# Checked products for the ATLAS power-2 long words\n-/\n",
            helper.LEAN_NAMESPACE_OPEN,
            "/-- The original matrices multiply to the reduced `ab` "
            "matrix. -/\n",
            f"theorem {LEAN_STEM}_longMatrixAB_eq :\n",
            f"    {a_name} *\n",
            f"        {b_name} =\n",
            f"      {target_names['ab']} :=\n",
            f"  {LEAN_STEM}_longMatrixAB_mul\n\n",
            "/-- Reduced matrix for the left-associated word `ab²`. -/\n",
            f"theorem {LEAN_STEM}_longMatrixABB_eq :\n",
            f"    ({a_name} *\n",
            f"      {b_name}) *\n",
            f"      {b_name} =\n",
            f"      {target_names['abb']} := by\n",
            f"  rw [{LEAN_STEM}_longMatrixAB_eq,\n",
            f"    {LEAN_STEM}_longMatrixABB_mul]\n\n",
            "/-- Reduced matrix for the left-associated word `ab³`. -/\n",
            f"theorem {LEAN_STEM}_longMatrixABBB_eq :\n",
            f"    (({a_name} *\n",
            f"        {b_name}) *\n",
            f"      {b_name}) *\n",
            f"      {b_name} =\n",
            f"      {target_names['abbb']} := by\n",
            f"  rw [{LEAN_STEM}_longMatrixABB_eq,\n",
            f"    {LEAN_STEM}_longMatrixABBB_mul]\n\n",
            helper.LEAN_NAMESPACE_CLOSE,
        ]
    )
    (output_directory / f"{MODULE_STEM}LongWordProducts.lean").write_text(
        "".join(aggregate_chunks), encoding="utf-8"
    )

    def explicit_trace_certificate(
        theorem_name: str,
        matrix_name: str,
        matrix: base.PolynomialMatrix,
    ) -> str:
        value = helper.trace(matrix)
        quotient = helper.reduction_quotient(
            helper.trace_raw(matrix), value
        )
        target = helper.lean_polynomial_value(value)
        chunks = [
            f"theorem {theorem_name} :\n",
            f"    {matrix_name}.trace =\n",
            f"      {target} := by\n",
            "  change\n",
            f"    (∑ i : Fin {dimension}, {matrix_name} i i) =\n",
            f"      {target}\n",
            "  simp [\n",
            f"    {matrix_name},\n",
            "    alternatingSixCyclotomicValue,\n",
            "    Fin.sum_univ_succ\n",
            "  ]",
        ]
        if not quotient.coefficients:
            chunks.extend(["\n  all_goals ring\n\n"])
            return "".join(chunks)
        chunks.extend(
            [
                "\n",
                base.render_stage_entry_tactic(quotient, indent="  "),
                "\n",
            ]
        )
        return "".join(chunks)

    positive77_factors = [
        a_name,
        b_name,
        a_name,
        b_name,
        b_name,
        a_name,
        b_name,
        b_name,
        b_name,
    ]
    positive79_factors = [
        a_name,
        b_name,
        a_name,
        b_name,
        b_name,
        b_name,
        a_name,
        b_name,
        b_name,
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
    trace77 = helper.lean_polynomial_value(helper.trace(state77))
    trace79 = helper.lean_polynomial_value(helper.trace(state79))
    trace_chunks = [
        helper.LEAN_HEADER,
        "import Mathlib.Tactic.LinearCombination\n",
        "import McKayConjecture.InductiveMcKay."
        f"{MODULE_STEM}LongWordProducts\n",
        "\n/-!\n# Exact traces of the ATLAS power-2 long words\n-/\n",
        helper.LEAN_NAMESPACE_OPEN,
        explicit_trace_certificate(
            f"{LEAN_STEM}_longState77Reduced_trace",
            target_names["state77"],
            state77,
        ),
        explicit_trace_certificate(
            f"{LEAN_STEM}_longState79Reduced_trace",
            target_names["state79"],
            state79,
        ),
        "/-- Trace of the positive word `ababbabbb`. -/\n",
        f"theorem {LEAN_STEM}_positiveState77_trace :\n",
        "    (",
        helper.lean_product(positive77_factors, "      "),
        ").trace =\n",
        f"      {trace77} := by\n",
        "  rw [show\n",
        "    ",
        helper.lean_product(positive77_factors, "      "),
        " =\n",
        f"        {ab_group} *\n",
        f"        {abb_group} *\n",
        f"        {abbb_group} by\n",
        "      simp only [Matrix.mul_assoc]]\n",
        f"  rw [{LEAN_STEM}_longMatrixABBB_eq,\n",
        f"    {LEAN_STEM}_longMatrixABB_eq,\n",
        f"    {LEAN_STEM}_longMatrixAB_eq,\n",
        f"    {LEAN_STEM}_longPrefix77_mul,\n",
        f"    {LEAN_STEM}_longState77_mul]\n",
        f"  exact {LEAN_STEM}_longState77Reduced_trace\n\n",
        "/-- Trace of the positive word `ababbbabb`. -/\n",
        f"theorem {LEAN_STEM}_positiveState79_trace :\n",
        "    (",
        helper.lean_product(positive79_factors, "      "),
        ").trace =\n",
        f"      {trace79} := by\n",
        "  rw [show\n",
        "    ",
        helper.lean_product(positive79_factors, "      "),
        " =\n",
        f"        {ab_group} *\n",
        f"        {abbb_group} *\n",
        f"        {abb_group} by\n",
        "      simp only [Matrix.mul_assoc]]\n",
        f"  rw [{LEAN_STEM}_longMatrixABBB_eq,\n",
        f"    {LEAN_STEM}_longMatrixABB_eq,\n",
        f"    {LEAN_STEM}_longMatrixAB_eq,\n",
        f"    {LEAN_STEM}_longPrefix79_mul,\n",
        f"    {LEAN_STEM}_longState79_mul]\n",
        f"  exact {LEAN_STEM}_longState79Reduced_trace\n\n",
        helper.LEAN_NAMESPACE_CLOSE,
    ]
    (output_directory / f"{MODULE_STEM}LongWordTraces.lean").write_text(
        "".join(trace_chunks), encoding="utf-8"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write-lean",
        action="store_true",
        help="write the split kernel-checked long-word certificate modules",
    )
    arguments = parser.parse_args()

    matrix_a = helper.extract_matrix(f"{MATRIX_STEM}_matrixA")
    matrix_b = helper.extract_matrix(f"{MATRIX_STEM}_matrixB")
    dimension = len(matrix_a)
    if arguments.write_lean:
        write_long_word_certificates(matrix_a, matrix_b)

    matrix_a_inverse = helper.scalar_multiply(
        base.Polynomial.monomial(20, 1), matrix_a
    )
    matrix_b_inverse = helper.scalar_multiply(
        base.Polynomial.monomial(60, 1),
        base.matrix_power(matrix_b, 3),
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
    for (name, word), weight in zip(words, weights, strict=True):
        value = helper.trace(
            helper.product([generators[letter] for letter in word], dimension)
        )
        inverse_value = helper.trace(
            helper.inverse_word(word, generators, dimension)
        )
        pairing = (value * inverse_value).reduce()
        norm = (norm + weight * pairing).reduce()
        print(f"{name}_trace = {base.polynomial_to_lean(value)}")
        print(
            f"{name}_inverse_trace = "
            f"{base.polynomial_to_lean(inverse_value)}"
        )
        print(f"{name}_pairing = {base.polynomial_to_lean(pairing)}")
    print(f"weighted_norm = {base.polynomial_to_lean(norm)}")


if __name__ == "__main__":
    main()
