#!/usr/bin/env python3
"""Compute and emit representative traces for ATLAS degree 12, power 1.

The long class words are checked through five split matrix products. This
keeps every generated Lean module within the stock heartbeat budget while
leaving the shared row generator unchanged.

The final audit computes the seven base-word traces, their inverse traces,
and the class-size weighted norm in `Q[zeta_120] / (Phi_120)`.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
HELPER_PATH = ROOT / "scripts" / "a6_row19_representative_traces.py"
MATRIX_DATA_MODULE = "AlternatingSixFiveAmbientMatrixDataDegreeTwelve"
DUMMY_ROW = 1201
DUMMY_MODULE_STEM = "AlternatingSixAmbientRow1201"
TARGET_MODULE_STEM = "AlternatingSixAmbientAtlas12P1"
DUMMY_LEAN_STEM = "alternatingSixAmbientRow1201"
TARGET_LEAN_STEM = "alternatingSixAmbientAtlas12P1"
DUMMY_MATRIX_STEM = "alternatingSixFiveAmbient_row1201"
TARGET_MATRIX_STEM = "alternatingSixFiveAmbient_atlas12Power1"
LONG_WORD_SUFFIXES = (
    "LongWordData",
    "LongWordProductAB",
    "LongWordProductABB",
    "LongWordProductABBB",
    "LongWordProductPrefix77",
    "LongWordProductPrefix79",
    "LongWordProducts",
    "LongWordTraces",
)

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


def polynomial(terms: list[tuple[int, int]]) -> base.Polynomial:
    """Build and reduce a sparse cyclotomic value."""

    value = base.Polynomial.constant(0)
    for coefficient, degree in terms:
        value += base.Polynomial.monomial(degree, coefficient)
    return value.reduce()


def write_long_word_certificates(
    matrix_a: base.PolynomialMatrix,
    matrix_b: base.PolynomialMatrix,
) -> None:
    """Generate through a private dummy row stem, then rename explicitly."""

    helper.write_long_word_certificates(DUMMY_ROW, matrix_a, matrix_b)
    output_directory = ROOT / "McKayConjecture" / "InductiveMcKay"
    for suffix in LONG_WORD_SUFFIXES:
        source_path = output_directory / f"{DUMMY_MODULE_STEM}{suffix}.lean"
        target_path = output_directory / f"{TARGET_MODULE_STEM}{suffix}.lean"
        source = source_path.read_text(encoding="utf-8")
        rewritten = (
            source.replace(
                "scripts/a6_row19_representative_traces.py",
                "scripts/a6_atlas12_power1_representative_traces.py",
            )
            .replace(DUMMY_MODULE_STEM, TARGET_MODULE_STEM)
            .replace(DUMMY_LEAN_STEM, TARGET_LEAN_STEM)
            .replace(DUMMY_MATRIX_STEM, TARGET_MATRIX_STEM)
            .replace("row-1201", "ATLAS degree-12 power-one")
            .replace(
                "AlternatingSixFiveAmbientMatrixDataDegreeEightNine",
                MATRIX_DATA_MODULE,
            )
            .replace("  simp only [\n", "  simp [\n")
            .replace("  ]; ring\n", "  ]\n  all_goals ring\n")
        )
        target_path.write_text(rewritten, encoding="utf-8")
        source_path.unlink()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write-lean",
        action="store_true",
        help="write the split kernel-checked long-word certificate modules",
    )
    arguments = parser.parse_args()

    matrix_a = helper.extract_matrix(
        "alternatingSixFiveAmbient_atlas12Power1_matrixA"
    )
    matrix_b = helper.extract_matrix(
        "alternatingSixFiveAmbient_atlas12Power1_matrixB"
    )
    dimension = len(matrix_a)
    if arguments.write_lean:
        write_long_word_certificates(matrix_a, matrix_b)

    # Here a^2 = zeta^20 and b^4 = zeta^60. Thus
    # a^-1 = zeta^100 a and b^-1 = zeta^60 b^3.
    matrix_a_inverse = helper.scalar_multiply(
        base.Polynomial.monomial(100), matrix_a
    )
    matrix_b_inverse = helper.scalar_multiply(
        base.Polynomial.monomial(60),
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
    inverse_values: dict[str, base.Polynomial] = {}
    values: dict[str, base.Polynomial] = {}
    for (name, word), weight in zip(words, weights, strict=True):
        matrices = [generators[letter] for letter in word]
        value = helper.trace(helper.product(matrices, dimension))
        inverse_value = helper.trace(
            helper.inverse_word(word, generators, dimension)
        )
        pairing = (value * inverse_value).reduce()
        norm = (norm + weight * pairing).reduce()
        values[name] = value
        inverse_values[name] = inverse_value
        print(f"{name}_trace = {base.polynomial_to_lean(value)}")
        print(
            f"{name}_inverse_trace = "
            f"{base.polynomial_to_lean(inverse_value)}"
        )
        print(f"{name}_pairing = {base.polynomial_to_lean(pairing)}")

    expected_ab_inverse = polynomial([(1, 4), (-1, 16)])
    expected_abb_inverse = polynomial(
        [
            (1, 0),
            (1, 4),
            (-1, 8),
            (-1, 12),
            (-1, 16),
            (-1, 20),
            (1, 28),
        ]
    )
    print(
        "ab_inverse_expected_match = "
        f"{inverse_values['ab'] == expected_ab_inverse}"
    )
    print(
        "abb_inverse_expected_match = "
        f"{inverse_values['abb'] == expected_abb_inverse}"
    )
    combined_pairing_quotient = helper.reduction_quotient(
        values["ab"] * expected_ab_inverse
        + values["abb"] * expected_abb_inverse,
        base.Polynomial.constant(3),
    )
    eta = base.Polynomial.monomial(20)
    central_pairing_quotient = helper.reduction_quotient(
        eta ** 4 * values["ab"] ** 2
        + eta ** 2 * values["abb"] ** 2,
        base.Polynomial.constant(3),
    )
    print(
        "combined_pairing_quotient = "
        f"{base.polynomial_expression_to_lean(combined_pairing_quotient)}"
    )
    print(
        "central_pairing_quotient = "
        f"{base.polynomial_expression_to_lean(central_pairing_quotient)}"
    )
    print(f"weighted_norm = {base.polynomial_to_lean(norm)}")


if __name__ == "__main__":
    main()
