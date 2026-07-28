#!/usr/bin/env python3
"""Compute and emit class-representative trace certificates for row 24.

Row 25 has the same degree and central scalar pattern, but the displayed
row-24 matrices are neither equal to its displayed matrices nor their
transposes.  More importantly, the Lean development contains no proved
intertwiner between the two representations.  Reusing row 25's character
would therefore hide an unproved change-of-basis claim.  The generated Lean
modules instead recheck the five matrix multiplications used by the two long
class words directly.

The final audit computes all seven base-word traces and their inverse
pairings in `Q[zeta_120] / (Phi_120)`.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
HELPER_PATH = ROOT / "scripts" / "a6_row19_representative_traces.py"
MATRIX_DATA_MODULE = (
    "AlternatingSixFiveAmbientMatrixDataDegreeFiveTenFifteen"
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


def transpose(
    matrix: base.PolynomialMatrix,
) -> base.PolynomialMatrix:
    """Return the displayed transpose, for the structural-shortcut audit."""
    dimension = len(matrix)
    return [
        [matrix[column][row] for column in range(dimension)]
        for row in range(dimension)
    ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write-lean",
        action="store_true",
        help="write the split kernel-checked long-word certificate modules",
    )
    arguments = parser.parse_args()

    matrix_a = helper.extract_matrix(
        "alternatingSixFiveAmbient_row24_matrixA"
    )
    matrix_b = helper.extract_matrix(
        "alternatingSixFiveAmbient_row24_matrixB"
    )
    row25_matrix_a = helper.extract_matrix(
        "alternatingSixFiveAmbient_row25_matrixA"
    )
    row25_matrix_b = helper.extract_matrix(
        "alternatingSixFiveAmbient_row25_matrixB"
    )
    print(f"row24_A_equals_row25_A = {matrix_a == row25_matrix_a}")
    print(f"row24_B_equals_row25_B = {matrix_b == row25_matrix_b}")
    print(
        "row24_A_transpose_equals_row25_A = "
        f"{transpose(matrix_a) == row25_matrix_a}"
    )
    print(
        "row24_B_transpose_equals_row25_B = "
        f"{transpose(matrix_b) == row25_matrix_b}"
    )

    dimension = len(matrix_a)
    if arguments.write_lean:
        helper.write_long_word_certificates(24, matrix_a, matrix_b)
        output_directory = ROOT / "McKayConjecture" / "InductiveMcKay"
        for path in output_directory.glob(
            "AlternatingSixAmbientRow24LongWord*.lean"
        ):
            source = path.read_text(encoding="utf-8")
            path.write_text(
                source.replace(
                    "scripts/a6_row19_representative_traces.py",
                    "scripts/a6_row24_representative_traces.py",
                ).replace(
                    "AlternatingSixFiveAmbientMatrixDataDegreeEightNine",
                    MATRIX_DATA_MODULE,
                ).replace(
                    "  simp only [\n",
                    "  simp [\n",
                ),
                encoding="utf-8",
            )

    # Row 24 has a^2 = -1 and b^4 = -1.  Hence
    # a^-1 = -a and b^-1 = -b^3.
    negative_one = base.Polynomial.constant(-1)
    matrix_a_inverse = helper.scalar_multiply(negative_one, matrix_a)
    matrix_b_inverse = helper.scalar_multiply(
        negative_one, base.matrix_power(matrix_b, 3)
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
