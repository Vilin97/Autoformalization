#!/usr/bin/env python3
"""Compute and emit class-representative trace certificates for row 31.

Row 30 has the same degree, but it has the opposite order-three central
pattern. The displayed row-31 matrices are neither its displayed matrices
nor their transposes, and the Lean development contains no proved
intertwiner between the two representations. Transporting row 30's
character would therefore leave a change-of-basis or Galois-transport claim
unproved. The generated modules instead recheck the five matrix
multiplications needed by the two long class words directly.

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
    """Return the displayed transpose, for the shortcut audit."""
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
        "alternatingSixFiveAmbient_row31_matrixA"
    )
    matrix_b = helper.extract_matrix(
        "alternatingSixFiveAmbient_row31_matrixB"
    )
    row30_matrix_a = helper.extract_matrix(
        "alternatingSixFiveAmbient_row30_matrixA"
    )
    row30_matrix_b = helper.extract_matrix(
        "alternatingSixFiveAmbient_row30_matrixB"
    )
    print(f"row31_A_equals_row30_A = {matrix_a == row30_matrix_a}")
    print(f"row31_B_equals_row30_B = {matrix_b == row30_matrix_b}")
    print(
        "row31_A_transpose_equals_row30_A = "
        f"{transpose(matrix_a) == row30_matrix_a}"
    )
    print(
        "row31_B_transpose_equals_row30_B = "
        f"{transpose(matrix_b) == row30_matrix_b}"
    )

    dimension = len(matrix_a)
    if arguments.write_lean:
        helper.write_long_word_certificates(31, matrix_a, matrix_b)
        output_directory = ROOT / "McKayConjecture" / "InductiveMcKay"
        for path in output_directory.glob(
            "AlternatingSixAmbientRow31LongWord*.lean"
        ):
            source = path.read_text(encoding="utf-8")
            path.write_text(
                source.replace(
                    "scripts/a6_row19_representative_traces.py",
                    "scripts/a6_row31_representative_traces.py",
                ).replace(
                    "AlternatingSixFiveAmbientMatrixDataDegreeEightNine",
                    MATRIX_DATA_MODULE,
                ).replace(
                    "  simp only [\n",
                    "  simp [\n",
                ).replace(
                    "  ]; ring\n",
                    "  ]\n  all_goals ring\n",
                ),
                encoding="utf-8",
            )

    # Row 31 has a^2 = zeta^40 and b^4 = 1. Hence
    # a^-1 = zeta^80 a and b^-1 = b^3.
    matrix_a_inverse = helper.scalar_multiply(
        base.Polynomial.monomial(80, 1), matrix_a
    )
    matrix_b_inverse = base.matrix_power(matrix_b, 3)
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
