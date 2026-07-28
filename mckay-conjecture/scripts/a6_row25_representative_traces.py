#!/usr/bin/env python3
"""Compute and emit class-representative trace certificates for row 25.

No existing certified ambient row comes with an explicit Lean intertwiner to
row 25.  In particular, the degree-ten row paired with it in the ordinary
table has not yet been normalized.  The generated Lean modules therefore
recheck the five matrix multiplications needed by the two long class words
directly.

The final audit computes the seven base-word traces and their inverse
pairings in `Q[zeta_120] / (Phi_120)`.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
HELPER_PATH = ROOT / "scripts" / "a6_row19_representative_traces.py"

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
    / "AlternatingSixFiveAmbientMatrixDataDegreeFiveTenFifteen.lean"
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write-lean",
        action="store_true",
        help="write the split kernel-checked long-word certificate modules",
    )
    arguments = parser.parse_args()

    matrix_a = helper.extract_matrix(
        "alternatingSixFiveAmbient_row25_matrixA"
    )
    matrix_b = helper.extract_matrix(
        "alternatingSixFiveAmbient_row25_matrixB"
    )
    dimension = len(matrix_a)
    if arguments.write_lean:
        helper.write_long_word_certificates(25, matrix_a, matrix_b)
        output_directory = ROOT / "McKayConjecture" / "InductiveMcKay"
        for path in output_directory.glob(
            "AlternatingSixAmbientRow25LongWord*.lean"
        ):
            source = path.read_text(encoding="utf-8")
            path.write_text(
                source.replace(
                    "scripts/a6_row19_representative_traces.py",
                    "scripts/a6_row25_representative_traces.py",
                ).replace(
                    "AlternatingSixFiveAmbientMatrixDataDegreeEightNine",
                    "AlternatingSixFiveAmbientMatrixDataDegreeFiveTenFifteen",
                ).replace(
                    "  simp only [\n",
                    "  simp [\n",
                ),
                encoding="utf-8",
            )

    # Row 25 has a^2 = -1 and b^4 = -1.  Hence
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
        matrices = [generators[letter] for letter in word]
        value = helper.trace(helper.product(matrices, dimension))
        raw_value = helper.trace_raw(
            helper.product_raw(matrices, dimension)
        )
        quotient = helper.reduction_quotient(raw_value, value)
        inverse_value = helper.trace(
            helper.inverse_word(word, generators, dimension)
        )
        pairing = (value * inverse_value).reduce()
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
    gamma = (
        base.Polynomial.monomial(5)
        + base.Polynomial.monomial(15)
        - base.Polynomial.monomial(25)
    )
    gamma_square_quotient = helper.reduction_quotient(
        gamma * gamma, base.Polynomial.constant(2)
    )
    print(
        "gamma_square_quotient = "
        f"{base.polynomial_expression_to_lean(gamma_square_quotient)}"
    )
    print(f"weighted_norm = {base.polynomial_to_lean(norm)}")


if __name__ == "__main__":
    main()
