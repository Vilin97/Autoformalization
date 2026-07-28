#!/usr/bin/env python3
"""Generate the checked conjugacy-class certificate for the sixfold A6 cover.

The discovery phase recomputes the finite group law from the proof-producing
shortlex rewrite certificate.  The emitted Lean files do not trust this
script: they reduce every advertised generator-conjugation and orbit witness
against the checked Lean group law.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
from pathlib import Path
from typing import Callable


ROOT = Path(__file__).resolve().parents[1]
GROUP_THEORY = ROOT / "McKayConjecture" / "GroupTheory"
REWRITE_GENERATOR = Path(__file__).with_name("a6_rewrite_certificate.py")

BLOCK_SIZE = 10
STATE_COUNT = 360
CENTRAL_ORDER = 6
GROUP_ORDER = STATE_COUNT * CENTRAL_ORDER
EXPECTED_CLASS_COUNT = 31

Coordinate = tuple[int, int]
Weight = tuple[int, int, int, int]


def load_rewrite_certificate():
    spec = importlib.util.spec_from_file_location(
        "a6_rewrite_certificate", REWRITE_GENERATOR
    )
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {REWRITE_GENERATOR}")
    module = importlib.util.module_from_spec(spec)
    with contextlib.redirect_stdout(io.StringIO()):
        spec.loader.exec_module(module)
    return module


def build_group_operations(rewrite):
    words = sorted(rewrite.normal_forms, key=rewrite.shortlex_key)
    if len(words) != STATE_COUNT:
        raise RuntimeError(f"expected {STATE_COUNT} normal words")
    word_index = {word: index for index, word in enumerate(words)}

    transition: dict[tuple[int, int], tuple[int, Weight]] = {}
    for (word, letter), (target, path) in rewrite.transitions.items():
        weight = rewrite.path_weight(path, rewrite.rules_by_id)
        transition[(word_index[word], letter)] = (
            word_index[target],
            weight,
        )

    def trace(state: int, word: tuple[int, ...]) -> tuple[int, Weight]:
        weight = [0, 0, 0, 0]
        for letter in word:
            state, increment = transition[(state, letter)]
            weight = [
                left + right for left, right in zip(weight, increment)
            ]
        return state, tuple(weight)

    product_trace = {
        (left, right): trace(left, word)
        for left in range(STATE_COUNT)
        for right, word in enumerate(words)
    }
    inverse_trace = {
        state: trace(
            0,
            tuple(
                rewrite.INVERSE[letter]
                for letter in reversed(word)
            ),
        )
        for state, word in enumerate(words)
    }

    def exponent(weight: Weight) -> int:
        return (
            weight[0] + 3 * weight[1] - weight[2] + weight[3]
        ) % CENTRAL_ORDER

    def multiply(left: Coordinate, right: Coordinate) -> Coordinate:
        state, weight = product_trace[(left[0], right[0])]
        central = (left[1] + exponent(weight) + right[1]) % CENTRAL_ORDER
        return state, central

    def inverse(coordinate: Coordinate) -> Coordinate:
        state, weight = inverse_trace[coordinate[0]]
        central = (exponent(weight) - coordinate[1]) % CENTRAL_ORDER
        return state, central

    def evaluate_word(word: tuple[int, ...]) -> Coordinate:
        state, weight = trace(0, word)
        return state, exponent(weight)

    def factor_coordinate(coordinate: Coordinate) -> tuple[Coordinate, Coordinate]:
        word = words[coordinate[0]]
        midpoint = len(word) // 2
        left = evaluate_word(word[:midpoint])
        right = evaluate_word(word[midpoint:])
        product = multiply(left, right)
        right = (
            right[0],
            (
                right[1]
                + coordinate[1]
                - product[1]
            )
            % CENTRAL_ORDER,
        )
        if multiply(left, right) != coordinate:
            raise RuntimeError("normal-word factorization failed")
        return left, right

    return multiply, inverse, factor_coordinate


def discover_conjugacy_data(
    multiply: Callable[[Coordinate, Coordinate], Coordinate],
    inverse: Callable[[Coordinate], Coordinate],
    factor_coordinate: Callable[
        [Coordinate], tuple[Coordinate, Coordinate]
    ],
):
    coordinates = [
        (state, central)
        for state in range(STATE_COUNT)
        for central in range(CENTRAL_ORDER)
    ]

    def conjugate(conjugator: Coordinate, target: Coordinate) -> Coordinate:
        return multiply(multiply(conjugator, target), inverse(conjugator))

    unseen = set(coordinates)
    representatives: list[Coordinate] = []
    class_index: dict[Coordinate, int] = {}
    conjugator_state: dict[Coordinate, int] = {}
    class_sizes: list[int] = []

    while unseen:
        representative = min(
            unseen, key=lambda coordinate: coordinate[0] * 6 + coordinate[1]
        )
        index = len(representatives)
        representatives.append(representative)
        witnesses: dict[Coordinate, int] = {}
        for state in range(STATE_COUNT):
            image = conjugate((state, 0), representative)
            witnesses.setdefault(image, state)
        orbit = set(witnesses)
        class_sizes.append(len(orbit))
        for coordinate, state in witnesses.items():
            if coordinate in class_index:
                raise RuntimeError("computed conjugacy classes overlap")
            class_index[coordinate] = index
            conjugator_state[coordinate] = state
        unseen.difference_update(orbit)

    if len(representatives) != EXPECTED_CLASS_COUNT:
        raise RuntimeError(
            f"expected {EXPECTED_CLASS_COUNT} classes, "
            f"found {len(representatives)}"
        )
    if len(class_index) != GROUP_ORDER:
        raise RuntimeError("conjugacy classes do not cover the group")
    if sum(class_sizes) != GROUP_ORDER:
        raise RuntimeError("conjugacy-class sizes have the wrong sum")

    expected_representatives = [
        (0, 0),
        (0, 1),
        (0, 2),
        (0, 3),
        (0, 4),
        (0, 5),
        (1, 0),
        (1, 1),
        (1, 2),
        (2, 0),
        (2, 1),
        (2, 2),
        (2, 3),
        (2, 4),
        (2, 5),
        (4, 0),
        (4, 1),
        (4, 2),
        (4, 3),
        (4, 4),
        (4, 5),
        (10, 0),
        (10, 1),
        (10, 2),
        (10, 3),
        (10, 4),
        (10, 5),
        (77, 0),
        (77, 1),
        (79, 0),
        (79, 1),
    ]
    expected_sizes = (
        [1] * 6
        + [90] * 9
        + [72] * 12
        + [120] * 4
    )
    if representatives != expected_representatives:
        raise RuntimeError("canonical representative list changed")
    if class_sizes != expected_sizes:
        raise RuntimeError("canonical conjugacy-class sizes changed")

    orbit_middle: dict[Coordinate, Coordinate] = {}
    conjugator_inverse: dict[Coordinate, Coordinate] = {}
    inverse_factor_left: dict[Coordinate, Coordinate] = {}
    inverse_factor_right: dict[Coordinate, Coordinate] = {}
    orbit_penultimate: dict[Coordinate, Coordinate] = {}
    for coordinate in coordinates:
        conjugator = (conjugator_state[coordinate], 0)
        representative = representatives[class_index[coordinate]]
        middle = multiply(conjugator, representative)
        conjugator_inv = inverse(conjugator)
        if multiply(middle, conjugator_inv) != coordinate:
            raise RuntimeError("split orbit witness does not compose")
        orbit_middle[coordinate] = middle
        conjugator_inverse[coordinate] = conjugator_inv
        factor_left, factor_right = factor_coordinate(conjugator_inv)
        penultimate = multiply(middle, factor_left)
        if multiply(penultimate, factor_right) != coordinate:
            raise RuntimeError("split final orbit product does not compose")
        inverse_factor_left[coordinate] = factor_left
        inverse_factor_right[coordinate] = factor_right
        orbit_penultimate[coordinate] = penultimate

    return (
        representatives,
        class_index,
        conjugator_state,
        orbit_middle,
        conjugator_inverse,
        inverse_factor_left,
        inverse_factor_right,
        orbit_penultimate,
        class_sizes,
    )


COPYRIGHT = """/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
"""

NAMESPACE_OPEN = """
namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

"""

NAMESPACE_CLOSE = """
end GroupTheory
end McKayConjecture
"""


def module_header(import_name: str, title: str, description: str) -> str:
    return (
        COPYRIGHT
        + f"import McKayConjecture.GroupTheory.{import_name}\n\n"
        + f"/-!\n# {title}\n\n{description}\n-/\n"
        + NAMESPACE_OPEN
    )


def vector(values: list[int]) -> str:
    return "![" + ", ".join(str(value) for value in values) + "]"


def emit_data_types():
    chunks = [
        module_header(
            "AlternatingSixSchurCoverCoordinateModel",
            "Certificate records for sixfold-cover conjugacy",
            "A compact generated record stores the class label and the "
            "short factors used to check one orbit witness.",
        ),
        """/-- One row entry in the finite conjugacy certificate. -/
structure AlternatingSixSchurConjugacyDatum where
  classIndex : Fin 31
  conjugatorState : Fin 360
  orbitMiddleState : Fin 360
  orbitMiddleCentral : Fin 6
  conjugatorInverseState : Fin 360
  conjugatorInverseCentral : Fin 6
  inverseFactorLeftState : Fin 360
  inverseFactorLeftCentral : Fin 6
  inverseFactorRightState : Fin 360
  inverseFactorRightCentral : Fin 6
  orbitPenultimateState : Fin 360
  orbitPenultimateCentral : Fin 6
deriving DecidableEq

""",
        NAMESPACE_CLOSE,
    ]
    (
        GROUP_THEORY
        / "AlternatingSixSchurCoverConjugacyCertificateTypes.lean"
    ).write_text("".join(chunks))


def emit_data_blocks(
    class_index: dict[Coordinate, int],
    conjugator_state: dict[Coordinate, int],
    orbit_middle: dict[Coordinate, Coordinate],
    conjugator_inverse: dict[Coordinate, Coordinate],
    inverse_factor_left: dict[Coordinate, Coordinate],
    inverse_factor_right: dict[Coordinate, Coordinate],
    orbit_penultimate: dict[Coordinate, Coordinate],
):
    block_count = STATE_COUNT // BLOCK_SIZE
    for block in range(block_count):
        start = block * BLOCK_SIZE
        end = start + BLOCK_SIZE
        chunks = [
            module_header(
                "AlternatingSixSchurCoverConjugacyCertificateTypes",
                f"Sixfold-cover conjugacy data, states {start}–{end - 1}",
                "Generated class labels and orbit witnesses for one block\n"
                "of normal-word states.  The accompanying check modules\n"
                "verify the data against the group law.",
            )
        ]
        for state in range(start, end):
            entries = []
            for central in range(CENTRAL_ORDER):
                coordinate = (state, central)
                middle = orbit_middle[coordinate]
                conjugator_inv = conjugator_inverse[coordinate]
                factor_left = inverse_factor_left[coordinate]
                factor_right = inverse_factor_right[coordinate]
                penultimate = orbit_penultimate[coordinate]
                entries.append(
                    "{ classIndex := "
                    f"{class_index[coordinate]}, conjugatorState := "
                    f"{conjugator_state[coordinate]}, orbitMiddleState := "
                    f"{middle[0]}, orbitMiddleCentral := {middle[1]}, "
                    "conjugatorInverseState := "
                    f"{conjugator_inv[0]}, conjugatorInverseCentral := "
                    f"{conjugator_inv[1]}, inverseFactorLeftState := "
                    f"{factor_left[0]}, inverseFactorLeftCentral := "
                    f"{factor_left[1]}, inverseFactorRightState := "
                    f"{factor_right[0]}, inverseFactorRightCentral := "
                    f"{factor_right[1]}, orbitPenultimateState := "
                    f"{penultimate[0]}, orbitPenultimateCentral := "
                    f"{penultimate[1]} }}"
                )
            chunks.extend(
                [
                    f"/-- Certificate data above normal-word state {state}. -/\n",
                    f"def alternatingSixSchurConjugacyDatumRow{state:03d} :\n",
                    "    Fin 6 → AlternatingSixSchurConjugacyDatum :=\n",
                    "  ![\n    ",
                    ",\n    ".join(entries),
                    "\n  ]\n\n",
                ]
            )
        chunks.append(NAMESPACE_CLOSE)
        output = (
            GROUP_THEORY
            / f"AlternatingSixSchurCoverConjugacyData{block:02d}.lean"
        )
        output.write_text("".join(chunks))


def emit_data_umbrella(
    representatives: list[Coordinate],
    class_sizes: list[int],
):
    block_count = STATE_COUNT // BLOCK_SIZE
    imports = "\n".join(
        "import McKayConjecture.GroupTheory."
        f"AlternatingSixSchurCoverConjugacyData{block:02d}"
        for block in range(block_count)
    )
    chunks = [
        COPYRIGHT,
        imports,
        """

/-!
# Finite conjugacy data for the sixfold cover of `A₆`

This generated interface combines the blockwise class labels and orbit
witnesses.  Its companion check files verify that labels are invariant under
the two noncentral presentation generators and that every coordinate is
conjugate to its advertised representative.
-/
""",
        NAMESPACE_OPEN,
        """/-- The coordinate of the presentation generator `a`. -/
def alternatingSixSchurCoordinateA :
    AlternatingSixSchurCoordinates :=
  ⟨1, 0⟩

/-- The coordinate of the presentation generator `b`. -/
def alternatingSixSchurCoordinateB :
    AlternatingSixSchurCoordinates :=
  ⟨2, 0⟩

/-- The canonical representative of each advertised conjugacy class. -/
def alternatingSixSchurClassRepresentative :
    Fin 31 → AlternatingSixSchurCoordinates :=
  fun index =>
    match index.val with
""",
    ]
    for index, (state, central) in enumerate(representatives[:-1]):
        chunks.append(
            f"    | {index} => ⟨{state}, {central}⟩\n"
        )
    state, central = representatives[-1]
    chunks.append(f"    | _ => ⟨{state}, {central}⟩\n\n")

    chunks.extend(
        [
            """/-- The externally discovered size of each advertised class.
These values are metadata; class completeness is proved from checked orbit
witnesses rather than assumed from their sum. -/
def alternatingSixSchurClassSize :
    Fin 31 → Nat :=
  """,
            vector(class_sizes),
            "\n\n",
            """/-- The packed checked data attached to a coordinate. -/
def alternatingSixSchurConjugacyDatum
    (coordinate : AlternatingSixSchurCoordinates) :
    AlternatingSixSchurConjugacyDatum :=
  let central := (ZMod.finEquiv 6).symm coordinate.central
  match coordinate.state.val with
""",
        ]
    )
    for state in range(STATE_COUNT - 1):
        chunks.append(
            f"  | {state} => "
            f"alternatingSixSchurConjugacyDatumRow{state:03d} central\n"
        )
    chunks.append(
        "  | _ => alternatingSixSchurConjugacyDatumRow359 central\n\n"
    )

    chunks.extend(
        [
            """/-- The checked-data label of a coordinate. -/
def alternatingSixSchurClassIndex
    (coordinate : AlternatingSixSchurCoordinates) :
    Fin 31 :=
  (alternatingSixSchurConjugacyDatum coordinate).classIndex

/-- A checked-data conjugator carrying the representative of a
coordinate's label to that coordinate.  Its central coordinate can be chosen
to be zero because central factors do not affect conjugation. -/
def alternatingSixSchurClassConjugator
    (coordinate : AlternatingSixSchurCoordinates) :
    AlternatingSixSchurCoordinates :=
  ⟨(alternatingSixSchurConjugacyDatum coordinate).conjugatorState, 0⟩

/-- The tabulated first product in an orbit witness. -/
def alternatingSixSchurOrbitMiddle
    (coordinate : AlternatingSixSchurCoordinates) :
    AlternatingSixSchurCoordinates :=
  let datum := alternatingSixSchurConjugacyDatum coordinate
  ⟨datum.orbitMiddleState,
    (ZMod.finEquiv 6) datum.orbitMiddleCentral⟩

/-- The tabulated inverse of an orbit conjugator. -/
def alternatingSixSchurClassConjugatorInverse
    (coordinate : AlternatingSixSchurCoordinates) :
    AlternatingSixSchurCoordinates :=
  let datum := alternatingSixSchurConjugacyDatum coordinate
  ⟨datum.conjugatorInverseState,
    (ZMod.finEquiv 6) datum.conjugatorInverseCentral⟩

/-- The left short factor of the inverse conjugator. -/
def alternatingSixSchurInverseFactorLeft
    (coordinate : AlternatingSixSchurCoordinates) :
    AlternatingSixSchurCoordinates :=
  let datum := alternatingSixSchurConjugacyDatum coordinate
  ⟨datum.inverseFactorLeftState,
    (ZMod.finEquiv 6) datum.inverseFactorLeftCentral⟩

/-- The right short factor of the inverse conjugator. -/
def alternatingSixSchurInverseFactorRight
    (coordinate : AlternatingSixSchurCoordinates) :
    AlternatingSixSchurCoordinates :=
  let datum := alternatingSixSchurConjugacyDatum coordinate
  ⟨datum.inverseFactorRightState,
    (ZMod.finEquiv 6) datum.inverseFactorRightCentral⟩

/-- The penultimate product in the split orbit witness. -/
def alternatingSixSchurOrbitPenultimate
    (coordinate : AlternatingSixSchurCoordinates) :
    AlternatingSixSchurCoordinates :=
  let datum := alternatingSixSchurConjugacyDatum coordinate
  ⟨datum.orbitPenultimateState,
    (ZMod.finEquiv 6) datum.orbitPenultimateCentral⟩

""",
        ]
    )
    chunks.append(NAMESPACE_CLOSE)
    (
        GROUP_THEORY / "AlternatingSixSchurCoverConjugacyData.lean"
    ).write_text("".join(chunks))


def coordinate_term(state: int) -> str:
    return (
        "({ state := "
        f"{state}, central := (ZMod.finEquiv 6) central "
        "} : AlternatingSixSchurCoordinates)"
    )


def emit_check_blocks():
    block_count = STATE_COUNT // BLOCK_SIZE
    for block in range(block_count):
        start = block * BLOCK_SIZE
        end = start + BLOCK_SIZE
        import_name = (
            "AlternatingSixSchurCoverConjugacyData"
            if block == 0
            else f"AlternatingSixSchurCoverConjugacyChecks{block - 1:02d}"
        )
        chunks = [
            module_header(
                import_name,
                f"Checked sixfold-cover conjugacy data, states {start}–{end - 1}",
                "Each theorem below is a kernel-checked finite computation "
                "against the coordinate group law.",
            )
        ]
        for state in range(start, end):
            coordinate = coordinate_term(state)
            chunks.extend(
                [
                    f"/-- Class-label invariance under `a`, state {state}. -/\n",
                    "theorem alternatingSixSchurClassIndex_conjugateA_"
                    f"state{state:03d} (central : Fin 6) :\n",
                    "    alternatingSixSchurClassIndex\n",
                    "        (alternatingSixSchurCoordinateA *\n",
                    f"          {coordinate} *\n",
                    "          alternatingSixSchurCoordinateA⁻¹) =\n",
                    f"      alternatingSixSchurClassIndex {coordinate} := by\n",
                    "  fin_cases central <;> decide\n\n",
                    f"/-- Class-label invariance under `b`, state {state}. -/\n",
                    "theorem alternatingSixSchurClassIndex_conjugateB_"
                    f"state{state:03d} (central : Fin 6) :\n",
                    "    alternatingSixSchurClassIndex\n",
                    "        (alternatingSixSchurCoordinateB *\n",
                    f"          {coordinate} *\n",
                    "          alternatingSixSchurCoordinateB⁻¹) =\n",
                    f"      alternatingSixSchurClassIndex {coordinate} := by\n",
                    "  fin_cases central <;> decide\n\n",
                    f"/-- First orbit-witness multiplication above state {state}. -/\n",
                    "theorem alternatingSixSchurOrbitMiddle_"
                    f"state{state:03d} (central : Fin 6) :\n",
                    "    alternatingSixSchurClassConjugator "
                    f"{coordinate} *\n",
                    "        alternatingSixSchurClassRepresentative\n",
                    "          (alternatingSixSchurClassIndex "
                    f"{coordinate}) =\n",
                    "      alternatingSixSchurOrbitMiddle "
                    f"{coordinate} := by\n",
                    "  fin_cases central <;> decide\n\n",
                    f"/-- Conjugator inversion above state {state}. -/\n",
                    "theorem alternatingSixSchurClassConjugatorInverse_"
                    f"state{state:03d} (central : Fin 6) :\n",
                    "    (alternatingSixSchurClassConjugator "
                    f"{coordinate})⁻¹ =\n",
                    "      alternatingSixSchurClassConjugatorInverse "
                    f"{coordinate} := by\n",
                    "  fin_cases central <;> decide\n\n",
                    f"/-- Short inverse factorization above state {state}. -/\n",
                    "theorem alternatingSixSchurInverseFactor_"
                    f"state{state:03d} (central : Fin 6) :\n",
                    "    alternatingSixSchurInverseFactorLeft "
                    f"{coordinate} *\n",
                    "        alternatingSixSchurInverseFactorRight "
                    f"{coordinate} =\n",
                    "      alternatingSixSchurClassConjugatorInverse "
                    f"{coordinate} := by\n",
                    "  fin_cases central <;> decide\n\n",
                    f"/-- Penultimate orbit multiplication above state {state}. -/\n",
                    "theorem alternatingSixSchurOrbitPenultimate_"
                    f"state{state:03d} (central : Fin 6) :\n",
                    "    alternatingSixSchurOrbitMiddle "
                    f"{coordinate} *\n",
                    "        alternatingSixSchurInverseFactorLeft "
                    f"{coordinate} =\n",
                    "      alternatingSixSchurOrbitPenultimate "
                    f"{coordinate} := by\n",
                    "  fin_cases central <;> decide\n\n",
                    f"/-- Final orbit-witness multiplication above state {state}. -/\n",
                    "theorem alternatingSixSchurOrbitFinish_"
                    f"state{state:03d} (central : Fin 6) :\n",
                    "    alternatingSixSchurOrbitPenultimate "
                    f"{coordinate} *\n",
                    "        alternatingSixSchurInverseFactorRight "
                    f"{coordinate} =\n",
                    f"      {coordinate} := by\n",
                    "  fin_cases central <;> decide\n\n",
                ]
            )
        chunks.append(NAMESPACE_CLOSE)
        (
            GROUP_THEORY
            / f"AlternatingSixSchurCoverConjugacyChecks{block:02d}.lean"
        ).write_text("".join(chunks))


def emit_check_umbrella():
    block_count = STATE_COUNT // BLOCK_SIZE
    imports = (
        "import McKayConjecture.GroupTheory."
        f"AlternatingSixSchurCoverConjugacyChecks{block_count - 1:02d}"
    )
    chunks = [
        COPYRIGHT,
        imports,
        """

/-!
# Complete checked conjugacy data for the sixfold cover of `A₆`

The blockwise computations are assembled into quantified generator
invariance and orbit-witness statements.
-/
""",
        NAMESPACE_OPEN,
    ]

    theorem_specs = [
        (
            "alternatingSixSchurClassIndex_conjugateA",
            "alternatingSixSchurClassIndex_conjugateA_state",
            """alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA * coordinate *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex coordinate""",
        ),
        (
            "alternatingSixSchurClassIndex_conjugateB",
            "alternatingSixSchurClassIndex_conjugateB_state",
            """alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB * coordinate *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex coordinate""",
        ),
        (
            "alternatingSixSchurOrbitMiddle_spec",
            "alternatingSixSchurOrbitMiddle_state",
            """alternatingSixSchurClassConjugator coordinate *
          alternatingSixSchurClassRepresentative
            (alternatingSixSchurClassIndex coordinate) =
      alternatingSixSchurOrbitMiddle coordinate""",
        ),
        (
            "alternatingSixSchurClassConjugatorInverse_spec",
            "alternatingSixSchurClassConjugatorInverse_state",
            """(alternatingSixSchurClassConjugator coordinate)⁻¹ =
      alternatingSixSchurClassConjugatorInverse coordinate""",
        ),
        (
            "alternatingSixSchurInverseFactor_spec",
            "alternatingSixSchurInverseFactor_state",
            """alternatingSixSchurInverseFactorLeft coordinate *
          alternatingSixSchurInverseFactorRight coordinate =
      alternatingSixSchurClassConjugatorInverse coordinate""",
        ),
        (
            "alternatingSixSchurOrbitPenultimate_spec",
            "alternatingSixSchurOrbitPenultimate_state",
            """alternatingSixSchurOrbitMiddle coordinate *
          alternatingSixSchurInverseFactorLeft coordinate =
      alternatingSixSchurOrbitPenultimate coordinate""",
        ),
        (
            "alternatingSixSchurOrbitFinish_spec",
            "alternatingSixSchurOrbitFinish_state",
            """alternatingSixSchurOrbitPenultimate coordinate *
          alternatingSixSchurInverseFactorRight coordinate =
      coordinate""",
        ),
    ]
    for theorem_name, row_prefix, proposition in theorem_specs:
        chunks.extend(
            [
                f"/-- The blockwise checks imply `{theorem_name}` globally. -/\n",
                f"theorem {theorem_name}\n",
                "    (coordinate : AlternatingSixSchurCoordinates) :\n",
                f"    {proposition} := by\n",
                "  rcases coordinate with ⟨state, central⟩\n",
                "  let centralIndex : Fin 6 :=\n",
                "    (ZMod.finEquiv 6).symm central\n",
                "  fin_cases state\n",
            ]
        )
        for state in range(STATE_COUNT):
            chunks.extend(
                [
                    f"  · simpa [centralIndex] using\n",
                    f"      {row_prefix}{state:03d} centralIndex\n",
                ]
            )
        chunks.append("\n")
    chunks.extend(
        [
            """/-- Every coordinate is conjugate to its advertised class
representative. -/
theorem alternatingSixSchurClassConjugator_spec
    (coordinate : AlternatingSixSchurCoordinates) :
    alternatingSixSchurClassConjugator coordinate *
          alternatingSixSchurClassRepresentative
            (alternatingSixSchurClassIndex coordinate) *
          (alternatingSixSchurClassConjugator coordinate)⁻¹ =
      coordinate := by
  rw [alternatingSixSchurOrbitMiddle_spec,
    alternatingSixSchurClassConjugatorInverse_spec]
  rw [← alternatingSixSchurInverseFactor_spec, ← mul_assoc,
    alternatingSixSchurOrbitPenultimate_spec,
    alternatingSixSchurOrbitFinish_spec]

""",
        ]
    )
    chunks.append(NAMESPACE_CLOSE)
    (
        GROUP_THEORY / "AlternatingSixSchurCoverConjugacyChecks.lean"
    ).write_text("".join(chunks))


def main():
    rewrite = load_rewrite_certificate()
    multiply, inverse, factor_coordinate = build_group_operations(rewrite)
    (
        representatives,
        class_index,
        conjugator_state,
        orbit_middle,
        conjugator_inverse,
        inverse_factor_left,
        inverse_factor_right,
        orbit_penultimate,
        class_sizes,
    ) = discover_conjugacy_data(
        multiply,
        inverse,
        factor_coordinate,
    )
    emit_data_types()
    emit_data_blocks(
        class_index,
        conjugator_state,
        orbit_middle,
        conjugator_inverse,
        inverse_factor_left,
        inverse_factor_right,
        orbit_penultimate,
    )
    emit_data_umbrella(representatives, class_sizes)
    emit_check_blocks()
    emit_check_umbrella()
    print(
        f"generated {EXPECTED_CLASS_COUNT} classes in "
        f"{2 * (STATE_COUNT // BLOCK_SIZE) + 2} Lean files"
    )


if __name__ == "__main__":
    main()
