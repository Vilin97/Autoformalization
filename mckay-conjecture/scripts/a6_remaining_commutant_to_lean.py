#!/usr/bin/env python3
"""Generate diagonal-basis commutant certificates for the remaining numeric rows.

This is a thin driver around ``a6_degree_four_six_commutant_to_lean.py``.
The underlying exact arithmetic and proof renderer are dimension-agnostic;
this file supplies the metadata and matrix-data bucket for degrees
5, 8, 9, 10, and 15.  Pass row numbers as arguments to regenerate only a
small independently compiled batch.
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE_GENERATOR_PATH = (
    ROOT / "scripts" / "a6_degree_four_six_commutant_to_lean.py"
)
SPEC = importlib.util.spec_from_file_location(
    "a6_degree_four_six_commutant_to_lean",
    BASE_GENERATOR_PATH,
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("could not load the diagonal commutant generator")
BASE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = BASE
SPEC.loader.exec_module(BASE)


def order_four_metadata(row: str, dimension: int):
    return BASE.RowMetadata(
        row,
        dimension,
        (0, 30, 60, 90),
        "alternatingSixOrderFourEigenvalue",
        "alternatingSixOrderFourEigenvalue_injective",
    )


def order_eight_metadata(row: str, dimension: int):
    return BASE.RowMetadata(
        row,
        dimension,
        (15, 45, 75, 105),
        "alternatingSixOrderEightOddEigenvalue",
        "alternatingSixOrderEightOddEigenvalue_injective",
    )


ROWS = {
    "08": (
        order_four_metadata("08", 5),
        "AlternatingSixFiveAmbientMatrixDataDegreeFiveTenFifteen",
    ),
    "09": (
        order_four_metadata("09", 5),
        "AlternatingSixFiveAmbientMatrixDataDegreeFiveTenFifteen",
    ),
    "16": (
        order_four_metadata("16", 8),
        "AlternatingSixFiveAmbientMatrixDataDegreeEightNine",
    ),
    "17": (
        order_four_metadata("17", 8),
        "AlternatingSixFiveAmbientMatrixDataDegreeEightNine",
    ),
    "18": (
        order_eight_metadata("18", 8),
        "AlternatingSixFiveAmbientMatrixDataDegreeEightNine",
    ),
    "19": (
        order_eight_metadata("19", 8),
        "AlternatingSixFiveAmbientMatrixDataDegreeEightNine",
    ),
    "20": (
        order_four_metadata("20", 9),
        "AlternatingSixFiveAmbientMatrixDataDegreeEightNine",
    ),
    "21": (
        order_four_metadata("21", 9),
        "AlternatingSixFiveAmbientMatrixDataDegreeEightNine",
    ),
    "22": (
        order_four_metadata("22", 9),
        "AlternatingSixFiveAmbientMatrixDataDegreeEightNine",
    ),
    "23": (
        order_four_metadata("23", 10),
        "AlternatingSixFiveAmbientMatrixDataDegreeFiveTenFifteen",
    ),
    "24": (
        order_eight_metadata("24", 10),
        "AlternatingSixFiveAmbientMatrixDataDegreeFiveTenFifteen",
    ),
    "25": (
        order_eight_metadata("25", 10),
        "AlternatingSixFiveAmbientMatrixDataDegreeFiveTenFifteen",
    ),
    "30": (
        order_four_metadata("30", 15),
        "AlternatingSixFiveAmbientMatrixDataDegreeFiveTenFifteen",
    ),
    "31": (
        order_four_metadata("31", 15),
        "AlternatingSixFiveAmbientMatrixDataDegreeFiveTenFifteen",
    ),
}


def lean_linear_form(
    coefficients: list,
    allowed_pairs: list[tuple[int, int]],
) -> str:
    terms = [
        f"({BASE.lean_complex(coefficient.polynomial)}) * "
        f"Y {row} {column}"
        for coefficient, (row, column) in zip(
            coefficients, allowed_pairs, strict=True
        )
        if coefficient != BASE.CyclotomicElement(0)
    ]
    if not terms:
        return "(0 : ℂ)"
    return "(\n      " + "\n      + ".join(terms) + ")"


def render_off_block_theorem(metadata) -> str:
    row = metadata.row
    dimension = metadata.dimension
    return f"""/-- Entries between distinct second-generator eigenspaces
vanish in its commutant. -/
theorem alternatingSixAmbientRow{row}_off_block
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

"""


def render_commutator_equation(
    metadata,
    data,
    reduction,
    equations,
    equation_index: int,
) -> str:
    row = metadata.row
    dimension = metadata.dimension
    output_row, output_column = divmod(equation_index, dimension)
    off_blocks = BASE.relevant_off_blocks(
        metadata, data, [equation_index]
    )
    off_proofs = "".join(
        f"""  have {BASE.off_block_name(i, j)} :
      Y {i} {j} = 0 :=
    alternatingSixAmbientRow{row}_off_block
      Y commutesDiagonal {i} {j} (by decide)
"""
        for i, j in off_blocks
    )
    off_names = ",\n      ".join(
        BASE.off_block_name(i, j) for i, j in off_blocks
    )
    eliminate_off_blocks = (
        f"""  simp only [
      {off_names}] at equation
"""
        if off_blocks
        else ""
    )
    goal = lean_linear_form(
        equations[equation_index], reduction.allowed_pairs
    )
    return f"""theorem row{row}_commutatorEquation{output_row}{output_column}
    (Y : Matrix (Fin {dimension}) (Fin {dimension}) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow{row}TransformedGeneratorA =
        alternatingSixAmbientRow{row}TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow{row}GeneratorBDiagonal =
        alternatingSixAmbientRow{row}GeneratorBDiagonal * Y) :
    {goal} = 0 := by
{off_proofs}  have equation :=
    congrFun (congrFun commutesA
      ({output_row} : Fin {dimension}))
      ({output_column} : Fin {dimension})
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow{row}TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
{eliminate_off_blocks}  linear_combination equation

"""


def partial_combination_data(
    previous: list,
    coefficient,
    equation: list,
) -> tuple[list, list]:
    next_coefficients = [
        left + coefficient * right
        for left, right in zip(previous, equation, strict=True)
    ]
    quotients = []
    for left, right, target in zip(
        previous, equation, next_coefficients, strict=True
    ):
        raw = (
            left.polynomial
            + coefficient.polynomial * right.polynomial
        )
        quotients.append(
            BASE.quotient_of_zero(raw - target.polynomial)
        )
    return next_coefficients, quotients


def render_combination_correction(
    quotients: list,
    allowed_pairs: list[tuple[int, int]],
) -> str:
    terms = [
        f"({BASE.lean_complex(quotient)}) * Y {row} {column}"
        for quotient, (row, column) in zip(
            quotients, allowed_pairs, strict=True
        )
        if quotient != BASE.zero_polynomial()
    ]
    if not terms:
        return ""
    return (
        "\n      - (\n        "
        + "\n        + ".join(terms)
        + ")\n        * "
        "alternatingSixComplexCyclotomicRoot_relation"
    )


def lean_named_linear_form(
    coefficient_names: list[str],
    allowed_pairs: list[tuple[int, int]],
) -> str:
    """Render a linear form whose coefficients are separately checked defs."""

    terms = [
        f"({name}) * Y {row} {column}"
        for name, (row, column) in zip(
            coefficient_names, allowed_pairs, strict=True
        )
    ]
    return "(\n      " + "\n      + ".join(terms) + ")"


def render_sequential_reduced_relation(
    metadata,
    reduction,
    equations,
    reduction_row: int,
) -> tuple[str, str, str]:
    row = metadata.row
    dimension = metadata.dimension
    pair, reduced_name, goal = BASE.reduced_relation_goal(
        metadata, reduction, reduction_row
    )
    support = [
        index
        for index, coefficient in enumerate(
            reduction.combinations[reduction_row]
        )
        if coefficient != BASE.CyclotomicElement(0)
    ]
    previous = [
        BASE.CyclotomicElement(0)
        for _ in reduction.allowed_pairs
    ]
    previous_name: str | None = None
    previous_coefficient_names = [
        "(0 : ℂ)" for _ in reduction.allowed_pairs
    ]
    chunks: list[str] = []
    for step, equation_index in enumerate(support):
        coefficient = reduction.combinations[
            reduction_row
        ][equation_index]
        next_coefficients, quotients = partial_combination_data(
            previous, coefficient, equations[equation_index]
        )
        equation_row, equation_column = divmod(
            equation_index, dimension
        )
        step_name = (
            f"row{row}_{reduced_name}_combinationStep{step:02d}"
        )
        multiplier_name = f"{step_name}Multiplier"
        chunks.append(
            f"""private def {multiplier_name} : ℂ :=
  {BASE.lean_complex(coefficient.polynomial)}

"""
        )
        next_coefficient_names: list[str] = []
        coefficient_identity_names: list[str] = []
        for variable, (
            next_coefficient,
            quotient,
            equation_coefficient,
            previous_coefficient_name,
        ) in enumerate(
            zip(
                next_coefficients,
                quotients,
                equations[equation_index],
                previous_coefficient_names,
                strict=True,
            )
        ):
            coefficient_name = (
                f"{step_name}Coefficient{variable:02d}"
            )
            identity_name = (
                f"{step_name}CoefficientIdentity{variable:02d}"
            )
            next_coefficient_names.append(coefficient_name)
            coefficient_identity_names.append(identity_name)
            previous_unfold = (
                ""
                if previous_name is None
                else f" {previous_coefficient_name}"
            )
            chunks.append(
                f"""private def {coefficient_name} : ℂ :=
  {BASE.lean_complex(next_coefficient.polynomial)}

private theorem {identity_name} :
    {coefficient_name} =
      {previous_coefficient_name} +
        {multiplier_name} *
          {BASE.lean_complex(equation_coefficient.polynomial)} := by
  unfold {coefficient_name}{previous_unfold} {multiplier_name}
  close_cyclotomic_row{row} {BASE.lean_complex(quotient)}

"""
            )
        previous_hypothesis = ""
        previous_term = ""
        if previous_name is not None:
            previous_hypothesis = f"""  have previous :=
    {previous_name} Y commutesA commutesDiagonal
"""
            previous_term = "previous\n      + "
        identity_rewrites = ",\n      ".join(
            coefficient_identity_names
        )
        chunks.append(
            f"""private theorem {step_name}
    (Y : Matrix (Fin {dimension}) (Fin {dimension}) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow{row}TransformedGeneratorA =
        alternatingSixAmbientRow{row}TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow{row}GeneratorBDiagonal =
        alternatingSixAmbientRow{row}GeneratorBDiagonal * Y) :
    {lean_named_linear_form(next_coefficient_names, reduction.allowed_pairs)} = 0 := by
{previous_hypothesis}  have equation :=
    row{row}_commutatorEquation{equation_row}{equation_column}
      Y commutesA commutesDiagonal
  rw [
      {identity_rewrites}]
  linear_combination
    {previous_term}{multiplier_name} * equation

"""
        )
        previous = next_coefficients
        previous_name = step_name
        previous_coefficient_names = next_coefficient_names
    if previous != reduction.reduced_rows[reduction_row]:
        raise ValueError(
            f"sequential combination for row {row} {pair} "
            "did not reach the checked reduced equation"
        )
    chunks.append(
        f"""theorem row{row}_{reduced_name}
    (Y : Matrix (Fin {dimension}) (Fin {dimension}) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow{row}TransformedGeneratorA =
        alternatingSixAmbientRow{row}TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow{row}GeneratorBDiagonal =
        alternatingSixAmbientRow{row}GeneratorBDiagonal * Y) :
    {goal} := by
  have reduced :=
    {previous_name} Y commutesA commutesDiagonal
  simp only [
      {",\n      ".join(previous_coefficient_names)}] at reduced
  linear_combination reduced

"""
    )
    application = f"""  have {reduced_name} : {goal} :=
    row{row}_{reduced_name} Y commutesA commutesDiagonal
"""
    return "".join(chunks), application, reduced_name


def render_scalar_identity_rows(
    metadata,
    data,
    reduction,
) -> tuple[str, str]:
    row = metadata.row
    dimension = metadata.dimension
    free_pair = (dimension - 1, dimension - 1)
    reduced_name_by_pair = {
        BASE.reduced_relation_goal(
            metadata, reduction, reduction_row
        )[0]: BASE.reduced_relation_goal(
            metadata, reduction, reduction_row
        )[1]
        for reduction_row in range(len(reduction.pivots))
    }
    declarations: list[str] = []
    dispatch: list[str] = []
    for output_row in range(dimension):
        branches: list[str] = []
        for output_column in range(dimension):
            pair = (output_row, output_column)
            if pair == free_pair:
                proof = (
                    "by simp [Matrix.HasScalarIdentityRow]"
                )
            elif data.labels[output_row] != data.labels[output_column]:
                proof = f"""by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow{row}_off_block
            Y commutesDiagonal {output_row} {output_column} (by decide)"""
            else:
                reduced_name = reduced_name_by_pair[pair]
                proof = f"""by
        simpa [Matrix.HasScalarIdentityRow] using
          row{row}_{reduced_name}
            Y commutesA commutesDiagonal"""
            branches.append(f"  · exact {proof}\n")
        declarations.append(
            f"""private theorem row{row}_scalarIdentityRow{output_row}
    (Y : Matrix (Fin {dimension}) (Fin {dimension}) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow{row}TransformedGeneratorA =
        alternatingSixAmbientRow{row}TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow{row}GeneratorBDiagonal =
        alternatingSixAmbientRow{row}GeneratorBDiagonal * Y) :
    Matrix.HasScalarIdentityRow
      Y (Y {dimension - 1} {dimension - 1}) {output_row} := by
  intro j
  fin_cases j
{"".join(branches)}
"""
        )
        dispatch.append(
            f"""  · exact row{row}_scalarIdentityRow{output_row}
      Y commutesA commutesDiagonal
"""
        )
    return "".join(declarations), "".join(dispatch)


def render_sequential_commutant_module(metadata, data) -> str:
    row = metadata.row
    dimension = metadata.dimension
    reduction = BASE.row_reduce_commutator(data)
    equations = BASE.restricted_commutator_rows(
        data.transformed_a, reduction.allowed_pairs
    )
    equation_support = sorted(
        {
            index
            for combination in reduction.combinations
            for index, coefficient in enumerate(combination)
            if coefficient != BASE.CyclotomicElement(0)
        }
    )
    equation_lemmas = "".join(
        render_commutator_equation(
            metadata, data, reduction, equations, index
        )
        for index in equation_support
    )
    reduced_chunks: list[str] = []
    for reduction_row in range(len(reduction.pivots)):
        chunk, application, name = (
            render_sequential_reduced_relation(
                metadata, reduction, equations, reduction_row
            )
        )
        reduced_chunks.append(chunk)
    scalar_identity_rows, scalar_identity_dispatch = (
        render_scalar_identity_rows(metadata, data, reduction)
    )
    return f"""/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DiagonalBasisMatrixCommutant
import McKayConjecture.Character.MatrixScalarIdentity
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow{row}DiagonalData

/-!
# Scalar common commutant for ambient row {row}

The second generator is diagonal in the checked basis.  The exact
commutator system is normalized one equation at a time, and each reduced
relation is assembled from short checked combination steps.  This keeps
every declaration within Lean's default elaboration budget.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

{render_off_block_theorem(metadata)}
{equation_lemmas}
{"".join(reduced_chunks)}
{scalar_identity_rows}
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
  refine ⟨Y {dimension - 1} {dimension - 1}, ?_⟩
  apply Matrix.eq_smul_one_of_scalar_identity_rows
  intro i
  fin_cases i
{scalar_identity_dispatch}

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


def sequential_commutant_certificate_data(metadata, data):
    """Compute the shared exact data for partitioned commutant modules."""

    reduction = BASE.row_reduce_commutator(data)
    equations = BASE.restricted_commutator_rows(
        data.transformed_a, reduction.allowed_pairs
    )
    equation_support = sorted(
        {
            index
            for combination in reduction.combinations
            for index, coefficient in enumerate(combination)
            if coefficient != BASE.CyclotomicElement(0)
        }
    )
    return reduction, equations, equation_support


def render_sequential_commutant_core_module(
    metadata,
    data,
    reduction,
    equations,
    equation_support,
) -> str:
    """Render off-block vanishing and the checked commutator equations."""

    row = metadata.row
    equation_lemmas = "".join(
        render_commutator_equation(
            metadata, data, reduction, equations, index
        )
        for index in equation_support
    )
    return f"""/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DiagonalBasisMatrixCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow{row}DiagonalData

/-!
# Commutator equations for ambient row {row}

This generated core records off-block vanishing and the exact commutator
equations used by the chained row-reduction certificates.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

{render_off_block_theorem(metadata)}
{equation_lemmas}
end InductiveMcKay
end McKayConjecture
"""


def render_sequential_commutant_reduction_module(
    metadata,
    reduction,
    equations,
    reduction_row: int,
) -> str:
    """Render one reduced relation in a serialized import chain."""

    row = metadata.row
    dependency = (
        f"AlternatingSixAmbientRow{row}DiagonalCommutantCore"
        if reduction_row == 0
        else (
            f"AlternatingSixAmbientRow{row}"
            f"DiagonalCommutantReduction{reduction_row - 1:02d}"
        )
    )
    chunk, _, reduced_name = render_sequential_reduced_relation(
        metadata, reduction, equations, reduction_row
    )
    pair, _, _ = BASE.reduced_relation_goal(
        metadata, reduction, reduction_row
    )
    return f"""/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.{dependency}

/-!
# Ambient row {row} commutant reduction {reduction_row:02d}

This generated module checks the reduced relation `{reduced_name}` for
matrix coordinate {pair}.  Its import of the preceding reduction serializes
clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

{chunk}
end InductiveMcKay
end McKayConjecture
"""


def render_sequential_commutant_wrapper_module(
    metadata,
    data,
    reduction,
) -> str:
    """Assemble reduced relations into the stable scalar-commutant API."""

    row = metadata.row
    dimension = metadata.dimension
    final_reduction = len(reduction.pivots) - 1
    scalar_identity_rows, scalar_identity_dispatch = (
        render_scalar_identity_rows(metadata, data, reduction)
    )
    return f"""/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.MatrixScalarIdentity
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow{row}DiagonalCommutantReduction{final_reduction:02d}

/-!
# Scalar common commutant for ambient row {row}

This wrapper assembles the independently checked reduced relations, proves
the transformed common commutant is scalar, and transports the conclusion
back to the original generator basis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

{scalar_identity_rows}
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
  refine ⟨Y {dimension - 1} {dimension - 1}, ?_⟩
  apply Matrix.eq_smul_one_of_scalar_identity_rows
  intro i
  fin_cases i
{scalar_identity_dispatch}

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


def generate(row: str) -> None:
    metadata, data_module = ROWS[row]
    BASE.DATA_PATH = (
        ROOT
        / "McKayConjecture"
        / "InductiveMcKay"
        / f"{data_module}.lean"
    )
    data = BASE.compute_diagonal_data(metadata)
    data_path = (
        BASE.OUTPUT_DIRECTORY
        / f"AlternatingSixAmbientRow{row}DiagonalData.lean"
    )
    commutant_path = (
        BASE.OUTPUT_DIRECTORY
        / f"AlternatingSixAmbientRow{row}DiagonalCommutant.lean"
    )
    data_sources = []
    if metadata.dimension >= 8:
        data_sources.append(
            (
                BASE.OUTPUT_DIRECTORY
                / (
                    f"AlternatingSixAmbientRow{row}"
                    "DiagonalDataCore.lean"
                ),
                BASE.render_data_core_module(
                    metadata, data, data_module
                ),
            )
        )
        data_sources.extend(
            (
                BASE.OUTPUT_DIRECTORY
                / (
                    f"AlternatingSixAmbientRow{row}"
                    f"TransformedDataRow{output_row}.lean"
                ),
                BASE.render_transformed_data_row_module(
                    metadata, data, output_row
                ),
            )
            for output_row in range(metadata.dimension)
        )
        data_sources.append(
            (
                data_path,
                BASE.render_partitioned_data_wrapper_module(metadata),
            )
        )
    else:
        data_sources.append(
            (
                data_path,
                BASE.render_data_module(
                    metadata, data, data_module
                ),
            )
        )
    commutant_sources = []
    if metadata.dimension >= 8:
        reduction, equations, equation_support = (
            sequential_commutant_certificate_data(metadata, data)
        )
        commutant_sources.append(
            (
                BASE.OUTPUT_DIRECTORY
                / (
                    f"AlternatingSixAmbientRow{row}"
                    "DiagonalCommutantCore.lean"
                ),
                render_sequential_commutant_core_module(
                    metadata,
                    data,
                    reduction,
                    equations,
                    equation_support,
                ),
            )
        )
        commutant_sources.extend(
            (
                BASE.OUTPUT_DIRECTORY
                / (
                    f"AlternatingSixAmbientRow{row}"
                    f"DiagonalCommutantReduction{reduction_row:02d}.lean"
                ),
                render_sequential_commutant_reduction_module(
                    metadata,
                    reduction,
                    equations,
                    reduction_row,
                ),
            )
            for reduction_row in range(len(reduction.pivots))
        )
        commutant_sources.append(
            (
                commutant_path,
                render_sequential_commutant_wrapper_module(
                    metadata, data, reduction
                ),
            )
        )
    else:
        commutant_sources.append(
            (
                commutant_path,
                BASE.render_commutant_module(metadata, data),
            )
        )
    changed_data_paths = [
        path
        for path, source in data_sources
        if BASE.write_if_changed(path, source)
    ]
    changed_commutant_paths = [
        path
        for path, source in commutant_sources
        if BASE.write_if_changed(path, source)
    ]
    action = (
        "wrote"
        if changed_data_paths or changed_commutant_paths
        else "unchanged"
    )
    data_description = ", ".join(
        str(path.relative_to(ROOT))
        for path, _ in data_sources
    )
    commutant_description = ", ".join(
        str(path.relative_to(ROOT))
        for path, _ in commutant_sources
    )
    print(
        f"{action} {data_description} and "
        f"{commutant_description}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "rows",
        nargs="+",
        choices=tuple(ROWS),
        help="two-digit numeric ordinary-row labels",
    )
    arguments = parser.parse_args()
    for row in arguments.rows:
        generate(row)


if __name__ == "__main__":
    main()
