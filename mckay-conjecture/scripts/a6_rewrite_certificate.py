#!/usr/bin/env python3
"""Proof-producing shortlex completion for the ATLAS presentation of A6.

This is a discovery/generation tool.  Every derived rule carries a short
path whose steps cite either a defining relation, a free cancellation, or
an earlier rule.  Thus the resulting proof is a DAG rather than a flattened
product of conjugates.
"""

from collections import deque
from dataclasses import dataclass
from pathlib import Path as FilePath
import sys
from typing import Optional

A, AI, B, BI = range(4)
NAMES = "aAbB"
INVERSE = {A: AI, AI: A, B: BI, BI: B}

Word = tuple[int, ...]
Vector = tuple[int, int, int, int]


def inverse_word(word: Word) -> Word:
    return tuple(INVERSE[x] for x in reversed(word))


def shortlex_key(word: Word):
    return (len(word), word)


def pretty(word: Word) -> str:
    return "".join(NAMES[x] for x in word) or "1"


def add_vector(left: Vector, right: Vector) -> Vector:
    return tuple(x + y for x, y in zip(left, right))


def neg_vector(vector: Vector) -> Vector:
    return tuple(-x for x in vector)


ZERO: Vector = (0, 0, 0, 0)


@dataclass(frozen=True)
class Atom:
    """One contextual equality step.

    kind is "rule", "cancel", or "relator".  For rules, index is the stable
    rule id.  For cancellations it is the letter being cancelled with its
    inverse.  For relators it is the defining-relator index.
    """

    left: Word
    right: Word
    kind: str
    index: int
    forward: bool


Path = tuple[Atom, ...]


@dataclass
class Rule:
    id: int
    lhs: Word
    rhs: Word
    proof: Path
    weight: Vector


@dataclass
class Equation:
    left: Word
    right: Word
    proof: Path


def reverse_atom(atom: Atom) -> Atom:
    return Atom(atom.left, atom.right, atom.kind, atom.index, not atom.forward)


def reverse_path(path: Path) -> Path:
    return tuple(reverse_atom(atom) for atom in reversed(path))


def atom_source_target(atom: Atom, rules_by_id: list[Rule]) -> tuple[Word, Word]:
    if atom.kind == "rule":
        pattern_left = rules_by_id[atom.index].lhs
        pattern_right = rules_by_id[atom.index].rhs
    elif atom.kind == "cancel":
        pattern_left = (atom.index, INVERSE[atom.index])
        pattern_right = ()
    elif atom.kind == "relator":
        pattern_left = RELATORS[atom.index]
        pattern_right = ()
    elif atom.kind == "relatorInv":
        pattern_left = inverse_word(RELATORS[atom.index])
        pattern_right = ()
    else:
        raise ValueError(atom.kind)
    if not atom.forward:
        pattern_left, pattern_right = pattern_right, pattern_left
    return (
        atom.left + pattern_left + atom.right,
        atom.left + pattern_right + atom.right,
    )


def atom_weight(atom: Atom, rules_by_id: list[Rule]) -> Vector:
    if atom.kind == "rule":
        weight = rules_by_id[atom.index].weight
    elif atom.kind == "cancel":
        weight = ZERO
    elif atom.kind == "relator":
        weight = tuple(1 if i == atom.index else 0 for i in range(4))
    elif atom.kind == "relatorInv":
        weight = tuple(-1 if i == atom.index else 0 for i in range(4))
    else:
        raise ValueError(atom.kind)
    return weight if atom.forward else neg_vector(weight)


def path_weight(path: Path, rules_by_id: list[Rule]) -> Vector:
    result = ZERO
    for atom in path:
        result = add_vector(result, atom_weight(atom, rules_by_id))
    return result


def check_path(source: Word, target: Word, path: Path, rules_by_id: list[Rule]):
    current = source
    for atom in path:
        step_source, step_target = atom_source_target(atom, rules_by_id)
        assert current == step_source, (
            pretty(current),
            pretty(step_source),
            atom,
        )
        current = step_target
    assert current == target, (pretty(current), pretty(target))


RELATORS: tuple[Word, ...] = (
    (A, A),
    (B, B, B, B),
    (A, B) * 5,
    (A, B, B) * 5,
)

rules_by_id: list[Rule] = []
ordered_rules: list[Rule] = []
pending: deque[Equation] = deque()
loops: list[Equation] = []


def contextual_atom(
    word: Word,
    position: int,
    rule: Rule,
    forward: bool = True,
) -> Atom:
    pattern = rule.lhs if forward else rule.rhs
    return Atom(
        word[:position],
        word[position + len(pattern) :],
        "rule",
        rule.id,
        forward,
    )


def reduce_word(word: Word, record_path: bool = False):
    word = tuple(word)
    path: list[Atom] = []
    while True:
        changed = False
        for position in range(len(word) + 1):
            candidates = [
                rule
                for rule in ordered_rules
                if word[position : position + len(rule.lhs)] == rule.lhs
            ]
            if candidates:
                rule = max(candidates, key=lambda r: (len(r.lhs), r.id))
                if record_path:
                    path.append(contextual_atom(word, position, rule))
                word = (
                    word[:position]
                    + rule.rhs
                    + word[position + len(rule.lhs) :]
                )
                changed = True
                break
        if not changed:
            return (word, tuple(path)) if record_path else word


def queue_equation(left: Word, right: Word, proof: Path):
    pending.append(Equation(tuple(left), tuple(right), tuple(proof)))


def all_critical_pairs(first: Rule, second: Rule):
    lhs1, rhs1 = first.lhs, first.rhs
    lhs2, rhs2 = second.lhs, second.rhs
    for overlap in range(1, min(len(lhs1), len(lhs2)) + 1):
        if lhs1[-overlap:] == lhs2[:overlap]:
            prefix = lhs1[:-overlap]
            common = lhs1 + lhs2[overlap:]
            left = rhs1 + lhs2[overlap:]
            right = prefix + rhs2
            first_step = contextual_atom(common, 0, first)
            second_step = contextual_atom(common, len(prefix), second)
            yield Equation(
                left,
                right,
                (reverse_atom(first_step), second_step),
            )
    for position in range(len(lhs1) - len(lhs2) + 1):
        if lhs1[position : position + len(lhs2)] == lhs2:
            common = lhs1
            left = rhs1
            right = lhs1[:position] + rhs2 + lhs1[position + len(lhs2) :]
            first_step = contextual_atom(common, 0, first)
            second_step = contextual_atom(common, position, second)
            yield Equation(
                left,
                right,
                (reverse_atom(first_step), second_step),
            )


def insert_rule(equation: Equation):
    original_left, original_right = equation.left, equation.right
    left, left_reduction = reduce_word(original_left, record_path=True)
    right, right_reduction = reduce_word(original_right, record_path=True)
    proof = reverse_path(left_reduction) + equation.proof + right_reduction
    check_path(left, right, proof, rules_by_id)
    if left == right:
        loops.append(Equation(left, right, proof))
        return False
    if shortlex_key(left) < shortlex_key(right):
        left, right = right, left
        proof = reverse_path(proof)
    for old_rule in ordered_rules:
        if old_rule.lhs == left:
            if right != old_rule.rhs:
                old_step = Atom((), (), "rule", old_rule.id, True)
                queue_equation(
                    right,
                    old_rule.rhs,
                    reverse_path(proof) + (old_step,),
                )
            return False
    rule = Rule(
        len(rules_by_id),
        left,
        right,
        proof,
        path_weight(proof, rules_by_id),
    )
    rules_by_id.append(rule)
    old_rules = list(ordered_rules)
    ordered_rules.append(rule)
    ordered_rules.sort(key=lambda item: shortlex_key(item.lhs), reverse=True)
    for old_rule in old_rules:
        pending.extend(all_critical_pairs(rule, old_rule))
        pending.extend(all_critical_pairs(old_rule, rule))
    pending.extend(all_critical_pairs(rule, rule))
    return True


for letter in (A, AI, B, BI):
    insert_rule(
        Equation(
            (letter, INVERSE[letter]),
            (),
            (Atom((), (), "cancel", letter, True),),
        )
    )

for relation_index, relator in enumerate(RELATORS):
    insert_rule(
        Equation(
            relator,
            (),
            (Atom((), (), "relator", relation_index, True),),
        )
    )
    inverse_relator = inverse_word(relator)
    insert_rule(
        Equation(
            inverse_relator,
            (),
            (
                Atom(
                    (),
                    (),
                    "relatorInv",
                    relation_index,
                    True,
                ),
            ),
        )
    )

steps = 0
while pending and steps < 10_000 and len(rules_by_id) < 2_000:
    insert_rule(pending.popleft())
    steps += 1

print(
    "completion",
    {
        "steps": steps,
        "rules": len(rules_by_id),
        "pending": len(pending),
        "loops": len(loops),
    },
)
print(
    "proof DAG",
    {
        "atoms": sum(len(rule.proof) for rule in rules_by_id),
        "max_rule_atoms": max(map(lambda rule: len(rule.proof), rules_by_id)),
        "max_dependency": max(
            (
                rule.id - atom.index
                for rule in rules_by_id
                for atom in rule.proof
                if atom.kind == "rule"
            ),
            default=0,
        ),
    },
)

normal_forms: set[Word] = {()}
frontier: deque[Word] = deque([()])
transitions = {}
while frontier and len(normal_forms) <= 10_000:
    word = frontier.popleft()
    for letter in range(4):
        reduced, path = reduce_word(word + (letter,), record_path=True)
        transitions[word, letter] = (reduced, path)
        if reduced not in normal_forms:
            normal_forms.add(reduced)
            frontier.append(reduced)

normal_forms = set(normal_forms)
print(
    "normal forms",
    {
        "count": len(normal_forms),
        "frontier": len(frontier),
        "max_length": max(map(len, normal_forms)),
        "transition_atoms": sum(len(path) for _, path in transitions.values()),
        "max_transition_atoms": max(
            len(path) for _, path in transitions.values()
        ),
    },
)

loop_vectors = {}
for index, equation in enumerate(loops):
    vector = path_weight(equation.proof, rules_by_id)
    if vector != ZERO and vector not in loop_vectors:
        loop_vectors[vector] = index

print("nonzero loop vectors", len(loop_vectors))
for vector, index in sorted(
    loop_vectors.items(),
    key=lambda item: (sum(abs(x) for x in item[0]), item[0]),
)[:80]:
    print("loop", index, vector, "atoms", len(loops[index].proof))

try:
    from itertools import combinations
    from sympy import Matrix
    from sympy.matrices.normalforms import smith_normal_form
    from sympy.polys.domains import ZZ

    complement_vectors = [(3, 0, -2, 1), (0, 4, 3, -3)]
    loop_items = list(loop_vectors.items())
    best_pair = None
    for (first_vector, first_index), (second_vector, second_index) in combinations(
        loop_items, 2
    ):
        matrix = Matrix(
            complement_vectors + [first_vector, second_vector]
        )
        determinant = abs(int(matrix.det()))
        if determinant == 6:
            score = (
                len(loops[first_index].proof) + len(loops[second_index].proof),
                sum(abs(x) for x in first_vector)
                + sum(abs(x) for x in second_vector),
            )
            candidate = (
                score,
                first_index,
                first_vector,
                second_index,
                second_vector,
            )
            if best_pair is None or candidate < best_pair:
                best_pair = candidate
    print("best determinant-six loop pair", best_pair)
    all_matrix = Matrix(complement_vectors + list(loop_vectors))
    print(
        "all lattice smith",
        smith_normal_form(all_matrix, domain=ZZ),
    )
except ImportError:
    pass

for rule in rules_by_id:
    check_path(rule.lhs, rule.rhs, rule.proof, rules_by_id)
for equation in loops:
    check_path(equation.left, equation.right, equation.proof, rules_by_id)


def raw_word(word: Word) -> str:
    return "".join(NAMES[letter] for letter in word)


def encode_atom(atom: Atom) -> str:
    kind = {
        "rule": "r",
        "cancel": "c",
        "relator": "d",
        "relatorInv": "i",
    }[atom.kind]
    return ",".join(
        [
            raw_word(atom.left),
            raw_word(atom.right),
            kind,
            str(atom.index),
            "1" if atom.forward else "0",
        ]
    )


def encode_path(path: Path) -> str:
    return ";".join(encode_atom(atom) for atom in path)


def lean_letter(letter: int) -> str:
    generator = 0 if letter in (A, AI) else 1
    positive = letter in (A, B)
    return f"({generator}, {'true' if positive else 'false'})"


def lean_word(word: Word) -> str:
    return "[" + ", ".join(lean_letter(letter) for letter in word) + "]"


def lean_atom(atom: Atom) -> str:
    kind = {
        "rule": ".rule",
        "cancel": ".cancel",
        "relator": ".relator",
        "relatorInv": ".inverseRelator",
    }[atom.kind]
    return (
        f"⟨{lean_word(atom.left)}, {lean_word(atom.right)}, "
        f"{kind}, {atom.index}, "
        f"{'true' if atom.forward else 'false'}⟩"
    )


def lean_path(path: Path) -> str:
    return "[" + ", ".join(lean_atom(atom) for atom in path) + "]"


def lean_int(value: int) -> str:
    return str(value) if value >= 0 else f"({value})"


def lean_weight(vector: Vector) -> str:
    return "![" + ", ".join(lean_int(value) for value in vector) + "]"


def header(import_name: str, title: str) -> str:
    return f"""/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import {import_name}

/-!
# {title}

This file is generated by `tmp/a6_dag_kb.py`.  Lean independently checks
every proof path, so the generator is not part of the trusted base.
-/

namespace McKayConjecture
namespace GroupTheory

"""


FOOTER = """
end GroupTheory
end McKayConjecture
"""


def emit_data(output_directory: FilePath):
    output_directory.mkdir(parents=True, exist_ok=True)
    sorted_normal_forms = sorted(normal_forms, key=shortlex_key)
    normal_index = {
        word: index for index, word in enumerate(sorted_normal_forms)
    }

    data = [
        header(
            "McKayConjecture.GroupTheory.AlternatingSixRewriteCertificateChecker",
            "Generated `A₆` rewrite rules and normal words",
        ),
        "set_option linter.style.longLine false\n\n",
        "/-- The 360 certified shortlex normal words. -/\n",
        "def alternatingSixRewriteNormalWords :\n",
        "    Fin 360 → AlternatingSixRewriteWord :=\n",
        "  fun i =>\n",
        "    match i.val with\n",
    ]
    for index, word in enumerate(sorted_normal_forms[:-1]):
        data.append(f"    | {index} => {lean_word(word)}\n")
    data.append(f"    | _ => {lean_word(sorted_normal_forms[-1])}\n\n")
    data.extend(
        [
            "/-- The 188 rules, in acyclic derivation order. -/\n",
            "def alternatingSixRewriteRules :\n",
            "    Fin 188 → AlternatingSixRewriteRule :=\n",
            "  fun i =>\n",
            "    match i.val with\n",
        ]
    )
    for rule in rules_by_id[:-1]:
        data.append(
            f"    | {rule.id} => ⟨{lean_word(rule.lhs)}, "
            f"{lean_word(rule.rhs)}, {lean_path(rule.proof)}, "
            f"{lean_weight(rule.weight)}⟩\n"
        )
    rule = rules_by_id[-1]
    data.append(
        f"    | _ => ⟨{lean_word(rule.lhs)}, "
        f"{lean_word(rule.rhs)}, {lean_path(rule.proof)}, "
        f"{lean_weight(rule.weight)}⟩\n\n"
    )

    selected = [
        min(
            (
                (index, equation)
                for index, equation in enumerate(loops)
                if path_weight(equation.proof, rules_by_id)
                == target_vector
            ),
            key=lambda item: len(item[1].proof),
        )
        for target_vector in [(-5, -5, 0, 2), (-55, -25, 24, -2)]
    ]
    for number, (index, equation) in enumerate(selected):
        vector = path_weight(equation.proof, rules_by_id)
        data.extend(
            [
                f"/-- Selected closed rewrite path {number + 1}. -/\n",
                f"def alternatingSixRewriteKernelLoop{number + 1} :\n",
                "    AlternatingSixRewriteLoop :=\n",
                f"  ⟨{lean_word(equation.left)}, "
                f"{lean_path(equation.proof)}, "
                f"{lean_weight(vector)}⟩\n\n",
            ]
        )
        print(
            "emitting selected loop",
            number + 1,
            index,
            vector,
            len(equation.proof),
        )
    data.append(FOOTER)
    (output_directory / "AlternatingSixRewriteCertificateData.lean").write_text(
        "".join(data)
    )

    rows_per_file = 30
    transition_file_count = (360 + rows_per_file - 1) // rows_per_file
    for file_index in range(transition_file_count):
        start = file_index * rows_per_file
        end = min(360, start + rows_per_file)
        chunks = [
            header(
                "McKayConjecture.GroupTheory.AlternatingSixRewriteCertificateData",
                f"Generated `A₆` transitions, rows {start}–{end - 1}",
            ),
            "set_option linter.style.longLine false\n\n",
        ]
        for index in range(start, end):
            word = sorted_normal_forms[index]
            chunks.extend(
                [
                    f"/-- Right-multiplication row {index}. -/\n",
                    f"def alternatingSixRewriteTransitionRow{index:03d} :\n",
                    "    Fin 4 → AlternatingSixRewriteTransition :=\n",
                    "  ![\n",
                ]
            )
            entries = []
            for letter in range(4):
                target, proof = transitions[word, letter]
                entries.append(
                    f"    ⟨{normal_index[target]}, {lean_path(proof)}⟩"
                )
            chunks.append(",\n".join(entries))
            chunks.append("\n  ]\n\n")
        chunks.append(FOOTER)
        (
            output_directory
            / f"AlternatingSixRewriteTransitions{file_index:02d}.lean"
        ).write_text("".join(chunks))

    transition_imports = "\n".join(
        "import "
        "McKayConjecture.GroupTheory."
        f"AlternatingSixRewriteTransitions{file_index:02d}"
        for file_index in range(transition_file_count)
    )
    umbrella = [
        header(
            "McKayConjecture.GroupTheory.AlternatingSixRewriteTransitions00",
            "The complete generated `A₆` transition table",
        ).replace(
            "import "
            "McKayConjecture.GroupTheory."
            "AlternatingSixRewriteTransitions00",
            transition_imports,
        )
    ]
    umbrella.extend(
        [
            "/-- All 360 right-multiplication rows. -/\n",
            "def alternatingSixRewriteTransitions :\n",
            "    Fin 360 → Fin 4 → AlternatingSixRewriteTransition :=\n",
            "  fun i =>\n",
            "    match i.val with\n",
        ]
    )
    for index in range(359):
        umbrella.append(
            f"    | {index} => alternatingSixRewriteTransitionRow{index:03d}\n"
        )
    umbrella.append(
        "    | _ => alternatingSixRewriteTransitionRow359\n"
    )
    umbrella.append(FOOTER)
    (output_directory / "AlternatingSixRewriteTransitions.lean").write_text(
        "".join(umbrella)
    )

    rules_per_file = 20
    rule_check_file_count = (
        len(rules_by_id) + rules_per_file - 1
    ) // rules_per_file
    for file_index in range(rule_check_file_count):
        start = file_index * rules_per_file
        end = min(len(rules_by_id), start + rules_per_file)
        chunks = [
            header(
                "McKayConjecture.GroupTheory.AlternatingSixRewriteCertificateData",
                f"Checked `A₆` rewrite rules {start}–{end - 1}",
            )
        ]
        for index in range(start, end):
            chunks.extend(
                [
                    f"theorem alternatingSixRewriteRule{index:03d}_valid :\n",
                    "    AlternatingSixRewriteRule.Valid "
                    "alternatingSixRewriteRules "
                    f"{index} = true := by\n",
                    "  decide\n\n",
                ]
            )
        chunks.append(FOOTER)
        (
            output_directory
            / f"AlternatingSixRewriteRuleChecks{file_index:02d}.lean"
        ).write_text("".join(chunks))

    rule_check_imports = "\n".join(
        "import "
        "McKayConjecture.GroupTheory."
        f"AlternatingSixRewriteRuleChecks{file_index:02d}"
        for file_index in range(rule_check_file_count)
    )
    rule_umbrella = [
        header(
            "McKayConjecture.GroupTheory.AlternatingSixRewriteRuleChecks00",
            "All checked `A₆` rewrite rules",
        ).replace(
            "import "
            "McKayConjecture.GroupTheory."
            "AlternatingSixRewriteRuleChecks00",
            rule_check_imports,
        ),
        "/-- Every generated rule has a valid acyclic proof. -/\n",
        "theorem alternatingSixRewriteRules_valid\n",
        "    (i : Fin 188) :\n",
        "    AlternatingSixRewriteRule.Valid\n",
        "      alternatingSixRewriteRules i = true := by\n",
        "  fin_cases i\n",
    ]
    for index in range(len(rules_by_id)):
        rule_umbrella.append(
            f"  · exact alternatingSixRewriteRule{index:03d}_valid\n"
        )
    rule_umbrella.append(FOOTER)
    (
        output_directory / "AlternatingSixRewriteRuleChecks.lean"
    ).write_text("".join(rule_umbrella))

    for file_index in range(transition_file_count):
        start = file_index * rows_per_file
        end = min(360, start + rows_per_file)
        chunks = [
            header(
                "McKayConjecture.GroupTheory."
                f"AlternatingSixRewriteTransitions{file_index:02d}",
                f"Checked `A₆` transitions {start}–{end - 1}",
            )
        ]
        for index in range(start, end):
            chunks.extend(
                [
                    f"theorem alternatingSixRewriteTransitionRow{index:03d}_valid :\n",
                    "    AlternatingSixRewriteTransition.Valid\n",
                    "      alternatingSixRewriteRules\n",
                    "      alternatingSixRewriteNormalWords\n",
                    "      alternatingSixRewriteTransitionRow"
                    f"{index:03d} {index} = true := by\n",
                    "  decide\n\n",
                ]
            )
        chunks.append(FOOTER)
        (
            output_directory
            / f"AlternatingSixRewriteTransitionChecks{file_index:02d}.lean"
        ).write_text("".join(chunks))

    transition_check_imports = "\n".join(
        "import "
        "McKayConjecture.GroupTheory."
        f"AlternatingSixRewriteTransitionChecks{file_index:02d}"
        for file_index in range(transition_file_count)
    )
    transition_checks = [
        header(
            "McKayConjecture.GroupTheory.AlternatingSixRewriteTransitionChecks00",
            "All checked `A₆` normal-form transitions",
        ).replace(
            "import "
            "McKayConjecture.GroupTheory."
            "AlternatingSixRewriteTransitionChecks00",
            transition_check_imports
            + "\nimport "
            "McKayConjecture.GroupTheory."
            "AlternatingSixRewriteTransitions",
        ),
        "/-- Every generated normal-form transition is valid. -/\n",
    ]
    transition_checks.extend(
        [
            "theorem alternatingSixRewriteTransitions_valid\n",
            "    (i : Fin 360) :\n",
            "    AlternatingSixRewriteTransition.Valid\n",
            "      alternatingSixRewriteRules\n",
            "      alternatingSixRewriteNormalWords\n",
            "      (alternatingSixRewriteTransitions i) i = true := by\n",
            "  fin_cases i\n",
        ]
    )
    for index in range(360):
        transition_checks.append(
            "  · exact "
            f"alternatingSixRewriteTransitionRow{index:03d}_valid\n"
        )
    transition_checks.append(FOOTER)
    (
        output_directory / "AlternatingSixRewriteTransitionChecks.lean"
    ).write_text("".join(transition_checks))


if "--emit" in sys.argv:
    emit_data(
        FilePath(__file__).resolve().parents[1]
        / "McKayConjecture"
        / "GroupTheory"
    )
