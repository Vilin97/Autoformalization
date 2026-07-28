#!/usr/bin/env python3
"""Independently validate the finite permutation certificates used for the A6 Schur cover.

The input matrices are the two ATLAS projective representations.  We realize
F_{p^2} as F_p[z]/(z^2-z-1), correct the first matrix by the first relation-
module row, and let the resulting matrices act on their full vector spaces.
The Lean certificate writes the same actions in finite-field coordinates;
this script checks its source matrices, correction, and relation values.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable


@dataclass(frozen=True)
class Fq:
    """An element a+b*z of F_p[z]/(z^2-z-1)."""

    a: int
    b: int
    p: int

    def __post_init__(self) -> None:
        object.__setattr__(self, "a", self.a % self.p)
        object.__setattr__(self, "b", self.b % self.p)

    def __add__(self, other: "Fq") -> "Fq":
        assert self.p == other.p
        return Fq(self.a + other.a, self.b + other.b, self.p)

    def __neg__(self) -> "Fq":
        return Fq(-self.a, -self.b, self.p)

    def __sub__(self, other: "Fq") -> "Fq":
        return self + -other

    def __mul__(self, other: "Fq") -> "Fq":
        assert self.p == other.p
        # z^2 = z + 1
        return Fq(
            self.a * other.a + self.b * other.b,
            self.a * other.b + self.b * other.a + self.b * other.b,
            self.p,
        )

    def __pow__(self, exponent: int) -> "Fq":
        if exponent < 0:
            return self.inverse() ** (-exponent)
        result = Fq(1, 0, self.p)
        base = self
        while exponent:
            if exponent & 1:
                result = result * base
            base = base * base
            exponent //= 2
        return result

    def inverse(self) -> "Fq":
        assert self != Fq(0, 0, self.p)
        return self ** (self.p * self.p - 2)

    def code(self) -> int:
        return self.a + self.p * self.b

    @staticmethod
    def decode(code: int, p: int) -> "Fq":
        return Fq(code % p, code // p, p)


Matrix = tuple[tuple[Fq, ...], ...]


def identity_matrix(n: int, p: int) -> Matrix:
    return tuple(
        tuple(Fq(int(i == j), 0, p) for j in range(n))
        for i in range(n)
    )


def matrix_mul(left: Matrix, right: Matrix) -> Matrix:
    n = len(left)
    zero = Fq(0, 0, left[0][0].p)
    return tuple(
        tuple(
            sum((left[i][k] * right[k][j] for k in range(n)), zero)
            for j in range(n)
        )
        for i in range(n)
    )


def matrix_pow(matrix: Matrix, exponent: int) -> Matrix:
    if exponent < 0:
        # The tiny matrices here have orders dividing 720; exhaustive search is
        # simpler and less error-prone than a separate determinant formula.
        inverse = identity_matrix(len(matrix), matrix[0][0].p)
        while matrix_mul(matrix, inverse) != identity_matrix(
            len(matrix), matrix[0][0].p
        ):
            inverse = matrix_mul(inverse, matrix)
        return matrix_pow(inverse, -exponent)
    result = identity_matrix(len(matrix), matrix[0][0].p)
    base = matrix
    while exponent:
        if exponent & 1:
            result = matrix_mul(result, base)
        base = matrix_mul(base, base)
        exponent //= 2
    return result


def matrix_vector_mul(matrix: Matrix, vector: tuple[Fq, ...]) -> tuple[Fq, ...]:
    zero = Fq(0, 0, matrix[0][0].p)
    return tuple(
        sum((matrix[i][j] * vector[j] for j in range(len(vector))), zero)
        for i in range(len(vector))
    )


def vector_decode(code: int, n: int, p: int) -> tuple[Fq, ...]:
    q = p * p
    coordinates = []
    for _ in range(n):
        coordinates.append(Fq.decode(code % q, p))
        code //= q
    return tuple(coordinates)


def vector_code(vector: Iterable[Fq], p: int) -> int:
    q = p * p
    result = 0
    place = 1
    for coordinate in vector:
        result += place * coordinate.code()
        place *= q
    return result


def permutation(matrix: Matrix) -> list[int]:
    p = matrix[0][0].p
    size = (p * p) ** len(matrix)
    return [
        vector_code(
            matrix_vector_mul(matrix, vector_decode(index, len(matrix), p)), p
        )
        for index in range(size)
    ]


def inverse_permutation(values: list[int]) -> list[int]:
    result = [0] * len(values)
    for index, value in enumerate(values):
        result[value] = index
    return result


def relation_values(a: Matrix, b: Matrix) -> tuple[Matrix, Matrix, Matrix, Matrix]:
    return (
        matrix_pow(a, 2),
        matrix_pow(b, 4),
        matrix_pow(matrix_mul(a, b), 5),
        matrix_pow(matrix_mul(a, matrix_pow(b, 2)), 5),
    )


def corrected_generators(a: Matrix, b: Matrix) -> tuple[Matrix, Matrix]:
    e0, _, e2, e3 = relation_values(a, b)
    h1 = matrix_mul(
        matrix_mul(matrix_pow(e0, 3), matrix_pow(e2, -2)), e3
    )
    return matrix_mul(a, matrix_pow(h1, -1)), b


def assert_certificate(a: Matrix, b: Matrix, expected_order: int) -> None:
    one = identity_matrix(len(a), a[0][0].p)
    k0, k1, k2, k3 = relation_values(a, b)
    generators = (a, b, k0, k1, k2, k3)
    for k in (k0, k1, k2, k3):
        for generator in generators:
            assert matrix_mul(k, generator) == matrix_mul(generator, k)
    assert (
        matrix_mul(matrix_mul(matrix_pow(k0, 3), matrix_pow(k2, -2)), k3)
        == one
    )
    assert (
        matrix_mul(matrix_mul(matrix_pow(k1, 4), matrix_pow(k2, 3)),
                   matrix_pow(k3, -3))
        == one
    )
    assert matrix_pow(k0, expected_order) == one
    assert all(matrix_pow(k0, i) != one for i in range(1, expected_order))


def main() -> None:
    f3 = lambda a=0, b=0: Fq(a, b, 3)
    z3 = f3(0, 1)
    a2_raw: Matrix = (
        (z3**6, f3()),
        (z3**3, z3**2),
    )
    b2: Matrix = (
        (f3(), z3**8),
        (z3**4, z3**2),
    )
    a2, b2 = corrected_generators(a2_raw, b2)
    assert_certificate(a2, b2, 2)

    f2 = lambda a=0, b=0: Fq(a, b, 2)
    z2 = f2(0, 1)
    a3_raw: Matrix = (
        (f2(1), f2(), f2()),
        (f2(), f2(), f2(1)),
        (f2(), f2(1), f2()),
    )
    b3: Matrix = (
        (f2(), f2(1), f2()),
        (f2(1), f2(), f2()),
        (f2(1), z2, f2(1)),
    )
    a3, b3 = corrected_generators(a3_raw, b3)
    assert_certificate(a3, b3, 3)

    print("validated corrected actions on 81 and 64 points")


if __name__ == "__main__":
    main()
