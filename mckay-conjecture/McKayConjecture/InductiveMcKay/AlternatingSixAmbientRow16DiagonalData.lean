/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixDegreeFourSixEigenvalues
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixDataDegreeEightNine

/-!
# Checked diagonal data for ambient row 16

This generated module records an exact eigenbasis for the second generator
and the first generator in that basis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Eigenvalue block labels for row 16. -/
def alternatingSixAmbientRow16EigenvalueLabel :
    Fin 8 → Fin 4 :=
  ![0, 0, 1, 1, 2, 2, 3, 3]

/-- Second-generator eigenvalues, including their multiplicities. -/
def alternatingSixAmbientRow16GeneratorBEigenvalue :
    Fin 8 → ℂ :=
  fun i ↦
    alternatingSixOrderFourEigenvalue
      (alternatingSixAmbientRow16EigenvalueLabel i)

/-- Diagonal form of the row 16 second generator. -/
def alternatingSixAmbientRow16GeneratorBDiagonal :
    Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.diagonal
    alternatingSixAmbientRow16GeneratorBEigenvalue

/-- Checked eigenbasis for the row 16 second generator. -/
def alternatingSixAmbientRow16Eigenbasis :
    Matrix (Fin 8) (Fin 8) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [(-1, 0), (1, 8), (1, 12), (-1, 24), (-1, 28)],
      alternatingSixCyclotomicValue [(-1, 0), (1, 8), (1, 12), (-1, 24), (-1, 28)],
      alternatingSixCyclotomicValue [(-1, 12), (-1, 18), (1, 24), (1, 30)],
      alternatingSixCyclotomicValue [(-2, 2), (1, 8), (1, 12), (2, 22), (-1, 24), (-1, 28), (-1, 30)],
      alternatingSixCyclotomicValue [((7 / 11), 0), ((1 / 11), 8), ((-9 / 11), 12), ((-7 / 11), 24), ((-1 / 11), 28)],
      alternatingSixCyclotomicValue [((-1 / 11), 0), ((3 / 11), 8), ((-5 / 11), 12), ((1 / 11), 24), ((-3 / 11), 28)],
      alternatingSixCyclotomicValue [(-1, 12), (1, 18), (1, 24), (-1, 30)],
      alternatingSixCyclotomicValue [(2, 2), (1, 8), (1, 12), (-2, 22), (-1, 24), (-1, 28), (1, 30)]],
    ![alternatingSixCyclotomicValue [(1, 8), (-1, 28)],
      alternatingSixCyclotomicValue [(-1, 0)],
      alternatingSixCyclotomicValue [(-1, 0), (-1, 2), (-1, 6), (-1, 8), (1, 18), (1, 22), (1, 24), (1, 28)],
      alternatingSixCyclotomicValue [(1, 8), (-1, 18), (-1, 28), (1, 30)],
      alternatingSixCyclotomicValue [((14 / 11), 0), ((-1 / 11), 8), ((-16 / 11), 12), ((6 / 11), 24), ((1 / 11), 28)],
      alternatingSixCyclotomicValue [(1, 0), ((-10 / 11), 8), ((-8 / 11), 12), ((8 / 11), 24), ((10 / 11), 28)],
      alternatingSixCyclotomicValue [(-1, 0), (1, 2), (1, 6), (-1, 8), (-1, 18), (-1, 22), (1, 24), (1, 28)],
      alternatingSixCyclotomicValue [(1, 8), (1, 18), (-1, 28), (-1, 30)]],
    ![alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(-1, 0), (1, 6), (1, 8), (1, 12), (1, 24), (-1, 28), (1, 30)],
      alternatingSixCyclotomicValue [(1, 6), (-1, 12), (-1, 18), (1, 24)],
      alternatingSixCyclotomicValue [((-1 / 11), 0), ((-2 / 11), 8), ((2 / 11), 12), ((-6 / 11), 24), ((2 / 11), 28)],
      alternatingSixCyclotomicValue [((-7 / 11), 0), ((8 / 11), 8), ((14 / 11), 12), ((2 / 11), 24), ((-8 / 11), 28)],
      alternatingSixCyclotomicValue [(-1, 0), (-1, 6), (1, 8), (1, 12), (1, 24), (-1, 28), (-1, 30)],
      alternatingSixCyclotomicValue [(-1, 6), (-1, 12), (1, 18), (1, 24)]],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 24)],
      alternatingSixCyclotomicValue [(-1, 0), (1, 6), (1, 8), (-1, 12), (-2, 18), (1, 24), (-1, 28), (2, 30)],
      alternatingSixCyclotomicValue [(1, 0), (-1, 2), (1, 6), (-1, 8), (-2, 18), (1, 22), (2, 24), (1, 28), (-2, 30)],
      alternatingSixCyclotomicValue [((-2 / 11), 0), ((-6 / 11), 8), ((-2 / 11), 12), ((-6 / 11), 24), ((6 / 11), 28)],
      alternatingSixCyclotomicValue [((2 / 11), 0), ((-2 / 11), 8), ((-3 / 11), 24), ((2 / 11), 28)],
      alternatingSixCyclotomicValue [(-1, 0), (-1, 6), (1, 8), (-1, 12), (2, 18), (1, 24), (-1, 28), (-2, 30)],
      alternatingSixCyclotomicValue [(1, 0), (1, 2), (-1, 6), (-1, 8), (2, 18), (-1, 22), (2, 24), (1, 28), (2, 30)]],
    ![alternatingSixCyclotomicValue [(-1, 24)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(-1, 0), (2, 2), (1, 6), (2, 8), (1, 12), (-1, 18), (-2, 22), (-2, 24), (-2, 28)],
      alternatingSixCyclotomicValue [(1, 0), (-1, 6), (1, 12), (-1, 18), (1, 24)],
      alternatingSixCyclotomicValue [((2 / 11), 0), ((-4 / 11), 8), ((-6 / 11), 12), ((3 / 11), 24), ((4 / 11), 28)],
      alternatingSixCyclotomicValue [((-10 / 11), 0), ((14 / 11), 12), ((-10 / 11), 24)],
      alternatingSixCyclotomicValue [(-1, 0), (-2, 2), (-1, 6), (2, 8), (1, 12), (1, 18), (2, 22), (-2, 24), (-2, 28)],
      alternatingSixCyclotomicValue [(1, 0), (1, 6), (1, 12), (1, 18), (1, 24)]],
    ![alternatingSixCyclotomicValue [(-1, 0), (1, 8), (1, 12), (-1, 24), (-1, 28)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0), (-1, 2), (1, 6), (-2, 8), (-1, 12), (-2, 18), (1, 22), (2, 24), (2, 28), (3, 30)],
      alternatingSixCyclotomicValue [(-2, 0), (-1, 2), (1, 6), (2, 12), (-1, 18), (1, 22), (-1, 24), (-1, 30)],
      alternatingSixCyclotomicValue [((5 / 11), 0), ((-3 / 11), 8), ((-5 / 11), 12), ((3 / 11), 24), ((3 / 11), 28)],
      alternatingSixCyclotomicValue [((-4 / 11), 0), ((8 / 11), 8), ((12 / 11), 12), ((-6 / 11), 24), ((-8 / 11), 28)],
      alternatingSixCyclotomicValue [(1, 0), (1, 2), (-1, 6), (-2, 8), (-1, 12), (2, 18), (-1, 22), (2, 24), (2, 28), (-3, 30)],
      alternatingSixCyclotomicValue [(-2, 0), (1, 2), (-1, 6), (2, 12), (1, 18), (-1, 22), (-1, 24), (1, 30)]],
    ![alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue []],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)]]
  ]

/-- Checked inverse of the row 16 eigenbasis. -/
def alternatingSixAmbientRow16EigenbasisInverse :
    Matrix (Fin 8) (Fin 8) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((11 / 20), 0), ((-3 / 20), 8), ((-19 / 20), 12), ((3 / 5), 24), ((3 / 20), 28)],
      alternatingSixCyclotomicValue [((-17 / 20), 0), ((11 / 20), 8), ((23 / 20), 12), ((-7 / 10), 24), ((-11 / 20), 28)],
      alternatingSixCyclotomicValue [((-4 / 5), 0), ((13 / 20), 8), ((1 / 5), 12), ((-17 / 20), 24), ((-13 / 20), 28)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((3 / 4), 8), ((1 / 4), 12), ((-1 / 4), 24), ((-3 / 4), 28)],
      alternatingSixCyclotomicValue [((1 / 20), 0), ((-2 / 5), 8), ((-6 / 5), 12), ((17 / 20), 24), ((2 / 5), 28)],
      alternatingSixCyclotomicValue [((-4 / 5), 8), ((-1 / 10), 12), ((1 / 10), 24), ((4 / 5), 28)],
      alternatingSixCyclotomicValue [((-3 / 20), 0), ((1 / 2), 8), ((1 / 5), 12), ((-3 / 20), 24), ((-1 / 2), 28)],
      alternatingSixCyclotomicValue [((-7 / 20), 0), ((3 / 10), 8), ((-1 / 10), 12), ((11 / 20), 24), ((-3 / 10), 28)]],
    ![alternatingSixCyclotomicValue [((3 / 5), 0), ((-11 / 20), 8), ((1 / 10), 12), ((-1 / 20), 24), ((11 / 20), 28)],
      alternatingSixCyclotomicValue [((-7 / 10), 0), ((7 / 20), 8), ((-9 / 20), 12), ((7 / 20), 24), ((-7 / 20), 28)],
      alternatingSixCyclotomicValue [((2 / 5), 0), ((-7 / 10), 8), ((-17 / 20), 12), ((4 / 5), 24), ((7 / 10), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 12), ((-1 / 4), 24)],
      alternatingSixCyclotomicValue [((17 / 20), 0), ((-4 / 5), 8), ((-3 / 20), 12), ((9 / 20), 24), ((4 / 5), 28)],
      alternatingSixCyclotomicValue [((-3 / 20), 0), ((1 / 10), 8), ((2 / 5), 12), ((2 / 5), 24), ((-1 / 10), 28)],
      alternatingSixCyclotomicValue [((7 / 20), 0), ((-1 / 5), 8), ((-19 / 20), 12), ((1 / 4), 24), ((1 / 5), 28)],
      alternatingSixCyclotomicValue [((21 / 20), 0), ((-2 / 5), 8), ((-7 / 10), 12), ((1 / 10), 24), ((2 / 5), 28)]],
    ![alternatingSixCyclotomicValue [((-9 / 20), 0), ((-1 / 2), 6), ((7 / 20), 8), ((11 / 20), 12), ((1 / 2), 18), ((-2 / 5), 24), ((-7 / 20), 28)],
      alternatingSixCyclotomicValue [((2 / 5), 0), ((-1 / 4), 2), ((1 / 2), 6), ((-1 / 5), 8), ((-3 / 5), 12), ((-1 / 4), 18), ((1 / 4), 22), ((3 / 10), 24), ((1 / 5), 28), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 5), 0), ((-1 / 4), 2), ((-1 / 10), 8), ((-1 / 20), 12), ((1 / 4), 18), ((1 / 4), 22), ((3 / 20), 24), ((1 / 10), 28), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 6), ((-1 / 4), 8), ((1 / 4), 18), ((1 / 4), 28), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 5), 0), ((-1 / 4), 6), ((1 / 10), 8), ((11 / 20), 12), ((1 / 4), 18), ((-2 / 5), 24), ((-1 / 10), 28)],
      alternatingSixCyclotomicValue [((-1 / 5), 2), ((1 / 5), 6), ((1 / 5), 8), ((-1 / 10), 12), ((-2 / 5), 18), ((1 / 5), 22), ((1 / 10), 24), ((-1 / 5), 28), ((1 / 10), 30)],
      alternatingSixCyclotomicValue [((3 / 5), 0), ((-3 / 10), 2), ((-9 / 20), 6), ((-1 / 4), 8), ((-1 / 20), 12), ((2 / 5), 18), ((3 / 10), 22), ((1 / 10), 24), ((1 / 4), 28), ((-3 / 5), 30)],
      alternatingSixCyclotomicValue [((3 / 20), 0), ((-1 / 4), 6), ((-1 / 5), 8), ((3 / 20), 12), ((1 / 4), 18), ((-1 / 5), 24), ((1 / 5), 28), ((-1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 10), 2), ((-1 / 10), 6), ((1 / 2), 8), ((-1 / 20), 18), ((-1 / 10), 22), ((1 / 4), 24), ((-1 / 2), 28), ((1 / 5), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 20), 2), ((-1 / 20), 6), ((-1 / 2), 8), ((1 / 4), 12), ((1 / 10), 18), ((-1 / 20), 22), ((-1 / 2), 24), ((1 / 2), 28), ((-3 / 20), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-7 / 20), 2), ((-13 / 20), 6), ((-1 / 4), 8), ((1 / 4), 12), ((3 / 10), 18), ((7 / 20), 22), ((-1 / 4), 24), ((1 / 4), 28), ((-1 / 5), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 4), 8), ((1 / 2), 12), ((-1 / 4), 18), ((-1 / 4), 24), ((-1 / 4), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-2 / 5), 2), ((-1 / 10), 6), ((1 / 4), 8), ((1 / 4), 12), ((9 / 20), 18), ((2 / 5), 22), ((1 / 4), 24), ((-1 / 4), 28), ((-1 / 20), 30)],
      alternatingSixCyclotomicValue [((11 / 20), 0), ((-1 / 4), 2), ((-1 / 10), 6), ((-2 / 5), 8), ((-9 / 20), 12), ((3 / 10), 18), ((1 / 4), 22), ((1 / 10), 24), ((2 / 5), 28), ((-1 / 10), 30)],
      alternatingSixCyclotomicValue [((-11 / 20), 0), ((-1 / 20), 2), ((-1 / 10), 6), ((3 / 20), 8), ((7 / 10), 12), ((-3 / 20), 18), ((1 / 20), 22), ((-7 / 20), 24), ((-3 / 20), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((3 / 10), 2), ((9 / 20), 6), ((1 / 2), 8), ((3 / 4), 12), ((-3 / 20), 18), ((-3 / 10), 22), ((-1 / 4), 24), ((-1 / 2), 28), ((1 / 10), 30)]],
    ![alternatingSixCyclotomicValue [((7 / 20), 0), ((-11 / 20), 8), ((-3 / 20), 12), ((1 / 5), 24), ((11 / 20), 28)],
      alternatingSixCyclotomicValue [((1 / 20), 0), ((-3 / 20), 8), ((1 / 20), 12), ((1 / 10), 24), ((3 / 20), 28)],
      alternatingSixCyclotomicValue [((2 / 5), 0), ((-9 / 20), 8), ((-1 / 10), 12), ((11 / 20), 24), ((9 / 20), 28)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 8), ((-1 / 4), 12), ((1 / 4), 24), ((1 / 4), 28)],
      alternatingSixCyclotomicValue [((7 / 20), 0), ((1 / 5), 8), ((1 / 10), 12), ((-1 / 20), 24), ((-1 / 5), 28)],
      alternatingSixCyclotomicValue [((2 / 5), 8), ((3 / 10), 12), ((-3 / 10), 24), ((-2 / 5), 28)],
      alternatingSixCyclotomicValue [((-1 / 20), 0), ((-1 / 10), 12), ((-1 / 20), 24)],
      alternatingSixCyclotomicValue [((1 / 20), 0), ((1 / 10), 8), ((-1 / 5), 12), ((-3 / 20), 24), ((-1 / 10), 28)]],
    ![alternatingSixCyclotomicValue [((2 / 5), 0), ((-9 / 20), 8), ((-1 / 10), 12), ((-9 / 20), 24), ((9 / 20), 28)],
      alternatingSixCyclotomicValue [((-3 / 10), 0), ((13 / 20), 8), ((-1 / 20), 12), ((13 / 20), 24), ((-13 / 20), 28)],
      alternatingSixCyclotomicValue [((1 / 10), 0), ((6 / 5), 8), ((7 / 20), 12), ((-3 / 10), 24), ((-6 / 5), 28)],
      alternatingSixCyclotomicValue [(1, 0), ((-1 / 2), 8), ((-1 / 2), 12), ((3 / 4), 24), ((1 / 2), 28)],
      alternatingSixCyclotomicValue [((3 / 20), 0), ((3 / 10), 8), ((-7 / 20), 12), ((-19 / 20), 24), ((-3 / 10), 28)],
      alternatingSixCyclotomicValue [((-19 / 20), 0), ((7 / 10), 8), ((1 / 2), 12), ((-3 / 5), 24), ((-7 / 10), 28)],
      alternatingSixCyclotomicValue [((3 / 4), 0), ((-1 / 10), 8), ((-9 / 20), 12), ((9 / 20), 24), ((1 / 10), 28)],
      alternatingSixCyclotomicValue [((19 / 20), 0), ((-3 / 5), 8), ((-4 / 5), 12), ((2 / 5), 24), ((3 / 5), 28)]],
    ![alternatingSixCyclotomicValue [((-9 / 20), 0), ((1 / 2), 6), ((7 / 20), 8), ((11 / 20), 12), ((-1 / 2), 18), ((-2 / 5), 24), ((-7 / 20), 28)],
      alternatingSixCyclotomicValue [((2 / 5), 0), ((1 / 4), 2), ((-1 / 2), 6), ((-1 / 5), 8), ((-3 / 5), 12), ((1 / 4), 18), ((-1 / 4), 22), ((3 / 10), 24), ((1 / 5), 28), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 5), 0), ((1 / 4), 2), ((-1 / 10), 8), ((-1 / 20), 12), ((-1 / 4), 18), ((-1 / 4), 22), ((3 / 20), 24), ((1 / 10), 28), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 6), ((-1 / 4), 8), ((-1 / 4), 18), ((1 / 4), 28), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 5), 0), ((1 / 4), 6), ((1 / 10), 8), ((11 / 20), 12), ((-1 / 4), 18), ((-2 / 5), 24), ((-1 / 10), 28)],
      alternatingSixCyclotomicValue [((1 / 5), 2), ((-1 / 5), 6), ((1 / 5), 8), ((-1 / 10), 12), ((2 / 5), 18), ((-1 / 5), 22), ((1 / 10), 24), ((-1 / 5), 28), ((-1 / 10), 30)],
      alternatingSixCyclotomicValue [((3 / 5), 0), ((3 / 10), 2), ((9 / 20), 6), ((-1 / 4), 8), ((-1 / 20), 12), ((-2 / 5), 18), ((-3 / 10), 22), ((1 / 10), 24), ((1 / 4), 28), ((3 / 5), 30)],
      alternatingSixCyclotomicValue [((3 / 20), 0), ((1 / 4), 6), ((-1 / 5), 8), ((3 / 20), 12), ((-1 / 4), 18), ((-1 / 5), 24), ((1 / 5), 28), ((1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 10), 2), ((1 / 10), 6), ((1 / 2), 8), ((1 / 20), 18), ((1 / 10), 22), ((1 / 4), 24), ((-1 / 2), 28), ((-1 / 5), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 20), 2), ((1 / 20), 6), ((-1 / 2), 8), ((1 / 4), 12), ((-1 / 10), 18), ((1 / 20), 22), ((-1 / 2), 24), ((1 / 2), 28), ((3 / 20), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((7 / 20), 2), ((13 / 20), 6), ((-1 / 4), 8), ((1 / 4), 12), ((-3 / 10), 18), ((-7 / 20), 22), ((-1 / 4), 24), ((1 / 4), 28), ((1 / 5), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 4), 8), ((1 / 2), 12), ((1 / 4), 18), ((-1 / 4), 24), ((-1 / 4), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((2 / 5), 2), ((1 / 10), 6), ((1 / 4), 8), ((1 / 4), 12), ((-9 / 20), 18), ((-2 / 5), 22), ((1 / 4), 24), ((-1 / 4), 28), ((1 / 20), 30)],
      alternatingSixCyclotomicValue [((11 / 20), 0), ((1 / 4), 2), ((1 / 10), 6), ((-2 / 5), 8), ((-9 / 20), 12), ((-3 / 10), 18), ((-1 / 4), 22), ((1 / 10), 24), ((2 / 5), 28), ((1 / 10), 30)],
      alternatingSixCyclotomicValue [((-11 / 20), 0), ((1 / 20), 2), ((1 / 10), 6), ((3 / 20), 8), ((7 / 10), 12), ((3 / 20), 18), ((-1 / 20), 22), ((-7 / 20), 24), ((-3 / 20), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-3 / 10), 2), ((-9 / 20), 6), ((1 / 2), 8), ((3 / 4), 12), ((3 / 20), 18), ((3 / 10), 22), ((-1 / 4), 24), ((-1 / 2), 28), ((-1 / 10), 30)]]
  ]

/-- The row 16 first generator in the checked diagonal basis. -/
def alternatingSixAmbientRow16TransformedGeneratorA :
    Matrix (Fin 8) (Fin 8) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 2), 8), ((-1 / 2), 12), ((1 / 2), 28)],
      alternatingSixCyclotomicValue [((1 / 4), 8), ((1 / 4), 12), ((-1 / 4), 24), ((-1 / 4), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 2), 2), ((-1 / 2), 6), ((1 / 2), 22), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 6), ((1 / 4), 8), ((-1 / 4), 18), ((-1 / 4), 28)],
      alternatingSixCyclotomicValue [((-15 / 44), 0), ((3 / 22), 8), ((3 / 22), 12), ((-3 / 22), 28)],
      alternatingSixCyclotomicValue [((-15 / 22), 0), ((15 / 44), 8), ((21 / 44), 12), ((-9 / 44), 24), ((-15 / 44), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 2), ((1 / 2), 6), ((-1 / 2), 22), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 6), ((1 / 4), 8), ((1 / 4), 18), ((-1 / 4), 28)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 24)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 8), ((1 / 4), 12), ((-1 / 4), 28)],
      alternatingSixCyclotomicValue [((1 / 2), 2), ((1 / 4), 6), ((1 / 4), 12), ((-3 / 4), 18), ((-1 / 2), 22), (1, 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((3 / 4), 6), ((1 / 2), 12), ((-1 / 2), 18), ((-3 / 4), 24), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((9 / 44), 0), ((-3 / 22), 12), ((9 / 44), 24)],
      alternatingSixCyclotomicValue [((9 / 44), 0), ((-3 / 44), 8), ((-15 / 44), 12), ((9 / 22), 24), ((3 / 44), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 2), ((-1 / 4), 6), ((1 / 4), 12), ((3 / 4), 18), ((1 / 2), 22), (-1, 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-3 / 4), 6), ((1 / 2), 12), ((1 / 2), 18), ((-3 / 4), 24), ((-1 / 2), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 2), ((-1 / 2), 6), ((1 / 4), 8), ((1 / 4), 12), ((1 / 4), 18), ((1 / 4), 22), ((-1 / 4), 28), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 8), ((-1 / 4), 12), ((1 / 4), 24), ((-1 / 4), 28)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 2), ((-1 / 4), 8), ((-1 / 4), 12), ((1 / 4), 18), ((-1 / 4), 22), ((1 / 4), 28)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 2), 2), ((-3 / 4), 6), ((1 / 4), 8), ((1 / 2), 12), ((1 / 4), 18), ((1 / 2), 22), ((-1 / 4), 28), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((-3 / 11), 0), ((1 / 44), 2), ((3 / 22), 6), ((7 / 44), 8), ((7 / 44), 12), ((-5 / 44), 18), ((-1 / 44), 22), ((-7 / 44), 28), ((3 / 44), 30)],
      alternatingSixCyclotomicValue [((-1 / 22), 0), ((-7 / 22), 6), ((1 / 44), 8), ((-3 / 44), 12), ((6 / 11), 18), ((-5 / 44), 24), ((-1 / 44), 28), ((-7 / 22), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((5 / 4), 2), (2, 6), ((-5 / 4), 8), ((-5 / 4), 12), ((-3 / 4), 18), ((-5 / 4), 22), ((5 / 4), 28), (1, 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 2), 2), ((1 / 4), 6), ((-1 / 4), 8), ((-1 / 4), 18), ((1 / 2), 22), ((-1 / 2), 24), ((1 / 4), 28)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 24), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 4), 2), ((1 / 4), 6), ((-1 / 4), 8), ((-1 / 4), 12), ((-1 / 4), 18), ((-1 / 4), 22), ((1 / 4), 24), ((1 / 4), 28), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 6), ((1 / 4), 12), ((-1 / 4), 18), ((1 / 2), 24), ((3 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 2), ((-1 / 4), 18), ((1 / 4), 22)],
      alternatingSixCyclotomicValue [((2 / 11), 0), ((-1 / 11), 2), ((-3 / 22), 6), ((-1 / 22), 8), ((-1 / 11), 12), ((2 / 11), 18), ((1 / 11), 22), ((3 / 44), 24), ((1 / 22), 28), ((-5 / 44), 30)],
      alternatingSixCyclotomicValue [((-5 / 11), 0), ((27 / 44), 2), ((13 / 44), 6), ((27 / 44), 8), ((21 / 44), 12), ((-21 / 44), 18), ((-27 / 44), 22), ((-13 / 44), 24), ((-27 / 44), 28), ((5 / 11), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 6), ((-1 / 2), 8), ((-1 / 4), 12), ((1 / 4), 18), ((1 / 2), 28), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 2), ((1 / 2), 12), ((1 / 4), 18), ((1 / 4), 22), ((-1 / 2), 24), ((-1 / 2), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 0)],
      alternatingSixCyclotomicValue [((1 / 4), 8), ((1 / 4), 12), ((-1 / 4), 24), ((-1 / 4), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 2), ((1 / 2), 6), ((1 / 2), 8), ((1 / 2), 12), ((-1 / 2), 22), ((-1 / 2), 28), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((3 / 4), 0), (-1, 2), ((-5 / 4), 6), ((3 / 4), 8), ((1 / 2), 12), ((-1 / 4), 18), (1, 22), ((1 / 2), 24), ((-3 / 4), 28), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((-17 / 44), 0), ((5 / 11), 8), ((5 / 11), 12), ((-5 / 11), 28)],
      alternatingSixCyclotomicValue [((5 / 22), 0), ((-5 / 44), 8), ((-7 / 44), 12), ((3 / 44), 24), ((5 / 44), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 2), 2), ((-1 / 2), 6), ((1 / 2), 8), ((1 / 2), 12), ((1 / 2), 22), ((-1 / 2), 28), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((3 / 4), 0), (1, 2), ((5 / 4), 6), ((3 / 4), 8), ((1 / 2), 12), ((1 / 4), 18), (-1, 22), ((1 / 2), 24), ((-3 / 4), 28), ((1 / 2), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 24)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 8), ((1 / 4), 12), ((-1 / 2), 24), ((-1 / 4), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 2), ((-1 / 4), 6), ((-1 / 2), 8), ((-1 / 4), 12), ((1 / 4), 18), ((1 / 2), 22), ((1 / 2), 24), ((1 / 2), 28)],
      alternatingSixCyclotomicValue [((1 / 4), 6), ((1 / 4), 24)],
      alternatingSixCyclotomicValue [((7 / 44), 0), ((-1 / 11), 8), ((-1 / 22), 12), ((-3 / 44), 24), ((1 / 11), 28)],
      alternatingSixCyclotomicValue [((-5 / 44), 0), ((13 / 44), 8), ((13 / 44), 12), ((-13 / 44), 28)],
      alternatingSixCyclotomicValue [((1 / 2), 2), ((1 / 4), 6), ((-1 / 2), 8), ((-1 / 4), 12), ((-1 / 4), 18), ((-1 / 2), 22), ((1 / 2), 24), ((1 / 2), 28)],
      alternatingSixCyclotomicValue [((-1 / 4), 6), ((1 / 4), 24)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 2), ((1 / 2), 6), ((1 / 4), 8), ((1 / 4), 12), ((-1 / 4), 18), ((-1 / 4), 22), ((-1 / 4), 28), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 8), ((-1 / 4), 12), ((1 / 4), 24), ((-1 / 4), 28)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-5 / 4), 2), (-2, 6), ((-5 / 4), 8), ((-5 / 4), 12), ((3 / 4), 18), ((5 / 4), 22), ((5 / 4), 28), (-1, 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 2), 2), ((-1 / 4), 6), ((-1 / 4), 8), ((1 / 4), 18), ((-1 / 2), 22), ((-1 / 2), 24), ((1 / 4), 28)],
      alternatingSixCyclotomicValue [((-3 / 11), 0), ((-1 / 44), 2), ((-3 / 22), 6), ((7 / 44), 8), ((7 / 44), 12), ((5 / 44), 18), ((1 / 44), 22), ((-7 / 44), 28), ((-3 / 44), 30)],
      alternatingSixCyclotomicValue [((-1 / 22), 0), ((7 / 22), 6), ((1 / 44), 8), ((-3 / 44), 12), ((-6 / 11), 18), ((-5 / 44), 24), ((-1 / 44), 28), ((7 / 22), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 2), ((-1 / 4), 8), ((-1 / 4), 12), ((-1 / 4), 18), ((1 / 4), 22), ((1 / 4), 28)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 2), 2), ((3 / 4), 6), ((1 / 4), 8), ((1 / 2), 12), ((-1 / 4), 18), ((-1 / 2), 22), ((-1 / 4), 28), ((1 / 2), 30)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 24), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 4), 2), ((-1 / 4), 6), ((-1 / 4), 8), ((-1 / 4), 12), ((1 / 4), 18), ((1 / 4), 22), ((1 / 4), 24), ((1 / 4), 28), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 6), ((-1 / 2), 8), ((-1 / 4), 12), ((-1 / 4), 18), ((1 / 2), 28), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 2), ((1 / 2), 12), ((-1 / 4), 18), ((-1 / 4), 22), ((-1 / 2), 24), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((2 / 11), 0), ((1 / 11), 2), ((3 / 22), 6), ((-1 / 22), 8), ((-1 / 11), 12), ((-2 / 11), 18), ((-1 / 11), 22), ((3 / 44), 24), ((1 / 22), 28), ((5 / 44), 30)],
      alternatingSixCyclotomicValue [((-5 / 11), 0), ((-27 / 44), 2), ((-13 / 44), 6), ((27 / 44), 8), ((21 / 44), 12), ((21 / 44), 18), ((27 / 44), 22), ((-13 / 44), 24), ((-27 / 44), 28), ((-5 / 11), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 6), ((1 / 4), 12), ((1 / 4), 18), ((1 / 2), 24), ((-3 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 2), ((1 / 4), 18), ((-1 / 4), 22)]]
  ]

macro "close_cyclotomic_row16" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)


private theorem row16_eigenbasisInverse_mul_0_0 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        0 0 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        0 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((5 / 2) : ℂ) + ((5 / 2) : ℂ) * ζ ^ 4 - ((7 / 10) : ℂ) * ζ ^ 8 + ((1 / 5) : ℂ) * ζ ^ 12 - ((3 / 5) : ℂ) * ζ ^ 16 - ((19 / 20) : ℂ) * ζ ^ 20 - ((2 / 5) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_0_1 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        0 1 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        0 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((17 / 20) : ℂ) + ((17 / 20) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 - ((13 / 20) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 16 - ((27 / 20) : ℂ) * ζ ^ 20 - ((3 / 20) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_0_2 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        0 2 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        0 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((17 / 10) : ℂ) + ((19 / 20) : ℂ) * ζ ^ 2 - ((17 / 10) : ℂ) * ζ ^ 4 - ((11 / 10) : ℂ) * ζ ^ 6 - ((1 / 4) : ℂ) * ζ ^ 8 + ((11 / 20) : ℂ) * ζ ^ 10 + ((3 / 5) : ℂ) * ζ ^ 12 - ((17 / 5) : ℂ) * ζ ^ 14 + ((21 / 20) : ℂ) * ζ ^ 16 + ((3 / 10) : ℂ) * ζ ^ 18 - ((15 / 4) : ℂ) * ζ ^ 20 - ((17 / 20) : ℂ) * ζ ^ 22 + ((33 / 20) : ℂ) * ζ ^ 24 + ((2 / 5) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_0_3 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        0 3 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        0 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((11 / 20) : ℂ) - ((17 / 20) : ℂ) * ζ ^ 2 + ((11 / 20) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 6 + ((33 / 20) : ℂ) * ζ ^ 8 + ((3 / 5) : ℂ) * ζ ^ 10 - ((33 / 20) : ℂ) * ζ ^ 12 + ((13 / 10) : ℂ) * ζ ^ 14 + ((13 / 10) : ℂ) * ζ ^ 16 + ((5 / 4) : ℂ) * ζ ^ 18 - ((5 / 2) : ℂ) * ζ ^ 20 - ((9 / 10) : ℂ) * ζ ^ 22 - ((7 / 20) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_0_4 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        0 4 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        0 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((83 / 110) : ℂ) + ((83 / 110) : ℂ) * ζ ^ 4 + ((6 / 55) : ℂ) * ζ ^ 8 + ((29 / 55) : ℂ) * ζ ^ 12 - ((83 / 110) : ℂ) * ζ ^ 16 + ((17 / 20) : ℂ) * ζ ^ 20 - ((5 / 22) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_0_5 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        0 5 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        0 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((183 / 220) : ℂ) + ((183 / 220) : ℂ) * ζ ^ 4 + ((35 / 44) : ℂ) * ζ ^ 8 - ((7 / 220) : ℂ) * ζ ^ 12 - ((83 / 110) : ℂ) * ζ ^ 16 - ((27 / 44) : ℂ) * ζ ^ 20 - ((173 / 220) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_0_6 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        0 6 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        0 6 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((17 / 10) : ℂ) - ((19 / 20) : ℂ) * ζ ^ 2 - ((17 / 10) : ℂ) * ζ ^ 4 + ((11 / 10) : ℂ) * ζ ^ 6 - ((1 / 4) : ℂ) * ζ ^ 8 - ((11 / 20) : ℂ) * ζ ^ 10 + ((3 / 5) : ℂ) * ζ ^ 12 + ((17 / 5) : ℂ) * ζ ^ 14 + ((21 / 20) : ℂ) * ζ ^ 16 - ((3 / 10) : ℂ) * ζ ^ 18 - ((15 / 4) : ℂ) * ζ ^ 20 + ((17 / 20) : ℂ) * ζ ^ 22 + ((33 / 20) : ℂ) * ζ ^ 24 - ((2 / 5) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_0_7 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        0 7 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        0 7 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((11 / 20) : ℂ) + ((17 / 20) : ℂ) * ζ ^ 2 + ((11 / 20) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 + ((33 / 20) : ℂ) * ζ ^ 8 - ((3 / 5) : ℂ) * ζ ^ 10 - ((33 / 20) : ℂ) * ζ ^ 12 - ((13 / 10) : ℂ) * ζ ^ 14 + ((13 / 10) : ℂ) * ζ ^ 16 - ((5 / 4) : ℂ) * ζ ^ 18 - ((5 / 2) : ℂ) * ζ ^ 20 + ((9 / 10) : ℂ) * ζ ^ 22 - ((7 / 20) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_1_0 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        1 0 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        1 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((3 / 10) : ℂ) - ((3 / 10) : ℂ) * ζ ^ 4 - ((2 / 5) : ℂ) * ζ ^ 8 - ((23 / 20) : ℂ) * ζ ^ 12 + ((21 / 20) : ℂ) * ζ ^ 16 - ((37 / 20) : ℂ) * ζ ^ 20 - ((1 / 10) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_1_1 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        1 1 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        1 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((11 / 20) : ℂ) - ((11 / 20) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 - ((3 / 10) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 16 + ((1 / 20) : ℂ) * ζ ^ 20 - ((11 / 20) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_1_2 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        1 2 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        1 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((7 / 20) : ℂ) + ((51 / 20) : ℂ) * ζ ^ 2 + ((7 / 20) : ℂ) * ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 6 + ((19 / 5) : ℂ) * ζ ^ 8 - ((13 / 10) : ℂ) * ζ ^ 10 - ((39 / 20) : ℂ) * ζ ^ 12 + ((37 / 20) : ℂ) * ζ ^ 14 - ((9 / 10) : ℂ) * ζ ^ 16 - ((51 / 20) : ℂ) * ζ ^ 18 + ((33 / 20) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 22 - ((57 / 20) : ℂ) * ζ ^ 24 + ((19 / 20) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_1_3 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        1 3 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        1 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((11 / 5) : ℂ) - ((21 / 20) : ℂ) * ζ ^ 2 - ((11 / 5) : ℂ) * ζ ^ 4 + ((9 / 20) : ℂ) * ζ ^ 6 + ((7 / 10) : ℂ) * ζ ^ 8 + ((11 / 20) : ℂ) * ζ ^ 10 + ((1 / 10) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 14 - ((3 / 10) : ℂ) * ζ ^ 16 - ((3 / 10) : ℂ) * ζ ^ 18 + ((7 / 10) : ℂ) * ζ ^ 20 + ((13 / 10) : ℂ) * ζ ^ 22 - ((1 / 5) : ℂ) * ζ ^ 24 - ((4 / 5) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_1_4 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        1 4 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        1 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((6 / 55) : ℂ) + ((6 / 55) : ℂ) * ζ ^ 4 - ((26 / 55) : ℂ) * ζ ^ 8 - ((25 / 44) : ℂ) * ζ ^ 12 + ((193 / 220) : ℂ) * ζ ^ 16 - ((159 / 220) : ℂ) * ζ ^ 20 + ((17 / 55) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_1_5 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        1 5 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        1 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((149 / 220) : ℂ) + ((149 / 220) : ℂ) * ζ ^ 4 + ((317 / 220) : ℂ) * ζ ^ 8 - ((129 / 110) : ℂ) * ζ ^ 12 + ((59 / 220) : ℂ) * ζ ^ 16 - ((19 / 44) : ℂ) * ζ ^ 20 - ((199 / 220) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_1_6 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        1 6 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        1 6 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((7 / 20) : ℂ) - ((51 / 20) : ℂ) * ζ ^ 2 + ((7 / 20) : ℂ) * ζ ^ 4 + ((3 / 4) : ℂ) * ζ ^ 6 + ((19 / 5) : ℂ) * ζ ^ 8 + ((13 / 10) : ℂ) * ζ ^ 10 - ((39 / 20) : ℂ) * ζ ^ 12 - ((37 / 20) : ℂ) * ζ ^ 14 - ((9 / 10) : ℂ) * ζ ^ 16 + ((51 / 20) : ℂ) * ζ ^ 18 + ((33 / 20) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((57 / 20) : ℂ) * ζ ^ 24 - ((19 / 20) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_1_7 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        1 7 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        1 7 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((11 / 5) : ℂ) + ((21 / 20) : ℂ) * ζ ^ 2 - ((11 / 5) : ℂ) * ζ ^ 4 - ((9 / 20) : ℂ) * ζ ^ 6 + ((7 / 10) : ℂ) * ζ ^ 8 - ((11 / 20) : ℂ) * ζ ^ 10 + ((1 / 10) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 14 - ((3 / 10) : ℂ) * ζ ^ 16 + ((3 / 10) : ℂ) * ζ ^ 18 + ((7 / 10) : ℂ) * ζ ^ 20 - ((13 / 10) : ℂ) * ζ ^ 22 - ((1 / 5) : ℂ) * ζ ^ 24 + ((4 / 5) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_2_0 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        2 0 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        2 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((5 / 4) : ℂ) - ((7 / 20) : ℂ) * ζ ^ 2 - ((5 / 4) : ℂ) * ζ ^ 4 + ((1 / 5) : ℂ) * ζ ^ 6 + ((3 / 10) : ℂ) * ζ ^ 8 - ((13 / 20) : ℂ) * ζ ^ 10 - ((1 / 20) : ℂ) * ζ ^ 12 + ((3 / 10) : ℂ) * ζ ^ 14 + ((2 / 5) : ℂ) * ζ ^ 16 - ((1 / 5) : ℂ) * ζ ^ 18 + ((3 / 10) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 22 + ((7 / 20) : ℂ) * ζ ^ 24 + ((3 / 20) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_2_1 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        2 1 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        2 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((2 / 5) : ℂ) - ((2 / 5) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 + ((3 / 5) : ℂ) * ζ ^ 12 - ((3 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 16 + ((1 / 4) : ℂ) * ζ ^ 18 + ((13 / 20) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 22 + ((7 / 20) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_2_2 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        2 2 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        2 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((21 / 20) : ℂ) - ((4 / 5) : ℂ) * ζ ^ 2 + ((3 / 2) : ℂ) * ζ ^ 4 + ((2 / 5) : ℂ) * ζ ^ 6 - ((57 / 20) : ℂ) * ζ ^ 8 + ((1 / 5) : ℂ) * ζ ^ 10 + ((23 / 20) : ℂ) * ζ ^ 12 - ((3 / 4) : ℂ) * ζ ^ 14 - ((21 / 20) : ℂ) * ζ ^ 16 + ((17 / 10) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 20 - ((11 / 10) : ℂ) * ζ ^ 22 + ((7 / 20) : ℂ) * ζ ^ 24 + ((7 / 20) : ℂ) * ζ ^ 26 - ((7 / 10) : ℂ) * ζ ^ 28)
private theorem row16_eigenbasisInverse_mul_2_3 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        2 3 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        2 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((1 / 5) : ℂ) + ((21 / 20) : ℂ) * ζ ^ 2 - ((31 / 20) : ℂ) * ζ ^ 6 - ((9 / 20) : ℂ) * ζ ^ 8 + ((13 / 20) : ℂ) * ζ ^ 10 + ((9 / 10) : ℂ) * ζ ^ 12 - ((3 / 4) : ℂ) * ζ ^ 14 - ((3 / 10) : ℂ) * ζ ^ 16 - ((3 / 20) : ℂ) * ζ ^ 18 + ((4 / 5) : ℂ) * ζ ^ 20 - ((3 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 26 + ((3 / 20) : ℂ) * ζ ^ 28)
private theorem row16_eigenbasisInverse_mul_2_4 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        2 4 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        2 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((159 / 220) : ℂ) - ((151 / 220) : ℂ) * ζ ^ 2 - ((159 / 220) : ℂ) * ζ ^ 4 + ((71 / 110) : ℂ) * ζ ^ 6 + ((47 / 110) : ℂ) * ζ ^ 8 - ((23 / 44) : ℂ) * ζ ^ 10 - ((49 / 220) : ℂ) * ζ ^ 12 + ((18 / 55) : ℂ) * ζ ^ 14 + ((37 / 110) : ℂ) * ζ ^ 16 - ((2 / 5) : ℂ) * ζ ^ 18 - ((9 / 110) : ℂ) * ζ ^ 20 + ((23 / 44) : ℂ) * ζ ^ 22 + ((5 / 44) : ℂ) * ζ ^ 24 - ((49 / 220) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_2_5 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        2 5 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        2 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((38 / 55) : ℂ) - ((1 / 55) : ℂ) * ζ ^ 2 - ((38 / 55) : ℂ) * ζ ^ 4 + ((93 / 220) : ℂ) * ζ ^ 6 - ((3 / 11) : ℂ) * ζ ^ 8 - ((23 / 44) : ℂ) * ζ ^ 10 - ((3 / 55) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 14 + ((9 / 20) : ℂ) * ζ ^ 16 + ((39 / 220) : ℂ) * ζ ^ 18 + ((3 / 44) : ℂ) * ζ ^ 20 - ((61 / 220) : ℂ) * ζ ^ 22 + ((87 / 220) : ℂ) * ζ ^ 24 + ((1 / 55) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_2_6 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        2 6 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        2 6 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((1 / 20) : ℂ) + ((4 / 5) : ℂ) * ζ ^ 2 - ((2 / 5) : ℂ) * ζ ^ 4 - ((9 / 10) : ℂ) * ζ ^ 6 + ((37 / 20) : ℂ) * ζ ^ 8 + ((11 / 10) : ℂ) * ζ ^ 10 - ((19 / 20) : ℂ) * ζ ^ 12 - ((79 / 20) : ℂ) * ζ ^ 14 + ((3 / 20) : ℂ) * ζ ^ 16 + ((21 / 10) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 20 - ((19 / 10) : ℂ) * ζ ^ 22 - ((21 / 20) : ℂ) * ζ ^ 24 + ((21 / 20) : ℂ) * ζ ^ 26 + ((7 / 10) : ℂ) * ζ ^ 28)
private theorem row16_eigenbasisInverse_mul_2_7 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        2 7 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        2 7 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((1 / 5) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 - ((2 / 5) : ℂ) * ζ ^ 4 - ((31 / 20) : ℂ) * ζ ^ 6 - ((5 / 4) : ℂ) * ζ ^ 8 + ((39 / 20) : ℂ) * ζ ^ 10 + ((13 / 10) : ℂ) * ζ ^ 12 - ((17 / 20) : ℂ) * ζ ^ 14 - ((11 / 10) : ℂ) * ζ ^ 16 + ((37 / 20) : ℂ) * ζ ^ 18 + ((7 / 10) : ℂ) * ζ ^ 20 - ((29 / 20) : ℂ) * ζ ^ 22 + ((11 / 20) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 26 - ((3 / 20) : ℂ) * ζ ^ 28)
private theorem row16_eigenbasisInverse_mul_3_0 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        3 0 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        3 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((17 / 20) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 + ((17 / 20) : ℂ) * ζ ^ 4 - ((3 / 10) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 5) : ℂ) * ζ ^ 10 + ((11 / 10) : ℂ) * ζ ^ 12 - ((17 / 20) : ℂ) * ζ ^ 14 - ((3 / 2) : ℂ) * ζ ^ 16 + ((9 / 10) : ℂ) * ζ ^ 20 - ((1 / 10) : ℂ) * ζ ^ 22 - ((2 / 5) : ℂ) * ζ ^ 24 + ((1 / 20) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_3_1 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        3 1 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        3 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((3 / 4) : ℂ) - ((1 / 5) : ℂ) * ζ ^ 2 + ((3 / 4) : ℂ) * ζ ^ 4 + ((3 / 20) : ℂ) * ζ ^ 6 - ζ ^ 8 - ((1 / 20) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 - ((3 / 20) : ℂ) * ζ ^ 14 + ((1 / 10) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 5) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_3_2 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        3 2 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        3 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((3 / 4) : ℂ) - ((33 / 20) : ℂ) * ζ ^ 2 - ((27 / 20) : ℂ) * ζ ^ 4 + ((21 / 20) : ℂ) * ζ ^ 6 - ((31 / 10) : ℂ) * ζ ^ 8 - ((7 / 20) : ℂ) * ζ ^ 10 + ((7 / 4) : ℂ) * ζ ^ 12 - ((29 / 20) : ℂ) * ζ ^ 14 - ((11 / 20) : ℂ) * ζ ^ 16 + ((31 / 20) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 - ((17 / 20) : ℂ) * ζ ^ 22 + ((21 / 10) : ℂ) * ζ ^ 24 + ((2 / 5) : ℂ) * ζ ^ 26 - ((3 / 10) : ℂ) * ζ ^ 28)
private theorem row16_eigenbasisInverse_mul_3_3 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        3 3 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        3 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((18 / 5) : ℂ) + ((27 / 20) : ℂ) * ζ ^ 2 + ((73 / 20) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 6 - ((5 / 4) : ℂ) * ζ ^ 8 - ((1 / 5) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 20) : ℂ) * ζ ^ 16 + ((21 / 20) : ℂ) * ζ ^ 18 - ((3 / 10) : ℂ) * ζ ^ 20 - ((7 / 4) : ℂ) * ζ ^ 22 + ((21 / 20) : ℂ) * ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row16_eigenbasisInverse_mul_3_4 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        3 4 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        3 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((9 / 220) : ℂ) - ((17 / 220) : ℂ) * ζ ^ 2 - ((9 / 220) : ℂ) * ζ ^ 4 - ((17 / 110) : ℂ) * ζ ^ 6 - ((3 / 110) : ℂ) * ζ ^ 8 + ((24 / 55) : ℂ) * ζ ^ 10 + ((31 / 55) : ℂ) * ζ ^ 12 - ((49 / 220) : ℂ) * ζ ^ 14 - ((6 / 11) : ℂ) * ζ ^ 16 + ((17 / 55) : ℂ) * ζ ^ 18 + ((53 / 110) : ℂ) * ζ ^ 20 - ((3 / 110) : ℂ) * ζ ^ 22 + ((1 / 55) : ℂ) * ζ ^ 24 - ((5 / 44) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_3_5 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        3 5 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        3 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((81 / 220) : ℂ) + ((56 / 55) : ℂ) * ζ ^ 2 - ((81 / 220) : ℂ) * ζ ^ 4 - ((3 / 44) : ℂ) * ζ ^ 6 + ((9 / 55) : ℂ) * ζ ^ 8 - ((17 / 44) : ℂ) * ζ ^ 10 + ((32 / 55) : ℂ) * ζ ^ 12 - ((19 / 44) : ℂ) * ζ ^ 14 - ((28 / 55) : ℂ) * ζ ^ 16 - ((2 / 5) : ℂ) * ζ ^ 18 - ((1 / 11) : ℂ) * ζ ^ 20 - ((3 / 55) : ℂ) * ζ ^ 22 + ((4 / 55) : ℂ) * ζ ^ 24 + ((3 / 110) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_3_6 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        3 6 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        3 6 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((3 / 4) : ℂ) + ((49 / 20) : ℂ) * ζ ^ 2 - ((3 / 20) : ℂ) * ζ ^ 4 - ((13 / 20) : ℂ) * ζ ^ 6 - ((21 / 10) : ℂ) * ζ ^ 8 - ((29 / 20) : ℂ) * ζ ^ 10 + ((47 / 20) : ℂ) * ζ ^ 12 + ((33 / 20) : ℂ) * ζ ^ 14 + ((1 / 20) : ℂ) * ζ ^ 16 - ((51 / 20) : ℂ) * ζ ^ 18 - ((27 / 20) : ℂ) * ζ ^ 20 + ((9 / 20) : ℂ) * ζ ^ 22 + ((3 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 26 + ((3 / 10) : ℂ) * ζ ^ 28)
private theorem row16_eigenbasisInverse_mul_3_7 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        3 7 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        3 7 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((13 / 5) : ℂ) - ((11 / 20) : ℂ) * ζ ^ 2 + ((51 / 20) : ℂ) * ζ ^ 4 + ((4 / 5) : ℂ) * ζ ^ 6 - ((7 / 20) : ℂ) * ζ ^ 8 + ((1 / 5) : ℂ) * ζ ^ 10 + ((23 / 20) : ℂ) * ζ ^ 12 - ((13 / 20) : ℂ) * ζ ^ 14 - ((29 / 20) : ℂ) * ζ ^ 16 - ((3 / 20) : ℂ) * ζ ^ 18 + ((23 / 20) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 - ((23 / 20) : ℂ) * ζ ^ 26 + ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row16_eigenbasisInverse_mul_4_0 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        4 0 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        4 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((1 / 10) : ℂ) * ζ ^ 8 - ((1 / 10) : ℂ) * ζ ^ 12 - ((1 / 5) : ℂ) * ζ ^ 16 + ((7 / 20) : ℂ) * ζ ^ 20 - ((3 / 10) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_4_1 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        4 1 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        4 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((1 / 20) : ℂ) - ((1 / 20) : ℂ) * ζ ^ 4 + ((3 / 4) : ℂ) * ζ ^ 8 - ((11 / 20) : ℂ) * ζ ^ 12 + ((1 / 20) : ℂ) * ζ ^ 20 - ((11 / 20) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_4_2 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        4 2 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        4 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((3 / 5) : ℂ) + ((13 / 20) : ℂ) * ζ ^ 2 + ((3 / 5) : ℂ) * ζ ^ 4 - ((1 / 5) : ℂ) * ζ ^ 6 + ((5 / 4) : ℂ) * ζ ^ 8 + ((7 / 20) : ℂ) * ζ ^ 10 - ((4 / 5) : ℂ) * ζ ^ 12 + ((1 / 5) : ℂ) * ζ ^ 14 - ((3 / 20) : ℂ) * ζ ^ 16 + ((1 / 10) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 20 + ((1 / 20) : ℂ) * ζ ^ 22 - ((19 / 20) : ℂ) * ζ ^ 24 + ((3 / 10) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_4_3 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        4 3 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        4 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((3 / 20) : ℂ) - ((9 / 20) : ℂ) * ζ ^ 2 - ((3 / 20) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 20) : ℂ) * ζ ^ 8 + ((7 / 10) : ℂ) * ζ ^ 10 - ((11 / 20) : ℂ) * ζ ^ 12 - ((7 / 5) : ℂ) * ζ ^ 14 + ((1 / 10) : ℂ) * ζ ^ 16 + ((3 / 4) : ℂ) * ζ ^ 18 + ζ ^ 20 + ((1 / 5) : ℂ) * ζ ^ 22 - ((9 / 20) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_4_4 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        4 4 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        4 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((38 / 55) : ℂ) + ((38 / 55) : ℂ) * ζ ^ 4 - ((53 / 55) : ℂ) * ζ ^ 8 - ((9 / 110) : ℂ) * ζ ^ 12 + ((9 / 110) : ℂ) * ζ ^ 16 - ((151 / 220) : ℂ) * ζ ^ 20)
private theorem row16_eigenbasisInverse_mul_4_5 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        4 5 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        4 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((11 / 20) : ℂ) + ((11 / 20) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 + ((31 / 220) : ℂ) * ζ ^ 12 - ((8 / 55) : ℂ) * ζ ^ 16 + ((21 / 44) : ℂ) * ζ ^ 20 - ((1 / 220) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_4_6 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        4 6 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        4 6 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((3 / 5) : ℂ) - ((13 / 20) : ℂ) * ζ ^ 2 + ((3 / 5) : ℂ) * ζ ^ 4 + ((1 / 5) : ℂ) * ζ ^ 6 + ((5 / 4) : ℂ) * ζ ^ 8 - ((7 / 20) : ℂ) * ζ ^ 10 - ((4 / 5) : ℂ) * ζ ^ 12 - ((1 / 5) : ℂ) * ζ ^ 14 - ((3 / 20) : ℂ) * ζ ^ 16 - ((1 / 10) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 20 - ((1 / 20) : ℂ) * ζ ^ 22 - ((19 / 20) : ℂ) * ζ ^ 24 - ((3 / 10) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_4_7 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        4 7 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        4 7 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((3 / 20) : ℂ) + ((9 / 20) : ℂ) * ζ ^ 2 - ((3 / 20) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 20) : ℂ) * ζ ^ 8 - ((7 / 10) : ℂ) * ζ ^ 10 - ((11 / 20) : ℂ) * ζ ^ 12 + ((7 / 5) : ℂ) * ζ ^ 14 + ((1 / 10) : ℂ) * ζ ^ 16 - ((3 / 4) : ℂ) * ζ ^ 18 + ζ ^ 20 - ((1 / 5) : ℂ) * ζ ^ 22 - ((9 / 20) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_5_0 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        5 0 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        5 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((7 / 5) : ℂ) - ((7 / 5) : ℂ) * ζ ^ 4 + ((7 / 5) : ℂ) * ζ ^ 8 - ((21 / 20) : ℂ) * ζ ^ 12 + ((39 / 20) : ℂ) * ζ ^ 16 + ((1 / 20) : ℂ) * ζ ^ 20 + ((9 / 10) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_5_1 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        5 1 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        5 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((19 / 20) : ℂ) - ((19 / 20) : ℂ) * ζ ^ 4 + ((7 / 4) : ℂ) * ζ ^ 8 - ((7 / 10) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 16 + ((19 / 20) : ℂ) * ζ ^ 20 - ((9 / 20) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_5_2 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        5 2 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        5 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((23 / 20) : ℂ) + ((31 / 20) : ℂ) * ζ ^ 2 + ((23 / 20) : ℂ) * ζ ^ 4 - ((19 / 20) : ℂ) * ζ ^ 6 + ((7 / 5) : ℂ) * ζ ^ 8 + ((1 / 5) : ℂ) * ζ ^ 10 - ((43 / 20) : ℂ) * ζ ^ 12 + ((5 / 4) : ℂ) * ζ ^ 14 + ((7 / 5) : ℂ) * ζ ^ 16 - ((31 / 20) : ℂ) * ζ ^ 18 - ((1 / 20) : ℂ) * ζ ^ 20 + ((4 / 5) : ℂ) * ζ ^ 22 - ((3 / 4) : ℂ) * ζ ^ 24 - ((37 / 20) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_5_3 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        5 3 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        5 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 ((4 : ℂ) - ((17 / 20) : ℂ) * ζ ^ 2 - (4 : ℂ) * ζ ^ 4 + ((17 / 20) : ℂ) * ζ ^ 6 + ((9 / 10) : ℂ) * ζ ^ 8 - ((3 / 20) : ℂ) * ζ ^ 10 - ζ ^ 12 + ((3 / 5) : ℂ) * ζ ^ 14 + ((17 / 10) : ℂ) * ζ ^ 16 - ((9 / 10) : ℂ) * ζ ^ 18 - ((2 / 5) : ℂ) * ζ ^ 20 + ((8 / 5) : ℂ) * ζ ^ 22 + ((7 / 10) : ℂ) * ζ ^ 24 - ((7 / 5) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_5_4 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        5 4 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        5 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((3 / 110) : ℂ) - ((3 / 110) : ℂ) * ζ ^ 4 + ((29 / 55) : ℂ) * ζ ^ 8 - ((123 / 220) : ℂ) * ζ ^ 12 + ((47 / 220) : ℂ) * ζ ^ 16 - ((53 / 220) : ℂ) * ζ ^ 20 - ((19 / 55) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_5_5 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        5 5 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        5 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((13 / 220) : ℂ) + ((13 / 220) : ℂ) * ζ ^ 4 - ((389 / 220) : ℂ) * ζ ^ 8 + ((1 / 110) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 16 + ((27 / 44) : ℂ) * ζ ^ 20 + ((167 / 220) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_5_6 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        5 6 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        5 6 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((23 / 20) : ℂ) - ((31 / 20) : ℂ) * ζ ^ 2 + ((23 / 20) : ℂ) * ζ ^ 4 + ((19 / 20) : ℂ) * ζ ^ 6 + ((7 / 5) : ℂ) * ζ ^ 8 - ((1 / 5) : ℂ) * ζ ^ 10 - ((43 / 20) : ℂ) * ζ ^ 12 - ((5 / 4) : ℂ) * ζ ^ 14 + ((7 / 5) : ℂ) * ζ ^ 16 + ((31 / 20) : ℂ) * ζ ^ 18 - ((1 / 20) : ℂ) * ζ ^ 20 - ((4 / 5) : ℂ) * ζ ^ 22 - ((3 / 4) : ℂ) * ζ ^ 24 + ((37 / 20) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_5_7 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        5 7 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        5 7 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 ((4 : ℂ) + ((17 / 20) : ℂ) * ζ ^ 2 - (4 : ℂ) * ζ ^ 4 - ((17 / 20) : ℂ) * ζ ^ 6 + ((9 / 10) : ℂ) * ζ ^ 8 + ((3 / 20) : ℂ) * ζ ^ 10 - ζ ^ 12 - ((3 / 5) : ℂ) * ζ ^ 14 + ((17 / 10) : ℂ) * ζ ^ 16 + ((9 / 10) : ℂ) * ζ ^ 18 - ((2 / 5) : ℂ) * ζ ^ 20 - ((8 / 5) : ℂ) * ζ ^ 22 + ((7 / 10) : ℂ) * ζ ^ 24 + ((7 / 5) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_6_0 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        6 0 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        6 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((5 / 4) : ℂ) + ((7 / 20) : ℂ) * ζ ^ 2 - ((5 / 4) : ℂ) * ζ ^ 4 - ((1 / 5) : ℂ) * ζ ^ 6 + ((3 / 10) : ℂ) * ζ ^ 8 + ((13 / 20) : ℂ) * ζ ^ 10 - ((1 / 20) : ℂ) * ζ ^ 12 - ((3 / 10) : ℂ) * ζ ^ 14 + ((2 / 5) : ℂ) * ζ ^ 16 + ((1 / 5) : ℂ) * ζ ^ 18 + ((3 / 10) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 22 + ((7 / 20) : ℂ) * ζ ^ 24 - ((3 / 20) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_6_1 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        6 1 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        6 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((2 / 5) : ℂ) - ((2 / 5) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 10 + ((3 / 5) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 16 - ((1 / 4) : ℂ) * ζ ^ 18 + ((13 / 20) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 22 + ((7 / 20) : ℂ) * ζ ^ 24)
private theorem row16_eigenbasisInverse_mul_6_2 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        6 2 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        6 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((1 / 20) : ℂ) - ((4 / 5) : ℂ) * ζ ^ 2 - ((2 / 5) : ℂ) * ζ ^ 4 + ((9 / 10) : ℂ) * ζ ^ 6 + ((37 / 20) : ℂ) * ζ ^ 8 - ((11 / 10) : ℂ) * ζ ^ 10 - ((19 / 20) : ℂ) * ζ ^ 12 + ((79 / 20) : ℂ) * ζ ^ 14 + ((3 / 20) : ℂ) * ζ ^ 16 - ((21 / 10) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 20 + ((19 / 10) : ℂ) * ζ ^ 22 - ((21 / 20) : ℂ) * ζ ^ 24 - ((21 / 20) : ℂ) * ζ ^ 26 + ((7 / 10) : ℂ) * ζ ^ 28)
private theorem row16_eigenbasisInverse_mul_6_3 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        6 3 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        6 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((1 / 5) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 2 - ((2 / 5) : ℂ) * ζ ^ 4 + ((31 / 20) : ℂ) * ζ ^ 6 - ((5 / 4) : ℂ) * ζ ^ 8 - ((39 / 20) : ℂ) * ζ ^ 10 + ((13 / 10) : ℂ) * ζ ^ 12 + ((17 / 20) : ℂ) * ζ ^ 14 - ((11 / 10) : ℂ) * ζ ^ 16 - ((37 / 20) : ℂ) * ζ ^ 18 + ((7 / 10) : ℂ) * ζ ^ 20 + ((29 / 20) : ℂ) * ζ ^ 22 + ((11 / 20) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 26 - ((3 / 20) : ℂ) * ζ ^ 28)
private theorem row16_eigenbasisInverse_mul_6_4 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        6 4 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        6 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((159 / 220) : ℂ) + ((151 / 220) : ℂ) * ζ ^ 2 - ((159 / 220) : ℂ) * ζ ^ 4 - ((71 / 110) : ℂ) * ζ ^ 6 + ((47 / 110) : ℂ) * ζ ^ 8 + ((23 / 44) : ℂ) * ζ ^ 10 - ((49 / 220) : ℂ) * ζ ^ 12 - ((18 / 55) : ℂ) * ζ ^ 14 + ((37 / 110) : ℂ) * ζ ^ 16 + ((2 / 5) : ℂ) * ζ ^ 18 - ((9 / 110) : ℂ) * ζ ^ 20 - ((23 / 44) : ℂ) * ζ ^ 22 + ((5 / 44) : ℂ) * ζ ^ 24 + ((49 / 220) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_6_5 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        6 5 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        6 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((38 / 55) : ℂ) + ((1 / 55) : ℂ) * ζ ^ 2 - ((38 / 55) : ℂ) * ζ ^ 4 - ((93 / 220) : ℂ) * ζ ^ 6 - ((3 / 11) : ℂ) * ζ ^ 8 + ((23 / 44) : ℂ) * ζ ^ 10 - ((3 / 55) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 14 + ((9 / 20) : ℂ) * ζ ^ 16 - ((39 / 220) : ℂ) * ζ ^ 18 + ((3 / 44) : ℂ) * ζ ^ 20 + ((61 / 220) : ℂ) * ζ ^ 22 + ((87 / 220) : ℂ) * ζ ^ 24 - ((1 / 55) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_6_6 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        6 6 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        6 6 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((21 / 20) : ℂ) + ((4 / 5) : ℂ) * ζ ^ 2 + ((3 / 2) : ℂ) * ζ ^ 4 - ((2 / 5) : ℂ) * ζ ^ 6 - ((57 / 20) : ℂ) * ζ ^ 8 - ((1 / 5) : ℂ) * ζ ^ 10 + ((23 / 20) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 14 - ((21 / 20) : ℂ) * ζ ^ 16 - ((17 / 10) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 20 + ((11 / 10) : ℂ) * ζ ^ 22 + ((7 / 20) : ℂ) * ζ ^ 24 - ((7 / 20) : ℂ) * ζ ^ 26 - ((7 / 10) : ℂ) * ζ ^ 28)
private theorem row16_eigenbasisInverse_mul_6_7 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        6 7 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        6 7 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((1 / 5) : ℂ) - ((21 / 20) : ℂ) * ζ ^ 2 + ((31 / 20) : ℂ) * ζ ^ 6 - ((9 / 20) : ℂ) * ζ ^ 8 - ((13 / 20) : ℂ) * ζ ^ 10 + ((9 / 10) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 14 - ((3 / 10) : ℂ) * ζ ^ 16 + ((3 / 20) : ℂ) * ζ ^ 18 + ((4 / 5) : ℂ) * ζ ^ 20 + ((3 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 26 + ((3 / 20) : ℂ) * ζ ^ 28)
private theorem row16_eigenbasisInverse_mul_7_0 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        7 0 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        7 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((17 / 20) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 2 + ((17 / 20) : ℂ) * ζ ^ 4 + ((3 / 10) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 5) : ℂ) * ζ ^ 10 + ((11 / 10) : ℂ) * ζ ^ 12 + ((17 / 20) : ℂ) * ζ ^ 14 - ((3 / 2) : ℂ) * ζ ^ 16 + ((9 / 10) : ℂ) * ζ ^ 20 + ((1 / 10) : ℂ) * ζ ^ 22 - ((2 / 5) : ℂ) * ζ ^ 24 - ((1 / 20) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_7_1 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        7 1 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        7 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((3 / 4) : ℂ) + ((1 / 5) : ℂ) * ζ ^ 2 + ((3 / 4) : ℂ) * ζ ^ 4 - ((3 / 20) : ℂ) * ζ ^ 6 - ζ ^ 8 + ((1 / 20) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 + ((3 / 20) : ℂ) * ζ ^ 14 - ((1 / 10) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 5) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_7_2 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        7 2 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        7 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((3 / 4) : ℂ) - ((49 / 20) : ℂ) * ζ ^ 2 - ((3 / 20) : ℂ) * ζ ^ 4 + ((13 / 20) : ℂ) * ζ ^ 6 - ((21 / 10) : ℂ) * ζ ^ 8 + ((29 / 20) : ℂ) * ζ ^ 10 + ((47 / 20) : ℂ) * ζ ^ 12 - ((33 / 20) : ℂ) * ζ ^ 14 + ((1 / 20) : ℂ) * ζ ^ 16 + ((51 / 20) : ℂ) * ζ ^ 18 - ((27 / 20) : ℂ) * ζ ^ 20 - ((9 / 20) : ℂ) * ζ ^ 22 + ((3 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26 + ((3 / 10) : ℂ) * ζ ^ 28)
private theorem row16_eigenbasisInverse_mul_7_3 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        7 3 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        7 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((13 / 5) : ℂ) + ((11 / 20) : ℂ) * ζ ^ 2 + ((51 / 20) : ℂ) * ζ ^ 4 - ((4 / 5) : ℂ) * ζ ^ 6 - ((7 / 20) : ℂ) * ζ ^ 8 - ((1 / 5) : ℂ) * ζ ^ 10 + ((23 / 20) : ℂ) * ζ ^ 12 + ((13 / 20) : ℂ) * ζ ^ 14 - ((29 / 20) : ℂ) * ζ ^ 16 + ((3 / 20) : ℂ) * ζ ^ 18 - ((23 / 20) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 + ((23 / 20) : ℂ) * ζ ^ 26 + ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row16_eigenbasisInverse_mul_7_4 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        7 4 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        7 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((9 / 220) : ℂ) + ((17 / 220) : ℂ) * ζ ^ 2 - ((9 / 220) : ℂ) * ζ ^ 4 + ((17 / 110) : ℂ) * ζ ^ 6 - ((3 / 110) : ℂ) * ζ ^ 8 - ((24 / 55) : ℂ) * ζ ^ 10 + ((31 / 55) : ℂ) * ζ ^ 12 + ((49 / 220) : ℂ) * ζ ^ 14 - ((6 / 11) : ℂ) * ζ ^ 16 - ((17 / 55) : ℂ) * ζ ^ 18 + ((53 / 110) : ℂ) * ζ ^ 20 + ((3 / 110) : ℂ) * ζ ^ 22 + ((1 / 55) : ℂ) * ζ ^ 24 + ((5 / 44) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_7_5 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        7 5 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        7 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((81 / 220) : ℂ) - ((56 / 55) : ℂ) * ζ ^ 2 - ((81 / 220) : ℂ) * ζ ^ 4 + ((3 / 44) : ℂ) * ζ ^ 6 + ((9 / 55) : ℂ) * ζ ^ 8 + ((17 / 44) : ℂ) * ζ ^ 10 + ((32 / 55) : ℂ) * ζ ^ 12 + ((19 / 44) : ℂ) * ζ ^ 14 - ((28 / 55) : ℂ) * ζ ^ 16 + ((2 / 5) : ℂ) * ζ ^ 18 - ((1 / 11) : ℂ) * ζ ^ 20 + ((3 / 55) : ℂ) * ζ ^ 22 + ((4 / 55) : ℂ) * ζ ^ 24 - ((3 / 110) : ℂ) * ζ ^ 26)
private theorem row16_eigenbasisInverse_mul_7_6 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        7 6 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        7 6 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((3 / 4) : ℂ) + ((33 / 20) : ℂ) * ζ ^ 2 - ((27 / 20) : ℂ) * ζ ^ 4 - ((21 / 20) : ℂ) * ζ ^ 6 - ((31 / 10) : ℂ) * ζ ^ 8 + ((7 / 20) : ℂ) * ζ ^ 10 + ((7 / 4) : ℂ) * ζ ^ 12 + ((29 / 20) : ℂ) * ζ ^ 14 - ((11 / 20) : ℂ) * ζ ^ 16 - ((31 / 20) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 + ((17 / 20) : ℂ) * ζ ^ 22 + ((21 / 10) : ℂ) * ζ ^ 24 - ((2 / 5) : ℂ) * ζ ^ 26 - ((3 / 10) : ℂ) * ζ ^ 28)
private theorem row16_eigenbasisInverse_mul_7_7 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis)
        7 7 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        7 7 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((18 / 5) : ℂ) - ((27 / 20) : ℂ) * ζ ^ 2 + ((73 / 20) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 6 - ((5 / 4) : ℂ) * ζ ^ 8 + ((1 / 5) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 20) : ℂ) * ζ ^ 16 - ((21 / 20) : ℂ) * ζ ^ 18 - ((3 / 10) : ℂ) * ζ ^ 20 + ((7 / 4) : ℂ) * ζ ^ 22 - ((21 / 20) : ℂ) * ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 28)
/-- The displayed row 16 matrix is a left inverse of its
eigenbasis. -/
theorem alternatingSixAmbientRow16EigenbasisInverse_mul :
    alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixAmbientRow16Eigenbasis =
      1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row16_eigenbasisInverse_mul_0_0
  · exact row16_eigenbasisInverse_mul_0_1
  · exact row16_eigenbasisInverse_mul_0_2
  · exact row16_eigenbasisInverse_mul_0_3
  · exact row16_eigenbasisInverse_mul_0_4
  · exact row16_eigenbasisInverse_mul_0_5
  · exact row16_eigenbasisInverse_mul_0_6
  · exact row16_eigenbasisInverse_mul_0_7
  · exact row16_eigenbasisInverse_mul_1_0
  · exact row16_eigenbasisInverse_mul_1_1
  · exact row16_eigenbasisInverse_mul_1_2
  · exact row16_eigenbasisInverse_mul_1_3
  · exact row16_eigenbasisInverse_mul_1_4
  · exact row16_eigenbasisInverse_mul_1_5
  · exact row16_eigenbasisInverse_mul_1_6
  · exact row16_eigenbasisInverse_mul_1_7
  · exact row16_eigenbasisInverse_mul_2_0
  · exact row16_eigenbasisInverse_mul_2_1
  · exact row16_eigenbasisInverse_mul_2_2
  · exact row16_eigenbasisInverse_mul_2_3
  · exact row16_eigenbasisInverse_mul_2_4
  · exact row16_eigenbasisInverse_mul_2_5
  · exact row16_eigenbasisInverse_mul_2_6
  · exact row16_eigenbasisInverse_mul_2_7
  · exact row16_eigenbasisInverse_mul_3_0
  · exact row16_eigenbasisInverse_mul_3_1
  · exact row16_eigenbasisInverse_mul_3_2
  · exact row16_eigenbasisInverse_mul_3_3
  · exact row16_eigenbasisInverse_mul_3_4
  · exact row16_eigenbasisInverse_mul_3_5
  · exact row16_eigenbasisInverse_mul_3_6
  · exact row16_eigenbasisInverse_mul_3_7
  · exact row16_eigenbasisInverse_mul_4_0
  · exact row16_eigenbasisInverse_mul_4_1
  · exact row16_eigenbasisInverse_mul_4_2
  · exact row16_eigenbasisInverse_mul_4_3
  · exact row16_eigenbasisInverse_mul_4_4
  · exact row16_eigenbasisInverse_mul_4_5
  · exact row16_eigenbasisInverse_mul_4_6
  · exact row16_eigenbasisInverse_mul_4_7
  · exact row16_eigenbasisInverse_mul_5_0
  · exact row16_eigenbasisInverse_mul_5_1
  · exact row16_eigenbasisInverse_mul_5_2
  · exact row16_eigenbasisInverse_mul_5_3
  · exact row16_eigenbasisInverse_mul_5_4
  · exact row16_eigenbasisInverse_mul_5_5
  · exact row16_eigenbasisInverse_mul_5_6
  · exact row16_eigenbasisInverse_mul_5_7
  · exact row16_eigenbasisInverse_mul_6_0
  · exact row16_eigenbasisInverse_mul_6_1
  · exact row16_eigenbasisInverse_mul_6_2
  · exact row16_eigenbasisInverse_mul_6_3
  · exact row16_eigenbasisInverse_mul_6_4
  · exact row16_eigenbasisInverse_mul_6_5
  · exact row16_eigenbasisInverse_mul_6_6
  · exact row16_eigenbasisInverse_mul_6_7
  · exact row16_eigenbasisInverse_mul_7_0
  · exact row16_eigenbasisInverse_mul_7_1
  · exact row16_eigenbasisInverse_mul_7_2
  · exact row16_eigenbasisInverse_mul_7_3
  · exact row16_eigenbasisInverse_mul_7_4
  · exact row16_eigenbasisInverse_mul_7_5
  · exact row16_eigenbasisInverse_mul_7_6
  · exact row16_eigenbasisInverse_mul_7_7

/-- The displayed row 16 inverse is also a right inverse. -/
theorem alternatingSixAmbientRow16Eigenbasis_mul_inverse :
    alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixAmbientRow16EigenbasisInverse_mul


private theorem row16_generatorB_mul_eigenbasis_0_0 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        0 0 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        0 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((17 / 5) : ℂ) - ((17 / 5) : ℂ) * ζ ^ 4 + ((2 / 5) : ℂ) * ζ ^ 8 - ((9 / 5) : ℂ) * ζ ^ 12 + ((6 / 5) : ℂ) * ζ ^ 16 - ((11 / 5) : ℂ) * ζ ^ 20 - ((3 / 5) : ℂ) * ζ ^ 24)
private theorem row16_generatorB_mul_eigenbasis_0_1 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        0 1 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        0 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((6 / 5) : ℂ) - ((6 / 5) : ℂ) * ζ ^ 4 - (4 : ℂ) * ζ ^ 8 + ((19 / 5) : ℂ) * ζ ^ 12 - (3 : ℂ) * ζ ^ 16 + ((11 / 5) : ℂ) * ζ ^ 20 + ((4 / 5) : ℂ) * ζ ^ 24)
private theorem row16_generatorB_mul_eigenbasis_0_2 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        0 2 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        0 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((12 / 5) : ℂ) - ((26 / 5) : ℂ) * ζ ^ 2 + ((12 / 5) : ℂ) * ζ ^ 4 + ((14 / 5) : ℂ) * ζ ^ 6 - ((13 / 5) : ℂ) * ζ ^ 8 - ((19 / 5) : ℂ) * ζ ^ 10 + ((23 / 5) : ℂ) * ζ ^ 12 + (6 : ℂ) * ζ ^ 14 - ((43 / 5) : ℂ) * ζ ^ 16 + ((1 / 5) : ℂ) * ζ ^ 18 + ((61 / 5) : ℂ) * ζ ^ 20 - ((6 / 5) : ℂ) * ζ ^ 22 - (3 : ℂ) * ζ ^ 24 + ((12 / 5) : ℂ) * ζ ^ 26 - ζ ^ 28)
private theorem row16_generatorB_mul_eigenbasis_0_3 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        0 3 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        0 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-(2 : ℂ) + ((22 / 5) : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 4 - ((12 / 5) : ℂ) * ζ ^ 6 - ((23 / 5) : ℂ) * ζ ^ 8 + ((8 / 5) : ℂ) * ζ ^ 10 + (7 : ℂ) * ζ ^ 12 - ((12 / 5) : ℂ) * ζ ^ 14 - ((34 / 5) : ℂ) * ζ ^ 16 - ((22 / 5) : ℂ) * ζ ^ 18 + ((13 / 5) : ℂ) * ζ ^ 20 + ((18 / 5) : ℂ) * ζ ^ 22 - ((4 / 5) : ℂ) * ζ ^ 24 + ((8 / 5) : ℂ) * ζ ^ 26 + ζ ^ 28)
private theorem row16_generatorB_mul_eigenbasis_0_4 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        0 4 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        0 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((144 / 55) : ℂ) - ((144 / 55) : ℂ) * ζ ^ 4 + ((4 / 55) : ℂ) * ζ ^ 8 - ((127 / 55) : ℂ) * ζ ^ 12 + ((208 / 55) : ℂ) * ζ ^ 16 - ((7 / 5) : ℂ) * ζ ^ 20 + ((151 / 55) : ℂ) * ζ ^ 24 - ((14 / 11) : ℂ) * ζ ^ 28 + ((16 / 11) : ℂ) * ζ ^ 32 - ((9 / 11) : ℂ) * ζ ^ 36 + ((9 / 11) : ℂ) * ζ ^ 40 + ((7 / 11) : ℂ) * ζ ^ 44 - ((6 / 11) : ℂ) * ζ ^ 48 + ((6 / 11) : ℂ) * ζ ^ 52 + ((1 / 11) : ℂ) * ζ ^ 56)
private theorem row16_generatorB_mul_eigenbasis_0_5 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        0 5 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        0 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((193 / 55) : ℂ) - ((193 / 55) : ℂ) * ζ ^ 4 + ((34 / 55) : ℂ) * ζ ^ 8 - ((7 / 55) : ℂ) * ζ ^ 12 + ((9 / 11) : ℂ) * ζ ^ 16 - ((7 / 11) : ℂ) * ζ ^ 20 + ((28 / 55) : ℂ) * ζ ^ 24 + ((2 / 11) : ℂ) * ζ ^ 28 + ((4 / 11) : ℂ) * ζ ^ 32 - ((5 / 11) : ℂ) * ζ ^ 36 + ((5 / 11) : ℂ) * ζ ^ 40 - ((1 / 11) : ℂ) * ζ ^ 44 + ((4 / 11) : ℂ) * ζ ^ 48 - ((4 / 11) : ℂ) * ζ ^ 52 + ((3 / 11) : ℂ) * ζ ^ 56)
private theorem row16_generatorB_mul_eigenbasis_0_6 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        0 6 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        0 6 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((12 / 5) : ℂ) + ((26 / 5) : ℂ) * ζ ^ 2 + ((12 / 5) : ℂ) * ζ ^ 4 - ((14 / 5) : ℂ) * ζ ^ 6 - ((13 / 5) : ℂ) * ζ ^ 8 + ((19 / 5) : ℂ) * ζ ^ 10 + ((23 / 5) : ℂ) * ζ ^ 12 - (6 : ℂ) * ζ ^ 14 - ((43 / 5) : ℂ) * ζ ^ 16 - ((1 / 5) : ℂ) * ζ ^ 18 + ((61 / 5) : ℂ) * ζ ^ 20 + ((6 / 5) : ℂ) * ζ ^ 22 - (3 : ℂ) * ζ ^ 24 - ((12 / 5) : ℂ) * ζ ^ 26 - ζ ^ 28 + ζ ^ 42 - ζ ^ 46 - ζ ^ 48 + ζ ^ 50 + ζ ^ 52 - ζ ^ 54 - ζ ^ 56 + ζ ^ 58 + ζ ^ 60 - ζ ^ 64 - ζ ^ 66 + ζ ^ 70 + ζ ^ 72 - ζ ^ 74 - ζ ^ 76 + ζ ^ 78 + ζ ^ 80 - ζ ^ 82 - ζ ^ 84 + ζ ^ 88)
private theorem row16_generatorB_mul_eigenbasis_0_7 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        0 7 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        0 7 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-(2 : ℂ) - ((22 / 5) : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 4 + ((12 / 5) : ℂ) * ζ ^ 6 - ((23 / 5) : ℂ) * ζ ^ 8 - ((8 / 5) : ℂ) * ζ ^ 10 + (7 : ℂ) * ζ ^ 12 + ((12 / 5) : ℂ) * ζ ^ 14 - ((34 / 5) : ℂ) * ζ ^ 16 + ((22 / 5) : ℂ) * ζ ^ 18 + ((13 / 5) : ℂ) * ζ ^ 20 - ((18 / 5) : ℂ) * ζ ^ 22 - ((4 / 5) : ℂ) * ζ ^ 24 - ((8 / 5) : ℂ) * ζ ^ 26 + ζ ^ 28 - (2 : ℂ) * ζ ^ 32 + (2 : ℂ) * ζ ^ 36 - ζ ^ 38 - (2 : ℂ) * ζ ^ 40 - ζ ^ 50 + ζ ^ 54 - ζ ^ 58 - ζ ^ 60 + ζ ^ 64 + ζ ^ 66 - ζ ^ 68 - ζ ^ 70 + (2 : ℂ) * ζ ^ 72 + ζ ^ 74 - (2 : ℂ) * ζ ^ 76 + ζ ^ 80 + ζ ^ 84 + ζ ^ 86 - ζ ^ 88)
private theorem row16_generatorB_mul_eigenbasis_1_0 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        1 0 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        1 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((6 / 5) : ℂ) + ((6 / 5) : ℂ) * ζ ^ 4 - ((4 / 5) : ℂ) * ζ ^ 12 - ((6 / 5) : ℂ) * ζ ^ 20 - ((4 / 5) : ℂ) * ζ ^ 24)
private theorem row16_generatorB_mul_eigenbasis_1_1 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        1 1 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        1 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-(1 : ℂ) + ζ ^ 4 - (3 : ℂ) * ζ ^ 8 + ζ ^ 12 - ζ ^ 20 + ζ ^ 24)
private theorem row16_generatorB_mul_eigenbasis_1_2 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        1 2 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        1 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 ((3 : ℂ) - ((28 / 5) : ℂ) * ζ ^ 2 - (3 : ℂ) * ζ ^ 4 + ((6 / 5) : ℂ) * ζ ^ 6 - ((36 / 5) : ℂ) * ζ ^ 8 - ((7 / 5) : ℂ) * ζ ^ 10 + ((33 / 5) : ℂ) * ζ ^ 12 - ((18 / 5) : ℂ) * ζ ^ 14 - (3 : ℂ) * ζ ^ 16 + ((13 / 5) : ℂ) * ζ ^ 18 - ((3 / 5) : ℂ) * ζ ^ 20 - ((14 / 5) : ℂ) * ζ ^ 22 + ((18 / 5) : ℂ) * ζ ^ 24 + ((2 / 5) : ℂ) * ζ ^ 26)
private theorem row16_generatorB_mul_eigenbasis_1_3 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        1 3 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        1 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((21 / 5) : ℂ) + ((17 / 5) : ℂ) * ζ ^ 2 + ((21 / 5) : ℂ) * ζ ^ 4 - ((14 / 5) : ℂ) * ζ ^ 6 - ((8 / 5) : ℂ) * ζ ^ 8 + ((8 / 5) : ℂ) * ζ ^ 10 + ((12 / 5) : ℂ) * ζ ^ 12 + ((7 / 5) : ℂ) * ζ ^ 14 - ((12 / 5) : ℂ) * ζ ^ 16 + ((6 / 5) : ℂ) * ζ ^ 18 - ((19 / 5) : ℂ) * ζ ^ 20 - ((12 / 5) : ℂ) * ζ ^ 22 + ζ ^ 24 + ((11 / 5) : ℂ) * ζ ^ 26 - ζ ^ 28)
private theorem row16_generatorB_mul_eigenbasis_1_4 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        1 4 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        1 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((28 / 55) : ℂ) + ((28 / 55) : ℂ) * ζ ^ 4 + ((17 / 55) : ℂ) * ζ ^ 8 + ((57 / 55) : ℂ) * ζ ^ 12 - ((9 / 11) : ℂ) * ζ ^ 16 + ((8 / 5) : ℂ) * ζ ^ 20 + ((52 / 55) : ℂ) * ζ ^ 24 - ((8 / 11) : ℂ) * ζ ^ 28 + ((10 / 11) : ℂ) * ζ ^ 32 - ((16 / 11) : ℂ) * ζ ^ 36 + ((16 / 11) : ℂ) * ζ ^ 40 - ((6 / 11) : ℂ) * ζ ^ 44 + ((5 / 11) : ℂ) * ζ ^ 48 - ((5 / 11) : ℂ) * ζ ^ 52 - ((1 / 11) : ℂ) * ζ ^ 56)
private theorem row16_generatorB_mul_eigenbasis_1_5 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        1 5 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        1 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((168 / 55) : ℂ) - ((168 / 55) : ℂ) * ζ ^ 4 + ((8 / 5) : ℂ) * ζ ^ 8 - ((1 / 5) : ℂ) * ζ ^ 12 - ((16 / 55) : ℂ) * ζ ^ 16 - ((16 / 11) : ℂ) * ζ ^ 20 - ((12 / 55) : ℂ) * ζ ^ 24 - ((3 / 11) : ℂ) * ζ ^ 28 - ((8 / 11) : ℂ) * ζ ^ 36 + ((8 / 11) : ℂ) * ζ ^ 40 - ((8 / 11) : ℂ) * ζ ^ 44 - ((2 / 11) : ℂ) * ζ ^ 48 + ((2 / 11) : ℂ) * ζ ^ 52 - ((10 / 11) : ℂ) * ζ ^ 56)
private theorem row16_generatorB_mul_eigenbasis_1_6 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        1 6 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        1 6 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 ((3 : ℂ) + ((28 / 5) : ℂ) * ζ ^ 2 - (3 : ℂ) * ζ ^ 4 - ((6 / 5) : ℂ) * ζ ^ 6 - ((36 / 5) : ℂ) * ζ ^ 8 + ((7 / 5) : ℂ) * ζ ^ 10 + ((33 / 5) : ℂ) * ζ ^ 12 + ((18 / 5) : ℂ) * ζ ^ 14 - (3 : ℂ) * ζ ^ 16 - ((13 / 5) : ℂ) * ζ ^ 18 - ((3 / 5) : ℂ) * ζ ^ 20 + ((14 / 5) : ℂ) * ζ ^ 22 + ((18 / 5) : ℂ) * ζ ^ 24 - ((2 / 5) : ℂ) * ζ ^ 26 + ζ ^ 30 - ζ ^ 32 - ζ ^ 34 + (2 : ℂ) * ζ ^ 38 - ζ ^ 42 - ζ ^ 44 + ζ ^ 46 + ζ ^ 48 + ζ ^ 50 - ζ ^ 52 - (2 : ℂ) * ζ ^ 54 + (2 : ℂ) * ζ ^ 58 + ζ ^ 60 - ζ ^ 62 - ζ ^ 64 + ζ ^ 68 - ζ ^ 74 + ζ ^ 80 - ζ ^ 86)
private theorem row16_generatorB_mul_eigenbasis_1_7 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        1 7 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        1 7 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((21 / 5) : ℂ) - ((17 / 5) : ℂ) * ζ ^ 2 + ((21 / 5) : ℂ) * ζ ^ 4 + ((14 / 5) : ℂ) * ζ ^ 6 - ((8 / 5) : ℂ) * ζ ^ 8 - ((8 / 5) : ℂ) * ζ ^ 10 + ((12 / 5) : ℂ) * ζ ^ 12 - ((7 / 5) : ℂ) * ζ ^ 14 - ((12 / 5) : ℂ) * ζ ^ 16 - ((6 / 5) : ℂ) * ζ ^ 18 - ((19 / 5) : ℂ) * ζ ^ 20 + ((12 / 5) : ℂ) * ζ ^ 22 + ζ ^ 24 - ((11 / 5) : ℂ) * ζ ^ 26 - ζ ^ 28 - ζ ^ 38 + ζ ^ 42 - ζ ^ 46 - ζ ^ 48 + ζ ^ 52 - ζ ^ 56 + ζ ^ 60 - ζ ^ 64 + ζ ^ 72 - ζ ^ 76 + ζ ^ 78 + ζ ^ 80 - ζ ^ 82 - ζ ^ 84 + ζ ^ 86 + ζ ^ 88)
private theorem row16_generatorB_mul_eigenbasis_2_0 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        2 0 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        2 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((18 / 5) : ℂ) + ((18 / 5) : ℂ) * ζ ^ 4 - (3 : ℂ) * ζ ^ 8 - ((12 / 5) : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 16 - ((33 / 5) : ℂ) * ζ ^ 20 - ((2 / 5) : ℂ) * ζ ^ 24)
private theorem row16_generatorB_mul_eigenbasis_2_1 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        2 1 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        2 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 ((2 : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 24)
private theorem row16_generatorB_mul_eigenbasis_2_2 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        2 2 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        2 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((51 / 5) : ℂ) * ζ ^ 2 - ((32 / 5) : ℂ) * ζ ^ 6 + ((57 / 5) : ℂ) * ζ ^ 8 - ((6 / 5) : ℂ) * ζ ^ 10 - ((31 / 5) : ℂ) * ζ ^ 12 - ((14 / 5) : ℂ) * ζ ^ 14 - ζ ^ 16 - ((26 / 5) : ℂ) * ζ ^ 18 - ((19 / 5) : ℂ) * ζ ^ 20 - ((12 / 5) : ℂ) * ζ ^ 22 - ((31 / 5) : ℂ) * ζ ^ 24 + ((16 / 5) : ℂ) * ζ ^ 26 - ζ ^ 28)
private theorem row16_generatorB_mul_eigenbasis_2_3 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        2 3 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        2 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((37 / 5) : ℂ) - ((24 / 5) : ℂ) * ζ ^ 2 - ((37 / 5) : ℂ) * ζ ^ 4 - ((2 / 5) : ℂ) * ζ ^ 6 + ((31 / 5) : ℂ) * ζ ^ 8 + ((19 / 5) : ℂ) * ζ ^ 10 - ((19 / 5) : ℂ) * ζ ^ 12 - ((14 / 5) : ℂ) * ζ ^ 14 + ((14 / 5) : ℂ) * ζ ^ 16 + ((8 / 5) : ℂ) * ζ ^ 18 - ((7 / 5) : ℂ) * ζ ^ 20 + ((9 / 5) : ℂ) * ζ ^ 22 - ζ ^ 24 - ((12 / 5) : ℂ) * ζ ^ 26)
private theorem row16_generatorB_mul_eigenbasis_2_4 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        2 4 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        2 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((89 / 55) : ℂ) + ((89 / 55) : ℂ) * ζ ^ 4 - ((4 / 5) : ℂ) * ζ ^ 8 - ((74 / 55) : ℂ) * ζ ^ 12 + ((20 / 11) : ℂ) * ζ ^ 16 - ((6 / 5) : ℂ) * ζ ^ 20 + ((51 / 55) : ℂ) * ζ ^ 24 - ((5 / 11) : ℂ) * ζ ^ 28 + ((4 / 11) : ℂ) * ζ ^ 32 + ((2 / 11) : ℂ) * ζ ^ 36 - ((2 / 11) : ℂ) * ζ ^ 40 + ((6 / 11) : ℂ) * ζ ^ 44 - ((8 / 11) : ℂ) * ζ ^ 48 + ((8 / 11) : ℂ) * ζ ^ 52 - ((2 / 11) : ℂ) * ζ ^ 56)
private theorem row16_generatorB_mul_eigenbasis_2_5 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        2 5 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        2 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((161 / 55) : ℂ) + ((161 / 55) : ℂ) * ζ ^ 4 + ((269 / 55) : ℂ) * ζ ^ 8 - ((188 / 55) : ℂ) * ζ ^ 12 - ((8 / 55) : ℂ) * ζ ^ 16 - ((27 / 11) : ℂ) * ζ ^ 20 - ((241 / 55) : ℂ) * ζ ^ 24 + ((9 / 11) : ℂ) * ζ ^ 28 - ((16 / 11) : ℂ) * ζ ^ 32 + ((14 / 11) : ℂ) * ζ ^ 36 - ((14 / 11) : ℂ) * ζ ^ 40 - ((2 / 11) : ℂ) * ζ ^ 44 + ((10 / 11) : ℂ) * ζ ^ 48 - ((10 / 11) : ℂ) * ζ ^ 52 + ((8 / 11) : ℂ) * ζ ^ 56)
private theorem row16_generatorB_mul_eigenbasis_2_6 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        2 6 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        2 6 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((51 / 5) : ℂ) * ζ ^ 2 + ((32 / 5) : ℂ) * ζ ^ 6 + ((57 / 5) : ℂ) * ζ ^ 8 + ((6 / 5) : ℂ) * ζ ^ 10 - ((31 / 5) : ℂ) * ζ ^ 12 + ((14 / 5) : ℂ) * ζ ^ 14 - ζ ^ 16 + ((26 / 5) : ℂ) * ζ ^ 18 - ((19 / 5) : ℂ) * ζ ^ 20 + ((12 / 5) : ℂ) * ζ ^ 22 - ((31 / 5) : ℂ) * ζ ^ 24 - ((16 / 5) : ℂ) * ζ ^ 26 - ζ ^ 28 + ζ ^ 30 - ζ ^ 34 + ζ ^ 36 - ζ ^ 40 + ζ ^ 44 - (2 : ℂ) * ζ ^ 54 + ζ ^ 56 + (2 : ℂ) * ζ ^ 58 - (2 : ℂ) * ζ ^ 62 + ζ ^ 66 + ζ ^ 68 - ζ ^ 70 - ζ ^ 74 + (2 : ℂ) * ζ ^ 78 + ζ ^ 80 - (2 : ℂ) * ζ ^ 82 - ζ ^ 84 + ζ ^ 86 + ζ ^ 88)
private theorem row16_generatorB_mul_eigenbasis_2_7 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        2 7 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        2 7 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((37 / 5) : ℂ) + ((24 / 5) : ℂ) * ζ ^ 2 - ((37 / 5) : ℂ) * ζ ^ 4 + ((2 / 5) : ℂ) * ζ ^ 6 + ((31 / 5) : ℂ) * ζ ^ 8 - ((19 / 5) : ℂ) * ζ ^ 10 - ((19 / 5) : ℂ) * ζ ^ 12 + ((14 / 5) : ℂ) * ζ ^ 14 + ((14 / 5) : ℂ) * ζ ^ 16 - ((8 / 5) : ℂ) * ζ ^ 18 - ((7 / 5) : ℂ) * ζ ^ 20 - ((9 / 5) : ℂ) * ζ ^ 22 - ζ ^ 24 + ((12 / 5) : ℂ) * ζ ^ 26 + ζ ^ 36 - ζ ^ 40 + ζ ^ 42 + ζ ^ 44 - ζ ^ 46 - ζ ^ 48 + ζ ^ 50 + ζ ^ 52 - ζ ^ 54 + ζ ^ 58 - ζ ^ 60 + ζ ^ 64 - ζ ^ 66 - ζ ^ 68 + ζ ^ 70 + ζ ^ 72 - ζ ^ 74 - ζ ^ 76 + ζ ^ 78 - ζ ^ 82)
private theorem row16_generatorB_mul_eigenbasis_3_0 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        3 0 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        3 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((3 / 5) : ℂ) - ((3 / 5) : ℂ) * ζ ^ 4 + ((9 / 5) : ℂ) * ζ ^ 8 - ((2 / 5) : ℂ) * ζ ^ 12 + ((2 / 5) : ℂ) * ζ ^ 16 + ((2 / 5) : ℂ) * ζ ^ 20)
private theorem row16_generatorB_mul_eigenbasis_3_1 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        3 1 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        3 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((8 / 5) : ℂ) + ((8 / 5) : ℂ) * ζ ^ 4 - ζ ^ 8 + ((3 / 5) : ℂ) * ζ ^ 12 - ζ ^ 16 - ((3 / 5) : ℂ) * ζ ^ 20 - ((2 / 5) : ℂ) * ζ ^ 24)
private theorem row16_generatorB_mul_eigenbasis_3_2 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        3 2 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        3 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((9 / 5) : ℂ) - (3 : ℂ) * ζ ^ 2 + ((9 / 5) : ℂ) * ζ ^ 4 - ((1 / 5) : ℂ) * ζ ^ 6 - ((17 / 5) : ℂ) * ζ ^ 8 + ζ ^ 10 + ((4 / 5) : ℂ) * ζ ^ 12 + ((2 / 5) : ℂ) * ζ ^ 14 - ((1 / 5) : ℂ) * ζ ^ 16 + (3 : ℂ) * ζ ^ 18 + ((9 / 5) : ℂ) * ζ ^ 20 - ((11 / 5) : ℂ) * ζ ^ 22 + ((13 / 5) : ℂ) * ζ ^ 24 - ((4 / 5) : ℂ) * ζ ^ 26 - (2 : ℂ) * ζ ^ 28)
private theorem row16_generatorB_mul_eigenbasis_3_3 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        3 3 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        3 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((1 / 5) : ℂ) + ((6 / 5) : ℂ) * ζ ^ 2 + ((1 / 5) : ℂ) * ζ ^ 4 - ((3 / 5) : ℂ) * ζ ^ 6 + ((1 / 5) : ℂ) * ζ ^ 8 + ((4 / 5) : ℂ) * ζ ^ 10 - ((3 / 5) : ℂ) * ζ ^ 12 + ((3 / 5) : ℂ) * ζ ^ 14 + ((2 / 5) : ℂ) * ζ ^ 18 - ((3 / 5) : ℂ) * ζ ^ 20 - ((1 / 5) : ℂ) * ζ ^ 22 - ((13 / 5) : ℂ) * ζ ^ 24 - ((3 / 5) : ℂ) * ζ ^ 26 + (2 : ℂ) * ζ ^ 28)
private theorem row16_generatorB_mul_eigenbasis_3_4 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        3 4 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        3 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((5 / 11) : ℂ) - ((5 / 11) : ℂ) * ζ ^ 4 + ((15 / 11) : ℂ) * ζ ^ 8 - ((102 / 55) : ℂ) * ζ ^ 12 + ((76 / 55) : ℂ) * ζ ^ 16 - ((36 / 55) : ℂ) * ζ ^ 20 - ((6 / 55) : ℂ) * ζ ^ 24 - ((4 / 11) : ℂ) * ζ ^ 28 + ((8 / 11) : ℂ) * ζ ^ 32 - ((2 / 11) : ℂ) * ζ ^ 36 + ((2 / 11) : ℂ) * ζ ^ 40 + ((6 / 11) : ℂ) * ζ ^ 44 - ((12 / 11) : ℂ) * ζ ^ 48 + ((12 / 11) : ℂ) * ζ ^ 52 - ((6 / 11) : ℂ) * ζ ^ 56)
private theorem row16_generatorB_mul_eigenbasis_3_5 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        3 5 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        3 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((114 / 55) : ℂ) - ((114 / 55) : ℂ) * ζ ^ 4 - ((59 / 55) : ℂ) * ζ ^ 8 - ((7 / 11) : ℂ) * ζ ^ 12 + ((79 / 55) : ℂ) * ζ ^ 16 - ((1 / 11) : ℂ) * ζ ^ 20 + ((69 / 55) : ℂ) * ζ ^ 24 - ((5 / 11) : ℂ) * ζ ^ 28 + ((3 / 11) : ℂ) * ζ ^ 32 + ((3 / 11) : ℂ) * ζ ^ 44 - ((5 / 11) : ℂ) * ζ ^ 48 + ((5 / 11) : ℂ) * ζ ^ 52 - ((2 / 11) : ℂ) * ζ ^ 56)
private theorem row16_generatorB_mul_eigenbasis_3_6 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        3 6 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        3 6 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((9 / 5) : ℂ) + (3 : ℂ) * ζ ^ 2 + ((9 / 5) : ℂ) * ζ ^ 4 + ((1 / 5) : ℂ) * ζ ^ 6 - ((17 / 5) : ℂ) * ζ ^ 8 - ζ ^ 10 + ((4 / 5) : ℂ) * ζ ^ 12 - ((2 / 5) : ℂ) * ζ ^ 14 - ((1 / 5) : ℂ) * ζ ^ 16 - (3 : ℂ) * ζ ^ 18 + ((9 / 5) : ℂ) * ζ ^ 20 + ((11 / 5) : ℂ) * ζ ^ 22 + ((13 / 5) : ℂ) * ζ ^ 24 + ((4 / 5) : ℂ) * ζ ^ 26 - (2 : ℂ) * ζ ^ 28 + ζ ^ 30 - ζ ^ 34 + ζ ^ 36 - ζ ^ 40 + (2 : ℂ) * ζ ^ 42 + ζ ^ 44 - (2 : ℂ) * ζ ^ 46 - (2 : ℂ) * ζ ^ 48 + (2 : ℂ) * ζ ^ 50 + (2 : ℂ) * ζ ^ 52 - (2 : ℂ) * ζ ^ 54 - ζ ^ 56 + (2 : ℂ) * ζ ^ 58 + ζ ^ 60 - ζ ^ 64 - ζ ^ 66 + ζ ^ 70 + (2 : ℂ) * ζ ^ 72 - ζ ^ 74 - (2 : ℂ) * ζ ^ 76 + (2 : ℂ) * ζ ^ 78 + (2 : ℂ) * ζ ^ 80 - (2 : ℂ) * ζ ^ 82 - (2 : ℂ) * ζ ^ 84 + ζ ^ 86 + (2 : ℂ) * ζ ^ 88)
private theorem row16_generatorB_mul_eigenbasis_3_7 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        3 7 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        3 7 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((1 / 5) : ℂ) - ((6 / 5) : ℂ) * ζ ^ 2 + ((1 / 5) : ℂ) * ζ ^ 4 + ((3 / 5) : ℂ) * ζ ^ 6 + ((1 / 5) : ℂ) * ζ ^ 8 - ((4 / 5) : ℂ) * ζ ^ 10 - ((3 / 5) : ℂ) * ζ ^ 12 - ((3 / 5) : ℂ) * ζ ^ 14 - ((2 / 5) : ℂ) * ζ ^ 18 - ((3 / 5) : ℂ) * ζ ^ 20 + ((1 / 5) : ℂ) * ζ ^ 22 - ((13 / 5) : ℂ) * ζ ^ 24 + ((3 / 5) : ℂ) * ζ ^ 26 + (2 : ℂ) * ζ ^ 28 - ζ ^ 30 - ζ ^ 32 + ζ ^ 34 + (2 : ℂ) * ζ ^ 36 - (2 : ℂ) * ζ ^ 40 - ζ ^ 42 + ζ ^ 44 + ζ ^ 46 - (2 : ℂ) * ζ ^ 48 - ζ ^ 50 + (2 : ℂ) * ζ ^ 52 - ζ ^ 54 - ζ ^ 56 + ζ ^ 58 - (3 : ℂ) * ζ ^ 60 - (2 : ℂ) * ζ ^ 62 + (3 : ℂ) * ζ ^ 64 - (4 : ℂ) * ζ ^ 68 + (3 : ℂ) * ζ ^ 72 - (2 : ℂ) * ζ ^ 74 - (3 : ℂ) * ζ ^ 76 + ζ ^ 78 - ζ ^ 80 - ζ ^ 82 + (2 : ℂ) * ζ ^ 84 - ζ ^ 86 - (2 : ℂ) * ζ ^ 88)
private theorem row16_generatorB_mul_eigenbasis_4_0 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        4 0 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        4 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((3 / 5) : ℂ) + ((3 / 5) : ℂ) * ζ ^ 4 - ((6 / 5) : ℂ) * ζ ^ 8 - ((1 / 5) : ℂ) * ζ ^ 12 + ((12 / 5) : ℂ) * ζ ^ 16 - ((9 / 5) : ℂ) * ζ ^ 20 + ((11 / 5) : ℂ) * ζ ^ 24)
private theorem row16_generatorB_mul_eigenbasis_4_1 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        4 1 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        4 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((7 / 5) : ℂ) - ((7 / 5) : ℂ) * ζ ^ 4 + (4 : ℂ) * ζ ^ 8 - ((12 / 5) : ℂ) * ζ ^ 12 + ζ ^ 16 - ((3 / 5) : ℂ) * ζ ^ 20 - ((7 / 5) : ℂ) * ζ ^ 24)
private theorem row16_generatorB_mul_eigenbasis_4_2 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        4 2 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        4 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((1 / 5) : ℂ) + ((47 / 5) : ℂ) * ζ ^ 2 - ((1 / 5) : ℂ) * ζ ^ 4 - (6 : ℂ) * ζ ^ 6 + ((47 / 5) : ℂ) * ζ ^ 8 + ((8 / 5) : ℂ) * ζ ^ 10 - ((38 / 5) : ℂ) * ζ ^ 12 - ((11 / 5) : ℂ) * ζ ^ 14 + ((19 / 5) : ℂ) * ζ ^ 16 - ((22 / 5) : ℂ) * ζ ^ 18 - ((29 / 5) : ℂ) * ζ ^ 20 - ((19 / 5) : ℂ) * ζ ^ 24 - ((2 / 5) : ℂ) * ζ ^ 26)
private theorem row16_generatorB_mul_eigenbasis_4_3 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        4 3 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        4 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((43 / 5) : ℂ) - ((22 / 5) : ℂ) * ζ ^ 2 - ((43 / 5) : ℂ) * ζ ^ 4 + ((3 / 5) : ℂ) * ζ ^ 6 + ((23 / 5) : ℂ) * ζ ^ 8 + ((7 / 5) : ℂ) * ζ ^ 10 - ((31 / 5) : ℂ) * ζ ^ 12 + ζ ^ 14 + ((38 / 5) : ℂ) * ζ ^ 16 + ((3 / 5) : ℂ) * ζ ^ 18 - ((12 / 5) : ℂ) * ζ ^ 20 + ((7 / 5) : ℂ) * ζ ^ 22 + ((7 / 5) : ℂ) * ζ ^ 24 - ((17 / 5) : ℂ) * ζ ^ 26)
private theorem row16_generatorB_mul_eigenbasis_4_4 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        4 4 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        4 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((153 / 55) : ℂ) + ((153 / 55) : ℂ) * ζ ^ 4 + ((32 / 55) : ℂ) * ζ ^ 8 + ((3 / 11) : ℂ) * ζ ^ 12 - ((54 / 55) : ℂ) * ζ ^ 16 - ((23 / 55) : ℂ) * ζ ^ 20 - ((4 / 5) : ℂ) * ζ ^ 24 + ((1 / 11) : ℂ) * ζ ^ 28 + ((3 / 11) : ℂ) * ζ ^ 32 - ((6 / 11) : ℂ) * ζ ^ 36 + ((6 / 11) : ℂ) * ζ ^ 40 - ((3 / 11) : ℂ) * ζ ^ 44 - ((1 / 11) : ℂ) * ζ ^ 48 + ((1 / 11) : ℂ) * ζ ^ 52 - ((4 / 11) : ℂ) * ζ ^ 56)
private theorem row16_generatorB_mul_eigenbasis_4_5 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        4 5 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        4 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((13 / 5) : ℂ) + ((13 / 5) : ℂ) * ζ ^ 4 + ((54 / 55) : ℂ) * ζ ^ 8 - ((146 / 55) : ℂ) * ζ ^ 12 + ((73 / 55) : ℂ) * ζ ^ 16 - ((3 / 11) : ℂ) * ζ ^ 20 - ((73 / 55) : ℂ) * ζ ^ 24 - ((4 / 11) : ℂ) * ζ ^ 32 + ((14 / 11) : ℂ) * ζ ^ 36 - ((14 / 11) : ℂ) * ζ ^ 40 + ((10 / 11) : ℂ) * ζ ^ 44 - ((10 / 11) : ℂ) * ζ ^ 48 + ((10 / 11) : ℂ) * ζ ^ 52)
private theorem row16_generatorB_mul_eigenbasis_4_6 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        4 6 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        4 6 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((1 / 5) : ℂ) - ((47 / 5) : ℂ) * ζ ^ 2 - ((1 / 5) : ℂ) * ζ ^ 4 + (6 : ℂ) * ζ ^ 6 + ((47 / 5) : ℂ) * ζ ^ 8 - ((8 / 5) : ℂ) * ζ ^ 10 - ((38 / 5) : ℂ) * ζ ^ 12 + ((11 / 5) : ℂ) * ζ ^ 14 + ((19 / 5) : ℂ) * ζ ^ 16 + ((22 / 5) : ℂ) * ζ ^ 18 - ((29 / 5) : ℂ) * ζ ^ 20 - ((19 / 5) : ℂ) * ζ ^ 24 + ((2 / 5) : ℂ) * ζ ^ 26 + ζ ^ 30 + (2 : ℂ) * ζ ^ 32 - ζ ^ 34 - ζ ^ 36 - ζ ^ 38 + ζ ^ 40 + ζ ^ 42 + ζ ^ 44 - ζ ^ 46 - ζ ^ 48 + ζ ^ 52 + ζ ^ 54 - ζ ^ 58 - ζ ^ 60 + ζ ^ 62 + ζ ^ 64 + ζ ^ 66 - ζ ^ 68 - ζ ^ 70 - ζ ^ 72 + (2 : ℂ) * ζ ^ 74 + ζ ^ 76 - (2 : ℂ) * ζ ^ 80 + (2 : ℂ) * ζ ^ 86)
private theorem row16_generatorB_mul_eigenbasis_4_7 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        4 7 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        4 7 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((43 / 5) : ℂ) + ((22 / 5) : ℂ) * ζ ^ 2 - ((43 / 5) : ℂ) * ζ ^ 4 - ((3 / 5) : ℂ) * ζ ^ 6 + ((23 / 5) : ℂ) * ζ ^ 8 - ((7 / 5) : ℂ) * ζ ^ 10 - ((31 / 5) : ℂ) * ζ ^ 12 - ζ ^ 14 + ((38 / 5) : ℂ) * ζ ^ 16 - ((3 / 5) : ℂ) * ζ ^ 18 - ((12 / 5) : ℂ) * ζ ^ 20 - ((7 / 5) : ℂ) * ζ ^ 22 + ((7 / 5) : ℂ) * ζ ^ 24 + ((17 / 5) : ℂ) * ζ ^ 26 - ζ ^ 30 + ζ ^ 34 - ζ ^ 36 - ζ ^ 38 + ζ ^ 40 - ζ ^ 42 - ζ ^ 44 + ζ ^ 46 - ζ ^ 48 - (2 : ℂ) * ζ ^ 50 + ζ ^ 52 - (2 : ℂ) * ζ ^ 56 + ζ ^ 60 - (2 : ℂ) * ζ ^ 62 - ζ ^ 64 + ζ ^ 66 - ζ ^ 68 - ζ ^ 70 + ζ ^ 72 - ζ ^ 74 - ζ ^ 76 + ζ ^ 78 - ζ ^ 82)
private theorem row16_generatorB_mul_eigenbasis_5_0 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        5 0 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        5 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((12 / 5) : ℂ) - ((12 / 5) : ℂ) * ζ ^ 4 - ((4 / 5) : ℂ) * ζ ^ 8 - ((13 / 5) : ℂ) * ζ ^ 12 + ((13 / 5) : ℂ) * ζ ^ 16 - ((22 / 5) : ℂ) * ζ ^ 20)
private theorem row16_generatorB_mul_eigenbasis_5_1 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        5 1 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        5 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((8 / 5) : ℂ) - ((8 / 5) : ℂ) * ζ ^ 4 - ζ ^ 8 + ((7 / 5) : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 16 + ((8 / 5) : ℂ) * ζ ^ 20 - ((3 / 5) : ℂ) * ζ ^ 24)
private theorem row16_generatorB_mul_eigenbasis_5_2 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        5 2 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        5 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((16 / 5) : ℂ) + (2 : ℂ) * ζ ^ 2 + ((16 / 5) : ℂ) * ζ ^ 4 + ((1 / 5) : ℂ) * ζ ^ 6 + ((27 / 5) : ℂ) * ζ ^ 8 - (4 : ℂ) * ζ ^ 10 - ((19 / 5) : ℂ) * ζ ^ 12 + ((28 / 5) : ℂ) * ζ ^ 14 - ((19 / 5) : ℂ) * ζ ^ 16 - (5 : ℂ) * ζ ^ 18 + ((36 / 5) : ℂ) * ζ ^ 20 + ((6 / 5) : ℂ) * ζ ^ 22 - ((23 / 5) : ℂ) * ζ ^ 24 + ((9 / 5) : ℂ) * ζ ^ 26 - (3 : ℂ) * ζ ^ 28)
private theorem row16_generatorB_mul_eigenbasis_5_3 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        5 3 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        5 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((21 / 5) : ℂ) - ((6 / 5) : ℂ) * ζ ^ 2 - ((21 / 5) : ℂ) * ζ ^ 4 + ((8 / 5) : ℂ) * ζ ^ 6 - ((1 / 5) : ℂ) * ζ ^ 8 + ((1 / 5) : ℂ) * ζ ^ 10 + ((18 / 5) : ℂ) * ζ ^ 12 - ((23 / 5) : ℂ) * ζ ^ 14 - (3 : ℂ) * ζ ^ 16 - ((17 / 5) : ℂ) * ζ ^ 18 + ((18 / 5) : ℂ) * ζ ^ 20 + ((26 / 5) : ℂ) * ζ ^ 22 - ((2 / 5) : ℂ) * ζ ^ 24 - ((12 / 5) : ℂ) * ζ ^ 26 + ζ ^ 28)
private theorem row16_generatorB_mul_eigenbasis_5_4 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        5 4 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        5 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((15 / 11) : ℂ) - ((15 / 11) : ℂ) * ζ ^ 4 - ((2 / 11) : ℂ) * ζ ^ 8 - ((13 / 5) : ℂ) * ζ ^ 12 + ((219 / 55) : ℂ) * ζ ^ 16 - ((14 / 5) : ℂ) * ζ ^ 20 + ((86 / 55) : ℂ) * ζ ^ 24 - ((2 / 11) : ℂ) * ζ ^ 28 + ((2 / 11) : ℂ) * ζ ^ 32 - ((5 / 11) : ℂ) * ζ ^ 36 + ((5 / 11) : ℂ) * ζ ^ 40 - ((3 / 11) : ℂ) * ζ ^ 44 - ((3 / 11) : ℂ) * ζ ^ 56)
private theorem row16_generatorB_mul_eigenbasis_5_5 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        5 5 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        5 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((46 / 55) : ℂ) - ((46 / 55) : ℂ) * ζ ^ 4 + ((149 / 55) : ℂ) * ζ ^ 8 - (3 : ℂ) * ζ ^ 12 + ((76 / 55) : ℂ) * ζ ^ 16 - ((20 / 11) : ℂ) * ζ ^ 20 - ((79 / 55) : ℂ) * ζ ^ 24 - ((2 / 11) : ℂ) * ζ ^ 28 - ((6 / 11) : ℂ) * ζ ^ 32 + ((12 / 11) : ℂ) * ζ ^ 36 - ((12 / 11) : ℂ) * ζ ^ 40 + ((6 / 11) : ℂ) * ζ ^ 44 + ((2 / 11) : ℂ) * ζ ^ 48 - ((2 / 11) : ℂ) * ζ ^ 52 + ((8 / 11) : ℂ) * ζ ^ 56)
private theorem row16_generatorB_mul_eigenbasis_5_6 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        5 6 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        5 6 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((16 / 5) : ℂ) - (2 : ℂ) * ζ ^ 2 + ((16 / 5) : ℂ) * ζ ^ 4 - ((1 / 5) : ℂ) * ζ ^ 6 + ((27 / 5) : ℂ) * ζ ^ 8 + (4 : ℂ) * ζ ^ 10 - ((19 / 5) : ℂ) * ζ ^ 12 - ((28 / 5) : ℂ) * ζ ^ 14 - ((19 / 5) : ℂ) * ζ ^ 16 + (5 : ℂ) * ζ ^ 18 + ((36 / 5) : ℂ) * ζ ^ 20 - ((6 / 5) : ℂ) * ζ ^ 22 - ((23 / 5) : ℂ) * ζ ^ 24 - ((9 / 5) : ℂ) * ζ ^ 26 - (3 : ℂ) * ζ ^ 28 - ζ ^ 30 - ζ ^ 32 + ζ ^ 34 + (2 : ℂ) * ζ ^ 36 + ζ ^ 38 - (2 : ℂ) * ζ ^ 40 - ζ ^ 42 + ζ ^ 44 + ζ ^ 46 - (2 : ℂ) * ζ ^ 48 + (2 : ℂ) * ζ ^ 52 - ζ ^ 54 - ζ ^ 56 + ζ ^ 58 + (2 : ℂ) * ζ ^ 60 - ζ ^ 62 - (2 : ℂ) * ζ ^ 64 - ζ ^ 66 + ζ ^ 68 + ζ ^ 70 + (3 : ℂ) * ζ ^ 72 - (2 : ℂ) * ζ ^ 74 - (3 : ℂ) * ζ ^ 76 + (4 : ℂ) * ζ ^ 80 - (3 : ℂ) * ζ ^ 84 - (2 : ℂ) * ζ ^ 86 + (3 : ℂ) * ζ ^ 88)
private theorem row16_generatorB_mul_eigenbasis_5_7 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        5 7 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        5 7 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((21 / 5) : ℂ) + ((6 / 5) : ℂ) * ζ ^ 2 - ((21 / 5) : ℂ) * ζ ^ 4 - ((8 / 5) : ℂ) * ζ ^ 6 - ((1 / 5) : ℂ) * ζ ^ 8 - ((1 / 5) : ℂ) * ζ ^ 10 + ((18 / 5) : ℂ) * ζ ^ 12 + ((23 / 5) : ℂ) * ζ ^ 14 - (3 : ℂ) * ζ ^ 16 + ((17 / 5) : ℂ) * ζ ^ 18 + ((18 / 5) : ℂ) * ζ ^ 20 - ((26 / 5) : ℂ) * ζ ^ 22 - ((2 / 5) : ℂ) * ζ ^ 24 + ((12 / 5) : ℂ) * ζ ^ 26 + ζ ^ 28 + (2 : ℂ) * ζ ^ 30 - ζ ^ 32 - (2 : ℂ) * ζ ^ 34 + (2 : ℂ) * ζ ^ 36 + (2 : ℂ) * ζ ^ 38 - (2 : ℂ) * ζ ^ 40 - (2 : ℂ) * ζ ^ 42 + ζ ^ 44 + (2 : ℂ) * ζ ^ 46 - ζ ^ 48 + ζ ^ 52 - ζ ^ 54 + ζ ^ 58 - (2 : ℂ) * ζ ^ 60 - ζ ^ 62 + (2 : ℂ) * ζ ^ 64 + (2 : ℂ) * ζ ^ 66 - (2 : ℂ) * ζ ^ 68 - (2 : ℂ) * ζ ^ 70 + (2 : ℂ) * ζ ^ 72 + ζ ^ 74 - (2 : ℂ) * ζ ^ 76 - ζ ^ 78 + ζ ^ 82 + ζ ^ 84 - ζ ^ 88)
private theorem row16_generatorB_mul_eigenbasis_6_0 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        6 0 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        6 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((2 / 5) : ℂ) + ((2 / 5) : ℂ) * ζ ^ 4 + ((6 / 5) : ℂ) * ζ ^ 8 - ((4 / 5) : ℂ) * ζ ^ 12 + ((3 / 5) : ℂ) * ζ ^ 16 - ((6 / 5) : ℂ) * ζ ^ 20 - ((1 / 5) : ℂ) * ζ ^ 24)
private theorem row16_generatorB_mul_eigenbasis_6_1 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        6 1 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        6 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((2 / 5) : ℂ) + ((2 / 5) : ℂ) * ζ ^ 4 - ζ ^ 8 + ((2 / 5) : ℂ) * ζ ^ 12 - ((2 / 5) : ℂ) * ζ ^ 20 + ((2 / 5) : ℂ) * ζ ^ 24)
private theorem row16_generatorB_mul_eigenbasis_6_2 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        6 2 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        6 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((4 / 5) : ℂ) - ((12 / 5) : ℂ) * ζ ^ 2 - ((4 / 5) : ℂ) * ζ ^ 4 + ζ ^ 6 - ((17 / 5) : ℂ) * ζ ^ 8 - ((8 / 5) : ℂ) * ζ ^ 10 + ((18 / 5) : ℂ) * ζ ^ 12 - ((4 / 5) : ℂ) * ζ ^ 14 - ((9 / 5) : ℂ) * ζ ^ 16 + ((2 / 5) : ℂ) * ζ ^ 18 - ((1 / 5) : ℂ) * ζ ^ 20 - ζ ^ 22 + ((9 / 5) : ℂ) * ζ ^ 24 - ((3 / 5) : ℂ) * ζ ^ 26)
private theorem row16_generatorB_mul_eigenbasis_6_3 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        6 3 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        6 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((8 / 5) : ℂ) + ((7 / 5) : ℂ) * ζ ^ 2 + ((8 / 5) : ℂ) * ζ ^ 4 - ((3 / 5) : ℂ) * ζ ^ 6 + ((2 / 5) : ℂ) * ζ ^ 8 - ((2 / 5) : ℂ) * ζ ^ 10 + ((1 / 5) : ℂ) * ζ ^ 12 + (3 : ℂ) * ζ ^ 14 - ((3 / 5) : ℂ) * ζ ^ 16 - ((8 / 5) : ℂ) * ζ ^ 18 - ((13 / 5) : ℂ) * ζ ^ 20 + ((3 / 5) : ℂ) * ζ ^ 22 - ((2 / 5) : ℂ) * ζ ^ 24 + ((7 / 5) : ℂ) * ζ ^ 26)
private theorem row16_generatorB_mul_eigenbasis_6_4 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        6 4 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        6 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((23 / 55) : ℂ) - ((23 / 55) : ℂ) * ζ ^ 4 + ((53 / 55) : ℂ) * ζ ^ 8 - ((12 / 11) : ℂ) * ζ ^ 12 + ((49 / 55) : ℂ) * ζ ^ 16 + ((13 / 55) : ℂ) * ζ ^ 20 + ((4 / 5) : ℂ) * ζ ^ 24 - ζ ^ 28)
private theorem row16_generatorB_mul_eigenbasis_6_5 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        6 5 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        6 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((58 / 55) : ℂ) - ((58 / 55) : ℂ) * ζ ^ 4 + ((71 / 55) : ℂ) * ζ ^ 8 + ((16 / 55) : ℂ) * ζ ^ 12 - ((38 / 55) : ℂ) * ζ ^ 16 - ((2 / 5) : ℂ) * ζ ^ 24)
private theorem row16_generatorB_mul_eigenbasis_6_6 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        6 6 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        6 6 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((4 / 5) : ℂ) + ((12 / 5) : ℂ) * ζ ^ 2 - ((4 / 5) : ℂ) * ζ ^ 4 - ζ ^ 6 - ((17 / 5) : ℂ) * ζ ^ 8 + ((8 / 5) : ℂ) * ζ ^ 10 + ((18 / 5) : ℂ) * ζ ^ 12 + ((4 / 5) : ℂ) * ζ ^ 14 - ((9 / 5) : ℂ) * ζ ^ 16 - ((2 / 5) : ℂ) * ζ ^ 18 - ((1 / 5) : ℂ) * ζ ^ 20 + ζ ^ 22 + ((9 / 5) : ℂ) * ζ ^ 24 + ((3 / 5) : ℂ) * ζ ^ 26 - ζ ^ 30 + ζ ^ 34 - ζ ^ 38 - ζ ^ 50 + ζ ^ 54 - ζ ^ 58)
private theorem row16_generatorB_mul_eigenbasis_6_7 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        6 7 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        6 7 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((8 / 5) : ℂ) - ((7 / 5) : ℂ) * ζ ^ 2 + ((8 / 5) : ℂ) * ζ ^ 4 + ((3 / 5) : ℂ) * ζ ^ 6 + ((2 / 5) : ℂ) * ζ ^ 8 + ((2 / 5) : ℂ) * ζ ^ 10 + ((1 / 5) : ℂ) * ζ ^ 12 - (3 : ℂ) * ζ ^ 14 - ((3 / 5) : ℂ) * ζ ^ 16 + ((8 / 5) : ℂ) * ζ ^ 18 - ((13 / 5) : ℂ) * ζ ^ 20 - ((3 / 5) : ℂ) * ζ ^ 22 - ((2 / 5) : ℂ) * ζ ^ 24 - ((7 / 5) : ℂ) * ζ ^ 26)
private theorem row16_generatorB_mul_eigenbasis_7_0 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        7 0 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        7 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((8 / 5) : ℂ) + ((8 / 5) : ℂ) * ζ ^ 4 - ((7 / 5) : ℂ) * ζ ^ 8 - ζ ^ 12 - ((1 / 5) : ℂ) * ζ ^ 16 - (2 : ℂ) * ζ ^ 20 - ((6 / 5) : ℂ) * ζ ^ 24)
private theorem row16_generatorB_mul_eigenbasis_7_1 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        7 1 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        7 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((1 / 5) : ℂ) + ((1 / 5) : ℂ) * ζ ^ 4 - (2 : ℂ) * ζ ^ 8 + ((1 / 5) : ℂ) * ζ ^ 12 - ((6 / 5) : ℂ) * ζ ^ 20 + ((1 / 5) : ℂ) * ζ ^ 24)
private theorem row16_generatorB_mul_eigenbasis_7_2 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        7 2 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        7 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((7 / 5) : ℂ) + ((3 / 5) : ℂ) * ζ ^ 2 - ((7 / 5) : ℂ) * ζ ^ 4 - ((3 / 5) : ℂ) * ζ ^ 6 + ((7 / 5) : ℂ) * ζ ^ 8 - ((8 / 5) : ℂ) * ζ ^ 10 + ζ ^ 12 - ((3 / 5) : ℂ) * ζ ^ 14 - ((12 / 5) : ℂ) * ζ ^ 16 - ((3 / 5) : ℂ) * ζ ^ 18 + ((1 / 5) : ℂ) * ζ ^ 20 - ((8 / 5) : ℂ) * ζ ^ 22 - ((7 / 5) : ℂ) * ζ ^ 24 + (2 : ℂ) * ζ ^ 26)
private theorem row16_generatorB_mul_eigenbasis_7_3 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        7 3 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        7 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((6 / 5) : ℂ) + ζ ^ 2 + ((6 / 5) : ℂ) * ζ ^ 4 - ((12 / 5) : ℂ) * ζ ^ 6 + (2 : ℂ) * ζ ^ 10 + ((7 / 5) : ℂ) * ζ ^ 12 - ((6 / 5) : ℂ) * ζ ^ 14 - ((13 / 5) : ℂ) * ζ ^ 16 + ((3 / 5) : ℂ) * ζ ^ 18 + ((3 / 5) : ℂ) * ζ ^ 20 - ζ ^ 22 - ((6 / 5) : ℂ) * ζ ^ 24 + ((8 / 5) : ℂ) * ζ ^ 26)
private theorem row16_generatorB_mul_eigenbasis_7_4 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        7 4 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        7 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((2 / 5) : ℂ) + ((2 / 5) : ℂ) * ζ ^ 4 - ((57 / 55) : ℂ) * ζ ^ 8 + ((9 / 55) : ℂ) * ζ ^ 12 + ((27 / 55) : ℂ) * ζ ^ 16 + ((4 / 11) : ℂ) * ζ ^ 20 + ((36 / 55) : ℂ) * ζ ^ 24)
private theorem row16_generatorB_mul_eigenbasis_7_5 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        7 5 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        7 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((139 / 55) : ℂ) * ζ ^ 8 - ((49 / 55) : ℂ) * ζ ^ 12 - ((26 / 55) : ℂ) * ζ ^ 16 - ((23 / 11) : ℂ) * ζ ^ 20 - ((4 / 11) : ℂ) * ζ ^ 24 - ζ ^ 28)
private theorem row16_generatorB_mul_eigenbasis_7_6 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        7 6 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        7 6 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((7 / 5) : ℂ) - ((3 / 5) : ℂ) * ζ ^ 2 - ((7 / 5) : ℂ) * ζ ^ 4 + ((3 / 5) : ℂ) * ζ ^ 6 + ((7 / 5) : ℂ) * ζ ^ 8 + ((8 / 5) : ℂ) * ζ ^ 10 + ζ ^ 12 + ((3 / 5) : ℂ) * ζ ^ 14 - ((12 / 5) : ℂ) * ζ ^ 16 + ((3 / 5) : ℂ) * ζ ^ 18 + ((1 / 5) : ℂ) * ζ ^ 20 + ((8 / 5) : ℂ) * ζ ^ 22 - ((7 / 5) : ℂ) * ζ ^ 24 - (2 : ℂ) * ζ ^ 26)
private theorem row16_generatorB_mul_eigenbasis_7_7 :
    (alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis)
        7 7 =
      (alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal)
        7 7 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row16_matrixB,
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16GeneratorBDiagonal,
      alternatingSixAmbientRow16GeneratorBEigenvalue,
      alternatingSixAmbientRow16EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((6 / 5) : ℂ) - ζ ^ 2 + ((6 / 5) : ℂ) * ζ ^ 4 + ((12 / 5) : ℂ) * ζ ^ 6 - (2 : ℂ) * ζ ^ 10 + ((7 / 5) : ℂ) * ζ ^ 12 + ((6 / 5) : ℂ) * ζ ^ 14 - ((13 / 5) : ℂ) * ζ ^ 16 - ((3 / 5) : ℂ) * ζ ^ 18 + ((3 / 5) : ℂ) * ζ ^ 20 + ζ ^ 22 - ((6 / 5) : ℂ) * ζ ^ 24 - ((8 / 5) : ℂ) * ζ ^ 26 - ζ ^ 30 + ζ ^ 34 - ζ ^ 38 - ζ ^ 50 + ζ ^ 54 - ζ ^ 58)
/-- The checked row 16 basis diagonalizes the second
generator. -/
theorem alternatingSixAmbientRow16GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixAmbientRow16Eigenbasis =
      alternatingSixAmbientRow16Eigenbasis *
        alternatingSixAmbientRow16GeneratorBDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row16_generatorB_mul_eigenbasis_0_0
  · exact row16_generatorB_mul_eigenbasis_0_1
  · exact row16_generatorB_mul_eigenbasis_0_2
  · exact row16_generatorB_mul_eigenbasis_0_3
  · exact row16_generatorB_mul_eigenbasis_0_4
  · exact row16_generatorB_mul_eigenbasis_0_5
  · exact row16_generatorB_mul_eigenbasis_0_6
  · exact row16_generatorB_mul_eigenbasis_0_7
  · exact row16_generatorB_mul_eigenbasis_1_0
  · exact row16_generatorB_mul_eigenbasis_1_1
  · exact row16_generatorB_mul_eigenbasis_1_2
  · exact row16_generatorB_mul_eigenbasis_1_3
  · exact row16_generatorB_mul_eigenbasis_1_4
  · exact row16_generatorB_mul_eigenbasis_1_5
  · exact row16_generatorB_mul_eigenbasis_1_6
  · exact row16_generatorB_mul_eigenbasis_1_7
  · exact row16_generatorB_mul_eigenbasis_2_0
  · exact row16_generatorB_mul_eigenbasis_2_1
  · exact row16_generatorB_mul_eigenbasis_2_2
  · exact row16_generatorB_mul_eigenbasis_2_3
  · exact row16_generatorB_mul_eigenbasis_2_4
  · exact row16_generatorB_mul_eigenbasis_2_5
  · exact row16_generatorB_mul_eigenbasis_2_6
  · exact row16_generatorB_mul_eigenbasis_2_7
  · exact row16_generatorB_mul_eigenbasis_3_0
  · exact row16_generatorB_mul_eigenbasis_3_1
  · exact row16_generatorB_mul_eigenbasis_3_2
  · exact row16_generatorB_mul_eigenbasis_3_3
  · exact row16_generatorB_mul_eigenbasis_3_4
  · exact row16_generatorB_mul_eigenbasis_3_5
  · exact row16_generatorB_mul_eigenbasis_3_6
  · exact row16_generatorB_mul_eigenbasis_3_7
  · exact row16_generatorB_mul_eigenbasis_4_0
  · exact row16_generatorB_mul_eigenbasis_4_1
  · exact row16_generatorB_mul_eigenbasis_4_2
  · exact row16_generatorB_mul_eigenbasis_4_3
  · exact row16_generatorB_mul_eigenbasis_4_4
  · exact row16_generatorB_mul_eigenbasis_4_5
  · exact row16_generatorB_mul_eigenbasis_4_6
  · exact row16_generatorB_mul_eigenbasis_4_7
  · exact row16_generatorB_mul_eigenbasis_5_0
  · exact row16_generatorB_mul_eigenbasis_5_1
  · exact row16_generatorB_mul_eigenbasis_5_2
  · exact row16_generatorB_mul_eigenbasis_5_3
  · exact row16_generatorB_mul_eigenbasis_5_4
  · exact row16_generatorB_mul_eigenbasis_5_5
  · exact row16_generatorB_mul_eigenbasis_5_6
  · exact row16_generatorB_mul_eigenbasis_5_7
  · exact row16_generatorB_mul_eigenbasis_6_0
  · exact row16_generatorB_mul_eigenbasis_6_1
  · exact row16_generatorB_mul_eigenbasis_6_2
  · exact row16_generatorB_mul_eigenbasis_6_3
  · exact row16_generatorB_mul_eigenbasis_6_4
  · exact row16_generatorB_mul_eigenbasis_6_5
  · exact row16_generatorB_mul_eigenbasis_6_6
  · exact row16_generatorB_mul_eigenbasis_6_7
  · exact row16_generatorB_mul_eigenbasis_7_0
  · exact row16_generatorB_mul_eigenbasis_7_1
  · exact row16_generatorB_mul_eigenbasis_7_2
  · exact row16_generatorB_mul_eigenbasis_7_3
  · exact row16_generatorB_mul_eigenbasis_7_4
  · exact row16_generatorB_mul_eigenbasis_7_5
  · exact row16_generatorB_mul_eigenbasis_7_6
  · exact row16_generatorB_mul_eigenbasis_7_7


private theorem row16_transformedGeneratorA_0_0 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        0 0 =
      alternatingSixAmbientRow16TransformedGeneratorA
        0 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((109 / 100) : ℂ) + ((109 / 100) : ℂ) * ζ ^ 4 + ((22 / 5) : ℂ) * ζ ^ 8 + ((91 / 50) : ℂ) * ζ ^ 12 - ((203 / 100) : ℂ) * ζ ^ 16 - ((107 / 100) : ℂ) * ζ ^ 20 - ((113 / 20) : ℂ) * ζ ^ 24 + ((33 / 10) : ℂ) * ζ ^ 28 + ((77 / 100) : ℂ) * ζ ^ 32 + ((2 / 25) : ℂ) * ζ ^ 36 + ((47 / 50) : ℂ) * ζ ^ 40 - ((2 / 25) : ℂ) * ζ ^ 44 + ((241 / 100) : ℂ) * ζ ^ 48 + ((3 / 4) : ℂ) * ζ ^ 52)
private theorem row16_transformedGeneratorA_0_1 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        0 1 =
      alternatingSixAmbientRow16TransformedGeneratorA
        0 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((1 / 25) : ℂ) + ((1 / 25) : ℂ) * ζ ^ 4 + ((377 / 100) : ℂ) * ζ ^ 8 - ((13 / 25) : ℂ) * ζ ^ 12 - ((144 / 25) : ℂ) * ζ ^ 16 - ((141 / 100) : ℂ) * ζ ^ 20 - ((51 / 20) : ℂ) * ζ ^ 24 + ((63 / 100) : ℂ) * ζ ^ 28 + ((199 / 25) : ℂ) * ζ ^ 32 + ((101 / 50) : ℂ) * ζ ^ 36 - ((3 / 100) : ℂ) * ζ ^ 40 - ((33 / 100) : ℂ) * ζ ^ 44 - ((46 / 25) : ℂ) * ζ ^ 48 - ((53 / 100) : ℂ) * ζ ^ 52)
private theorem row16_transformedGeneratorA_0_2 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        0 2 =
      alternatingSixAmbientRow16TransformedGeneratorA
        0 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((29 / 50) : ℂ) + ((861 / 100) : ℂ) * ζ ^ 2 - ((29 / 50) : ℂ) * ζ ^ 4 - ((97 / 20) : ℂ) * ζ ^ 6 + ((108 / 25) : ℂ) * ζ ^ 8 - ((273 / 50) : ℂ) * ζ ^ 10 - ((1017 / 100) : ℂ) * ζ ^ 12 - ((277 / 100) : ℂ) * ζ ^ 14 + ((617 / 100) : ℂ) * ζ ^ 16 - ((162 / 25) : ℂ) * ζ ^ 18 - ((29 / 20) : ℂ) * ζ ^ 20 + ((13 / 5) : ℂ) * ζ ^ 22 - ((487 / 100) : ℂ) * ζ ^ 24 + ((392 / 25) : ℂ) * ζ ^ 26 + ((86 / 25) : ℂ) * ζ ^ 28 - ((51 / 100) : ℂ) * ζ ^ 30 + ((1123 / 100) : ℂ) * ζ ^ 32 + ((137 / 50) : ℂ) * ζ ^ 34 - ((289 / 50) : ℂ) * ζ ^ 36 - ((191 / 50) : ℂ) * ζ ^ 38 + ((73 / 20) : ℂ) * ζ ^ 40 - ((613 / 100) : ℂ) * ζ ^ 42 - ((479 / 100) : ℂ) * ζ ^ 44 + ((87 / 100) : ℂ) * ζ ^ 46 - ((807 / 100) : ℂ) * ζ ^ 48 - ((33 / 25) : ℂ) * ζ ^ 50 + ((337 / 100) : ℂ) * ζ ^ 52 - ((53 / 50) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_0_3 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        0 3 =
      alternatingSixAmbientRow16TransformedGeneratorA
        0 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((357 / 50) : ℂ) - ((119 / 25) : ℂ) * ζ ^ 2 - ((357 / 50) : ℂ) * ζ ^ 4 + ((119 / 100) : ℂ) * ζ ^ 6 + ((343 / 100) : ℂ) * ζ ^ 8 + ((321 / 50) : ℂ) * ζ ^ 10 + ((17 / 50) : ℂ) * ζ ^ 12 + ((297 / 100) : ℂ) * ζ ^ 14 - ((44 / 25) : ℂ) * ζ ^ 16 - ((1 / 4) : ℂ) * ζ ^ 18 + ((63 / 50) : ℂ) * ζ ^ 20 + ((11 / 25) : ℂ) * ζ ^ 22 + ((11 / 20) : ℂ) * ζ ^ 24 - ((1441 / 100) : ℂ) * ζ ^ 26 - ((77 / 20) : ℂ) * ζ ^ 28 - ((39 / 5) : ℂ) * ζ ^ 30 + ((127 / 20) : ℂ) * ζ ^ 32 + ((202 / 25) : ℂ) * ζ ^ 34 - ((131 / 50) : ℂ) * ζ ^ 36 + ((191 / 50) : ℂ) * ζ ^ 38 - ((27 / 25) : ℂ) * ζ ^ 40 + ((178 / 25) : ℂ) * ζ ^ 42 + ((23 / 4) : ℂ) * ζ ^ 44 - ((109 / 100) : ℂ) * ζ ^ 46 - ((5 / 2) : ℂ) * ζ ^ 48 - ((349 / 100) : ℂ) * ζ ^ 50 + ((17 / 25) : ℂ) * ζ ^ 52 - ((167 / 100) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_0_4 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        0 4 =
      alternatingSixAmbientRow16TransformedGeneratorA
        0 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((749 / 1100) : ℂ) + ((749 / 1100) : ℂ) * ζ ^ 4 + ((999 / 275) : ℂ) * ζ ^ 8 + ((138 / 275) : ℂ) * ζ ^ 12 - ((3589 / 1100) : ℂ) * ζ ^ 16 - ((2749 / 1100) : ℂ) * ζ ^ 20 - ((4219 / 1100) : ℂ) * ζ ^ 24 + ((2333 / 550) : ℂ) * ζ ^ 28 + ((291 / 220) : ℂ) * ζ ^ 32 + ((1107 / 275) : ℂ) * ζ ^ 36 - ((493 / 275) : ℂ) * ζ ^ 40 - ((1429 / 550) : ℂ) * ζ ^ 44 + ((111 / 1100) : ℂ) * ζ ^ 48 - ((1139 / 1100) : ℂ) * ζ ^ 52)
private theorem row16_transformedGeneratorA_0_5 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        0 5 =
      alternatingSixAmbientRow16TransformedGeneratorA
        0 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((516 / 275) : ℂ) + ((516 / 275) : ℂ) * ζ ^ 4 + ((6131 / 1100) : ℂ) * ζ ^ 8 - ((383 / 275) : ℂ) * ζ ^ 12 - ((181 / 55) : ℂ) * ζ ^ 16 - ((889 / 1100) : ℂ) * ζ ^ 20 - ((4033 / 1100) : ℂ) * ζ ^ 24 - ((1051 / 1100) : ℂ) * ζ ^ 28 + ((2429 / 550) : ℂ) * ζ ^ 32 + ((273 / 550) : ℂ) * ζ ^ 36 + ((241 / 1100) : ℂ) * ζ ^ 40 - ((149 / 100) : ℂ) * ζ ^ 44 + ((262 / 275) : ℂ) * ζ ^ 48 - ((329 / 1100) : ℂ) * ζ ^ 52)
private theorem row16_transformedGeneratorA_0_6 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        0 6 =
      alternatingSixAmbientRow16TransformedGeneratorA
        0 6 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((29 / 50) : ℂ) - ((861 / 100) : ℂ) * ζ ^ 2 - ((29 / 50) : ℂ) * ζ ^ 4 + ((97 / 20) : ℂ) * ζ ^ 6 + ((108 / 25) : ℂ) * ζ ^ 8 + ((273 / 50) : ℂ) * ζ ^ 10 - ((1017 / 100) : ℂ) * ζ ^ 12 + ((277 / 100) : ℂ) * ζ ^ 14 + ((617 / 100) : ℂ) * ζ ^ 16 + ((162 / 25) : ℂ) * ζ ^ 18 - ((29 / 20) : ℂ) * ζ ^ 20 - ((13 / 5) : ℂ) * ζ ^ 22 - ((487 / 100) : ℂ) * ζ ^ 24 - ((392 / 25) : ℂ) * ζ ^ 26 + ((86 / 25) : ℂ) * ζ ^ 28 + ((51 / 100) : ℂ) * ζ ^ 30 + ((1123 / 100) : ℂ) * ζ ^ 32 - ((137 / 50) : ℂ) * ζ ^ 34 - ((289 / 50) : ℂ) * ζ ^ 36 + ((191 / 50) : ℂ) * ζ ^ 38 + ((73 / 20) : ℂ) * ζ ^ 40 + ((613 / 100) : ℂ) * ζ ^ 42 - ((479 / 100) : ℂ) * ζ ^ 44 - ((87 / 100) : ℂ) * ζ ^ 46 - ((807 / 100) : ℂ) * ζ ^ 48 + ((33 / 25) : ℂ) * ζ ^ 50 + ((337 / 100) : ℂ) * ζ ^ 52 + ((53 / 50) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_0_7 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        0 7 =
      alternatingSixAmbientRow16TransformedGeneratorA
        0 7 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((357 / 50) : ℂ) + ((119 / 25) : ℂ) * ζ ^ 2 - ((357 / 50) : ℂ) * ζ ^ 4 - ((119 / 100) : ℂ) * ζ ^ 6 + ((343 / 100) : ℂ) * ζ ^ 8 - ((321 / 50) : ℂ) * ζ ^ 10 + ((17 / 50) : ℂ) * ζ ^ 12 - ((297 / 100) : ℂ) * ζ ^ 14 - ((44 / 25) : ℂ) * ζ ^ 16 + ((1 / 4) : ℂ) * ζ ^ 18 + ((63 / 50) : ℂ) * ζ ^ 20 - ((11 / 25) : ℂ) * ζ ^ 22 + ((11 / 20) : ℂ) * ζ ^ 24 + ((1441 / 100) : ℂ) * ζ ^ 26 - ((77 / 20) : ℂ) * ζ ^ 28 + ((39 / 5) : ℂ) * ζ ^ 30 + ((127 / 20) : ℂ) * ζ ^ 32 - ((202 / 25) : ℂ) * ζ ^ 34 - ((131 / 50) : ℂ) * ζ ^ 36 - ((191 / 50) : ℂ) * ζ ^ 38 - ((27 / 25) : ℂ) * ζ ^ 40 - ((178 / 25) : ℂ) * ζ ^ 42 + ((23 / 4) : ℂ) * ζ ^ 44 + ((109 / 100) : ℂ) * ζ ^ 46 - ((5 / 2) : ℂ) * ζ ^ 48 + ((349 / 100) : ℂ) * ζ ^ 50 + ((17 / 25) : ℂ) * ζ ^ 52 + ((167 / 100) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_1_0 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        1 0 =
      alternatingSixAmbientRow16TransformedGeneratorA
        1 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((67 / 10) : ℂ) + ((67 / 10) : ℂ) * ζ ^ 4 + ((19 / 25) : ℂ) * ζ ^ 8 + ((223 / 100) : ℂ) * ζ ^ 12 - ((469 / 100) : ℂ) * ζ ^ 16 + ((17 / 25) : ℂ) * ζ ^ 20 - ((7 / 10) : ℂ) * ζ ^ 24 - ((53 / 50) : ℂ) * ζ ^ 28 + ((43 / 25) : ℂ) * ζ ^ 32 + ((38 / 25) : ℂ) * ζ ^ 36 - ((61 / 100) : ℂ) * ζ ^ 40 - ((5 / 4) : ℂ) * ζ ^ 44 + ((21 / 20) : ℂ) * ζ ^ 48 - ((21 / 25) : ℂ) * ζ ^ 52)
private theorem row16_transformedGeneratorA_1_1 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        1 1 =
      alternatingSixAmbientRow16TransformedGeneratorA
        1 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((189 / 50) : ℂ) + ((189 / 50) : ℂ) * ζ ^ 4 + ((239 / 100) : ℂ) * ζ ^ 8 - ((61 / 25) : ℂ) * ζ ^ 12 + ((9 / 50) : ℂ) * ζ ^ 16 - ((38 / 25) : ℂ) * ζ ^ 20 - ((39 / 10) : ℂ) * ζ ^ 24 + ((113 / 50) : ℂ) * ζ ^ 28 + ((111 / 50) : ℂ) * ζ ^ 32 - ((51 / 100) : ℂ) * ζ ^ 36 + ((7 / 50) : ℂ) * ζ ^ 40 - ((41 / 100) : ℂ) * ζ ^ 44 - ((69 / 50) : ℂ) * ζ ^ 48 + ((39 / 100) : ℂ) * ζ ^ 52)
private theorem row16_transformedGeneratorA_1_2 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        1 2 =
      alternatingSixAmbientRow16TransformedGeneratorA
        1 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((671 / 100) : ℂ) - ((419 / 100) : ℂ) * ζ ^ 2 - ((671 / 100) : ℂ) * ζ ^ 4 + ((237 / 100) : ℂ) * ζ ^ 6 - ((873 / 100) : ℂ) * ζ ^ 8 + ((327 / 100) : ℂ) * ζ ^ 10 + ((467 / 100) : ℂ) * ζ ^ 12 - ((191 / 50) : ℂ) * ζ ^ 14 + ((37 / 5) : ℂ) * ζ ^ 16 - ((24 / 25) : ℂ) * ζ ^ 18 - ((333 / 50) : ℂ) * ζ ^ 20 + ((204 / 25) : ℂ) * ζ ^ 22 + ((313 / 100) : ℂ) * ζ ^ 24 - ((203 / 50) : ℂ) * ζ ^ 26 + ((1101 / 100) : ℂ) * ζ ^ 28 + ((9 / 100) : ℂ) * ζ ^ 30 - ((1007 / 100) : ℂ) * ζ ^ 32 + ((41 / 100) : ℂ) * ζ ^ 34 - ((51 / 25) : ℂ) * ζ ^ 36 - ((7 / 50) : ℂ) * ζ ^ 38 + ((333 / 100) : ℂ) * ζ ^ 40 - ((407 / 100) : ℂ) * ζ ^ 42 - ((19 / 10) : ℂ) * ζ ^ 44 + ((114 / 25) : ℂ) * ζ ^ 46 - ((81 / 20) : ℂ) * ζ ^ 48 - ((11 / 5) : ℂ) * ζ ^ 50 + ((327 / 100) : ℂ) * ζ ^ 52 + ((31 / 20) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_1_3 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        1 3 =
      alternatingSixAmbientRow16TransformedGeneratorA
        1 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((969 / 100) : ℂ) - ((52 / 25) : ℂ) * ζ ^ 2 + ((969 / 100) : ℂ) * ζ ^ 4 + ((33 / 20) : ℂ) * ζ ^ 6 + ((501 / 100) : ℂ) * ζ ^ 8 - ((17 / 100) : ℂ) * ζ ^ 10 - ((93 / 50) : ℂ) * ζ ^ 12 - ((1 / 25) : ℂ) * ζ ^ 14 - ((401 / 100) : ℂ) * ζ ^ 16 + ((189 / 25) : ℂ) * ζ ^ 18 + ((183 / 50) : ℂ) * ζ ^ 20 - ((158 / 25) : ℂ) * ζ ^ 22 - ((302 / 25) : ℂ) * ζ ^ 24 - ((86 / 25) : ℂ) * ζ ^ 26 + ((703 / 100) : ℂ) * ζ ^ 28 + ((27 / 20) : ℂ) * ζ ^ 30 + ((103 / 50) : ℂ) * ζ ^ 32 - ((21 / 100) : ℂ) * ζ ^ 34 - ((6 / 25) : ℂ) * ζ ^ 36 - ((59 / 50) : ℂ) * ζ ^ 38 - ((87 / 100) : ℂ) * ζ ^ 40 + (2 : ℂ) * ζ ^ 42 + ((297 / 100) : ℂ) * ζ ^ 44 - ((159 / 100) : ℂ) * ζ ^ 48 - ((161 / 100) : ℂ) * ζ ^ 50 - ((17 / 50) : ℂ) * ζ ^ 52 + ((31 / 50) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_1_4 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        1 4 =
      alternatingSixAmbientRow16TransformedGeneratorA
        1 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((826 / 275) : ℂ) + ((826 / 275) : ℂ) * ζ ^ 4 + ((207 / 550) : ℂ) * ζ ^ 8 + ((2089 / 1100) : ℂ) * ζ ^ 12 - ((3349 / 1100) : ℂ) * ζ ^ 16 + ((58 / 55) : ℂ) * ζ ^ 20 - ((38 / 275) : ℂ) * ζ ^ 24 - ((388 / 275) : ℂ) * ζ ^ 28 + ((17 / 110) : ℂ) * ζ ^ 32 + ((1 / 55) : ℂ) * ζ ^ 36 + ((193 / 1100) : ℂ) * ζ ^ 40 - ((1949 / 1100) : ℂ) * ζ ^ 44 + ((703 / 1100) : ℂ) * ζ ^ 48 - ((23 / 550) : ℂ) * ζ ^ 52)
private theorem row16_transformedGeneratorA_1_5 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        1 5 =
      alternatingSixAmbientRow16TransformedGeneratorA
        1 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((923 / 275) : ℂ) + ((923 / 275) : ℂ) * ζ ^ 4 + ((729 / 220) : ℂ) * ζ ^ 8 - ((983 / 275) : ℂ) * ζ ^ 12 + ((71 / 275) : ℂ) * ζ ^ 16 - ((414 / 275) : ℂ) * ζ ^ 20 - ((107 / 50) : ℂ) * ζ ^ 24 - ((207 / 275) : ℂ) * ζ ^ 28 + ((471 / 550) : ℂ) * ζ ^ 32 + ((1017 / 1100) : ℂ) * ζ ^ 36 + ((138 / 275) : ℂ) * ζ ^ 40 - ((1139 / 1100) : ℂ) * ζ ^ 44 + ((312 / 275) : ℂ) * ζ ^ 48 - ((29 / 220) : ℂ) * ζ ^ 52)
private theorem row16_transformedGeneratorA_1_6 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        1 6 =
      alternatingSixAmbientRow16TransformedGeneratorA
        1 6 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((671 / 100) : ℂ) + ((419 / 100) : ℂ) * ζ ^ 2 - ((671 / 100) : ℂ) * ζ ^ 4 - ((237 / 100) : ℂ) * ζ ^ 6 - ((873 / 100) : ℂ) * ζ ^ 8 - ((327 / 100) : ℂ) * ζ ^ 10 + ((467 / 100) : ℂ) * ζ ^ 12 + ((191 / 50) : ℂ) * ζ ^ 14 + ((37 / 5) : ℂ) * ζ ^ 16 + ((24 / 25) : ℂ) * ζ ^ 18 - ((333 / 50) : ℂ) * ζ ^ 20 - ((204 / 25) : ℂ) * ζ ^ 22 + ((313 / 100) : ℂ) * ζ ^ 24 + ((203 / 50) : ℂ) * ζ ^ 26 + ((1101 / 100) : ℂ) * ζ ^ 28 - ((9 / 100) : ℂ) * ζ ^ 30 - ((1007 / 100) : ℂ) * ζ ^ 32 - ((41 / 100) : ℂ) * ζ ^ 34 - ((51 / 25) : ℂ) * ζ ^ 36 + ((7 / 50) : ℂ) * ζ ^ 38 + ((333 / 100) : ℂ) * ζ ^ 40 + ((407 / 100) : ℂ) * ζ ^ 42 - ((19 / 10) : ℂ) * ζ ^ 44 - ((114 / 25) : ℂ) * ζ ^ 46 - ((81 / 20) : ℂ) * ζ ^ 48 + ((11 / 5) : ℂ) * ζ ^ 50 + ((327 / 100) : ℂ) * ζ ^ 52 - ((31 / 20) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_1_7 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        1 7 =
      alternatingSixAmbientRow16TransformedGeneratorA
        1 7 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((969 / 100) : ℂ) + ((52 / 25) : ℂ) * ζ ^ 2 + ((969 / 100) : ℂ) * ζ ^ 4 - ((33 / 20) : ℂ) * ζ ^ 6 + ((501 / 100) : ℂ) * ζ ^ 8 + ((17 / 100) : ℂ) * ζ ^ 10 - ((93 / 50) : ℂ) * ζ ^ 12 + ((1 / 25) : ℂ) * ζ ^ 14 - ((401 / 100) : ℂ) * ζ ^ 16 - ((189 / 25) : ℂ) * ζ ^ 18 + ((183 / 50) : ℂ) * ζ ^ 20 + ((158 / 25) : ℂ) * ζ ^ 22 - ((302 / 25) : ℂ) * ζ ^ 24 + ((86 / 25) : ℂ) * ζ ^ 26 + ((703 / 100) : ℂ) * ζ ^ 28 - ((27 / 20) : ℂ) * ζ ^ 30 + ((103 / 50) : ℂ) * ζ ^ 32 + ((21 / 100) : ℂ) * ζ ^ 34 - ((6 / 25) : ℂ) * ζ ^ 36 + ((59 / 50) : ℂ) * ζ ^ 38 - ((87 / 100) : ℂ) * ζ ^ 40 - (2 : ℂ) * ζ ^ 42 + ((297 / 100) : ℂ) * ζ ^ 44 - ((159 / 100) : ℂ) * ζ ^ 48 + ((161 / 100) : ℂ) * ζ ^ 50 - ((17 / 50) : ℂ) * ζ ^ 52 - ((31 / 50) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_2_0 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        2 0 =
      alternatingSixAmbientRow16TransformedGeneratorA
        2 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((1 / 100) : ℂ) - ((41 / 100) : ℂ) * ζ ^ 2 - ((1 / 100) : ℂ) * ζ ^ 4 + ((58 / 25) : ℂ) * ζ ^ 6 - ((3 / 5) : ℂ) * ζ ^ 8 - ((101 / 100) : ℂ) * ζ ^ 10 - ((119 / 50) : ℂ) * ζ ^ 12 + ((14 / 25) : ℂ) * ζ ^ 14 + ((187 / 100) : ℂ) * ζ ^ 16 - ((163 / 100) : ℂ) * ζ ^ 18 - ((71 / 50) : ℂ) * ζ ^ 20 + ((197 / 100) : ℂ) * ζ ^ 22 + ((43 / 10) : ℂ) * ζ ^ 24 - ((29 / 100) : ℂ) * ζ ^ 26 - ((9 / 2) : ℂ) * ζ ^ 28 - ((33 / 50) : ℂ) * ζ ^ 30 + ((97 / 100) : ℂ) * ζ ^ 32 + ((41 / 100) : ℂ) * ζ ^ 34 - ((67 / 100) : ℂ) * ζ ^ 36 - ((67 / 100) : ℂ) * ζ ^ 38 + ((119 / 100) : ℂ) * ζ ^ 40 - ((3 / 20) : ℂ) * ζ ^ 42 - ((89 / 50) : ℂ) * ζ ^ 44 + ((99 / 100) : ℂ) * ζ ^ 46 + ((53 / 50) : ℂ) * ζ ^ 48 + ((2 / 25) : ℂ) * ζ ^ 50 - ((17 / 20) : ℂ) * ζ ^ 52 + ((3 / 25) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_2_1 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        2 1 =
      alternatingSixAmbientRow16TransformedGeneratorA
        2 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((49 / 100) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((49 / 100) : ℂ) * ζ ^ 4 + ((7 / 5) : ℂ) * ζ ^ 6 - ((123 / 100) : ℂ) * ζ ^ 8 - ((7 / 5) : ℂ) * ζ ^ 10 - ((13 / 25) : ℂ) * ζ ^ 12 - ((3 / 5) : ℂ) * ζ ^ 14 + ((269 / 100) : ℂ) * ζ ^ 16 + ((1 / 5) : ℂ) * ζ ^ 18 + ((39 / 100) : ℂ) * ζ ^ 20 + ((9 / 20) : ℂ) * ζ ^ 24 + ((6 / 5) : ℂ) * ζ ^ 26 - ((11 / 50) : ℂ) * ζ ^ 28 + ((3 / 4) : ℂ) * ζ ^ 30 - ((249 / 100) : ℂ) * ζ ^ 32 - ((1 / 4) : ℂ) * ζ ^ 34 - ((47 / 25) : ℂ) * ζ ^ 36 + ((9 / 10) : ℂ) * ζ ^ 38 + ((47 / 100) : ℂ) * ζ ^ 40 - ((21 / 20) : ℂ) * ζ ^ 42 + ((27 / 100) : ℂ) * ζ ^ 44 + ((9 / 10) : ℂ) * ζ ^ 46 - ((19 / 100) : ℂ) * ζ ^ 48 + ((3 / 20) : ℂ) * ζ ^ 50 + ((18 / 25) : ℂ) * ζ ^ 52 - ((9 / 20) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_2_2 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        2 2 =
      alternatingSixAmbientRow16TransformedGeneratorA
        2 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((27 / 100) : ℂ) - ((399 / 100) : ℂ) * ζ ^ 2 + ((1 / 25) : ℂ) * ζ ^ 4 + ((13 / 20) : ℂ) * ζ ^ 6 - ((499 / 100) : ℂ) * ζ ^ 8 + ((403 / 100) : ℂ) * ζ ^ 10 + ((15 / 2) : ℂ) * ζ ^ 12 + ((147 / 100) : ℂ) * ζ ^ 14 - ((26 / 25) : ℂ) * ζ ^ 16 + ((76 / 25) : ℂ) * ζ ^ 18 + ((7 / 4) : ℂ) * ζ ^ 20 - ((163 / 100) : ℂ) * ζ ^ 22 + ((69 / 25) : ℂ) * ζ ^ 24 - ((329 / 50) : ℂ) * ζ ^ 26 + ((57 / 20) : ℂ) * ζ ^ 28 - ((81 / 50) : ℂ) * ζ ^ 30 - ((869 / 100) : ℂ) * ζ ^ 32 + ((14 / 25) : ℂ) * ζ ^ 34 - ((78 / 25) : ℂ) * ζ ^ 36 + ((67 / 20) : ℂ) * ζ ^ 38 + ((13 / 4) : ℂ) * ζ ^ 40 - ((29 / 50) : ℂ) * ζ ^ 42 + ((53 / 100) : ℂ) * ζ ^ 44 + ((91 / 25) : ℂ) * ζ ^ 46 + ((57 / 100) : ℂ) * ζ ^ 48 - ((393 / 100) : ℂ) * ζ ^ 50 + ((16 / 25) : ℂ) * ζ ^ 52 + ((17 / 20) : ℂ) * ζ ^ 54 + ((37 / 50) : ℂ) * ζ ^ 56)
private theorem row16_transformedGeneratorA_2_3 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        2 3 =
      alternatingSixAmbientRow16TransformedGeneratorA
        2 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((243 / 50) : ℂ) + ((163 / 100) : ℂ) * ζ ^ 2 + ((473 / 100) : ℂ) * ζ ^ 4 + ((73 / 50) : ℂ) * ζ ^ 6 + ((337 / 100) : ℂ) * ζ ^ 8 - ((103 / 25) : ℂ) * ζ ^ 10 - ((429 / 100) : ℂ) * ζ ^ 12 - ((22 / 25) : ℂ) * ζ ^ 14 + ((3 / 100) : ℂ) * ζ ^ 16 + ((41 / 25) : ℂ) * ζ ^ 18 - ((71 / 100) : ℂ) * ζ ^ 20 - ((47 / 20) : ℂ) * ζ ^ 22 - ((37 / 25) : ℂ) * ζ ^ 24 + ((293 / 50) : ℂ) * ζ ^ 26 - ((227 / 100) : ℂ) * ζ ^ 28 + ((47 / 5) : ℂ) * ζ ^ 30 + ((11 / 25) : ℂ) * ζ ^ 32 - ((841 / 100) : ℂ) * ζ ^ 34 + ((13 / 10) : ℂ) * ζ ^ 36 - ((3 / 20) : ℂ) * ζ ^ 38 + ((43 / 100) : ℂ) * ζ ^ 40 - ((59 / 20) : ℂ) * ζ ^ 42 - ((397 / 100) : ℂ) * ζ ^ 44 + ((467 / 100) : ℂ) * ζ ^ 46 + ((73 / 50) : ℂ) * ζ ^ 48 - ((81 / 50) : ℂ) * ζ ^ 50 - ((11 / 100) : ℂ) * ζ ^ 52 + ((67 / 25) : ℂ) * ζ ^ 54 - ((42 / 25) : ℂ) * ζ ^ 56)
private theorem row16_transformedGeneratorA_2_4 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        2 4 =
      alternatingSixAmbientRow16TransformedGeneratorA
        2 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((721 / 1100) : ℂ) + ((207 / 1100) : ℂ) * ζ ^ 2 - ((721 / 1100) : ℂ) * ζ ^ 4 + ((114 / 275) : ℂ) * ζ ^ 6 - ((357 / 550) : ℂ) * ζ ^ 8 - ((601 / 1100) : ℂ) * ζ ^ 10 - ((217 / 275) : ℂ) * ζ ^ 12 - ((13 / 55) : ℂ) * ζ ^ 14 + ((1761 / 1100) : ℂ) * ζ ^ 16 - ((233 / 1100) : ℂ) * ζ ^ 18 - ((227 / 550) : ℂ) * ζ ^ 20 + ((267 / 1100) : ℂ) * ζ ^ 22 + ((1563 / 550) : ℂ) * ζ ^ 24 - ((47 / 220) : ℂ) * ζ ^ 26 - ((1497 / 550) : ℂ) * ζ ^ 28 - ((104 / 275) : ℂ) * ζ ^ 30 + ((71 / 220) : ℂ) * ζ ^ 32 + ((489 / 1100) : ℂ) * ζ ^ 34 - ((1447 / 1100) : ℂ) * ζ ^ 36 - ((3 / 220) : ℂ) * ζ ^ 38 + ((133 / 100) : ℂ) * ζ ^ 40 + ((9 / 20) : ℂ) * ζ ^ 42 - ((149 / 550) : ℂ) * ζ ^ 44 - ((757 / 1100) : ℂ) * ζ ^ 46 + ((159 / 275) : ℂ) * ζ ^ 48 + ((4 / 25) : ℂ) * ζ ^ 50 + ((141 / 1100) : ℂ) * ζ ^ 52 - ((39 / 275) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_2_5 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        2 5 =
      alternatingSixAmbientRow16TransformedGeneratorA
        2 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((1051 / 1100) : ℂ) - ((93 / 275) : ℂ) * ζ ^ 2 - ((1051 / 1100) : ℂ) * ζ ^ 4 + ((827 / 550) : ℂ) * ζ ^ 6 - ((1569 / 1100) : ℂ) * ζ ^ 8 - ((16 / 25) : ℂ) * ζ ^ 10 + ((7 / 275) : ℂ) * ζ ^ 12 - ((697 / 550) : ℂ) * ζ ^ 14 + ((417 / 220) : ℂ) * ζ ^ 16 + ((34 / 275) : ℂ) * ζ ^ 18 - ((19 / 1100) : ℂ) * ζ ^ 20 + ((3 / 25) : ℂ) * ζ ^ 22 + ((1777 / 1100) : ℂ) * ζ ^ 24 + ((323 / 275) : ℂ) * ζ ^ 26 + ((7 / 550) : ℂ) * ζ ^ 28 - ((2217 / 1100) : ℂ) * ζ ^ 30 - ((2587 / 1100) : ℂ) * ζ ^ 32 + ((203 / 100) : ℂ) * ζ ^ 34 - ((216 / 275) : ℂ) * ζ ^ 36 - ((122 / 275) : ℂ) * ζ ^ 38 + ((941 / 1100) : ℂ) * ζ ^ 40 - ((271 / 1100) : ℂ) * ζ ^ 42 + ((21 / 1100) : ℂ) * ζ ^ 44 + ((23 / 110) : ℂ) * ζ ^ 46 - ((17 / 1100) : ℂ) * ζ ^ 48 + ((49 / 220) : ℂ) * ζ ^ 50 + ((104 / 275) : ℂ) * ζ ^ 52 - ((739 / 1100) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_2_6 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        2 6 =
      alternatingSixAmbientRow16TransformedGeneratorA
        2 6 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((23 / 100) : ℂ) + ((439 / 100) : ℂ) * ζ ^ 2 - ((121 / 20) : ℂ) * ζ ^ 6 - ((267 / 100) : ℂ) * ζ ^ 8 - ((71 / 20) : ℂ) * ζ ^ 10 + ((169 / 25) : ℂ) * ζ ^ 12 - ((239 / 100) : ℂ) * ζ ^ 14 + ((29 / 50) : ℂ) * ζ ^ 16 + ((3 / 2) : ℂ) * ζ ^ 18 - ((43 / 20) : ℂ) * ζ ^ 20 - ((543 / 100) : ℂ) * ζ ^ 22 + ((3 / 5) : ℂ) * ζ ^ 24 + ((344 / 25) : ℂ) * ζ ^ 26 + ((203 / 100) : ℂ) * ζ ^ 28 + ((14 / 5) : ℂ) * ζ ^ 30 - ((213 / 20) : ℂ) * ζ ^ 32 - ((18 / 25) : ℂ) * ζ ^ 34 + ((29 / 25) : ℂ) * ζ ^ 36 - ((331 / 100) : ℂ) * ζ ^ 38 + ((7 / 20) : ℂ) * ζ ^ 40 - ((43 / 25) : ℂ) * ζ ^ 42 + ((299 / 100) : ℂ) * ζ ^ 44 - (2 : ℂ) * ζ ^ 46 + ((249 / 100) : ℂ) * ζ ^ 48 - ((339 / 100) : ℂ) * ζ ^ 50 + ((7 / 2) : ℂ) * ζ ^ 52 - ((13 / 100) : ℂ) * ζ ^ 54 - ((37 / 50) : ℂ) * ζ ^ 56)
private theorem row16_transformedGeneratorA_2_7 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        2 7 =
      alternatingSixAmbientRow16TransformedGeneratorA
        2 7 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((243 / 50) : ℂ) - ((61 / 20) : ℂ) * ζ ^ 2 + ((499 / 100) : ℂ) * ζ ^ 4 + ((32 / 25) : ℂ) * ζ ^ 6 + ((49 / 100) : ℂ) * ζ ^ 8 + ((121 / 25) : ℂ) * ζ ^ 10 - ((323 / 100) : ℂ) * ζ ^ 12 + ((9 / 50) : ℂ) * ζ ^ 14 + ((17 / 20) : ℂ) * ζ ^ 16 + ((1 / 25) : ℂ) * ζ ^ 18 + ((193 / 100) : ℂ) * ζ ^ 20 + ((7 / 100) : ℂ) * ζ ^ 22 - ((28 / 25) : ℂ) * ζ ^ 24 - ((111 / 50) : ℂ) * ζ ^ 26 - ((153 / 100) : ℂ) * ζ ^ 28 - ((26 / 5) : ℂ) * ζ ^ 30 + ((203 / 50) : ℂ) * ζ ^ 32 + ((223 / 100) : ℂ) * ζ ^ 34 - ((147 / 50) : ℂ) * ζ ^ 36 + ((461 / 100) : ℂ) * ζ ^ 38 + ((31 / 100) : ℂ) * ζ ^ 40 - ((59 / 100) : ℂ) * ζ ^ 42 - ((33 / 100) : ℂ) * ζ ^ 44 + ((37 / 20) : ℂ) * ζ ^ 46 - ((24 / 25) : ℂ) * ζ ^ 48 + ((4 / 25) : ℂ) * ζ ^ 50 - ((153 / 100) : ℂ) * ζ ^ 52 - ((89 / 50) : ℂ) * ζ ^ 54 + ((42 / 25) : ℂ) * ζ ^ 56)
private theorem row16_transformedGeneratorA_3_0 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        3 0 =
      alternatingSixAmbientRow16TransformedGeneratorA
        3 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((269 / 100) : ℂ) + ((101 / 50) : ℂ) * ζ ^ 2 - ((269 / 100) : ℂ) * ζ ^ 4 - ((207 / 100) : ℂ) * ζ ^ 6 - ((11 / 50) : ℂ) * ζ ^ 8 + ((167 / 50) : ℂ) * ζ ^ 10 - ((123 / 100) : ℂ) * ζ ^ 12 - ((27 / 20) : ℂ) * ζ ^ 14 + ((243 / 50) : ℂ) * ζ ^ 16 + ((89 / 100) : ℂ) * ζ ^ 18 - ((69 / 100) : ℂ) * ζ ^ 20 - ((24 / 25) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 24 + ((107 / 100) : ℂ) * ζ ^ 26 + ((41 / 50) : ℂ) * ζ ^ 28 + ((33 / 100) : ℂ) * ζ ^ 30 - ((221 / 100) : ℂ) * ζ ^ 32 - ((41 / 100) : ℂ) * ζ ^ 34 - ((31 / 50) : ℂ) * ζ ^ 36 - ((23 / 100) : ℂ) * ζ ^ 38 + ((3 / 100) : ℂ) * ζ ^ 40 + ((13 / 100) : ℂ) * ζ ^ 42 - ((77 / 100) : ℂ) * ζ ^ 44 + ((133 / 100) : ℂ) * ζ ^ 46 + ((139 / 100) : ℂ) * ζ ^ 48 - ((101 / 100) : ℂ) * ζ ^ 50 + ((29 / 50) : ℂ) * ζ ^ 52 + ((1 / 5) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_3_1 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        3 1 =
      alternatingSixAmbientRow16TransformedGeneratorA
        3 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((33 / 20) : ℂ) + ((137 / 100) : ℂ) * ζ ^ 2 - ((33 / 20) : ℂ) * ζ ^ 4 - ((41 / 25) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 + ((23 / 25) : ℂ) * ζ ^ 10 - ((7 / 10) : ℂ) * ζ ^ 12 - ((51 / 50) : ℂ) * ζ ^ 14 + ((33 / 20) : ℂ) * ζ ^ 16 - ((169 / 100) : ℂ) * ζ ^ 18 - ((13 / 10) : ℂ) * ζ ^ 20 + ((131 / 100) : ℂ) * ζ ^ 22 + ((17 / 20) : ℂ) * ζ ^ 24 + ((12 / 25) : ℂ) * ζ ^ 26 - ((1 / 5) : ℂ) * ζ ^ 28 - ((33 / 100) : ℂ) * ζ ^ 30 - ((13 / 20) : ℂ) * ζ ^ 32 + ((113 / 100) : ℂ) * ζ ^ 34 - ((4 / 5) : ℂ) * ζ ^ 36 - ((11 / 100) : ℂ) * ζ ^ 38 + ((9 / 5) : ℂ) * ζ ^ 40 - ((19 / 20) : ℂ) * ζ ^ 42 - ((13 / 10) : ℂ) * ζ ^ 44 + ((23 / 25) : ℂ) * ζ ^ 46 + ((3 / 4) : ℂ) * ζ ^ 48 + ((9 / 100) : ℂ) * ζ ^ 50 + ((11 / 20) : ℂ) * ζ ^ 52 - ((49 / 100) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_3_2 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        3 2 =
      alternatingSixAmbientRow16TransformedGeneratorA
        3 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((57 / 20) : ℂ) + ((89 / 50) : ℂ) * ζ ^ 2 + ((327 / 100) : ℂ) * ζ ^ 4 + ((17 / 50) : ℂ) * ζ ^ 6 + ((333 / 100) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 10 - ((104 / 25) : ℂ) * ζ ^ 12 - ((183 / 25) : ℂ) * ζ ^ 14 + ((17 / 25) : ℂ) * ζ ^ 16 + ((179 / 50) : ℂ) * ζ ^ 18 - ((321 / 50) : ℂ) * ζ ^ 20 + ((43 / 25) : ℂ) * ζ ^ 22 + ((54 / 25) : ℂ) * ζ ^ 24 - ((53 / 50) : ℂ) * ζ ^ 26 - ((101 / 100) : ℂ) * ζ ^ 28 - ((37 / 100) : ℂ) * ζ ^ 30 + ((481 / 100) : ℂ) * ζ ^ 32 + ((973 / 100) : ℂ) * ζ ^ 34 + ((89 / 100) : ℂ) * ζ ^ 36 - ((949 / 100) : ℂ) * ζ ^ 38 + ((437 / 100) : ℂ) * ζ ^ 40 + ((119 / 100) : ℂ) * ζ ^ 42 - ((659 / 100) : ℂ) * ζ ^ 44 + ((19 / 50) : ℂ) * ζ ^ 46 + ((46 / 25) : ℂ) * ζ ^ 48 + ((51 / 20) : ℂ) * ζ ^ 50 - ((163 / 100) : ℂ) * ζ ^ 52 - ((52 / 25) : ℂ) * ζ ^ 54 - ((2 / 25) : ℂ) * ζ ^ 56)
private theorem row16_transformedGeneratorA_3_3 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        3 3 =
      alternatingSixAmbientRow16TransformedGeneratorA
        3 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((146 / 25) : ℂ) + ((93 / 20) : ℂ) * ζ ^ 2 - ((581 / 100) : ℂ) * ζ ^ 4 - ((673 / 100) : ℂ) * ζ ^ 6 + ((191 / 100) : ℂ) * ζ ^ 8 + ((241 / 100) : ℂ) * ζ ^ 10 - ((107 / 20) : ℂ) * ζ ^ 12 + ((303 / 100) : ℂ) * ζ ^ 14 + ((159 / 20) : ℂ) * ζ ^ 16 - ((447 / 100) : ℂ) * ζ ^ 18 - ((74 / 25) : ℂ) * ζ ^ 20 - ((199 / 100) : ℂ) * ζ ^ 22 + ((238 / 25) : ℂ) * ζ ^ 24 + ((191 / 50) : ℂ) * ζ ^ 26 - ((611 / 50) : ℂ) * ζ ^ 28 + ((93 / 100) : ℂ) * ζ ^ 30 + ((11 / 4) : ℂ) * ζ ^ 32 - ((379 / 100) : ℂ) * ζ ^ 34 - ((409 / 100) : ℂ) * ζ ^ 36 + ((23 / 10) : ℂ) * ζ ^ 38 + ((419 / 100) : ℂ) * ζ ^ 40 + ((99 / 50) : ℂ) * ζ ^ 42 - ((363 / 100) : ℂ) * ζ ^ 44 - ((123 / 100) : ℂ) * ζ ^ 46 + ((399 / 100) : ℂ) * ζ ^ 48 - ((49 / 20) : ℂ) * ζ ^ 50 + ((69 / 50) : ℂ) * ζ ^ 52 + ((147 / 100) : ℂ) * ζ ^ 54 - ((29 / 25) : ℂ) * ζ ^ 56)
private theorem row16_transformedGeneratorA_3_4 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        3 4 =
      alternatingSixAmbientRow16TransformedGeneratorA
        3 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((757 / 1100) : ℂ) + ((268 / 275) : ℂ) * ζ ^ 2 - ((757 / 1100) : ℂ) * ζ ^ 4 - ((933 / 1100) : ℂ) * ζ ^ 6 - ((26 / 275) : ℂ) * ζ ^ 8 + ((252 / 275) : ℂ) * ζ ^ 10 - ((119 / 220) : ℂ) * ζ ^ 12 - ((1091 / 1100) : ℂ) * ζ ^ 14 + ((328 / 275) : ℂ) * ζ ^ 16 + ((483 / 1100) : ℂ) * ζ ^ 18 - ((1261 / 1100) : ℂ) * ζ ^ 20 - ((391 / 550) : ℂ) * ζ ^ 22 - ((647 / 1100) : ℂ) * ζ ^ 24 - ((19 / 1100) : ℂ) * ζ ^ 26 + ((27 / 25) : ℂ) * ζ ^ 28 + ((201 / 220) : ℂ) * ζ ^ 30 - ((147 / 220) : ℂ) * ζ ^ 32 - ((1013 / 1100) : ℂ) * ζ ^ 34 + ((71 / 50) : ℂ) * ζ ^ 36 - ((289 / 1100) : ℂ) * ζ ^ 38 - ((1839 / 1100) : ℂ) * ζ ^ 40 - ((247 / 1100) : ℂ) * ζ ^ 42 + ((681 / 1100) : ℂ) * ζ ^ 44 + ((491 / 1100) : ℂ) * ζ ^ 46 - ((277 / 1100) : ℂ) * ζ ^ 48 - ((227 / 1100) : ℂ) * ζ ^ 50 + ((4 / 25) : ℂ) * ζ ^ 52 - ((61 / 550) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_3_5 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        3 5 =
      alternatingSixAmbientRow16TransformedGeneratorA
        3 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((1433 / 1100) : ℂ) + ((147 / 100) : ℂ) * ζ ^ 2 - ((1433 / 1100) : ℂ) * ζ ^ 4 - ((7 / 10) : ℂ) * ζ ^ 6 - ((1791 / 1100) : ℂ) * ζ ^ 8 - ((142 / 275) : ℂ) * ζ ^ 10 + ((1423 / 550) : ℂ) * ζ ^ 12 - ((823 / 550) : ℂ) * ζ ^ 14 - ((133 / 1100) : ℂ) * ζ ^ 16 - ((887 / 1100) : ℂ) * ζ ^ 18 + ((153 / 550) : ℂ) * ζ ^ 20 + ((17 / 44) : ℂ) * ζ ^ 22 - ((1439 / 1100) : ℂ) * ζ ^ 24 + ((29 / 55) : ℂ) * ζ ^ 26 + ((718 / 275) : ℂ) * ζ ^ 28 + ((1603 / 1100) : ℂ) * ζ ^ 30 - ((1317 / 1100) : ℂ) * ζ ^ 32 + ((123 / 1100) : ℂ) * ζ ^ 34 - ((27 / 110) : ℂ) * ζ ^ 36 - ((501 / 1100) : ℂ) * ζ ^ 38 - ((13 / 55) : ℂ) * ζ ^ 40 - ((243 / 1100) : ℂ) * ζ ^ 42 - ((2 / 275) : ℂ) * ζ ^ 44 + ((323 / 550) : ℂ) * ζ ^ 46 - ((39 / 100) : ℂ) * ζ ^ 48 - ((1 / 220) : ℂ) * ζ ^ 50 + ((1179 / 1100) : ℂ) * ζ ^ 52 - ((447 / 1100) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_3_6 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        3 6 =
      alternatingSixAmbientRow16TransformedGeneratorA
        3 6 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((67 / 20) : ℂ) - ((119 / 25) : ℂ) * ζ ^ 2 + ((293 / 100) : ℂ) * ζ ^ 4 + ((98 / 25) : ℂ) * ζ ^ 6 + ((153 / 20) : ℂ) * ζ ^ 8 - ((99 / 100) : ℂ) * ζ ^ 10 - ((32 / 25) : ℂ) * ζ ^ 12 - ((46 / 25) : ℂ) * ζ ^ 14 - ((361 / 50) : ℂ) * ζ ^ 16 + ((2 / 25) : ℂ) * ζ ^ 18 - ((57 / 50) : ℂ) * ζ ^ 20 + ((403 / 50) : ℂ) * ζ ^ 22 + ((44 / 25) : ℂ) * ζ ^ 24 - ((161 / 25) : ℂ) * ζ ^ 26 - ((641 / 100) : ℂ) * ζ ^ 28 + ((377 / 100) : ℂ) * ζ ^ 30 + ((821 / 100) : ℂ) * ζ ^ 32 - ((13 / 20) : ℂ) * ζ ^ 34 + ((423 / 100) : ℂ) * ζ ^ 36 + ((71 / 100) : ℂ) * ζ ^ 38 + ((41 / 100) : ℂ) * ζ ^ 40 - ((99 / 20) : ℂ) * ζ ^ 42 - ((683 / 100) : ℂ) * ζ ^ 44 + ((89 / 25) : ℂ) * ζ ^ 46 + ((12 / 5) : ℂ) * ζ ^ 48 - ((269 / 100) : ℂ) * ζ ^ 50 - ((119 / 100) : ℂ) * ζ ^ 52 + ((7 / 10) : ℂ) * ζ ^ 54 + ((2 / 25) : ℂ) * ζ ^ 56)
private theorem row16_transformedGeneratorA_3_7 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        3 7 =
      alternatingSixAmbientRow16TransformedGeneratorA
        3 7 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((146 / 25) : ℂ) + ((351 / 100) : ℂ) * ζ ^ 2 - ((587 / 100) : ℂ) * ζ ^ 4 - ((77 / 20) : ℂ) * ζ ^ 6 - ((51 / 100) : ℂ) * ζ ^ 8 + ((267 / 100) : ℂ) * ζ ^ 10 - ((689 / 100) : ℂ) * ζ ^ 12 - ((59 / 100) : ℂ) * ζ ^ 14 + ((891 / 100) : ℂ) * ζ ^ 16 - ((223 / 100) : ℂ) * ζ ^ 18 - ((2 / 5) : ℂ) * ζ ^ 20 - ((219 / 100) : ℂ) * ζ ^ 22 + ((13 / 5) : ℂ) * ζ ^ 24 + ((97 / 50) : ℂ) * ζ ^ 26 - ((41 / 10) : ℂ) * ζ ^ 28 - ((377 / 100) : ℂ) * ζ ^ 30 + ((321 / 100) : ℂ) * ζ ^ 32 + ((293 / 100) : ℂ) * ζ ^ 34 - ((841 / 100) : ℂ) * ζ ^ 36 + ((53 / 25) : ℂ) * ζ ^ 38 + ((121 / 20) : ℂ) * ζ ^ 40 - ((89 / 50) : ℂ) * ζ ^ 42 - ((11 / 20) : ℂ) * ζ ^ 44 + ((309 / 100) : ℂ) * ζ ^ 46 + ((217 / 100) : ℂ) * ζ ^ 48 + ((63 / 100) : ℂ) * ζ ^ 50 - ((49 / 50) : ℂ) * ζ ^ 52 - ((109 / 100) : ℂ) * ζ ^ 54 + ((29 / 25) : ℂ) * ζ ^ 56)
private theorem row16_transformedGeneratorA_4_0 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        4 0 =
      alternatingSixAmbientRow16TransformedGeneratorA
        4 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((53 / 100) : ℂ) + ((53 / 100) : ℂ) * ζ ^ 4 - ((26 / 5) : ℂ) * ζ ^ 8 + ((227 / 50) : ℂ) * ζ ^ 12 - ((271 / 100) : ℂ) * ζ ^ 16 + ((431 / 100) : ℂ) * ζ ^ 20 - ((47 / 20) : ℂ) * ζ ^ 24 + ((57 / 10) : ℂ) * ζ ^ 28 - ((271 / 100) : ℂ) * ζ ^ 32 + ((63 / 50) : ℂ) * ζ ^ 36 - ((83 / 25) : ℂ) * ζ ^ 40 + ((91 / 25) : ℂ) * ζ ^ 44 - ((453 / 100) : ℂ) * ζ ^ 48 + ((19 / 20) : ℂ) * ζ ^ 52)
private theorem row16_transformedGeneratorA_4_1 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        4 1 =
      alternatingSixAmbientRow16TransformedGeneratorA
        4 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((1 / 50) : ℂ) - ((1 / 50) : ℂ) * ζ ^ 4 - ((131 / 100) : ℂ) * ζ ^ 8 + ((39 / 25) : ℂ) * ζ ^ 12 + ((19 / 50) : ℂ) * ζ ^ 16 - ((37 / 100) : ℂ) * ζ ^ 20 + ((33 / 20) : ℂ) * ζ ^ 24 - ((19 / 100) : ℂ) * ζ ^ 28 - ((149 / 50) : ℂ) * ζ ^ 32 + ((87 / 50) : ℂ) * ζ ^ 36 - ((91 / 100) : ℂ) * ζ ^ 40 - ((21 / 100) : ℂ) * ζ ^ 44 + ((111 / 50) : ℂ) * ζ ^ 48 - ((91 / 100) : ℂ) * ζ ^ 52)
private theorem row16_transformedGeneratorA_4_2 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        4 2 =
      alternatingSixAmbientRow16TransformedGeneratorA
        4 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((23 / 50) : ℂ) + ((197 / 100) : ℂ) * ζ ^ 2 - ((23 / 50) : ℂ) * ζ ^ 4 - ((5 / 4) : ℂ) * ζ ^ 6 + ((337 / 50) : ℂ) * ζ ^ 8 - ((33 / 25) : ℂ) * ζ ^ 10 - ((629 / 100) : ℂ) * ζ ^ 12 + ((11 / 100) : ℂ) * ζ ^ 14 - ((271 / 100) : ℂ) * ζ ^ 16 + ((187 / 50) : ℂ) * ζ ^ 18 + ((1 / 20) : ℂ) * ζ ^ 20 - ((19 / 5) : ℂ) * ζ ^ 22 + ((231 / 100) : ℂ) * ζ ^ 24 + ((143 / 50) : ℂ) * ζ ^ 26 - ((208 / 25) : ℂ) * ζ ^ 28 + ((493 / 100) : ℂ) * ζ ^ 30 + ((811 / 100) : ℂ) * ζ ^ 32 - ((201 / 50) : ℂ) * ζ ^ 34 + ((387 / 50) : ℂ) * ζ ^ 36 - ((71 / 25) : ℂ) * ζ ^ 38 - ((29 / 4) : ℂ) * ζ ^ 40 + ((499 / 100) : ℂ) * ζ ^ 42 + ((127 / 100) : ℂ) * ζ ^ 44 - ((651 / 100) : ℂ) * ζ ^ 46 + ((501 / 100) : ℂ) * ζ ^ 48 + ((93 / 50) : ℂ) * ζ ^ 50 - ((751 / 100) : ℂ) * ζ ^ 52 + ((2 / 25) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_4_3 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        4 3 =
      alternatingSixAmbientRow16TransformedGeneratorA
        4 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((49 / 50) : ℂ) - ((18 / 25) : ℂ) * ζ ^ 2 - ((49 / 50) : ℂ) * ζ ^ 4 + ((123 / 100) : ℂ) * ζ ^ 6 - ((909 / 100) : ℂ) * ζ ^ 8 - ((33 / 50) : ℂ) * ζ ^ 10 + ((269 / 50) : ℂ) * ζ ^ 12 + ((129 / 100) : ℂ) * ζ ^ 14 + ((67 / 25) : ℂ) * ζ ^ 16 - ((3 / 4) : ℂ) * ζ ^ 18 - ((97 / 25) : ℂ) * ζ ^ 20 + ((39 / 50) : ℂ) * ζ ^ 22 + ((41 / 20) : ℂ) * ζ ^ 24 + ((693 / 100) : ℂ) * ζ ^ 26 + ((153 / 20) : ℂ) * ζ ^ 28 - ((34 / 5) : ℂ) * ζ ^ 30 - ((217 / 20) : ℂ) * ζ ^ 32 + ((64 / 25) : ℂ) * ζ ^ 34 + ((213 / 50) : ℂ) * ζ ^ 36 + ((47 / 50) : ℂ) * ζ ^ 38 + ((17 / 50) : ℂ) * ζ ^ 40 - ((119 / 25) : ℂ) * ζ ^ 42 - ((29 / 20) : ℂ) * ζ ^ 44 - ((173 / 100) : ℂ) * ζ ^ 46 + (2 : ℂ) * ζ ^ 48 + ((527 / 100) : ℂ) * ζ ^ 50 + ((24 / 25) : ℂ) * ζ ^ 52 - ((279 / 100) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_4_4 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        4 4 =
      alternatingSixAmbientRow16TransformedGeneratorA
        4 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((973 / 1100) : ℂ) + ((973 / 1100) : ℂ) * ζ ^ 4 - ((662 / 275) : ℂ) * ζ ^ 8 + ((526 / 275) : ℂ) * ζ ^ 12 - ((1433 / 1100) : ℂ) * ζ ^ 16 + ((3737 / 1100) : ℂ) * ζ ^ 20 - ((2613 / 1100) : ℂ) * ζ ^ 24 + ((661 / 550) : ℂ) * ζ ^ 28 - ((433 / 220) : ℂ) * ζ ^ 32 - ((767 / 550) : ℂ) * ζ ^ 36 - ((477 / 550) : ℂ) * ζ ^ 40 + ((157 / 50) : ℂ) * ζ ^ 44 - ((1383 / 1100) : ℂ) * ζ ^ 48 + ((857 / 1100) : ℂ) * ζ ^ 52)
private theorem row16_transformedGeneratorA_4_5 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        4 5 =
      alternatingSixAmbientRow16TransformedGeneratorA
        4 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((829 / 550) : ℂ) + ((829 / 550) : ℂ) * ζ ^ 4 - ((3913 / 1100) : ℂ) * ζ ^ 8 + ((379 / 275) : ℂ) * ζ ^ 12 - ((1 / 10) : ℂ) * ζ ^ 16 + ((1027 / 1100) : ℂ) * ζ ^ 20 + ((959 / 1100) : ℂ) * ζ ^ 24 + ((93 / 100) : ℂ) * ζ ^ 28 + ((79 / 275) : ℂ) * ζ ^ 32 + ((591 / 550) : ℂ) * ζ ^ 36 - ((193 / 100) : ℂ) * ζ ^ 40 + ((1597 / 1100) : ℂ) * ζ ^ 44 - ((507 / 550) : ℂ) * ζ ^ 48 - ((503 / 1100) : ℂ) * ζ ^ 52)
private theorem row16_transformedGeneratorA_4_6 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        4 6 =
      alternatingSixAmbientRow16TransformedGeneratorA
        4 6 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((23 / 50) : ℂ) - ((197 / 100) : ℂ) * ζ ^ 2 - ((23 / 50) : ℂ) * ζ ^ 4 + ((5 / 4) : ℂ) * ζ ^ 6 + ((337 / 50) : ℂ) * ζ ^ 8 + ((33 / 25) : ℂ) * ζ ^ 10 - ((629 / 100) : ℂ) * ζ ^ 12 - ((11 / 100) : ℂ) * ζ ^ 14 - ((271 / 100) : ℂ) * ζ ^ 16 - ((187 / 50) : ℂ) * ζ ^ 18 + ((1 / 20) : ℂ) * ζ ^ 20 + ((19 / 5) : ℂ) * ζ ^ 22 + ((231 / 100) : ℂ) * ζ ^ 24 - ((143 / 50) : ℂ) * ζ ^ 26 - ((208 / 25) : ℂ) * ζ ^ 28 - ((493 / 100) : ℂ) * ζ ^ 30 + ((811 / 100) : ℂ) * ζ ^ 32 + ((201 / 50) : ℂ) * ζ ^ 34 + ((387 / 50) : ℂ) * ζ ^ 36 + ((71 / 25) : ℂ) * ζ ^ 38 - ((29 / 4) : ℂ) * ζ ^ 40 - ((499 / 100) : ℂ) * ζ ^ 42 + ((127 / 100) : ℂ) * ζ ^ 44 + ((651 / 100) : ℂ) * ζ ^ 46 + ((501 / 100) : ℂ) * ζ ^ 48 - ((93 / 50) : ℂ) * ζ ^ 50 - ((751 / 100) : ℂ) * ζ ^ 52 - ((2 / 25) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_4_7 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        4 7 =
      alternatingSixAmbientRow16TransformedGeneratorA
        4 7 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((49 / 50) : ℂ) + ((18 / 25) : ℂ) * ζ ^ 2 - ((49 / 50) : ℂ) * ζ ^ 4 - ((123 / 100) : ℂ) * ζ ^ 6 - ((909 / 100) : ℂ) * ζ ^ 8 + ((33 / 50) : ℂ) * ζ ^ 10 + ((269 / 50) : ℂ) * ζ ^ 12 - ((129 / 100) : ℂ) * ζ ^ 14 + ((67 / 25) : ℂ) * ζ ^ 16 + ((3 / 4) : ℂ) * ζ ^ 18 - ((97 / 25) : ℂ) * ζ ^ 20 - ((39 / 50) : ℂ) * ζ ^ 22 + ((41 / 20) : ℂ) * ζ ^ 24 - ((693 / 100) : ℂ) * ζ ^ 26 + ((153 / 20) : ℂ) * ζ ^ 28 + ((34 / 5) : ℂ) * ζ ^ 30 - ((217 / 20) : ℂ) * ζ ^ 32 - ((64 / 25) : ℂ) * ζ ^ 34 + ((213 / 50) : ℂ) * ζ ^ 36 - ((47 / 50) : ℂ) * ζ ^ 38 + ((17 / 50) : ℂ) * ζ ^ 40 + ((119 / 25) : ℂ) * ζ ^ 42 - ((29 / 20) : ℂ) * ζ ^ 44 + ((173 / 100) : ℂ) * ζ ^ 46 + (2 : ℂ) * ζ ^ 48 - ((527 / 100) : ℂ) * ζ ^ 50 + ((24 / 25) : ℂ) * ζ ^ 52 + ((279 / 100) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_5_0 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        5 0 =
      alternatingSixAmbientRow16TransformedGeneratorA
        5 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((2 / 25) : ℂ) + ((2 / 25) : ℂ) * ζ ^ 4 + ((22 / 25) : ℂ) * ζ ^ 8 + ((43 / 100) : ℂ) * ζ ^ 12 - ((643 / 100) : ℂ) * ζ ^ 16 + ((5 / 2) : ℂ) * ζ ^ 20 - ζ ^ 24 - ((29 / 50) : ℂ) * ζ ^ 28 + ((27 / 10) : ℂ) * ζ ^ 32 - ((7 / 25) : ℂ) * ζ ^ 36 + ((11 / 20) : ℂ) * ζ ^ 40 + ((279 / 100) : ℂ) * ζ ^ 44 - ((383 / 100) : ℂ) * ζ ^ 48 - ((8 / 25) : ℂ) * ζ ^ 52)
private theorem row16_transformedGeneratorA_5_1 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        5 1 =
      alternatingSixAmbientRow16TransformedGeneratorA
        5 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((23 / 25) : ℂ) + ((23 / 25) : ℂ) * ζ ^ 4 - ((389 / 100) : ℂ) * ζ ^ 8 + ((81 / 25) : ℂ) * ζ ^ 12 - ((62 / 25) : ℂ) * ζ ^ 16 + ((68 / 25) : ℂ) * ζ ^ 20 + ((13 / 5) : ℂ) * ζ ^ 24 - ((93 / 50) : ℂ) * ζ ^ 28 - ((23 / 25) : ℂ) * ζ ^ 32 + ((211 / 100) : ℂ) * ζ ^ 36 - ((187 / 50) : ℂ) * ζ ^ 40 + ((301 / 100) : ℂ) * ζ ^ 44 - ((3 / 25) : ℂ) * ζ ^ 48 - ((149 / 100) : ℂ) * ζ ^ 52)
private theorem row16_transformedGeneratorA_5_2 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        5 2 =
      alternatingSixAmbientRow16TransformedGeneratorA
        5 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((229 / 100) : ℂ) - ((31 / 4) : ℂ) * ζ ^ 2 - ((229 / 100) : ℂ) * ζ ^ 4 + ((421 / 100) : ℂ) * ζ ^ 6 - ((153 / 20) : ℂ) * ζ ^ 8 - ((411 / 100) : ℂ) * ζ ^ 10 + ((437 / 100) : ℂ) * ζ ^ 12 + ((15 / 2) : ℂ) * ζ ^ 14 + ((17 / 50) : ℂ) * ζ ^ 16 + ((43 / 50) : ℂ) * ζ ^ 18 + ((601 / 50) : ℂ) * ζ ^ 20 - ((141 / 50) : ℂ) * ζ ^ 22 - ((9 / 4) : ℂ) * ζ ^ 24 - ((48 / 25) : ℂ) * ζ ^ 26 - ((359 / 100) : ℂ) * ζ ^ 28 + ((81 / 20) : ℂ) * ζ ^ 30 - ((59 / 20) : ℂ) * ζ ^ 32 - ((1079 / 100) : ℂ) * ζ ^ 34 - ((77 / 25) : ℂ) * ζ ^ 36 + ((517 / 50) : ℂ) * ζ ^ 38 - ((811 / 100) : ℂ) * ζ ^ 40 - ((207 / 100) : ℂ) * ζ ^ 42 + ((383 / 25) : ℂ) * ζ ^ 44 - ((69 / 50) : ℂ) * ζ ^ 46 - ((19 / 100) : ℂ) * ζ ^ 48 - ((76 / 25) : ℂ) * ζ ^ 50 - ((9 / 20) : ℂ) * ζ ^ 52 + ((123 / 100) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_5_3 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        5 3 =
      alternatingSixAmbientRow16TransformedGeneratorA
        5 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((659 / 100) : ℂ) + ((117 / 50) : ℂ) * ζ ^ 2 + ((659 / 100) : ℂ) * ζ ^ 4 + ((63 / 100) : ℂ) * ζ ^ 6 - ((701 / 100) : ℂ) * ζ ^ 8 + ((3 / 100) : ℂ) * ζ ^ 10 + ((133 / 10) : ℂ) * ζ ^ 12 - ((79 / 50) : ℂ) * ζ ^ 14 - ((269 / 20) : ℂ) * ζ ^ 16 - ((73 / 25) : ℂ) * ζ ^ 18 - ((19 / 10) : ℂ) * ζ ^ 20 + ((68 / 25) : ℂ) * ζ ^ 22 - ((36 / 25) : ℂ) * ζ ^ 24 + ((99 / 25) : ℂ) * ζ ^ 26 + ((929 / 100) : ℂ) * ζ ^ 28 - ((121 / 20) : ℂ) * ζ ^ 30 - ((401 / 50) : ℂ) * ζ ^ 32 + ((693 / 100) : ℂ) * ζ ^ 34 + ((637 / 50) : ℂ) * ζ ^ 36 + ζ ^ 38 - ((937 / 100) : ℂ) * ζ ^ 40 - ((144 / 25) : ℂ) * ζ ^ 42 + ((121 / 100) : ℂ) * ζ ^ 44 + ((108 / 25) : ℂ) * ζ ^ 46 - ((457 / 100) : ℂ) * ζ ^ 48 + ((469 / 100) : ℂ) * ζ ^ 50 - ((3 / 50) : ℂ) * ζ ^ 52 - ((159 / 50) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_5_4 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        5 4 =
      alternatingSixAmbientRow16TransformedGeneratorA
        5 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((17 / 22) : ℂ) - ((17 / 22) : ℂ) * ζ ^ 4 - ((423 / 550) : ℂ) * ζ ^ 8 + ((401 / 1100) : ℂ) * ζ ^ 12 - ((219 / 220) : ℂ) * ζ ^ 16 + ((1511 / 550) : ℂ) * ζ ^ 20 + ((463 / 550) : ℂ) * ζ ^ 24 - ((206 / 275) : ℂ) * ζ ^ 28 + ((13 / 11) : ℂ) * ζ ^ 32 - ((786 / 275) : ℂ) * ζ ^ 36 + ((697 / 220) : ℂ) * ζ ^ 40 + ((587 / 1100) : ℂ) * ζ ^ 44 - ((149 / 1100) : ℂ) * ζ ^ 48 - ((153 / 550) : ℂ) * ζ ^ 52)
private theorem row16_transformedGeneratorA_5_5 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        5 5 =
      alternatingSixAmbientRow16TransformedGeneratorA
        5 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((1643 / 550) : ℂ) - ((1643 / 550) : ℂ) * ζ ^ 4 - ((43 / 1100) : ℂ) * ζ ^ 8 - ((27 / 55) : ℂ) * ζ ^ 12 - ((339 / 550) : ℂ) * ζ ^ 16 + ((386 / 275) : ℂ) * ζ ^ 20 + ((1448 / 275) : ℂ) * ζ ^ 24 - ((1229 / 275) : ℂ) * ζ ^ 28 + ((423 / 275) : ℂ) * ζ ^ 32 - ((477 / 1100) : ℂ) * ζ ^ 36 - ((8 / 275) : ℂ) * ζ ^ 40 + ((21 / 20) : ℂ) * ζ ^ 44 - ((39 / 110) : ℂ) * ζ ^ 48 - ((2213 / 1100) : ℂ) * ζ ^ 52)
private theorem row16_transformedGeneratorA_5_6 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        5 6 =
      alternatingSixAmbientRow16TransformedGeneratorA
        5 6 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((229 / 100) : ℂ) + ((31 / 4) : ℂ) * ζ ^ 2 - ((229 / 100) : ℂ) * ζ ^ 4 - ((421 / 100) : ℂ) * ζ ^ 6 - ((153 / 20) : ℂ) * ζ ^ 8 + ((411 / 100) : ℂ) * ζ ^ 10 + ((437 / 100) : ℂ) * ζ ^ 12 - ((15 / 2) : ℂ) * ζ ^ 14 + ((17 / 50) : ℂ) * ζ ^ 16 - ((43 / 50) : ℂ) * ζ ^ 18 + ((601 / 50) : ℂ) * ζ ^ 20 + ((141 / 50) : ℂ) * ζ ^ 22 - ((9 / 4) : ℂ) * ζ ^ 24 + ((48 / 25) : ℂ) * ζ ^ 26 - ((359 / 100) : ℂ) * ζ ^ 28 - ((81 / 20) : ℂ) * ζ ^ 30 - ((59 / 20) : ℂ) * ζ ^ 32 + ((1079 / 100) : ℂ) * ζ ^ 34 - ((77 / 25) : ℂ) * ζ ^ 36 - ((517 / 50) : ℂ) * ζ ^ 38 - ((811 / 100) : ℂ) * ζ ^ 40 + ((207 / 100) : ℂ) * ζ ^ 42 + ((383 / 25) : ℂ) * ζ ^ 44 + ((69 / 50) : ℂ) * ζ ^ 46 - ((19 / 100) : ℂ) * ζ ^ 48 + ((76 / 25) : ℂ) * ζ ^ 50 - ((9 / 20) : ℂ) * ζ ^ 52 - ((123 / 100) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_5_7 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        5 7 =
      alternatingSixAmbientRow16TransformedGeneratorA
        5 7 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((659 / 100) : ℂ) - ((117 / 50) : ℂ) * ζ ^ 2 + ((659 / 100) : ℂ) * ζ ^ 4 - ((63 / 100) : ℂ) * ζ ^ 6 - ((701 / 100) : ℂ) * ζ ^ 8 - ((3 / 100) : ℂ) * ζ ^ 10 + ((133 / 10) : ℂ) * ζ ^ 12 + ((79 / 50) : ℂ) * ζ ^ 14 - ((269 / 20) : ℂ) * ζ ^ 16 + ((73 / 25) : ℂ) * ζ ^ 18 - ((19 / 10) : ℂ) * ζ ^ 20 - ((68 / 25) : ℂ) * ζ ^ 22 - ((36 / 25) : ℂ) * ζ ^ 24 - ((99 / 25) : ℂ) * ζ ^ 26 + ((929 / 100) : ℂ) * ζ ^ 28 + ((121 / 20) : ℂ) * ζ ^ 30 - ((401 / 50) : ℂ) * ζ ^ 32 - ((693 / 100) : ℂ) * ζ ^ 34 + ((637 / 50) : ℂ) * ζ ^ 36 - ζ ^ 38 - ((937 / 100) : ℂ) * ζ ^ 40 + ((144 / 25) : ℂ) * ζ ^ 42 + ((121 / 100) : ℂ) * ζ ^ 44 - ((108 / 25) : ℂ) * ζ ^ 46 - ((457 / 100) : ℂ) * ζ ^ 48 - ((469 / 100) : ℂ) * ζ ^ 50 - ((3 / 50) : ℂ) * ζ ^ 52 + ((159 / 50) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_6_0 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        6 0 =
      alternatingSixAmbientRow16TransformedGeneratorA
        6 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((1 / 100) : ℂ) + ((41 / 100) : ℂ) * ζ ^ 2 - ((1 / 100) : ℂ) * ζ ^ 4 - ((58 / 25) : ℂ) * ζ ^ 6 - ((3 / 5) : ℂ) * ζ ^ 8 + ((101 / 100) : ℂ) * ζ ^ 10 - ((119 / 50) : ℂ) * ζ ^ 12 - ((14 / 25) : ℂ) * ζ ^ 14 + ((187 / 100) : ℂ) * ζ ^ 16 + ((163 / 100) : ℂ) * ζ ^ 18 - ((71 / 50) : ℂ) * ζ ^ 20 - ((197 / 100) : ℂ) * ζ ^ 22 + ((43 / 10) : ℂ) * ζ ^ 24 + ((29 / 100) : ℂ) * ζ ^ 26 - ((9 / 2) : ℂ) * ζ ^ 28 + ((33 / 50) : ℂ) * ζ ^ 30 + ((97 / 100) : ℂ) * ζ ^ 32 - ((41 / 100) : ℂ) * ζ ^ 34 - ((67 / 100) : ℂ) * ζ ^ 36 + ((67 / 100) : ℂ) * ζ ^ 38 + ((119 / 100) : ℂ) * ζ ^ 40 + ((3 / 20) : ℂ) * ζ ^ 42 - ((89 / 50) : ℂ) * ζ ^ 44 - ((99 / 100) : ℂ) * ζ ^ 46 + ((53 / 50) : ℂ) * ζ ^ 48 - ((2 / 25) : ℂ) * ζ ^ 50 - ((17 / 20) : ℂ) * ζ ^ 52 - ((3 / 25) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_6_1 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        6 1 =
      alternatingSixAmbientRow16TransformedGeneratorA
        6 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((49 / 100) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((49 / 100) : ℂ) * ζ ^ 4 - ((7 / 5) : ℂ) * ζ ^ 6 - ((123 / 100) : ℂ) * ζ ^ 8 + ((7 / 5) : ℂ) * ζ ^ 10 - ((13 / 25) : ℂ) * ζ ^ 12 + ((3 / 5) : ℂ) * ζ ^ 14 + ((269 / 100) : ℂ) * ζ ^ 16 - ((1 / 5) : ℂ) * ζ ^ 18 + ((39 / 100) : ℂ) * ζ ^ 20 + ((9 / 20) : ℂ) * ζ ^ 24 - ((6 / 5) : ℂ) * ζ ^ 26 - ((11 / 50) : ℂ) * ζ ^ 28 - ((3 / 4) : ℂ) * ζ ^ 30 - ((249 / 100) : ℂ) * ζ ^ 32 + ((1 / 4) : ℂ) * ζ ^ 34 - ((47 / 25) : ℂ) * ζ ^ 36 - ((9 / 10) : ℂ) * ζ ^ 38 + ((47 / 100) : ℂ) * ζ ^ 40 + ((21 / 20) : ℂ) * ζ ^ 42 + ((27 / 100) : ℂ) * ζ ^ 44 - ((9 / 10) : ℂ) * ζ ^ 46 - ((19 / 100) : ℂ) * ζ ^ 48 - ((3 / 20) : ℂ) * ζ ^ 50 + ((18 / 25) : ℂ) * ζ ^ 52 + ((9 / 20) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_6_2 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        6 2 =
      alternatingSixAmbientRow16TransformedGeneratorA
        6 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((23 / 100) : ℂ) - ((439 / 100) : ℂ) * ζ ^ 2 + ((121 / 20) : ℂ) * ζ ^ 6 - ((267 / 100) : ℂ) * ζ ^ 8 + ((71 / 20) : ℂ) * ζ ^ 10 + ((169 / 25) : ℂ) * ζ ^ 12 + ((239 / 100) : ℂ) * ζ ^ 14 + ((29 / 50) : ℂ) * ζ ^ 16 - ((3 / 2) : ℂ) * ζ ^ 18 - ((43 / 20) : ℂ) * ζ ^ 20 + ((543 / 100) : ℂ) * ζ ^ 22 + ((3 / 5) : ℂ) * ζ ^ 24 - ((344 / 25) : ℂ) * ζ ^ 26 + ((203 / 100) : ℂ) * ζ ^ 28 - ((14 / 5) : ℂ) * ζ ^ 30 - ((213 / 20) : ℂ) * ζ ^ 32 + ((18 / 25) : ℂ) * ζ ^ 34 + ((29 / 25) : ℂ) * ζ ^ 36 + ((331 / 100) : ℂ) * ζ ^ 38 + ((7 / 20) : ℂ) * ζ ^ 40 + ((43 / 25) : ℂ) * ζ ^ 42 + ((299 / 100) : ℂ) * ζ ^ 44 + (2 : ℂ) * ζ ^ 46 + ((249 / 100) : ℂ) * ζ ^ 48 + ((339 / 100) : ℂ) * ζ ^ 50 + ((7 / 2) : ℂ) * ζ ^ 52 + ((13 / 100) : ℂ) * ζ ^ 54 - ((37 / 50) : ℂ) * ζ ^ 56)
private theorem row16_transformedGeneratorA_6_3 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        6 3 =
      alternatingSixAmbientRow16TransformedGeneratorA
        6 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((243 / 50) : ℂ) + ((61 / 20) : ℂ) * ζ ^ 2 + ((499 / 100) : ℂ) * ζ ^ 4 - ((32 / 25) : ℂ) * ζ ^ 6 + ((49 / 100) : ℂ) * ζ ^ 8 - ((121 / 25) : ℂ) * ζ ^ 10 - ((323 / 100) : ℂ) * ζ ^ 12 - ((9 / 50) : ℂ) * ζ ^ 14 + ((17 / 20) : ℂ) * ζ ^ 16 - ((1 / 25) : ℂ) * ζ ^ 18 + ((193 / 100) : ℂ) * ζ ^ 20 - ((7 / 100) : ℂ) * ζ ^ 22 - ((28 / 25) : ℂ) * ζ ^ 24 + ((111 / 50) : ℂ) * ζ ^ 26 - ((153 / 100) : ℂ) * ζ ^ 28 + ((26 / 5) : ℂ) * ζ ^ 30 + ((203 / 50) : ℂ) * ζ ^ 32 - ((223 / 100) : ℂ) * ζ ^ 34 - ((147 / 50) : ℂ) * ζ ^ 36 - ((461 / 100) : ℂ) * ζ ^ 38 + ((31 / 100) : ℂ) * ζ ^ 40 + ((59 / 100) : ℂ) * ζ ^ 42 - ((33 / 100) : ℂ) * ζ ^ 44 - ((37 / 20) : ℂ) * ζ ^ 46 - ((24 / 25) : ℂ) * ζ ^ 48 - ((4 / 25) : ℂ) * ζ ^ 50 - ((153 / 100) : ℂ) * ζ ^ 52 + ((89 / 50) : ℂ) * ζ ^ 54 + ((42 / 25) : ℂ) * ζ ^ 56)
private theorem row16_transformedGeneratorA_6_4 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        6 4 =
      alternatingSixAmbientRow16TransformedGeneratorA
        6 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((721 / 1100) : ℂ) - ((207 / 1100) : ℂ) * ζ ^ 2 - ((721 / 1100) : ℂ) * ζ ^ 4 - ((114 / 275) : ℂ) * ζ ^ 6 - ((357 / 550) : ℂ) * ζ ^ 8 + ((601 / 1100) : ℂ) * ζ ^ 10 - ((217 / 275) : ℂ) * ζ ^ 12 + ((13 / 55) : ℂ) * ζ ^ 14 + ((1761 / 1100) : ℂ) * ζ ^ 16 + ((233 / 1100) : ℂ) * ζ ^ 18 - ((227 / 550) : ℂ) * ζ ^ 20 - ((267 / 1100) : ℂ) * ζ ^ 22 + ((1563 / 550) : ℂ) * ζ ^ 24 + ((47 / 220) : ℂ) * ζ ^ 26 - ((1497 / 550) : ℂ) * ζ ^ 28 + ((104 / 275) : ℂ) * ζ ^ 30 + ((71 / 220) : ℂ) * ζ ^ 32 - ((489 / 1100) : ℂ) * ζ ^ 34 - ((1447 / 1100) : ℂ) * ζ ^ 36 + ((3 / 220) : ℂ) * ζ ^ 38 + ((133 / 100) : ℂ) * ζ ^ 40 - ((9 / 20) : ℂ) * ζ ^ 42 - ((149 / 550) : ℂ) * ζ ^ 44 + ((757 / 1100) : ℂ) * ζ ^ 46 + ((159 / 275) : ℂ) * ζ ^ 48 - ((4 / 25) : ℂ) * ζ ^ 50 + ((141 / 1100) : ℂ) * ζ ^ 52 + ((39 / 275) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_6_5 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        6 5 =
      alternatingSixAmbientRow16TransformedGeneratorA
        6 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((1051 / 1100) : ℂ) + ((93 / 275) : ℂ) * ζ ^ 2 - ((1051 / 1100) : ℂ) * ζ ^ 4 - ((827 / 550) : ℂ) * ζ ^ 6 - ((1569 / 1100) : ℂ) * ζ ^ 8 + ((16 / 25) : ℂ) * ζ ^ 10 + ((7 / 275) : ℂ) * ζ ^ 12 + ((697 / 550) : ℂ) * ζ ^ 14 + ((417 / 220) : ℂ) * ζ ^ 16 - ((34 / 275) : ℂ) * ζ ^ 18 - ((19 / 1100) : ℂ) * ζ ^ 20 - ((3 / 25) : ℂ) * ζ ^ 22 + ((1777 / 1100) : ℂ) * ζ ^ 24 - ((323 / 275) : ℂ) * ζ ^ 26 + ((7 / 550) : ℂ) * ζ ^ 28 + ((2217 / 1100) : ℂ) * ζ ^ 30 - ((2587 / 1100) : ℂ) * ζ ^ 32 - ((203 / 100) : ℂ) * ζ ^ 34 - ((216 / 275) : ℂ) * ζ ^ 36 + ((122 / 275) : ℂ) * ζ ^ 38 + ((941 / 1100) : ℂ) * ζ ^ 40 + ((271 / 1100) : ℂ) * ζ ^ 42 + ((21 / 1100) : ℂ) * ζ ^ 44 - ((23 / 110) : ℂ) * ζ ^ 46 - ((17 / 1100) : ℂ) * ζ ^ 48 - ((49 / 220) : ℂ) * ζ ^ 50 + ((104 / 275) : ℂ) * ζ ^ 52 + ((739 / 1100) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_6_6 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        6 6 =
      alternatingSixAmbientRow16TransformedGeneratorA
        6 6 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((27 / 100) : ℂ) + ((399 / 100) : ℂ) * ζ ^ 2 + ((1 / 25) : ℂ) * ζ ^ 4 - ((13 / 20) : ℂ) * ζ ^ 6 - ((499 / 100) : ℂ) * ζ ^ 8 - ((403 / 100) : ℂ) * ζ ^ 10 + ((15 / 2) : ℂ) * ζ ^ 12 - ((147 / 100) : ℂ) * ζ ^ 14 - ((26 / 25) : ℂ) * ζ ^ 16 - ((76 / 25) : ℂ) * ζ ^ 18 + ((7 / 4) : ℂ) * ζ ^ 20 + ((163 / 100) : ℂ) * ζ ^ 22 + ((69 / 25) : ℂ) * ζ ^ 24 + ((329 / 50) : ℂ) * ζ ^ 26 + ((57 / 20) : ℂ) * ζ ^ 28 + ((81 / 50) : ℂ) * ζ ^ 30 - ((869 / 100) : ℂ) * ζ ^ 32 - ((14 / 25) : ℂ) * ζ ^ 34 - ((78 / 25) : ℂ) * ζ ^ 36 - ((67 / 20) : ℂ) * ζ ^ 38 + ((13 / 4) : ℂ) * ζ ^ 40 + ((29 / 50) : ℂ) * ζ ^ 42 + ((53 / 100) : ℂ) * ζ ^ 44 - ((91 / 25) : ℂ) * ζ ^ 46 + ((57 / 100) : ℂ) * ζ ^ 48 + ((393 / 100) : ℂ) * ζ ^ 50 + ((16 / 25) : ℂ) * ζ ^ 52 - ((17 / 20) : ℂ) * ζ ^ 54 + ((37 / 50) : ℂ) * ζ ^ 56)
private theorem row16_transformedGeneratorA_6_7 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        6 7 =
      alternatingSixAmbientRow16TransformedGeneratorA
        6 7 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((243 / 50) : ℂ) - ((163 / 100) : ℂ) * ζ ^ 2 + ((473 / 100) : ℂ) * ζ ^ 4 - ((73 / 50) : ℂ) * ζ ^ 6 + ((337 / 100) : ℂ) * ζ ^ 8 + ((103 / 25) : ℂ) * ζ ^ 10 - ((429 / 100) : ℂ) * ζ ^ 12 + ((22 / 25) : ℂ) * ζ ^ 14 + ((3 / 100) : ℂ) * ζ ^ 16 - ((41 / 25) : ℂ) * ζ ^ 18 - ((71 / 100) : ℂ) * ζ ^ 20 + ((47 / 20) : ℂ) * ζ ^ 22 - ((37 / 25) : ℂ) * ζ ^ 24 - ((293 / 50) : ℂ) * ζ ^ 26 - ((227 / 100) : ℂ) * ζ ^ 28 - ((47 / 5) : ℂ) * ζ ^ 30 + ((11 / 25) : ℂ) * ζ ^ 32 + ((841 / 100) : ℂ) * ζ ^ 34 + ((13 / 10) : ℂ) * ζ ^ 36 + ((3 / 20) : ℂ) * ζ ^ 38 + ((43 / 100) : ℂ) * ζ ^ 40 + ((59 / 20) : ℂ) * ζ ^ 42 - ((397 / 100) : ℂ) * ζ ^ 44 - ((467 / 100) : ℂ) * ζ ^ 46 + ((73 / 50) : ℂ) * ζ ^ 48 + ((81 / 50) : ℂ) * ζ ^ 50 - ((11 / 100) : ℂ) * ζ ^ 52 - ((67 / 25) : ℂ) * ζ ^ 54 - ((42 / 25) : ℂ) * ζ ^ 56)
private theorem row16_transformedGeneratorA_7_0 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        7 0 =
      alternatingSixAmbientRow16TransformedGeneratorA
        7 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((269 / 100) : ℂ) - ((101 / 50) : ℂ) * ζ ^ 2 - ((269 / 100) : ℂ) * ζ ^ 4 + ((207 / 100) : ℂ) * ζ ^ 6 - ((11 / 50) : ℂ) * ζ ^ 8 - ((167 / 50) : ℂ) * ζ ^ 10 - ((123 / 100) : ℂ) * ζ ^ 12 + ((27 / 20) : ℂ) * ζ ^ 14 + ((243 / 50) : ℂ) * ζ ^ 16 - ((89 / 100) : ℂ) * ζ ^ 18 - ((69 / 100) : ℂ) * ζ ^ 20 + ((24 / 25) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 24 - ((107 / 100) : ℂ) * ζ ^ 26 + ((41 / 50) : ℂ) * ζ ^ 28 - ((33 / 100) : ℂ) * ζ ^ 30 - ((221 / 100) : ℂ) * ζ ^ 32 + ((41 / 100) : ℂ) * ζ ^ 34 - ((31 / 50) : ℂ) * ζ ^ 36 + ((23 / 100) : ℂ) * ζ ^ 38 + ((3 / 100) : ℂ) * ζ ^ 40 - ((13 / 100) : ℂ) * ζ ^ 42 - ((77 / 100) : ℂ) * ζ ^ 44 - ((133 / 100) : ℂ) * ζ ^ 46 + ((139 / 100) : ℂ) * ζ ^ 48 + ((101 / 100) : ℂ) * ζ ^ 50 + ((29 / 50) : ℂ) * ζ ^ 52 - ((1 / 5) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_7_1 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        7 1 =
      alternatingSixAmbientRow16TransformedGeneratorA
        7 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((33 / 20) : ℂ) - ((137 / 100) : ℂ) * ζ ^ 2 - ((33 / 20) : ℂ) * ζ ^ 4 + ((41 / 25) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 - ((23 / 25) : ℂ) * ζ ^ 10 - ((7 / 10) : ℂ) * ζ ^ 12 + ((51 / 50) : ℂ) * ζ ^ 14 + ((33 / 20) : ℂ) * ζ ^ 16 + ((169 / 100) : ℂ) * ζ ^ 18 - ((13 / 10) : ℂ) * ζ ^ 20 - ((131 / 100) : ℂ) * ζ ^ 22 + ((17 / 20) : ℂ) * ζ ^ 24 - ((12 / 25) : ℂ) * ζ ^ 26 - ((1 / 5) : ℂ) * ζ ^ 28 + ((33 / 100) : ℂ) * ζ ^ 30 - ((13 / 20) : ℂ) * ζ ^ 32 - ((113 / 100) : ℂ) * ζ ^ 34 - ((4 / 5) : ℂ) * ζ ^ 36 + ((11 / 100) : ℂ) * ζ ^ 38 + ((9 / 5) : ℂ) * ζ ^ 40 + ((19 / 20) : ℂ) * ζ ^ 42 - ((13 / 10) : ℂ) * ζ ^ 44 - ((23 / 25) : ℂ) * ζ ^ 46 + ((3 / 4) : ℂ) * ζ ^ 48 - ((9 / 100) : ℂ) * ζ ^ 50 + ((11 / 20) : ℂ) * ζ ^ 52 + ((49 / 100) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_7_2 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        7 2 =
      alternatingSixAmbientRow16TransformedGeneratorA
        7 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((67 / 20) : ℂ) + ((119 / 25) : ℂ) * ζ ^ 2 + ((293 / 100) : ℂ) * ζ ^ 4 - ((98 / 25) : ℂ) * ζ ^ 6 + ((153 / 20) : ℂ) * ζ ^ 8 + ((99 / 100) : ℂ) * ζ ^ 10 - ((32 / 25) : ℂ) * ζ ^ 12 + ((46 / 25) : ℂ) * ζ ^ 14 - ((361 / 50) : ℂ) * ζ ^ 16 - ((2 / 25) : ℂ) * ζ ^ 18 - ((57 / 50) : ℂ) * ζ ^ 20 - ((403 / 50) : ℂ) * ζ ^ 22 + ((44 / 25) : ℂ) * ζ ^ 24 + ((161 / 25) : ℂ) * ζ ^ 26 - ((641 / 100) : ℂ) * ζ ^ 28 - ((377 / 100) : ℂ) * ζ ^ 30 + ((821 / 100) : ℂ) * ζ ^ 32 + ((13 / 20) : ℂ) * ζ ^ 34 + ((423 / 100) : ℂ) * ζ ^ 36 - ((71 / 100) : ℂ) * ζ ^ 38 + ((41 / 100) : ℂ) * ζ ^ 40 + ((99 / 20) : ℂ) * ζ ^ 42 - ((683 / 100) : ℂ) * ζ ^ 44 - ((89 / 25) : ℂ) * ζ ^ 46 + ((12 / 5) : ℂ) * ζ ^ 48 + ((269 / 100) : ℂ) * ζ ^ 50 - ((119 / 100) : ℂ) * ζ ^ 52 - ((7 / 10) : ℂ) * ζ ^ 54 + ((2 / 25) : ℂ) * ζ ^ 56)
private theorem row16_transformedGeneratorA_7_3 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        7 3 =
      alternatingSixAmbientRow16TransformedGeneratorA
        7 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((146 / 25) : ℂ) - ((351 / 100) : ℂ) * ζ ^ 2 - ((587 / 100) : ℂ) * ζ ^ 4 + ((77 / 20) : ℂ) * ζ ^ 6 - ((51 / 100) : ℂ) * ζ ^ 8 - ((267 / 100) : ℂ) * ζ ^ 10 - ((689 / 100) : ℂ) * ζ ^ 12 + ((59 / 100) : ℂ) * ζ ^ 14 + ((891 / 100) : ℂ) * ζ ^ 16 + ((223 / 100) : ℂ) * ζ ^ 18 - ((2 / 5) : ℂ) * ζ ^ 20 + ((219 / 100) : ℂ) * ζ ^ 22 + ((13 / 5) : ℂ) * ζ ^ 24 - ((97 / 50) : ℂ) * ζ ^ 26 - ((41 / 10) : ℂ) * ζ ^ 28 + ((377 / 100) : ℂ) * ζ ^ 30 + ((321 / 100) : ℂ) * ζ ^ 32 - ((293 / 100) : ℂ) * ζ ^ 34 - ((841 / 100) : ℂ) * ζ ^ 36 - ((53 / 25) : ℂ) * ζ ^ 38 + ((121 / 20) : ℂ) * ζ ^ 40 + ((89 / 50) : ℂ) * ζ ^ 42 - ((11 / 20) : ℂ) * ζ ^ 44 - ((309 / 100) : ℂ) * ζ ^ 46 + ((217 / 100) : ℂ) * ζ ^ 48 - ((63 / 100) : ℂ) * ζ ^ 50 - ((49 / 50) : ℂ) * ζ ^ 52 + ((109 / 100) : ℂ) * ζ ^ 54 + ((29 / 25) : ℂ) * ζ ^ 56)
private theorem row16_transformedGeneratorA_7_4 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        7 4 =
      alternatingSixAmbientRow16TransformedGeneratorA
        7 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((757 / 1100) : ℂ) - ((268 / 275) : ℂ) * ζ ^ 2 - ((757 / 1100) : ℂ) * ζ ^ 4 + ((933 / 1100) : ℂ) * ζ ^ 6 - ((26 / 275) : ℂ) * ζ ^ 8 - ((252 / 275) : ℂ) * ζ ^ 10 - ((119 / 220) : ℂ) * ζ ^ 12 + ((1091 / 1100) : ℂ) * ζ ^ 14 + ((328 / 275) : ℂ) * ζ ^ 16 - ((483 / 1100) : ℂ) * ζ ^ 18 - ((1261 / 1100) : ℂ) * ζ ^ 20 + ((391 / 550) : ℂ) * ζ ^ 22 - ((647 / 1100) : ℂ) * ζ ^ 24 + ((19 / 1100) : ℂ) * ζ ^ 26 + ((27 / 25) : ℂ) * ζ ^ 28 - ((201 / 220) : ℂ) * ζ ^ 30 - ((147 / 220) : ℂ) * ζ ^ 32 + ((1013 / 1100) : ℂ) * ζ ^ 34 + ((71 / 50) : ℂ) * ζ ^ 36 + ((289 / 1100) : ℂ) * ζ ^ 38 - ((1839 / 1100) : ℂ) * ζ ^ 40 + ((247 / 1100) : ℂ) * ζ ^ 42 + ((681 / 1100) : ℂ) * ζ ^ 44 - ((491 / 1100) : ℂ) * ζ ^ 46 - ((277 / 1100) : ℂ) * ζ ^ 48 + ((227 / 1100) : ℂ) * ζ ^ 50 + ((4 / 25) : ℂ) * ζ ^ 52 + ((61 / 550) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_7_5 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        7 5 =
      alternatingSixAmbientRow16TransformedGeneratorA
        7 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((1433 / 1100) : ℂ) - ((147 / 100) : ℂ) * ζ ^ 2 - ((1433 / 1100) : ℂ) * ζ ^ 4 + ((7 / 10) : ℂ) * ζ ^ 6 - ((1791 / 1100) : ℂ) * ζ ^ 8 + ((142 / 275) : ℂ) * ζ ^ 10 + ((1423 / 550) : ℂ) * ζ ^ 12 + ((823 / 550) : ℂ) * ζ ^ 14 - ((133 / 1100) : ℂ) * ζ ^ 16 + ((887 / 1100) : ℂ) * ζ ^ 18 + ((153 / 550) : ℂ) * ζ ^ 20 - ((17 / 44) : ℂ) * ζ ^ 22 - ((1439 / 1100) : ℂ) * ζ ^ 24 - ((29 / 55) : ℂ) * ζ ^ 26 + ((718 / 275) : ℂ) * ζ ^ 28 - ((1603 / 1100) : ℂ) * ζ ^ 30 - ((1317 / 1100) : ℂ) * ζ ^ 32 - ((123 / 1100) : ℂ) * ζ ^ 34 - ((27 / 110) : ℂ) * ζ ^ 36 + ((501 / 1100) : ℂ) * ζ ^ 38 - ((13 / 55) : ℂ) * ζ ^ 40 + ((243 / 1100) : ℂ) * ζ ^ 42 - ((2 / 275) : ℂ) * ζ ^ 44 - ((323 / 550) : ℂ) * ζ ^ 46 - ((39 / 100) : ℂ) * ζ ^ 48 + ((1 / 220) : ℂ) * ζ ^ 50 + ((1179 / 1100) : ℂ) * ζ ^ 52 + ((447 / 1100) : ℂ) * ζ ^ 54)
private theorem row16_transformedGeneratorA_7_6 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        7 6 =
      alternatingSixAmbientRow16TransformedGeneratorA
        7 6 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (-((57 / 20) : ℂ) - ((89 / 50) : ℂ) * ζ ^ 2 + ((327 / 100) : ℂ) * ζ ^ 4 - ((17 / 50) : ℂ) * ζ ^ 6 + ((333 / 100) : ℂ) * ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 10 - ((104 / 25) : ℂ) * ζ ^ 12 + ((183 / 25) : ℂ) * ζ ^ 14 + ((17 / 25) : ℂ) * ζ ^ 16 - ((179 / 50) : ℂ) * ζ ^ 18 - ((321 / 50) : ℂ) * ζ ^ 20 - ((43 / 25) : ℂ) * ζ ^ 22 + ((54 / 25) : ℂ) * ζ ^ 24 + ((53 / 50) : ℂ) * ζ ^ 26 - ((101 / 100) : ℂ) * ζ ^ 28 + ((37 / 100) : ℂ) * ζ ^ 30 + ((481 / 100) : ℂ) * ζ ^ 32 - ((973 / 100) : ℂ) * ζ ^ 34 + ((89 / 100) : ℂ) * ζ ^ 36 + ((949 / 100) : ℂ) * ζ ^ 38 + ((437 / 100) : ℂ) * ζ ^ 40 - ((119 / 100) : ℂ) * ζ ^ 42 - ((659 / 100) : ℂ) * ζ ^ 44 - ((19 / 50) : ℂ) * ζ ^ 46 + ((46 / 25) : ℂ) * ζ ^ 48 - ((51 / 20) : ℂ) * ζ ^ 50 - ((163 / 100) : ℂ) * ζ ^ 52 + ((52 / 25) : ℂ) * ζ ^ 54 - ((2 / 25) : ℂ) * ζ ^ 56)
private theorem row16_transformedGeneratorA_7_7 :
    (alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis)
        7 7 =
      alternatingSixAmbientRow16TransformedGeneratorA
        7 7 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow16Eigenbasis,
      alternatingSixAmbientRow16EigenbasisInverse,
      alternatingSixFiveAmbient_row16_matrixA,
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row16 (((146 / 25) : ℂ) - ((93 / 20) : ℂ) * ζ ^ 2 - ((581 / 100) : ℂ) * ζ ^ 4 + ((673 / 100) : ℂ) * ζ ^ 6 + ((191 / 100) : ℂ) * ζ ^ 8 - ((241 / 100) : ℂ) * ζ ^ 10 - ((107 / 20) : ℂ) * ζ ^ 12 - ((303 / 100) : ℂ) * ζ ^ 14 + ((159 / 20) : ℂ) * ζ ^ 16 + ((447 / 100) : ℂ) * ζ ^ 18 - ((74 / 25) : ℂ) * ζ ^ 20 + ((199 / 100) : ℂ) * ζ ^ 22 + ((238 / 25) : ℂ) * ζ ^ 24 - ((191 / 50) : ℂ) * ζ ^ 26 - ((611 / 50) : ℂ) * ζ ^ 28 - ((93 / 100) : ℂ) * ζ ^ 30 + ((11 / 4) : ℂ) * ζ ^ 32 + ((379 / 100) : ℂ) * ζ ^ 34 - ((409 / 100) : ℂ) * ζ ^ 36 - ((23 / 10) : ℂ) * ζ ^ 38 + ((419 / 100) : ℂ) * ζ ^ 40 - ((99 / 50) : ℂ) * ζ ^ 42 - ((363 / 100) : ℂ) * ζ ^ 44 + ((123 / 100) : ℂ) * ζ ^ 46 + ((399 / 100) : ℂ) * ζ ^ 48 + ((49 / 20) : ℂ) * ζ ^ 50 + ((69 / 50) : ℂ) * ζ ^ 52 - ((147 / 100) : ℂ) * ζ ^ 54 - ((29 / 25) : ℂ) * ζ ^ 56)
/-- Exact conjugation formula for the row 16 first
generator. -/
theorem alternatingSixAmbientRow16TransformedGeneratorA_eq :
    alternatingSixAmbientRow16EigenbasisInverse *
        alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixAmbientRow16Eigenbasis =
      alternatingSixAmbientRow16TransformedGeneratorA := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row16_transformedGeneratorA_0_0
  · exact row16_transformedGeneratorA_0_1
  · exact row16_transformedGeneratorA_0_2
  · exact row16_transformedGeneratorA_0_3
  · exact row16_transformedGeneratorA_0_4
  · exact row16_transformedGeneratorA_0_5
  · exact row16_transformedGeneratorA_0_6
  · exact row16_transformedGeneratorA_0_7
  · exact row16_transformedGeneratorA_1_0
  · exact row16_transformedGeneratorA_1_1
  · exact row16_transformedGeneratorA_1_2
  · exact row16_transformedGeneratorA_1_3
  · exact row16_transformedGeneratorA_1_4
  · exact row16_transformedGeneratorA_1_5
  · exact row16_transformedGeneratorA_1_6
  · exact row16_transformedGeneratorA_1_7
  · exact row16_transformedGeneratorA_2_0
  · exact row16_transformedGeneratorA_2_1
  · exact row16_transformedGeneratorA_2_2
  · exact row16_transformedGeneratorA_2_3
  · exact row16_transformedGeneratorA_2_4
  · exact row16_transformedGeneratorA_2_5
  · exact row16_transformedGeneratorA_2_6
  · exact row16_transformedGeneratorA_2_7
  · exact row16_transformedGeneratorA_3_0
  · exact row16_transformedGeneratorA_3_1
  · exact row16_transformedGeneratorA_3_2
  · exact row16_transformedGeneratorA_3_3
  · exact row16_transformedGeneratorA_3_4
  · exact row16_transformedGeneratorA_3_5
  · exact row16_transformedGeneratorA_3_6
  · exact row16_transformedGeneratorA_3_7
  · exact row16_transformedGeneratorA_4_0
  · exact row16_transformedGeneratorA_4_1
  · exact row16_transformedGeneratorA_4_2
  · exact row16_transformedGeneratorA_4_3
  · exact row16_transformedGeneratorA_4_4
  · exact row16_transformedGeneratorA_4_5
  · exact row16_transformedGeneratorA_4_6
  · exact row16_transformedGeneratorA_4_7
  · exact row16_transformedGeneratorA_5_0
  · exact row16_transformedGeneratorA_5_1
  · exact row16_transformedGeneratorA_5_2
  · exact row16_transformedGeneratorA_5_3
  · exact row16_transformedGeneratorA_5_4
  · exact row16_transformedGeneratorA_5_5
  · exact row16_transformedGeneratorA_5_6
  · exact row16_transformedGeneratorA_5_7
  · exact row16_transformedGeneratorA_6_0
  · exact row16_transformedGeneratorA_6_1
  · exact row16_transformedGeneratorA_6_2
  · exact row16_transformedGeneratorA_6_3
  · exact row16_transformedGeneratorA_6_4
  · exact row16_transformedGeneratorA_6_5
  · exact row16_transformedGeneratorA_6_6
  · exact row16_transformedGeneratorA_6_7
  · exact row16_transformedGeneratorA_7_0
  · exact row16_transformedGeneratorA_7_1
  · exact row16_transformedGeneratorA_7_2
  · exact row16_transformedGeneratorA_7_3
  · exact row16_transformedGeneratorA_7_4
  · exact row16_transformedGeneratorA_7_5
  · exact row16_transformedGeneratorA_7_6
  · exact row16_transformedGeneratorA_7_7


end InductiveMcKay
end McKayConjecture
