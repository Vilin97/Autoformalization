/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixDegreeFourSixEigenvalues
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixDataDegreeFourSix

/-!
# Checked diagonal data for ambient row 14

This generated module records an exact eigenbasis for the second generator
and the first generator in that basis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Eigenvalue block labels for row 14. -/
def alternatingSixAmbientRow14EigenvalueLabel :
    Fin 6 → Fin 4 :=
  ![0, 1, 1, 2, 2, 3]

/-- Second-generator eigenvalues, including their multiplicities. -/
def alternatingSixAmbientRow14GeneratorBEigenvalue :
    Fin 6 → ℂ :=
  fun i ↦
    alternatingSixOrderEightOddEigenvalue
      (alternatingSixAmbientRow14EigenvalueLabel i)

/-- Diagonal form of the row 14 second generator. -/
def alternatingSixAmbientRow14GeneratorBDiagonal :
    Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.diagonal
    alternatingSixAmbientRow14GeneratorBEigenvalue

/-- Checked eigenbasis for the row 14 second generator. -/
def alternatingSixAmbientRow14Eigenbasis :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [((2 / 11), 0), ((-3 / 11), 3), ((1 / 11), 5), ((-3 / 11), 7), ((4 / 11), 10), ((1 / 11), 15), ((3 / 11), 19), ((-2 / 11), 20), ((3 / 11), 23), ((-3 / 11), 25), ((-8 / 11), 30), ((-3 / 11), 31)],
      alternatingSixCyclotomicValue [((-3 / 11), 0), ((8 / 11), 3), ((2 / 11), 5), ((8 / 11), 7), ((1 / 11), 10), ((-4 / 11), 15), ((-8 / 11), 19), ((1 / 11), 20), ((-8 / 11), 23), ((-2 / 11), 25), ((-3 / 11), 30), ((8 / 11), 31)],
      alternatingSixCyclotomicValue [((-4 / 3), 0), ((1 / 3), 3), ((1 / 3), 7), ((-4 / 3), 10), ((-2 / 3), 15), ((-1 / 3), 19), ((2 / 3), 20), ((-1 / 3), 23), ((2 / 3), 30), ((1 / 3), 31)],
      alternatingSixCyclotomicValue [(1, 0), (1, 10), (-1, 20), (-1, 30)],
      alternatingSixCyclotomicValue [(-1, 0), (1, 10), (1, 20), (-1, 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 2), 3), ((-1 / 2), 7), ((-1 / 2), 10), ((1 / 2), 19), ((1 / 2), 20), ((1 / 2), 23), ((1 / 2), 25), (1, 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((-3 / 11), 0), ((-4 / 11), 3), ((1 / 11), 5), ((-4 / 11), 7), ((-1 / 11), 10), ((3 / 11), 15), ((4 / 11), 19), ((4 / 11), 23), ((3 / 11), 25), ((-5 / 11), 30), ((-4 / 11), 31)],
      alternatingSixCyclotomicValue [((3 / 22), 0), ((-1 / 22), 3), ((-3 / 11), 5), ((-1 / 22), 7), ((-9 / 22), 10), ((5 / 11), 15), ((1 / 22), 19), ((-5 / 22), 20), ((1 / 22), 23), ((1 / 2), 25), ((3 / 11), 30), ((-1 / 22), 31)],
      alternatingSixCyclotomicValue [(-1, 0), ((-2 / 3), 3), ((1 / 3), 5), ((-2 / 3), 7), ((1 / 3), 10), ((1 / 3), 15), ((2 / 3), 19), ((2 / 3), 23), ((1 / 3), 25), ((1 / 3), 30), ((-2 / 3), 31)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 2), 3), (-1, 5), ((1 / 2), 7), ((1 / 2), 10), ((-1 / 2), 19), ((-1 / 2), 20), ((-1 / 2), 23), ((1 / 2), 25), (-1, 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 2), 3), ((-1 / 2), 7), ((1 / 2), 10), ((1 / 2), 19), ((1 / 2), 20), ((1 / 2), 23), ((1 / 2), 25), ((-1 / 2), 31)]],
    ![alternatingSixCyclotomicValue [((1 / 2), 0), (-1, 3), ((1 / 2), 5), (-1, 7), ((1 / 2), 15), (1, 19), (1, 23), ((-1 / 2), 25), ((-1 / 2), 30), (-1, 31)],
      alternatingSixCyclotomicValue [((5 / 11), 0), ((7 / 11), 3), ((6 / 11), 5), ((7 / 11), 7), ((6 / 11), 10), ((-7 / 11), 19), ((4 / 11), 20), ((-7 / 11), 23), ((-3 / 11), 25), ((-2 / 11), 30), ((7 / 11), 31)],
      alternatingSixCyclotomicValue [((3 / 22), 0), ((2 / 11), 3), ((-1 / 22), 5), ((2 / 11), 7), ((6 / 11), 10), ((-3 / 22), 15), ((-2 / 11), 19), ((-2 / 11), 23), ((-3 / 22), 25), ((-17 / 22), 30), ((2 / 11), 31)],
      alternatingSixCyclotomicValue [((-1 / 3), 3), ((-4 / 3), 5), ((-1 / 3), 7), ((2 / 3), 10), ((-4 / 3), 15), ((1 / 3), 19), ((1 / 3), 23), ((-1 / 3), 25), ((-1 / 3), 30), ((-1 / 3), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), (1, 3), ((3 / 2), 5), (1, 7), ((1 / 2), 15), (-1, 19), (-1, 23), ((-1 / 2), 25), ((1 / 2), 30), (1, 31)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 2), 5), ((1 / 2), 15), ((1 / 2), 25), ((1 / 2), 30)]],
    ![alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(-1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(-1, 0)]],
    ![alternatingSixCyclotomicValue [(-1, 3), (-1, 5), (-1, 7), (1, 19), (1, 23), (1, 25), (-1, 31)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue []],
    ![alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)]]
  ]

/-- Checked inverse of the row 14 eigenbasis. -/
def alternatingSixAmbientRow14EigenbasisInverse :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((3 / 2), 0), ((7 / 4), 3), (-1, 5), ((7 / 4), 7), ((-5 / 4), 10), ((-3 / 4), 15), ((-7 / 4), 19), ((-1 / 4), 20), ((-7 / 4), 23), ((5 / 4), 25), (1, 30), ((7 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 3), ((1 / 2), 5), ((-1 / 2), 7), ((-1 / 4), 10), ((-1 / 4), 15), ((1 / 2), 19), ((1 / 2), 23), ((-1 / 4), 25), ((-1 / 4), 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((7 / 4), 0), (2, 3), ((-5 / 4), 5), (2, 7), ((-5 / 2), 10), (-2, 15), (-2, 19), ((1 / 2), 20), (-2, 23), ((9 / 4), 25), (1, 30), (2, 31)],
      alternatingSixCyclotomicValue [(-1, 0), ((5 / 4), 3), ((-3 / 2), 5), ((5 / 4), 7), ((1 / 2), 15), ((-5 / 4), 19), ((5 / 2), 20), ((-5 / 4), 23), ((1 / 4), 25), (-2, 30), ((5 / 4), 31)],
      alternatingSixCyclotomicValue [(1, 0), ((-1 / 2), 3), ((3 / 4), 5), ((-1 / 2), 7), ((-1 / 4), 10), ((-3 / 4), 15), ((1 / 2), 19), (-1, 20), ((1 / 2), 23), ((1 / 2), 25), (1, 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [(1, 0), (1, 3), ((-3 / 4), 5), (1, 7), ((-5 / 4), 10), ((-5 / 4), 15), (-1, 19), (-1, 23), ((3 / 2), 25), (1, 30), (1, 31)]],
    ![alternatingSixCyclotomicValue [((-3 / 2), 0), ((7 / 4), 3), ((-3 / 4), 5), ((7 / 4), 7), ((7 / 4), 10), ((-3 / 4), 15), ((-7 / 4), 19), ((9 / 4), 20), ((-7 / 4), 23), (2, 25), ((-9 / 4), 30), ((7 / 4), 31)],
      alternatingSixCyclotomicValue [((5 / 4), 0), ((1 / 4), 3), ((-1 / 2), 5), ((1 / 4), 7), ((-5 / 4), 10), ((-1 / 4), 19), ((-5 / 4), 20), ((-1 / 4), 23), ((-3 / 4), 25), (1, 30), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [(-1, 0), ((9 / 4), 3), ((-11 / 4), 5), ((9 / 4), 7), ((-3 / 4), 10), ((-1 / 4), 15), ((-9 / 4), 19), ((9 / 4), 20), ((-9 / 4), 23), ((3 / 2), 25), ((-7 / 4), 30), ((9 / 4), 31)],
      alternatingSixCyclotomicValue [((-3 / 2), 0), ((-1 / 2), 3), ((-1 / 2), 5), ((-1 / 2), 7), ((3 / 2), 10), (3, 15), ((1 / 2), 19), ((1 / 2), 20), ((1 / 2), 23), (-2, 25), (-1, 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((7 / 4), 0), ((1 / 2), 3), ((-1 / 4), 5), ((1 / 2), 7), ((-3 / 2), 10), ((-3 / 4), 15), ((-1 / 2), 19), ((1 / 2), 20), ((-1 / 2), 23), ((5 / 4), 25), ((5 / 4), 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((-5 / 4), 0), ((1 / 2), 3), ((-5 / 4), 5), ((1 / 2), 7), (-1, 10), ((-1 / 4), 15), ((-1 / 2), 19), (2, 20), ((-1 / 2), 23), ((5 / 4), 25), ((-3 / 4), 30), ((1 / 2), 31)]],
    ![alternatingSixCyclotomicValue [((1 / 2), 0), ((5 / 4), 3), ((1 / 2), 5), ((5 / 4), 7), ((3 / 4), 10), ((3 / 4), 15), ((-5 / 4), 19), ((3 / 4), 20), ((-5 / 4), 23), ((-3 / 4), 25), ((-3 / 2), 30), ((5 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 2), 5), ((-3 / 4), 10), ((-3 / 4), 15), ((1 / 4), 25), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-7 / 4), 0), ((1 / 2), 3), ((-7 / 4), 5), ((1 / 2), 7), (1, 15), ((-1 / 2), 19), (2, 20), ((-1 / 2), 23), ((1 / 4), 25), (-1, 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((-3 / 2), 0), ((-3 / 4), 3), ((3 / 4), 5), ((-3 / 4), 7), (2, 10), ((5 / 4), 15), ((3 / 4), 19), ((3 / 4), 23), ((-3 / 2), 25), (-1, 30), ((-3 / 4), 31)],
      alternatingSixCyclotomicValue [(1, 0), (1, 3), ((-1 / 4), 5), (1, 7), ((-1 / 4), 10), ((-1 / 4), 15), (-1, 19), ((1 / 2), 20), (-1, 23), (1, 25), (1, 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), (-1, 5), ((-1 / 4), 10), (1, 15), ((3 / 2), 20), ((3 / 4), 25)]],
    ![alternatingSixCyclotomicValue [((3 / 2), 0), ((-3 / 2), 3), ((3 / 4), 5), ((-3 / 2), 7), ((-1 / 2), 10), ((3 / 2), 15), ((3 / 2), 19), ((-11 / 4), 20), ((3 / 2), 23), ((-5 / 2), 25), ((3 / 2), 30), ((-3 / 2), 31)],
      alternatingSixCyclotomicValue [((-3 / 2), 0), ((-1 / 2), 3), ((1 / 4), 5), ((-1 / 2), 7), ((3 / 4), 10), ((-1 / 4), 15), ((1 / 2), 19), ((3 / 2), 20), ((1 / 2), 23), ((1 / 2), 25), (-1, 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), (-3, 3), ((5 / 2), 5), (-3, 7), ((7 / 4), 10), ((7 / 4), 15), (3, 19), (-2, 20), (3, 23), ((-9 / 4), 25), (1, 30), (-3, 31)],
      alternatingSixCyclotomicValue [((7 / 4), 0), ((-1 / 2), 3), (2, 5), ((-1 / 2), 7), (-1, 10), ((-5 / 2), 15), ((1 / 2), 19), ((-3 / 2), 20), ((1 / 2), 23), (1, 25), ((5 / 4), 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((-5 / 4), 0), ((1 / 4), 3), ((1 / 4), 7), ((3 / 2), 10), ((3 / 4), 15), ((-1 / 4), 19), ((1 / 2), 20), ((-1 / 4), 23), ((-5 / 4), 25), ((-3 / 2), 30), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-3 / 4), 3), (1, 5), ((-3 / 4), 7), ((3 / 2), 10), ((5 / 4), 15), ((3 / 4), 19), ((-3 / 2), 20), ((3 / 4), 23), ((-5 / 4), 25), ((1 / 2), 30), ((-3 / 4), 31)]],
    ![alternatingSixCyclotomicValue [((-3 / 2), 0), ((-7 / 4), 3), (1, 5), ((-7 / 4), 7), ((5 / 4), 10), ((3 / 4), 15), ((7 / 4), 19), ((1 / 4), 20), ((7 / 4), 23), ((-5 / 4), 25), (-1, 30), ((-7 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 2), 3), ((-1 / 2), 5), ((1 / 2), 7), ((1 / 4), 10), ((1 / 4), 15), ((-1 / 2), 19), ((-1 / 2), 23), ((1 / 4), 25), ((1 / 4), 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((-7 / 4), 0), (-2, 3), ((5 / 4), 5), (-2, 7), ((5 / 2), 10), (2, 15), (2, 19), ((-1 / 2), 20), (2, 23), ((-9 / 4), 25), (-1, 30), (-2, 31)],
      alternatingSixCyclotomicValue [((3 / 2), 0), ((-5 / 4), 3), ((3 / 2), 5), ((-5 / 4), 7), ((-1 / 2), 15), ((5 / 4), 19), ((-5 / 2), 20), ((5 / 4), 23), ((-1 / 4), 25), (2, 30), ((-5 / 4), 31)],
      alternatingSixCyclotomicValue [(-1, 0), ((1 / 2), 3), ((-3 / 4), 5), ((1 / 2), 7), ((1 / 4), 10), ((3 / 4), 15), ((-1 / 2), 19), (1, 20), ((-1 / 2), 23), ((-1 / 2), 25), (-1, 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), (-1, 3), ((3 / 4), 5), (-1, 7), ((5 / 4), 10), ((5 / 4), 15), (1, 19), (1, 23), ((-3 / 2), 25), (-1, 30), (-1, 31)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 0), ((-5 / 4), 3), ((-1 / 2), 5), ((-5 / 4), 7), ((-3 / 4), 10), ((-3 / 4), 15), ((5 / 4), 19), ((-3 / 4), 20), ((5 / 4), 23), ((3 / 4), 25), ((3 / 2), 30), ((-5 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 2), 5), ((3 / 4), 10), ((3 / 4), 15), ((-1 / 4), 25), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((7 / 4), 0), ((-1 / 2), 3), ((7 / 4), 5), ((-1 / 2), 7), (-1, 15), ((1 / 2), 19), (-2, 20), ((1 / 2), 23), ((-1 / 4), 25), (1, 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [(1, 0), ((3 / 4), 3), ((-3 / 4), 5), ((3 / 4), 7), (-2, 10), ((-5 / 4), 15), ((-3 / 4), 19), ((-3 / 4), 23), ((3 / 2), 25), (1, 30), ((3 / 4), 31)],
      alternatingSixCyclotomicValue [(-1, 0), (-1, 3), ((1 / 4), 5), (-1, 7), ((1 / 4), 10), ((1 / 4), 15), (1, 19), ((-1 / 2), 20), (1, 23), (-1, 25), (-1, 31)],
      alternatingSixCyclotomicValue [(1, 0), (1, 5), ((1 / 4), 10), (-1, 15), ((-3 / 2), 20), ((-3 / 4), 25)]]
  ]

/-- The row 14 first generator in the checked diagonal basis. -/
def alternatingSixAmbientRow14TransformedGeneratorA :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((1 / 4), 10), ((1 / 4), 15), ((-1 / 4), 25), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-9 / 44), 0), ((3 / 22), 3), ((5 / 22), 5), ((3 / 22), 7), ((-1 / 4), 10), ((1 / 11), 15), ((-3 / 22), 19), ((7 / 44), 20), ((-3 / 22), 23), ((-1 / 11), 25), ((5 / 22), 30), ((3 / 22), 31)],
      alternatingSixCyclotomicValue [((3 / 22), 0), ((1 / 44), 3), ((1 / 22), 5), ((1 / 44), 7), ((-1 / 44), 10), ((-1 / 44), 15), ((-1 / 44), 19), ((1 / 11), 20), ((-1 / 44), 23), ((-1 / 11), 25), ((7 / 44), 30), ((1 / 44), 31)],
      alternatingSixCyclotomicValue [((-1 / 12), 0), ((-2 / 3), 3), ((-1 / 2), 5), ((-2 / 3), 7), ((-1 / 12), 10), ((1 / 3), 15), ((2 / 3), 19), ((-1 / 12), 20), ((2 / 3), 23), ((1 / 2), 25), ((1 / 6), 30), ((-2 / 3), 31)],
      alternatingSixCyclotomicValue [((1 / 2), 3), ((1 / 4), 5), ((1 / 2), 7), ((1 / 4), 10), ((-1 / 2), 15), ((-1 / 2), 19), ((-1 / 2), 23), ((-1 / 2), 25), ((-1 / 4), 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 3), ((1 / 4), 7), ((-1 / 4), 10), ((-1 / 4), 15), ((-1 / 4), 19), ((-1 / 4), 23), ((1 / 4), 30), ((1 / 4), 31)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 3), ((1 / 4), 7), ((-1 / 4), 10), ((-1 / 4), 19), ((-1 / 4), 20), ((-1 / 4), 23), ((-1 / 4), 25), ((1 / 2), 30), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((-5 / 11), 0), ((1 / 11), 5), ((-3 / 11), 10), ((1 / 22), 15), ((3 / 11), 20), ((1 / 11), 25), ((5 / 11), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((13 / 44), 3), ((1 / 22), 5), ((13 / 44), 7), ((-7 / 44), 10), ((-7 / 22), 15), ((-13 / 44), 19), ((13 / 44), 20), ((-13 / 44), 23), ((1 / 44), 25), ((1 / 11), 30), ((13 / 44), 31)],
      alternatingSixCyclotomicValue [((1 / 2), 5), ((-1 / 2), 25)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 3), ((-1 / 4), 7), ((-1 / 4), 10), ((1 / 4), 19), ((1 / 4), 20), ((1 / 4), 23), ((1 / 4), 25), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-3 / 4), 3), ((1 / 2), 5), ((-3 / 4), 7), ((-1 / 4), 10), ((1 / 2), 15), ((3 / 4), 19), ((-1 / 4), 20), ((3 / 4), 23), ((-3 / 4), 25), ((-3 / 4), 31)]],
    ![alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 4), 5), ((-1 / 4), 10), ((-1 / 2), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((9 / 22), 0), ((9 / 44), 3), ((3 / 11), 5), ((9 / 44), 7), ((5 / 11), 10), ((-3 / 11), 15), ((-9 / 44), 19), ((-1 / 11), 20), ((-9 / 44), 23), ((-9 / 44), 25), ((9 / 44), 31)],
      alternatingSixCyclotomicValue [((5 / 11), 0), ((-1 / 4), 3), ((-15 / 44), 5), ((-1 / 4), 7), ((1 / 44), 10), ((-1 / 22), 15), ((1 / 4), 19), ((-3 / 11), 20), ((1 / 4), 23), ((7 / 44), 25), ((-9 / 44), 30), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 3), 0), ((-1 / 12), 3), ((-1 / 12), 7), ((-1 / 6), 10), ((-1 / 3), 15), ((1 / 12), 19), ((-1 / 6), 20), ((1 / 12), 23), ((-3 / 4), 25), ((1 / 3), 30), ((-1 / 12), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 5), ((-1 / 4), 10), ((1 / 2), 15), ((1 / 2), 20)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 4), 3), ((-1 / 4), 5), ((-1 / 4), 7), ((-1 / 4), 10), ((1 / 4), 19), ((1 / 2), 20), ((1 / 4), 23), ((1 / 4), 25), ((1 / 4), 30), ((-1 / 4), 31)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 3), ((-1 / 4), 5), ((-1 / 2), 7), ((-1 / 4), 10), ((1 / 4), 15), ((1 / 2), 19), ((1 / 2), 20), ((1 / 2), 23), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((-7 / 11), 0), ((-1 / 11), 3), ((-5 / 44), 5), ((-1 / 11), 7), ((-4 / 11), 10), ((1 / 4), 15), ((1 / 11), 19), ((13 / 22), 20), ((1 / 11), 23), ((19 / 44), 25), ((5 / 11), 30), ((-1 / 11), 31)],
      alternatingSixCyclotomicValue [((7 / 44), 0), ((1 / 22), 3), ((5 / 44), 5), ((1 / 22), 7), ((-5 / 44), 10), ((15 / 44), 15), ((-1 / 22), 19), ((-1 / 22), 23), ((1 / 11), 25), ((19 / 44), 30), ((1 / 22), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 3), ((1 / 4), 5), ((1 / 2), 7), ((-1 / 4), 15), ((-1 / 2), 19), ((1 / 2), 20), ((-1 / 2), 23), ((-1 / 4), 25), ((1 / 2), 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 4), 5), ((-1 / 2), 10), ((1 / 4), 15), ((-3 / 4), 20), ((1 / 2), 25), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 5), ((-1 / 4), 10), ((1 / 4), 15), ((1 / 2), 20), ((1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 4), 10), ((-1 / 4), 15), ((1 / 2), 20), ((1 / 4), 25), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-25 / 44), 0), ((-3 / 22), 3), ((-3 / 11), 5), ((-3 / 22), 7), ((-27 / 44), 10), ((3 / 22), 15), ((3 / 22), 19), ((9 / 44), 20), ((3 / 22), 23), ((6 / 11), 25), ((6 / 11), 30), ((-3 / 22), 31)],
      alternatingSixCyclotomicValue [((-3 / 22), 0), ((-13 / 44), 3), ((2 / 11), 5), ((-13 / 44), 7), ((-1 / 44), 10), ((19 / 44), 15), ((13 / 44), 19), ((3 / 22), 20), ((13 / 44), 23), ((-1 / 22), 25), ((13 / 44), 30), ((-13 / 44), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 6), 3), ((2 / 3), 5), ((1 / 6), 7), ((-7 / 12), 10), ((1 / 6), 15), ((-1 / 6), 19), ((1 / 4), 20), ((-1 / 6), 23), ((-1 / 3), 25), ((2 / 3), 30), ((1 / 6), 31)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 2), 3), ((-1 / 4), 5), ((-1 / 2), 7), ((1 / 4), 10), ((1 / 2), 19), ((-1 / 2), 20), ((1 / 2), 23), ((1 / 2), 25), ((-3 / 4), 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 4), 3), ((-1 / 4), 7), ((-1 / 4), 10), ((1 / 4), 15), ((1 / 4), 19), ((1 / 2), 20), ((1 / 4), 23), ((1 / 4), 30), ((-1 / 4), 31)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 5), ((-1 / 4), 10), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((2 / 11), 0), ((3 / 44), 3), ((-7 / 22), 5), ((3 / 44), 7), ((1 / 22), 10), ((-1 / 22), 15), ((-3 / 44), 19), ((-1 / 11), 20), ((-3 / 44), 23), ((1 / 44), 25), ((-1 / 22), 30), ((3 / 44), 31)],
      alternatingSixCyclotomicValue [((-2 / 11), 0), ((-9 / 44), 3), ((-3 / 44), 5), ((-9 / 44), 7), ((-3 / 44), 10), ((9 / 44), 19), ((-1 / 22), 20), ((9 / 44), 23), ((7 / 44), 25), ((1 / 44), 30), ((-9 / 44), 31)],
      alternatingSixCyclotomicValue [((-1 / 12), 3), ((1 / 6), 5), ((-1 / 12), 7), ((1 / 6), 10), ((1 / 6), 15), ((1 / 12), 19), ((1 / 12), 23), ((-1 / 12), 25), ((1 / 6), 30), ((-1 / 12), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 5), ((-1 / 4), 10)],
      alternatingSixCyclotomicValue [((1 / 4), 3), ((1 / 4), 5), ((1 / 4), 7), ((-1 / 4), 10), ((-1 / 4), 19), ((-1 / 4), 23), ((-1 / 4), 25), ((1 / 4), 30), ((1 / 4), 31)]]
  ]

macro "close_cyclotomic_row14" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)


private theorem row14_eigenbasisInverse_mul_0_0 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        0 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((1 / 8) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 3 + ((1 / 8) : ℂ) * ζ ^ 4 - ((13 / 4) : ℂ) * ζ ^ 5 - ((5 / 4) : ℂ) * ζ ^ 6 + ((13 / 8) : ℂ) * ζ ^ 8 + ((13 / 4) : ℂ) * ζ ^ 9 - (5 : ℂ) * ζ ^ 10 - ((1 / 8) : ℂ) * ζ ^ 13 + ((15 / 4) : ℂ) * ζ ^ 14 - ((5 / 4) : ℂ) * ζ ^ 15 - ((9 / 8) : ℂ) * ζ ^ 18 + ((5 / 4) : ℂ) * ζ ^ 19 + ((29 / 8) : ℂ) * ζ ^ 20 + ((5 / 4) : ℂ) * ζ ^ 22 - ζ ^ 23 - ((29 / 8) : ℂ) * ζ ^ 24 + ((27 / 8) : ℂ) * ζ ^ 25 + ((5 / 4) : ℂ) * ζ ^ 26 - ((3 / 4) : ℂ) * ζ ^ 28 - ((27 / 8) : ℂ) * ζ ^ 29 - ((5 / 4) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_0_1 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        0 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((91 / 44) : ℂ) + ((69 / 44) : ℂ) * ζ ^ 3 - ((91 / 44) : ℂ) * ζ ^ 4 + ((21 / 22) : ℂ) * ζ ^ 5 + ((43 / 44) : ℂ) * ζ ^ 6 + ((113 / 44) : ℂ) * ζ ^ 8 - ((21 / 22) : ℂ) * ζ ^ 9 + ((9 / 44) : ℂ) * ζ ^ 10 + ((69 / 44) : ℂ) * ζ ^ 13 + ((17 / 22) : ℂ) * ζ ^ 14 - ((115 / 44) : ℂ) * ζ ^ 15 - ((3 / 4) : ℂ) * ζ ^ 18 + ((115 / 44) : ℂ) * ζ ^ 19 - ((9 / 11) : ℂ) * ζ ^ 20 - ((43 / 44) : ℂ) * ζ ^ 22 - ((20 / 11) : ℂ) * ζ ^ 23 + ((9 / 11) : ℂ) * ζ ^ 24 + ((21 / 22) : ℂ) * ζ ^ 25 - ((43 / 44) : ℂ) * ζ ^ 26 - ((35 / 44) : ℂ) * ζ ^ 28 - ((21 / 22) : ℂ) * ζ ^ 29 + ((43 / 44) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_0_2 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        0 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((161 / 88) : ℂ) + ((39 / 44) : ℂ) * ζ ^ 3 - ((161 / 88) : ℂ) * ζ ^ 4 + ((49 / 44) : ℂ) * ζ ^ 5 + ((73 / 44) : ℂ) * ζ ^ 6 + ((107 / 88) : ℂ) * ζ ^ 8 - ((49 / 44) : ℂ) * ζ ^ 9 + ((53 / 44) : ℂ) * ζ ^ 10 + ((107 / 88) : ℂ) * ζ ^ 13 + ((5 / 11) : ℂ) * ζ ^ 14 - ((61 / 22) : ℂ) * ζ ^ 15 - ((73 / 88) : ℂ) * ζ ^ 18 + ((61 / 22) : ℂ) * ζ ^ 19 - ((141 / 88) : ℂ) * ζ ^ 20 - ((73 / 44) : ℂ) * ζ ^ 22 - ((57 / 22) : ℂ) * ζ ^ 23 + ((141 / 88) : ℂ) * ζ ^ 24 + ((109 / 88) : ℂ) * ζ ^ 25 - ((73 / 44) : ℂ) * ζ ^ 26 - ((49 / 44) : ℂ) * ζ ^ 28 - ((109 / 88) : ℂ) * ζ ^ 29 + ((73 / 44) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_0_3 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        0 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-(1 : ℂ) - ((29 / 12) : ℂ) * ζ ^ 3 + ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 5 + ((1 / 4) : ℂ) * ζ ^ 6 - ((49 / 12) : ℂ) * ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 9 + ((35 / 12) : ℂ) * ζ ^ 10 - ((4 / 3) : ℂ) * ζ ^ 13 - ((8 / 3) : ℂ) * ζ ^ 14 - ((4 / 3) : ℂ) * ζ ^ 15 - ((1 / 2) : ℂ) * ζ ^ 18 + ((4 / 3) : ℂ) * ζ ^ 19 + ((5 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 22 - ((5 / 12) : ℂ) * ζ ^ 23 - ((5 / 4) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 25 - ((1 / 4) : ℂ) * ζ ^ 26 + ((1 / 4) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 29 + ((1 / 4) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_0_4 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        0 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((5 / 8) : ℂ) + ((9 / 2) : ℂ) * ζ ^ 3 - ((5 / 8) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 5 + ((7 / 4) : ℂ) * ζ ^ 6 + ((25 / 8) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 9 - ((1 / 2) : ℂ) * ζ ^ 10 - ((7 / 8) : ℂ) * ζ ^ 13 + ((9 / 4) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 15 - ((13 / 8) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 19 - ((9 / 8) : ℂ) * ζ ^ 20 - ((7 / 4) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 23 + ((9 / 8) : ℂ) * ζ ^ 24 - ((5 / 8) : ℂ) * ζ ^ 25 - ((7 / 4) : ℂ) * ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 28 + ((5 / 8) : ℂ) * ζ ^ 29 + ((7 / 4) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_0_5 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        0 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((11 / 8) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 3 - ((11 / 8) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 8) : ℂ) * ζ ^ 8 + ((5 / 4) : ℂ) * ζ ^ 10 + ((13 / 8) : ℂ) * ζ ^ 13 - ζ ^ 14 - ((5 / 4) : ℂ) * ζ ^ 15 + ((19 / 8) : ℂ) * ζ ^ 18 + ((5 / 4) : ℂ) * ζ ^ 19 - ((11 / 8) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 23 + ((11 / 8) : ℂ) * ζ ^ 24 + ((5 / 8) : ℂ) * ζ ^ 25 - ((1 / 4) : ℂ) * ζ ^ 26 - ((1 / 2) : ℂ) * ζ ^ 28 - ((5 / 8) : ℂ) * ζ ^ 29 + ((1 / 4) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_1_0 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        1 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((31 / 8) : ℂ) - ((3 / 8) : ℂ) * ζ ^ 3 + ((31 / 8) : ℂ) * ζ ^ 4 - ((41 / 8) : ℂ) * ζ ^ 5 - ((23 / 8) : ℂ) * ζ ^ 6 + ((41 / 8) : ℂ) * ζ ^ 9 - ((31 / 8) : ℂ) * ζ ^ 10 - ((19 / 8) : ℂ) * ζ ^ 13 + ζ ^ 14 + ((25 / 8) : ℂ) * ζ ^ 15 - ((7 / 4) : ℂ) * ζ ^ 18 - ((25 / 8) : ℂ) * ζ ^ 19 + ((19 / 4) : ℂ) * ζ ^ 20 + ((23 / 8) : ℂ) * ζ ^ 22 + ((9 / 8) : ℂ) * ζ ^ 23 - ((19 / 4) : ℂ) * ζ ^ 24 + ((7 / 8) : ℂ) * ζ ^ 25 + ((23 / 8) : ℂ) * ζ ^ 26 + ((15 / 8) : ℂ) * ζ ^ 28 - ((7 / 8) : ℂ) * ζ ^ 29 - ((23 / 8) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_1_1 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        1 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((7 / 22) : ℂ) + ((12 / 11) : ℂ) * ζ ^ 3 + ((7 / 22) : ℂ) * ζ ^ 4 - ((91 / 44) : ℂ) * ζ ^ 5 + ((19 / 22) : ℂ) * ζ ^ 6 - ((3 / 11) : ℂ) * ζ ^ 8 + ((91 / 44) : ℂ) * ζ ^ 9 - ((69 / 22) : ℂ) * ζ ^ 10 - ((8 / 11) : ℂ) * ζ ^ 13 + (4 : ℂ) * ζ ^ 14 - ((79 / 44) : ℂ) * ζ ^ 15 - ((63 / 22) : ℂ) * ζ ^ 18 + ((79 / 44) : ℂ) * ζ ^ 19 + ((81 / 44) : ℂ) * ζ ^ 20 - ((19 / 22) : ℂ) * ζ ^ 22 - ((1 / 44) : ℂ) * ζ ^ 23 - ((81 / 44) : ℂ) * ζ ^ 24 + ((117 / 44) : ℂ) * ζ ^ 25 - ((19 / 22) : ℂ) * ζ ^ 26 + ((3 / 2) : ℂ) * ζ ^ 28 - ((117 / 44) : ℂ) * ζ ^ 29 + ((19 / 22) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_1_2 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        1 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((61 / 88) : ℂ) - ((41 / 88) : ℂ) * ζ ^ 3 - ((61 / 88) : ℂ) * ζ ^ 4 - ((137 / 88) : ℂ) * ζ ^ 5 + ((147 / 88) : ℂ) * ζ ^ 6 - ((2 / 11) : ℂ) * ζ ^ 8 + ((137 / 88) : ℂ) * ζ ^ 9 - ((233 / 88) : ℂ) * ζ ^ 10 + ((81 / 88) : ℂ) * ζ ^ 13 + ((95 / 22) : ℂ) * ζ ^ 14 - ((261 / 88) : ℂ) * ζ ^ 15 - ((179 / 44) : ℂ) * ζ ^ 18 + ((261 / 88) : ℂ) * ζ ^ 19 + ((43 / 44) : ℂ) * ζ ^ 20 - ((147 / 88) : ℂ) * ζ ^ 22 - ((67 / 88) : ℂ) * ζ ^ 23 - ((43 / 44) : ℂ) * ζ ^ 24 + ((365 / 88) : ℂ) * ζ ^ 25 - ((147 / 88) : ℂ) * ζ ^ 26 + ((197 / 88) : ℂ) * ζ ^ 28 - ((365 / 88) : ℂ) * ζ ^ 29 + ((147 / 88) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_1_3 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        1 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((5 / 2) : ℂ) - ((37 / 12) : ℂ) * ζ ^ 3 - ((5 / 2) : ℂ) * ζ ^ 4 + (3 : ℂ) * ζ ^ 5 - ((1 / 3) : ℂ) * ζ ^ 6 + ((7 / 12) : ℂ) * ζ ^ 8 - (3 : ℂ) * ζ ^ 9 + ((7 / 3) : ℂ) * ζ ^ 10 + ((47 / 12) : ℂ) * ζ ^ 13 - ((8 / 3) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 15 - ((23 / 12) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 19 - ((7 / 12) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 22 + ((3 / 2) : ℂ) * ζ ^ 23 + ((7 / 12) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 25 + ((1 / 3) : ℂ) * ζ ^ 26 - ((7 / 12) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 29 - ((1 / 3) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_1_4 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        1 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((25 / 8) : ℂ) + ((3 / 8) : ℂ) * ζ ^ 3 + ((25 / 8) : ℂ) * ζ ^ 4 - ((33 / 8) : ℂ) * ζ ^ 5 + ((19 / 8) : ℂ) * ζ ^ 6 - (3 : ℂ) * ζ ^ 8 + ((33 / 8) : ℂ) * ζ ^ 9 - ((1 / 8) : ℂ) * ζ ^ 10 - ((29 / 8) : ℂ) * ζ ^ 13 + ((5 / 2) : ℂ) * ζ ^ 14 + ((9 / 8) : ℂ) * ζ ^ 15 + ((3 / 4) : ℂ) * ζ ^ 18 - ((9 / 8) : ℂ) * ζ ^ 19 + ((1 / 4) : ℂ) * ζ ^ 20 - ((19 / 8) : ℂ) * ζ ^ 22 + ((7 / 8) : ℂ) * ζ ^ 23 - ((1 / 4) : ℂ) * ζ ^ 24 + ((17 / 8) : ℂ) * ζ ^ 25 - ((19 / 8) : ℂ) * ζ ^ 26 + ((3 / 8) : ℂ) * ζ ^ 28 - ((17 / 8) : ℂ) * ζ ^ 29 + ((19 / 8) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_1_5 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        1 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((5 / 8) : ℂ) - ((3 / 8) : ℂ) * ζ ^ 3 - ((5 / 8) : ℂ) * ζ ^ 4 - ((5 / 8) : ℂ) * ζ ^ 5 - ((1 / 8) : ℂ) * ζ ^ 6 - ((1 / 4) : ℂ) * ζ ^ 8 + ((5 / 8) : ℂ) * ζ ^ 9 - ((29 / 8) : ℂ) * ζ ^ 10 + ((15 / 8) : ℂ) * ζ ^ 13 + ((7 / 2) : ℂ) * ζ ^ 14 - ((33 / 8) : ℂ) * ζ ^ 15 - ((5 / 2) : ℂ) * ζ ^ 18 + ((33 / 8) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 8) : ℂ) * ζ ^ 22 - ((13 / 8) : ℂ) * ζ ^ 23 + ((1 / 4) : ℂ) * ζ ^ 24 + ((9 / 8) : ℂ) * ζ ^ 25 + ((1 / 8) : ℂ) * ζ ^ 26 + ((11 / 8) : ℂ) * ζ ^ 28 - ((9 / 8) : ℂ) * ζ ^ 29 - ((1 / 8) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_2_0 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        2 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((21 / 8) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 3 + ((21 / 8) : ℂ) * ζ ^ 4 - ((11 / 4) : ℂ) * ζ ^ 5 - ((3 / 2) : ℂ) * ζ ^ 6 - ((9 / 8) : ℂ) * ζ ^ 8 + ((11 / 4) : ℂ) * ζ ^ 9 + ((1 / 4) : ℂ) * ζ ^ 10 - ((17 / 8) : ℂ) * ζ ^ 13 - ((7 / 4) : ℂ) * ζ ^ 14 + ((13 / 4) : ℂ) * ζ ^ 15 + ((1 / 8) : ℂ) * ζ ^ 18 - ((13 / 4) : ℂ) * ζ ^ 19 + ((11 / 8) : ℂ) * ζ ^ 20 + ((3 / 2) : ℂ) * ζ ^ 22 + ((3 / 4) : ℂ) * ζ ^ 23 - ((11 / 8) : ℂ) * ζ ^ 24 - ((5 / 8) : ℂ) * ζ ^ 25 + ((3 / 2) : ℂ) * ζ ^ 26 + ((3 / 4) : ℂ) * ζ ^ 28 + ((5 / 8) : ℂ) * ζ ^ 29 - ((3 / 2) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_2_1 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        2 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((19 / 44) : ℂ) + ((17 / 44) : ℂ) * ζ ^ 3 - ((19 / 44) : ℂ) * ζ ^ 4 - ((39 / 22) : ℂ) * ζ ^ 5 - ((1 / 44) : ℂ) * ζ ^ 6 - ((1 / 4) : ℂ) * ζ ^ 8 + ((39 / 22) : ℂ) * ζ ^ 9 - ((71 / 44) : ℂ) * ζ ^ 10 - ((43 / 44) : ℂ) * ζ ^ 13 + ((35 / 22) : ℂ) * ζ ^ 14 + ((5 / 44) : ℂ) * ζ ^ 15 - ((35 / 44) : ℂ) * ζ ^ 18 - ((5 / 44) : ℂ) * ζ ^ 19 + ((15 / 11) : ℂ) * ζ ^ 20 + ((1 / 44) : ℂ) * ζ ^ 22 + ((25 / 22) : ℂ) * ζ ^ 23 - ((15 / 11) : ℂ) * ζ ^ 24 + ((29 / 22) : ℂ) * ζ ^ 25 + ((1 / 44) : ℂ) * ζ ^ 26 + ((51 / 44) : ℂ) * ζ ^ 28 - ((29 / 22) : ℂ) * ζ ^ 29 - ((1 / 44) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_2_2 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        2 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((39 / 88) : ℂ) + ((6 / 11) : ℂ) * ζ ^ 3 + ((39 / 88) : ℂ) * ζ ^ 4 - ((83 / 44) : ℂ) * ζ ^ 5 + ζ ^ 6 - ((15 / 88) : ℂ) * ζ ^ 8 + ((83 / 44) : ℂ) * ζ ^ 9 - ((43 / 22) : ℂ) * ζ ^ 10 - ((81 / 88) : ℂ) * ζ ^ 13 + ((65 / 22) : ℂ) * ζ ^ 14 - ((9 / 22) : ℂ) * ζ ^ 15 - ((151 / 88) : ℂ) * ζ ^ 18 + ((9 / 22) : ℂ) * ζ ^ 19 + ((181 / 88) : ℂ) * ζ ^ 20 - ζ ^ 22 + ((27 / 44) : ℂ) * ζ ^ 23 - ((181 / 88) : ℂ) * ζ ^ 24 + ((177 / 88) : ℂ) * ζ ^ 25 - ζ ^ 26 + ((5 / 4) : ℂ) * ζ ^ 28 - ((177 / 88) : ℂ) * ζ ^ 29 + ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_2_3 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        2 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((5 / 6) : ℂ) + ((5 / 12) : ℂ) * ζ ^ 3 - ((5 / 6) : ℂ) * ζ ^ 4 + ((7 / 4) : ℂ) * ζ ^ 5 + ((1 / 4) : ℂ) * ζ ^ 6 + ((5 / 4) : ℂ) * ζ ^ 8 - ((7 / 4) : ℂ) * ζ ^ 9 - ((1 / 12) : ℂ) * ζ ^ 10 + ((7 / 6) : ℂ) * ζ ^ 13 + ((1 / 3) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 15 - ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 19 + ((1 / 12) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 12) : ℂ) * ζ ^ 23 - ((1 / 12) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 25 - ((1 / 4) : ℂ) * ζ ^ 26 - ((7 / 12) : ℂ) * ζ ^ 28 + ((1 / 3) : ℂ) * ζ ^ 29 + ((1 / 4) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_2_4 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        2 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((7 / 8) : ℂ) - ((7 / 4) : ℂ) * ζ ^ 3 + ((7 / 8) : ℂ) * ζ ^ 4 - ((5 / 4) : ℂ) * ζ ^ 5 + ((1 / 2) : ℂ) * ζ ^ 6 - ((17 / 8) : ℂ) * ζ ^ 8 + ((5 / 4) : ℂ) * ζ ^ 9 + ((3 / 4) : ℂ) * ζ ^ 10 - ((3 / 8) : ℂ) * ζ ^ 13 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 15 + ((13 / 8) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 19 + ((5 / 8) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 4) : ℂ) * ζ ^ 23 - ((5 / 8) : ℂ) * ζ ^ 24 + ((15 / 8) : ℂ) * ζ ^ 25 - ((1 / 2) : ℂ) * ζ ^ 26 + ((3 / 4) : ℂ) * ζ ^ 28 - ((15 / 8) : ℂ) * ζ ^ 29 + ((1 / 2) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_2_5 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        2 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((1 / 8) : ℂ) + ((1 / 8) : ℂ) * ζ ^ 4 - (2 : ℂ) * ζ ^ 5 - ((1 / 8) : ℂ) * ζ ^ 8 + (2 : ℂ) * ζ ^ 9 - ((3 / 2) : ℂ) * ζ ^ 10 - ((3 / 8) : ℂ) * ζ ^ 13 + ((3 / 2) : ℂ) * ζ ^ 14 - ((3 / 4) : ℂ) * ζ ^ 15 - ((7 / 8) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 19 + ((7 / 8) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 23 - ((7 / 8) : ℂ) * ζ ^ 24 + ((9 / 8) : ℂ) * ζ ^ 25 + ζ ^ 28 - ((9 / 8) : ℂ) * ζ ^ 29)
private theorem row14_eigenbasisInverse_mul_3_0 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        3 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((21 / 8) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 3 - ((21 / 8) : ℂ) * ζ ^ 4 + ((21 / 4) : ℂ) * ζ ^ 5 + (3 : ℂ) * ζ ^ 6 - ((7 / 4) : ℂ) * ζ ^ 8 - ((21 / 4) : ℂ) * ζ ^ 9 + (6 : ℂ) * ζ ^ 10 + ((15 / 8) : ℂ) * ζ ^ 13 - (3 : ℂ) * ζ ^ 14 - ((11 / 8) : ℂ) * ζ ^ 15 + ((17 / 8) : ℂ) * ζ ^ 18 + ((11 / 8) : ℂ) * ζ ^ 19 - ((25 / 4) : ℂ) * ζ ^ 20 - (3 : ℂ) * ζ ^ 22 - ((7 / 8) : ℂ) * ζ ^ 23 + ((25 / 4) : ℂ) * ζ ^ 24 - (2 : ℂ) * ζ ^ 25 - (3 : ℂ) * ζ ^ 26 - ((3 / 2) : ℂ) * ζ ^ 28 + (2 : ℂ) * ζ ^ 29 + (3 : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_3_1 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        3 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((15 / 22) : ℂ) - ((14 / 11) : ℂ) * ζ ^ 3 + ((15 / 22) : ℂ) * ζ ^ 4 + ((47 / 44) : ℂ) * ζ ^ 5 - ((29 / 22) : ℂ) * ζ ^ 6 - ((53 / 44) : ℂ) * ζ ^ 8 - ((47 / 44) : ℂ) * ζ ^ 9 + ((59 / 22) : ℂ) * ζ ^ 10 - ((1 / 11) : ℂ) * ζ ^ 13 - (4 : ℂ) * ζ ^ 14 + ((129 / 44) : ℂ) * ζ ^ 15 + ((141 / 44) : ℂ) * ζ ^ 18 - ((129 / 44) : ℂ) * ζ ^ 19 - ((43 / 44) : ℂ) * ζ ^ 20 + ((29 / 22) : ℂ) * ζ ^ 22 + ((23 / 22) : ℂ) * ζ ^ 23 + ((43 / 44) : ℂ) * ζ ^ 24 - ((27 / 11) : ℂ) * ζ ^ 25 + ((29 / 22) : ℂ) * ζ ^ 26 - ((9 / 11) : ℂ) * ζ ^ 28 + ((27 / 11) : ℂ) * ζ ^ 29 - ((29 / 22) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_3_2 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        3 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((189 / 88) : ℂ) + ((35 / 44) : ℂ) * ζ ^ 3 + ((189 / 88) : ℂ) * ζ ^ 4 - ((3 / 22) : ℂ) * ζ ^ 5 - ((71 / 44) : ℂ) * ζ ^ 6 - ((51 / 44) : ℂ) * ζ ^ 8 + ((3 / 22) : ℂ) * ζ ^ 9 + ((85 / 44) : ℂ) * ζ ^ 10 - ((157 / 88) : ℂ) * ζ ^ 13 - ((39 / 11) : ℂ) * ζ ^ 14 + ((361 / 88) : ℂ) * ζ ^ 15 + ((359 / 88) : ℂ) * ζ ^ 18 - ((361 / 88) : ℂ) * ζ ^ 19 + ((4 / 11) : ℂ) * ζ ^ 20 + ((71 / 44) : ℂ) * ζ ^ 22 + ((145 / 88) : ℂ) * ζ ^ 23 - ((4 / 11) : ℂ) * ζ ^ 24 - ((43 / 11) : ℂ) * ζ ^ 25 + ((71 / 44) : ℂ) * ζ ^ 26 - ((16 / 11) : ℂ) * ζ ^ 28 + ((43 / 11) : ℂ) * ζ ^ 29 - ((71 / 44) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_3_3 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        3 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((11 / 4) : ℂ) + ((13 / 3) : ℂ) * ζ ^ 3 + ((11 / 4) : ℂ) * ζ ^ 4 - ((17 / 12) : ℂ) * ζ ^ 5 + ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ((17 / 12) : ℂ) * ζ ^ 9 - ((11 / 3) : ℂ) * ζ ^ 10 - ((17 / 6) : ℂ) * ζ ^ 13 + ((9 / 2) : ℂ) * ζ ^ 14 + ((5 / 6) : ℂ) * ζ ^ 15 + ((5 / 4) : ℂ) * ζ ^ 18 - ((5 / 6) : ℂ) * ζ ^ 19 - ((1 / 12) : ℂ) * ζ ^ 20 - ((5 / 6) : ℂ) * ζ ^ 22 - ((17 / 12) : ℂ) * ζ ^ 23 + ((1 / 12) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 25 - ((5 / 6) : ℂ) * ζ ^ 26 + ((1 / 3) : ℂ) * ζ ^ 28 + ((2 / 3) : ℂ) * ζ ^ 29 + ((5 / 6) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_3_4 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        3 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((23 / 8) : ℂ) - ((5 / 2) : ℂ) * ζ ^ 3 - ((23 / 8) : ℂ) * ζ ^ 4 + ((15 / 4) : ℂ) * ζ ^ 5 - ((13 / 4) : ℂ) * ζ ^ 6 + ((3 / 2) : ℂ) * ζ ^ 8 - ((15 / 4) : ℂ) * ζ ^ 9 + ((1 / 2) : ℂ) * ζ ^ 10 + ((33 / 8) : ℂ) * ζ ^ 13 - ((15 / 4) : ℂ) * ζ ^ 14 - ((5 / 8) : ℂ) * ζ ^ 15 + ((5 / 8) : ℂ) * ζ ^ 18 + ((5 / 8) : ℂ) * ζ ^ 19 + ((3 / 4) : ℂ) * ζ ^ 20 + ((13 / 4) : ℂ) * ζ ^ 22 - ((1 / 8) : ℂ) * ζ ^ 23 - ((3 / 4) : ℂ) * ζ ^ 24 - ζ ^ 25 + ((13 / 4) : ℂ) * ζ ^ 26 + ζ ^ 29 - ((13 / 4) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_3_5 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        3 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((19 / 8) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 3 + ((19 / 8) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 5 + ((1 / 4) : ℂ) * ζ ^ 6 - ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 9 + ((13 / 4) : ℂ) * ζ ^ 10 - ((21 / 8) : ℂ) * ζ ^ 13 - (3 : ℂ) * ζ ^ 14 + ((31 / 8) : ℂ) * ζ ^ 15 + ((15 / 8) : ℂ) * ζ ^ 18 - ((31 / 8) : ℂ) * ζ ^ 19 + ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 22 + ((11 / 8) : ℂ) * ζ ^ 23 - ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 25 - ((1 / 4) : ℂ) * ζ ^ 26 - ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 29 + ((1 / 4) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_4_0 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        4 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((1 / 8) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 3 - ((1 / 8) : ℂ) * ζ ^ 4 + ((13 / 4) : ℂ) * ζ ^ 5 + ((5 / 4) : ℂ) * ζ ^ 6 - ((13 / 8) : ℂ) * ζ ^ 8 - ((13 / 4) : ℂ) * ζ ^ 9 + (5 : ℂ) * ζ ^ 10 + ((1 / 8) : ℂ) * ζ ^ 13 - ((15 / 4) : ℂ) * ζ ^ 14 + ((5 / 4) : ℂ) * ζ ^ 15 + ((9 / 8) : ℂ) * ζ ^ 18 - ((5 / 4) : ℂ) * ζ ^ 19 - ((29 / 8) : ℂ) * ζ ^ 20 - ((5 / 4) : ℂ) * ζ ^ 22 + ζ ^ 23 + ((29 / 8) : ℂ) * ζ ^ 24 - ((27 / 8) : ℂ) * ζ ^ 25 - ((5 / 4) : ℂ) * ζ ^ 26 + ((3 / 4) : ℂ) * ζ ^ 28 + ((27 / 8) : ℂ) * ζ ^ 29 + ((5 / 4) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_4_1 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        4 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((91 / 44) : ℂ) - ((69 / 44) : ℂ) * ζ ^ 3 + ((91 / 44) : ℂ) * ζ ^ 4 - ((21 / 22) : ℂ) * ζ ^ 5 - ((43 / 44) : ℂ) * ζ ^ 6 - ((113 / 44) : ℂ) * ζ ^ 8 + ((21 / 22) : ℂ) * ζ ^ 9 - ((9 / 44) : ℂ) * ζ ^ 10 - ((69 / 44) : ℂ) * ζ ^ 13 - ((17 / 22) : ℂ) * ζ ^ 14 + ((115 / 44) : ℂ) * ζ ^ 15 + ((3 / 4) : ℂ) * ζ ^ 18 - ((115 / 44) : ℂ) * ζ ^ 19 + ((9 / 11) : ℂ) * ζ ^ 20 + ((43 / 44) : ℂ) * ζ ^ 22 + ((20 / 11) : ℂ) * ζ ^ 23 - ((9 / 11) : ℂ) * ζ ^ 24 - ((21 / 22) : ℂ) * ζ ^ 25 + ((43 / 44) : ℂ) * ζ ^ 26 + ((35 / 44) : ℂ) * ζ ^ 28 + ((21 / 22) : ℂ) * ζ ^ 29 - ((43 / 44) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_4_2 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        4 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((161 / 88) : ℂ) - ((39 / 44) : ℂ) * ζ ^ 3 + ((161 / 88) : ℂ) * ζ ^ 4 - ((49 / 44) : ℂ) * ζ ^ 5 - ((73 / 44) : ℂ) * ζ ^ 6 - ((107 / 88) : ℂ) * ζ ^ 8 + ((49 / 44) : ℂ) * ζ ^ 9 - ((53 / 44) : ℂ) * ζ ^ 10 - ((107 / 88) : ℂ) * ζ ^ 13 - ((5 / 11) : ℂ) * ζ ^ 14 + ((61 / 22) : ℂ) * ζ ^ 15 + ((73 / 88) : ℂ) * ζ ^ 18 - ((61 / 22) : ℂ) * ζ ^ 19 + ((141 / 88) : ℂ) * ζ ^ 20 + ((73 / 44) : ℂ) * ζ ^ 22 + ((57 / 22) : ℂ) * ζ ^ 23 - ((141 / 88) : ℂ) * ζ ^ 24 - ((109 / 88) : ℂ) * ζ ^ 25 + ((73 / 44) : ℂ) * ζ ^ 26 + ((49 / 44) : ℂ) * ζ ^ 28 + ((109 / 88) : ℂ) * ζ ^ 29 - ((73 / 44) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_4_3 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        4 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 ((1 : ℂ) + ((29 / 12) : ℂ) * ζ ^ 3 - ζ ^ 4 + ((3 / 4) : ℂ) * ζ ^ 5 - ((1 / 4) : ℂ) * ζ ^ 6 + ((49 / 12) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 9 - ((35 / 12) : ℂ) * ζ ^ 10 + ((4 / 3) : ℂ) * ζ ^ 13 + ((8 / 3) : ℂ) * ζ ^ 14 + ((4 / 3) : ℂ) * ζ ^ 15 + ((1 / 2) : ℂ) * ζ ^ 18 - ((4 / 3) : ℂ) * ζ ^ 19 - ((5 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 22 + ((5 / 12) : ℂ) * ζ ^ 23 + ((5 / 4) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 29 - ((1 / 4) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_4_4 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        4 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((5 / 8) : ℂ) - ((9 / 2) : ℂ) * ζ ^ 3 + ((5 / 8) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 5 - ((7 / 4) : ℂ) * ζ ^ 6 - ((25 / 8) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 9 + ((1 / 2) : ℂ) * ζ ^ 10 + ((7 / 8) : ℂ) * ζ ^ 13 - ((9 / 4) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 15 + ((13 / 8) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 19 + ((9 / 8) : ℂ) * ζ ^ 20 + ((7 / 4) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 23 - ((9 / 8) : ℂ) * ζ ^ 24 + ((5 / 8) : ℂ) * ζ ^ 25 + ((7 / 4) : ℂ) * ζ ^ 26 + ((1 / 4) : ℂ) * ζ ^ 28 - ((5 / 8) : ℂ) * ζ ^ 29 - ((7 / 4) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_4_5 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        4 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((11 / 8) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 3 + ((11 / 8) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 8) : ℂ) * ζ ^ 8 - ((5 / 4) : ℂ) * ζ ^ 10 - ((13 / 8) : ℂ) * ζ ^ 13 + ζ ^ 14 + ((5 / 4) : ℂ) * ζ ^ 15 - ((19 / 8) : ℂ) * ζ ^ 18 - ((5 / 4) : ℂ) * ζ ^ 19 + ((11 / 8) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 23 - ((11 / 8) : ℂ) * ζ ^ 24 - ((5 / 8) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 28 + ((5 / 8) : ℂ) * ζ ^ 29 - ((1 / 4) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_5_0 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        5 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((21 / 8) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 3 - ((21 / 8) : ℂ) * ζ ^ 4 + ((11 / 4) : ℂ) * ζ ^ 5 + ((3 / 2) : ℂ) * ζ ^ 6 + ((9 / 8) : ℂ) * ζ ^ 8 - ((11 / 4) : ℂ) * ζ ^ 9 - ((1 / 4) : ℂ) * ζ ^ 10 + ((17 / 8) : ℂ) * ζ ^ 13 + ((7 / 4) : ℂ) * ζ ^ 14 - ((13 / 4) : ℂ) * ζ ^ 15 - ((1 / 8) : ℂ) * ζ ^ 18 + ((13 / 4) : ℂ) * ζ ^ 19 - ((11 / 8) : ℂ) * ζ ^ 20 - ((3 / 2) : ℂ) * ζ ^ 22 - ((3 / 4) : ℂ) * ζ ^ 23 + ((11 / 8) : ℂ) * ζ ^ 24 + ((5 / 8) : ℂ) * ζ ^ 25 - ((3 / 2) : ℂ) * ζ ^ 26 - ((3 / 4) : ℂ) * ζ ^ 28 - ((5 / 8) : ℂ) * ζ ^ 29 + ((3 / 2) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_5_1 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        5 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((19 / 44) : ℂ) - ((17 / 44) : ℂ) * ζ ^ 3 + ((19 / 44) : ℂ) * ζ ^ 4 + ((39 / 22) : ℂ) * ζ ^ 5 + ((1 / 44) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 - ((39 / 22) : ℂ) * ζ ^ 9 + ((71 / 44) : ℂ) * ζ ^ 10 + ((43 / 44) : ℂ) * ζ ^ 13 - ((35 / 22) : ℂ) * ζ ^ 14 - ((5 / 44) : ℂ) * ζ ^ 15 + ((35 / 44) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 19 - ((15 / 11) : ℂ) * ζ ^ 20 - ((1 / 44) : ℂ) * ζ ^ 22 - ((25 / 22) : ℂ) * ζ ^ 23 + ((15 / 11) : ℂ) * ζ ^ 24 - ((29 / 22) : ℂ) * ζ ^ 25 - ((1 / 44) : ℂ) * ζ ^ 26 - ((51 / 44) : ℂ) * ζ ^ 28 + ((29 / 22) : ℂ) * ζ ^ 29 + ((1 / 44) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_5_2 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        5 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((39 / 88) : ℂ) - ((6 / 11) : ℂ) * ζ ^ 3 - ((39 / 88) : ℂ) * ζ ^ 4 + ((83 / 44) : ℂ) * ζ ^ 5 - ζ ^ 6 + ((15 / 88) : ℂ) * ζ ^ 8 - ((83 / 44) : ℂ) * ζ ^ 9 + ((43 / 22) : ℂ) * ζ ^ 10 + ((81 / 88) : ℂ) * ζ ^ 13 - ((65 / 22) : ℂ) * ζ ^ 14 + ((9 / 22) : ℂ) * ζ ^ 15 + ((151 / 88) : ℂ) * ζ ^ 18 - ((9 / 22) : ℂ) * ζ ^ 19 - ((181 / 88) : ℂ) * ζ ^ 20 + ζ ^ 22 - ((27 / 44) : ℂ) * ζ ^ 23 + ((181 / 88) : ℂ) * ζ ^ 24 - ((177 / 88) : ℂ) * ζ ^ 25 + ζ ^ 26 - ((5 / 4) : ℂ) * ζ ^ 28 + ((177 / 88) : ℂ) * ζ ^ 29 - ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_5_3 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        5 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((5 / 6) : ℂ) - ((5 / 12) : ℂ) * ζ ^ 3 + ((5 / 6) : ℂ) * ζ ^ 4 - ((7 / 4) : ℂ) * ζ ^ 5 - ((1 / 4) : ℂ) * ζ ^ 6 - ((5 / 4) : ℂ) * ζ ^ 8 + ((7 / 4) : ℂ) * ζ ^ 9 + ((1 / 12) : ℂ) * ζ ^ 10 - ((7 / 6) : ℂ) * ζ ^ 13 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 15 + ((7 / 6) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 19 - ((1 / 12) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 12) : ℂ) * ζ ^ 23 + ((1 / 12) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 26 + ((7 / 12) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 29 - ((1 / 4) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_5_4 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        5 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((7 / 8) : ℂ) + ((7 / 4) : ℂ) * ζ ^ 3 - ((7 / 8) : ℂ) * ζ ^ 4 + ((5 / 4) : ℂ) * ζ ^ 5 - ((1 / 2) : ℂ) * ζ ^ 6 + ((17 / 8) : ℂ) * ζ ^ 8 - ((5 / 4) : ℂ) * ζ ^ 9 - ((3 / 4) : ℂ) * ζ ^ 10 + ((3 / 8) : ℂ) * ζ ^ 13 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 15 - ((13 / 8) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 19 - ((5 / 8) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 4) : ℂ) * ζ ^ 23 + ((5 / 8) : ℂ) * ζ ^ 24 - ((15 / 8) : ℂ) * ζ ^ 25 + ((1 / 2) : ℂ) * ζ ^ 26 - ((3 / 4) : ℂ) * ζ ^ 28 + ((15 / 8) : ℂ) * ζ ^ 29 - ((1 / 2) : ℂ) * ζ ^ 30)
private theorem row14_eigenbasisInverse_mul_5_5 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis)
        5 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((1 / 8) : ℂ) - ((1 / 8) : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 5 + ((1 / 8) : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 9 + ((3 / 2) : ℂ) * ζ ^ 10 + ((3 / 8) : ℂ) * ζ ^ 13 - ((3 / 2) : ℂ) * ζ ^ 14 + ((3 / 4) : ℂ) * ζ ^ 15 + ((7 / 8) : ℂ) * ζ ^ 18 - ((3 / 4) : ℂ) * ζ ^ 19 - ((7 / 8) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 23 + ((7 / 8) : ℂ) * ζ ^ 24 - ((9 / 8) : ℂ) * ζ ^ 25 - ζ ^ 28 + ((9 / 8) : ℂ) * ζ ^ 29)
/-- The displayed row 14 matrix is a left inverse of its
eigenbasis. -/
theorem alternatingSixAmbientRow14EigenbasisInverse_mul :
    alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixAmbientRow14Eigenbasis =
      1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row14_eigenbasisInverse_mul_0_0
  · exact row14_eigenbasisInverse_mul_0_1
  · exact row14_eigenbasisInverse_mul_0_2
  · exact row14_eigenbasisInverse_mul_0_3
  · exact row14_eigenbasisInverse_mul_0_4
  · exact row14_eigenbasisInverse_mul_0_5
  · exact row14_eigenbasisInverse_mul_1_0
  · exact row14_eigenbasisInverse_mul_1_1
  · exact row14_eigenbasisInverse_mul_1_2
  · exact row14_eigenbasisInverse_mul_1_3
  · exact row14_eigenbasisInverse_mul_1_4
  · exact row14_eigenbasisInverse_mul_1_5
  · exact row14_eigenbasisInverse_mul_2_0
  · exact row14_eigenbasisInverse_mul_2_1
  · exact row14_eigenbasisInverse_mul_2_2
  · exact row14_eigenbasisInverse_mul_2_3
  · exact row14_eigenbasisInverse_mul_2_4
  · exact row14_eigenbasisInverse_mul_2_5
  · exact row14_eigenbasisInverse_mul_3_0
  · exact row14_eigenbasisInverse_mul_3_1
  · exact row14_eigenbasisInverse_mul_3_2
  · exact row14_eigenbasisInverse_mul_3_3
  · exact row14_eigenbasisInverse_mul_3_4
  · exact row14_eigenbasisInverse_mul_3_5
  · exact row14_eigenbasisInverse_mul_4_0
  · exact row14_eigenbasisInverse_mul_4_1
  · exact row14_eigenbasisInverse_mul_4_2
  · exact row14_eigenbasisInverse_mul_4_3
  · exact row14_eigenbasisInverse_mul_4_4
  · exact row14_eigenbasisInverse_mul_4_5
  · exact row14_eigenbasisInverse_mul_5_0
  · exact row14_eigenbasisInverse_mul_5_1
  · exact row14_eigenbasisInverse_mul_5_2
  · exact row14_eigenbasisInverse_mul_5_3
  · exact row14_eigenbasisInverse_mul_5_4
  · exact row14_eigenbasisInverse_mul_5_5

/-- The displayed row 14 inverse is also a right inverse. -/
theorem alternatingSixAmbientRow14Eigenbasis_mul_inverse :
    alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixAmbientRow14EigenbasisInverse_mul


private theorem row14_generatorB_mul_eigenbasis_0_0 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        0 0 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        0 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((15 / 2) : ℂ) - (3 : ℂ) * ζ ^ 3 - ((15 / 2) : ℂ) * ζ ^ 4 + (9 : ℂ) * ζ ^ 5 + (8 : ℂ) * ζ ^ 6 + ((3 / 2) : ℂ) * ζ ^ 8 - (9 : ℂ) * ζ ^ 9 + (4 : ℂ) * ζ ^ 10 + (6 : ℂ) * ζ ^ 13 + (4 : ℂ) * ζ ^ 14 - (12 : ℂ) * ζ ^ 15 - ζ ^ 18 + (12 : ℂ) * ζ ^ 19 - ((15 / 2) : ℂ) * ζ ^ 20 - (8 : ℂ) * ζ ^ 22 - ((9 / 2) : ℂ) * ζ ^ 23 + ((15 / 2) : ℂ) * ζ ^ 24 + (3 : ℂ) * ζ ^ 25 - (8 : ℂ) * ζ ^ 26 - ((7 / 2) : ℂ) * ζ ^ 28 - (3 : ℂ) * ζ ^ 29 + (8 : ℂ) * ζ ^ 30)
private theorem row14_generatorB_mul_eigenbasis_0_1 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        0 1 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        0 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((5 / 11) : ℂ) - ((51 / 11) : ℂ) * ζ ^ 3 + ((5 / 11) : ℂ) * ζ ^ 4 + ((74 / 11) : ℂ) * ζ ^ 5 - ((24 / 11) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 - ((74 / 11) : ℂ) * ζ ^ 9 + (7 : ℂ) * ζ ^ 10 + ((29 / 11) : ℂ) * ζ ^ 13 - ((101 / 11) : ℂ) * ζ ^ 14 + ((40 / 11) : ℂ) * ζ ^ 15 + ((123 / 22) : ℂ) * ζ ^ 18 - ((40 / 11) : ℂ) * ζ ^ 19 - ((89 / 22) : ℂ) * ζ ^ 20 + ((24 / 11) : ℂ) * ζ ^ 22 - ((7 / 11) : ℂ) * ζ ^ 23 + ((89 / 22) : ℂ) * ζ ^ 24 - ((65 / 11) : ℂ) * ζ ^ 25 + ((24 / 11) : ℂ) * ζ ^ 26 - ((53 / 22) : ℂ) * ζ ^ 28 + ((65 / 11) : ℂ) * ζ ^ 29 - ((21 / 11) : ℂ) * ζ ^ 30 + ((2 / 11) : ℂ) * ζ ^ 33 - ((3 / 11) : ℂ) * ζ ^ 34 + ((8 / 11) : ℂ) * ζ ^ 35 + ((3 / 11) : ℂ) * ζ ^ 38 - ((8 / 11) : ℂ) * ζ ^ 39 - ((3 / 11) : ℂ) * ζ ^ 40 + ((8 / 11) : ℂ) * ζ ^ 43 + ((3 / 11) : ℂ) * ζ ^ 44)
private theorem row14_generatorB_mul_eigenbasis_0_2 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        0 2 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        0 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((135 / 22) : ℂ) - ((129 / 22) : ℂ) * ζ ^ 3 + ((135 / 22) : ℂ) * ζ ^ 4 + ((35 / 11) : ℂ) * ζ ^ 5 - ((29 / 11) : ℂ) * ζ ^ 6 - ((18 / 11) : ℂ) * ζ ^ 8 - ((35 / 11) : ℂ) * ζ ^ 9 + ((107 / 22) : ℂ) * ζ ^ 10 + ((3 / 2) : ℂ) * ζ ^ 13 - ((15 / 2) : ℂ) * ζ ^ 14 + ((31 / 11) : ℂ) * ζ ^ 15 + ((58 / 11) : ℂ) * ζ ^ 18 - ((31 / 11) : ℂ) * ζ ^ 19 - ((60 / 11) : ℂ) * ζ ^ 20 + ((29 / 11) : ℂ) * ζ ^ 22 - ((4 / 11) : ℂ) * ζ ^ 23 + ((60 / 11) : ℂ) * ζ ^ 24 - ((75 / 11) : ℂ) * ζ ^ 25 + ((29 / 11) : ℂ) * ζ ^ 26 - ((109 / 22) : ℂ) * ζ ^ 28 + ((75 / 11) : ℂ) * ζ ^ 29 - ((27 / 11) : ℂ) * ζ ^ 30 - ((1 / 11) : ℂ) * ζ ^ 33 - ((2 / 11) : ℂ) * ζ ^ 34 + ((3 / 11) : ℂ) * ζ ^ 35 + ((2 / 11) : ℂ) * ζ ^ 38 - ((3 / 11) : ℂ) * ζ ^ 39 + ((8 / 11) : ℂ) * ζ ^ 40 + ((3 / 11) : ℂ) * ζ ^ 43 - ((8 / 11) : ℂ) * ζ ^ 44)
private theorem row14_generatorB_mul_eigenbasis_0_3 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        0 3 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        0 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((7 / 2) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 3 + ((7 / 2) : ℂ) * ζ ^ 4 - ((49 / 6) : ℂ) * ζ ^ 5 + ((2 / 3) : ℂ) * ζ ^ 6 + ((5 / 2) : ℂ) * ζ ^ 8 + ((49 / 6) : ℂ) * ζ ^ 9 - ((13 / 2) : ℂ) * ζ ^ 10 - ((43 / 6) : ℂ) * ζ ^ 13 + ((43 / 6) : ℂ) * ζ ^ 14 - ((3 / 2) : ℂ) * ζ ^ 15 + ((7 / 6) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 19 - ((11 / 3) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 - ((7 / 6) : ℂ) * ζ ^ 23 + ((11 / 3) : ℂ) * ζ ^ 24 + ((5 / 2) : ℂ) * ζ ^ 25 - ((2 / 3) : ℂ) * ζ ^ 26 - ((5 / 6) : ℂ) * ζ ^ 28 - ((5 / 2) : ℂ) * ζ ^ 29 + ζ ^ 30 + ((4 / 3) : ℂ) * ζ ^ 33 - ((1 / 3) : ℂ) * ζ ^ 34 + ((2 / 3) : ℂ) * ζ ^ 35 + ((1 / 3) : ℂ) * ζ ^ 38 - ((2 / 3) : ℂ) * ζ ^ 39 + ((2 / 3) : ℂ) * ζ ^ 43 + ((2 / 3) : ℂ) * ζ ^ 45 - ((2 / 3) : ℂ) * ζ ^ 49 + ((2 / 3) : ℂ) * ζ ^ 50 + ((2 / 3) : ℂ) * ζ ^ 53 - ((2 / 3) : ℂ) * ζ ^ 54 - ((2 / 3) : ℂ) * ζ ^ 55 + ((2 / 3) : ℂ) * ζ ^ 58 + ((2 / 3) : ℂ) * ζ ^ 59 - ((2 / 3) : ℂ) * ζ ^ 63 - ((2 / 3) : ℂ) * ζ ^ 65 + ((2 / 3) : ℂ) * ζ ^ 69 + ((1 / 3) : ℂ) * ζ ^ 70 - ((2 / 3) : ℂ) * ζ ^ 73 - ((1 / 3) : ℂ) * ζ ^ 74)
private theorem row14_generatorB_mul_eigenbasis_0_4 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        0 4 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        0 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 ((6 : ℂ) + ((3 / 2) : ℂ) * ζ ^ 3 - (6 : ℂ) * ζ ^ 4 + ((17 / 2) : ℂ) * ζ ^ 5 - ((9 / 2) : ℂ) * ζ ^ 6 + (5 : ℂ) * ζ ^ 8 - ((17 / 2) : ℂ) * ζ ^ 9 + ((5 / 2) : ℂ) * ζ ^ 10 + ((11 / 2) : ℂ) * ζ ^ 13 - (7 : ℂ) * ζ ^ 14 + ((3 / 2) : ℂ) * ζ ^ 15 - ((3 / 2) : ℂ) * ζ ^ 18 - ((3 / 2) : ℂ) * ζ ^ 19 + ((3 / 2) : ℂ) * ζ ^ 20 + ((9 / 2) : ℂ) * ζ ^ 22 - (3 : ℂ) * ζ ^ 23 - ((3 / 2) : ℂ) * ζ ^ 24 - (7 : ℂ) * ζ ^ 25 + ((9 / 2) : ℂ) * ζ ^ 26 + ((3 / 2) : ℂ) * ζ ^ 28 + (7 : ℂ) * ζ ^ 29 - ((9 / 2) : ℂ) * ζ ^ 30 - ζ ^ 33 + ζ ^ 55 - ζ ^ 59 + ζ ^ 63 + ζ ^ 65 - ζ ^ 69 + ζ ^ 73)
private theorem row14_generatorB_mul_eigenbasis_0_5 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        0 5 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        0 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-(6 : ℂ) - (7 : ℂ) * ζ ^ 3 + (6 : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 5 - ((7 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 9 + (2 : ℂ) * ζ ^ 10 - (2 : ℂ) * ζ ^ 13 - (2 : ℂ) * ζ ^ 14 + ((9 / 2) : ℂ) * ζ ^ 15 - ((1 / 2) : ℂ) * ζ ^ 18 - ((9 / 2) : ℂ) * ζ ^ 19 + ((5 / 2) : ℂ) * ζ ^ 20 + ((5 / 2) : ℂ) * ζ ^ 23 - ((5 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 25 + ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 29 + ζ ^ 33 - ζ ^ 35 + ζ ^ 39 - ζ ^ 43 + ζ ^ 45 - ζ ^ 49 + ζ ^ 53 - ζ ^ 55 + ζ ^ 59 - ζ ^ 63 - ζ ^ 85 + ζ ^ 89 - ζ ^ 93 + ζ ^ 95 - ζ ^ 99 + ζ ^ 103)
private theorem row14_generatorB_mul_eigenbasis_1_0 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        1 0 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        1 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((3 / 4) : ℂ) + ((7 / 4) : ℂ) * ζ ^ 3 + ((3 / 4) : ℂ) * ζ ^ 4 - ((21 / 4) : ℂ) * ζ ^ 5 - ((19 / 4) : ℂ) * ζ ^ 6 + ζ ^ 8 + ((21 / 4) : ℂ) * ζ ^ 9 - ((13 / 4) : ℂ) * ζ ^ 10 - ((11 / 4) : ℂ) * ζ ^ 13 - ((3 / 2) : ℂ) * ζ ^ 14 + ((21 / 4) : ℂ) * ζ ^ 15 - ((21 / 4) : ℂ) * ζ ^ 19 + (6 : ℂ) * ζ ^ 20 + ((19 / 4) : ℂ) * ζ ^ 22 + ((9 / 4) : ℂ) * ζ ^ 23 - (6 : ℂ) * ζ ^ 24 + ((5 / 4) : ℂ) * ζ ^ 25 + ((19 / 4) : ℂ) * ζ ^ 26 + ((13 / 4) : ℂ) * ζ ^ 28 - ((5 / 4) : ℂ) * ζ ^ 29 - ((19 / 4) : ℂ) * ζ ^ 30)
private theorem row14_generatorB_mul_eigenbasis_1_1 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        1 1 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        1 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 ((2 : ℂ) + ((53 / 11) : ℂ) * ζ ^ 3 - (2 : ℂ) * ζ ^ 4 - ((31 / 22) : ℂ) * ζ ^ 5 + ((23 / 11) : ℂ) * ζ ^ 6 + ((37 / 11) : ℂ) * ζ ^ 8 + ((31 / 22) : ℂ) * ζ ^ 9 - ((25 / 11) : ℂ) * ζ ^ 10 + ((27 / 11) : ℂ) * ζ ^ 13 + ((48 / 11) : ℂ) * ζ ^ 14 - ((27 / 22) : ℂ) * ζ ^ 15 - ((21 / 11) : ℂ) * ζ ^ 18 + ((27 / 22) : ℂ) * ζ ^ 19 + ((53 / 22) : ℂ) * ζ ^ 20 - ((23 / 11) : ℂ) * ζ ^ 22 + ((31 / 22) : ℂ) * ζ ^ 23 - ((53 / 22) : ℂ) * ζ ^ 24 + ((75 / 22) : ℂ) * ζ ^ 25 - ((23 / 11) : ℂ) * ζ ^ 26 + ((12 / 11) : ℂ) * ζ ^ 28 - ((75 / 22) : ℂ) * ζ ^ 29 + ((20 / 11) : ℂ) * ζ ^ 30 + ((3 / 11) : ℂ) * ζ ^ 34 + ((5 / 11) : ℂ) * ζ ^ 35 - ((3 / 11) : ℂ) * ζ ^ 38 - ((5 / 11) : ℂ) * ζ ^ 39 - ((4 / 11) : ℂ) * ζ ^ 40 + ((5 / 11) : ℂ) * ζ ^ 43 + ((4 / 11) : ℂ) * ζ ^ 44)
private theorem row14_generatorB_mul_eigenbasis_1_2 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        1 2 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        1 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((181 / 44) : ℂ) + ((137 / 44) : ℂ) * ζ ^ 3 - ((181 / 44) : ℂ) * ζ ^ 4 + ((71 / 44) : ℂ) * ζ ^ 5 + ((111 / 44) : ℂ) * ζ ^ 6 + ((20 / 11) : ℂ) * ζ ^ 8 - ((71 / 44) : ℂ) * ζ ^ 9 + ((89 / 44) : ℂ) * ζ ^ 10 + ((149 / 44) : ℂ) * ζ ^ 13 + ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 44) : ℂ) * ζ ^ 15 - ((57 / 22) : ℂ) * ζ ^ 18 - ((1 / 44) : ℂ) * ζ ^ 19 + ((45 / 11) : ℂ) * ζ ^ 20 - ((111 / 44) : ℂ) * ζ ^ 22 + ((35 / 44) : ℂ) * ζ ^ 23 - ((45 / 11) : ℂ) * ζ ^ 24 + ((281 / 44) : ℂ) * ζ ^ 25 - ((111 / 44) : ℂ) * ζ ^ 26 + ((119 / 44) : ℂ) * ζ ^ 28 - ((281 / 44) : ℂ) * ζ ^ 29 + ((89 / 44) : ℂ) * ζ ^ 30 + ((5 / 22) : ℂ) * ζ ^ 33 + ((1 / 2) : ℂ) * ζ ^ 34 - ((3 / 11) : ℂ) * ζ ^ 35 - ((1 / 2) : ℂ) * ζ ^ 38 + ((3 / 11) : ℂ) * ζ ^ 39 - ((1 / 22) : ℂ) * ζ ^ 40 - ((3 / 11) : ℂ) * ζ ^ 43 + ((1 / 22) : ℂ) * ζ ^ 44)
private theorem row14_generatorB_mul_eigenbasis_1_3 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        1 3 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        1 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((14 / 3) : ℂ) - ((5 / 6) : ℂ) * ζ ^ 3 - ((14 / 3) : ℂ) * ζ ^ 4 + ((16 / 3) : ℂ) * ζ ^ 5 + ((2 / 3) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((16 / 3) : ℂ) * ζ ^ 9 + ((22 / 3) : ℂ) * ζ ^ 10 + ((7 / 2) : ℂ) * ζ ^ 13 - ((20 / 3) : ℂ) * ζ ^ 14 + (3 : ℂ) * ζ ^ 15 - ((13 / 6) : ℂ) * ζ ^ 18 - (3 : ℂ) * ζ ^ 19 + ((17 / 6) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 + ((7 / 3) : ℂ) * ζ ^ 23 - ((17 / 6) : ℂ) * ζ ^ 24 + ζ ^ 25 - ((2 / 3) : ℂ) * ζ ^ 26 - ((1 / 2) : ℂ) * ζ ^ 28 - ζ ^ 29 + ζ ^ 30 - ((1 / 3) : ℂ) * ζ ^ 33 - ((1 / 3) : ℂ) * ζ ^ 34 + ζ ^ 35 + ((1 / 3) : ℂ) * ζ ^ 38 - ζ ^ 39 - ((2 / 3) : ℂ) * ζ ^ 40 + ζ ^ 43 + ((2 / 3) : ℂ) * ζ ^ 44 - ((2 / 3) : ℂ) * ζ ^ 45 - ((2 / 3) : ℂ) * ζ ^ 48 + ((2 / 3) : ℂ) * ζ ^ 49 - ((1 / 3) : ℂ) * ζ ^ 50 - ((2 / 3) : ℂ) * ζ ^ 53 + ((1 / 3) : ℂ) * ζ ^ 54 - ((1 / 3) : ℂ) * ζ ^ 58 - ((1 / 3) : ℂ) * ζ ^ 60 + ((1 / 3) : ℂ) * ζ ^ 64 - ((1 / 3) : ℂ) * ζ ^ 65 - ((1 / 3) : ℂ) * ζ ^ 68 + ((1 / 3) : ℂ) * ζ ^ 69 - ((2 / 3) : ℂ) * ζ ^ 70 - ((1 / 3) : ℂ) * ζ ^ 73 + ((2 / 3) : ℂ) * ζ ^ 74)
private theorem row14_generatorB_mul_eigenbasis_1_4 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        1 4 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        1 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((9 / 4) : ℂ) + ((9 / 4) : ℂ) * ζ ^ 3 + ((9 / 4) : ℂ) * ζ ^ 4 - ((17 / 4) : ℂ) * ζ ^ 5 + ((11 / 4) : ℂ) * ζ ^ 6 + (2 : ℂ) * ζ ^ 8 + ((17 / 4) : ℂ) * ζ ^ 9 - ((7 / 4) : ℂ) * ζ ^ 10 - ((9 / 4) : ℂ) * ζ ^ 13 + ((9 / 2) : ℂ) * ζ ^ 14 - ((5 / 4) : ℂ) * ζ ^ 15 + ((3 / 2) : ℂ) * ζ ^ 18 + ((5 / 4) : ℂ) * ζ ^ 19 - ((11 / 4) : ℂ) * ζ ^ 22 + ((5 / 4) : ℂ) * ζ ^ 23 + ((1 / 4) : ℂ) * ζ ^ 25 - ((11 / 4) : ℂ) * ζ ^ 26 + ((1 / 4) : ℂ) * ζ ^ 28 - ((1 / 4) : ℂ) * ζ ^ 29 + ((9 / 4) : ℂ) * ζ ^ 30 - ((1 / 2) : ℂ) * ζ ^ 33 + ((1 / 2) : ℂ) * ζ ^ 34 - ((1 / 2) : ℂ) * ζ ^ 38 + ((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 44 + ((1 / 2) : ℂ) * ζ ^ 45 + ((1 / 2) : ℂ) * ζ ^ 48 - ((1 / 2) : ℂ) * ζ ^ 49 + ((1 / 2) : ℂ) * ζ ^ 53 + ((1 / 2) : ℂ) * ζ ^ 55 - ((1 / 2) : ℂ) * ζ ^ 59 - ((1 / 2) : ℂ) * ζ ^ 60 + ((1 / 2) : ℂ) * ζ ^ 63 + ((1 / 2) : ℂ) * ζ ^ 64 + ζ ^ 65 - ((1 / 2) : ℂ) * ζ ^ 68 - ζ ^ 69 + ((1 / 2) : ℂ) * ζ ^ 70 + ζ ^ 73 - ((1 / 2) : ℂ) * ζ ^ 74)
private theorem row14_generatorB_mul_eigenbasis_1_5 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        1 5 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        1 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((21 / 4) : ℂ) + ((19 / 4) : ℂ) * ζ ^ 3 - ((21 / 4) : ℂ) * ζ ^ 4 + ((15 / 4) : ℂ) * ζ ^ 5 + ((3 / 4) : ℂ) * ζ ^ 6 + ((7 / 2) : ℂ) * ζ ^ 8 - ((15 / 4) : ℂ) * ζ ^ 9 + ((9 / 4) : ℂ) * ζ ^ 10 + ((23 / 4) : ℂ) * ζ ^ 13 - ((3 / 2) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 15 + (3 : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 19 + ζ ^ 20 - ((3 / 4) : ℂ) * ζ ^ 22 + ((5 / 4) : ℂ) * ζ ^ 23 - ζ ^ 24 + ((9 / 4) : ℂ) * ζ ^ 25 - ((3 / 4) : ℂ) * ζ ^ 26 + ((5 / 4) : ℂ) * ζ ^ 28 - ((9 / 4) : ℂ) * ζ ^ 29 + ((5 / 4) : ℂ) * ζ ^ 30 + ((1 / 2) : ℂ) * ζ ^ 33 - ((1 / 2) : ℂ) * ζ ^ 34 + ((1 / 2) : ℂ) * ζ ^ 38 + ((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 44 + ((1 / 2) : ℂ) * ζ ^ 45 + ((1 / 2) : ℂ) * ζ ^ 48 - ((1 / 2) : ℂ) * ζ ^ 49 + ((1 / 2) : ℂ) * ζ ^ 53 - ((1 / 2) : ℂ) * ζ ^ 55 + ((1 / 2) : ℂ) * ζ ^ 59 + ((1 / 2) : ℂ) * ζ ^ 60 - ((1 / 2) : ℂ) * ζ ^ 63 - ((1 / 2) : ℂ) * ζ ^ 64 + ((1 / 2) : ℂ) * ζ ^ 68 - ((1 / 2) : ℂ) * ζ ^ 70 + ((1 / 2) : ℂ) * ζ ^ 74 - ((1 / 2) : ℂ) * ζ ^ 75 - ((1 / 2) : ℂ) * ζ ^ 78 + ((1 / 2) : ℂ) * ζ ^ 79 - ((1 / 2) : ℂ) * ζ ^ 83 - ((1 / 2) : ℂ) * ζ ^ 85 + ((1 / 2) : ℂ) * ζ ^ 89 - ((1 / 2) : ℂ) * ζ ^ 90 - ((1 / 2) : ℂ) * ζ ^ 93 + ((1 / 2) : ℂ) * ζ ^ 94 - ((1 / 2) : ℂ) * ζ ^ 98 - ((1 / 2) : ℂ) * ζ ^ 100 + ((1 / 2) : ℂ) * ζ ^ 104)
private theorem row14_generatorB_mul_eigenbasis_2_0 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        2 0 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        2 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((5 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 3 - ((5 / 2) : ℂ) * ζ ^ 4 + (3 : ℂ) * ζ ^ 8 - (6 : ℂ) * ζ ^ 10 + ((5 / 2) : ℂ) * ζ ^ 13 + (6 : ℂ) * ζ ^ 14 - (4 : ℂ) * ζ ^ 15 - ((1 / 2) : ℂ) * ζ ^ 18 + (4 : ℂ) * ζ ^ 19 + ((1 / 2) : ℂ) * ζ ^ 20 - ((5 / 2) : ℂ) * ζ ^ 23 - ((1 / 2) : ℂ) * ζ ^ 24 + ((7 / 2) : ℂ) * ζ ^ 25 - ((5 / 2) : ℂ) * ζ ^ 28 - ((7 / 2) : ℂ) * ζ ^ 29)
private theorem row14_generatorB_mul_eigenbasis_2_1 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        2 1 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        2 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((8 / 11) : ℂ) + ((10 / 11) : ℂ) * ζ ^ 3 - ((8 / 11) : ℂ) * ζ ^ 4 + ((15 / 11) : ℂ) * ζ ^ 5 + ((9 / 11) : ℂ) * ζ ^ 6 + ((3 / 2) : ℂ) * ζ ^ 8 - ((15 / 11) : ℂ) * ζ ^ 9 + ((9 / 11) : ℂ) * ζ ^ 10 + ((12 / 11) : ℂ) * ζ ^ 13 - ((37 / 11) : ℂ) * ζ ^ 15 - ((19 / 22) : ℂ) * ζ ^ 18 + ((37 / 11) : ℂ) * ζ ^ 19 - ((63 / 22) : ℂ) * ζ ^ 20 - ((9 / 11) : ℂ) * ζ ^ 22 - ((42 / 11) : ℂ) * ζ ^ 23 + ((63 / 22) : ℂ) * ζ ^ 24 - ((5 / 11) : ℂ) * ζ ^ 25 - ((9 / 11) : ℂ) * ζ ^ 26 - ((57 / 22) : ℂ) * ζ ^ 28 + ((5 / 11) : ℂ) * ζ ^ 29 + ((12 / 11) : ℂ) * ζ ^ 30 - ((4 / 11) : ℂ) * ζ ^ 33 - ((3 / 11) : ℂ) * ζ ^ 34 + ((2 / 11) : ℂ) * ζ ^ 35 + ((3 / 11) : ℂ) * ζ ^ 38 - ((2 / 11) : ℂ) * ζ ^ 39 + ((7 / 11) : ℂ) * ζ ^ 40 + ((2 / 11) : ℂ) * ζ ^ 43 - ((7 / 11) : ℂ) * ζ ^ 44)
private theorem row14_generatorB_mul_eigenbasis_2_2 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        2 2 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        2 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((47 / 22) : ℂ) + ((25 / 11) : ℂ) * ζ ^ 3 - ((47 / 22) : ℂ) * ζ ^ 4 + ((29 / 11) : ℂ) * ζ ^ 5 + ((7 / 11) : ℂ) * ζ ^ 6 - ((3 / 22) : ℂ) * ζ ^ 8 - ((29 / 11) : ℂ) * ζ ^ 9 + ((49 / 22) : ℂ) * ζ ^ 10 + ((13 / 11) : ℂ) * ζ ^ 13 - ((35 / 22) : ℂ) * ζ ^ 14 - ((53 / 22) : ℂ) * ζ ^ 15 + ((29 / 22) : ℂ) * ζ ^ 18 + ((53 / 22) : ℂ) * ζ ^ 19 - ((105 / 22) : ℂ) * ζ ^ 20 - ((7 / 11) : ℂ) * ζ ^ 22 - ((83 / 22) : ℂ) * ζ ^ 23 + ((105 / 22) : ℂ) * ζ ^ 24 - ((45 / 22) : ℂ) * ζ ^ 25 - ((7 / 11) : ℂ) * ζ ^ 26 - ((32 / 11) : ℂ) * ζ ^ 28 + ((45 / 22) : ℂ) * ζ ^ 29 + ((17 / 22) : ℂ) * ζ ^ 30 - ((3 / 22) : ℂ) * ζ ^ 34 + ((17 / 22) : ℂ) * ζ ^ 35 + ((3 / 22) : ℂ) * ζ ^ 38 - ((17 / 22) : ℂ) * ζ ^ 39 + ((2 / 11) : ℂ) * ζ ^ 40 + ((17 / 22) : ℂ) * ζ ^ 43 - ((2 / 11) : ℂ) * ζ ^ 44)
private theorem row14_generatorB_mul_eigenbasis_2_3 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        2 3 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        2 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((7 / 2) : ℂ) - ((19 / 6) : ℂ) * ζ ^ 3 + ((7 / 2) : ℂ) * ζ ^ 4 - ((5 / 2) : ℂ) * ζ ^ 5 - ((1 / 3) : ℂ) * ζ ^ 6 - ((49 / 6) : ℂ) * ζ ^ 8 + ((5 / 2) : ℂ) * ζ ^ 9 + ((17 / 6) : ℂ) * ζ ^ 10 - ((17 / 6) : ℂ) * ζ ^ 13 - ((19 / 6) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 15 + ((11 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 19 + (2 : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 23 - (2 : ℂ) * ζ ^ 24 - ((13 / 6) : ℂ) * ζ ^ 25 + ((1 / 3) : ℂ) * ζ ^ 26 + ((17 / 6) : ℂ) * ζ ^ 28 + ((13 / 6) : ℂ) * ζ ^ 29 + ((4 / 3) : ℂ) * ζ ^ 30 - ((2 / 3) : ℂ) * ζ ^ 33 - ((5 / 3) : ℂ) * ζ ^ 34 + ((5 / 3) : ℂ) * ζ ^ 38 + ((5 / 3) : ℂ) * ζ ^ 40 - ((5 / 3) : ℂ) * ζ ^ 44 - ((1 / 3) : ℂ) * ζ ^ 45 + ((5 / 3) : ℂ) * ζ ^ 48 + ((1 / 3) : ℂ) * ζ ^ 49 + ((4 / 3) : ℂ) * ζ ^ 50 - ((1 / 3) : ℂ) * ζ ^ 53 - ((4 / 3) : ℂ) * ζ ^ 54 + ((4 / 3) : ℂ) * ζ ^ 58 + ((1 / 3) : ℂ) * ζ ^ 60 - ((1 / 3) : ℂ) * ζ ^ 64 + ((1 / 3) : ℂ) * ζ ^ 65 + ((1 / 3) : ℂ) * ζ ^ 68 - ((1 / 3) : ℂ) * ζ ^ 69 - ((1 / 3) : ℂ) * ζ ^ 70 + ((1 / 3) : ℂ) * ζ ^ 73 + ((1 / 3) : ℂ) * ζ ^ 74)
private theorem row14_generatorB_mul_eigenbasis_2_4 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        2 4 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        2 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 ((1 : ℂ) + (6 : ℂ) * ζ ^ 3 - ζ ^ 4 + ((3 / 2) : ℂ) * ζ ^ 5 + ((3 / 2) : ℂ) * ζ ^ 6 + ((9 / 2) : ℂ) * ζ ^ 8 - ((3 / 2) : ℂ) * ζ ^ 9 - ((7 / 2) : ℂ) * ζ ^ 10 + (5 : ℂ) * ζ ^ 14 - (6 : ℂ) * ζ ^ 18 - (3 : ℂ) * ζ ^ 20 - ((3 / 2) : ℂ) * ζ ^ 22 - ((3 / 2) : ℂ) * ζ ^ 23 + (3 : ℂ) * ζ ^ 24 - ((3 / 2) : ℂ) * ζ ^ 25 - ((3 / 2) : ℂ) * ζ ^ 26 - (3 : ℂ) * ζ ^ 28 + ((3 / 2) : ℂ) * ζ ^ 29 + ((3 / 2) : ℂ) * ζ ^ 34 + ((1 / 2) : ℂ) * ζ ^ 35 - ((3 / 2) : ℂ) * ζ ^ 38 - ((1 / 2) : ℂ) * ζ ^ 39 - ζ ^ 40 + ((1 / 2) : ℂ) * ζ ^ 43 + ζ ^ 44 - ((1 / 2) : ℂ) * ζ ^ 45 - ζ ^ 48 + ((1 / 2) : ℂ) * ζ ^ 49 - ((1 / 2) : ℂ) * ζ ^ 50 - ((1 / 2) : ℂ) * ζ ^ 53 + ((1 / 2) : ℂ) * ζ ^ 54 - ((1 / 2) : ℂ) * ζ ^ 58 + ((1 / 2) : ℂ) * ζ ^ 60 - ((1 / 2) : ℂ) * ζ ^ 64 - ((1 / 2) : ℂ) * ζ ^ 65 + ((1 / 2) : ℂ) * ζ ^ 68 + ((1 / 2) : ℂ) * ζ ^ 69 + ζ ^ 70 - ((1 / 2) : ℂ) * ζ ^ 73 - ζ ^ 74)
private theorem row14_generatorB_mul_eigenbasis_2_5 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        2 5 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        2 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 ((2 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 3 - (2 : ℂ) * ζ ^ 4 + ((3 / 2) : ℂ) * ζ ^ 5 - ((3 / 2) : ℂ) * ζ ^ 9 + (3 : ℂ) * ζ ^ 10 + ((3 / 2) : ℂ) * ζ ^ 13 - (3 : ℂ) * ζ ^ 14 - ζ ^ 15 + (4 : ℂ) * ζ ^ 18 + ζ ^ 19 - (4 : ℂ) * ζ ^ 20 - ζ ^ 23 + (4 : ℂ) * ζ ^ 24 - ζ ^ 25 - ((5 / 2) : ℂ) * ζ ^ 28 + ζ ^ 29 + ((1 / 2) : ℂ) * ζ ^ 30 - ((1 / 2) : ℂ) * ζ ^ 34 + ((1 / 2) : ℂ) * ζ ^ 35 + ((1 / 2) : ℂ) * ζ ^ 38 - ((1 / 2) : ℂ) * ζ ^ 39 + ((1 / 2) : ℂ) * ζ ^ 43 - ((1 / 2) : ℂ) * ζ ^ 45 + ((1 / 2) : ℂ) * ζ ^ 49 + ((1 / 2) : ℂ) * ζ ^ 50 - ((1 / 2) : ℂ) * ζ ^ 53 - ((1 / 2) : ℂ) * ζ ^ 54 + ((1 / 2) : ℂ) * ζ ^ 58 - ((1 / 2) : ℂ) * ζ ^ 60 + ((1 / 2) : ℂ) * ζ ^ 64 - ((1 / 2) : ℂ) * ζ ^ 65 - ((1 / 2) : ℂ) * ζ ^ 68 + ((1 / 2) : ℂ) * ζ ^ 69 - ((1 / 2) : ℂ) * ζ ^ 73 - ((1 / 2) : ℂ) * ζ ^ 75 + ((1 / 2) : ℂ) * ζ ^ 79 - ((1 / 2) : ℂ) * ζ ^ 80 - ((1 / 2) : ℂ) * ζ ^ 83 + ((1 / 2) : ℂ) * ζ ^ 84 - ((1 / 2) : ℂ) * ζ ^ 88 - ((1 / 2) : ℂ) * ζ ^ 90 + ((1 / 2) : ℂ) * ζ ^ 94 - ((1 / 2) : ℂ) * ζ ^ 95 - ((1 / 2) : ℂ) * ζ ^ 98 + ((1 / 2) : ℂ) * ζ ^ 99 - ((1 / 2) : ℂ) * ζ ^ 103)
private theorem row14_generatorB_mul_eigenbasis_3_0 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        3 0 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        3 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((3 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 3 + ((3 / 4) : ℂ) * ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 5 + ((1 / 4) : ℂ) * ζ ^ 6 - (2 : ℂ) * ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 9 + ((11 / 4) : ℂ) * ζ ^ 10 - ((3 / 4) : ℂ) * ζ ^ 13 - ((5 / 2) : ℂ) * ζ ^ 14 + ((7 / 4) : ℂ) * ζ ^ 15 - ((1 / 2) : ℂ) * ζ ^ 18 - ((7 / 4) : ℂ) * ζ ^ 19 - ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 22 - ((3 / 4) : ℂ) * ζ ^ 23 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 25 - ((1 / 4) : ℂ) * ζ ^ 26 + ((3 / 4) : ℂ) * ζ ^ 28 + ((1 / 4) : ℂ) * ζ ^ 29 + ((1 / 4) : ℂ) * ζ ^ 30)
private theorem row14_generatorB_mul_eigenbasis_3_1 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        3 1 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        3 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((4 / 11) : ℂ) + ((9 / 11) : ℂ) * ζ ^ 3 - ((4 / 11) : ℂ) * ζ ^ 4 - ((5 / 22) : ℂ) * ζ ^ 5 - ((7 / 11) : ℂ) * ζ ^ 6 - ((23 / 22) : ℂ) * ζ ^ 8 + ((5 / 22) : ℂ) * ζ ^ 9 + ((3 / 11) : ℂ) * ζ ^ 10 + ((5 / 11) : ℂ) * ζ ^ 13 - ((10 / 11) : ℂ) * ζ ^ 14 + ((37 / 22) : ℂ) * ζ ^ 15 + ((35 / 22) : ℂ) * ζ ^ 18 - ((37 / 22) : ℂ) * ζ ^ 19 + ((18 / 11) : ℂ) * ζ ^ 20 + ((7 / 11) : ℂ) * ζ ^ 22 + ((43 / 22) : ℂ) * ζ ^ 23 - ((18 / 11) : ℂ) * ζ ^ 24 + ((9 / 22) : ℂ) * ζ ^ 25 + ((7 / 11) : ℂ) * ζ ^ 26 + ((37 / 22) : ℂ) * ζ ^ 28 - ((9 / 22) : ℂ) * ζ ^ 29 - ((7 / 11) : ℂ) * ζ ^ 30)
private theorem row14_generatorB_mul_eigenbasis_3_2 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        3 2 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        3 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((9 / 4) : ℂ) + ((21 / 44) : ℂ) * ζ ^ 3 + ((9 / 4) : ℂ) * ζ ^ 4 - ((79 / 44) : ℂ) * ζ ^ 5 + ((59 / 44) : ℂ) * ζ ^ 6 - ((29 / 22) : ℂ) * ζ ^ 8 + ((79 / 44) : ℂ) * ζ ^ 9 + ((43 / 44) : ℂ) * ζ ^ 10 + ((39 / 44) : ℂ) * ζ ^ 13 + ((4 / 11) : ℂ) * ζ ^ 14 + ((69 / 44) : ℂ) * ζ ^ 15 - ((5 / 22) : ℂ) * ζ ^ 18 - ((69 / 44) : ℂ) * ζ ^ 19 + ((35 / 11) : ℂ) * ζ ^ 20 - ((59 / 44) : ℂ) * ζ ^ 22 + ((35 / 44) : ℂ) * ζ ^ 23 - ((35 / 11) : ℂ) * ζ ^ 24 + ((93 / 44) : ℂ) * ζ ^ 25 - ((59 / 44) : ℂ) * ζ ^ 26 + ((53 / 44) : ℂ) * ζ ^ 28 - ((93 / 44) : ℂ) * ζ ^ 29 + ((59 / 44) : ℂ) * ζ ^ 30)
private theorem row14_generatorB_mul_eigenbasis_3_3 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        3 3 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        3 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((1 / 2) : ℂ) + (2 : ℂ) * ζ ^ 3 + ((1 / 2) : ℂ) * ζ ^ 4 + ((5 / 2) : ℂ) * ζ ^ 5 + (2 : ℂ) * ζ ^ 6 + ((4 / 3) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 9 - ((3 / 2) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 13 + ((7 / 2) : ℂ) * ζ ^ 14 - ((5 / 6) : ℂ) * ζ ^ 15 - ((10 / 3) : ℂ) * ζ ^ 18 + ((5 / 6) : ℂ) * ζ ^ 19 - ((1 / 2) : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 23 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 25 - (2 : ℂ) * ζ ^ 26 - ((4 / 3) : ℂ) * ζ ^ 28 + ((1 / 6) : ℂ) * ζ ^ 29 + (2 : ℂ) * ζ ^ 30)
private theorem row14_generatorB_mul_eigenbasis_3_4 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        3 4 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        3 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((5 / 4) : ℂ) - ((7 / 4) : ℂ) * ζ ^ 3 - ((5 / 4) : ℂ) * ζ ^ 4 + ((3 / 4) : ℂ) * ζ ^ 5 - ((7 / 4) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 9 + ((7 / 4) : ℂ) * ζ ^ 10 + ((9 / 4) : ℂ) * ζ ^ 13 - ((7 / 2) : ℂ) * ζ ^ 14 + ((5 / 4) : ℂ) * ζ ^ 15 + (4 : ℂ) * ζ ^ 18 - ((5 / 4) : ℂ) * ζ ^ 19 + ((3 / 2) : ℂ) * ζ ^ 20 + ((7 / 4) : ℂ) * ζ ^ 22 + ((5 / 4) : ℂ) * ζ ^ 23 - ((3 / 2) : ℂ) * ζ ^ 24 + ((5 / 4) : ℂ) * ζ ^ 25 + ((7 / 4) : ℂ) * ζ ^ 26 + ((7 / 4) : ℂ) * ζ ^ 28 - ((5 / 4) : ℂ) * ζ ^ 29 - ((7 / 4) : ℂ) * ζ ^ 30 - ζ ^ 35 + ζ ^ 39 - ζ ^ 43)
private theorem row14_generatorB_mul_eigenbasis_3_5 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        3 5 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        3 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((13 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 3 + ((13 / 4) : ℂ) * ζ ^ 4 - ((9 / 4) : ℂ) * ζ ^ 5 + ((3 / 4) : ℂ) * ζ ^ 6 - ((5 / 2) : ℂ) * ζ ^ 8 + ((9 / 4) : ℂ) * ζ ^ 9 + ((5 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 13 - ((1 / 2) : ℂ) * ζ ^ 14 + ((3 / 4) : ℂ) * ζ ^ 15 + ((1 / 2) : ℂ) * ζ ^ 18 - ((3 / 4) : ℂ) * ζ ^ 19 + ((7 / 2) : ℂ) * ζ ^ 20 - ((3 / 4) : ℂ) * ζ ^ 22 + ((7 / 4) : ℂ) * ζ ^ 23 - ((7 / 2) : ℂ) * ζ ^ 24 + ((11 / 4) : ℂ) * ζ ^ 25 - ((3 / 4) : ℂ) * ζ ^ 26 + ((9 / 4) : ℂ) * ζ ^ 28 - ((11 / 4) : ℂ) * ζ ^ 29 + ((3 / 4) : ℂ) * ζ ^ 30 + ζ ^ 45 - ζ ^ 49 + ζ ^ 53 + ζ ^ 65 - ζ ^ 69 + ζ ^ 73)
private theorem row14_generatorB_mul_eigenbasis_4_0 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        4 0 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        4 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((13 / 2) : ℂ) + ((13 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 5 - ((7 / 2) : ℂ) * ζ ^ 6 - ((9 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 9 + ((13 / 2) : ℂ) * ζ ^ 10 - (5 : ℂ) * ζ ^ 13 - (10 : ℂ) * ζ ^ 14 + ((19 / 2) : ℂ) * ζ ^ 15 + ((7 / 2) : ℂ) * ζ ^ 18 - ((19 / 2) : ℂ) * ζ ^ 19 - (3 : ℂ) * ζ ^ 20 + ((7 / 2) : ℂ) * ζ ^ 22 + (6 : ℂ) * ζ ^ 23 + (3 : ℂ) * ζ ^ 24 - ((21 / 2) : ℂ) * ζ ^ 25 + ((7 / 2) : ℂ) * ζ ^ 26 + (3 : ℂ) * ζ ^ 28 + ((21 / 2) : ℂ) * ζ ^ 29 - ((7 / 2) : ℂ) * ζ ^ 30)
private theorem row14_generatorB_mul_eigenbasis_4_1 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        4 1 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        4 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-(4 : ℂ) - ((14 / 11) : ℂ) * ζ ^ 3 + (4 : ℂ) * ζ ^ 4 - ((80 / 11) : ℂ) * ζ ^ 5 - ((4 / 11) : ℂ) * ζ ^ 6 - (5 : ℂ) * ζ ^ 8 + ((80 / 11) : ℂ) * ζ ^ 9 - ((60 / 11) : ℂ) * ζ ^ 10 - ((82 / 11) : ℂ) * ζ ^ 13 + ((56 / 11) : ℂ) * ζ ^ 14 + ((34 / 11) : ℂ) * ζ ^ 15 - ((29 / 11) : ℂ) * ζ ^ 18 - ((34 / 11) : ℂ) * ζ ^ 19 + ((36 / 11) : ℂ) * ζ ^ 20 + ((4 / 11) : ℂ) * ζ ^ 22 + ((49 / 11) : ℂ) * ζ ^ 23 - ((36 / 11) : ℂ) * ζ ^ 24 + ((6 / 11) : ℂ) * ζ ^ 25 + ((4 / 11) : ℂ) * ζ ^ 26 + ((36 / 11) : ℂ) * ζ ^ 28 - ((6 / 11) : ℂ) * ζ ^ 29 - ((4 / 11) : ℂ) * ζ ^ 30)
private theorem row14_generatorB_mul_eigenbasis_4_2 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        4 2 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        4 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((31 / 22) : ℂ) + ((20 / 11) : ℂ) * ζ ^ 3 - ((31 / 22) : ℂ) * ζ ^ 4 - ((83 / 22) : ℂ) * ζ ^ 5 - ((87 / 22) : ℂ) * ζ ^ 6 - ((9 / 22) : ℂ) * ζ ^ 8 + ((83 / 22) : ℂ) * ζ ^ 9 - ((193 / 22) : ℂ) * ζ ^ 10 - ((57 / 11) : ℂ) * ζ ^ 13 + ((53 / 11) : ℂ) * ζ ^ 14 + ((7 / 2) : ℂ) * ζ ^ 15 - ((35 / 22) : ℂ) * ζ ^ 18 - ((7 / 2) : ℂ) * ζ ^ 19 + ((65 / 11) : ℂ) * ζ ^ 20 + ((87 / 22) : ℂ) * ζ ^ 22 + ((64 / 11) : ℂ) * ζ ^ 23 - ((65 / 11) : ℂ) * ζ ^ 24 + ((7 / 22) : ℂ) * ζ ^ 25 + ((87 / 22) : ℂ) * ζ ^ 26 + ((60 / 11) : ℂ) * ζ ^ 28 - ((7 / 22) : ℂ) * ζ ^ 29 - ((87 / 22) : ℂ) * ζ ^ 30)
private theorem row14_generatorB_mul_eigenbasis_4_3 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        4 3 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        4 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((13 / 3) : ℂ) + (7 : ℂ) * ζ ^ 3 - ((13 / 3) : ℂ) * ζ ^ 4 + ((11 / 3) : ℂ) * ζ ^ 5 - ((10 / 3) : ℂ) * ζ ^ 6 + ((23 / 3) : ℂ) * ζ ^ 8 - ((11 / 3) : ℂ) * ζ ^ 9 - ((13 / 3) : ℂ) * ζ ^ 10 + ((23 / 3) : ℂ) * ζ ^ 13 + ζ ^ 14 + (4 : ℂ) * ζ ^ 15 + ((5 / 3) : ℂ) * ζ ^ 18 - (4 : ℂ) * ζ ^ 19 - ((1 / 3) : ℂ) * ζ ^ 20 + ((10 / 3) : ℂ) * ζ ^ 22 + ζ ^ 23 + ((1 / 3) : ℂ) * ζ ^ 24 + ζ ^ 25 + ((10 / 3) : ℂ) * ζ ^ 26 - ζ ^ 29 - ((10 / 3) : ℂ) * ζ ^ 30 - ζ ^ 35 + ζ ^ 39 - ζ ^ 43)
private theorem row14_generatorB_mul_eigenbasis_4_4 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        4 4 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        4 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((11 / 2) : ℂ) - (12 : ℂ) * ζ ^ 3 + ((11 / 2) : ℂ) * ζ ^ 4 - ((11 / 2) : ℂ) * ζ ^ 5 + ((1 / 2) : ℂ) * ζ ^ 6 - ((23 / 2) : ℂ) * ζ ^ 8 + ((11 / 2) : ℂ) * ζ ^ 9 - ((1 / 2) : ℂ) * ζ ^ 10 - (3 : ℂ) * ζ ^ 13 + ζ ^ 14 - ((9 / 2) : ℂ) * ζ ^ 15 + ((7 / 2) : ℂ) * ζ ^ 18 + ((9 / 2) : ℂ) * ζ ^ 19 + ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 + (2 : ℂ) * ζ ^ 23 - ζ ^ 24 + ((9 / 2) : ℂ) * ζ ^ 25 - ((1 / 2) : ℂ) * ζ ^ 26 - ((9 / 2) : ℂ) * ζ ^ 29 + ((1 / 2) : ℂ) * ζ ^ 30)
private theorem row14_generatorB_mul_eigenbasis_4_5 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        4 5 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        4 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((5 / 2) : ℂ) + (7 : ℂ) * ζ ^ 3 - ((5 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 5 - ((3 / 2) : ℂ) * ζ ^ 6 + ((7 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 9 - ((13 / 2) : ℂ) * ζ ^ 10 - (5 : ℂ) * ζ ^ 13 + (5 : ℂ) * ζ ^ 14 + ((3 / 2) : ℂ) * ζ ^ 15 - ((13 / 2) : ℂ) * ζ ^ 18 - ((3 / 2) : ℂ) * ζ ^ 19 + ((3 / 2) : ℂ) * ζ ^ 22 - (2 : ℂ) * ζ ^ 23 - ((9 / 2) : ℂ) * ζ ^ 25 + ((3 / 2) : ℂ) * ζ ^ 26 + ((9 / 2) : ℂ) * ζ ^ 29 - ((3 / 2) : ℂ) * ζ ^ 30)
private theorem row14_generatorB_mul_eigenbasis_5_0 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        5 0 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        5 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((45 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 3 + ((45 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 5 - ((9 / 4) : ℂ) * ζ ^ 6 - ((15 / 2) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 9 + ((43 / 4) : ℂ) * ζ ^ 10 - ((21 / 4) : ℂ) * ζ ^ 13 - (13 : ℂ) * ζ ^ 14 + ((37 / 4) : ℂ) * ζ ^ 15 + (4 : ℂ) * ζ ^ 18 - ((37 / 4) : ℂ) * ζ ^ 19 - ((11 / 2) : ℂ) * ζ ^ 20 + ((9 / 4) : ℂ) * ζ ^ 22 + ((9 / 4) : ℂ) * ζ ^ 23 + ((11 / 2) : ℂ) * ζ ^ 24 - ((49 / 4) : ℂ) * ζ ^ 25 + ((9 / 4) : ℂ) * ζ ^ 26 + ((9 / 4) : ℂ) * ζ ^ 28 + ((49 / 4) : ℂ) * ζ ^ 29 - ((9 / 4) : ℂ) * ζ ^ 30)
private theorem row14_generatorB_mul_eigenbasis_5_1 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        5 1 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        5 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((84 / 11) : ℂ) - ((25 / 11) : ℂ) * ζ ^ 3 + ((84 / 11) : ℂ) * ζ ^ 4 - ((261 / 22) : ℂ) * ζ ^ 5 - ((10 / 11) : ℂ) * ζ ^ 6 - ((199 / 22) : ℂ) * ζ ^ 8 + ((261 / 22) : ℂ) * ζ ^ 9 - ((84 / 11) : ℂ) * ζ ^ 10 - ((103 / 11) : ℂ) * ζ ^ 13 + ((74 / 11) : ℂ) * ζ ^ 14 + ((61 / 22) : ℂ) * ζ ^ 15 - ((9 / 2) : ℂ) * ζ ^ 18 - ((61 / 22) : ℂ) * ζ ^ 19 + (5 : ℂ) * ζ ^ 20 + ((10 / 11) : ℂ) * ζ ^ 22 + ((7 / 2) : ℂ) * ζ ^ 23 - (5 : ℂ) * ζ ^ 24 + ((85 / 22) : ℂ) * ζ ^ 25 + ((10 / 11) : ℂ) * ζ ^ 26 + ((53 / 22) : ℂ) * ζ ^ 28 - ((85 / 22) : ℂ) * ζ ^ 29 - ((10 / 11) : ℂ) * ζ ^ 30)
private theorem row14_generatorB_mul_eigenbasis_5_2 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        5 2 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        5 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((109 / 44) : ℂ) + ((161 / 44) : ℂ) * ζ ^ 3 + ((109 / 44) : ℂ) * ζ ^ 4 - ((453 / 44) : ℂ) * ζ ^ 5 - ((43 / 44) : ℂ) * ζ ^ 6 - ((75 / 11) : ℂ) * ζ ^ 8 + ((453 / 44) : ℂ) * ζ ^ 9 - ((409 / 44) : ℂ) * ζ ^ 10 - ((323 / 44) : ℂ) * ζ ^ 13 + ((183 / 22) : ℂ) * ζ ^ 14 + ((107 / 44) : ℂ) * ζ ^ 15 - ((32 / 11) : ℂ) * ζ ^ 18 - ((107 / 44) : ℂ) * ζ ^ 19 + ((57 / 11) : ℂ) * ζ ^ 20 + ((43 / 44) : ℂ) * ζ ^ 22 + ((207 / 44) : ℂ) * ζ ^ 23 - ((57 / 11) : ℂ) * ζ ^ 24 + ((9 / 44) : ℂ) * ζ ^ 25 + ((43 / 44) : ℂ) * ζ ^ 26 + ((243 / 44) : ℂ) * ζ ^ 28 - ((9 / 44) : ℂ) * ζ ^ 29 - ((43 / 44) : ℂ) * ζ ^ 30)
private theorem row14_generatorB_mul_eigenbasis_5_3 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        5 3 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        5 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((25 / 6) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 3 - ((25 / 6) : ℂ) * ζ ^ 4 + ((61 / 6) : ℂ) * ζ ^ 5 - ζ ^ 6 + ((13 / 3) : ℂ) * ζ ^ 8 - ((61 / 6) : ℂ) * ζ ^ 9 - ((1 / 6) : ℂ) * ζ ^ 10 + ((32 / 3) : ℂ) * ζ ^ 13 - ((5 / 6) : ℂ) * ζ ^ 14 + ((29 / 6) : ℂ) * ζ ^ 15 + ((7 / 3) : ℂ) * ζ ^ 18 - ((29 / 6) : ℂ) * ζ ^ 19 - ((17 / 6) : ℂ) * ζ ^ 20 + ζ ^ 22 + ((23 / 6) : ℂ) * ζ ^ 23 + ((17 / 6) : ℂ) * ζ ^ 24 - ((7 / 2) : ℂ) * ζ ^ 25 + ζ ^ 26 + ((5 / 3) : ℂ) * ζ ^ 28 + ((7 / 2) : ℂ) * ζ ^ 29 - ζ ^ 30)
private theorem row14_generatorB_mul_eigenbasis_5_4 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        5 4 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        5 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((33 / 4) : ℂ) - ((59 / 4) : ℂ) * ζ ^ 3 + ((33 / 4) : ℂ) * ζ ^ 4 - ((51 / 4) : ℂ) * ζ ^ 5 - ((1 / 4) : ℂ) * ζ ^ 6 - (13 : ℂ) * ζ ^ 8 + ((51 / 4) : ℂ) * ζ ^ 9 - ((17 / 4) : ℂ) * ζ ^ 10 - ((25 / 4) : ℂ) * ζ ^ 13 + (4 : ℂ) * ζ ^ 14 - ((13 / 4) : ℂ) * ζ ^ 15 + ((3 / 2) : ℂ) * ζ ^ 18 + ((13 / 4) : ℂ) * ζ ^ 19 + ((9 / 2) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 23 - ((9 / 2) : ℂ) * ζ ^ 24 + ((37 / 4) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 26 - ((7 / 4) : ℂ) * ζ ^ 28 - ((37 / 4) : ℂ) * ζ ^ 29 - ((1 / 4) : ℂ) * ζ ^ 30 - ζ ^ 35 + ζ ^ 39 - ζ ^ 43)
private theorem row14_generatorB_mul_eigenbasis_5_5 :
    (alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis)
        5 5 =
      (alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal)
        5 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row14_matrixB,
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14GeneratorBDiagonal,
      alternatingSixAmbientRow14GeneratorBEigenvalue,
      alternatingSixAmbientRow14EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((7 / 4) : ℂ) + ((33 / 4) : ℂ) * ζ ^ 3 + ((7 / 4) : ℂ) * ζ ^ 4 - ((15 / 4) : ℂ) * ζ ^ 5 - ((3 / 4) : ℂ) * ζ ^ 6 - (2 : ℂ) * ζ ^ 8 + ((15 / 4) : ℂ) * ζ ^ 9 - ((27 / 4) : ℂ) * ζ ^ 10 - ((15 / 4) : ℂ) * ζ ^ 13 + (6 : ℂ) * ζ ^ 14 - ((31 / 4) : ℂ) * ζ ^ 15 - (7 : ℂ) * ζ ^ 18 + ((31 / 4) : ℂ) * ζ ^ 19 - ((9 / 2) : ℂ) * ζ ^ 20 + ((3 / 4) : ℂ) * ζ ^ 22 - ((33 / 4) : ℂ) * ζ ^ 23 + ((9 / 2) : ℂ) * ζ ^ 24 - ((5 / 4) : ℂ) * ζ ^ 25 + ((3 / 4) : ℂ) * ζ ^ 26 - ((13 / 4) : ℂ) * ζ ^ 28 + ((5 / 4) : ℂ) * ζ ^ 29 - ((3 / 4) : ℂ) * ζ ^ 30 - ζ ^ 45 + ζ ^ 49 - ζ ^ 53 - ζ ^ 65 + ζ ^ 69 - ζ ^ 73)
/-- The checked row 14 basis diagonalizes the second
generator. -/
theorem alternatingSixAmbientRow14GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row14_matrixB *
        alternatingSixAmbientRow14Eigenbasis =
      alternatingSixAmbientRow14Eigenbasis *
        alternatingSixAmbientRow14GeneratorBDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row14_generatorB_mul_eigenbasis_0_0
  · exact row14_generatorB_mul_eigenbasis_0_1
  · exact row14_generatorB_mul_eigenbasis_0_2
  · exact row14_generatorB_mul_eigenbasis_0_3
  · exact row14_generatorB_mul_eigenbasis_0_4
  · exact row14_generatorB_mul_eigenbasis_0_5
  · exact row14_generatorB_mul_eigenbasis_1_0
  · exact row14_generatorB_mul_eigenbasis_1_1
  · exact row14_generatorB_mul_eigenbasis_1_2
  · exact row14_generatorB_mul_eigenbasis_1_3
  · exact row14_generatorB_mul_eigenbasis_1_4
  · exact row14_generatorB_mul_eigenbasis_1_5
  · exact row14_generatorB_mul_eigenbasis_2_0
  · exact row14_generatorB_mul_eigenbasis_2_1
  · exact row14_generatorB_mul_eigenbasis_2_2
  · exact row14_generatorB_mul_eigenbasis_2_3
  · exact row14_generatorB_mul_eigenbasis_2_4
  · exact row14_generatorB_mul_eigenbasis_2_5
  · exact row14_generatorB_mul_eigenbasis_3_0
  · exact row14_generatorB_mul_eigenbasis_3_1
  · exact row14_generatorB_mul_eigenbasis_3_2
  · exact row14_generatorB_mul_eigenbasis_3_3
  · exact row14_generatorB_mul_eigenbasis_3_4
  · exact row14_generatorB_mul_eigenbasis_3_5
  · exact row14_generatorB_mul_eigenbasis_4_0
  · exact row14_generatorB_mul_eigenbasis_4_1
  · exact row14_generatorB_mul_eigenbasis_4_2
  · exact row14_generatorB_mul_eigenbasis_4_3
  · exact row14_generatorB_mul_eigenbasis_4_4
  · exact row14_generatorB_mul_eigenbasis_4_5
  · exact row14_generatorB_mul_eigenbasis_5_0
  · exact row14_generatorB_mul_eigenbasis_5_1
  · exact row14_generatorB_mul_eigenbasis_5_2
  · exact row14_generatorB_mul_eigenbasis_5_3
  · exact row14_generatorB_mul_eigenbasis_5_4
  · exact row14_generatorB_mul_eigenbasis_5_5


private theorem row14_transformedGeneratorA_0_0 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        0 0 =
      alternatingSixAmbientRow14TransformedGeneratorA
        0 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((29 / 16) : ℂ) - ((11 / 16) : ℂ) * ζ ^ 3 - ((29 / 16) : ℂ) * ζ ^ 4 - ((23 / 16) : ℂ) * ζ ^ 5 - ((119 / 16) : ℂ) * ζ ^ 6 - ((73 / 8) : ℂ) * ζ ^ 8 - ((113 / 16) : ℂ) * ζ ^ 9 - ((9 / 8) : ℂ) * ζ ^ 10 + ((31 / 4) : ℂ) * ζ ^ 11 - ((13 / 2) : ℂ) * ζ ^ 13 - ((101 / 16) : ℂ) * ζ ^ 14 + ((99 / 16) : ℂ) * ζ ^ 15 + ((187 / 16) : ℂ) * ζ ^ 16 - ((17 / 2) : ℂ) * ζ ^ 17 + ((277 / 16) : ℂ) * ζ ^ 18 + ((25 / 16) : ℂ) * ζ ^ 19 - ((5 / 2) : ℂ) * ζ ^ 20 + ((3 / 16) : ℂ) * ζ ^ 21 + ((119 / 16) : ℂ) * ζ ^ 22 + ((5 / 2) : ℂ) * ζ ^ 23 + ((227 / 16) : ℂ) * ζ ^ 24 + ((183 / 8) : ℂ) * ζ ^ 25 - ((43 / 16) : ℂ) * ζ ^ 26 - ((31 / 4) : ℂ) * ζ ^ 27 - ((25 / 16) : ℂ) * ζ ^ 28 + ((453 / 16) : ℂ) * ζ ^ 29 - ((143 / 16) : ℂ) * ζ ^ 30 - ((357 / 16) : ℂ) * ζ ^ 31 - ((187 / 16) : ℂ) * ζ ^ 32 + ((3 / 16) : ℂ) * ζ ^ 33 - ((69 / 8) : ℂ) * ζ ^ 34 - ((49 / 8) : ℂ) * ζ ^ 35 - ((311 / 16) : ℂ) * ζ ^ 36 - ((275 / 16) : ℂ) * ζ ^ 37 - ((39 / 16) : ℂ) * ζ ^ 38 - ((11 / 16) : ℂ) * ζ ^ 39 - ((19 / 16) : ℂ) * ζ ^ 40 - ((275 / 16) : ℂ) * ζ ^ 41 + ((81 / 8) : ℂ) * ζ ^ 42 + ((107 / 16) : ℂ) * ζ ^ 43 + ((41 / 8) : ℂ) * ζ ^ 44 - ((425 / 16) : ℂ) * ζ ^ 45 + ((81 / 8) : ℂ) * ζ ^ 46 + ((233 / 16) : ℂ) * ζ ^ 47 + ((23 / 16) : ℂ) * ζ ^ 48 + ((39 / 4) : ℂ) * ζ ^ 49 + ((93 / 16) : ℂ) * ζ ^ 50 + ((233 / 16) : ℂ) * ζ ^ 51 + ((31 / 4) : ℂ) * ζ ^ 52 + ((289 / 16) : ℂ) * ζ ^ 53 - ((255 / 16) : ℂ) * ζ ^ 54 + ((21 / 16) : ℂ) * ζ ^ 55 + ((31 / 4) : ℂ) * ζ ^ 56 + ((17 / 2) : ℂ) * ζ ^ 57 + ((9 / 4) : ℂ) * ζ ^ 58 - ((127 / 8) : ℂ) * ζ ^ 59 - ((31 / 4) : ℂ) * ζ ^ 60 - ((17 / 2) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_0_1 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        0 1 =
      alternatingSixAmbientRow14TransformedGeneratorA
        0 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((437 / 44) : ℂ) + ((213 / 11) : ℂ) * ζ ^ 3 - ((437 / 44) : ℂ) * ζ ^ 4 + ((11 / 8) : ℂ) * ζ ^ 5 + ((487 / 44) : ℂ) * ζ ^ 6 + ((763 / 88) : ℂ) * ζ ^ 8 - ((51 / 88) : ℂ) * ζ ^ 9 + ((61 / 11) : ℂ) * ζ ^ 10 + ((5 / 88) : ℂ) * ζ ^ 11 - ((5 / 4) : ℂ) * ζ ^ 13 + ((243 / 44) : ℂ) * ζ ^ 14 - ((355 / 88) : ℂ) * ζ ^ 15 + ((125 / 44) : ℂ) * ζ ^ 16 + ((35 / 44) : ℂ) * ζ ^ 17 - (14 : ℂ) * ζ ^ 18 + ((45 / 11) : ℂ) * ζ ^ 19 - ((845 / 88) : ℂ) * ζ ^ 20 + ((139 / 88) : ℂ) * ζ ^ 21 - ((487 / 44) : ℂ) * ζ ^ 22 - ((1729 / 88) : ℂ) * ζ ^ 23 + ((1095 / 88) : ℂ) * ζ ^ 24 - ((163 / 88) : ℂ) * ζ ^ 25 - ((101 / 11) : ℂ) * ζ ^ 26 - ((5 / 88) : ℂ) * ζ ^ 27 - ((117 / 8) : ℂ) * ζ ^ 28 - ((59 / 44) : ℂ) * ζ ^ 29 + ((413 / 44) : ℂ) * ζ ^ 30 + ((9 / 8) : ℂ) * ζ ^ 31 - ((125 / 44) : ℂ) * ζ ^ 32 - ((243 / 88) : ℂ) * ζ ^ 33 + ((157 / 44) : ℂ) * ζ ^ 34 + ((85 / 22) : ℂ) * ζ ^ 35 - ((41 / 11) : ℂ) * ζ ^ 36 + ((1 / 88) : ℂ) * ζ ^ 37 + ((761 / 44) : ℂ) * ζ ^ 38 - ((21 / 8) : ℂ) * ζ ^ 39 + ((339 / 88) : ℂ) * ζ ^ 40 + ((1 / 88) : ℂ) * ζ ^ 41 - ((83 / 44) : ℂ) * ζ ^ 42 + ((531 / 22) : ℂ) * ζ ^ 43 - ((167 / 88) : ℂ) * ζ ^ 44 - ((57 / 44) : ℂ) * ζ ^ 45 - ((83 / 44) : ℂ) * ζ ^ 46 - ((13 / 11) : ℂ) * ζ ^ 47 + ((1201 / 88) : ℂ) * ζ ^ 48 + ((393 / 88) : ℂ) * ζ ^ 49 + ((24 / 11) : ℂ) * ζ ^ 50 - ((13 / 11) : ℂ) * ζ ^ 51 + ((39 / 44) : ℂ) * ζ ^ 52 - ((15 / 8) : ℂ) * ζ ^ 53 - ((13 / 44) : ℂ) * ζ ^ 54 + ((21 / 8) : ℂ) * ζ ^ 55 + ((39 / 44) : ℂ) * ζ ^ 56 - ((35 / 44) : ℂ) * ζ ^ 57 - ((325 / 88) : ℂ) * ζ ^ 58 - ((127 / 88) : ℂ) * ζ ^ 59 - ((39 / 44) : ℂ) * ζ ^ 60 + ((35 / 44) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_0_2 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        0 2 =
      alternatingSixAmbientRow14TransformedGeneratorA
        0 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((1857 / 176) : ℂ) + ((1913 / 176) : ℂ) * ζ ^ 3 - ((1857 / 176) : ℂ) * ζ ^ 4 + ((1273 / 176) : ℂ) * ζ ^ 5 + ((2821 / 176) : ℂ) * ζ ^ 6 - ((29 / 11) : ℂ) * ζ ^ 8 - ((173 / 176) : ℂ) * ζ ^ 9 + ((875 / 44) : ℂ) * ζ ^ 10 - ((59 / 88) : ℂ) * ζ ^ 11 + ((129 / 44) : ℂ) * ζ ^ 13 - ((679 / 176) : ℂ) * ζ ^ 14 - ((233 / 176) : ℂ) * ζ ^ 15 - ((949 / 176) : ℂ) * ζ ^ 16 + ((25 / 4) : ℂ) * ζ ^ 17 - ((1425 / 176) : ℂ) * ζ ^ 18 + ((115 / 176) : ℂ) * ζ ^ 19 - ((711 / 44) : ℂ) * ζ ^ 20 - ((1049 / 176) : ℂ) * ζ ^ 21 - ((2821 / 176) : ℂ) * ζ ^ 22 + ((527 / 88) : ℂ) * ζ ^ 23 + ((1895 / 176) : ℂ) * ζ ^ 24 - ((2889 / 88) : ℂ) * ζ ^ 25 - ((3545 / 176) : ℂ) * ζ ^ 26 + ((59 / 88) : ℂ) * ζ ^ 27 + ((1549 / 176) : ℂ) * ζ ^ 28 - ((1871 / 176) : ℂ) * ζ ^ 29 - ((2065 / 176) : ℂ) * ζ ^ 30 + ((257 / 176) : ℂ) * ζ ^ 31 + ((949 / 176) : ℂ) * ζ ^ 32 - ((2325 / 176) : ℂ) * ζ ^ 33 + ((2081 / 88) : ℂ) * ζ ^ 34 + ((125 / 88) : ℂ) * ζ ^ 35 + ((921 / 176) : ℂ) * ζ ^ 36 + ((3249 / 176) : ℂ) * ζ ^ 37 + ((969 / 176) : ℂ) * ζ ^ 38 - ((229 / 176) : ℂ) * ζ ^ 39 + ((2259 / 176) : ℂ) * ζ ^ 40 + ((3249 / 176) : ℂ) * ζ ^ 41 + ((181 / 44) : ℂ) * ζ ^ 42 + ((2753 / 176) : ℂ) * ζ ^ 43 - ((809 / 44) : ℂ) * ζ ^ 44 + ((3329 / 176) : ℂ) * ζ ^ 45 + ((181 / 44) : ℂ) * ζ ^ 46 - ((139 / 176) : ℂ) * ζ ^ 47 + ((1193 / 176) : ℂ) * ζ ^ 48 - ((99 / 8) : ℂ) * ζ ^ 49 + ((1201 / 176) : ℂ) * ζ ^ 50 - ((139 / 176) : ℂ) * ζ ^ 51 + ((7 / 44) : ℂ) * ζ ^ 52 - ((2451 / 176) : ℂ) * ζ ^ 53 - ((175 / 16) : ℂ) * ζ ^ 54 + ((111 / 16) : ℂ) * ζ ^ 55 + ((7 / 44) : ℂ) * ζ ^ 56 - ((25 / 4) : ℂ) * ζ ^ 57 - ((59 / 22) : ℂ) * ζ ^ 58 - ((541 / 88) : ℂ) * ζ ^ 59 - ((7 / 44) : ℂ) * ζ ^ 60 + ((25 / 4) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_0_3 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        0 3 =
      alternatingSixAmbientRow14TransformedGeneratorA
        0 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((137 / 24) : ℂ) + ((59 / 24) : ℂ) * ζ ^ 3 - ((137 / 24) : ℂ) * ζ ^ 4 + ((163 / 24) : ℂ) * ζ ^ 5 + ((197 / 24) : ℂ) * ζ ^ 6 - ((169 / 24) : ℂ) * ζ ^ 8 - ((97 / 24) : ℂ) * ζ ^ 9 + ((105 / 8) : ℂ) * ζ ^ 10 - ((5 / 3) : ℂ) * ζ ^ 11 - ((35 / 8) : ℂ) * ζ ^ 13 - ((59 / 12) : ℂ) * ζ ^ 14 + ((5 / 12) : ℂ) * ζ ^ 15 - (12 : ℂ) * ζ ^ 16 + ((11 / 4) : ℂ) * ζ ^ 17 - ((19 / 8) : ℂ) * ζ ^ 18 - ((25 / 12) : ℂ) * ζ ^ 19 - ((49 / 8) : ℂ) * ζ ^ 20 - ((77 / 6) : ℂ) * ζ ^ 21 - ((197 / 24) : ℂ) * ζ ^ 22 + ((367 / 12) : ℂ) * ζ ^ 23 - ((47 / 8) : ℂ) * ζ ^ 24 - ((125 / 6) : ℂ) * ζ ^ 25 - ((275 / 24) : ℂ) * ζ ^ 26 + ((5 / 3) : ℂ) * ζ ^ 27 + ((361 / 12) : ℂ) * ζ ^ 28 - ((17 / 2) : ℂ) * ζ ^ 29 - (10 : ℂ) * ζ ^ 30 - ((13 / 8) : ℂ) * ζ ^ 31 + (12 : ℂ) * ζ ^ 32 + ((149 / 24) : ℂ) * ζ ^ 33 + ((359 / 24) : ℂ) * ζ ^ 34 - ((35 / 8) : ℂ) * ζ ^ 35 + ((147 / 8) : ℂ) * ζ ^ 36 + ((55 / 3) : ℂ) * ζ ^ 37 - ((99 / 8) : ℂ) * ζ ^ 38 - ((7 / 12) : ℂ) * ζ ^ 39 + ((5 / 3) : ℂ) * ζ ^ 40 + ((55 / 3) : ℂ) * ζ ^ 41 + ((13 / 4) : ℂ) * ζ ^ 42 - ((71 / 4) : ℂ) * ζ ^ 43 - ((175 / 24) : ℂ) * ζ ^ 44 + ((43 / 12) : ℂ) * ζ ^ 45 + ((13 / 4) : ℂ) * ζ ^ 46 + ((79 / 24) : ℂ) * ζ ^ 47 - ((97 / 8) : ℂ) * ζ ^ 48 - ((131 / 12) : ℂ) * ζ ^ 49 + ((49 / 6) : ℂ) * ζ ^ 50 + ((79 / 24) : ℂ) * ζ ^ 51 - ((51 / 8) : ℂ) * ζ ^ 52 - ((73 / 8) : ℂ) * ζ ^ 53 - ((137 / 12) : ℂ) * ζ ^ 54 + ((11 / 8) : ℂ) * ζ ^ 55 - ((51 / 8) : ℂ) * ζ ^ 56 - ((11 / 4) : ℂ) * ζ ^ 57 + ((5 / 8) : ℂ) * ζ ^ 58 - ((14 / 3) : ℂ) * ζ ^ 59 + ((51 / 8) : ℂ) * ζ ^ 60 + ((11 / 4) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_0_4 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        0 4 =
      alternatingSixAmbientRow14TransformedGeneratorA
        0 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((27 / 16) : ℂ) + ((175 / 16) : ℂ) * ζ ^ 3 + ((27 / 16) : ℂ) * ζ ^ 4 + ((39 / 16) : ℂ) * ζ ^ 5 + ((35 / 16) : ℂ) * ζ ^ 6 + ((169 / 8) : ℂ) * ζ ^ 8 - ((1 / 16) : ℂ) * ζ ^ 9 - (3 : ℂ) * ζ ^ 10 - ((3 / 4) : ℂ) * ζ ^ 11 + ((55 / 4) : ℂ) * ζ ^ 13 + ((83 / 16) : ℂ) * ζ ^ 14 - ((151 / 16) : ℂ) * ζ ^ 15 + ((35 / 16) : ℂ) * ζ ^ 16 + ((19 / 8) : ℂ) * ζ ^ 17 - ((317 / 16) : ℂ) * ζ ^ 18 + ((139 / 16) : ℂ) * ζ ^ 19 - ((35 / 8) : ℂ) * ζ ^ 20 + ((69 / 16) : ℂ) * ζ ^ 21 - ((35 / 16) : ℂ) * ζ ^ 22 - ((187 / 4) : ℂ) * ζ ^ 23 + ((105 / 16) : ℂ) * ζ ^ 24 - ((37 / 8) : ℂ) * ζ ^ 25 - ((27 / 16) : ℂ) * ζ ^ 26 + ((3 / 4) : ℂ) * ζ ^ 27 - ((465 / 16) : ℂ) * ζ ^ 28 - ((85 / 16) : ℂ) * ζ ^ 29 + ((159 / 16) : ℂ) * ζ ^ 30 + ((99 / 16) : ℂ) * ζ ^ 31 - ((35 / 16) : ℂ) * ζ ^ 32 + ((169 / 16) : ℂ) * ζ ^ 33 - ((29 / 4) : ℂ) * ζ ^ 34 + ((105 / 8) : ℂ) * ζ ^ 35 - ((41 / 16) : ℂ) * ζ ^ 36 + ((7 / 16) : ℂ) * ζ ^ 37 + ((521 / 16) : ℂ) * ζ ^ 38 - ((135 / 16) : ℂ) * ζ ^ 39 + ((65 / 16) : ℂ) * ζ ^ 40 + ((7 / 16) : ℂ) * ζ ^ 41 - ((1 / 2) : ℂ) * ζ ^ 42 + ((325 / 16) : ℂ) * ζ ^ 43 - ((9 / 4) : ℂ) * ζ ^ 44 + ((201 / 16) : ℂ) * ζ ^ 45 - ((1 / 2) : ℂ) * ζ ^ 46 - ((87 / 16) : ℂ) * ζ ^ 47 + ((165 / 16) : ℂ) * ζ ^ 48 - ((7 / 2) : ℂ) * ζ ^ 49 - ((117 / 16) : ℂ) * ζ ^ 50 - ((87 / 16) : ℂ) * ζ ^ 51 + ((3 / 8) : ℂ) * ζ ^ 52 - ((21 / 16) : ℂ) * ζ ^ 53 + ((125 / 16) : ℂ) * ζ ^ 54 - ((75 / 16) : ℂ) * ζ ^ 55 + ((3 / 8) : ℂ) * ζ ^ 56 - ((19 / 8) : ℂ) * ζ ^ 57 - ((13 / 4) : ℂ) * ζ ^ 58 + ((81 / 8) : ℂ) * ζ ^ 59 - ((3 / 8) : ℂ) * ζ ^ 60 + ((19 / 8) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_0_5 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        0 5 =
      alternatingSixAmbientRow14TransformedGeneratorA
        0 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((187 / 16) : ℂ) + ((87 / 16) : ℂ) * ζ ^ 3 - ((187 / 16) : ℂ) * ζ ^ 4 + ((167 / 16) : ℂ) * ζ ^ 5 + ((91 / 16) : ℂ) * ζ ^ 6 - ((13 / 8) : ℂ) * ζ ^ 8 - ((151 / 16) : ℂ) * ζ ^ 9 + ((147 / 8) : ℂ) * ζ ^ 10 - ((1 / 8) : ℂ) * ζ ^ 11 + ((113 / 8) : ℂ) * ζ ^ 13 - ((203 / 16) : ℂ) * ζ ^ 14 - ((37 / 16) : ℂ) * ζ ^ 15 + ((83 / 16) : ℂ) * ζ ^ 16 + ζ ^ 17 + ((245 / 16) : ℂ) * ζ ^ 18 + ((35 / 16) : ℂ) * ζ ^ 19 - ((167 / 8) : ℂ) * ζ ^ 20 + ((15 / 16) : ℂ) * ζ ^ 21 - ((91 / 16) : ℂ) * ζ ^ 22 + ((69 / 8) : ℂ) * ζ ^ 23 + ((417 / 16) : ℂ) * ζ ^ 24 - ((121 / 8) : ℂ) * ζ ^ 25 - ((39 / 16) : ℂ) * ζ ^ 26 + ((1 / 8) : ℂ) * ζ ^ 27 - ((267 / 16) : ℂ) * ζ ^ 28 + ((161 / 16) : ℂ) * ζ ^ 29 - ((45 / 16) : ℂ) * ζ ^ 30 + ((17 / 16) : ℂ) * ζ ^ 31 - ((83 / 16) : ℂ) * ζ ^ 32 - ((637 / 16) : ℂ) * ζ ^ 33 + ((47 / 4) : ℂ) * ζ ^ 34 + ((13 / 2) : ℂ) * ζ ^ 35 - ((137 / 16) : ℂ) * ζ ^ 36 + ((17 / 16) : ℂ) * ζ ^ 37 - ((187 / 16) : ℂ) * ζ ^ 38 - ((91 / 16) : ℂ) * ζ ^ 39 + ((265 / 16) : ℂ) * ζ ^ 40 + ((17 / 16) : ℂ) * ζ ^ 41 - ((13 / 4) : ℂ) * ζ ^ 42 + ((373 / 16) : ℂ) * ζ ^ 43 - ((59 / 4) : ℂ) * ζ ^ 44 + ((25 / 16) : ℂ) * ζ ^ 45 - ((13 / 4) : ℂ) * ζ ^ 46 - ((15 / 16) : ℂ) * ζ ^ 47 + ((465 / 16) : ℂ) * ζ ^ 48 + ((11 / 8) : ℂ) * ζ ^ 49 + ((75 / 16) : ℂ) * ζ ^ 50 - ((15 / 16) : ℂ) * ζ ^ 51 + ((27 / 8) : ℂ) * ζ ^ 52 + ((159 / 16) : ℂ) * ζ ^ 53 - ((23 / 16) : ℂ) * ζ ^ 54 + ((85 / 16) : ℂ) * ζ ^ 55 + ((27 / 8) : ℂ) * ζ ^ 56 - ζ ^ 57 + ((11 / 8) : ℂ) * ζ ^ 58 - ((35 / 8) : ℂ) * ζ ^ 59 - ((27 / 8) : ℂ) * ζ ^ 60 + ζ ^ 61)
private theorem row14_transformedGeneratorA_1_0 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        1 0 =
      alternatingSixAmbientRow14TransformedGeneratorA
        1 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((111 / 16) : ℂ) + ((7 / 4) : ℂ) * ζ ^ 3 - ((111 / 16) : ℂ) * ζ ^ 4 + ((203 / 16) : ℂ) * ζ ^ 5 + (10 : ℂ) * ζ ^ 6 - ((135 / 16) : ℂ) * ζ ^ 8 - (22 : ℂ) * ζ ^ 9 + ((107 / 16) : ℂ) * ζ ^ 10 + ((109 / 16) : ℂ) * ζ ^ 11 - ((95 / 8) : ℂ) * ζ ^ 13 + ((53 / 16) : ℂ) * ζ ^ 14 - ((199 / 8) : ℂ) * ζ ^ 15 + ((173 / 16) : ℂ) * ζ ^ 16 - ((149 / 16) : ℂ) * ζ ^ 17 + ((7 / 16) : ℂ) * ζ ^ 18 + ((507 / 16) : ℂ) * ζ ^ 19 - ((219 / 16) : ℂ) * ζ ^ 20 + ((9 / 2) : ℂ) * ζ ^ 21 - (10 : ℂ) * ζ ^ 22 + ((7 / 16) : ℂ) * ζ ^ 23 + ((49 / 2) : ℂ) * ζ ^ 24 + ((109 / 4) : ℂ) * ζ ^ 25 - ((599 / 16) : ℂ) * ζ ^ 26 - ((109 / 16) : ℂ) * ζ ^ 27 + ((7 / 16) : ℂ) * ζ ^ 28 + ((265 / 8) : ℂ) * ζ ^ 29 - ((35 / 4) : ℂ) * ζ ^ 30 - ((491 / 16) : ℂ) * ζ ^ 31 - ((173 / 16) : ℂ) * ζ ^ 32 + ((13 / 16) : ℂ) * ζ ^ 33 - ((139 / 16) : ℂ) * ζ ^ 34 + ((33 / 16) : ℂ) * ζ ^ 35 - ((125 / 8) : ℂ) * ζ ^ 36 - ((185 / 8) : ℂ) * ζ ^ 37 + (11 : ℂ) * ζ ^ 38 - ((153 / 8) : ℂ) * ζ ^ 39 + ((117 / 16) : ℂ) * ζ ^ 40 - ((185 / 8) : ℂ) * ζ ^ 41 + ((439 / 16) : ℂ) * ζ ^ 42 + ((189 / 16) : ℂ) * ζ ^ 43 - ((21 / 16) : ℂ) * ζ ^ 44 - ((59 / 16) : ℂ) * ζ ^ 45 + ((439 / 16) : ℂ) * ζ ^ 46 + ((191 / 8) : ℂ) * ζ ^ 47 + ((69 / 8) : ℂ) * ζ ^ 48 - ((167 / 16) : ℂ) * ζ ^ 49 - ((227 / 16) : ℂ) * ζ ^ 50 + ((191 / 8) : ℂ) * ζ ^ 51 + ((77 / 16) : ℂ) * ζ ^ 52 + ((371 / 16) : ℂ) * ζ ^ 53 - ((53 / 4) : ℂ) * ζ ^ 54 - ((507 / 16) : ℂ) * ζ ^ 55 + ((77 / 16) : ℂ) * ζ ^ 56 + ((149 / 16) : ℂ) * ζ ^ 57 - ((9 / 4) : ℂ) * ζ ^ 58 + ((125 / 16) : ℂ) * ζ ^ 59 - ((77 / 16) : ℂ) * ζ ^ 60 - ((149 / 16) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_1_1 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        1 1 =
      alternatingSixAmbientRow14TransformedGeneratorA
        1 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((93 / 22) : ℂ) + ((433 / 44) : ℂ) * ζ ^ 3 + ((93 / 22) : ℂ) * ζ ^ 4 - ((417 / 88) : ℂ) * ζ ^ 5 + ((181 / 11) : ℂ) * ζ ^ 6 - ((683 / 88) : ℂ) * ζ ^ 8 + ((771 / 88) : ℂ) * ζ ^ 9 + ((69 / 4) : ℂ) * ζ ^ 10 + ((223 / 88) : ℂ) * ζ ^ 11 - ((575 / 88) : ℂ) * ζ ^ 13 - ((35 / 44) : ℂ) * ζ ^ 14 - ((525 / 88) : ℂ) * ζ ^ 15 + ((615 / 88) : ℂ) * ζ ^ 16 + ((177 / 44) : ℂ) * ζ ^ 17 - ((63 / 2) : ℂ) * ζ ^ 18 + ((17 / 2) : ℂ) * ζ ^ 19 - ((281 / 88) : ℂ) * ζ ^ 20 - ((79 / 88) : ℂ) * ζ ^ 21 - ((181 / 11) : ℂ) * ζ ^ 22 - ((1805 / 88) : ℂ) * ζ ^ 23 + ((112 / 11) : ℂ) * ζ ^ 24 - ((1091 / 88) : ℂ) * ζ ^ 25 - ((90 / 11) : ℂ) * ζ ^ 26 - ((223 / 88) : ℂ) * ζ ^ 27 + ((265 / 88) : ℂ) * ζ ^ 28 - ((139 / 11) : ℂ) * ζ ^ 29 + ((13 / 22) : ℂ) * ζ ^ 30 + ((23 / 44) : ℂ) * ζ ^ 31 - ((615 / 88) : ℂ) * ζ ^ 32 + ((1197 / 88) : ℂ) * ζ ^ 33 + ((531 / 22) : ℂ) * ζ ^ 34 - ((17 / 2) : ℂ) * ζ ^ 35 - ((57 / 4) : ℂ) * ζ ^ 36 + ((787 / 88) : ℂ) * ζ ^ 37 + ((2287 / 88) : ℂ) * ζ ^ 38 + ((155 / 11) : ℂ) * ζ ^ 39 - ((257 / 44) : ℂ) * ζ ^ 40 + ((787 / 88) : ℂ) * ζ ^ 41 - ((91 / 11) : ℂ) * ζ ^ 42 + ((677 / 44) : ℂ) * ζ ^ 43 + ((245 / 44) : ℂ) * ζ ^ 44 + ((813 / 44) : ℂ) * ζ ^ 45 - ((91 / 11) : ℂ) * ζ ^ 46 - ((269 / 88) : ℂ) * ζ ^ 47 + ((269 / 88) : ℂ) * ζ ^ 48 - ((997 / 88) : ℂ) * ζ ^ 49 + ((1137 / 88) : ℂ) * ζ ^ 50 - ((269 / 88) : ℂ) * ζ ^ 51 + ((639 / 88) : ℂ) * ζ ^ 52 - ((711 / 44) : ℂ) * ζ ^ 53 - ((409 / 88) : ℂ) * ζ ^ 54 - ((3 / 44) : ℂ) * ζ ^ 55 + ((639 / 88) : ℂ) * ζ ^ 56 - ((177 / 44) : ℂ) * ζ ^ 57 - ((523 / 88) : ℂ) * ζ ^ 58 + ((25 / 8) : ℂ) * ζ ^ 59 - ((639 / 88) : ℂ) * ζ ^ 60 + ((177 / 44) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_1_2 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        1 2 =
      alternatingSixAmbientRow14TransformedGeneratorA
        1 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((1043 / 176) : ℂ) + ((965 / 88) : ℂ) * ζ ^ 3 - ((1043 / 176) : ℂ) * ζ ^ 4 + ((435 / 176) : ℂ) * ζ ^ 5 + ((333 / 88) : ℂ) * ζ ^ 6 - ((1157 / 176) : ℂ) * ζ ^ 8 + ((667 / 88) : ℂ) * ζ ^ 9 + ((1005 / 176) : ℂ) * ζ ^ 10 - ((1841 / 176) : ℂ) * ζ ^ 11 + ((1509 / 88) : ℂ) * ζ ^ 13 - ((339 / 176) : ℂ) * ζ ^ 14 - ((761 / 44) : ℂ) * ζ ^ 15 - ((183 / 176) : ℂ) * ζ ^ 16 + ((1769 / 176) : ℂ) * ζ ^ 17 + ((595 / 176) : ℂ) * ζ ^ 18 + ((1203 / 176) : ℂ) * ζ ^ 19 - ((4321 / 176) : ℂ) * ζ ^ 20 - ((127 / 8) : ℂ) * ζ ^ 21 - ((333 / 88) : ℂ) * ζ ^ 22 + ((885 / 176) : ℂ) * ζ ^ 23 + ((2069 / 88) : ℂ) * ζ ^ 24 - ((1255 / 22) : ℂ) * ζ ^ 25 + ((91 / 16) : ℂ) * ζ ^ 26 + ((1841 / 176) : ℂ) * ζ ^ 27 + ((183 / 176) : ℂ) * ζ ^ 28 - ((421 / 22) : ℂ) * ζ ^ 29 + ((47 / 8) : ℂ) * ζ ^ 30 + ((3161 / 176) : ℂ) * ζ ^ 31 + ((183 / 176) : ℂ) * ζ ^ 32 - ((131 / 176) : ℂ) * ζ ^ 33 + ((1299 / 176) : ℂ) * ζ ^ 34 + ((269 / 16) : ℂ) * ζ ^ 35 - ((403 / 22) : ℂ) * ζ ^ 36 + ((1583 / 44) : ℂ) * ζ ^ 37 + ((1305 / 88) : ℂ) * ζ ^ 38 - ((435 / 22) : ℂ) * ζ ^ 39 - ((31 / 176) : ℂ) * ζ ^ 40 + ((1583 / 44) : ℂ) * ζ ^ 41 - ((1667 / 176) : ℂ) * ζ ^ 42 + ((1413 / 176) : ℂ) * ζ ^ 43 - ((3559 / 176) : ℂ) * ζ ^ 44 + ((5829 / 176) : ℂ) * ζ ^ 45 - ((1667 / 176) : ℂ) * ζ ^ 46 - ((15 / 2) : ℂ) * ζ ^ 47 + ((104 / 11) : ℂ) * ζ ^ 48 - ((5085 / 176) : ℂ) * ζ ^ 49 + ((3117 / 176) : ℂ) * ζ ^ 50 - ((15 / 2) : ℂ) * ζ ^ 51 + ((3407 / 176) : ℂ) * ζ ^ 52 - ((3901 / 176) : ℂ) * ζ ^ 53 - ((725 / 88) : ℂ) * ζ ^ 54 - ((995 / 176) : ℂ) * ζ ^ 55 + ((3407 / 176) : ℂ) * ζ ^ 56 - ((1769 / 176) : ℂ) * ζ ^ 57 - ((63 / 22) : ℂ) * ζ ^ 58 + ((2315 / 176) : ℂ) * ζ ^ 59 - ((3407 / 176) : ℂ) * ζ ^ 60 + ((1769 / 176) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_1_3 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        1 3 =
      alternatingSixAmbientRow14TransformedGeneratorA
        1 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((5 / 4) : ℂ) + ((11 / 6) : ℂ) * ζ ^ 3 - ((5 / 4) : ℂ) * ζ ^ 4 - ((89 / 24) : ℂ) * ζ ^ 5 - ((13 / 3) : ℂ) * ζ ^ 6 - ((13 / 24) : ℂ) * ζ ^ 8 + ((217 / 24) : ℂ) * ζ ^ 9 + ((11 / 4) : ℂ) * ζ ^ 10 - ((431 / 24) : ℂ) * ζ ^ 11 + ((901 / 24) : ℂ) * ζ ^ 13 - ((85 / 12) : ℂ) * ζ ^ 14 - ((251 / 24) : ℂ) * ζ ^ 15 - ((105 / 8) : ℂ) * ζ ^ 16 + ((16 / 3) : ℂ) * ζ ^ 17 + ((134 / 3) : ℂ) * ζ ^ 18 - ((15 / 2) : ℂ) * ζ ^ 19 - ((37 / 8) : ℂ) * ζ ^ 20 - ((207 / 8) : ℂ) * ζ ^ 21 + ((13 / 3) : ℂ) * ζ ^ 22 + ((1163 / 24) : ℂ) * ζ ^ 23 - ((17 / 2) : ℂ) * ζ ^ 24 - ((249 / 8) : ℂ) * ζ ^ 25 + ((11 / 2) : ℂ) * ζ ^ 26 + ((431 / 24) : ℂ) * ζ ^ 27 + ((319 / 24) : ℂ) * ζ ^ 28 - ((107 / 4) : ℂ) * ζ ^ 29 + ((41 / 4) : ℂ) * ζ ^ 30 + ((83 / 6) : ℂ) * ζ ^ 31 + ((105 / 8) : ℂ) * ζ ^ 32 - ((125 / 8) : ℂ) * ζ ^ 33 - ((161 / 12) : ℂ) * ζ ^ 34 + ((25 / 6) : ℂ) * ζ ^ 35 + ((35 / 4) : ℂ) * ζ ^ 36 + ((877 / 24) : ℂ) * ζ ^ 37 - ((757 / 24) : ℂ) * ζ ^ 38 - ((105 / 4) : ℂ) * ζ ^ 39 - ((53 / 12) : ℂ) * ζ ^ 40 + ((877 / 24) : ℂ) * ζ ^ 41 - ((7 / 6) : ℂ) * ζ ^ 42 - ((137 / 12) : ℂ) * ζ ^ 43 - ((157 / 12) : ℂ) * ζ ^ 44 + ((131 / 12) : ℂ) * ζ ^ 45 - ((7 / 6) : ℂ) * ζ ^ 46 + ((33 / 8) : ℂ) * ζ ^ 47 + ((39 / 8) : ℂ) * ζ ^ 48 - ((209 / 8) : ℂ) * ζ ^ 49 + ((67 / 24) : ℂ) * ζ ^ 50 + ((33 / 8) : ℂ) * ζ ^ 51 + ((35 / 8) : ℂ) * ζ ^ 52 - ((73 / 12) : ℂ) * ζ ^ 53 - ((13 / 8) : ℂ) * ζ ^ 54 - ((19 / 4) : ℂ) * ζ ^ 55 + ((35 / 8) : ℂ) * ζ ^ 56 - ((16 / 3) : ℂ) * ζ ^ 57 + ((145 / 24) : ℂ) * ζ ^ 58 + ((5 / 8) : ℂ) * ζ ^ 59 - ((35 / 8) : ℂ) * ζ ^ 60 + ((16 / 3) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_1_4 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        1 4 =
      alternatingSixAmbientRow14TransformedGeneratorA
        1 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((31 / 16) : ℂ) + ((41 / 8) : ℂ) * ζ ^ 3 + ((31 / 16) : ℂ) * ζ ^ 4 - ((19 / 16) : ℂ) * ζ ^ 5 + ((121 / 8) : ℂ) * ζ ^ 6 + ((57 / 16) : ℂ) * ζ ^ 8 + ((47 / 8) : ℂ) * ζ ^ 9 + ((27 / 16) : ℂ) * ζ ^ 10 + ((185 / 16) : ℂ) * ζ ^ 11 - ((171 / 8) : ℂ) * ζ ^ 13 + ((215 / 16) : ℂ) * ζ ^ 14 + ((23 / 8) : ℂ) * ζ ^ 15 + ((15 / 16) : ℂ) * ζ ^ 16 + ((75 / 16) : ℂ) * ζ ^ 17 - ((1129 / 16) : ℂ) * ζ ^ 18 + ((139 / 16) : ℂ) * ζ ^ 19 - ((83 / 16) : ℂ) * ζ ^ 20 + ((17 / 4) : ℂ) * ζ ^ 21 - ((121 / 8) : ℂ) * ζ ^ 22 - ((791 / 16) : ℂ) * ζ ^ 23 + ((49 / 8) : ℂ) * ζ ^ 24 - (11 : ℂ) * ζ ^ 25 - ((75 / 16) : ℂ) * ζ ^ 26 - ((185 / 16) : ℂ) * ζ ^ 27 + ((227 / 16) : ℂ) * ζ ^ 28 - ((103 / 8) : ℂ) * ζ ^ 29 + ((55 / 8) : ℂ) * ζ ^ 30 - ((13 / 16) : ℂ) * ζ ^ 31 - ((15 / 16) : ℂ) * ζ ^ 32 + ((509 / 16) : ℂ) * ζ ^ 33 + ((299 / 16) : ℂ) * ζ ^ 34 + ((59 / 16) : ℂ) * ζ ^ 35 - ((3 / 4) : ℂ) * ζ ^ 36 + ((41 / 8) : ℂ) * ζ ^ 37 + ((135 / 4) : ℂ) * ζ ^ 38 + ((149 / 8) : ℂ) * ζ ^ 39 + ((89 / 16) : ℂ) * ζ ^ 40 + ((41 / 8) : ℂ) * ζ ^ 41 - ((167 / 16) : ℂ) * ζ ^ 42 + ((171 / 16) : ℂ) * ζ ^ 43 - ((71 / 16) : ℂ) * ζ ^ 44 + ((147 / 16) : ℂ) * ζ ^ 45 - ((167 / 16) : ℂ) * ζ ^ 46 - ((43 / 4) : ℂ) * ζ ^ 47 - ((31 / 8) : ℂ) * ζ ^ 48 + ((71 / 16) : ℂ) * ζ ^ 49 - ((7 / 16) : ℂ) * ζ ^ 50 - ((43 / 4) : ℂ) * ζ ^ 51 - ((3 / 16) : ℂ) * ζ ^ 52 - ((315 / 16) : ℂ) * ζ ^ 53 + ((87 / 8) : ℂ) * ζ ^ 54 + ((143 / 16) : ℂ) * ζ ^ 55 - ((3 / 16) : ℂ) * ζ ^ 56 - ((75 / 16) : ℂ) * ζ ^ 57 - ((31 / 4) : ℂ) * ζ ^ 58 + ((29 / 16) : ℂ) * ζ ^ 59 + ((3 / 16) : ℂ) * ζ ^ 60 + ((75 / 16) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_1_5 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        1 5 =
      alternatingSixAmbientRow14TransformedGeneratorA
        1 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((175 / 16) : ℂ) + ((161 / 8) : ℂ) * ζ ^ 3 - ((175 / 16) : ℂ) * ζ ^ 4 + ((133 / 16) : ℂ) * ζ ^ 5 + ((39 / 8) : ℂ) * ζ ^ 6 + ((117 / 16) : ℂ) * ζ ^ 8 - ((21 / 4) : ℂ) * ζ ^ 9 + ((25 / 16) : ℂ) * ζ ^ 10 - ((95 / 16) : ℂ) * ζ ^ 11 + ((25 / 2) : ℂ) * ζ ^ 13 + ((53 / 16) : ℂ) * ζ ^ 14 - ((205 / 8) : ℂ) * ζ ^ 15 + ((135 / 16) : ℂ) * ζ ^ 16 + ((49 / 16) : ℂ) * ζ ^ 17 + ((79 / 16) : ℂ) * ζ ^ 18 + ((315 / 16) : ℂ) * ζ ^ 19 - ((261 / 16) : ℂ) * ζ ^ 20 + ((3 / 2) : ℂ) * ζ ^ 21 - ((39 / 8) : ℂ) * ζ ^ 22 - ((387 / 16) : ℂ) * ζ ^ 23 + ((99 / 4) : ℂ) * ζ ^ 24 - ((25 / 2) : ℂ) * ζ ^ 25 + ((23 / 16) : ℂ) * ζ ^ 26 + ((95 / 16) : ℂ) * ζ ^ 27 - ((619 / 16) : ℂ) * ζ ^ 28 - ((35 / 8) : ℂ) * ζ ^ 29 + ((33 / 2) : ℂ) * ζ ^ 30 + ((137 / 16) : ℂ) * ζ ^ 31 - ((135 / 16) : ℂ) * ζ ^ 32 - ((71 / 16) : ℂ) * ζ ^ 33 - ((85 / 16) : ℂ) * ζ ^ 34 + ((193 / 16) : ℂ) * ζ ^ 35 - ((77 / 4) : ℂ) * ζ ^ 36 + ((37 / 8) : ℂ) * ζ ^ 37 + (29 : ℂ) * ζ ^ 38 - ((123 / 8) : ℂ) * ζ ^ 39 - ((131 / 16) : ℂ) * ζ ^ 40 + ((37 / 8) : ℂ) * ζ ^ 41 - ((101 / 16) : ℂ) * ζ ^ 42 + ((467 / 16) : ℂ) * ζ ^ 43 + ((93 / 16) : ℂ) * ζ ^ 44 - ((1 / 16) : ℂ) * ζ ^ 45 - ((101 / 16) : ℂ) * ζ ^ 46 - ((21 / 8) : ℂ) * ζ ^ 47 + ((35 / 2) : ℂ) * ζ ^ 48 + ((123 / 16) : ℂ) * ζ ^ 49 - ((15 / 16) : ℂ) * ζ ^ 50 - ((21 / 8) : ℂ) * ζ ^ 51 + ((173 / 16) : ℂ) * ζ ^ 52 - ((225 / 16) : ℂ) * ζ ^ 53 + ((29 / 4) : ℂ) * ζ ^ 54 - ((143 / 16) : ℂ) * ζ ^ 55 + ((173 / 16) : ℂ) * ζ ^ 56 - ((49 / 16) : ℂ) * ζ ^ 57 - ((83 / 8) : ℂ) * ζ ^ 58 + ((185 / 16) : ℂ) * ζ ^ 59 - ((173 / 16) : ℂ) * ζ ^ 60 + ((49 / 16) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_2_0 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        2 0 =
      alternatingSixAmbientRow14TransformedGeneratorA
        2 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((39 / 16) : ℂ) + ((15 / 16) : ℂ) * ζ ^ 3 - ((39 / 16) : ℂ) * ζ ^ 4 - ((147 / 16) : ℂ) * ζ ^ 5 + ((11 / 16) : ℂ) * ζ ^ 6 - ((29 / 4) : ℂ) * ζ ^ 8 + ((11 / 16) : ℂ) * ζ ^ 9 - (19 : ℂ) * ζ ^ 10 + ((17 / 8) : ℂ) * ζ ^ 11 - ((165 / 8) : ℂ) * ζ ^ 13 + ((315 / 16) : ℂ) * ζ ^ 14 - ((93 / 16) : ℂ) * ζ ^ 15 + ((13 / 16) : ℂ) * ζ ^ 16 - ((17 / 2) : ℂ) * ζ ^ 17 - ((105 / 16) : ℂ) * ζ ^ 18 + ((127 / 16) : ℂ) * ζ ^ 19 + ((101 / 8) : ℂ) * ζ ^ 20 - ((151 / 16) : ℂ) * ζ ^ 21 - ((11 / 16) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 23 - ((189 / 16) : ℂ) * ζ ^ 24 + ((131 / 4) : ℂ) * ζ ^ 25 - ((277 / 16) : ℂ) * ζ ^ 26 - ((17 / 8) : ℂ) * ζ ^ 27 + ((93 / 16) : ℂ) * ζ ^ 28 + ((141 / 16) : ℂ) * ζ ^ 29 - ((69 / 16) : ℂ) * ζ ^ 30 - ((145 / 16) : ℂ) * ζ ^ 31 - ((13 / 16) : ℂ) * ζ ^ 32 + ((269 / 16) : ℂ) * ζ ^ 33 - ((93 / 8) : ℂ) * ζ ^ 34 - ((45 / 8) : ℂ) * ζ ^ 35 + ((27 / 16) : ℂ) * ζ ^ 36 - ((121 / 16) : ℂ) * ζ ^ 37 + ((301 / 16) : ℂ) * ζ ^ 38 + ((13 / 16) : ℂ) * ζ ^ 39 - ((127 / 16) : ℂ) * ζ ^ 40 - ((121 / 16) : ℂ) * ζ ^ 41 + ((133 / 8) : ℂ) * ζ ^ 42 + ((153 / 16) : ℂ) * ζ ^ 43 + ((45 / 4) : ℂ) * ζ ^ 44 - ((493 / 16) : ℂ) * ζ ^ 45 + ((133 / 8) : ℂ) * ζ ^ 46 + ((111 / 16) : ℂ) * ζ ^ 47 - ((43 / 16) : ℂ) * ζ ^ 48 + ((35 / 8) : ℂ) * ζ ^ 49 - ((147 / 16) : ℂ) * ζ ^ 50 + ((111 / 16) : ℂ) * ζ ^ 51 - ((5 / 2) : ℂ) * ζ ^ 52 + ((189 / 16) : ℂ) * ζ ^ 53 - ((119 / 16) : ℂ) * ζ ^ 54 - ((69 / 16) : ℂ) * ζ ^ 55 - ((5 / 2) : ℂ) * ζ ^ 56 + ((17 / 2) : ℂ) * ζ ^ 57 - (4 : ℂ) * ζ ^ 58 - ((21 / 8) : ℂ) * ζ ^ 59 + ((5 / 2) : ℂ) * ζ ^ 60 - ((17 / 2) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_2_1 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        2 1 =
      alternatingSixAmbientRow14TransformedGeneratorA
        2 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((25 / 22) : ℂ) + ((27 / 4) : ℂ) * ζ ^ 3 - ((25 / 22) : ℂ) * ζ ^ 4 - ((535 / 88) : ℂ) * ζ ^ 5 + ((527 / 44) : ℂ) * ζ ^ 6 - ((505 / 88) : ℂ) * ζ ^ 8 + ((75 / 8) : ℂ) * ζ ^ 9 - ((54 / 11) : ℂ) * ζ ^ 10 + ((123 / 88) : ℂ) * ζ ^ 11 - ((475 / 44) : ℂ) * ζ ^ 13 + ((743 / 44) : ℂ) * ζ ^ 14 - ((1549 / 88) : ℂ) * ζ ^ 15 + ((225 / 44) : ℂ) * ζ ^ 16 + ((145 / 44) : ℂ) * ζ ^ 17 - ((585 / 22) : ℂ) * ζ ^ 18 + (19 : ℂ) * ζ ^ 19 - ((527 / 88) : ℂ) * ζ ^ 20 + ((321 / 88) : ℂ) * ζ ^ 21 - ((527 / 44) : ℂ) * ζ ^ 22 - ((887 / 88) : ℂ) * ζ ^ 23 + ((977 / 88) : ℂ) * ζ ^ 24 - ((155 / 88) : ℂ) * ζ ^ 25 - ((111 / 22) : ℂ) * ζ ^ 26 - ((123 / 88) : ℂ) * ζ ^ 27 + ((993 / 88) : ℂ) * ζ ^ 28 - ((158 / 11) : ℂ) * ζ ^ 29 + ((687 / 44) : ℂ) * ζ ^ 30 - ((125 / 88) : ℂ) * ζ ^ 31 - ((225 / 44) : ℂ) * ζ ^ 32 + ((1607 / 88) : ℂ) * ζ ^ 33 + ((145 / 44) : ℂ) * ζ ^ 34 + ((513 / 44) : ℂ) * ζ ^ 35 - ((255 / 22) : ℂ) * ζ ^ 36 + ((259 / 88) : ℂ) * ζ ^ 37 + ((555 / 22) : ℂ) * ζ ^ 38 - ((905 / 88) : ℂ) * ζ ^ 39 + ((701 / 88) : ℂ) * ζ ^ 40 + ((259 / 88) : ℂ) * ζ ^ 41 - ((305 / 44) : ℂ) * ζ ^ 42 + ((565 / 44) : ℂ) * ζ ^ 43 - ((821 / 88) : ℂ) * ζ ^ 44 + ((277 / 22) : ℂ) * ζ ^ 45 - ((305 / 44) : ℂ) * ζ ^ 46 + ((1 / 44) : ℂ) * ζ ^ 47 - ((279 / 88) : ℂ) * ζ ^ 48 - ((207 / 88) : ℂ) * ζ ^ 49 + ((83 / 44) : ℂ) * ζ ^ 50 + ((1 / 44) : ℂ) * ζ ^ 51 + ((285 / 44) : ℂ) * ζ ^ 52 - ((1607 / 88) : ℂ) * ζ ^ 53 + ((111 / 22) : ℂ) * ζ ^ 54 - ((411 / 88) : ℂ) * ζ ^ 55 + ((285 / 44) : ℂ) * ζ ^ 56 - ((145 / 44) : ℂ) * ζ ^ 57 - ((481 / 88) : ℂ) * ζ ^ 58 + ((409 / 88) : ℂ) * ζ ^ 59 - ((285 / 44) : ℂ) * ζ ^ 60 + ((145 / 44) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_2_2 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        2 2 =
      alternatingSixAmbientRow14TransformedGeneratorA
        2 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((731 / 176) : ℂ) + ((1295 / 176) : ℂ) * ζ ^ 3 - ((731 / 176) : ℂ) * ζ ^ 4 - ((51 / 176) : ℂ) * ζ ^ 5 + ((1115 / 176) : ℂ) * ζ ^ 6 - ((23 / 88) : ℂ) * ζ ^ 8 + ((983 / 176) : ℂ) * ζ ^ 9 - ((265 / 88) : ℂ) * ζ ^ 10 - ((119 / 11) : ℂ) * ζ ^ 11 + ((1131 / 88) : ℂ) * ζ ^ 13 + ((1645 / 176) : ℂ) * ζ ^ 14 - ((4877 / 176) : ℂ) * ζ ^ 15 - ((351 / 176) : ℂ) * ζ ^ 16 + ((233 / 44) : ℂ) * ζ ^ 17 - ((1171 / 176) : ℂ) * ζ ^ 18 + ((2973 / 176) : ℂ) * ζ ^ 19 - ((1565 / 88) : ℂ) * ζ ^ 20 - ((51 / 176) : ℂ) * ζ ^ 21 - ((1115 / 176) : ℂ) * ζ ^ 22 - ((1 / 88) : ℂ) * ζ ^ 23 + ((2779 / 176) : ℂ) * ζ ^ 24 - ((193 / 22) : ℂ) * ζ ^ 25 + ((281 / 176) : ℂ) * ζ ^ 26 + ((119 / 11) : ℂ) * ζ ^ 27 + ((1867 / 176) : ℂ) * ζ ^ 28 - ((4099 / 176) : ℂ) * ζ ^ 29 + ((4133 / 176) : ℂ) * ζ ^ 30 + ((2205 / 176) : ℂ) * ζ ^ 31 + ((351 / 176) : ℂ) * ζ ^ 32 + ((79 / 16) : ℂ) * ζ ^ 33 - ((811 / 88) : ℂ) * ζ ^ 34 + ((165 / 8) : ℂ) * ζ ^ 35 - ((1577 / 176) : ℂ) * ζ ^ 36 + ((1915 / 176) : ℂ) * ζ ^ 37 + ((3185 / 176) : ℂ) * ζ ^ 38 - ((5233 / 176) : ℂ) * ζ ^ 39 + ((1803 / 176) : ℂ) * ζ ^ 40 + ((1915 / 176) : ℂ) * ζ ^ 41 - ((349 / 44) : ℂ) * ζ ^ 42 + ((1891 / 176) : ℂ) * ζ ^ 43 - ((2041 / 88) : ℂ) * ζ ^ 44 + ((2617 / 176) : ℂ) * ζ ^ 45 - ((349 / 44) : ℂ) * ζ ^ 46 - ((301 / 176) : ℂ) * ζ ^ 47 + ((51 / 176) : ℂ) * ζ ^ 48 - ((201 / 44) : ℂ) * ζ ^ 49 - ((563 / 176) : ℂ) * ζ ^ 50 - ((301 / 176) : ℂ) * ζ ^ 51 + ((241 / 22) : ℂ) * ζ ^ 52 - ((3623 / 176) : ℂ) * ζ ^ 53 + ((1959 / 176) : ℂ) * ζ ^ 54 - ((151 / 16) : ℂ) * ζ ^ 55 + ((241 / 22) : ℂ) * ζ ^ 56 - ((233 / 44) : ℂ) * ζ ^ 57 - ((301 / 44) : ℂ) * ζ ^ 58 + ((981 / 88) : ℂ) * ζ ^ 59 - ((241 / 22) : ℂ) * ζ ^ 60 + ((233 / 44) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_2_3 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        2 3 =
      alternatingSixAmbientRow14TransformedGeneratorA
        2 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((31 / 24) : ℂ) + ((119 / 24) : ℂ) * ζ ^ 3 - ((31 / 24) : ℂ) * ζ ^ 4 + ((85 / 24) : ℂ) * ζ ^ 5 - ((43 / 24) : ℂ) * ζ ^ 6 + ((81 / 8) : ℂ) * ζ ^ 8 - ((13 / 8) : ℂ) * ζ ^ 9 + ((319 / 24) : ℂ) * ζ ^ 10 - ((175 / 12) : ℂ) * ζ ^ 11 + ((971 / 24) : ℂ) * ζ ^ 13 - ((181 / 12) : ℂ) * ζ ^ 14 + ζ ^ 15 - ((47 / 6) : ℂ) * ζ ^ 16 + ((23 / 12) : ℂ) * ζ ^ 17 + ((883 / 24) : ℂ) * ζ ^ 18 - ((187 / 12) : ℂ) * ζ ^ 19 + ((211 / 24) : ℂ) * ζ ^ 20 - ((181 / 12) : ℂ) * ζ ^ 21 + ((43 / 24) : ℂ) * ζ ^ 22 + ((371 / 12) : ℂ) * ζ ^ 23 - ((133 / 8) : ℂ) * ζ ^ 24 - ((16 / 3) : ℂ) * ζ ^ 25 + ((73 / 24) : ℂ) * ζ ^ 26 + ((175 / 12) : ℂ) * ζ ^ 27 - ((17 / 6) : ℂ) * ζ ^ 28 - ((85 / 4) : ℂ) * ζ ^ 29 + ((5 / 3) : ℂ) * ζ ^ 30 + ((257 / 24) : ℂ) * ζ ^ 31 + ((47 / 6) : ℂ) * ζ ^ 32 - ((211 / 8) : ℂ) * ζ ^ 33 - ((53 / 24) : ℂ) * ζ ^ 34 - ((179 / 24) : ℂ) * ζ ^ 35 + ((47 / 8) : ℂ) * ζ ^ 36 + ((227 / 12) : ℂ) * ζ ^ 37 - ((551 / 24) : ℂ) * ζ ^ 38 - (11 : ℂ) * ζ ^ 39 - ((83 / 12) : ℂ) * ζ ^ 40 + ((227 / 12) : ℂ) * ζ ^ 41 - ((5 / 4) : ℂ) * ζ ^ 42 - (11 : ℂ) * ζ ^ 43 - ((23 / 8) : ℂ) * ζ ^ 44 - ((17 / 3) : ℂ) * ζ ^ 45 - ((5 / 4) : ℂ) * ζ ^ 46 + ((31 / 8) : ℂ) * ζ ^ 47 + ((89 / 24) : ℂ) * ζ ^ 48 - ((67 / 12) : ℂ) * ζ ^ 49 - ((5 / 2) : ℂ) * ζ ^ 50 + ((31 / 8) : ℂ) * ζ ^ 51 + ((47 / 24) : ℂ) * ζ ^ 52 - ((37 / 24) : ℂ) * ζ ^ 53 + ((15 / 4) : ℂ) * ζ ^ 54 - ((101 / 24) : ℂ) * ζ ^ 55 + ((47 / 24) : ℂ) * ζ ^ 56 - ((23 / 12) : ℂ) * ζ ^ 57 + ((47 / 24) : ℂ) * ζ ^ 58 + ((1 / 3) : ℂ) * ζ ^ 59 - ((47 / 24) : ℂ) * ζ ^ 60 + ((23 / 12) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_2_4 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        2 4 =
      alternatingSixAmbientRow14TransformedGeneratorA
        2 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((7 / 16) : ℂ) + ((13 / 16) : ℂ) * ζ ^ 3 - ((7 / 16) : ℂ) * ζ ^ 4 - ((93 / 16) : ℂ) * ζ ^ 5 + ((137 / 16) : ℂ) * ζ ^ 6 - (17 : ℂ) * ζ ^ 8 + ((163 / 16) : ℂ) * ζ ^ 9 - ((115 / 8) : ℂ) * ζ ^ 10 + ((57 / 8) : ℂ) * ζ ^ 11 - ((369 / 8) : ℂ) * ζ ^ 13 + ((367 / 16) : ℂ) * ζ ^ 14 - ((159 / 16) : ℂ) * ζ ^ 15 + ((33 / 16) : ℂ) * ζ ^ 16 + ((35 / 8) : ℂ) * ζ ^ 17 - ((787 / 16) : ℂ) * ζ ^ 18 + ((273 / 16) : ℂ) * ζ ^ 19 - ((45 / 4) : ℂ) * ζ ^ 20 + ((191 / 16) : ℂ) * ζ ^ 21 - ((137 / 16) : ℂ) * ζ ^ 22 - (11 : ℂ) * ζ ^ 23 + ((213 / 16) : ℂ) * ζ ^ 24 - ((21 / 4) : ℂ) * ζ ^ 25 - ((1 / 16) : ℂ) * ζ ^ 26 - ((57 / 8) : ℂ) * ζ ^ 27 + ((509 / 16) : ℂ) * ζ ^ 28 - ((145 / 16) : ℂ) * ζ ^ 29 + ((381 / 16) : ℂ) * ζ ^ 30 - ((57 / 16) : ℂ) * ζ ^ 31 - ((33 / 16) : ℂ) * ζ ^ 32 + ((631 / 16) : ℂ) * ζ ^ 33 - ((27 / 4) : ℂ) * ζ ^ 34 + ((145 / 8) : ℂ) * ζ ^ 35 - ((59 / 16) : ℂ) * ζ ^ 36 - ((51 / 16) : ℂ) * ζ ^ 37 + ((393 / 16) : ℂ) * ζ ^ 38 - ((119 / 16) : ℂ) * ζ ^ 39 + ((173 / 16) : ℂ) * ζ ^ 40 - ((51 / 16) : ℂ) * ζ ^ 41 - ((17 / 2) : ℂ) * ζ ^ 42 + ((39 / 16) : ℂ) * ζ ^ 43 - ((83 / 8) : ℂ) * ζ ^ 44 + ((289 / 16) : ℂ) * ζ ^ 45 - ((17 / 2) : ℂ) * ζ ^ 46 - ((57 / 16) : ℂ) * ζ ^ 47 - ((189 / 16) : ℂ) * ζ ^ 48 + ((21 / 8) : ℂ) * ζ ^ 49 - ((33 / 16) : ℂ) * ζ ^ 50 - ((57 / 16) : ℂ) * ζ ^ 51 + ((13 / 8) : ℂ) * ζ ^ 52 - ((297 / 16) : ℂ) * ζ ^ 53 + ((169 / 16) : ℂ) * ζ ^ 54 - ((13 / 16) : ℂ) * ζ ^ 55 + ((13 / 8) : ℂ) * ζ ^ 56 - ((35 / 8) : ℂ) * ζ ^ 57 - ((5 / 2) : ℂ) * ζ ^ 58 + ((35 / 8) : ℂ) * ζ ^ 59 - ((13 / 8) : ℂ) * ζ ^ 60 + ((35 / 8) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_2_5 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        2 5 =
      alternatingSixAmbientRow14TransformedGeneratorA
        2 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((101 / 16) : ℂ) + ((169 / 16) : ℂ) * ζ ^ 3 - ((101 / 16) : ℂ) * ζ ^ 4 + ((11 / 16) : ℂ) * ζ ^ 5 + ((113 / 16) : ℂ) * ζ ^ 6 + ((23 / 2) : ℂ) * ζ ^ 8 + ((13 / 16) : ℂ) * ζ ^ 9 + ((3 / 4) : ℂ) * ζ ^ 10 - ((21 / 4) : ℂ) * ζ ^ 11 + ((39 / 2) : ℂ) * ζ ^ 13 + ((101 / 16) : ℂ) * ζ ^ 14 - ((321 / 16) : ℂ) * ζ ^ 15 + ((49 / 16) : ℂ) * ζ ^ 16 + ((3 / 2) : ℂ) * ζ ^ 17 - ((69 / 16) : ℂ) * ζ ^ 18 + ((237 / 16) : ℂ) * ζ ^ 19 - ((53 / 4) : ℂ) * ζ ^ 20 + ((37 / 16) : ℂ) * ζ ^ 21 - ((113 / 16) : ℂ) * ζ ^ 22 - ((179 / 8) : ℂ) * ζ ^ 23 + ((261 / 16) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 25 - ((53 / 16) : ℂ) * ζ ^ 26 + ((21 / 4) : ℂ) * ζ ^ 27 - ((313 / 16) : ℂ) * ζ ^ 28 - ((111 / 16) : ℂ) * ζ ^ 29 + ((113 / 16) : ℂ) * ζ ^ 30 + ((109 / 16) : ℂ) * ζ ^ 31 - ((49 / 16) : ℂ) * ζ ^ 32 - ((87 / 16) : ℂ) * ζ ^ 33 + ((15 / 4) : ℂ) * ζ ^ 34 + ((7 / 4) : ℂ) * ζ ^ 35 - ((123 / 16) : ℂ) * ζ ^ 36 + ((11 / 16) : ℂ) * ζ ^ 37 + ((361 / 16) : ℂ) * ζ ^ 38 - ((87 / 16) : ℂ) * ζ ^ 39 - ((39 / 16) : ℂ) * ζ ^ 40 + ((11 / 16) : ℂ) * ζ ^ 41 - ((15 / 4) : ℂ) * ζ ^ 42 + ((351 / 16) : ℂ) * ζ ^ 43 + ((7 / 8) : ℂ) * ζ ^ 44 - ((23 / 16) : ℂ) * ζ ^ 45 - ((15 / 4) : ℂ) * ζ ^ 46 - ((25 / 16) : ℂ) * ζ ^ 47 + ((83 / 16) : ℂ) * ζ ^ 48 + ((27 / 4) : ℂ) * ζ ^ 49 + ((7 / 16) : ℂ) * ζ ^ 50 - ((25 / 16) : ℂ) * ζ ^ 51 + ((37 / 8) : ℂ) * ζ ^ 52 - ((129 / 16) : ℂ) * ζ ^ 53 + ((53 / 16) : ℂ) * ζ ^ 54 - ((21 / 16) : ℂ) * ζ ^ 55 + ((37 / 8) : ℂ) * ζ ^ 56 - ((3 / 2) : ℂ) * ζ ^ 57 - ((27 / 8) : ℂ) * ζ ^ 58 + ((23 / 8) : ℂ) * ζ ^ 59 - ((37 / 8) : ℂ) * ζ ^ 60 + ((3 / 2) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_3_0 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        3 0 =
      alternatingSixAmbientRow14TransformedGeneratorA
        3 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((105 / 8) : ℂ) - ((25 / 16) : ℂ) * ζ ^ 3 + ((105 / 8) : ℂ) * ζ ^ 4 - (22 : ℂ) * ζ ^ 5 - ((141 / 16) : ℂ) * ζ ^ 6 - ((17 / 16) : ℂ) * ζ ^ 8 + ((449 / 16) : ℂ) * ζ ^ 9 - ((23 / 8) : ℂ) * ζ ^ 10 - ((115 / 16) : ℂ) * ζ ^ 11 - ((85 / 16) : ℂ) * ζ ^ 13 - ((95 / 16) : ℂ) * ζ ^ 14 + ((545 / 16) : ℂ) * ζ ^ 15 - ((245 / 16) : ℂ) * ζ ^ 16 + ((97 / 16) : ℂ) * ζ ^ 17 - ((75 / 16) : ℂ) * ζ ^ 18 - ((165 / 4) : ℂ) * ζ ^ 19 + ((99 / 8) : ℂ) * ζ ^ 20 - ((79 / 8) : ℂ) * ζ ^ 21 + ((141 / 16) : ℂ) * ζ ^ 22 + ((103 / 16) : ℂ) * ζ ^ 23 - ((443 / 16) : ℂ) * ζ ^ 24 - ((423 / 16) : ℂ) * ζ ^ 25 + ((519 / 16) : ℂ) * ζ ^ 26 + ((115 / 16) : ℂ) * ζ ^ 27 + ((99 / 16) : ℂ) * ζ ^ 28 - ((317 / 16) : ℂ) * ζ ^ 29 + ((51 / 16) : ℂ) * ζ ^ 30 + ((247 / 8) : ℂ) * ζ ^ 31 + ((245 / 16) : ℂ) * ζ ^ 32 + ((43 / 4) : ℂ) * ζ ^ 33 + ((93 / 8) : ℂ) * ζ ^ 34 - ((33 / 16) : ℂ) * ζ ^ 35 + ((169 / 8) : ℂ) * ζ ^ 36 + (22 : ℂ) * ζ ^ 37 - ((25 / 16) : ℂ) * ζ ^ 38 + ((297 / 16) : ℂ) * ζ ^ 39 - ((103 / 8) : ℂ) * ζ ^ 40 + (22 : ℂ) * ζ ^ 41 - ((189 / 8) : ℂ) * ζ ^ 42 - ((53 / 4) : ℂ) * ζ ^ 43 + ((27 / 8) : ℂ) * ζ ^ 44 - ((25 / 8) : ℂ) * ζ ^ 45 - ((189 / 8) : ℂ) * ζ ^ 46 - ((379 / 16) : ℂ) * ζ ^ 47 - ((47 / 4) : ℂ) * ζ ^ 48 + ((43 / 8) : ℂ) * ζ ^ 49 + ((203 / 16) : ℂ) * ζ ^ 50 - ((379 / 16) : ℂ) * ζ ^ 51 - ((93 / 16) : ℂ) * ζ ^ 52 - ((147 / 8) : ℂ) * ζ ^ 53 + ((175 / 16) : ℂ) * ζ ^ 54 + ((51 / 2) : ℂ) * ζ ^ 55 - ((93 / 16) : ℂ) * ζ ^ 56 - ((97 / 16) : ℂ) * ζ ^ 57 + ((5 / 8) : ℂ) * ζ ^ 58 - ((29 / 16) : ℂ) * ζ ^ 59 + ((93 / 16) : ℂ) * ζ ^ 60 + ((97 / 16) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_3_1 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        3 1 =
      alternatingSixAmbientRow14TransformedGeneratorA
        3 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((97 / 44) : ℂ) - ((281 / 22) : ℂ) * ζ ^ 3 + ((97 / 44) : ℂ) * ζ ^ 4 - ((475 / 44) : ℂ) * ζ ^ 5 - ((305 / 22) : ℂ) * ζ ^ 6 - ((487 / 88) : ℂ) * ζ ^ 8 + ((371 / 44) : ℂ) * ζ ^ 9 - ((609 / 22) : ℂ) * ζ ^ 10 - ((265 / 88) : ℂ) * ζ ^ 11 - ((163 / 22) : ℂ) * ζ ^ 13 + ((152 / 11) : ℂ) * ζ ^ 14 + (2 : ℂ) * ζ ^ 15 - ((31 / 8) : ℂ) * ζ ^ 16 - ((26 / 11) : ℂ) * ζ ^ 17 + ((1763 / 88) : ℂ) * ζ ^ 18 - ((441 / 88) : ℂ) * ζ ^ 19 + (10 : ℂ) * ζ ^ 20 + ((265 / 88) : ℂ) * ζ ^ 21 + ((305 / 22) : ℂ) * ζ ^ 22 + ((217 / 8) : ℂ) * ζ ^ 23 - ((111 / 8) : ℂ) * ζ ^ 24 + ((157 / 11) : ℂ) * ζ ^ 25 + ((201 / 22) : ℂ) * ζ ^ 26 + ((265 / 88) : ℂ) * ζ ^ 27 + ((563 / 44) : ℂ) * ζ ^ 28 + ((257 / 88) : ℂ) * ζ ^ 29 + ((25 / 4) : ℂ) * ζ ^ 30 - ((5 / 22) : ℂ) * ζ ^ 31 + ((31 / 8) : ℂ) * ζ ^ 32 - ((117 / 44) : ℂ) * ζ ^ 33 - ((1093 / 44) : ℂ) * ζ ^ 34 + ((101 / 8) : ℂ) * ζ ^ 35 + ((329 / 44) : ℂ) * ζ ^ 36 - ((681 / 88) : ℂ) * ζ ^ 37 - ((1667 / 88) : ℂ) * ζ ^ 38 - ((151 / 8) : ℂ) * ζ ^ 39 + ((73 / 11) : ℂ) * ζ ^ 40 - ((681 / 88) : ℂ) * ζ ^ 41 + ((52 / 11) : ℂ) * ζ ^ 42 - ((1611 / 88) : ℂ) * ζ ^ 43 - ((76 / 11) : ℂ) * ζ ^ 44 - ((511 / 44) : ℂ) * ζ ^ 45 + ((52 / 11) : ℂ) * ζ ^ 46 + ((285 / 88) : ℂ) * ζ ^ 47 - ((969 / 88) : ℂ) * ζ ^ 48 + ((871 / 88) : ℂ) * ζ ^ 49 - ((981 / 88) : ℂ) * ζ ^ 50 + ((285 / 88) : ℂ) * ζ ^ 51 - ((317 / 88) : ℂ) * ζ ^ 52 + (9 : ℂ) * ζ ^ 53 + ((565 / 88) : ℂ) * ζ ^ 54 - ((25 / 11) : ℂ) * ζ ^ 55 - ((317 / 88) : ℂ) * ζ ^ 56 + ((26 / 11) : ℂ) * ζ ^ 57 + ((127 / 22) : ℂ) * ζ ^ 58 - ((85 / 88) : ℂ) * ζ ^ 59 + ((317 / 88) : ℂ) * ζ ^ 60 - ((26 / 11) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_3_2 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        3 2 =
      alternatingSixAmbientRow14TransformedGeneratorA
        3 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((645 / 88) : ℂ) - ((1541 / 176) : ℂ) * ζ ^ 3 + ((645 / 88) : ℂ) * ζ ^ 4 - ((511 / 44) : ℂ) * ζ ^ 5 - ((1377 / 176) : ℂ) * ζ ^ 6 + ((1115 / 176) : ℂ) * ζ ^ 8 + ((45 / 16) : ℂ) * ζ ^ 9 - ((2065 / 88) : ℂ) * ζ ^ 10 + ((663 / 176) : ℂ) * ζ ^ 11 - ((307 / 16) : ℂ) * ζ ^ 13 + ((2753 / 176) : ℂ) * ζ ^ 14 + ((783 / 176) : ℂ) * ζ ^ 15 + ((911 / 176) : ℂ) * ζ ^ 16 - ((1549 / 176) : ℂ) * ζ ^ 17 - ((145 / 16) : ℂ) * ζ ^ 18 - ((15 / 22) : ℂ) * ζ ^ 19 + ((2941 / 88) : ℂ) * ζ ^ 20 + ((210 / 11) : ℂ) * ζ ^ 21 + ((1377 / 176) : ℂ) * ζ ^ 22 + ((47 / 16) : ℂ) * ζ ^ 23 - ((4971 / 176) : ℂ) * ζ ^ 24 + ((11049 / 176) : ℂ) * ζ ^ 25 + ((279 / 176) : ℂ) * ζ ^ 26 - ((663 / 176) : ℂ) * ζ ^ 27 + ((1225 / 176) : ℂ) * ζ ^ 28 + ((1605 / 176) : ℂ) * ζ ^ 29 + ((919 / 176) : ℂ) * ζ ^ 30 - ((425 / 44) : ℂ) * ζ ^ 31 - ((911 / 176) : ℂ) * ζ ^ 32 + ((84 / 11) : ℂ) * ζ ^ 33 - ((1697 / 88) : ℂ) * ζ ^ 34 - ((1035 / 176) : ℂ) * ζ ^ 35 + ((335 / 44) : ℂ) * ζ ^ 36 - ((3229 / 88) : ℂ) * ζ ^ 37 - ((1073 / 176) : ℂ) * ζ ^ 38 + ((661 / 176) : ℂ) * ζ ^ 39 - ((51 / 88) : ℂ) * ζ ^ 40 - ((3229 / 88) : ℂ) * ζ ^ 41 + ((549 / 88) : ℂ) * ζ ^ 42 - ((899 / 88) : ℂ) * ζ ^ 43 + ((204 / 11) : ℂ) * ζ ^ 44 - ((1417 / 44) : ℂ) * ζ ^ 45 + ((549 / 88) : ℂ) * ζ ^ 46 + ((1037 / 176) : ℂ) * ζ ^ 47 - ((29 / 2) : ℂ) * ζ ^ 48 + ((2965 / 88) : ℂ) * ζ ^ 49 - ((3359 / 176) : ℂ) * ζ ^ 50 + ((1037 / 176) : ℂ) * ζ ^ 51 - ((2251 / 176) : ℂ) * ζ ^ 52 + ((123 / 8) : ℂ) * ζ ^ 53 + ((2261 / 176) : ℂ) * ζ ^ 54 + ((9 / 8) : ℂ) * ζ ^ 55 - ((2251 / 176) : ℂ) * ζ ^ 56 + ((1549 / 176) : ℂ) * ζ ^ 57 + ((183 / 88) : ℂ) * ζ ^ 58 - ((1235 / 176) : ℂ) * ζ ^ 59 + ((2251 / 176) : ℂ) * ζ ^ 60 - ((1549 / 176) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_3_3 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        3 3 =
      alternatingSixAmbientRow14TransformedGeneratorA
        3 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((13 / 6) : ℂ) + ((79 / 24) : ℂ) * ζ ^ 3 - ((13 / 6) : ℂ) * ζ ^ 4 + ((125 / 12) : ℂ) * ζ ^ 5 + ((1 / 6) : ℂ) * ζ ^ 6 + ((401 / 24) : ℂ) * ζ ^ 8 - (16 : ℂ) * ζ ^ 9 + ((7 / 4) : ℂ) * ζ ^ 10 + ((245 / 24) : ℂ) * ζ ^ 11 - ((95 / 12) : ℂ) * ζ ^ 13 - ((19 / 12) : ℂ) * ζ ^ 14 + ((281 / 24) : ℂ) * ζ ^ 15 + ((361 / 24) : ℂ) * ζ ^ 16 - ((67 / 12) : ℂ) * ζ ^ 17 - ((205 / 8) : ℂ) * ζ ^ 18 - ((3 / 2) : ℂ) * ζ ^ 19 + ((89 / 6) : ℂ) * ζ ^ 20 + ((527 / 24) : ℂ) * ζ ^ 21 - ((1 / 6) : ℂ) * ζ ^ 22 - ((165 / 4) : ℂ) * ζ ^ 23 + ((5 / 24) : ℂ) * ζ ^ 24 + ((367 / 12) : ℂ) * ζ ^ 25 - ((7 / 12) : ℂ) * ζ ^ 26 - ((245 / 24) : ℂ) * ζ ^ 27 - (29 : ℂ) * ζ ^ 28 + ((199 / 8) : ℂ) * ζ ^ 29 - ((127 / 12) : ℂ) * ζ ^ 30 - ((15 / 2) : ℂ) * ζ ^ 31 - ((361 / 24) : ℂ) * ζ ^ 32 + ((43 / 12) : ℂ) * ζ ^ 33 + ((31 / 3) : ℂ) * ζ ^ 34 - ((17 / 4) : ℂ) * ζ ^ 35 - ((85 / 6) : ℂ) * ζ ^ 36 - ((265 / 8) : ℂ) * ζ ^ 37 + ((611 / 24) : ℂ) * ζ ^ 38 + ((103 / 6) : ℂ) * ζ ^ 39 - ((23 / 12) : ℂ) * ζ ^ 40 - ((265 / 8) : ℂ) * ζ ^ 41 + ((5 / 12) : ℂ) * ζ ^ 42 + ((37 / 3) : ℂ) * ζ ^ 43 + ((107 / 6) : ℂ) * ζ ^ 44 - ((187 / 12) : ℂ) * ζ ^ 45 + ((5 / 12) : ℂ) * ζ ^ 46 - ((65 / 24) : ℂ) * ζ ^ 47 + ((1 / 24) : ℂ) * ζ ^ 48 + ((211 / 8) : ℂ) * ζ ^ 49 - ((47 / 8) : ℂ) * ζ ^ 50 - ((65 / 24) : ℂ) * ζ ^ 51 - ((7 / 8) : ℂ) * ζ ^ 52 + ((15 / 2) : ℂ) * ζ ^ 53 + ((131 / 24) : ℂ) * ζ ^ 54 + ((17 / 8) : ℂ) * ζ ^ 55 - ((7 / 8) : ℂ) * ζ ^ 56 + ((67 / 12) : ℂ) * ζ ^ 57 - ((23 / 4) : ℂ) * ζ ^ 58 + ((7 / 12) : ℂ) * ζ ^ 59 + ((7 / 8) : ℂ) * ζ ^ 60 - ((67 / 12) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_3_4 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        3 4 =
      alternatingSixAmbientRow14TransformedGeneratorA
        3 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((21 / 8) : ℂ) - ((309 / 16) : ℂ) * ζ ^ 3 + ((21 / 8) : ℂ) * ζ ^ 4 - (14 : ℂ) * ζ ^ 5 - ((197 / 16) : ℂ) * ζ ^ 6 - ((599 / 16) : ℂ) * ζ ^ 8 + ((189 / 16) : ℂ) * ζ ^ 9 - ((47 / 4) : ℂ) * ζ ^ 10 - ((149 / 16) : ℂ) * ζ ^ 11 - ((143 / 16) : ℂ) * ζ ^ 13 - ((9 / 16) : ℂ) * ζ ^ 14 - ((99 / 16) : ℂ) * ζ ^ 15 + ((11 / 16) : ℂ) * ζ ^ 16 - ((35 / 16) : ℂ) * ζ ^ 17 + ((1025 / 16) : ℂ) * ζ ^ 18 - ((25 / 8) : ℂ) * ζ ^ 19 + (2 : ℂ) * ζ ^ 20 + ((11 / 8) : ℂ) * ζ ^ 21 + ((197 / 16) : ℂ) * ζ ^ 22 + ((989 / 16) : ℂ) * ζ ^ 23 - ((21 / 16) : ℂ) * ζ ^ 24 + ((299 / 16) : ℂ) * ζ ^ 25 + ((87 / 16) : ℂ) * ζ ^ 26 + ((149 / 16) : ℂ) * ζ ^ 27 + ((229 / 16) : ℂ) * ζ ^ 28 - ((67 / 16) : ℂ) * ζ ^ 29 + ((87 / 16) : ℂ) * ζ ^ 30 - ((11 / 16) : ℂ) * ζ ^ 32 - ((151 / 8) : ℂ) * ζ ^ 33 - ((197 / 8) : ℂ) * ζ ^ 34 - ((37 / 16) : ℂ) * ζ ^ 35 - ((3 / 2) : ℂ) * ζ ^ 36 - ((23 / 4) : ℂ) * ζ ^ 37 - ((561 / 16) : ℂ) * ζ ^ 38 - ((261 / 16) : ℂ) * ζ ^ 39 + ((17 / 8) : ℂ) * ζ ^ 40 - ((23 / 4) : ℂ) * ζ ^ 41 + ((55 / 8) : ℂ) * ζ ^ 42 - ((137 / 8) : ℂ) * ζ ^ 43 - ((9 / 4) : ℂ) * ζ ^ 44 - ((5 / 2) : ℂ) * ζ ^ 45 + ((55 / 8) : ℂ) * ζ ^ 46 + ((149 / 16) : ℂ) * ζ ^ 47 - ((17 / 4) : ℂ) * ζ ^ 48 - ((1 / 2) : ℂ) * ζ ^ 49 - ((9 / 16) : ℂ) * ζ ^ 50 + ((149 / 16) : ℂ) * ζ ^ 51 + ((13 / 16) : ℂ) * ζ ^ 52 + ((95 / 8) : ℂ) * ζ ^ 53 - ((101 / 16) : ℂ) * ζ ^ 54 - (5 : ℂ) * ζ ^ 55 + ((13 / 16) : ℂ) * ζ ^ 56 + ((35 / 16) : ℂ) * ζ ^ 57 + ((65 / 8) : ℂ) * ζ ^ 58 - ((69 / 16) : ℂ) * ζ ^ 59 - ((13 / 16) : ℂ) * ζ ^ 60 - ((35 / 16) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_3_5 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        3 5 =
      alternatingSixAmbientRow14TransformedGeneratorA
        3 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((87 / 8) : ℂ) - ((155 / 16) : ℂ) * ζ ^ 3 + ((87 / 8) : ℂ) * ζ ^ 4 - ((27 / 2) : ℂ) * ζ ^ 5 - ((77 / 16) : ℂ) * ζ ^ 6 + ((49 / 16) : ℂ) * ζ ^ 8 + ((171 / 16) : ℂ) * ζ ^ 9 - ((109 / 8) : ℂ) * ζ ^ 10 + ((41 / 16) : ℂ) * ζ ^ 11 - ((229 / 16) : ℂ) * ζ ^ 13 + ((141 / 16) : ℂ) * ζ ^ 14 + ((173 / 16) : ℂ) * ζ ^ 15 - ((107 / 16) : ℂ) * ζ ^ 16 - ((45 / 16) : ℂ) * ζ ^ 17 - ((353 / 16) : ℂ) * ζ ^ 18 - ((33 / 4) : ℂ) * ζ ^ 19 + ((149 / 8) : ℂ) * ζ ^ 20 + ((3 / 8) : ℂ) * ζ ^ 21 + ((77 / 16) : ℂ) * ζ ^ 22 + ((157 / 16) : ℂ) * ζ ^ 23 - ((405 / 16) : ℂ) * ζ ^ 24 + ((261 / 16) : ℂ) * ζ ^ 25 - ((3 / 16) : ℂ) * ζ ^ 26 - ((41 / 16) : ℂ) * ζ ^ 27 + ((513 / 16) : ℂ) * ζ ^ 28 + ((15 / 16) : ℂ) * ζ ^ 29 - ((225 / 16) : ℂ) * ζ ^ 30 - ((17 / 4) : ℂ) * ζ ^ 31 + ((107 / 16) : ℂ) * ζ ^ 32 + ((123 / 8) : ℂ) * ζ ^ 33 + ((17 / 4) : ℂ) * ζ ^ 34 - ((201 / 16) : ℂ) * ζ ^ 35 + ((63 / 4) : ℂ) * ζ ^ 36 - (6 : ℂ) * ζ ^ 37 - ((191 / 16) : ℂ) * ζ ^ 38 + ((215 / 16) : ℂ) * ζ ^ 39 + ζ ^ 40 - (6 : ℂ) * ζ ^ 41 + (5 : ℂ) * ζ ^ 42 - ((235 / 8) : ℂ) * ζ ^ 43 + ((11 / 8) : ℂ) * ζ ^ 44 - ((5 / 4) : ℂ) * ζ ^ 45 + (5 : ℂ) * ζ ^ 46 + ((27 / 16) : ℂ) * ζ ^ 47 - ((201 / 8) : ℂ) * ζ ^ 48 - (4 : ℂ) * ζ ^ 49 + ((27 / 16) : ℂ) * ζ ^ 50 + ((27 / 16) : ℂ) * ζ ^ 51 - ((145 / 16) : ℂ) * ζ ^ 52 + ((83 / 8) : ℂ) * ζ ^ 53 - ((107 / 16) : ℂ) * ζ ^ 54 + ((13 / 2) : ℂ) * ζ ^ 55 - ((145 / 16) : ℂ) * ζ ^ 56 + ((45 / 16) : ℂ) * ζ ^ 57 + ((73 / 8) : ℂ) * ζ ^ 58 - ((131 / 16) : ℂ) * ζ ^ 59 + ((145 / 16) : ℂ) * ζ ^ 60 - ((45 / 16) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_4_0 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        4 0 =
      alternatingSixAmbientRow14TransformedGeneratorA
        4 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((117 / 16) : ℂ) + ((19 / 16) : ℂ) * ζ ^ 3 + ((117 / 16) : ℂ) * ζ ^ 4 - ((25 / 16) : ℂ) * ζ ^ 5 + ((87 / 16) : ℂ) * ζ ^ 6 + ((51 / 8) : ℂ) * ζ ^ 8 + ((161 / 16) : ℂ) * ζ ^ 9 + ((37 / 8) : ℂ) * ζ ^ 10 - ((31 / 4) : ℂ) * ζ ^ 11 + ((9 / 4) : ℂ) * ζ ^ 13 + ((13 / 16) : ℂ) * ζ ^ 14 + ((5 / 16) : ℂ) * ζ ^ 15 - ((187 / 16) : ℂ) * ζ ^ 16 + ((17 / 2) : ℂ) * ζ ^ 17 - ((257 / 16) : ℂ) * ζ ^ 18 - ((129 / 16) : ℂ) * ζ ^ 19 + ((5 / 4) : ℂ) * ζ ^ 20 - ((3 / 16) : ℂ) * ζ ^ 21 - ((87 / 16) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 23 - ((207 / 16) : ℂ) * ζ ^ 24 - ((225 / 8) : ℂ) * ζ ^ 25 + ((75 / 16) : ℂ) * ζ ^ 26 + ((31 / 4) : ℂ) * ζ ^ 27 + ((29 / 16) : ℂ) * ζ ^ 28 - ((369 / 16) : ℂ) * ζ ^ 29 + ((111 / 16) : ℂ) * ζ ^ 30 + ((357 / 16) : ℂ) * ζ ^ 31 + ((187 / 16) : ℂ) * ζ ^ 32 - ((3 / 16) : ℂ) * ζ ^ 33 + ((69 / 8) : ℂ) * ζ ^ 34 + ((49 / 8) : ℂ) * ζ ^ 35 + ((311 / 16) : ℂ) * ζ ^ 36 + ((275 / 16) : ℂ) * ζ ^ 37 + ((39 / 16) : ℂ) * ζ ^ 38 + ((11 / 16) : ℂ) * ζ ^ 39 + ((19 / 16) : ℂ) * ζ ^ 40 + ((275 / 16) : ℂ) * ζ ^ 41 - ((81 / 8) : ℂ) * ζ ^ 42 - ((107 / 16) : ℂ) * ζ ^ 43 - ((41 / 8) : ℂ) * ζ ^ 44 + ((425 / 16) : ℂ) * ζ ^ 45 - ((81 / 8) : ℂ) * ζ ^ 46 - ((233 / 16) : ℂ) * ζ ^ 47 - ((23 / 16) : ℂ) * ζ ^ 48 - ((39 / 4) : ℂ) * ζ ^ 49 - ((93 / 16) : ℂ) * ζ ^ 50 - ((233 / 16) : ℂ) * ζ ^ 51 - ((31 / 4) : ℂ) * ζ ^ 52 - ((289 / 16) : ℂ) * ζ ^ 53 + ((255 / 16) : ℂ) * ζ ^ 54 - ((21 / 16) : ℂ) * ζ ^ 55 - ((31 / 4) : ℂ) * ζ ^ 56 - ((17 / 2) : ℂ) * ζ ^ 57 - ((9 / 4) : ℂ) * ζ ^ 58 + ((127 / 8) : ℂ) * ζ ^ 59 + ((31 / 4) : ℂ) * ζ ^ 60 + ((17 / 2) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_4_1 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        4 1 =
      alternatingSixAmbientRow14TransformedGeneratorA
        4 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((513 / 44) : ℂ) - ((41 / 2) : ℂ) * ζ ^ 3 + ((513 / 44) : ℂ) * ζ ^ 4 - ((613 / 88) : ℂ) * ζ ^ 5 - ((497 / 44) : ℂ) * ζ ^ 6 - ((1055 / 88) : ℂ) * ζ ^ 8 + ((543 / 88) : ℂ) * ζ ^ 9 - ((103 / 11) : ℂ) * ζ ^ 10 - ((5 / 88) : ℂ) * ζ ^ 11 - ((167 / 44) : ℂ) * ζ ^ 13 - ((85 / 44) : ℂ) * ζ ^ 14 + ((415 / 88) : ℂ) * ζ ^ 15 - ((125 / 44) : ℂ) * ζ ^ 16 - ((35 / 44) : ℂ) * ζ ^ 17 + ((259 / 22) : ℂ) * ζ ^ 18 - ((105 / 22) : ℂ) * ζ ^ 19 + ((1033 / 88) : ℂ) * ζ ^ 20 - ((139 / 88) : ℂ) * ζ ^ 21 + ((497 / 44) : ℂ) * ζ ^ 22 + ((1917 / 88) : ℂ) * ζ ^ 23 - ((1283 / 88) : ℂ) * ζ ^ 24 + ((307 / 88) : ℂ) * ζ ^ 25 + ((207 / 22) : ℂ) * ζ ^ 26 + ((5 / 88) : ℂ) * ζ ^ 27 + ((1435 / 88) : ℂ) * ζ ^ 28 - ((13 / 44) : ℂ) * ζ ^ 29 - ((423 / 44) : ℂ) * ζ ^ 30 - ((9 / 8) : ℂ) * ζ ^ 31 + ((125 / 44) : ℂ) * ζ ^ 32 + ((243 / 88) : ℂ) * ζ ^ 33 - ((157 / 44) : ℂ) * ζ ^ 34 - ((85 / 22) : ℂ) * ζ ^ 35 + ((41 / 11) : ℂ) * ζ ^ 36 - ((1 / 88) : ℂ) * ζ ^ 37 - ((761 / 44) : ℂ) * ζ ^ 38 + ((21 / 8) : ℂ) * ζ ^ 39 - ((339 / 88) : ℂ) * ζ ^ 40 - ((1 / 88) : ℂ) * ζ ^ 41 + ((83 / 44) : ℂ) * ζ ^ 42 - ((531 / 22) : ℂ) * ζ ^ 43 + ((167 / 88) : ℂ) * ζ ^ 44 + ((57 / 44) : ℂ) * ζ ^ 45 + ((83 / 44) : ℂ) * ζ ^ 46 + ((13 / 11) : ℂ) * ζ ^ 47 - ((1201 / 88) : ℂ) * ζ ^ 48 - ((393 / 88) : ℂ) * ζ ^ 49 - ((24 / 11) : ℂ) * ζ ^ 50 + ((13 / 11) : ℂ) * ζ ^ 51 - ((39 / 44) : ℂ) * ζ ^ 52 + ((15 / 8) : ℂ) * ζ ^ 53 + ((13 / 44) : ℂ) * ζ ^ 54 - ((21 / 8) : ℂ) * ζ ^ 55 - ((39 / 44) : ℂ) * ζ ^ 56 + ((35 / 44) : ℂ) * ζ ^ 57 + ((325 / 88) : ℂ) * ζ ^ 58 + ((127 / 88) : ℂ) * ζ ^ 59 + ((39 / 44) : ℂ) * ζ ^ 60 - ((35 / 44) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_4_2 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        4 2 =
      alternatingSixAmbientRow14TransformedGeneratorA
        4 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((1905 / 176) : ℂ) - ((1457 / 176) : ℂ) * ζ ^ 3 + ((1905 / 176) : ℂ) * ζ ^ 4 - ((2217 / 176) : ℂ) * ζ ^ 5 - ((263 / 16) : ℂ) * ζ ^ 6 + ((51 / 44) : ℂ) * ζ ^ 8 + ((1117 / 176) : ℂ) * ζ ^ 9 - ((1147 / 44) : ℂ) * ζ ^ 10 + ((59 / 88) : ℂ) * ζ ^ 11 - ((169 / 22) : ℂ) * ζ ^ 13 + ((1695 / 176) : ℂ) * ζ ^ 14 + ((241 / 176) : ℂ) * ζ ^ 15 + ((949 / 176) : ℂ) * ζ ^ 16 - ((25 / 4) : ℂ) * ζ ^ 17 + ((1069 / 176) : ℂ) * ζ ^ 18 - ((123 / 176) : ℂ) * ζ ^ 19 + ((214 / 11) : ℂ) * ζ ^ 20 + ((1049 / 176) : ℂ) * ζ ^ 21 + ((263 / 16) : ℂ) * ζ ^ 22 - ((371 / 88) : ℂ) * ζ ^ 23 - ((225 / 16) : ℂ) * ζ ^ 24 + ((2935 / 88) : ℂ) * ζ ^ 25 + ((3617 / 176) : ℂ) * ζ ^ 26 - ((59 / 88) : ℂ) * ζ ^ 27 - ((1121 / 176) : ℂ) * ζ ^ 28 + ((1779 / 176) : ℂ) * ζ ^ 29 + ((1993 / 176) : ℂ) * ζ ^ 30 - ((257 / 176) : ℂ) * ζ ^ 31 - ((949 / 176) : ℂ) * ζ ^ 32 + ((2325 / 176) : ℂ) * ζ ^ 33 - ((2081 / 88) : ℂ) * ζ ^ 34 - ((125 / 88) : ℂ) * ζ ^ 35 - ((921 / 176) : ℂ) * ζ ^ 36 - ((3249 / 176) : ℂ) * ζ ^ 37 - ((969 / 176) : ℂ) * ζ ^ 38 + ((229 / 176) : ℂ) * ζ ^ 39 - ((2259 / 176) : ℂ) * ζ ^ 40 - ((3249 / 176) : ℂ) * ζ ^ 41 - ((181 / 44) : ℂ) * ζ ^ 42 - ((2753 / 176) : ℂ) * ζ ^ 43 + ((809 / 44) : ℂ) * ζ ^ 44 - ((3329 / 176) : ℂ) * ζ ^ 45 - ((181 / 44) : ℂ) * ζ ^ 46 + ((139 / 176) : ℂ) * ζ ^ 47 - ((1193 / 176) : ℂ) * ζ ^ 48 + ((99 / 8) : ℂ) * ζ ^ 49 - ((1201 / 176) : ℂ) * ζ ^ 50 + ((139 / 176) : ℂ) * ζ ^ 51 - ((7 / 44) : ℂ) * ζ ^ 52 + ((2451 / 176) : ℂ) * ζ ^ 53 + ((175 / 16) : ℂ) * ζ ^ 54 - ((111 / 16) : ℂ) * ζ ^ 55 - ((7 / 44) : ℂ) * ζ ^ 56 + ((25 / 4) : ℂ) * ζ ^ 57 + ((59 / 22) : ℂ) * ζ ^ 58 + ((541 / 88) : ℂ) * ζ ^ 59 + ((7 / 44) : ℂ) * ζ ^ 60 - ((25 / 4) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_4_3 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        4 3 =
      alternatingSixAmbientRow14TransformedGeneratorA
        4 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((109 / 24) : ℂ) + ((5 / 24) : ℂ) * ζ ^ 3 + ((109 / 24) : ℂ) * ζ ^ 4 - ((83 / 24) : ℂ) * ζ ^ 5 - ((217 / 24) : ℂ) * ζ ^ 6 + ((71 / 8) : ℂ) * ζ ^ 8 + ((17 / 24) : ℂ) * ζ ^ 9 - ((347 / 24) : ℂ) * ζ ^ 10 + ((5 / 3) : ℂ) * ζ ^ 11 + ((193 / 24) : ℂ) * ζ ^ 13 + ((65 / 12) : ℂ) * ζ ^ 14 + ((7 / 12) : ℂ) * ζ ^ 15 + (12 : ℂ) * ζ ^ 16 - ((11 / 4) : ℂ) * ζ ^ 17 + ((73 / 24) : ℂ) * ζ ^ 18 + ((13 / 12) : ℂ) * ζ ^ 19 + ((143 / 24) : ℂ) * ζ ^ 20 + ((77 / 6) : ℂ) * ζ ^ 21 + ((217 / 24) : ℂ) * ζ ^ 22 - ((121 / 4) : ℂ) * ζ ^ 23 + ((145 / 24) : ℂ) * ζ ^ 24 + ((113 / 6) : ℂ) * ζ ^ 25 + ((295 / 24) : ℂ) * ζ ^ 26 - ((5 / 3) : ℂ) * ζ ^ 27 - ((119 / 4) : ℂ) * ζ ^ 28 + ((21 / 2) : ℂ) * ζ ^ 29 + ((55 / 6) : ℂ) * ζ ^ 30 + ((13 / 8) : ℂ) * ζ ^ 31 - (12 : ℂ) * ζ ^ 32 - ((149 / 24) : ℂ) * ζ ^ 33 - ((359 / 24) : ℂ) * ζ ^ 34 + ((35 / 8) : ℂ) * ζ ^ 35 - ((147 / 8) : ℂ) * ζ ^ 36 - ((55 / 3) : ℂ) * ζ ^ 37 + ((99 / 8) : ℂ) * ζ ^ 38 + ((7 / 12) : ℂ) * ζ ^ 39 - ((5 / 3) : ℂ) * ζ ^ 40 - ((55 / 3) : ℂ) * ζ ^ 41 - ((13 / 4) : ℂ) * ζ ^ 42 + ((71 / 4) : ℂ) * ζ ^ 43 + ((175 / 24) : ℂ) * ζ ^ 44 - ((43 / 12) : ℂ) * ζ ^ 45 - ((13 / 4) : ℂ) * ζ ^ 46 - ((79 / 24) : ℂ) * ζ ^ 47 + ((97 / 8) : ℂ) * ζ ^ 48 + ((131 / 12) : ℂ) * ζ ^ 49 - ((49 / 6) : ℂ) * ζ ^ 50 - ((79 / 24) : ℂ) * ζ ^ 51 + ((51 / 8) : ℂ) * ζ ^ 52 + ((73 / 8) : ℂ) * ζ ^ 53 + ((137 / 12) : ℂ) * ζ ^ 54 - ((11 / 8) : ℂ) * ζ ^ 55 + ((51 / 8) : ℂ) * ζ ^ 56 + ((11 / 4) : ℂ) * ζ ^ 57 - ((5 / 8) : ℂ) * ζ ^ 58 + ((14 / 3) : ℂ) * ζ ^ 59 - ((51 / 8) : ℂ) * ζ ^ 60 - ((11 / 4) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_4_4 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        4 4 =
      alternatingSixAmbientRow14TransformedGeneratorA
        4 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((29 / 16) : ℂ) - ((295 / 16) : ℂ) * ζ ^ 3 + ((29 / 16) : ℂ) * ζ ^ 4 - ((119 / 16) : ℂ) * ζ ^ 5 - ((27 / 16) : ℂ) * ζ ^ 6 - ((223 / 8) : ℂ) * ζ ^ 8 + ((81 / 16) : ℂ) * ζ ^ 9 + ((5 / 2) : ℂ) * ζ ^ 10 + ((3 / 4) : ℂ) * ζ ^ 11 - ((33 / 2) : ℂ) * ζ ^ 13 - ((67 / 16) : ℂ) * ζ ^ 14 + ((127 / 16) : ℂ) * ζ ^ 15 - ((35 / 16) : ℂ) * ζ ^ 16 - ((19 / 8) : ℂ) * ζ ^ 17 + ((345 / 16) : ℂ) * ζ ^ 18 - ((115 / 16) : ℂ) * ζ ^ 19 + ((49 / 8) : ℂ) * ζ ^ 20 - ((69 / 16) : ℂ) * ζ ^ 21 + ((27 / 16) : ℂ) * ζ ^ 22 + ((193 / 4) : ℂ) * ζ ^ 23 - ((133 / 16) : ℂ) * ζ ^ 24 + ((75 / 8) : ℂ) * ζ ^ 25 + ((19 / 16) : ℂ) * ζ ^ 26 - ((3 / 4) : ℂ) * ζ ^ 27 + ((469 / 16) : ℂ) * ζ ^ 28 + ((9 / 16) : ℂ) * ζ ^ 29 - ((151 / 16) : ℂ) * ζ ^ 30 - ((99 / 16) : ℂ) * ζ ^ 31 + ((35 / 16) : ℂ) * ζ ^ 32 - ((169 / 16) : ℂ) * ζ ^ 33 + ((29 / 4) : ℂ) * ζ ^ 34 - ((105 / 8) : ℂ) * ζ ^ 35 + ((41 / 16) : ℂ) * ζ ^ 36 - ((7 / 16) : ℂ) * ζ ^ 37 - ((521 / 16) : ℂ) * ζ ^ 38 + ((135 / 16) : ℂ) * ζ ^ 39 - ((65 / 16) : ℂ) * ζ ^ 40 - ((7 / 16) : ℂ) * ζ ^ 41 + ((1 / 2) : ℂ) * ζ ^ 42 - ((325 / 16) : ℂ) * ζ ^ 43 + ((9 / 4) : ℂ) * ζ ^ 44 - ((201 / 16) : ℂ) * ζ ^ 45 + ((1 / 2) : ℂ) * ζ ^ 46 + ((87 / 16) : ℂ) * ζ ^ 47 - ((165 / 16) : ℂ) * ζ ^ 48 + ((7 / 2) : ℂ) * ζ ^ 49 + ((117 / 16) : ℂ) * ζ ^ 50 + ((87 / 16) : ℂ) * ζ ^ 51 - ((3 / 8) : ℂ) * ζ ^ 52 + ((21 / 16) : ℂ) * ζ ^ 53 - ((125 / 16) : ℂ) * ζ ^ 54 + ((75 / 16) : ℂ) * ζ ^ 55 - ((3 / 8) : ℂ) * ζ ^ 56 + ((19 / 8) : ℂ) * ζ ^ 57 + ((13 / 4) : ℂ) * ζ ^ 58 - ((81 / 8) : ℂ) * ζ ^ 59 + ((3 / 8) : ℂ) * ζ ^ 60 - ((19 / 8) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_4_5 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        4 5 =
      alternatingSixAmbientRow14TransformedGeneratorA
        4 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((195 / 16) : ℂ) - ((31 / 16) : ℂ) * ζ ^ 3 + ((195 / 16) : ℂ) * ζ ^ 4 - ((231 / 16) : ℂ) * ζ ^ 5 - ((99 / 16) : ℂ) * ζ ^ 6 + ((7 / 8) : ℂ) * ζ ^ 8 + ((215 / 16) : ℂ) * ζ ^ 9 - ((175 / 8) : ℂ) * ζ ^ 10 + ((1 / 8) : ℂ) * ζ ^ 11 - ((147 / 8) : ℂ) * ζ ^ 13 + ((251 / 16) : ℂ) * ζ ^ 14 + ((5 / 16) : ℂ) * ζ ^ 15 - ((83 / 16) : ℂ) * ζ ^ 16 - ζ ^ 17 - ((289 / 16) : ℂ) * ζ ^ 18 - ((3 / 16) : ℂ) * ζ ^ 19 + ((153 / 8) : ℂ) * ζ ^ 20 - ((15 / 16) : ℂ) * ζ ^ 21 + ((99 / 16) : ℂ) * ζ ^ 22 - ((85 / 8) : ℂ) * ζ ^ 23 - ((389 / 16) : ℂ) * ζ ^ 24 + ((111 / 8) : ℂ) * ζ ^ 25 + ((47 / 16) : ℂ) * ζ ^ 26 - ((1 / 8) : ℂ) * ζ ^ 27 + ((247 / 16) : ℂ) * ζ ^ 28 - ((141 / 16) : ℂ) * ζ ^ 29 + ((37 / 16) : ℂ) * ζ ^ 30 - ((17 / 16) : ℂ) * ζ ^ 31 + ((83 / 16) : ℂ) * ζ ^ 32 + ((637 / 16) : ℂ) * ζ ^ 33 - ((47 / 4) : ℂ) * ζ ^ 34 - ((13 / 2) : ℂ) * ζ ^ 35 + ((137 / 16) : ℂ) * ζ ^ 36 - ((17 / 16) : ℂ) * ζ ^ 37 + ((187 / 16) : ℂ) * ζ ^ 38 + ((91 / 16) : ℂ) * ζ ^ 39 - ((265 / 16) : ℂ) * ζ ^ 40 - ((17 / 16) : ℂ) * ζ ^ 41 + ((13 / 4) : ℂ) * ζ ^ 42 - ((373 / 16) : ℂ) * ζ ^ 43 + ((59 / 4) : ℂ) * ζ ^ 44 - ((25 / 16) : ℂ) * ζ ^ 45 + ((13 / 4) : ℂ) * ζ ^ 46 + ((15 / 16) : ℂ) * ζ ^ 47 - ((465 / 16) : ℂ) * ζ ^ 48 - ((11 / 8) : ℂ) * ζ ^ 49 - ((75 / 16) : ℂ) * ζ ^ 50 + ((15 / 16) : ℂ) * ζ ^ 51 - ((27 / 8) : ℂ) * ζ ^ 52 - ((159 / 16) : ℂ) * ζ ^ 53 + ((23 / 16) : ℂ) * ζ ^ 54 - ((85 / 16) : ℂ) * ζ ^ 55 - ((27 / 8) : ℂ) * ζ ^ 56 + ζ ^ 57 - ((11 / 8) : ℂ) * ζ ^ 58 + ((35 / 8) : ℂ) * ζ ^ 59 + ((27 / 8) : ℂ) * ζ ^ 60 - ζ ^ 61)
private theorem row14_transformedGeneratorA_5_0 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        5 0 =
      alternatingSixAmbientRow14TransformedGeneratorA
        5 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((1 / 16) : ℂ) + ((1 / 16) : ℂ) * ζ ^ 3 - ((1 / 16) : ℂ) * ζ ^ 4 + ((107 / 16) : ℂ) * ζ ^ 5 - ((27 / 16) : ℂ) * ζ ^ 6 + ((19 / 2) : ℂ) * ζ ^ 8 + ((29 / 16) : ℂ) * ζ ^ 9 + (13 : ℂ) * ζ ^ 10 - ((17 / 8) : ℂ) * ζ ^ 11 + ((171 / 8) : ℂ) * ζ ^ 13 - ((235 / 16) : ℂ) * ζ ^ 14 + ((53 / 16) : ℂ) * ζ ^ 15 - ((13 / 16) : ℂ) * ζ ^ 16 + ((17 / 2) : ℂ) * ζ ^ 17 + ((93 / 16) : ℂ) * ζ ^ 18 - ((87 / 16) : ℂ) * ζ ^ 19 - ((71 / 8) : ℂ) * ζ ^ 20 + ((151 / 16) : ℂ) * ζ ^ 21 + ((27 / 16) : ℂ) * ζ ^ 22 - ζ ^ 23 + ((129 / 16) : ℂ) * ζ ^ 24 - (27 : ℂ) * ζ ^ 25 + ((293 / 16) : ℂ) * ζ ^ 26 + ((17 / 8) : ℂ) * ζ ^ 27 - ((105 / 16) : ℂ) * ζ ^ 28 - ((233 / 16) : ℂ) * ζ ^ 29 + ((53 / 16) : ℂ) * ζ ^ 30 + ((145 / 16) : ℂ) * ζ ^ 31 + ((13 / 16) : ℂ) * ζ ^ 32 - ((269 / 16) : ℂ) * ζ ^ 33 + ((93 / 8) : ℂ) * ζ ^ 34 + ((45 / 8) : ℂ) * ζ ^ 35 - ((27 / 16) : ℂ) * ζ ^ 36 + ((121 / 16) : ℂ) * ζ ^ 37 - ((301 / 16) : ℂ) * ζ ^ 38 - ((13 / 16) : ℂ) * ζ ^ 39 + ((127 / 16) : ℂ) * ζ ^ 40 + ((121 / 16) : ℂ) * ζ ^ 41 - ((133 / 8) : ℂ) * ζ ^ 42 - ((153 / 16) : ℂ) * ζ ^ 43 - ((45 / 4) : ℂ) * ζ ^ 44 + ((493 / 16) : ℂ) * ζ ^ 45 - ((133 / 8) : ℂ) * ζ ^ 46 - ((111 / 16) : ℂ) * ζ ^ 47 + ((43 / 16) : ℂ) * ζ ^ 48 - ((35 / 8) : ℂ) * ζ ^ 49 + ((147 / 16) : ℂ) * ζ ^ 50 - ((111 / 16) : ℂ) * ζ ^ 51 + ((5 / 2) : ℂ) * ζ ^ 52 - ((189 / 16) : ℂ) * ζ ^ 53 + ((119 / 16) : ℂ) * ζ ^ 54 + ((69 / 16) : ℂ) * ζ ^ 55 + ((5 / 2) : ℂ) * ζ ^ 56 - ((17 / 2) : ℂ) * ζ ^ 57 + (4 : ℂ) * ζ ^ 58 + ((21 / 8) : ℂ) * ζ ^ 59 - ((5 / 2) : ℂ) * ζ ^ 60 + ((17 / 2) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_5_1 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        5 1 =
      alternatingSixAmbientRow14TransformedGeneratorA
        5 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((43 / 22) : ℂ) - ((195 / 44) : ℂ) * ζ ^ 3 - ((43 / 22) : ℂ) * ζ ^ 4 + ((835 / 88) : ℂ) * ζ ^ 5 - ((485 / 44) : ℂ) * ζ ^ 6 + ((853 / 88) : ℂ) * ζ ^ 8 - ((1125 / 88) : ℂ) * ζ ^ 9 + ((75 / 11) : ℂ) * ζ ^ 10 - ((123 / 88) : ℂ) * ζ ^ 11 + ((665 / 44) : ℂ) * ζ ^ 13 - ((785 / 44) : ℂ) * ζ ^ 14 + ((1345 / 88) : ℂ) * ζ ^ 15 - ((225 / 44) : ℂ) * ζ ^ 16 - ((145 / 44) : ℂ) * ζ ^ 17 + ((300 / 11) : ℂ) * ζ ^ 18 - ((367 / 22) : ℂ) * ζ ^ 19 + ((347 / 88) : ℂ) * ζ ^ 20 - ((321 / 88) : ℂ) * ζ ^ 21 + ((485 / 44) : ℂ) * ζ ^ 22 + ((723 / 88) : ℂ) * ζ ^ 23 - ((797 / 88) : ℂ) * ζ ^ 24 + ((219 / 88) : ℂ) * ζ ^ 25 + ((45 / 11) : ℂ) * ζ ^ 26 + ((123 / 88) : ℂ) * ζ ^ 27 - ((1149 / 88) : ℂ) * ζ ^ 28 + ((150 / 11) : ℂ) * ζ ^ 29 - ((645 / 44) : ℂ) * ζ ^ 30 + ((125 / 88) : ℂ) * ζ ^ 31 + ((225 / 44) : ℂ) * ζ ^ 32 - ((1607 / 88) : ℂ) * ζ ^ 33 - ((145 / 44) : ℂ) * ζ ^ 34 - ((513 / 44) : ℂ) * ζ ^ 35 + ((255 / 22) : ℂ) * ζ ^ 36 - ((259 / 88) : ℂ) * ζ ^ 37 - ((555 / 22) : ℂ) * ζ ^ 38 + ((905 / 88) : ℂ) * ζ ^ 39 - ((701 / 88) : ℂ) * ζ ^ 40 - ((259 / 88) : ℂ) * ζ ^ 41 + ((305 / 44) : ℂ) * ζ ^ 42 - ((565 / 44) : ℂ) * ζ ^ 43 + ((821 / 88) : ℂ) * ζ ^ 44 - ((277 / 22) : ℂ) * ζ ^ 45 + ((305 / 44) : ℂ) * ζ ^ 46 - ((1 / 44) : ℂ) * ζ ^ 47 + ((279 / 88) : ℂ) * ζ ^ 48 + ((207 / 88) : ℂ) * ζ ^ 49 - ((83 / 44) : ℂ) * ζ ^ 50 - ((1 / 44) : ℂ) * ζ ^ 51 - ((285 / 44) : ℂ) * ζ ^ 52 + ((1607 / 88) : ℂ) * ζ ^ 53 - ((111 / 22) : ℂ) * ζ ^ 54 + ((411 / 88) : ℂ) * ζ ^ 55 - ((285 / 44) : ℂ) * ζ ^ 56 + ((145 / 44) : ℂ) * ζ ^ 57 + ((481 / 88) : ℂ) * ζ ^ 58 - ((409 / 88) : ℂ) * ζ ^ 59 + ((285 / 44) : ℂ) * ζ ^ 60 - ((145 / 44) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_5_2 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        5 2 =
      alternatingSixAmbientRow14TransformedGeneratorA
        5 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((523 / 176) : ℂ) - ((1087 / 176) : ℂ) * ζ ^ 3 + ((523 / 176) : ℂ) * ζ ^ 4 + ((619 / 176) : ℂ) * ζ ^ 5 - ((723 / 176) : ℂ) * ζ ^ 6 + ((141 / 88) : ℂ) * ζ ^ 8 - ((141 / 16) : ℂ) * ζ ^ 9 + ((613 / 88) : ℂ) * ζ ^ 10 + ((119 / 11) : ℂ) * ζ ^ 11 - ((79 / 8) : ℂ) * ζ ^ 13 - ((1949 / 176) : ℂ) * ζ ^ 14 + ((415 / 16) : ℂ) * ζ ^ 15 + ((351 / 176) : ℂ) * ζ ^ 16 - ((233 / 44) : ℂ) * ζ ^ 17 + ((1231 / 176) : ℂ) * ζ ^ 18 - ((2661 / 176) : ℂ) * ζ ^ 19 + ((1399 / 88) : ℂ) * ζ ^ 20 + ((51 / 176) : ℂ) * ζ ^ 21 + ((723 / 176) : ℂ) * ζ ^ 22 - ((247 / 88) : ℂ) * ζ ^ 23 - ((2447 / 176) : ℂ) * ζ ^ 24 + ((39 / 4) : ℂ) * ζ ^ 25 - ((673 / 176) : ℂ) * ζ ^ 26 - ((119 / 11) : ℂ) * ζ ^ 27 - ((205 / 16) : ℂ) * ζ ^ 28 + ((357 / 16) : ℂ) * ζ ^ 29 - ((3741 / 176) : ℂ) * ζ ^ 30 - ((2205 / 176) : ℂ) * ζ ^ 31 - ((351 / 176) : ℂ) * ζ ^ 32 - ((79 / 16) : ℂ) * ζ ^ 33 + ((811 / 88) : ℂ) * ζ ^ 34 - ((165 / 8) : ℂ) * ζ ^ 35 + ((1577 / 176) : ℂ) * ζ ^ 36 - ((1915 / 176) : ℂ) * ζ ^ 37 - ((3185 / 176) : ℂ) * ζ ^ 38 + ((5233 / 176) : ℂ) * ζ ^ 39 - ((1803 / 176) : ℂ) * ζ ^ 40 - ((1915 / 176) : ℂ) * ζ ^ 41 + ((349 / 44) : ℂ) * ζ ^ 42 - ((1891 / 176) : ℂ) * ζ ^ 43 + ((2041 / 88) : ℂ) * ζ ^ 44 - ((2617 / 176) : ℂ) * ζ ^ 45 + ((349 / 44) : ℂ) * ζ ^ 46 + ((301 / 176) : ℂ) * ζ ^ 47 - ((51 / 176) : ℂ) * ζ ^ 48 + ((201 / 44) : ℂ) * ζ ^ 49 + ((563 / 176) : ℂ) * ζ ^ 50 + ((301 / 176) : ℂ) * ζ ^ 51 - ((241 / 22) : ℂ) * ζ ^ 52 + ((3623 / 176) : ℂ) * ζ ^ 53 - ((1959 / 176) : ℂ) * ζ ^ 54 + ((151 / 16) : ℂ) * ζ ^ 55 - ((241 / 22) : ℂ) * ζ ^ 56 + ((233 / 44) : ℂ) * ζ ^ 57 + ((301 / 44) : ℂ) * ζ ^ 58 - ((981 / 88) : ℂ) * ζ ^ 59 + ((241 / 22) : ℂ) * ζ ^ 60 - ((233 / 44) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_5_3 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        5 3 =
      alternatingSixAmbientRow14TransformedGeneratorA
        5 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((25 / 8) : ℂ) - ((167 / 24) : ℂ) * ζ ^ 3 + ((25 / 8) : ℂ) * ζ ^ 4 - ((47 / 8) : ℂ) * ζ ^ 5 + ((21 / 8) : ℂ) * ζ ^ 6 - ((367 / 24) : ℂ) * ζ ^ 8 + ((95 / 24) : ℂ) * ζ ^ 9 - ((247 / 24) : ℂ) * ζ ^ 10 + ((175 / 12) : ℂ) * ζ ^ 11 - ((1067 / 24) : ℂ) * ζ ^ 13 + ((155 / 12) : ℂ) * ζ ^ 14 - ((8 / 3) : ℂ) * ζ ^ 15 + ((47 / 6) : ℂ) * ζ ^ 16 - ((23 / 12) : ℂ) * ζ ^ 17 - ((907 / 24) : ℂ) * ζ ^ 18 + ((69 / 4) : ℂ) * ζ ^ 19 - ((53 / 8) : ℂ) * ζ ^ 20 + ((181 / 12) : ℂ) * ζ ^ 21 - ((21 / 8) : ℂ) * ζ ^ 22 - ((129 / 4) : ℂ) * ζ ^ 23 + ((347 / 24) : ℂ) * ζ ^ 24 + ((16 / 3) : ℂ) * ζ ^ 25 - ((31 / 8) : ℂ) * ζ ^ 26 - ((175 / 12) : ℂ) * ζ ^ 27 + ((19 / 6) : ℂ) * ζ ^ 28 + ((85 / 4) : ℂ) * ζ ^ 29 - ((5 / 6) : ℂ) * ζ ^ 30 - ((257 / 24) : ℂ) * ζ ^ 31 - ((47 / 6) : ℂ) * ζ ^ 32 + ((211 / 8) : ℂ) * ζ ^ 33 + ((53 / 24) : ℂ) * ζ ^ 34 + ((179 / 24) : ℂ) * ζ ^ 35 - ((47 / 8) : ℂ) * ζ ^ 36 - ((227 / 12) : ℂ) * ζ ^ 37 + ((551 / 24) : ℂ) * ζ ^ 38 + (11 : ℂ) * ζ ^ 39 + ((83 / 12) : ℂ) * ζ ^ 40 - ((227 / 12) : ℂ) * ζ ^ 41 + ((5 / 4) : ℂ) * ζ ^ 42 + (11 : ℂ) * ζ ^ 43 + ((23 / 8) : ℂ) * ζ ^ 44 + ((17 / 3) : ℂ) * ζ ^ 45 + ((5 / 4) : ℂ) * ζ ^ 46 - ((31 / 8) : ℂ) * ζ ^ 47 - ((89 / 24) : ℂ) * ζ ^ 48 + ((67 / 12) : ℂ) * ζ ^ 49 + ((5 / 2) : ℂ) * ζ ^ 50 - ((31 / 8) : ℂ) * ζ ^ 51 - ((47 / 24) : ℂ) * ζ ^ 52 + ((37 / 24) : ℂ) * ζ ^ 53 - ((15 / 4) : ℂ) * ζ ^ 54 + ((101 / 24) : ℂ) * ζ ^ 55 - ((47 / 24) : ℂ) * ζ ^ 56 + ((23 / 12) : ℂ) * ζ ^ 57 - ((47 / 24) : ℂ) * ζ ^ 58 - ((1 / 3) : ℂ) * ζ ^ 59 + ((47 / 24) : ℂ) * ζ ^ 60 - ((23 / 12) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_5_4 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        5 4 =
      alternatingSixAmbientRow14TransformedGeneratorA
        5 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (((33 / 16) : ℂ) + ((99 / 16) : ℂ) * ζ ^ 3 - ((33 / 16) : ℂ) * ζ ^ 4 + ((149 / 16) : ℂ) * ζ ^ 5 - ((113 / 16) : ℂ) * ζ ^ 6 + ((93 / 4) : ℂ) * ζ ^ 8 - ((219 / 16) : ℂ) * ζ ^ 9 + ((115 / 8) : ℂ) * ζ ^ 10 - ((57 / 8) : ℂ) * ζ ^ 11 + ((387 / 8) : ℂ) * ζ ^ 13 - ((343 / 16) : ℂ) * ζ ^ 14 + ((183 / 16) : ℂ) * ζ ^ 15 - ((33 / 16) : ℂ) * ζ ^ 16 - ((35 / 8) : ℂ) * ζ ^ 17 + ((751 / 16) : ℂ) * ζ ^ 18 - ((297 / 16) : ℂ) * ζ ^ 19 + (9 : ℂ) * ζ ^ 20 - ((191 / 16) : ℂ) * ζ ^ 21 + ((113 / 16) : ℂ) * ζ ^ 22 + (11 : ℂ) * ζ ^ 23 - ((177 / 16) : ℂ) * ζ ^ 24 + (3 : ℂ) * ζ ^ 25 - ((23 / 16) : ℂ) * ζ ^ 26 + ((57 / 8) : ℂ) * ζ ^ 27 - ((521 / 16) : ℂ) * ζ ^ 28 + ((181 / 16) : ℂ) * ζ ^ 29 - ((357 / 16) : ℂ) * ζ ^ 30 + ((57 / 16) : ℂ) * ζ ^ 31 + ((33 / 16) : ℂ) * ζ ^ 32 - ((631 / 16) : ℂ) * ζ ^ 33 + ((27 / 4) : ℂ) * ζ ^ 34 - ((145 / 8) : ℂ) * ζ ^ 35 + ((59 / 16) : ℂ) * ζ ^ 36 + ((51 / 16) : ℂ) * ζ ^ 37 - ((393 / 16) : ℂ) * ζ ^ 38 + ((119 / 16) : ℂ) * ζ ^ 39 - ((173 / 16) : ℂ) * ζ ^ 40 + ((51 / 16) : ℂ) * ζ ^ 41 + ((17 / 2) : ℂ) * ζ ^ 42 - ((39 / 16) : ℂ) * ζ ^ 43 + ((83 / 8) : ℂ) * ζ ^ 44 - ((289 / 16) : ℂ) * ζ ^ 45 + ((17 / 2) : ℂ) * ζ ^ 46 + ((57 / 16) : ℂ) * ζ ^ 47 + ((189 / 16) : ℂ) * ζ ^ 48 - ((21 / 8) : ℂ) * ζ ^ 49 + ((33 / 16) : ℂ) * ζ ^ 50 + ((57 / 16) : ℂ) * ζ ^ 51 - ((13 / 8) : ℂ) * ζ ^ 52 + ((297 / 16) : ℂ) * ζ ^ 53 - ((169 / 16) : ℂ) * ζ ^ 54 + ((13 / 16) : ℂ) * ζ ^ 55 - ((13 / 8) : ℂ) * ζ ^ 56 + ((35 / 8) : ℂ) * ζ ^ 57 + ((5 / 2) : ℂ) * ζ ^ 58 - ((35 / 8) : ℂ) * ζ ^ 59 + ((13 / 8) : ℂ) * ζ ^ 60 - ((35 / 8) : ℂ) * ζ ^ 61)
private theorem row14_transformedGeneratorA_5_5 :
    (alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis)
        5 5 =
      alternatingSixAmbientRow14TransformedGeneratorA
        5 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow14Eigenbasis,
      alternatingSixAmbientRow14EigenbasisInverse,
      alternatingSixFiveAmbient_row14_matrixA,
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row14 (-((77 / 16) : ℂ) - ((201 / 16) : ℂ) * ζ ^ 3 + ((77 / 16) : ℂ) * ζ ^ 4 - ((3 / 16) : ℂ) * ζ ^ 5 - ((105 / 16) : ℂ) * ζ ^ 6 - ((45 / 4) : ℂ) * ζ ^ 8 - ((21 / 16) : ℂ) * ζ ^ 9 + ((13 / 4) : ℂ) * ζ ^ 10 + ((21 / 4) : ℂ) * ζ ^ 11 - ((67 / 4) : ℂ) * ζ ^ 13 - ((157 / 16) : ℂ) * ζ ^ 14 + ((337 / 16) : ℂ) * ζ ^ 15 - ((49 / 16) : ℂ) * ζ ^ 16 - ((3 / 2) : ℂ) * ζ ^ 17 + ((153 / 16) : ℂ) * ζ ^ 18 - ((253 / 16) : ℂ) * ζ ^ 19 + ((25 / 2) : ℂ) * ζ ^ 20 - ((37 / 16) : ℂ) * ζ ^ 21 + ((105 / 16) : ℂ) * ζ ^ 22 + ((199 / 8) : ℂ) * ζ ^ 23 - ((249 / 16) : ℂ) * ζ ^ 24 + ((3 / 2) : ℂ) * ζ ^ 25 + ((45 / 16) : ℂ) * ζ ^ 26 - ((21 / 4) : ℂ) * ζ ^ 27 + ((309 / 16) : ℂ) * ζ ^ 28 + ((83 / 16) : ℂ) * ζ ^ 29 - ((105 / 16) : ℂ) * ζ ^ 30 - ((109 / 16) : ℂ) * ζ ^ 31 + ((49 / 16) : ℂ) * ζ ^ 32 + ((87 / 16) : ℂ) * ζ ^ 33 - ((15 / 4) : ℂ) * ζ ^ 34 - ((7 / 4) : ℂ) * ζ ^ 35 + ((123 / 16) : ℂ) * ζ ^ 36 - ((11 / 16) : ℂ) * ζ ^ 37 - ((361 / 16) : ℂ) * ζ ^ 38 + ((87 / 16) : ℂ) * ζ ^ 39 + ((39 / 16) : ℂ) * ζ ^ 40 - ((11 / 16) : ℂ) * ζ ^ 41 + ((15 / 4) : ℂ) * ζ ^ 42 - ((351 / 16) : ℂ) * ζ ^ 43 - ((7 / 8) : ℂ) * ζ ^ 44 + ((23 / 16) : ℂ) * ζ ^ 45 + ((15 / 4) : ℂ) * ζ ^ 46 + ((25 / 16) : ℂ) * ζ ^ 47 - ((83 / 16) : ℂ) * ζ ^ 48 - ((27 / 4) : ℂ) * ζ ^ 49 - ((7 / 16) : ℂ) * ζ ^ 50 + ((25 / 16) : ℂ) * ζ ^ 51 - ((37 / 8) : ℂ) * ζ ^ 52 + ((129 / 16) : ℂ) * ζ ^ 53 - ((53 / 16) : ℂ) * ζ ^ 54 + ((21 / 16) : ℂ) * ζ ^ 55 - ((37 / 8) : ℂ) * ζ ^ 56 + ((3 / 2) : ℂ) * ζ ^ 57 + ((27 / 8) : ℂ) * ζ ^ 58 - ((23 / 8) : ℂ) * ζ ^ 59 + ((37 / 8) : ℂ) * ζ ^ 60 - ((3 / 2) : ℂ) * ζ ^ 61)
/-- Exact conjugation formula for the row 14 first
generator. -/
theorem alternatingSixAmbientRow14TransformedGeneratorA_eq :
    alternatingSixAmbientRow14EigenbasisInverse *
        alternatingSixFiveAmbient_row14_matrixA *
        alternatingSixAmbientRow14Eigenbasis =
      alternatingSixAmbientRow14TransformedGeneratorA := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row14_transformedGeneratorA_0_0
  · exact row14_transformedGeneratorA_0_1
  · exact row14_transformedGeneratorA_0_2
  · exact row14_transformedGeneratorA_0_3
  · exact row14_transformedGeneratorA_0_4
  · exact row14_transformedGeneratorA_0_5
  · exact row14_transformedGeneratorA_1_0
  · exact row14_transformedGeneratorA_1_1
  · exact row14_transformedGeneratorA_1_2
  · exact row14_transformedGeneratorA_1_3
  · exact row14_transformedGeneratorA_1_4
  · exact row14_transformedGeneratorA_1_5
  · exact row14_transformedGeneratorA_2_0
  · exact row14_transformedGeneratorA_2_1
  · exact row14_transformedGeneratorA_2_2
  · exact row14_transformedGeneratorA_2_3
  · exact row14_transformedGeneratorA_2_4
  · exact row14_transformedGeneratorA_2_5
  · exact row14_transformedGeneratorA_3_0
  · exact row14_transformedGeneratorA_3_1
  · exact row14_transformedGeneratorA_3_2
  · exact row14_transformedGeneratorA_3_3
  · exact row14_transformedGeneratorA_3_4
  · exact row14_transformedGeneratorA_3_5
  · exact row14_transformedGeneratorA_4_0
  · exact row14_transformedGeneratorA_4_1
  · exact row14_transformedGeneratorA_4_2
  · exact row14_transformedGeneratorA_4_3
  · exact row14_transformedGeneratorA_4_4
  · exact row14_transformedGeneratorA_4_5
  · exact row14_transformedGeneratorA_5_0
  · exact row14_transformedGeneratorA_5_1
  · exact row14_transformedGeneratorA_5_2
  · exact row14_transformedGeneratorA_5_3
  · exact row14_transformedGeneratorA_5_4
  · exact row14_transformedGeneratorA_5_5


end InductiveMcKay
end McKayConjecture
