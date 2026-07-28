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
# Checked diagonal data for ambient row 17

This generated module records an exact eigenbasis for the second generator
and the first generator in that basis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Eigenvalue block labels for row 17. -/
def alternatingSixAmbientRow17EigenvalueLabel :
    Fin 8 → Fin 4 :=
  ![0, 0, 1, 1, 2, 2, 3, 3]

/-- Second-generator eigenvalues, including their multiplicities. -/
def alternatingSixAmbientRow17GeneratorBEigenvalue :
    Fin 8 → ℂ :=
  fun i ↦
    alternatingSixOrderFourEigenvalue
      (alternatingSixAmbientRow17EigenvalueLabel i)

/-- Diagonal form of the row 17 second generator. -/
def alternatingSixAmbientRow17GeneratorBDiagonal :
    Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.diagonal
    alternatingSixAmbientRow17GeneratorBEigenvalue

/-- Checked eigenbasis for the row 17 second generator. -/
def alternatingSixAmbientRow17Eigenbasis :
    Matrix (Fin 8) (Fin 8) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [(1, 0), (-1, 24)],
      alternatingSixCyclotomicValue [(1, 0), (-1, 8), (-1, 12), (1, 24), (1, 28)],
      alternatingSixCyclotomicValue [((-49 / 41), 0), ((-22 / 41), 2), ((-47 / 41), 6), ((11 / 41), 8), ((-21 / 41), 12), ((-18 / 41), 18), ((22 / 41), 22), ((-54 / 41), 24), ((-11 / 41), 28), ((-37 / 41), 30)],
      alternatingSixCyclotomicValue [((-13 / 41), 0), ((36 / 41), 2), ((21 / 41), 6), ((23 / 41), 8), ((12 / 41), 12), ((-19 / 41), 18), ((-36 / 41), 22), ((-16 / 41), 24), ((-23 / 41), 28), ((27 / 41), 30)],
      alternatingSixCyclotomicValue [((7 / 11), 0), ((-10 / 11), 8), ((2 / 11), 12), ((15 / 11), 24), ((10 / 11), 28)],
      alternatingSixCyclotomicValue [((-1 / 11), 0), ((-19 / 11), 8), ((-5 / 11), 12), ((1 / 11), 24), ((19 / 11), 28)],
      alternatingSixCyclotomicValue [((-49 / 41), 0), ((22 / 41), 2), ((47 / 41), 6), ((11 / 41), 8), ((-21 / 41), 12), ((18 / 41), 18), ((-22 / 41), 22), ((-54 / 41), 24), ((-11 / 41), 28), ((37 / 41), 30)],
      alternatingSixCyclotomicValue [((-13 / 41), 0), ((-36 / 41), 2), ((-21 / 41), 6), ((23 / 41), 8), ((12 / 41), 12), ((19 / 41), 18), ((36 / 41), 22), ((-16 / 41), 24), ((-23 / 41), 28), ((-27 / 41), 30)]],
    ![alternatingSixCyclotomicValue [(1, 8), (1, 24), (-1, 28)],
      alternatingSixCyclotomicValue [(1, 24)],
      alternatingSixCyclotomicValue [((-10 / 41), 0), ((34 / 41), 2), ((13 / 41), 6), ((24 / 41), 8), ((25 / 41), 12), ((-2 / 41), 18), ((-34 / 41), 22), ((-6 / 41), 24), ((-24 / 41), 28), ((5 / 41), 30)],
      alternatingSixCyclotomicValue [((35 / 41), 0), ((4 / 41), 2), ((16 / 41), 6), ((-43 / 41), 8), ((-26 / 41), 12), ((7 / 41), 18), ((-4 / 41), 22), ((21 / 41), 24), ((43 / 41), 28), ((3 / 41), 30)],
      alternatingSixCyclotomicValue [((-8 / 11), 0), ((13 / 11), 8), ((-18 / 11), 12), ((-3 / 11), 24), ((-13 / 11), 28)],
      alternatingSixCyclotomicValue [((-2 / 11), 0), ((6 / 11), 8), ((12 / 11), 12), ((-9 / 11), 24), ((-6 / 11), 28)],
      alternatingSixCyclotomicValue [((-10 / 41), 0), ((-34 / 41), 2), ((-13 / 41), 6), ((24 / 41), 8), ((25 / 41), 12), ((2 / 41), 18), ((34 / 41), 22), ((-6 / 41), 24), ((-24 / 41), 28), ((-5 / 41), 30)],
      alternatingSixCyclotomicValue [((35 / 41), 0), ((-4 / 41), 2), ((-16 / 41), 6), ((-43 / 41), 8), ((-26 / 41), 12), ((-7 / 41), 18), ((4 / 41), 22), ((21 / 41), 24), ((43 / 41), 28), ((-3 / 41), 30)]],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(-1, 0), (1, 8), (1, 12), (-1, 24), (-1, 28)],
      alternatingSixCyclotomicValue [((-23 / 41), 0), ((29 / 41), 2), ((34 / 41), 6), ((47 / 41), 8), ((37 / 41), 12), ((-21 / 41), 18), ((-29 / 41), 22), ((-22 / 41), 24), ((-47 / 41), 28), ((-9 / 41), 30)],
      alternatingSixCyclotomicValue [((-22 / 41), 0), ((1 / 41), 2), ((4 / 41), 6), ((20 / 41), 8), ((14 / 41), 12), ((-29 / 41), 18), ((-1 / 41), 22), ((-5 / 41), 24), ((-20 / 41), 28), ((11 / 41), 30)],
      alternatingSixCyclotomicValue [((26 / 11), 0), ((-34 / 11), 8), ((-46 / 11), 12), ((40 / 11), 24), ((34 / 11), 28)],
      alternatingSixCyclotomicValue [((-21 / 11), 0), ((-3 / 11), 8), ((5 / 11), 12), ((-23 / 11), 24), ((3 / 11), 28)],
      alternatingSixCyclotomicValue [((-23 / 41), 0), ((-29 / 41), 2), ((-34 / 41), 6), ((47 / 41), 8), ((37 / 41), 12), ((21 / 41), 18), ((29 / 41), 22), ((-22 / 41), 24), ((-47 / 41), 28), ((9 / 41), 30)],
      alternatingSixCyclotomicValue [((-22 / 41), 0), ((-1 / 41), 2), ((-4 / 41), 6), ((20 / 41), 8), ((14 / 41), 12), ((29 / 41), 18), ((1 / 41), 22), ((-5 / 41), 24), ((-20 / 41), 28), ((-11 / 41), 30)]],
    ![alternatingSixCyclotomicValue [(1, 0), (-1, 24)],
      alternatingSixCyclotomicValue [(1, 0), (-1, 8), (-1, 12), (1, 24), (1, 28)],
      alternatingSixCyclotomicValue [((10 / 41), 0), ((-75 / 41), 2), ((-54 / 41), 6), ((-65 / 41), 8), ((-25 / 41), 12), ((43 / 41), 18), ((75 / 41), 22), ((47 / 41), 24), ((65 / 41), 28), ((-5 / 41), 30)],
      alternatingSixCyclotomicValue [((6 / 41), 0), ((-4 / 41), 2), ((-16 / 41), 6), ((2 / 41), 8), ((-15 / 41), 12), ((-7 / 41), 18), ((4 / 41), 22), ((-21 / 41), 24), ((-2 / 41), 28), ((-3 / 41), 30)],
      alternatingSixCyclotomicValue [((-7 / 11), 0), ((10 / 11), 8), ((-2 / 11), 12), ((-15 / 11), 24), ((-10 / 11), 28)],
      alternatingSixCyclotomicValue [((1 / 11), 0), ((19 / 11), 8), ((5 / 11), 12), ((-1 / 11), 24), ((-19 / 11), 28)],
      alternatingSixCyclotomicValue [((10 / 41), 0), ((75 / 41), 2), ((54 / 41), 6), ((-65 / 41), 8), ((-25 / 41), 12), ((-43 / 41), 18), ((-75 / 41), 22), ((47 / 41), 24), ((65 / 41), 28), ((5 / 41), 30)],
      alternatingSixCyclotomicValue [((6 / 41), 0), ((4 / 41), 2), ((16 / 41), 6), ((2 / 41), 8), ((-15 / 41), 12), ((7 / 41), 18), ((-4 / 41), 22), ((-21 / 41), 24), ((-2 / 41), 28), ((3 / 41), 30)]],
    ![alternatingSixCyclotomicValue [(-2, 0), (1, 8), (1, 12), (-1, 24), (-1, 28)],
      alternatingSixCyclotomicValue [(1, 12)],
      alternatingSixCyclotomicValue [((-37 / 41), 0), ((11 / 41), 2), ((-38 / 41), 6), ((15 / 41), 8), ((-10 / 41), 12), ((-32 / 41), 18), ((-11 / 41), 22), ((-55 / 41), 24), ((-15 / 41), 28), ((-43 / 41), 30)],
      alternatingSixCyclotomicValue [((27 / 41), 0), ((23 / 41), 2), ((10 / 41), 6), ((9 / 41), 8), ((-6 / 41), 12), ((-11 / 41), 18), ((-23 / 41), 22), ((8 / 41), 24), ((-9 / 41), 28), ((7 / 41), 30)],
      alternatingSixCyclotomicValue [((-8 / 11), 0), ((-9 / 11), 8), ((-7 / 11), 12), ((-3 / 11), 24), ((9 / 11), 28)],
      alternatingSixCyclotomicValue [((-2 / 11), 0), ((6 / 11), 8), ((1 / 11), 12), ((-20 / 11), 24), ((-6 / 11), 28)],
      alternatingSixCyclotomicValue [((-37 / 41), 0), ((-11 / 41), 2), ((38 / 41), 6), ((15 / 41), 8), ((-10 / 41), 12), ((32 / 41), 18), ((11 / 41), 22), ((-55 / 41), 24), ((-15 / 41), 28), ((43 / 41), 30)],
      alternatingSixCyclotomicValue [((27 / 41), 0), ((-23 / 41), 2), ((-10 / 41), 6), ((9 / 41), 8), ((-6 / 41), 12), ((11 / 41), 18), ((23 / 41), 22), ((8 / 41), 24), ((-9 / 41), 28), ((-7 / 41), 30)]],
    ![alternatingSixCyclotomicValue [(1, 12)],
      alternatingSixCyclotomicValue [(-1, 8), (1, 28)],
      alternatingSixCyclotomicValue [((-49 / 41), 0), ((19 / 41), 2), ((-6 / 41), 6), ((52 / 41), 8), ((20 / 41), 12), ((-18 / 41), 18), ((-19 / 41), 22), ((-54 / 41), 24), ((-52 / 41), 28), ((-37 / 41), 30)],
      alternatingSixCyclotomicValue [((28 / 41), 0), ((-5 / 41), 2), ((21 / 41), 6), ((-18 / 41), 8), ((12 / 41), 12), ((22 / 41), 18), ((5 / 41), 22), ((25 / 41), 24), ((18 / 41), 28), ((27 / 41), 30)],
      alternatingSixCyclotomicValue [(-2, 0), (-1, 12)],
      alternatingSixCyclotomicValue [(1, 8), (-2, 24), (-1, 28)],
      alternatingSixCyclotomicValue [((-49 / 41), 0), ((-19 / 41), 2), ((6 / 41), 6), ((52 / 41), 8), ((20 / 41), 12), ((18 / 41), 18), ((19 / 41), 22), ((-54 / 41), 24), ((-52 / 41), 28), ((37 / 41), 30)],
      alternatingSixCyclotomicValue [((28 / 41), 0), ((5 / 41), 2), ((-21 / 41), 6), ((-18 / 41), 8), ((12 / 41), 12), ((-22 / 41), 18), ((-5 / 41), 22), ((25 / 41), 24), ((18 / 41), 28), ((-27 / 41), 30)]],
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

/-- Checked inverse of the row 17 eigenbasis. -/
def alternatingSixAmbientRow17EigenbasisInverse :
    Matrix (Fin 8) (Fin 8) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((1 / 8), 0), ((1 / 4), 8), ((-3 / 8), 12), ((-1 / 4), 24), ((-1 / 4), 28)],
      alternatingSixCyclotomicValue [((5 / 8), 0), ((-1 / 8), 8), ((-1 / 2), 12), ((1 / 2), 24), ((1 / 8), 28)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 8), ((3 / 8), 12), ((-1 / 8), 24), ((-1 / 4), 28)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-3 / 8), 8), ((-1 / 8), 12), ((1 / 8), 24), ((3 / 8), 28)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((-1 / 8), 8), ((-1 / 2), 12), ((3 / 8), 24), ((1 / 8), 28)],
      alternatingSixCyclotomicValue [((-3 / 8), 0), ((5 / 8), 8), ((1 / 4), 12), ((1 / 8), 24), ((-5 / 8), 28)],
      alternatingSixCyclotomicValue [((-1 / 8), 0), ((5 / 8), 8), ((-5 / 8), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 8), 8), (1, 12), ((-5 / 8), 24), ((-1 / 8), 28)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 8), ((1 / 2), 12), ((-3 / 8), 24), ((-1 / 2), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 8), ((5 / 8), 12), ((-1 / 2), 28)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((1 / 8), 8), ((-1 / 8), 12), ((1 / 8), 24), ((-1 / 8), 28)],
      alternatingSixCyclotomicValue [((-1 / 8), 0), ((1 / 4), 8), ((-3 / 8), 12), ((1 / 4), 24), ((-1 / 4), 28)],
      alternatingSixCyclotomicValue [((-5 / 8), 0), ((1 / 2), 8), ((3 / 8), 12), ((-1 / 8), 24), ((-1 / 2), 28)],
      alternatingSixCyclotomicValue [((-1 / 8), 0), ((-1 / 4), 8), ((5 / 8), 12), ((-3 / 8), 24), ((1 / 4), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 4), 8), ((7 / 8), 12), ((-1 / 2), 24), ((-1 / 4), 28)],
      alternatingSixCyclotomicValue [((11 / 8), 0), ((-3 / 8), 8), ((-3 / 4), 12), ((3 / 8), 28)]],
    ![alternatingSixCyclotomicValue [((1 / 8), 0), ((-1 / 8), 2), ((1 / 8), 6), ((-3 / 8), 8), ((1 / 8), 12), ((-1 / 4), 18), ((1 / 8), 22), ((3 / 8), 24), ((3 / 8), 28), ((-3 / 8), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-5 / 8), 2), ((3 / 8), 6), ((1 / 4), 8), ((1 / 4), 12), ((5 / 8), 22), ((-3 / 8), 24), ((-1 / 4), 28), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 2), ((3 / 8), 6), ((-1 / 8), 8), ((-1 / 4), 12), ((-1 / 4), 22), ((1 / 8), 28), ((1 / 8), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 2), ((-1 / 4), 6), ((1 / 4), 8), ((1 / 8), 12), ((5 / 8), 18), ((1 / 4), 22), ((-1 / 8), 24), ((-1 / 4), 28), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 8), 0), ((-3 / 8), 2), ((3 / 8), 6), ((1 / 8), 8), ((1 / 4), 12), ((-3 / 8), 18), ((3 / 8), 22), ((-1 / 4), 24), ((-1 / 8), 28), ((1 / 8), 30)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((7 / 8), 2), ((3 / 8), 6), ((-3 / 8), 8), ((-1 / 4), 12), ((-9 / 8), 18), ((-7 / 8), 22), ((3 / 8), 28), ((11 / 8), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((3 / 8), 2), ((3 / 8), 6), ((-1 / 2), 8), ((-1 / 4), 12), (-1, 18), ((-3 / 8), 22), ((1 / 8), 24), ((1 / 2), 28), ((3 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((1 / 2), 2), ((-5 / 8), 6), ((-3 / 8), 12), ((3 / 4), 18), ((-1 / 2), 22), ((1 / 4), 24)]],
    ![alternatingSixCyclotomicValue [((1 / 8), 2), ((1 / 8), 6), ((-3 / 8), 8), ((-1 / 4), 12), ((-1 / 8), 22), ((3 / 8), 28), ((3 / 8), 30)],
      alternatingSixCyclotomicValue [((3 / 8), 0), ((5 / 8), 2), ((-1 / 8), 6), ((-3 / 8), 8), ((-1 / 8), 12), ((-1 / 2), 18), ((-5 / 8), 22), ((1 / 8), 24), ((3 / 8), 28), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 8), 0), ((-1 / 2), 2), ((-3 / 8), 6), ((1 / 4), 8), ((1 / 4), 12), ((1 / 2), 22), ((-1 / 4), 24), ((-1 / 4), 28), ((-1 / 8), 30)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((-1 / 4), 2), ((-1 / 8), 8), ((1 / 8), 12), ((-1 / 8), 18), ((1 / 4), 22), ((1 / 8), 28), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((3 / 8), 0), ((1 / 8), 2), ((-3 / 8), 6), ((-1 / 4), 8), ((-1 / 8), 12), ((3 / 8), 18), ((-1 / 8), 22), ((1 / 4), 28), ((-1 / 8), 30)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((-1 / 8), 2), ((-5 / 8), 6), ((1 / 4), 8), ((-3 / 8), 12), ((7 / 8), 18), ((1 / 8), 22), ((-1 / 4), 28), ((-5 / 8), 30)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((-1 / 8), 2), ((-3 / 8), 6), ((1 / 8), 8), ((-3 / 8), 12), ((1 / 2), 18), ((1 / 8), 22), ((-1 / 8), 24), ((-1 / 8), 28)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 2), 2), ((1 / 8), 6), ((1 / 4), 8), ((3 / 8), 12), ((-1 / 4), 18), ((1 / 2), 22), ((1 / 8), 24), ((-1 / 4), 28), ((-1 / 2), 30)]],
    ![alternatingSixCyclotomicValue [((-3 / 8), 0), ((1 / 2), 8), ((1 / 8), 12), ((-1 / 2), 24), ((-1 / 2), 28)],
      alternatingSixCyclotomicValue [((-1 / 8), 0), ((-3 / 8), 8), ((1 / 4), 24), ((3 / 8), 28)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 8), 12), ((1 / 8), 24)],
      alternatingSixCyclotomicValue [((-1 / 8), 8), ((-1 / 8), 12), ((1 / 8), 24), ((1 / 8), 28)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((-1 / 8), 8), ((1 / 8), 24), ((1 / 8), 28)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((1 / 8), 8), ((1 / 4), 12), ((-1 / 8), 24), ((-1 / 8), 28)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((3 / 8), 8), ((1 / 2), 12), ((-1 / 4), 24), ((-3 / 8), 28)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 8), 8), ((-1 / 4), 12), ((1 / 8), 24), ((1 / 8), 28)]],
    ![alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 4), 8), ((3 / 8), 24), ((-1 / 4), 28)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 8), ((-3 / 8), 12), ((-1 / 4), 24), ((-1 / 4), 28)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((-5 / 8), 8), ((-3 / 8), 12), ((3 / 8), 24), ((5 / 8), 28)],
      alternatingSixCyclotomicValue [((-1 / 8), 0), ((1 / 8), 12), ((-1 / 4), 24)],
      alternatingSixCyclotomicValue [((-1 / 8), 0), ((-1 / 8), 12), ((1 / 8), 24)],
      alternatingSixCyclotomicValue [((-1 / 8), 0), ((-1 / 4), 8), ((1 / 8), 12), ((3 / 8), 24), ((1 / 4), 28)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 2), 8), ((-1 / 8), 12), ((3 / 4), 24), ((1 / 2), 28)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((-1 / 8), 8), ((-1 / 4), 24), ((1 / 8), 28)]],
    ![alternatingSixCyclotomicValue [((1 / 8), 0), ((1 / 8), 2), ((-1 / 8), 6), ((-3 / 8), 8), ((1 / 8), 12), ((1 / 4), 18), ((-1 / 8), 22), ((3 / 8), 24), ((3 / 8), 28), ((3 / 8), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((5 / 8), 2), ((-3 / 8), 6), ((1 / 4), 8), ((1 / 4), 12), ((-5 / 8), 22), ((-3 / 8), 24), ((-1 / 4), 28), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 2), ((-3 / 8), 6), ((-1 / 8), 8), ((-1 / 4), 12), ((1 / 4), 22), ((1 / 8), 28), ((-1 / 8), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 2), ((1 / 4), 6), ((1 / 4), 8), ((1 / 8), 12), ((-5 / 8), 18), ((-1 / 4), 22), ((-1 / 8), 24), ((-1 / 4), 28), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 8), 0), ((3 / 8), 2), ((-3 / 8), 6), ((1 / 8), 8), ((1 / 4), 12), ((3 / 8), 18), ((-3 / 8), 22), ((-1 / 4), 24), ((-1 / 8), 28), ((-1 / 8), 30)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((-7 / 8), 2), ((-3 / 8), 6), ((-3 / 8), 8), ((-1 / 4), 12), ((9 / 8), 18), ((7 / 8), 22), ((3 / 8), 28), ((-11 / 8), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-3 / 8), 2), ((-3 / 8), 6), ((-1 / 2), 8), ((-1 / 4), 12), (1, 18), ((3 / 8), 22), ((1 / 8), 24), ((1 / 2), 28), ((-3 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((-1 / 2), 2), ((5 / 8), 6), ((-3 / 8), 12), ((-3 / 4), 18), ((1 / 2), 22), ((1 / 4), 24)]],
    ![alternatingSixCyclotomicValue [((-1 / 8), 2), ((-1 / 8), 6), ((-3 / 8), 8), ((-1 / 4), 12), ((1 / 8), 22), ((3 / 8), 28), ((-3 / 8), 30)],
      alternatingSixCyclotomicValue [((3 / 8), 0), ((-5 / 8), 2), ((1 / 8), 6), ((-3 / 8), 8), ((-1 / 8), 12), ((1 / 2), 18), ((5 / 8), 22), ((1 / 8), 24), ((3 / 8), 28), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 8), 0), ((1 / 2), 2), ((3 / 8), 6), ((1 / 4), 8), ((1 / 4), 12), ((-1 / 2), 22), ((-1 / 4), 24), ((-1 / 4), 28), ((1 / 8), 30)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((1 / 4), 2), ((-1 / 8), 8), ((1 / 8), 12), ((1 / 8), 18), ((-1 / 4), 22), ((1 / 8), 28), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((3 / 8), 0), ((-1 / 8), 2), ((3 / 8), 6), ((-1 / 4), 8), ((-1 / 8), 12), ((-3 / 8), 18), ((1 / 8), 22), ((1 / 4), 28), ((1 / 8), 30)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((1 / 8), 2), ((5 / 8), 6), ((1 / 4), 8), ((-3 / 8), 12), ((-7 / 8), 18), ((-1 / 8), 22), ((-1 / 4), 28), ((5 / 8), 30)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((1 / 8), 2), ((3 / 8), 6), ((1 / 8), 8), ((-3 / 8), 12), ((-1 / 2), 18), ((-1 / 8), 22), ((-1 / 8), 24), ((-1 / 8), 28)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 2), 2), ((-1 / 8), 6), ((1 / 4), 8), ((3 / 8), 12), ((1 / 4), 18), ((-1 / 2), 22), ((1 / 8), 24), ((-1 / 4), 28), ((1 / 2), 30)]]
  ]

/-- The row 17 first generator in the checked diagonal basis. -/
def alternatingSixAmbientRow17TransformedGeneratorA :
    Matrix (Fin 8) (Fin 8) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((1 / 2), 8), ((1 / 4), 12), ((1 / 4), 24), ((-1 / 2), 28)],
      alternatingSixCyclotomicValue [((-1 / 4), 12), ((1 / 4), 24)],
      alternatingSixCyclotomicValue [((2 / 41), 0), ((11 / 82), 2), ((3 / 82), 6), ((15 / 82), 8), ((21 / 164), 12), ((9 / 82), 18), ((-11 / 82), 22), ((13 / 164), 24), ((-15 / 82), 28), ((-1 / 41), 30)],
      alternatingSixCyclotomicValue [((13 / 164), 0), ((-9 / 41), 2), ((-21 / 164), 6), ((-23 / 164), 8), ((-3 / 41), 12), ((-11 / 82), 18), ((9 / 41), 22), ((4 / 41), 24), ((23 / 164), 28), ((7 / 82), 30)],
      alternatingSixCyclotomicValue [((-6 / 11), 0), ((3 / 22), 8), ((-21 / 44), 12), ((-9 / 44), 24), ((-3 / 22), 28)],
      alternatingSixCyclotomicValue [((-3 / 22), 0), ((9 / 22), 8), ((3 / 44), 12), ((-27 / 44), 24), ((-9 / 22), 28)],
      alternatingSixCyclotomicValue [((2 / 41), 0), ((-11 / 82), 2), ((-3 / 82), 6), ((15 / 82), 8), ((21 / 164), 12), ((-9 / 82), 18), ((11 / 82), 22), ((13 / 164), 24), ((-15 / 82), 28), ((1 / 41), 30)],
      alternatingSixCyclotomicValue [((13 / 164), 0), ((9 / 41), 2), ((21 / 164), 6), ((-23 / 164), 8), ((-3 / 41), 12), ((11 / 82), 18), ((-9 / 41), 22), ((4 / 41), 24), ((23 / 164), 28), ((-7 / 82), 30)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 0), ((-3 / 4), 8), ((1 / 2), 12), ((-1 / 4), 24), ((3 / 4), 28)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 8), ((-1 / 4), 24), ((1 / 4), 28)],
      alternatingSixCyclotomicValue [((-1 / 82), 0), ((-27 / 41), 2), ((-63 / 164), 6), ((-55 / 82), 8), ((-77 / 164), 12), ((4 / 41), 18), ((27 / 41), 22), ((12 / 41), 24), ((55 / 82), 28), ((-10 / 41), 30)],
      alternatingSixCyclotomicValue [((-17 / 82), 0), ((9 / 164), 2), ((-5 / 164), 6), ((4 / 41), 8), ((-19 / 82), 12), ((13 / 82), 18), ((-9 / 164), 22), ((-1 / 41), 24), ((-4 / 41), 28), ((-6 / 41), 30)],
      alternatingSixCyclotomicValue [((-63 / 44), 0), ((57 / 44), 8), ((12 / 11), 12), ((-69 / 44), 24), ((-57 / 44), 28)],
      alternatingSixCyclotomicValue [((9 / 44), 0), ((39 / 44), 8), ((3 / 11), 12), ((-9 / 44), 24), ((-39 / 44), 28)],
      alternatingSixCyclotomicValue [((-1 / 82), 0), ((27 / 41), 2), ((63 / 164), 6), ((-55 / 82), 8), ((-77 / 164), 12), ((-4 / 41), 18), ((-27 / 41), 22), ((12 / 41), 24), ((55 / 82), 28), ((10 / 41), 30)],
      alternatingSixCyclotomicValue [((-17 / 82), 0), ((-9 / 164), 2), ((5 / 164), 6), ((4 / 41), 8), ((-19 / 82), 12), ((-13 / 82), 18), ((9 / 164), 22), ((-1 / 41), 24), ((-4 / 41), 28), ((6 / 41), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 8), ((1 / 4), 12), ((1 / 4), 18), ((-1 / 4), 24), ((1 / 4), 28)],
      alternatingSixCyclotomicValue [((-1 / 4), 2), ((1 / 4), 22), ((-1 / 4), 24)],
      alternatingSixCyclotomicValue [((-9 / 82), 0), ((3 / 41), 2), ((-17 / 82), 6), ((35 / 164), 8), ((45 / 164), 12), ((21 / 164), 18), ((-3 / 41), 22), ((-19 / 164), 24), ((-35 / 164), 28), ((-8 / 41), 30)],
      alternatingSixCyclotomicValue [((63 / 164), 0), ((81 / 164), 2), ((37 / 164), 6), ((-61 / 164), 8), ((-55 / 164), 12), ((-3 / 41), 18), ((-81 / 164), 22), ((23 / 82), 24), ((61 / 164), 28), ((15 / 82), 30)],
      alternatingSixCyclotomicValue [((1 / 22), 0), ((-1 / 11), 2), ((-5 / 22), 6), ((-17 / 44), 8), ((21 / 44), 12), ((7 / 44), 18), ((1 / 11), 22), ((-13 / 44), 24), ((17 / 44), 28), ((-5 / 11), 30)],
      alternatingSixCyclotomicValue [((3 / 22), 0), ((-1 / 44), 2), ((7 / 22), 6), ((1 / 11), 8), ((-7 / 22), 12), ((-3 / 11), 18), ((1 / 44), 22), ((5 / 44), 24), ((-1 / 11), 28), ((3 / 22), 30)],
      alternatingSixCyclotomicValue [((-10 / 41), 0), ((-34 / 41), 2), ((-13 / 41), 6), ((137 / 164), 8), ((59 / 164), 12), ((49 / 164), 18), ((34 / 41), 22), ((-65 / 164), 24), ((-137 / 164), 28), ((-5 / 41), 30)],
      alternatingSixCyclotomicValue [((99 / 164), 0), ((107 / 164), 2), ((-23 / 164), 6), ((-131 / 164), 8), ((-63 / 164), 12), ((-7 / 41), 18), ((-107 / 164), 22), ((21 / 41), 24), ((131 / 164), 28), ((-3 / 41), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 2), ((-1 / 4), 6), ((1 / 4), 12), ((1 / 2), 22), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 2), ((1 / 4), 6), ((-1 / 4), 8), ((-1 / 4), 18), ((-1 / 4), 22), ((1 / 4), 28)],
      alternatingSixCyclotomicValue [((-11 / 164), 0), ((31 / 82), 2), ((21 / 41), 6), ((51 / 164), 8), ((12 / 41), 12), ((3 / 82), 18), ((-31 / 82), 22), ((-23 / 164), 24), ((-51 / 164), 28), ((13 / 82), 30)],
      alternatingSixCyclotomicValue [((-23 / 164), 0), ((-3 / 41), 2), ((17 / 82), 6), ((3 / 82), 8), ((-1 / 41), 12), ((-21 / 164), 18), ((3 / 41), 22), ((19 / 164), 24), ((-3 / 82), 28), ((8 / 41), 30)],
      alternatingSixCyclotomicValue [((-9 / 22), 0), ((1 / 11), 2), ((-23 / 44), 6), ((5 / 22), 8), ((31 / 44), 12), ((1 / 11), 18), ((-1 / 11), 22), ((-13 / 22), 24), ((-5 / 22), 28), ((-1 / 22), 30)],
      alternatingSixCyclotomicValue [((3 / 11), 0), ((1 / 44), 2), ((19 / 44), 6), ((-3 / 44), 8), ((-3 / 22), 12), ((-21 / 44), 18), ((-1 / 44), 22), ((5 / 22), 24), ((3 / 44), 28), ((-3 / 22), 30)],
      alternatingSixCyclotomicValue [((61 / 164), 0), ((17 / 41), 2), ((13 / 82), 6), ((-89 / 164), 8), ((-25 / 82), 12), ((-43 / 82), 18), ((-17 / 41), 22), ((53 / 164), 24), ((89 / 164), 28), ((5 / 82), 30)],
      alternatingSixCyclotomicValue [((-29 / 164), 0), ((2 / 41), 2), ((8 / 41), 6), ((1 / 41), 8), ((-15 / 82), 12), ((-27 / 164), 18), ((-2 / 41), 22), ((-1 / 164), 24), ((-1 / 41), 28), ((3 / 82), 30)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 12), ((1 / 4), 24)],
      alternatingSixCyclotomicValue [((1 / 4), 12), ((1 / 4), 24)],
      alternatingSixCyclotomicValue [((-13 / 82), 0), ((-5 / 82), 2), ((-10 / 41), 6), ((23 / 82), 8), ((-17 / 164), 12), ((-19 / 82), 18), ((5 / 82), 22), ((-73 / 164), 24), ((-23 / 82), 28), ((-7 / 41), 30)],
      alternatingSixCyclotomicValue [((9 / 164), 0), ((-3 / 82), 2), ((17 / 164), 6), ((3 / 164), 8), ((-1 / 82), 12), ((5 / 82), 18), ((3 / 82), 22), ((15 / 82), 24), ((-3 / 164), 28), ((4 / 41), 30)],
      alternatingSixCyclotomicValue [((-1 / 11), 0), ((3 / 11), 8), ((-9 / 44), 12), ((-29 / 44), 24), ((-3 / 11), 28)],
      alternatingSixCyclotomicValue [((5 / 22), 0), ((7 / 22), 8), ((17 / 44), 12), ((1 / 44), 24), ((-7 / 22), 28)],
      alternatingSixCyclotomicValue [((-13 / 82), 0), ((5 / 82), 2), ((10 / 41), 6), ((23 / 82), 8), ((-17 / 164), 12), ((19 / 82), 18), ((-5 / 82), 22), ((-73 / 164), 24), ((-23 / 82), 28), ((7 / 41), 30)],
      alternatingSixCyclotomicValue [((9 / 164), 0), ((3 / 82), 2), ((-17 / 164), 6), ((3 / 164), 8), ((-1 / 82), 12), ((-5 / 82), 18), ((-3 / 82), 22), ((15 / 82), 24), ((-3 / 164), 28), ((-4 / 41), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 8), ((1 / 4), 24), ((1 / 4), 28)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 8), ((1 / 4), 24), ((1 / 4), 28)],
      alternatingSixCyclotomicValue [((13 / 41), 0), ((51 / 82), 2), ((121 / 164), 6), ((18 / 41), 8), ((75 / 164), 12), ((-22 / 41), 18), ((-51 / 82), 22), ((-9 / 82), 24), ((-18 / 41), 28), ((14 / 41), 30)],
      alternatingSixCyclotomicValue [((-9 / 82), 0), ((-29 / 164), 2), ((7 / 164), 6), ((-3 / 82), 8), ((1 / 41), 12), ((-5 / 41), 18), ((29 / 164), 22), ((11 / 82), 24), ((3 / 82), 28), ((25 / 82), 30)],
      alternatingSixCyclotomicValue [((27 / 44), 0), ((7 / 44), 8), ((7 / 22), 12), ((17 / 44), 24), ((-7 / 44), 28)],
      alternatingSixCyclotomicValue [((15 / 44), 0), ((-45 / 44), 8), ((-6 / 11), 12), ((29 / 44), 24), ((45 / 44), 28)],
      alternatingSixCyclotomicValue [((13 / 41), 0), ((-51 / 82), 2), ((-121 / 164), 6), ((18 / 41), 8), ((75 / 164), 12), ((22 / 41), 18), ((51 / 82), 22), ((-9 / 82), 24), ((-18 / 41), 28), ((-14 / 41), 30)],
      alternatingSixCyclotomicValue [((-9 / 82), 0), ((29 / 164), 2), ((-7 / 164), 6), ((-3 / 82), 8), ((1 / 41), 12), ((5 / 41), 18), ((-29 / 164), 22), ((11 / 82), 24), ((3 / 82), 28), ((-25 / 82), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 8), ((1 / 4), 12), ((-1 / 4), 18), ((-1 / 4), 24), ((1 / 4), 28)],
      alternatingSixCyclotomicValue [((1 / 4), 2), ((-1 / 4), 22), ((-1 / 4), 24)],
      alternatingSixCyclotomicValue [((-10 / 41), 0), ((34 / 41), 2), ((13 / 41), 6), ((137 / 164), 8), ((59 / 164), 12), ((-49 / 164), 18), ((-34 / 41), 22), ((-65 / 164), 24), ((-137 / 164), 28), ((5 / 41), 30)],
      alternatingSixCyclotomicValue [((99 / 164), 0), ((-107 / 164), 2), ((23 / 164), 6), ((-131 / 164), 8), ((-63 / 164), 12), ((7 / 41), 18), ((107 / 164), 22), ((21 / 41), 24), ((131 / 164), 28), ((3 / 41), 30)],
      alternatingSixCyclotomicValue [((1 / 22), 0), ((1 / 11), 2), ((5 / 22), 6), ((-17 / 44), 8), ((21 / 44), 12), ((-7 / 44), 18), ((-1 / 11), 22), ((-13 / 44), 24), ((17 / 44), 28), ((5 / 11), 30)],
      alternatingSixCyclotomicValue [((3 / 22), 0), ((1 / 44), 2), ((-7 / 22), 6), ((1 / 11), 8), ((-7 / 22), 12), ((3 / 11), 18), ((-1 / 44), 22), ((5 / 44), 24), ((-1 / 11), 28), ((-3 / 22), 30)],
      alternatingSixCyclotomicValue [((-9 / 82), 0), ((-3 / 41), 2), ((17 / 82), 6), ((35 / 164), 8), ((45 / 164), 12), ((-21 / 164), 18), ((3 / 41), 22), ((-19 / 164), 24), ((-35 / 164), 28), ((8 / 41), 30)],
      alternatingSixCyclotomicValue [((63 / 164), 0), ((-81 / 164), 2), ((-37 / 164), 6), ((-61 / 164), 8), ((-55 / 164), 12), ((3 / 41), 18), ((81 / 164), 22), ((23 / 82), 24), ((61 / 164), 28), ((-15 / 82), 30)]],
    ![alternatingSixCyclotomicValue [((1 / 2), 2), ((1 / 4), 6), ((1 / 4), 12), ((-1 / 2), 22), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 2), ((-1 / 4), 6), ((-1 / 4), 8), ((1 / 4), 18), ((1 / 4), 22), ((1 / 4), 28)],
      alternatingSixCyclotomicValue [((61 / 164), 0), ((-17 / 41), 2), ((-13 / 82), 6), ((-89 / 164), 8), ((-25 / 82), 12), ((43 / 82), 18), ((17 / 41), 22), ((53 / 164), 24), ((89 / 164), 28), ((-5 / 82), 30)],
      alternatingSixCyclotomicValue [((-29 / 164), 0), ((-2 / 41), 2), ((-8 / 41), 6), ((1 / 41), 8), ((-15 / 82), 12), ((27 / 164), 18), ((2 / 41), 22), ((-1 / 164), 24), ((-1 / 41), 28), ((-3 / 82), 30)],
      alternatingSixCyclotomicValue [((-9 / 22), 0), ((-1 / 11), 2), ((23 / 44), 6), ((5 / 22), 8), ((31 / 44), 12), ((-1 / 11), 18), ((1 / 11), 22), ((-13 / 22), 24), ((-5 / 22), 28), ((1 / 22), 30)],
      alternatingSixCyclotomicValue [((3 / 11), 0), ((-1 / 44), 2), ((-19 / 44), 6), ((-3 / 44), 8), ((-3 / 22), 12), ((21 / 44), 18), ((1 / 44), 22), ((5 / 22), 24), ((3 / 44), 28), ((3 / 22), 30)],
      alternatingSixCyclotomicValue [((-11 / 164), 0), ((-31 / 82), 2), ((-21 / 41), 6), ((51 / 164), 8), ((12 / 41), 12), ((-3 / 82), 18), ((31 / 82), 22), ((-23 / 164), 24), ((-51 / 164), 28), ((-13 / 82), 30)],
      alternatingSixCyclotomicValue [((-23 / 164), 0), ((3 / 41), 2), ((-17 / 82), 6), ((3 / 82), 8), ((-1 / 41), 12), ((21 / 164), 18), ((-3 / 41), 22), ((19 / 164), 24), ((-3 / 82), 28), ((-8 / 41), 30)]]
  ]

macro "close_cyclotomic_row17" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)


private theorem row17_eigenbasisInverse_mul_0_0 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        0 0 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        0 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 + ((3 / 4) : ℂ) * ζ ^ 8 - ((5 / 4) : ℂ) * ζ ^ 12 + ζ ^ 16 - ((3 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24)
private theorem row17_eigenbasisInverse_mul_0_1 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        0 1 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        0 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((1 / 8) : ℂ) + ((1 / 8) : ℂ) * ζ ^ 4 - ((3 / 8) : ℂ) * ζ ^ 8 + ((1 / 8) : ℂ) * ζ ^ 12 - ((3 / 8) : ℂ) * ζ ^ 16 + ((7 / 8) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24)
private theorem row17_eigenbasisInverse_mul_0_2 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        0 2 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        0 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((9 / 82) : ℂ) - ((35 / 82) : ℂ) * ζ ^ 2 + ((9 / 82) : ℂ) * ζ ^ 4 - ((5 / 164) : ℂ) * ζ ^ 6 - ((379 / 328) : ℂ) * ζ ^ 8 + ((299 / 328) : ℂ) * ζ ^ 10 + ((509 / 328) : ℂ) * ζ ^ 12 - ((111 / 164) : ℂ) * ζ ^ 14 + ((23 / 328) : ℂ) * ζ ^ 16 + ((581 / 328) : ℂ) * ζ ^ 18 - ((89 / 328) : ℂ) * ζ ^ 20 - ((73 / 82) : ℂ) * ζ ^ 22 + ((133 / 82) : ℂ) * ζ ^ 24 + ((28 / 41) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_0_3 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        0 3 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        0 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((79 / 328) : ℂ) + ((10 / 41) : ℂ) * ζ ^ 2 + ((79 / 328) : ℂ) * ζ ^ 4 - ((11 / 41) : ℂ) * ζ ^ 6 - ((129 / 328) : ℂ) * ζ ^ 8 + ((61 / 164) : ℂ) * ζ ^ 10 - ((39 / 328) : ℂ) * ζ ^ 12 - ((21 / 82) : ℂ) * ζ ^ 14 + ((63 / 328) : ℂ) * ζ ^ 16 - ((21 / 41) : ℂ) * ζ ^ 18 + ((43 / 164) : ℂ) * ζ ^ 20 + ((101 / 164) : ℂ) * ζ ^ 22 + ((3 / 41) : ℂ) * ζ ^ 24 - ((105 / 164) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_0_4 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        0 4 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        0 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((19 / 44) : ℂ) - ((19 / 44) : ℂ) * ζ ^ 4 + ((13 / 11) : ℂ) * ζ ^ 8 - ((18 / 11) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 16 - ((16 / 11) : ℂ) * ζ ^ 20 - ((61 / 44) : ℂ) * ζ ^ 24)
private theorem row17_eigenbasisInverse_mul_0_5 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        0 5 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        0 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((95 / 88) : ℂ) + ((95 / 88) : ℂ) * ζ ^ 4 - ((73 / 88) : ℂ) * ζ ^ 8 + ((107 / 88) : ℂ) * ζ ^ 12 - ((15 / 8) : ℂ) * ζ ^ 16 + ((67 / 88) : ℂ) * ζ ^ 20 - ((29 / 44) : ℂ) * ζ ^ 24)
private theorem row17_eigenbasisInverse_mul_0_6 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        0 6 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        0 6 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((9 / 82) : ℂ) + ((35 / 82) : ℂ) * ζ ^ 2 + ((9 / 82) : ℂ) * ζ ^ 4 + ((5 / 164) : ℂ) * ζ ^ 6 - ((379 / 328) : ℂ) * ζ ^ 8 - ((299 / 328) : ℂ) * ζ ^ 10 + ((509 / 328) : ℂ) * ζ ^ 12 + ((111 / 164) : ℂ) * ζ ^ 14 + ((23 / 328) : ℂ) * ζ ^ 16 - ((581 / 328) : ℂ) * ζ ^ 18 - ((89 / 328) : ℂ) * ζ ^ 20 + ((73 / 82) : ℂ) * ζ ^ 22 + ((133 / 82) : ℂ) * ζ ^ 24 - ((28 / 41) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_0_7 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        0 7 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        0 7 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((79 / 328) : ℂ) - ((10 / 41) : ℂ) * ζ ^ 2 + ((79 / 328) : ℂ) * ζ ^ 4 + ((11 / 41) : ℂ) * ζ ^ 6 - ((129 / 328) : ℂ) * ζ ^ 8 - ((61 / 164) : ℂ) * ζ ^ 10 - ((39 / 328) : ℂ) * ζ ^ 12 + ((21 / 82) : ℂ) * ζ ^ 14 + ((63 / 328) : ℂ) * ζ ^ 16 + ((21 / 41) : ℂ) * ζ ^ 18 + ((43 / 164) : ℂ) * ζ ^ 20 - ((101 / 164) : ℂ) * ζ ^ 22 + ((3 / 41) : ℂ) * ζ ^ 24 + ((105 / 164) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_1_0 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        1 0 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        1 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((1 / 8) : ℂ) - ((1 / 8) : ℂ) * ζ ^ 4 - ζ ^ 8 + ((5 / 8) : ℂ) * ζ ^ 12 + ((3 / 8) : ℂ) * ζ ^ 16 - ((1 / 8) : ℂ) * ζ ^ 20 + ζ ^ 24)
private theorem row17_eigenbasisInverse_mul_1_1 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        1 1 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        1 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((3 / 8) : ℂ) + ((3 / 8) : ℂ) * ζ ^ 4 + ((3 / 4) : ℂ) * ζ ^ 8 - ((3 / 2) : ℂ) * ζ ^ 12 + ((9 / 8) : ℂ) * ζ ^ 16 - ((11 / 8) : ℂ) * ζ ^ 20 - ((3 / 8) : ℂ) * ζ ^ 24)
private theorem row17_eigenbasisInverse_mul_1_2 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        1 2 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        1 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((273 / 328) : ℂ) - ((9 / 164) : ℂ) * ζ ^ 2 - ((273 / 328) : ℂ) * ζ ^ 4 + ((219 / 164) : ℂ) * ζ ^ 6 - ((89 / 328) : ℂ) * ζ ^ 8 - ((505 / 328) : ℂ) * ζ ^ 10 + ((29 / 82) : ℂ) * ζ ^ 12 + ((543 / 328) : ℂ) * ζ ^ 14 - ((103 / 328) : ℂ) * ζ ^ 16 - ((17 / 82) : ℂ) * ζ ^ 18 + ((277 / 164) : ℂ) * ζ ^ 20 + ((1 / 328) : ℂ) * ζ ^ 22 + ((13 / 328) : ℂ) * ζ ^ 24 + ((245 / 328) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_1_3 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        1 3 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        1 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((43 / 82) : ℂ) - ((265 / 328) : ℂ) * ζ ^ 2 - ((43 / 82) : ℂ) * ζ ^ 4 + ((33 / 164) : ℂ) * ζ ^ 6 + ((125 / 164) : ℂ) * ζ ^ 8 + ((189 / 328) : ℂ) * ζ ^ 10 + ((127 / 328) : ℂ) * ζ ^ 12 - ((117 / 328) : ℂ) * ζ ^ 14 - ((111 / 328) : ℂ) * ζ ^ 16 + ((40 / 41) : ℂ) * ζ ^ 18 + ((29 / 328) : ℂ) * ζ ^ 20 - ((65 / 328) : ℂ) * ζ ^ 22 + ((2 / 41) : ℂ) * ζ ^ 24 - ((99 / 328) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_1_4 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        1 4 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        1 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((5 / 8) : ℂ) - ((5 / 8) : ℂ) * ζ ^ 4 + ((43 / 44) : ℂ) * ζ ^ 8 - ((39 / 88) : ℂ) * ζ ^ 12 + ((1 / 88) : ℂ) * ζ ^ 16 - ((3 / 8) : ℂ) * ζ ^ 20 - ((19 / 44) : ℂ) * ζ ^ 24)
private theorem row17_eigenbasisInverse_mul_1_5 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        1 5 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        1 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((11 / 8) : ℂ) - ((11 / 8) : ℂ) * ζ ^ 4 + ((19 / 44) : ℂ) * ζ ^ 8 - ((9 / 44) : ℂ) * ζ ^ 12 + ((3 / 88) : ℂ) * ζ ^ 16 + ((5 / 8) : ℂ) * ζ ^ 20 - ((15 / 88) : ℂ) * ζ ^ 24)
private theorem row17_eigenbasisInverse_mul_1_6 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        1 6 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        1 6 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((273 / 328) : ℂ) + ((9 / 164) : ℂ) * ζ ^ 2 - ((273 / 328) : ℂ) * ζ ^ 4 - ((219 / 164) : ℂ) * ζ ^ 6 - ((89 / 328) : ℂ) * ζ ^ 8 + ((505 / 328) : ℂ) * ζ ^ 10 + ((29 / 82) : ℂ) * ζ ^ 12 - ((543 / 328) : ℂ) * ζ ^ 14 - ((103 / 328) : ℂ) * ζ ^ 16 + ((17 / 82) : ℂ) * ζ ^ 18 + ((277 / 164) : ℂ) * ζ ^ 20 - ((1 / 328) : ℂ) * ζ ^ 22 + ((13 / 328) : ℂ) * ζ ^ 24 - ((245 / 328) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_1_7 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        1 7 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        1 7 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((43 / 82) : ℂ) + ((265 / 328) : ℂ) * ζ ^ 2 - ((43 / 82) : ℂ) * ζ ^ 4 - ((33 / 164) : ℂ) * ζ ^ 6 + ((125 / 164) : ℂ) * ζ ^ 8 - ((189 / 328) : ℂ) * ζ ^ 10 + ((127 / 328) : ℂ) * ζ ^ 12 + ((117 / 328) : ℂ) * ζ ^ 14 - ((111 / 328) : ℂ) * ζ ^ 16 - ((40 / 41) : ℂ) * ζ ^ 18 + ((29 / 328) : ℂ) * ζ ^ 20 + ((65 / 328) : ℂ) * ζ ^ 22 + ((2 / 41) : ℂ) * ζ ^ 24 + ((99 / 328) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_2_0 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        2 0 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        2 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((5 / 8) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 2 - ((5 / 8) : ℂ) * ζ ^ 4 - ((5 / 4) : ℂ) * ζ ^ 6 - ((5 / 8) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 + ((3 / 4) : ℂ) * ζ ^ 12 + ((7 / 4) : ℂ) * ζ ^ 14 - ((3 / 8) : ℂ) * ζ ^ 16 - ((11 / 8) : ℂ) * ζ ^ 18 + ((3 / 8) : ℂ) * ζ ^ 22 + ((3 / 8) : ℂ) * ζ ^ 24 + ((1 / 8) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_2_1 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        2 1 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        2 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((1 / 4) : ℂ) - ((1 / 8) : ℂ) * ζ ^ 2 - ((1 / 4) : ℂ) * ζ ^ 4 - ζ ^ 6 + ((3 / 4) : ℂ) * ζ ^ 10 + ((1 / 8) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 16 + ((11 / 8) : ℂ) * ζ ^ 18 - ((3 / 8) : ℂ) * ζ ^ 20 - ((13 / 8) : ℂ) * ζ ^ 22 + ((3 / 8) : ℂ) * ζ ^ 24 + ((3 / 8) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_2_2 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        2 2 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        2 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((179 / 328) : ℂ) - ((33 / 164) : ℂ) * ζ ^ 2 + ((339 / 328) : ℂ) * ζ ^ 4 - ((119 / 164) : ℂ) * ζ ^ 6 + ((225 / 164) : ℂ) * ζ ^ 8 + ((559 / 328) : ℂ) * ζ ^ 10 - ((695 / 328) : ℂ) * ζ ^ 12 + ((11 / 164) : ℂ) * ζ ^ 14 + ((69 / 41) : ℂ) * ζ ^ 16 + ((5 / 41) : ℂ) * ζ ^ 18 - ((825 / 328) : ℂ) * ζ ^ 20 + ((281 / 328) : ℂ) * ζ ^ 22 + ((35 / 328) : ℂ) * ζ ^ 24 - ((1001 / 328) : ℂ) * ζ ^ 26 - ((169 / 164) : ℂ) * ζ ^ 28)
private theorem row17_eigenbasisInverse_mul_2_3 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        2 3 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        2 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((9 / 328) : ℂ) + ((67 / 328) : ℂ) * ζ ^ 2 - ((141 / 328) : ℂ) * ζ ^ 4 - ((69 / 328) : ℂ) * ζ ^ 6 + ((217 / 164) : ℂ) * ζ ^ 8 + ((73 / 328) : ℂ) * ζ ^ 10 - ((171 / 328) : ℂ) * ζ ^ 12 + ((169 / 328) : ℂ) * ζ ^ 14 - ((87 / 328) : ℂ) * ζ ^ 16 - ((99 / 328) : ℂ) * ζ ^ 18 + ((161 / 328) : ℂ) * ζ ^ 20 + ((103 / 328) : ℂ) * ζ ^ 22 - ((87 / 82) : ℂ) * ζ ^ 24 + ((163 / 164) : ℂ) * ζ ^ 26 + ((30 / 41) : ℂ) * ζ ^ 28)
private theorem row17_eigenbasisInverse_mul_2_4 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        2 4 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        2 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((15 / 88) : ℂ) + ((1 / 44) : ℂ) * ζ ^ 2 - ((15 / 88) : ℂ) * ζ ^ 4 + ((2 / 11) : ℂ) * ζ ^ 6 - ((27 / 88) : ℂ) * ζ ^ 8 - ((3 / 2) : ℂ) * ζ ^ 10 + ((5 / 4) : ℂ) * ζ ^ 12 - ((21 / 44) : ℂ) * ζ ^ 14 - ((9 / 88) : ℂ) * ζ ^ 16 - ((95 / 88) : ℂ) * ζ ^ 18 + ((21 / 22) : ℂ) * ζ ^ 20 - ((21 / 88) : ℂ) * ζ ^ 22 + ((101 / 88) : ℂ) * ζ ^ 24 + ((79 / 88) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_2_5 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        2 5 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        2 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((7 / 11) : ℂ) + ((17 / 88) : ℂ) * ζ ^ 2 - ((7 / 11) : ℂ) * ζ ^ 4 - ((75 / 44) : ℂ) * ζ ^ 6 + ((9 / 44) : ℂ) * ζ ^ 8 + ((7 / 4) : ℂ) * ζ ^ 10 - ((1 / 8) : ℂ) * ζ ^ 12 - ((24 / 11) : ℂ) * ζ ^ 14 + ((47 / 44) : ℂ) * ζ ^ 16 + ((177 / 88) : ℂ) * ζ ^ 18 - ((23 / 88) : ℂ) * ζ ^ 20 - ((173 / 88) : ℂ) * ζ ^ 22 + ((83 / 88) : ℂ) * ζ ^ 24 - ((93 / 88) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_2_6 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        2 6 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        2 6 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((149 / 328) : ℂ) - ((43 / 164) : ℂ) * ζ ^ 2 - ((309 / 328) : ℂ) * ζ ^ 4 - ((27 / 41) : ℂ) * ζ ^ 6 - ((22 / 41) : ℂ) * ζ ^ 8 + ((719 / 328) : ℂ) * ζ ^ 10 + ((119 / 328) : ℂ) * ζ ^ 12 + ((19 / 164) : ℂ) * ζ ^ 14 - ((291 / 164) : ℂ) * ζ ^ 16 + ((66 / 41) : ℂ) * ζ ^ 18 + ((693 / 328) : ℂ) * ζ ^ 20 - ((25 / 328) : ℂ) * ζ ^ 22 - ((641 / 328) : ℂ) * ζ ^ 24 - ((625 / 328) : ℂ) * ζ ^ 26 + ((169 / 164) : ℂ) * ζ ^ 28)
private theorem row17_eigenbasisInverse_mul_2_7 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        2 7 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        2 7 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((9 / 328) : ℂ) + ((55 / 328) : ℂ) * ζ ^ 2 + ((159 / 328) : ℂ) * ζ ^ 4 - ((105 / 328) : ℂ) * ζ ^ 6 - ((51 / 82) : ℂ) * ζ ^ 8 + ((251 / 328) : ℂ) * ζ ^ 10 + ((55 / 328) : ℂ) * ζ ^ 12 + ((31 / 328) : ℂ) * ζ ^ 14 - ((13 / 328) : ℂ) * ζ ^ 16 - ((167 / 328) : ℂ) * ζ ^ 18 - ((273 / 328) : ℂ) * ζ ^ 20 + ((313 / 328) : ℂ) * ζ ^ 22 + ((33 / 82) : ℂ) * ζ ^ 24 - ((3 / 164) : ℂ) * ζ ^ 26 - ((30 / 41) : ℂ) * ζ ^ 28)
private theorem row17_eigenbasisInverse_mul_3_0 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        3 0 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        3 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 + ζ ^ 6 + ((3 / 8) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 10 - ((5 / 8) : ℂ) * ζ ^ 12 - ((3 / 4) : ℂ) * ζ ^ 14 - ((1 / 8) : ℂ) * ζ ^ 18 + ((1 / 8) : ℂ) * ζ ^ 20 + ((7 / 8) : ℂ) * ζ ^ 22 - ((5 / 8) : ℂ) * ζ ^ 24 - ((3 / 8) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_3_1 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        3 1 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        3 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((1 / 8) : ℂ) * ζ ^ 2 + ((3 / 4) : ℂ) * ζ ^ 6 - ((7 / 8) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 16 - ((11 / 8) : ℂ) * ζ ^ 18 + ((7 / 8) : ℂ) * ζ ^ 20 + ((9 / 8) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((3 / 8) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_3_2 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        3 2 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        3 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((29 / 82) : ℂ) - ((3 / 164) : ℂ) * ζ ^ 2 + ((145 / 164) : ℂ) * ζ ^ 4 + ((25 / 82) : ℂ) * ζ ^ 6 - ((51 / 41) : ℂ) * ζ ^ 8 + ((49 / 328) : ℂ) * ζ ^ 10 + ((5 / 4) : ℂ) * ζ ^ 12 - ((325 / 328) : ℂ) * ζ ^ 14 - ((27 / 82) : ℂ) * ζ ^ 16 + ((27 / 328) : ℂ) * ζ ^ 18 - ((53 / 164) : ℂ) * ζ ^ 20 + ((61 / 164) : ℂ) * ζ ^ 22 - ((7 / 82) : ℂ) * ζ ^ 24 - ((4 / 41) : ℂ) * ζ ^ 26 + ((39 / 82) : ℂ) * ζ ^ 28)
private theorem row17_eigenbasisInverse_mul_3_3 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        3 3 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        3 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((21 / 41) : ℂ) + ((18 / 41) : ℂ) * ζ ^ 2 + ((32 / 41) : ℂ) * ζ ^ 4 - ((227 / 328) : ℂ) * ζ ^ 6 - ((335 / 328) : ℂ) * ζ ^ 8 - ((24 / 41) : ℂ) * ζ ^ 10 - ((3 / 8) : ℂ) * ζ ^ 12 + ((23 / 82) : ℂ) * ζ ^ 14 + ((255 / 328) : ℂ) * ζ ^ 16 - ((279 / 328) : ℂ) * ζ ^ 18 - ((81 / 164) : ℂ) * ζ ^ 20 - ((35 / 82) : ℂ) * ζ ^ 22 + ((49 / 164) : ℂ) * ζ ^ 24 + ((71 / 328) : ℂ) * ζ ^ 26 - ((27 / 164) : ℂ) * ζ ^ 28)
private theorem row17_eigenbasisInverse_mul_3_4 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        3 4 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        3 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((23 / 22) : ℂ) - ((15 / 11) : ℂ) * ζ ^ 2 + ((23 / 22) : ℂ) * ζ ^ 4 + ((79 / 44) : ℂ) * ζ ^ 6 + ((9 / 88) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 10 - ((63 / 88) : ℂ) * ζ ^ 12 + ((43 / 44) : ℂ) * ζ ^ 14 - ((3 / 44) : ℂ) * ζ ^ 16 + ((91 / 88) : ℂ) * ζ ^ 18 - ((7 / 8) : ℂ) * ζ ^ 20 + ((71 / 88) : ℂ) * ζ ^ 22 - ((69 / 88) : ℂ) * ζ ^ 24 - ((45 / 88) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_3_5 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        3 5 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        3 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((3 / 22) : ℂ) + ((25 / 88) : ℂ) * ζ ^ 2 + ((3 / 22) : ℂ) * ζ ^ 4 + ((7 / 11) : ℂ) * ζ ^ 6 + ((49 / 88) : ℂ) * ζ ^ 8 - ((19 / 22) : ℂ) * ζ ^ 10 - ((3 / 11) : ℂ) * ζ ^ 12 + ((19 / 44) : ℂ) * ζ ^ 14 + ((6 / 11) : ℂ) * ζ ^ 16 - ((13 / 88) : ℂ) * ζ ^ 18 - ((1 / 8) : ℂ) * ζ ^ 20 - ((7 / 88) : ℂ) * ζ ^ 22 + ((3 / 11) : ℂ) * ζ ^ 24 + ((129 / 88) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_3_6 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        3 6 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        3 6 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((29 / 82) : ℂ) - ((53 / 164) : ℂ) * ζ ^ 2 - ((29 / 164) : ℂ) * ζ ^ 4 + ((269 / 164) : ℂ) * ζ ^ 6 + ((283 / 164) : ℂ) * ζ ^ 8 - ((15 / 8) : ℂ) * ζ ^ 10 - ((66 / 41) : ℂ) * ζ ^ 12 - ((187 / 328) : ℂ) * ζ ^ 14 + ((241 / 164) : ℂ) * ζ ^ 16 + ((37 / 328) : ℂ) * ζ ^ 18 - ((24 / 41) : ℂ) * ζ ^ 20 - ((57 / 164) : ℂ) * ζ ^ 22 + ((71 / 82) : ℂ) * ζ ^ 24 + ((79 / 164) : ℂ) * ζ ^ 26 - ((39 / 82) : ℂ) * ζ ^ 28)
private theorem row17_eigenbasisInverse_mul_3_7 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        3 7 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        3 7 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((20 / 41) : ℂ) + ((1 / 164) : ℂ) * ζ ^ 2 - ((31 / 41) : ℂ) * ζ ^ 4 - ((243 / 328) : ℂ) * ζ ^ 6 - ((13 / 328) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((167 / 328) : ℂ) * ζ ^ 12 - ((13 / 41) : ℂ) * ζ ^ 14 - ((211 / 328) : ℂ) * ζ ^ 16 - ((27 / 328) : ℂ) * ζ ^ 18 + ((45 / 82) : ℂ) * ζ ^ 20 - ((13 / 82) : ℂ) * ζ ^ 22 - ((5 / 164) : ℂ) * ζ ^ 24 + ((21 / 328) : ℂ) * ζ ^ 26 + ((27 / 164) : ℂ) * ζ ^ 28)
private theorem row17_eigenbasisInverse_mul_4_0 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        4 0 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        4 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 16 + ((3 / 4) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24)
private theorem row17_eigenbasisInverse_mul_4_1 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        4 1 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        4 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((3 / 8) : ℂ) + ((3 / 8) : ℂ) * ζ ^ 4 + ((3 / 8) : ℂ) * ζ ^ 8 - ((3 / 8) : ℂ) * ζ ^ 12 - ((1 / 8) : ℂ) * ζ ^ 16 - ((1 / 8) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24)
private theorem row17_eigenbasisInverse_mul_4_2 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        4 2 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        4 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((33 / 164) : ℂ) + ((15 / 41) : ℂ) * ζ ^ 2 - ((33 / 164) : ℂ) * ζ ^ 4 + ((4 / 41) : ℂ) * ζ ^ 6 + ((105 / 328) : ℂ) * ζ ^ 8 - ((139 / 328) : ℂ) * ζ ^ 10 + ((67 / 328) : ℂ) * ζ ^ 12 + ((119 / 164) : ℂ) * ζ ^ 14 + ((7 / 328) : ℂ) * ζ ^ 16 - ((93 / 328) : ℂ) * ζ ^ 18 + ((221 / 328) : ℂ) * ζ ^ 20 - ((7 / 164) : ℂ) * ζ ^ 22 + ((37 / 164) : ℂ) * ζ ^ 24 + ((19 / 41) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_4_3 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        4 3 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        4 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((97 / 328) : ℂ) - ((23 / 82) : ℂ) * ζ ^ 2 - ((97 / 328) : ℂ) * ζ ^ 4 + ((13 / 82) : ℂ) * ζ ^ 6 - ((101 / 328) : ℂ) * ζ ^ 8 + ((7 / 41) : ℂ) * ζ ^ 10 + ((155 / 328) : ℂ) * ζ ^ 12 - ((27 / 164) : ℂ) * ζ ^ 14 + ((37 / 328) : ℂ) * ζ ^ 16 + ((25 / 82) : ℂ) * ζ ^ 18 + ((13 / 164) : ℂ) * ζ ^ 20 + ((1 / 41) : ℂ) * ζ ^ 22 + ((24 / 41) : ℂ) * ζ ^ 24 - ((61 / 164) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_4_4 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        4 4 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        4 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((17 / 22) : ℂ) + ((17 / 22) : ℂ) * ζ ^ 4 - ((25 / 44) : ℂ) * ζ ^ 8 - ((19 / 22) : ℂ) * ζ ^ 12 - ((1 / 22) : ℂ) * ζ ^ 16 - ((5 / 11) : ℂ) * ζ ^ 20 - ((10 / 11) : ℂ) * ζ ^ 24)
private theorem row17_eigenbasisInverse_mul_4_5 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        4 5 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        4 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((17 / 88) : ℂ) + ((17 / 88) : ℂ) * ζ ^ 4 + ((37 / 88) : ℂ) * ζ ^ 8 - ((85 / 88) : ℂ) * ζ ^ 12 - ((23 / 88) : ℂ) * ζ ^ 16 - ((21 / 88) : ℂ) * ζ ^ 20 - ((27 / 22) : ℂ) * ζ ^ 24)
private theorem row17_eigenbasisInverse_mul_4_6 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        4 6 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        4 6 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((33 / 164) : ℂ) - ((15 / 41) : ℂ) * ζ ^ 2 - ((33 / 164) : ℂ) * ζ ^ 4 - ((4 / 41) : ℂ) * ζ ^ 6 + ((105 / 328) : ℂ) * ζ ^ 8 + ((139 / 328) : ℂ) * ζ ^ 10 + ((67 / 328) : ℂ) * ζ ^ 12 - ((119 / 164) : ℂ) * ζ ^ 14 + ((7 / 328) : ℂ) * ζ ^ 16 + ((93 / 328) : ℂ) * ζ ^ 18 + ((221 / 328) : ℂ) * ζ ^ 20 + ((7 / 164) : ℂ) * ζ ^ 22 + ((37 / 164) : ℂ) * ζ ^ 24 - ((19 / 41) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_4_7 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        4 7 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        4 7 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((97 / 328) : ℂ) + ((23 / 82) : ℂ) * ζ ^ 2 - ((97 / 328) : ℂ) * ζ ^ 4 - ((13 / 82) : ℂ) * ζ ^ 6 - ((101 / 328) : ℂ) * ζ ^ 8 - ((7 / 41) : ℂ) * ζ ^ 10 + ((155 / 328) : ℂ) * ζ ^ 12 + ((27 / 164) : ℂ) * ζ ^ 14 + ((37 / 328) : ℂ) * ζ ^ 16 - ((25 / 82) : ℂ) * ζ ^ 18 + ((13 / 164) : ℂ) * ζ ^ 20 - ((1 / 41) : ℂ) * ζ ^ 22 + ((24 / 41) : ℂ) * ζ ^ 24 + ((61 / 164) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_5_0 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        5 0 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        5 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((7 / 8) : ℂ) - ((7 / 8) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 + ((5 / 8) : ℂ) * ζ ^ 12 - ((3 / 8) : ℂ) * ζ ^ 16 - ((1 / 8) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24)
private theorem row17_eigenbasisInverse_mul_5_1 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        5 1 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        5 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((3 / 8) : ℂ) - ((3 / 8) : ℂ) * ζ ^ 4 + ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 8) : ℂ) * ζ ^ 16 - ((3 / 8) : ℂ) * ζ ^ 20 - ((5 / 8) : ℂ) * ζ ^ 24)
private theorem row17_eigenbasisInverse_mul_5_2 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        5 2 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        5 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((1 / 8) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 + ((1 / 8) : ℂ) * ζ ^ 4 - ((69 / 328) : ℂ) * ζ ^ 8 - ((159 / 328) : ℂ) * ζ ^ 10 + ((1 / 164) : ℂ) * ζ ^ 12 - ((405 / 328) : ℂ) * ζ ^ 14 - ((271 / 328) : ℂ) * ζ ^ 16 + ((39 / 164) : ℂ) * ζ ^ 18 - ((32 / 41) : ℂ) * ζ ^ 20 - ((237 / 328) : ℂ) * ζ ^ 22 - ((269 / 328) : ℂ) * ζ ^ 24 - ((55 / 328) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_5_3 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        5 3 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        5 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((1 / 2) : ℂ) + ((3 / 8) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 6 + ((49 / 164) : ℂ) * ζ ^ 8 + ((167 / 328) : ℂ) * ζ ^ 10 - ((171 / 328) : ℂ) * ζ ^ 12 - ((79 / 328) : ℂ) * ζ ^ 14 + ((67 / 328) : ℂ) * ζ ^ 16 - ((17 / 82) : ℂ) * ζ ^ 18 - ((47 / 328) : ℂ) * ζ ^ 20 + ((153 / 328) : ℂ) * ζ ^ 22 - ((13 / 41) : ℂ) * ζ ^ 24 + ((49 / 328) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_5_4 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        5 4 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        5 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((129 / 88) : ℂ) - ((129 / 88) : ℂ) * ζ ^ 4 - ((13 / 11) : ℂ) * ζ ^ 8 + ((15 / 8) : ℂ) * ζ ^ 12 + ((1 / 8) : ℂ) * ζ ^ 16 + ((17 / 8) : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24)
private theorem row17_eigenbasisInverse_mul_5_5 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        5 5 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        5 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((97 / 88) : ℂ) + ((97 / 88) : ℂ) * ζ ^ 4 - ((17 / 11) : ℂ) * ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 12 - ((9 / 8) : ℂ) * ζ ^ 16 - ((3 / 8) : ℂ) * ζ ^ 20 - ((3 / 8) : ℂ) * ζ ^ 24)
private theorem row17_eigenbasisInverse_mul_5_6 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        5 6 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        5 6 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((1 / 8) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 2 + ((1 / 8) : ℂ) * ζ ^ 4 - ((69 / 328) : ℂ) * ζ ^ 8 + ((159 / 328) : ℂ) * ζ ^ 10 + ((1 / 164) : ℂ) * ζ ^ 12 + ((405 / 328) : ℂ) * ζ ^ 14 - ((271 / 328) : ℂ) * ζ ^ 16 - ((39 / 164) : ℂ) * ζ ^ 18 - ((32 / 41) : ℂ) * ζ ^ 20 + ((237 / 328) : ℂ) * ζ ^ 22 - ((269 / 328) : ℂ) * ζ ^ 24 + ((55 / 328) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_5_7 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        5 7 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        5 7 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((1 / 2) : ℂ) - ((3 / 8) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 + ((49 / 164) : ℂ) * ζ ^ 8 - ((167 / 328) : ℂ) * ζ ^ 10 - ((171 / 328) : ℂ) * ζ ^ 12 + ((79 / 328) : ℂ) * ζ ^ 14 + ((67 / 328) : ℂ) * ζ ^ 16 + ((17 / 82) : ℂ) * ζ ^ 18 - ((47 / 328) : ℂ) * ζ ^ 20 - ((153 / 328) : ℂ) * ζ ^ 22 - ((13 / 41) : ℂ) * ζ ^ 24 - ((49 / 328) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_6_0 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        6 0 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        6 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((5 / 8) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 2 - ((5 / 8) : ℂ) * ζ ^ 4 + ((5 / 4) : ℂ) * ζ ^ 6 - ((5 / 8) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 10 + ((3 / 4) : ℂ) * ζ ^ 12 - ((7 / 4) : ℂ) * ζ ^ 14 - ((3 / 8) : ℂ) * ζ ^ 16 + ((11 / 8) : ℂ) * ζ ^ 18 - ((3 / 8) : ℂ) * ζ ^ 22 + ((3 / 8) : ℂ) * ζ ^ 24 - ((1 / 8) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_6_1 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        6 1 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        6 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((1 / 4) : ℂ) + ((1 / 8) : ℂ) * ζ ^ 2 - ((1 / 4) : ℂ) * ζ ^ 4 + ζ ^ 6 - ((3 / 4) : ℂ) * ζ ^ 10 + ((1 / 8) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 16 - ((11 / 8) : ℂ) * ζ ^ 18 - ((3 / 8) : ℂ) * ζ ^ 20 + ((13 / 8) : ℂ) * ζ ^ 22 + ((3 / 8) : ℂ) * ζ ^ 24 - ((3 / 8) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_6_2 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        6 2 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        6 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((149 / 328) : ℂ) + ((43 / 164) : ℂ) * ζ ^ 2 - ((309 / 328) : ℂ) * ζ ^ 4 + ((27 / 41) : ℂ) * ζ ^ 6 - ((22 / 41) : ℂ) * ζ ^ 8 - ((719 / 328) : ℂ) * ζ ^ 10 + ((119 / 328) : ℂ) * ζ ^ 12 - ((19 / 164) : ℂ) * ζ ^ 14 - ((291 / 164) : ℂ) * ζ ^ 16 - ((66 / 41) : ℂ) * ζ ^ 18 + ((693 / 328) : ℂ) * ζ ^ 20 + ((25 / 328) : ℂ) * ζ ^ 22 - ((641 / 328) : ℂ) * ζ ^ 24 + ((625 / 328) : ℂ) * ζ ^ 26 + ((169 / 164) : ℂ) * ζ ^ 28)
private theorem row17_eigenbasisInverse_mul_6_3 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        6 3 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        6 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((9 / 328) : ℂ) - ((55 / 328) : ℂ) * ζ ^ 2 + ((159 / 328) : ℂ) * ζ ^ 4 + ((105 / 328) : ℂ) * ζ ^ 6 - ((51 / 82) : ℂ) * ζ ^ 8 - ((251 / 328) : ℂ) * ζ ^ 10 + ((55 / 328) : ℂ) * ζ ^ 12 - ((31 / 328) : ℂ) * ζ ^ 14 - ((13 / 328) : ℂ) * ζ ^ 16 + ((167 / 328) : ℂ) * ζ ^ 18 - ((273 / 328) : ℂ) * ζ ^ 20 - ((313 / 328) : ℂ) * ζ ^ 22 + ((33 / 82) : ℂ) * ζ ^ 24 + ((3 / 164) : ℂ) * ζ ^ 26 - ((30 / 41) : ℂ) * ζ ^ 28)
private theorem row17_eigenbasisInverse_mul_6_4 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        6 4 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        6 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((15 / 88) : ℂ) - ((1 / 44) : ℂ) * ζ ^ 2 - ((15 / 88) : ℂ) * ζ ^ 4 - ((2 / 11) : ℂ) * ζ ^ 6 - ((27 / 88) : ℂ) * ζ ^ 8 + ((3 / 2) : ℂ) * ζ ^ 10 + ((5 / 4) : ℂ) * ζ ^ 12 + ((21 / 44) : ℂ) * ζ ^ 14 - ((9 / 88) : ℂ) * ζ ^ 16 + ((95 / 88) : ℂ) * ζ ^ 18 + ((21 / 22) : ℂ) * ζ ^ 20 + ((21 / 88) : ℂ) * ζ ^ 22 + ((101 / 88) : ℂ) * ζ ^ 24 - ((79 / 88) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_6_5 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        6 5 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        6 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((7 / 11) : ℂ) - ((17 / 88) : ℂ) * ζ ^ 2 - ((7 / 11) : ℂ) * ζ ^ 4 + ((75 / 44) : ℂ) * ζ ^ 6 + ((9 / 44) : ℂ) * ζ ^ 8 - ((7 / 4) : ℂ) * ζ ^ 10 - ((1 / 8) : ℂ) * ζ ^ 12 + ((24 / 11) : ℂ) * ζ ^ 14 + ((47 / 44) : ℂ) * ζ ^ 16 - ((177 / 88) : ℂ) * ζ ^ 18 - ((23 / 88) : ℂ) * ζ ^ 20 + ((173 / 88) : ℂ) * ζ ^ 22 + ((83 / 88) : ℂ) * ζ ^ 24 + ((93 / 88) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_6_6 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        6 6 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        6 6 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((179 / 328) : ℂ) + ((33 / 164) : ℂ) * ζ ^ 2 + ((339 / 328) : ℂ) * ζ ^ 4 + ((119 / 164) : ℂ) * ζ ^ 6 + ((225 / 164) : ℂ) * ζ ^ 8 - ((559 / 328) : ℂ) * ζ ^ 10 - ((695 / 328) : ℂ) * ζ ^ 12 - ((11 / 164) : ℂ) * ζ ^ 14 + ((69 / 41) : ℂ) * ζ ^ 16 - ((5 / 41) : ℂ) * ζ ^ 18 - ((825 / 328) : ℂ) * ζ ^ 20 - ((281 / 328) : ℂ) * ζ ^ 22 + ((35 / 328) : ℂ) * ζ ^ 24 + ((1001 / 328) : ℂ) * ζ ^ 26 - ((169 / 164) : ℂ) * ζ ^ 28)
private theorem row17_eigenbasisInverse_mul_6_7 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        6 7 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        6 7 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((9 / 328) : ℂ) - ((67 / 328) : ℂ) * ζ ^ 2 - ((141 / 328) : ℂ) * ζ ^ 4 + ((69 / 328) : ℂ) * ζ ^ 6 + ((217 / 164) : ℂ) * ζ ^ 8 - ((73 / 328) : ℂ) * ζ ^ 10 - ((171 / 328) : ℂ) * ζ ^ 12 - ((169 / 328) : ℂ) * ζ ^ 14 - ((87 / 328) : ℂ) * ζ ^ 16 + ((99 / 328) : ℂ) * ζ ^ 18 + ((161 / 328) : ℂ) * ζ ^ 20 - ((103 / 328) : ℂ) * ζ ^ 22 - ((87 / 82) : ℂ) * ζ ^ 24 - ((163 / 164) : ℂ) * ζ ^ 26 + ((30 / 41) : ℂ) * ζ ^ 28)
private theorem row17_eigenbasisInverse_mul_7_0 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        7 0 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        7 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ζ ^ 6 + ((3 / 8) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 - ((5 / 8) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 14 + ((1 / 8) : ℂ) * ζ ^ 18 + ((1 / 8) : ℂ) * ζ ^ 20 - ((7 / 8) : ℂ) * ζ ^ 22 - ((5 / 8) : ℂ) * ζ ^ 24 + ((3 / 8) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_7_1 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        7 1 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        7 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((1 / 8) : ℂ) * ζ ^ 2 - ((3 / 4) : ℂ) * ζ ^ 6 - ((7 / 8) : ℂ) * ζ ^ 8 + ζ ^ 10 + ζ ^ 12 - ((3 / 4) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 16 + ((11 / 8) : ℂ) * ζ ^ 18 + ((7 / 8) : ℂ) * ζ ^ 20 - ((9 / 8) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 + ((3 / 8) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_7_2 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        7 2 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        7 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((29 / 82) : ℂ) + ((53 / 164) : ℂ) * ζ ^ 2 - ((29 / 164) : ℂ) * ζ ^ 4 - ((269 / 164) : ℂ) * ζ ^ 6 + ((283 / 164) : ℂ) * ζ ^ 8 + ((15 / 8) : ℂ) * ζ ^ 10 - ((66 / 41) : ℂ) * ζ ^ 12 + ((187 / 328) : ℂ) * ζ ^ 14 + ((241 / 164) : ℂ) * ζ ^ 16 - ((37 / 328) : ℂ) * ζ ^ 18 - ((24 / 41) : ℂ) * ζ ^ 20 + ((57 / 164) : ℂ) * ζ ^ 22 + ((71 / 82) : ℂ) * ζ ^ 24 - ((79 / 164) : ℂ) * ζ ^ 26 - ((39 / 82) : ℂ) * ζ ^ 28)
private theorem row17_eigenbasisInverse_mul_7_3 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        7 3 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        7 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((20 / 41) : ℂ) - ((1 / 164) : ℂ) * ζ ^ 2 - ((31 / 41) : ℂ) * ζ ^ 4 + ((243 / 328) : ℂ) * ζ ^ 6 - ((13 / 328) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((167 / 328) : ℂ) * ζ ^ 12 + ((13 / 41) : ℂ) * ζ ^ 14 - ((211 / 328) : ℂ) * ζ ^ 16 + ((27 / 328) : ℂ) * ζ ^ 18 + ((45 / 82) : ℂ) * ζ ^ 20 + ((13 / 82) : ℂ) * ζ ^ 22 - ((5 / 164) : ℂ) * ζ ^ 24 - ((21 / 328) : ℂ) * ζ ^ 26 + ((27 / 164) : ℂ) * ζ ^ 28)
private theorem row17_eigenbasisInverse_mul_7_4 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        7 4 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        7 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((23 / 22) : ℂ) + ((15 / 11) : ℂ) * ζ ^ 2 + ((23 / 22) : ℂ) * ζ ^ 4 - ((79 / 44) : ℂ) * ζ ^ 6 + ((9 / 88) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 10 - ((63 / 88) : ℂ) * ζ ^ 12 - ((43 / 44) : ℂ) * ζ ^ 14 - ((3 / 44) : ℂ) * ζ ^ 16 - ((91 / 88) : ℂ) * ζ ^ 18 - ((7 / 8) : ℂ) * ζ ^ 20 - ((71 / 88) : ℂ) * ζ ^ 22 - ((69 / 88) : ℂ) * ζ ^ 24 + ((45 / 88) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_7_5 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        7 5 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        7 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((3 / 22) : ℂ) - ((25 / 88) : ℂ) * ζ ^ 2 + ((3 / 22) : ℂ) * ζ ^ 4 - ((7 / 11) : ℂ) * ζ ^ 6 + ((49 / 88) : ℂ) * ζ ^ 8 + ((19 / 22) : ℂ) * ζ ^ 10 - ((3 / 11) : ℂ) * ζ ^ 12 - ((19 / 44) : ℂ) * ζ ^ 14 + ((6 / 11) : ℂ) * ζ ^ 16 + ((13 / 88) : ℂ) * ζ ^ 18 - ((1 / 8) : ℂ) * ζ ^ 20 + ((7 / 88) : ℂ) * ζ ^ 22 + ((3 / 11) : ℂ) * ζ ^ 24 - ((129 / 88) : ℂ) * ζ ^ 26)
private theorem row17_eigenbasisInverse_mul_7_6 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        7 6 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        7 6 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((29 / 82) : ℂ) + ((3 / 164) : ℂ) * ζ ^ 2 + ((145 / 164) : ℂ) * ζ ^ 4 - ((25 / 82) : ℂ) * ζ ^ 6 - ((51 / 41) : ℂ) * ζ ^ 8 - ((49 / 328) : ℂ) * ζ ^ 10 + ((5 / 4) : ℂ) * ζ ^ 12 + ((325 / 328) : ℂ) * ζ ^ 14 - ((27 / 82) : ℂ) * ζ ^ 16 - ((27 / 328) : ℂ) * ζ ^ 18 - ((53 / 164) : ℂ) * ζ ^ 20 - ((61 / 164) : ℂ) * ζ ^ 22 - ((7 / 82) : ℂ) * ζ ^ 24 + ((4 / 41) : ℂ) * ζ ^ 26 + ((39 / 82) : ℂ) * ζ ^ 28)
private theorem row17_eigenbasisInverse_mul_7_7 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis)
        7 7 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ)
        7 7 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((21 / 41) : ℂ) - ((18 / 41) : ℂ) * ζ ^ 2 + ((32 / 41) : ℂ) * ζ ^ 4 + ((227 / 328) : ℂ) * ζ ^ 6 - ((335 / 328) : ℂ) * ζ ^ 8 + ((24 / 41) : ℂ) * ζ ^ 10 - ((3 / 8) : ℂ) * ζ ^ 12 - ((23 / 82) : ℂ) * ζ ^ 14 + ((255 / 328) : ℂ) * ζ ^ 16 + ((279 / 328) : ℂ) * ζ ^ 18 - ((81 / 164) : ℂ) * ζ ^ 20 + ((35 / 82) : ℂ) * ζ ^ 22 + ((49 / 164) : ℂ) * ζ ^ 24 - ((71 / 328) : ℂ) * ζ ^ 26 - ((27 / 164) : ℂ) * ζ ^ 28)
/-- The displayed row 17 matrix is a left inverse of its
eigenbasis. -/
theorem alternatingSixAmbientRow17EigenbasisInverse_mul :
    alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixAmbientRow17Eigenbasis =
      1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row17_eigenbasisInverse_mul_0_0
  · exact row17_eigenbasisInverse_mul_0_1
  · exact row17_eigenbasisInverse_mul_0_2
  · exact row17_eigenbasisInverse_mul_0_3
  · exact row17_eigenbasisInverse_mul_0_4
  · exact row17_eigenbasisInverse_mul_0_5
  · exact row17_eigenbasisInverse_mul_0_6
  · exact row17_eigenbasisInverse_mul_0_7
  · exact row17_eigenbasisInverse_mul_1_0
  · exact row17_eigenbasisInverse_mul_1_1
  · exact row17_eigenbasisInverse_mul_1_2
  · exact row17_eigenbasisInverse_mul_1_3
  · exact row17_eigenbasisInverse_mul_1_4
  · exact row17_eigenbasisInverse_mul_1_5
  · exact row17_eigenbasisInverse_mul_1_6
  · exact row17_eigenbasisInverse_mul_1_7
  · exact row17_eigenbasisInverse_mul_2_0
  · exact row17_eigenbasisInverse_mul_2_1
  · exact row17_eigenbasisInverse_mul_2_2
  · exact row17_eigenbasisInverse_mul_2_3
  · exact row17_eigenbasisInverse_mul_2_4
  · exact row17_eigenbasisInverse_mul_2_5
  · exact row17_eigenbasisInverse_mul_2_6
  · exact row17_eigenbasisInverse_mul_2_7
  · exact row17_eigenbasisInverse_mul_3_0
  · exact row17_eigenbasisInverse_mul_3_1
  · exact row17_eigenbasisInverse_mul_3_2
  · exact row17_eigenbasisInverse_mul_3_3
  · exact row17_eigenbasisInverse_mul_3_4
  · exact row17_eigenbasisInverse_mul_3_5
  · exact row17_eigenbasisInverse_mul_3_6
  · exact row17_eigenbasisInverse_mul_3_7
  · exact row17_eigenbasisInverse_mul_4_0
  · exact row17_eigenbasisInverse_mul_4_1
  · exact row17_eigenbasisInverse_mul_4_2
  · exact row17_eigenbasisInverse_mul_4_3
  · exact row17_eigenbasisInverse_mul_4_4
  · exact row17_eigenbasisInverse_mul_4_5
  · exact row17_eigenbasisInverse_mul_4_6
  · exact row17_eigenbasisInverse_mul_4_7
  · exact row17_eigenbasisInverse_mul_5_0
  · exact row17_eigenbasisInverse_mul_5_1
  · exact row17_eigenbasisInverse_mul_5_2
  · exact row17_eigenbasisInverse_mul_5_3
  · exact row17_eigenbasisInverse_mul_5_4
  · exact row17_eigenbasisInverse_mul_5_5
  · exact row17_eigenbasisInverse_mul_5_6
  · exact row17_eigenbasisInverse_mul_5_7
  · exact row17_eigenbasisInverse_mul_6_0
  · exact row17_eigenbasisInverse_mul_6_1
  · exact row17_eigenbasisInverse_mul_6_2
  · exact row17_eigenbasisInverse_mul_6_3
  · exact row17_eigenbasisInverse_mul_6_4
  · exact row17_eigenbasisInverse_mul_6_5
  · exact row17_eigenbasisInverse_mul_6_6
  · exact row17_eigenbasisInverse_mul_6_7
  · exact row17_eigenbasisInverse_mul_7_0
  · exact row17_eigenbasisInverse_mul_7_1
  · exact row17_eigenbasisInverse_mul_7_2
  · exact row17_eigenbasisInverse_mul_7_3
  · exact row17_eigenbasisInverse_mul_7_4
  · exact row17_eigenbasisInverse_mul_7_5
  · exact row17_eigenbasisInverse_mul_7_6
  · exact row17_eigenbasisInverse_mul_7_7

/-- The displayed row 17 inverse is also a right inverse. -/
theorem alternatingSixAmbientRow17Eigenbasis_mul_inverse :
    alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixAmbientRow17EigenbasisInverse_mul


private theorem row17_generatorB_mul_eigenbasis_0_0 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        0 0 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        0 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 - ζ ^ 20)
private theorem row17_generatorB_mul_eigenbasis_0_1 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        0 1 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        0 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-(1 : ℂ) + ζ ^ 4)
private theorem row17_generatorB_mul_eigenbasis_0_2 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        0 2 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        0 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((37 / 41) : ℂ) * ζ ^ 24 + ((11 / 41) : ℂ) * ζ ^ 26 + ((37 / 41) : ℂ) * ζ ^ 28)
private theorem row17_generatorB_mul_eigenbasis_0_3 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        0 3 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        0 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((27 / 41) : ℂ) * ζ ^ 24 + ((23 / 41) : ℂ) * ζ ^ 26 - ((27 / 41) : ℂ) * ζ ^ 28)
private theorem row17_generatorB_mul_eigenbasis_0_4 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        0 4 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        0 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((8 / 11) : ℂ) * ζ ^ 24 + ((8 / 11) : ℂ) * ζ ^ 28 - ((17 / 11) : ℂ) * ζ ^ 32 + ((2 / 11) : ℂ) * ζ ^ 36 - ((2 / 11) : ℂ) * ζ ^ 40 - ((15 / 11) : ℂ) * ζ ^ 44 + ((5 / 11) : ℂ) * ζ ^ 48 - ((5 / 11) : ℂ) * ζ ^ 52 - ((10 / 11) : ℂ) * ζ ^ 56)
private theorem row17_generatorB_mul_eigenbasis_0_5 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        0 5 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        0 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((2 / 11) : ℂ) * ζ ^ 24 + ((2 / 11) : ℂ) * ζ ^ 28 + ((4 / 11) : ℂ) * ζ ^ 32 - ((5 / 11) : ℂ) * ζ ^ 36 + ((5 / 11) : ℂ) * ζ ^ 40 - ((1 / 11) : ℂ) * ζ ^ 44 - ((18 / 11) : ℂ) * ζ ^ 48 + ((18 / 11) : ℂ) * ζ ^ 52 - ((19 / 11) : ℂ) * ζ ^ 56)
private theorem row17_generatorB_mul_eigenbasis_0_6 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        0 6 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        0 6 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((37 / 41) : ℂ) * ζ ^ 24 - ((11 / 41) : ℂ) * ζ ^ 26 + ((37 / 41) : ℂ) * ζ ^ 28 + ((49 / 41) : ℂ) * ζ ^ 30 - ((22 / 41) : ℂ) * ζ ^ 32 - ((49 / 41) : ℂ) * ζ ^ 34 - ((25 / 41) : ℂ) * ζ ^ 36 + ((38 / 41) : ℂ) * ζ ^ 38 + ((25 / 41) : ℂ) * ζ ^ 40 + ((32 / 41) : ℂ) * ζ ^ 42 - ((47 / 41) : ℂ) * ζ ^ 44 - ((32 / 41) : ℂ) * ζ ^ 46 - ((18 / 41) : ℂ) * ζ ^ 48 + ((70 / 41) : ℂ) * ζ ^ 50 + ((18 / 41) : ℂ) * ζ ^ 52 + ((5 / 41) : ℂ) * ζ ^ 54 - ((65 / 41) : ℂ) * ζ ^ 56 - ((5 / 41) : ℂ) * ζ ^ 58 + ((10 / 41) : ℂ) * ζ ^ 60 + ((75 / 41) : ℂ) * ζ ^ 62 - ((10 / 41) : ℂ) * ζ ^ 64 - ((21 / 41) : ℂ) * ζ ^ 66 - ((55 / 41) : ℂ) * ζ ^ 68 + ((21 / 41) : ℂ) * ζ ^ 70 + ((40 / 41) : ℂ) * ζ ^ 72 + ((54 / 41) : ℂ) * ζ ^ 74 - ((40 / 41) : ℂ) * ζ ^ 76 - ((43 / 41) : ℂ) * ζ ^ 78 - ((15 / 41) : ℂ) * ζ ^ 80 + ((43 / 41) : ℂ) * ζ ^ 82 + ((37 / 41) : ℂ) * ζ ^ 84 + ((11 / 41) : ℂ) * ζ ^ 86 - ((37 / 41) : ℂ) * ζ ^ 88)
private theorem row17_generatorB_mul_eigenbasis_0_7 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        0 7 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        0 7 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((27 / 41) : ℂ) * ζ ^ 24 - ((23 / 41) : ℂ) * ζ ^ 26 - ((27 / 41) : ℂ) * ζ ^ 28 + ((13 / 41) : ℂ) * ζ ^ 30 + ((36 / 41) : ℂ) * ζ ^ 32 - ((13 / 41) : ℂ) * ζ ^ 34 - ((15 / 41) : ℂ) * ζ ^ 36 - ((10 / 41) : ℂ) * ζ ^ 38 + ((15 / 41) : ℂ) * ζ ^ 40 + ((11 / 41) : ℂ) * ζ ^ 42 + ((21 / 41) : ℂ) * ζ ^ 44 - ((11 / 41) : ℂ) * ζ ^ 46 - ((19 / 41) : ℂ) * ζ ^ 48 + ((1 / 41) : ℂ) * ζ ^ 50 + ((19 / 41) : ℂ) * ζ ^ 52 + ((3 / 41) : ℂ) * ζ ^ 54 + ((2 / 41) : ℂ) * ζ ^ 56 - ((3 / 41) : ℂ) * ζ ^ 58 + ((6 / 41) : ℂ) * ζ ^ 60 + ((4 / 41) : ℂ) * ζ ^ 62 - ((6 / 41) : ℂ) * ζ ^ 64 + ((12 / 41) : ℂ) * ζ ^ 66 + ((8 / 41) : ℂ) * ζ ^ 68 - ((12 / 41) : ℂ) * ζ ^ 70 - ((17 / 41) : ℂ) * ζ ^ 72 + ((16 / 41) : ℂ) * ζ ^ 74 + ((17 / 41) : ℂ) * ζ ^ 76 + ((7 / 41) : ℂ) * ζ ^ 78 - ((9 / 41) : ℂ) * ζ ^ 80 - ((7 / 41) : ℂ) * ζ ^ 82 - ((27 / 41) : ℂ) * ζ ^ 84 + ((23 / 41) : ℂ) * ζ ^ 86 + ((27 / 41) : ℂ) * ζ ^ 88)
private theorem row17_generatorB_mul_eigenbasis_1_0 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        1 0 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        1 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((3 / 2) : ℂ) - ((3 / 2) : ℂ) * ζ ^ 4 + ((5 / 2) : ℂ) * ζ ^ 20)
private theorem row17_generatorB_mul_eigenbasis_1_1 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        1 1 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        1 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((3 / 2) : ℂ) - ((3 / 2) : ℂ) * ζ ^ 4 + (3 : ℂ) * ζ ^ 8 - ((9 / 2) : ℂ) * ζ ^ 12 + (4 : ℂ) * ζ ^ 16 - (5 : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24)
private theorem row17_generatorB_mul_eigenbasis_1_2 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        1 2 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        1 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((92 / 41) : ℂ) - ((109 / 82) : ℂ) * ζ ^ 2 - ((92 / 41) : ℂ) * ζ ^ 4 + ((329 / 82) : ℂ) * ζ ^ 6 + ((83 / 82) : ℂ) * ζ ^ 8 - ((222 / 41) : ℂ) * ζ ^ 10 - ((71 / 41) : ℂ) * ζ ^ 12 + ((282 / 41) : ℂ) * ζ ^ 14 + ((97 / 82) : ℂ) * ζ ^ 16 - ((186 / 41) : ℂ) * ζ ^ 18 + ((215 / 41) : ℂ) * ζ ^ 20 + ((257 / 82) : ℂ) * ζ ^ 22 - ((35 / 82) : ℂ) * ζ ^ 24 + ((83 / 82) : ℂ) * ζ ^ 26 - ((5 / 41) : ℂ) * ζ ^ 28)
private theorem row17_generatorB_mul_eigenbasis_1_3 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        1 3 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        1 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((135 / 82) : ℂ) - ((127 / 41) : ℂ) * ζ ^ 2 - ((135 / 82) : ℂ) * ζ ^ 4 + ((99 / 82) : ℂ) * ζ ^ 6 - ((12 / 41) : ℂ) * ζ ^ 8 + ((39 / 41) : ℂ) * ζ ^ 10 + ((146 / 41) : ℂ) * ζ ^ 12 - ((47 / 82) : ℂ) * ζ ^ 14 - ((155 / 82) : ℂ) * ζ ^ 16 + ((118 / 41) : ℂ) * ζ ^ 18 + ((53 / 82) : ℂ) * ζ ^ 20 - ((59 / 82) : ℂ) * ζ ^ 22 + ((143 / 82) : ℂ) * ζ ^ 24 - ((147 / 82) : ℂ) * ζ ^ 26 - ((3 / 41) : ℂ) * ζ ^ 28)
private theorem row17_generatorB_mul_eigenbasis_1_4 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        1 4 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        1 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((23 / 22) : ℂ) - ((23 / 22) : ℂ) * ζ ^ 4 + ((46 / 11) : ℂ) * ζ ^ 8 - ((43 / 11) : ℂ) * ζ ^ 12 + ((12 / 11) : ℂ) * ζ ^ 16 - ((23 / 22) : ℂ) * ζ ^ 20 - ((36 / 11) : ℂ) * ζ ^ 24 + ((5 / 11) : ℂ) * ζ ^ 28 + ((21 / 11) : ℂ) * ζ ^ 32 - ((18 / 11) : ℂ) * ζ ^ 36 + ((18 / 11) : ℂ) * ζ ^ 40 + ((3 / 11) : ℂ) * ζ ^ 44 + ((10 / 11) : ℂ) * ζ ^ 48 - ((10 / 11) : ℂ) * ζ ^ 52 + ((13 / 11) : ℂ) * ζ ^ 56)
private theorem row17_generatorB_mul_eigenbasis_1_5 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        1 5 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        1 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((69 / 22) : ℂ) - ((69 / 22) : ℂ) * ζ ^ 4 + ((39 / 11) : ℂ) * ζ ^ 8 - ((181 / 22) : ℂ) * ζ ^ 12 + ((25 / 11) : ℂ) * ζ ^ 16 + ((4 / 11) : ℂ) * ζ ^ 20 - ((117 / 22) : ℂ) * ζ ^ 24 - ((7 / 11) : ℂ) * ζ ^ 28 - ((3 / 11) : ℂ) * ζ ^ 32 + ((12 / 11) : ℂ) * ζ ^ 36 - ((12 / 11) : ℂ) * ζ ^ 40 + ((9 / 11) : ℂ) * ζ ^ 44 - ((3 / 11) : ℂ) * ζ ^ 48 + ((3 / 11) : ℂ) * ζ ^ 52 + ((6 / 11) : ℂ) * ζ ^ 56)
private theorem row17_generatorB_mul_eigenbasis_1_6 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        1 6 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        1 6 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((92 / 41) : ℂ) + ((109 / 82) : ℂ) * ζ ^ 2 - ((92 / 41) : ℂ) * ζ ^ 4 - ((329 / 82) : ℂ) * ζ ^ 6 + ((83 / 82) : ℂ) * ζ ^ 8 + ((222 / 41) : ℂ) * ζ ^ 10 - ((71 / 41) : ℂ) * ζ ^ 12 - ((282 / 41) : ℂ) * ζ ^ 14 + ((97 / 82) : ℂ) * ζ ^ 16 + ((186 / 41) : ℂ) * ζ ^ 18 + ((215 / 41) : ℂ) * ζ ^ 20 - ((257 / 82) : ℂ) * ζ ^ 22 - ((35 / 82) : ℂ) * ζ ^ 24 - ((83 / 82) : ℂ) * ζ ^ 26 - ((5 / 41) : ℂ) * ζ ^ 28 + ((10 / 41) : ℂ) * ζ ^ 30 + ((34 / 41) : ℂ) * ζ ^ 32 - ((10 / 41) : ℂ) * ζ ^ 34 - ((21 / 41) : ℂ) * ζ ^ 36 - ((14 / 41) : ℂ) * ζ ^ 38 + ((21 / 41) : ℂ) * ζ ^ 40 - ((1 / 41) : ℂ) * ζ ^ 42 + ((13 / 41) : ℂ) * ζ ^ 44 + ((1 / 41) : ℂ) * ζ ^ 46 - ((2 / 41) : ℂ) * ζ ^ 48 - ((15 / 41) : ℂ) * ζ ^ 50 + ((2 / 41) : ℂ) * ζ ^ 52 - ((4 / 41) : ℂ) * ζ ^ 54 + ((11 / 41) : ℂ) * ζ ^ 56 + ((4 / 41) : ℂ) * ζ ^ 58 - ((8 / 41) : ℂ) * ζ ^ 60 - ((19 / 41) : ℂ) * ζ ^ 62 + ((8 / 41) : ℂ) * ζ ^ 64 + ((25 / 41) : ℂ) * ζ ^ 66 + ((3 / 41) : ℂ) * ζ ^ 68 - ((25 / 41) : ℂ) * ζ ^ 70 - ((32 / 41) : ℂ) * ζ ^ 72 + ((6 / 41) : ℂ) * ζ ^ 74 + ((32 / 41) : ℂ) * ζ ^ 76 + ((18 / 41) : ℂ) * ζ ^ 78 - ((29 / 41) : ℂ) * ζ ^ 80 - ((18 / 41) : ℂ) * ζ ^ 82 - ((5 / 41) : ℂ) * ζ ^ 84 + ((24 / 41) : ℂ) * ζ ^ 86 + ((5 / 41) : ℂ) * ζ ^ 88)
private theorem row17_generatorB_mul_eigenbasis_1_7 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        1 7 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        1 7 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((135 / 82) : ℂ) + ((127 / 41) : ℂ) * ζ ^ 2 - ((135 / 82) : ℂ) * ζ ^ 4 - ((99 / 82) : ℂ) * ζ ^ 6 - ((12 / 41) : ℂ) * ζ ^ 8 - ((39 / 41) : ℂ) * ζ ^ 10 + ((146 / 41) : ℂ) * ζ ^ 12 + ((47 / 82) : ℂ) * ζ ^ 14 - ((155 / 82) : ℂ) * ζ ^ 16 - ((118 / 41) : ℂ) * ζ ^ 18 + ((53 / 82) : ℂ) * ζ ^ 20 + ((59 / 82) : ℂ) * ζ ^ 22 + ((143 / 82) : ℂ) * ζ ^ 24 + ((147 / 82) : ℂ) * ζ ^ 26 - ((3 / 41) : ℂ) * ζ ^ 28 - ((35 / 41) : ℂ) * ζ ^ 30 + ((4 / 41) : ℂ) * ζ ^ 32 + ((35 / 41) : ℂ) * ζ ^ 34 + ((12 / 41) : ℂ) * ζ ^ 36 + ((8 / 41) : ℂ) * ζ ^ 38 - ((12 / 41) : ℂ) * ζ ^ 40 - ((17 / 41) : ℂ) * ζ ^ 42 + ((16 / 41) : ℂ) * ζ ^ 44 + ((17 / 41) : ℂ) * ζ ^ 46 + ((7 / 41) : ℂ) * ζ ^ 48 - ((9 / 41) : ℂ) * ζ ^ 50 - ((7 / 41) : ℂ) * ζ ^ 52 + ((14 / 41) : ℂ) * ζ ^ 54 + ((23 / 41) : ℂ) * ζ ^ 56 - ((14 / 41) : ℂ) * ζ ^ 58 - ((13 / 41) : ℂ) * ζ ^ 60 + ((5 / 41) : ℂ) * ζ ^ 62 + ((13 / 41) : ℂ) * ζ ^ 64 - ((26 / 41) : ℂ) * ζ ^ 66 + ((10 / 41) : ℂ) * ζ ^ 68 + ((26 / 41) : ℂ) * ζ ^ 70 - ((11 / 41) : ℂ) * ζ ^ 72 - ((21 / 41) : ℂ) * ζ ^ 74 + ((11 / 41) : ℂ) * ζ ^ 76 - ((22 / 41) : ℂ) * ζ ^ 78 - ((1 / 41) : ℂ) * ζ ^ 80 + ((22 / 41) : ℂ) * ζ ^ 82 - ((3 / 41) : ℂ) * ζ ^ 84 - ((43 / 41) : ℂ) * ζ ^ 86 + ((3 / 41) : ℂ) * ζ ^ 88)
private theorem row17_generatorB_mul_eigenbasis_2_0 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        2 0 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        2 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-ζ ^ 8 - ζ ^ 12 + (2 : ℂ) * ζ ^ 16 - (3 : ℂ) * ζ ^ 20 + ζ ^ 24)
private theorem row17_generatorB_mul_eigenbasis_2_1 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        2 1 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        2 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 ((1 : ℂ) - ζ ^ 4 - ζ ^ 8 + ζ ^ 16 + ζ ^ 20 + ζ ^ 24)
private theorem row17_generatorB_mul_eigenbasis_2_2 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        2 2 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        2 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((23 / 41) : ℂ) - ((29 / 41) : ℂ) * ζ ^ 2 - ((23 / 41) : ℂ) * ζ ^ 4 - ((5 / 41) : ℂ) * ζ ^ 6 + ((15 / 41) : ℂ) * ζ ^ 8 + ((61 / 41) : ℂ) * ζ ^ 10 + ((28 / 41) : ℂ) * ζ ^ 12 - ((27 / 41) : ℂ) * ζ ^ 14 - ((15 / 41) : ℂ) * ζ ^ 16 + ((67 / 41) : ℂ) * ζ ^ 18 + ((13 / 41) : ℂ) * ζ ^ 20 - ((11 / 41) : ℂ) * ζ ^ 22 + ((4 / 41) : ℂ) * ζ ^ 24 + ((5 / 41) : ℂ) * ζ ^ 26 + ((9 / 41) : ℂ) * ζ ^ 28)
private theorem row17_generatorB_mul_eigenbasis_2_3 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        2 3 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        2 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((19 / 41) : ℂ) - ((1 / 41) : ℂ) * ζ ^ 2 + ((19 / 41) : ℂ) * ζ ^ 4 - ((3 / 41) : ℂ) * ζ ^ 6 + ((50 / 41) : ℂ) * ζ ^ 8 - ((29 / 41) : ℂ) * ζ ^ 10 - ((57 / 41) : ℂ) * ζ ^ 12 - ((8 / 41) : ℂ) * ζ ^ 14 - ((9 / 41) : ℂ) * ζ ^ 16 - ((9 / 41) : ℂ) * ζ ^ 18 + ((16 / 41) : ℂ) * ζ ^ 20 - ((23 / 41) : ℂ) * ζ ^ 22 - ((55 / 41) : ℂ) * ζ ^ 24 + ((44 / 41) : ℂ) * ζ ^ 26 - ((11 / 41) : ℂ) * ζ ^ 28)
private theorem row17_generatorB_mul_eigenbasis_2_4 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        2 4 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        2 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((26 / 11) : ℂ) + ((26 / 11) : ℂ) * ζ ^ 4 - ((7 / 11) : ℂ) * ζ ^ 8 + ((31 / 11) : ℂ) * ζ ^ 12 - ((8 / 11) : ℂ) * ζ ^ 16 - ((9 / 11) : ℂ) * ζ ^ 20 + ((9 / 11) : ℂ) * ζ ^ 24 + ((14 / 11) : ℂ) * ζ ^ 28 + ((6 / 11) : ℂ) * ζ ^ 32 - ((46 / 11) : ℂ) * ζ ^ 36 + ((46 / 11) : ℂ) * ζ ^ 40 - ((40 / 11) : ℂ) * ζ ^ 44 + ((6 / 11) : ℂ) * ζ ^ 48 - ((6 / 11) : ℂ) * ζ ^ 52 - ((34 / 11) : ℂ) * ζ ^ 56)
private theorem row17_generatorB_mul_eigenbasis_2_5 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        2 5 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        2 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((10 / 11) : ℂ) - ((10 / 11) : ℂ) * ζ ^ 4 + ((23 / 11) : ℂ) * ζ ^ 8 - ((6 / 11) : ℂ) * ζ ^ 12 + ((31 / 11) : ℂ) * ζ ^ 16 + ((17 / 11) : ℂ) * ζ ^ 20 + ((27 / 11) : ℂ) * ζ ^ 24 - ((2 / 11) : ℂ) * ζ ^ 28 + ((18 / 11) : ℂ) * ζ ^ 32 + ((5 / 11) : ℂ) * ζ ^ 36 - ((5 / 11) : ℂ) * ζ ^ 40 + ((23 / 11) : ℂ) * ζ ^ 44 - ((26 / 11) : ℂ) * ζ ^ 48 + ((26 / 11) : ℂ) * ζ ^ 52 - ((3 / 11) : ℂ) * ζ ^ 56)
private theorem row17_generatorB_mul_eigenbasis_2_6 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        2 6 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        2 6 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((23 / 41) : ℂ) + ((29 / 41) : ℂ) * ζ ^ 2 - ((23 / 41) : ℂ) * ζ ^ 4 + ((5 / 41) : ℂ) * ζ ^ 6 + ((15 / 41) : ℂ) * ζ ^ 8 - ((61 / 41) : ℂ) * ζ ^ 10 + ((28 / 41) : ℂ) * ζ ^ 12 + ((27 / 41) : ℂ) * ζ ^ 14 - ((15 / 41) : ℂ) * ζ ^ 16 - ((67 / 41) : ℂ) * ζ ^ 18 + ((13 / 41) : ℂ) * ζ ^ 20 + ((11 / 41) : ℂ) * ζ ^ 22 + ((4 / 41) : ℂ) * ζ ^ 24 - ((5 / 41) : ℂ) * ζ ^ 26 + ((9 / 41) : ℂ) * ζ ^ 28 + ((23 / 41) : ℂ) * ζ ^ 30 + ((29 / 41) : ℂ) * ζ ^ 32 - ((23 / 41) : ℂ) * ζ ^ 34 + ((5 / 41) : ℂ) * ζ ^ 36 - ((24 / 41) : ℂ) * ζ ^ 38 - ((5 / 41) : ℂ) * ζ ^ 40 + ((10 / 41) : ℂ) * ζ ^ 42 + ((34 / 41) : ℂ) * ζ ^ 44 - ((10 / 41) : ℂ) * ζ ^ 46 - ((21 / 41) : ℂ) * ζ ^ 48 - ((14 / 41) : ℂ) * ζ ^ 50 + ((21 / 41) : ℂ) * ζ ^ 52 - ((1 / 41) : ℂ) * ζ ^ 54 + ((13 / 41) : ℂ) * ζ ^ 56 + ((1 / 41) : ℂ) * ζ ^ 58 - ((43 / 41) : ℂ) * ζ ^ 60 - ((15 / 41) : ℂ) * ζ ^ 62 + ((43 / 41) : ℂ) * ζ ^ 64 + ((37 / 41) : ℂ) * ζ ^ 66 - ((30 / 41) : ℂ) * ζ ^ 68 - ((37 / 41) : ℂ) * ζ ^ 70 - ((8 / 41) : ℂ) * ζ ^ 72 + ((22 / 41) : ℂ) * ζ ^ 74 + ((8 / 41) : ℂ) * ζ ^ 76 + ((25 / 41) : ℂ) * ζ ^ 78 - ((38 / 41) : ℂ) * ζ ^ 80 - ((25 / 41) : ℂ) * ζ ^ 82 + ((9 / 41) : ℂ) * ζ ^ 84 + ((47 / 41) : ℂ) * ζ ^ 86 - ((9 / 41) : ℂ) * ζ ^ 88)
private theorem row17_generatorB_mul_eigenbasis_2_7 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        2 7 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        2 7 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((19 / 41) : ℂ) + ((1 / 41) : ℂ) * ζ ^ 2 + ((19 / 41) : ℂ) * ζ ^ 4 + ((3 / 41) : ℂ) * ζ ^ 6 + ((50 / 41) : ℂ) * ζ ^ 8 + ((29 / 41) : ℂ) * ζ ^ 10 - ((57 / 41) : ℂ) * ζ ^ 12 + ((8 / 41) : ℂ) * ζ ^ 14 - ((9 / 41) : ℂ) * ζ ^ 16 + ((9 / 41) : ℂ) * ζ ^ 18 + ((16 / 41) : ℂ) * ζ ^ 20 + ((23 / 41) : ℂ) * ζ ^ 22 - ((55 / 41) : ℂ) * ζ ^ 24 - ((44 / 41) : ℂ) * ζ ^ 26 - ((11 / 41) : ℂ) * ζ ^ 28 + ((22 / 41) : ℂ) * ζ ^ 30 + ((1 / 41) : ℂ) * ζ ^ 32 - ((22 / 41) : ℂ) * ζ ^ 34 + ((3 / 41) : ℂ) * ζ ^ 36 + ((2 / 41) : ℂ) * ζ ^ 38 - ((3 / 41) : ℂ) * ζ ^ 40 + ((6 / 41) : ℂ) * ζ ^ 42 + ((4 / 41) : ℂ) * ζ ^ 44 - ((6 / 41) : ℂ) * ζ ^ 46 - ((29 / 41) : ℂ) * ζ ^ 48 + ((8 / 41) : ℂ) * ζ ^ 50 + ((29 / 41) : ℂ) * ζ ^ 52 - ((17 / 41) : ℂ) * ζ ^ 54 - ((25 / 41) : ℂ) * ζ ^ 56 + ((17 / 41) : ℂ) * ζ ^ 58 + ((7 / 41) : ℂ) * ζ ^ 60 - ((9 / 41) : ℂ) * ζ ^ 62 - ((7 / 41) : ℂ) * ζ ^ 64 + ((14 / 41) : ℂ) * ζ ^ 66 - ((18 / 41) : ℂ) * ζ ^ 68 - ((14 / 41) : ℂ) * ζ ^ 70 + ((28 / 41) : ℂ) * ζ ^ 72 + ((5 / 41) : ℂ) * ζ ^ 74 - ((28 / 41) : ℂ) * ζ ^ 76 + ((15 / 41) : ℂ) * ζ ^ 78 + ((10 / 41) : ℂ) * ζ ^ 80 - ((15 / 41) : ℂ) * ζ ^ 82 - ((11 / 41) : ℂ) * ζ ^ 84 + ((20 / 41) : ℂ) * ζ ^ 86 + ((11 / 41) : ℂ) * ζ ^ 88)
private theorem row17_generatorB_mul_eigenbasis_3_0 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        3 0 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        3 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 0
private theorem row17_generatorB_mul_eigenbasis_3_1 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        3 1 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        3 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 0
private theorem row17_generatorB_mul_eigenbasis_3_2 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        3 2 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        3 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((49 / 41) : ℂ) - ((22 / 41) : ℂ) * ζ ^ 2 + ((49 / 41) : ℂ) * ζ ^ 4 - ((25 / 41) : ℂ) * ζ ^ 6 - ((38 / 41) : ℂ) * ζ ^ 8 + ((25 / 41) : ℂ) * ζ ^ 10 - ((32 / 41) : ℂ) * ζ ^ 12 - ((47 / 41) : ℂ) * ζ ^ 14 + ((32 / 41) : ℂ) * ζ ^ 16 - ((18 / 41) : ℂ) * ζ ^ 18 - ((70 / 41) : ℂ) * ζ ^ 20 + ((18 / 41) : ℂ) * ζ ^ 22 - ((5 / 41) : ℂ) * ζ ^ 24 - ((65 / 41) : ℂ) * ζ ^ 26 + ((5 / 41) : ℂ) * ζ ^ 28)
private theorem row17_generatorB_mul_eigenbasis_3_3 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        3 3 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        3 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((13 / 41) : ℂ) + ((36 / 41) : ℂ) * ζ ^ 2 + ((13 / 41) : ℂ) * ζ ^ 4 - ((15 / 41) : ℂ) * ζ ^ 6 + ((10 / 41) : ℂ) * ζ ^ 8 + ((15 / 41) : ℂ) * ζ ^ 10 - ((11 / 41) : ℂ) * ζ ^ 12 + ((21 / 41) : ℂ) * ζ ^ 14 + ((11 / 41) : ℂ) * ζ ^ 16 - ((19 / 41) : ℂ) * ζ ^ 18 - ((1 / 41) : ℂ) * ζ ^ 20 + ((19 / 41) : ℂ) * ζ ^ 22 - ((3 / 41) : ℂ) * ζ ^ 24 + ((2 / 41) : ℂ) * ζ ^ 26 + ((3 / 41) : ℂ) * ζ ^ 28)
private theorem row17_generatorB_mul_eigenbasis_3_4 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        3 4 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        3 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((7 / 11) : ℂ) - ((7 / 11) : ℂ) * ζ ^ 4 - ((3 / 11) : ℂ) * ζ ^ 8 + ((12 / 11) : ℂ) * ζ ^ 12 - ((12 / 11) : ℂ) * ζ ^ 16 + ((9 / 11) : ℂ) * ζ ^ 20 + ((8 / 11) : ℂ) * ζ ^ 24 - ((8 / 11) : ℂ) * ζ ^ 28 + ((17 / 11) : ℂ) * ζ ^ 32 - ((2 / 11) : ℂ) * ζ ^ 36 + ((2 / 11) : ℂ) * ζ ^ 40 + ((15 / 11) : ℂ) * ζ ^ 44 - ((5 / 11) : ℂ) * ζ ^ 48 + ((5 / 11) : ℂ) * ζ ^ 52 + ((10 / 11) : ℂ) * ζ ^ 56)
private theorem row17_generatorB_mul_eigenbasis_3_5 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        3 5 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        3 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((1 / 11) : ℂ) + ((1 / 11) : ℂ) * ζ ^ 4 - ((20 / 11) : ℂ) * ζ ^ 8 + ((14 / 11) : ℂ) * ζ ^ 12 - ((14 / 11) : ℂ) * ζ ^ 16 - ((6 / 11) : ℂ) * ζ ^ 20 + ((2 / 11) : ℂ) * ζ ^ 24 - ((2 / 11) : ℂ) * ζ ^ 28 - ((4 / 11) : ℂ) * ζ ^ 32 + ((5 / 11) : ℂ) * ζ ^ 36 - ((5 / 11) : ℂ) * ζ ^ 40 + ((1 / 11) : ℂ) * ζ ^ 44 + ((18 / 11) : ℂ) * ζ ^ 48 - ((18 / 11) : ℂ) * ζ ^ 52 + ((19 / 11) : ℂ) * ζ ^ 56)
private theorem row17_generatorB_mul_eigenbasis_3_6 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        3 6 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        3 6 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((49 / 41) : ℂ) + ((22 / 41) : ℂ) * ζ ^ 2 + ((49 / 41) : ℂ) * ζ ^ 4 + ((25 / 41) : ℂ) * ζ ^ 6 - ((38 / 41) : ℂ) * ζ ^ 8 - ((25 / 41) : ℂ) * ζ ^ 10 - ((32 / 41) : ℂ) * ζ ^ 12 + ((47 / 41) : ℂ) * ζ ^ 14 + ((32 / 41) : ℂ) * ζ ^ 16 + ((18 / 41) : ℂ) * ζ ^ 18 - ((70 / 41) : ℂ) * ζ ^ 20 - ((18 / 41) : ℂ) * ζ ^ 22 - ((5 / 41) : ℂ) * ζ ^ 24 + ((65 / 41) : ℂ) * ζ ^ 26 + ((5 / 41) : ℂ) * ζ ^ 28 - ((10 / 41) : ℂ) * ζ ^ 30 - ((75 / 41) : ℂ) * ζ ^ 32 + ((10 / 41) : ℂ) * ζ ^ 34 + ((21 / 41) : ℂ) * ζ ^ 36 + ((55 / 41) : ℂ) * ζ ^ 38 - ((21 / 41) : ℂ) * ζ ^ 40 - ((40 / 41) : ℂ) * ζ ^ 42 - ((54 / 41) : ℂ) * ζ ^ 44 + ((40 / 41) : ℂ) * ζ ^ 46 + ((43 / 41) : ℂ) * ζ ^ 48 + ((15 / 41) : ℂ) * ζ ^ 50 - ((43 / 41) : ℂ) * ζ ^ 52 - ((37 / 41) : ℂ) * ζ ^ 54 - ((11 / 41) : ℂ) * ζ ^ 56 + ((37 / 41) : ℂ) * ζ ^ 58 + ((49 / 41) : ℂ) * ζ ^ 60 - ((22 / 41) : ℂ) * ζ ^ 62 - ((49 / 41) : ℂ) * ζ ^ 64 - ((25 / 41) : ℂ) * ζ ^ 66 + ((38 / 41) : ℂ) * ζ ^ 68 + ((25 / 41) : ℂ) * ζ ^ 70 + ((32 / 41) : ℂ) * ζ ^ 72 - ((47 / 41) : ℂ) * ζ ^ 74 - ((32 / 41) : ℂ) * ζ ^ 76 - ((18 / 41) : ℂ) * ζ ^ 78 + ((70 / 41) : ℂ) * ζ ^ 80 + ((18 / 41) : ℂ) * ζ ^ 82 + ((5 / 41) : ℂ) * ζ ^ 84 - ((65 / 41) : ℂ) * ζ ^ 86 - ((5 / 41) : ℂ) * ζ ^ 88)
private theorem row17_generatorB_mul_eigenbasis_3_7 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        3 7 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        3 7 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((13 / 41) : ℂ) - ((36 / 41) : ℂ) * ζ ^ 2 + ((13 / 41) : ℂ) * ζ ^ 4 + ((15 / 41) : ℂ) * ζ ^ 6 + ((10 / 41) : ℂ) * ζ ^ 8 - ((15 / 41) : ℂ) * ζ ^ 10 - ((11 / 41) : ℂ) * ζ ^ 12 - ((21 / 41) : ℂ) * ζ ^ 14 + ((11 / 41) : ℂ) * ζ ^ 16 + ((19 / 41) : ℂ) * ζ ^ 18 - ((1 / 41) : ℂ) * ζ ^ 20 - ((19 / 41) : ℂ) * ζ ^ 22 - ((3 / 41) : ℂ) * ζ ^ 24 - ((2 / 41) : ℂ) * ζ ^ 26 + ((3 / 41) : ℂ) * ζ ^ 28 - ((6 / 41) : ℂ) * ζ ^ 30 - ((4 / 41) : ℂ) * ζ ^ 32 + ((6 / 41) : ℂ) * ζ ^ 34 - ((12 / 41) : ℂ) * ζ ^ 36 - ((8 / 41) : ℂ) * ζ ^ 38 + ((12 / 41) : ℂ) * ζ ^ 40 + ((17 / 41) : ℂ) * ζ ^ 42 - ((16 / 41) : ℂ) * ζ ^ 44 - ((17 / 41) : ℂ) * ζ ^ 46 - ((7 / 41) : ℂ) * ζ ^ 48 + ((9 / 41) : ℂ) * ζ ^ 50 + ((7 / 41) : ℂ) * ζ ^ 52 + ((27 / 41) : ℂ) * ζ ^ 54 - ((23 / 41) : ℂ) * ζ ^ 56 - ((27 / 41) : ℂ) * ζ ^ 58 + ((13 / 41) : ℂ) * ζ ^ 60 + ((36 / 41) : ℂ) * ζ ^ 62 - ((13 / 41) : ℂ) * ζ ^ 64 - ((15 / 41) : ℂ) * ζ ^ 66 - ((10 / 41) : ℂ) * ζ ^ 68 + ((15 / 41) : ℂ) * ζ ^ 70 + ((11 / 41) : ℂ) * ζ ^ 72 + ((21 / 41) : ℂ) * ζ ^ 74 - ((11 / 41) : ℂ) * ζ ^ 76 - ((19 / 41) : ℂ) * ζ ^ 78 + ((1 / 41) : ℂ) * ζ ^ 80 + ((19 / 41) : ℂ) * ζ ^ 82 + ((3 / 41) : ℂ) * ζ ^ 84 + ((2 / 41) : ℂ) * ζ ^ 86 - ((3 / 41) : ℂ) * ζ ^ 88)
private theorem row17_generatorB_mul_eigenbasis_4_0 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        4 0 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        4 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-(1 : ℂ) + ζ ^ 4 - ((5 / 2) : ℂ) * ζ ^ 8 + ((3 / 2) : ℂ) * ζ ^ 12 - ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24)
private theorem row17_generatorB_mul_eigenbasis_4_1 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        4 1 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        4 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 - ζ ^ 8 + ((3 / 2) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 16 - ζ ^ 20 + (3 : ℂ) * ζ ^ 24)
private theorem row17_generatorB_mul_eigenbasis_4_2 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        4 2 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        4 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((22 / 41) : ℂ) + ((1 / 41) : ℂ) * ζ ^ 2 + ((22 / 41) : ℂ) * ζ ^ 4 - ((117 / 82) : ℂ) * ζ ^ 6 + ((79 / 41) : ℂ) * ζ ^ 8 + ((91 / 82) : ℂ) * ζ ^ 10 - ((152 / 41) : ℂ) * ζ ^ 12 + ((167 / 82) : ℂ) * ζ ^ 14 + ((56 / 41) : ℂ) * ζ ^ 16 - ((188 / 41) : ℂ) * ζ ^ 18 + ((38 / 41) : ℂ) * ζ ^ 20 + ((175 / 41) : ℂ) * ζ ^ 22 - ((139 / 41) : ℂ) * ζ ^ 24 - ((217 / 82) : ℂ) * ζ ^ 26 + ((43 / 41) : ℂ) * ζ ^ 28)
private theorem row17_generatorB_mul_eigenbasis_4_3 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        4 3 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        4 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((113 / 82) : ℂ) - ((7 / 82) : ℂ) * ζ ^ 2 - ((113 / 82) : ℂ) * ζ ^ 4 + ((10 / 41) : ℂ) * ζ ^ 6 + ((185 / 82) : ℂ) * ζ ^ 8 - ((67 / 41) : ℂ) * ζ ^ 10 + ((39 / 82) : ℂ) * ζ ^ 12 + ((46 / 41) : ℂ) * ζ ^ 14 - ((105 / 82) : ℂ) * ζ ^ 16 + ((43 / 41) : ℂ) * ζ ^ 18 + ((21 / 82) : ℂ) * ζ ^ 20 - ((100 / 41) : ℂ) * ζ ^ 22 - ((26 / 41) : ℂ) * ζ ^ 24 + ((165 / 82) : ℂ) * ζ ^ 26 - ((7 / 41) : ℂ) * ζ ^ 28)
private theorem row17_generatorB_mul_eigenbasis_4_4 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        4 4 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        4 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((61 / 11) : ℂ) + ((61 / 11) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 + ((15 / 22) : ℂ) * ζ ^ 12 + ((1 / 11) : ℂ) * ζ ^ 16 - ((31 / 22) : ℂ) * ζ ^ 20 + ((7 / 22) : ℂ) * ζ ^ 24 + ((5 / 11) : ℂ) * ζ ^ 28 + ((10 / 11) : ℂ) * ζ ^ 32 - ((7 / 11) : ℂ) * ζ ^ 36 + ((7 / 11) : ℂ) * ζ ^ 40 + ((3 / 11) : ℂ) * ζ ^ 44 - ((12 / 11) : ℂ) * ζ ^ 48 + ((12 / 11) : ℂ) * ζ ^ 52 - ((9 / 11) : ℂ) * ζ ^ 56)
private theorem row17_generatorB_mul_eigenbasis_4_5 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        4 5 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        4 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((63 / 22) : ℂ) - ((63 / 22) : ℂ) * ζ ^ 4 + (4 : ℂ) * ζ ^ 8 - ((65 / 22) : ℂ) * ζ ^ 12 + ((127 / 22) : ℂ) * ζ ^ 16 + ((3 / 11) : ℂ) * ζ ^ 20 + ((49 / 11) : ℂ) * ζ ^ 24 - ((18 / 11) : ℂ) * ζ ^ 28 + ((19 / 11) : ℂ) * ζ ^ 32 + ((1 / 11) : ℂ) * ζ ^ 36 - ((1 / 11) : ℂ) * ζ ^ 40 + ((20 / 11) : ℂ) * ζ ^ 44 - ((14 / 11) : ℂ) * ζ ^ 48 + ((14 / 11) : ℂ) * ζ ^ 52 + ((6 / 11) : ℂ) * ζ ^ 56)
private theorem row17_generatorB_mul_eigenbasis_4_6 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        4 6 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        4 6 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((22 / 41) : ℂ) - ((1 / 41) : ℂ) * ζ ^ 2 + ((22 / 41) : ℂ) * ζ ^ 4 + ((117 / 82) : ℂ) * ζ ^ 6 + ((79 / 41) : ℂ) * ζ ^ 8 - ((91 / 82) : ℂ) * ζ ^ 10 - ((152 / 41) : ℂ) * ζ ^ 12 - ((167 / 82) : ℂ) * ζ ^ 14 + ((56 / 41) : ℂ) * ζ ^ 16 + ((188 / 41) : ℂ) * ζ ^ 18 + ((38 / 41) : ℂ) * ζ ^ 20 - ((175 / 41) : ℂ) * ζ ^ 22 - ((139 / 41) : ℂ) * ζ ^ 24 + ((217 / 82) : ℂ) * ζ ^ 26 + ((43 / 41) : ℂ) * ζ ^ 28 + ((37 / 41) : ℂ) * ζ ^ 30 + ((11 / 41) : ℂ) * ζ ^ 32 - ((37 / 41) : ℂ) * ζ ^ 34 - ((49 / 41) : ℂ) * ζ ^ 36 + ((22 / 41) : ℂ) * ζ ^ 38 + ((49 / 41) : ℂ) * ζ ^ 40 + ((25 / 41) : ℂ) * ζ ^ 42 - ((38 / 41) : ℂ) * ζ ^ 44 - ((25 / 41) : ℂ) * ζ ^ 46 - ((32 / 41) : ℂ) * ζ ^ 48 + ((47 / 41) : ℂ) * ζ ^ 50 + ((32 / 41) : ℂ) * ζ ^ 52 + ((18 / 41) : ℂ) * ζ ^ 54 - ((70 / 41) : ℂ) * ζ ^ 56 - ((18 / 41) : ℂ) * ζ ^ 58 - ((5 / 41) : ℂ) * ζ ^ 60 + ((65 / 41) : ℂ) * ζ ^ 62 + ((5 / 41) : ℂ) * ζ ^ 64 - ((10 / 41) : ℂ) * ζ ^ 66 - ((75 / 41) : ℂ) * ζ ^ 68 + ((10 / 41) : ℂ) * ζ ^ 70 + ((21 / 41) : ℂ) * ζ ^ 72 + ((55 / 41) : ℂ) * ζ ^ 74 - ((21 / 41) : ℂ) * ζ ^ 76 - ((40 / 41) : ℂ) * ζ ^ 78 - ((54 / 41) : ℂ) * ζ ^ 80 + ((40 / 41) : ℂ) * ζ ^ 82 + ((43 / 41) : ℂ) * ζ ^ 84 + ((15 / 41) : ℂ) * ζ ^ 86 - ((43 / 41) : ℂ) * ζ ^ 88)
private theorem row17_generatorB_mul_eigenbasis_4_7 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        4 7 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        4 7 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((113 / 82) : ℂ) + ((7 / 82) : ℂ) * ζ ^ 2 - ((113 / 82) : ℂ) * ζ ^ 4 - ((10 / 41) : ℂ) * ζ ^ 6 + ((185 / 82) : ℂ) * ζ ^ 8 + ((67 / 41) : ℂ) * ζ ^ 10 + ((39 / 82) : ℂ) * ζ ^ 12 - ((46 / 41) : ℂ) * ζ ^ 14 - ((105 / 82) : ℂ) * ζ ^ 16 - ((43 / 41) : ℂ) * ζ ^ 18 + ((21 / 82) : ℂ) * ζ ^ 20 + ((100 / 41) : ℂ) * ζ ^ 22 - ((26 / 41) : ℂ) * ζ ^ 24 - ((165 / 82) : ℂ) * ζ ^ 26 - ((7 / 41) : ℂ) * ζ ^ 28 - ((27 / 41) : ℂ) * ζ ^ 30 + ((23 / 41) : ℂ) * ζ ^ 32 + ((27 / 41) : ℂ) * ζ ^ 34 - ((13 / 41) : ℂ) * ζ ^ 36 - ((36 / 41) : ℂ) * ζ ^ 38 + ((13 / 41) : ℂ) * ζ ^ 40 + ((15 / 41) : ℂ) * ζ ^ 42 + ((10 / 41) : ℂ) * ζ ^ 44 - ((15 / 41) : ℂ) * ζ ^ 46 - ((11 / 41) : ℂ) * ζ ^ 48 - ((21 / 41) : ℂ) * ζ ^ 50 + ((11 / 41) : ℂ) * ζ ^ 52 + ((19 / 41) : ℂ) * ζ ^ 54 - ((1 / 41) : ℂ) * ζ ^ 56 - ((19 / 41) : ℂ) * ζ ^ 58 - ((3 / 41) : ℂ) * ζ ^ 60 - ((2 / 41) : ℂ) * ζ ^ 62 + ((3 / 41) : ℂ) * ζ ^ 64 - ((6 / 41) : ℂ) * ζ ^ 66 - ((4 / 41) : ℂ) * ζ ^ 68 + ((6 / 41) : ℂ) * ζ ^ 70 - ((12 / 41) : ℂ) * ζ ^ 72 - ((8 / 41) : ℂ) * ζ ^ 74 + ((12 / 41) : ℂ) * ζ ^ 76 + ((17 / 41) : ℂ) * ζ ^ 78 - ((16 / 41) : ℂ) * ζ ^ 80 - ((17 / 41) : ℂ) * ζ ^ 82 - ((7 / 41) : ℂ) * ζ ^ 84 + ((9 / 41) : ℂ) * ζ ^ 86 + ((7 / 41) : ℂ) * ζ ^ 88)
private theorem row17_generatorB_mul_eigenbasis_5_0 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        5 0 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        5 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (ζ ^ 20)
private theorem row17_generatorB_mul_eigenbasis_5_1 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        5 1 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        5 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((3 / 2) : ℂ) * ζ ^ 8 - ((3 / 2) : ℂ) * ζ ^ 12 + ((5 / 2) : ℂ) * ζ ^ 16 - ((5 / 2) : ℂ) * ζ ^ 20 + ζ ^ 24)
private theorem row17_generatorB_mul_eigenbasis_5_2 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        5 2 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        5 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((54 / 41) : ℂ) + ((5 / 41) : ℂ) * ζ ^ 2 - ((54 / 41) : ℂ) * ζ ^ 4 + ((56 / 41) : ℂ) * ζ ^ 6 + ((143 / 82) : ℂ) * ζ ^ 8 - ((207 / 82) : ℂ) * ζ ^ 10 - ((189 / 82) : ℂ) * ζ ^ 12 + ((201 / 41) : ℂ) * ζ ^ 14 + ((93 / 82) : ℂ) * ζ ^ 16 - ((319 / 82) : ℂ) * ζ ^ 18 + ((303 / 82) : ℂ) * ζ ^ 20 + ((112 / 41) : ℂ) * ζ ^ 22 - ((85 / 41) : ℂ) * ζ ^ 24 + ((21 / 41) : ℂ) * ζ ^ 26 + ((37 / 41) : ℂ) * ζ ^ 28)
private theorem row17_generatorB_mul_eigenbasis_5_3 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        5 3 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        5 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((155 / 82) : ℂ) - ((79 / 41) : ℂ) * ζ ^ 2 - ((155 / 82) : ℂ) * ζ ^ 4 + ((50 / 41) : ℂ) * ζ ^ 6 - ((29 / 82) : ℂ) * ζ ^ 8 - ((17 / 41) : ℂ) * ζ ^ 10 + ((231 / 82) : ℂ) * ζ ^ 12 + ((14 / 41) : ℂ) * ζ ^ 14 - ((141 / 82) : ℂ) * ζ ^ 16 + ((97 / 41) : ℂ) * ζ ^ 18 + ((13 / 41) : ℂ) * ζ ^ 20 - ((64 / 41) : ℂ) * ζ ^ 22 + ((72 / 41) : ℂ) * ζ ^ 24 - ((12 / 41) : ℂ) * ζ ^ 26 - ((27 / 41) : ℂ) * ζ ^ 28)
private theorem row17_generatorB_mul_eigenbasis_5_4 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        5 4 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        5 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-(2 : ℂ) + (2 : ℂ) * ζ ^ 4 + ((35 / 11) : ℂ) * ζ ^ 8 - ((32 / 11) : ℂ) * ζ ^ 12 + ((4 / 11) : ℂ) * ζ ^ 16 - ((23 / 11) : ℂ) * ζ ^ 20 - ((50 / 11) : ℂ) * ζ ^ 24 + (2 : ℂ) * ζ ^ 28 + ζ ^ 32 - ζ ^ 36 + ζ ^ 40)
private theorem row17_generatorB_mul_eigenbasis_5_5 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        5 5 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        5 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((5 / 2) : ℂ) - ((5 / 2) : ℂ) * ζ ^ 4 + ((67 / 22) : ℂ) * ζ ^ 8 - ((115 / 22) : ℂ) * ζ ^ 12 + ((57 / 22) : ℂ) * ζ ^ 16 - ((17 / 22) : ℂ) * ζ ^ 20 - ((7 / 11) : ℂ) * ζ ^ 24 - (2 : ℂ) * ζ ^ 28 + (2 : ℂ) * ζ ^ 32 + (2 : ℂ) * ζ ^ 44 - ζ ^ 48 + ζ ^ 52 + ζ ^ 56)
private theorem row17_generatorB_mul_eigenbasis_5_6 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        5 6 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        5 6 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((54 / 41) : ℂ) - ((5 / 41) : ℂ) * ζ ^ 2 - ((54 / 41) : ℂ) * ζ ^ 4 - ((56 / 41) : ℂ) * ζ ^ 6 + ((143 / 82) : ℂ) * ζ ^ 8 + ((207 / 82) : ℂ) * ζ ^ 10 - ((189 / 82) : ℂ) * ζ ^ 12 - ((201 / 41) : ℂ) * ζ ^ 14 + ((93 / 82) : ℂ) * ζ ^ 16 + ((319 / 82) : ℂ) * ζ ^ 18 + ((303 / 82) : ℂ) * ζ ^ 20 - ((112 / 41) : ℂ) * ζ ^ 22 - ((85 / 41) : ℂ) * ζ ^ 24 - ((21 / 41) : ℂ) * ζ ^ 26 + ((37 / 41) : ℂ) * ζ ^ 28 + ((49 / 41) : ℂ) * ζ ^ 30 + ((19 / 41) : ℂ) * ζ ^ 32 - ((49 / 41) : ℂ) * ζ ^ 34 - ((25 / 41) : ℂ) * ζ ^ 36 - ((3 / 41) : ℂ) * ζ ^ 38 + ((25 / 41) : ℂ) * ζ ^ 40 + ((32 / 41) : ℂ) * ζ ^ 42 - ((6 / 41) : ℂ) * ζ ^ 44 - ((32 / 41) : ℂ) * ζ ^ 46 - ((18 / 41) : ℂ) * ζ ^ 48 + ((29 / 41) : ℂ) * ζ ^ 50 + ((18 / 41) : ℂ) * ζ ^ 52 + ((5 / 41) : ℂ) * ζ ^ 54 - ((24 / 41) : ℂ) * ζ ^ 56 - ((5 / 41) : ℂ) * ζ ^ 58 - ((31 / 41) : ℂ) * ζ ^ 60 + ((34 / 41) : ℂ) * ζ ^ 62 + ((31 / 41) : ℂ) * ζ ^ 64 + ((20 / 41) : ℂ) * ζ ^ 66 - ((55 / 41) : ℂ) * ζ ^ 68 - ((20 / 41) : ℂ) * ζ ^ 70 - ((1 / 41) : ℂ) * ζ ^ 72 + ((54 / 41) : ℂ) * ζ ^ 74 + ((1 / 41) : ℂ) * ζ ^ 76 - ((2 / 41) : ℂ) * ζ ^ 78 - ((56 / 41) : ℂ) * ζ ^ 80 + ((2 / 41) : ℂ) * ζ ^ 82 + ((37 / 41) : ℂ) * ζ ^ 84 + ((52 / 41) : ℂ) * ζ ^ 86 - ((37 / 41) : ℂ) * ζ ^ 88)
private theorem row17_generatorB_mul_eigenbasis_5_7 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        5 7 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        5 7 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((155 / 82) : ℂ) + ((79 / 41) : ℂ) * ζ ^ 2 - ((155 / 82) : ℂ) * ζ ^ 4 - ((50 / 41) : ℂ) * ζ ^ 6 - ((29 / 82) : ℂ) * ζ ^ 8 + ((17 / 41) : ℂ) * ζ ^ 10 + ((231 / 82) : ℂ) * ζ ^ 12 - ((14 / 41) : ℂ) * ζ ^ 14 - ((141 / 82) : ℂ) * ζ ^ 16 - ((97 / 41) : ℂ) * ζ ^ 18 + ((13 / 41) : ℂ) * ζ ^ 20 + ((64 / 41) : ℂ) * ζ ^ 22 + ((72 / 41) : ℂ) * ζ ^ 24 + ((12 / 41) : ℂ) * ζ ^ 26 - ((27 / 41) : ℂ) * ζ ^ 28 - ((28 / 41) : ℂ) * ζ ^ 30 - ((5 / 41) : ℂ) * ζ ^ 32 + ((28 / 41) : ℂ) * ζ ^ 34 + ((26 / 41) : ℂ) * ζ ^ 36 - ((10 / 41) : ℂ) * ζ ^ 38 - ((26 / 41) : ℂ) * ζ ^ 40 - ((30 / 41) : ℂ) * ζ ^ 42 + ((21 / 41) : ℂ) * ζ ^ 44 + ((30 / 41) : ℂ) * ζ ^ 46 + ((22 / 41) : ℂ) * ζ ^ 48 - ((40 / 41) : ℂ) * ζ ^ 50 - ((22 / 41) : ℂ) * ζ ^ 52 + ((3 / 41) : ℂ) * ζ ^ 54 + ((43 / 41) : ℂ) * ζ ^ 56 - ((3 / 41) : ℂ) * ζ ^ 58 + ((6 / 41) : ℂ) * ζ ^ 60 - ((37 / 41) : ℂ) * ζ ^ 62 - ((6 / 41) : ℂ) * ζ ^ 64 + ((12 / 41) : ℂ) * ζ ^ 66 + ((49 / 41) : ℂ) * ζ ^ 68 - ((12 / 41) : ℂ) * ζ ^ 70 - ((17 / 41) : ℂ) * ζ ^ 72 - ((25 / 41) : ℂ) * ζ ^ 74 + ((17 / 41) : ℂ) * ζ ^ 76 + ((7 / 41) : ℂ) * ζ ^ 78 + ((32 / 41) : ℂ) * ζ ^ 80 - ((7 / 41) : ℂ) * ζ ^ 82 - ((27 / 41) : ℂ) * ζ ^ 84 - ((18 / 41) : ℂ) * ζ ^ 86 + ((27 / 41) : ℂ) * ζ ^ 88)
private theorem row17_generatorB_mul_eigenbasis_6_0 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        6 0 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        6 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 + ((5 / 2) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 16 - (2 : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24)
private theorem row17_generatorB_mul_eigenbasis_6_1 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        6 1 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        6 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (ζ ^ 12 - ((5 / 2) : ℂ) * ζ ^ 16 + (3 : ℂ) * ζ ^ 20 - ((3 / 2) : ℂ) * ζ ^ 24)
private theorem row17_generatorB_mul_eigenbasis_6_2 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        6 2 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        6 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((32 / 41) : ℂ) - ((135 / 82) : ℂ) * ζ ^ 2 + ((32 / 41) : ℂ) * ζ ^ 4 - ((18 / 41) : ℂ) * ζ ^ 6 - ((323 / 82) : ℂ) * ζ ^ 8 + ((199 / 82) : ℂ) * ζ ^ 10 + ((165 / 41) : ℂ) * ζ ^ 12 - ((429 / 82) : ℂ) * ζ ^ 14 - ((63 / 82) : ℂ) * ζ ^ 16 + ((244 / 41) : ℂ) * ζ ^ 18 - ((145 / 41) : ℂ) * ζ ^ 20 - ((325 / 82) : ℂ) * ζ ^ 22 + ((267 / 82) : ℂ) * ζ ^ 24 + ((67 / 41) : ℂ) * ζ ^ 26)
private theorem row17_generatorB_mul_eigenbasis_6_3 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        6 3 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        6 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((93 / 41) : ℂ) + ((165 / 82) : ℂ) * ζ ^ 2 + ((93 / 41) : ℂ) * ζ ^ 4 - ((161 / 82) : ℂ) * ζ ^ 6 - ((79 / 82) : ℂ) * ζ ^ 8 + ((72 / 41) : ℂ) * ζ ^ 10 - ((171 / 82) : ℂ) * ζ ^ 12 - ((77 / 82) : ℂ) * ζ ^ 14 + ((59 / 41) : ℂ) * ζ ^ 16 - ((116 / 41) : ℂ) * ζ ^ 18 - ((5 / 41) : ℂ) * ζ ^ 20 + ((215 / 82) : ℂ) * ζ ^ 22 - ((53 / 82) : ℂ) * ζ ^ 24 - ((50 / 41) : ℂ) * ζ ^ 26)
private theorem row17_generatorB_mul_eigenbasis_6_4 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        6 4 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        6 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((81 / 22) : ℂ) - ((81 / 22) : ℂ) * ζ ^ 4 + ((21 / 22) : ℂ) * ζ ^ 8 - ((5 / 22) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 16 + ((15 / 11) : ℂ) * ζ ^ 20 + ((23 / 22) : ℂ) * ζ ^ 24 - ζ ^ 28)
private theorem row17_generatorB_mul_eigenbasis_6_5 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        6 5 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        6 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((38 / 11) : ℂ) + ((38 / 11) : ℂ) * ζ ^ 4 - ((51 / 11) : ℂ) * ζ ^ 8 + ((86 / 11) : ℂ) * ζ ^ 12 - ((169 / 22) : ℂ) * ζ ^ 16 + ((23 / 11) : ℂ) * ζ ^ 20 + ((3 / 22) : ℂ) * ζ ^ 24)
private theorem row17_generatorB_mul_eigenbasis_6_6 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        6 6 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        6 6 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((32 / 41) : ℂ) + ((135 / 82) : ℂ) * ζ ^ 2 + ((32 / 41) : ℂ) * ζ ^ 4 + ((18 / 41) : ℂ) * ζ ^ 6 - ((323 / 82) : ℂ) * ζ ^ 8 - ((199 / 82) : ℂ) * ζ ^ 10 + ((165 / 41) : ℂ) * ζ ^ 12 + ((429 / 82) : ℂ) * ζ ^ 14 - ((63 / 82) : ℂ) * ζ ^ 16 - ((244 / 41) : ℂ) * ζ ^ 18 - ((145 / 41) : ℂ) * ζ ^ 20 + ((325 / 82) : ℂ) * ζ ^ 22 + ((267 / 82) : ℂ) * ζ ^ 24 - ((67 / 41) : ℂ) * ζ ^ 26 - ζ ^ 30 + ζ ^ 34 - ζ ^ 38 - ζ ^ 50 + ζ ^ 54 - ζ ^ 58)
private theorem row17_generatorB_mul_eigenbasis_6_7 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        6 7 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        6 7 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((93 / 41) : ℂ) - ((165 / 82) : ℂ) * ζ ^ 2 + ((93 / 41) : ℂ) * ζ ^ 4 + ((161 / 82) : ℂ) * ζ ^ 6 - ((79 / 82) : ℂ) * ζ ^ 8 - ((72 / 41) : ℂ) * ζ ^ 10 - ((171 / 82) : ℂ) * ζ ^ 12 + ((77 / 82) : ℂ) * ζ ^ 14 + ((59 / 41) : ℂ) * ζ ^ 16 + ((116 / 41) : ℂ) * ζ ^ 18 - ((5 / 41) : ℂ) * ζ ^ 20 - ((215 / 82) : ℂ) * ζ ^ 22 - ((53 / 82) : ℂ) * ζ ^ 24 + ((50 / 41) : ℂ) * ζ ^ 26)
private theorem row17_generatorB_mul_eigenbasis_7_0 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        7 0 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        7 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - (3 : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 12 + ((5 / 2) : ℂ) * ζ ^ 16 - ((3 / 2) : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24)
private theorem row17_generatorB_mul_eigenbasis_7_1 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        7 1 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        7 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 ((1 : ℂ) - ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 12 + (4 : ℂ) * ζ ^ 16 - (3 : ℂ) * ζ ^ 20 + ((3 / 2) : ℂ) * ζ ^ 24)
private theorem row17_generatorB_mul_eigenbasis_7_2 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        7 2 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        7 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((161 / 82) : ℂ) - ((81 / 41) : ℂ) * ζ ^ 2 - ((161 / 82) : ℂ) * ζ ^ 4 + ((126 / 41) : ℂ) * ζ ^ 6 - ((61 / 41) : ℂ) * ζ ^ 8 - ((73 / 41) : ℂ) * ζ ^ 10 - ((25 / 82) : ℂ) * ζ ^ 12 + ((427 / 82) : ℂ) * ζ ^ 14 + ((68 / 41) : ℂ) * ζ ^ 16 - ((155 / 82) : ℂ) * ζ ^ 18 + ((335 / 82) : ℂ) * ζ ^ 20 + ((261 / 82) : ℂ) * ζ ^ 22 + ((111 / 82) : ℂ) * ζ ^ 24 + ((23 / 82) : ℂ) * ζ ^ 26)
private theorem row17_generatorB_mul_eigenbasis_7_3 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        7 3 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        7 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((113 / 82) : ℂ) - ((171 / 82) : ℂ) * ζ ^ 2 - ((113 / 82) : ℂ) * ζ ^ 4 + ((10 / 41) : ℂ) * ζ ^ 6 + ((181 / 82) : ℂ) * ζ ^ 8 + ((19 / 82) : ℂ) * ζ ^ 10 + ((54 / 41) : ℂ) * ζ ^ 12 - ((39 / 82) : ℂ) * ζ ^ 14 - ((74 / 41) : ℂ) * ζ ^ 16 + ((97 / 41) : ℂ) * ζ ^ 18 + ((37 / 82) : ℂ) * ζ ^ 20 - ((155 / 82) : ℂ) * ζ ^ 22 - ((20 / 41) : ℂ) * ζ ^ 24 - ((19 / 82) : ℂ) * ζ ^ 26)
private theorem row17_generatorB_mul_eigenbasis_7_4 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        7 4 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        7 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((47 / 22) : ℂ) + ((47 / 22) : ℂ) * ζ ^ 4 + ((39 / 11) : ℂ) * ζ ^ 8 - ((95 / 22) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 16 - ((137 / 22) : ℂ) * ζ ^ 20 - ((31 / 11) : ℂ) * ζ ^ 24)
private theorem row17_generatorB_mul_eigenbasis_7_5 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        7 5 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        7 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((45 / 11) : ℂ) - ((45 / 11) : ℂ) * ζ ^ 4 + ((69 / 22) : ℂ) * ζ ^ 8 - ((65 / 22) : ℂ) * ζ ^ 12 + (4 : ℂ) * ζ ^ 16 + ((31 / 11) : ℂ) * ζ ^ 20 + ((45 / 22) : ℂ) * ζ ^ 24 - ζ ^ 28)
private theorem row17_generatorB_mul_eigenbasis_7_6 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        7 6 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        7 6 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((161 / 82) : ℂ) + ((81 / 41) : ℂ) * ζ ^ 2 - ((161 / 82) : ℂ) * ζ ^ 4 - ((126 / 41) : ℂ) * ζ ^ 6 - ((61 / 41) : ℂ) * ζ ^ 8 + ((73 / 41) : ℂ) * ζ ^ 10 - ((25 / 82) : ℂ) * ζ ^ 12 - ((427 / 82) : ℂ) * ζ ^ 14 + ((68 / 41) : ℂ) * ζ ^ 16 + ((155 / 82) : ℂ) * ζ ^ 18 + ((335 / 82) : ℂ) * ζ ^ 20 - ((261 / 82) : ℂ) * ζ ^ 22 + ((111 / 82) : ℂ) * ζ ^ 24 - ((23 / 82) : ℂ) * ζ ^ 26)
private theorem row17_generatorB_mul_eigenbasis_7_7 :
    (alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis)
        7 7 =
      (alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal)
        7 7 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row17_matrixB,
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17GeneratorBDiagonal,
      alternatingSixAmbientRow17GeneratorBEigenvalue,
      alternatingSixAmbientRow17EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((113 / 82) : ℂ) + ((171 / 82) : ℂ) * ζ ^ 2 - ((113 / 82) : ℂ) * ζ ^ 4 - ((10 / 41) : ℂ) * ζ ^ 6 + ((181 / 82) : ℂ) * ζ ^ 8 - ((19 / 82) : ℂ) * ζ ^ 10 + ((54 / 41) : ℂ) * ζ ^ 12 + ((39 / 82) : ℂ) * ζ ^ 14 - ((74 / 41) : ℂ) * ζ ^ 16 - ((97 / 41) : ℂ) * ζ ^ 18 + ((37 / 82) : ℂ) * ζ ^ 20 + ((155 / 82) : ℂ) * ζ ^ 22 - ((20 / 41) : ℂ) * ζ ^ 24 + ((19 / 82) : ℂ) * ζ ^ 26 - ζ ^ 30 + ζ ^ 34 - ζ ^ 38 - ζ ^ 50 + ζ ^ 54 - ζ ^ 58)
/-- The checked row 17 basis diagonalizes the second
generator. -/
theorem alternatingSixAmbientRow17GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixAmbientRow17Eigenbasis =
      alternatingSixAmbientRow17Eigenbasis *
        alternatingSixAmbientRow17GeneratorBDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row17_generatorB_mul_eigenbasis_0_0
  · exact row17_generatorB_mul_eigenbasis_0_1
  · exact row17_generatorB_mul_eigenbasis_0_2
  · exact row17_generatorB_mul_eigenbasis_0_3
  · exact row17_generatorB_mul_eigenbasis_0_4
  · exact row17_generatorB_mul_eigenbasis_0_5
  · exact row17_generatorB_mul_eigenbasis_0_6
  · exact row17_generatorB_mul_eigenbasis_0_7
  · exact row17_generatorB_mul_eigenbasis_1_0
  · exact row17_generatorB_mul_eigenbasis_1_1
  · exact row17_generatorB_mul_eigenbasis_1_2
  · exact row17_generatorB_mul_eigenbasis_1_3
  · exact row17_generatorB_mul_eigenbasis_1_4
  · exact row17_generatorB_mul_eigenbasis_1_5
  · exact row17_generatorB_mul_eigenbasis_1_6
  · exact row17_generatorB_mul_eigenbasis_1_7
  · exact row17_generatorB_mul_eigenbasis_2_0
  · exact row17_generatorB_mul_eigenbasis_2_1
  · exact row17_generatorB_mul_eigenbasis_2_2
  · exact row17_generatorB_mul_eigenbasis_2_3
  · exact row17_generatorB_mul_eigenbasis_2_4
  · exact row17_generatorB_mul_eigenbasis_2_5
  · exact row17_generatorB_mul_eigenbasis_2_6
  · exact row17_generatorB_mul_eigenbasis_2_7
  · exact row17_generatorB_mul_eigenbasis_3_0
  · exact row17_generatorB_mul_eigenbasis_3_1
  · exact row17_generatorB_mul_eigenbasis_3_2
  · exact row17_generatorB_mul_eigenbasis_3_3
  · exact row17_generatorB_mul_eigenbasis_3_4
  · exact row17_generatorB_mul_eigenbasis_3_5
  · exact row17_generatorB_mul_eigenbasis_3_6
  · exact row17_generatorB_mul_eigenbasis_3_7
  · exact row17_generatorB_mul_eigenbasis_4_0
  · exact row17_generatorB_mul_eigenbasis_4_1
  · exact row17_generatorB_mul_eigenbasis_4_2
  · exact row17_generatorB_mul_eigenbasis_4_3
  · exact row17_generatorB_mul_eigenbasis_4_4
  · exact row17_generatorB_mul_eigenbasis_4_5
  · exact row17_generatorB_mul_eigenbasis_4_6
  · exact row17_generatorB_mul_eigenbasis_4_7
  · exact row17_generatorB_mul_eigenbasis_5_0
  · exact row17_generatorB_mul_eigenbasis_5_1
  · exact row17_generatorB_mul_eigenbasis_5_2
  · exact row17_generatorB_mul_eigenbasis_5_3
  · exact row17_generatorB_mul_eigenbasis_5_4
  · exact row17_generatorB_mul_eigenbasis_5_5
  · exact row17_generatorB_mul_eigenbasis_5_6
  · exact row17_generatorB_mul_eigenbasis_5_7
  · exact row17_generatorB_mul_eigenbasis_6_0
  · exact row17_generatorB_mul_eigenbasis_6_1
  · exact row17_generatorB_mul_eigenbasis_6_2
  · exact row17_generatorB_mul_eigenbasis_6_3
  · exact row17_generatorB_mul_eigenbasis_6_4
  · exact row17_generatorB_mul_eigenbasis_6_5
  · exact row17_generatorB_mul_eigenbasis_6_6
  · exact row17_generatorB_mul_eigenbasis_6_7
  · exact row17_generatorB_mul_eigenbasis_7_0
  · exact row17_generatorB_mul_eigenbasis_7_1
  · exact row17_generatorB_mul_eigenbasis_7_2
  · exact row17_generatorB_mul_eigenbasis_7_3
  · exact row17_generatorB_mul_eigenbasis_7_4
  · exact row17_generatorB_mul_eigenbasis_7_5
  · exact row17_generatorB_mul_eigenbasis_7_6
  · exact row17_generatorB_mul_eigenbasis_7_7


private theorem row17_transformedGeneratorA_0_0 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        0 0 =
      alternatingSixAmbientRow17TransformedGeneratorA
        0 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((5 / 16) : ℂ) * ζ ^ 8 - ((35 / 16) : ℂ) * ζ ^ 12 + ((49 / 16) : ℂ) * ζ ^ 16 - ((17 / 8) : ℂ) * ζ ^ 20 + ζ ^ 24 - ((7 / 4) : ℂ) * ζ ^ 28 + ((11 / 16) : ℂ) * ζ ^ 32 - ((5 / 16) : ℂ) * ζ ^ 40 - ((13 / 16) : ℂ) * ζ ^ 44 + ((15 / 8) : ℂ) * ζ ^ 48 - ((9 / 16) : ℂ) * ζ ^ 52)
private theorem row17_transformedGeneratorA_0_1 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        0 1 =
      alternatingSixAmbientRow17TransformedGeneratorA
        0 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 4 + ((9 / 8) : ℂ) * ζ ^ 8 - ((25 / 16) : ℂ) * ζ ^ 12 + ((9 / 4) : ℂ) * ζ ^ 16 - ((5 / 2) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 28 + ((9 / 8) : ℂ) * ζ ^ 32 - ((17 / 16) : ℂ) * ζ ^ 36 + ζ ^ 40 - ((19 / 16) : ℂ) * ζ ^ 44 + ((1 / 8) : ℂ) * ζ ^ 48 + ((3 / 4) : ℂ) * ζ ^ 52)
private theorem row17_transformedGeneratorA_0_2 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        0 2 =
      alternatingSixAmbientRow17TransformedGeneratorA
        0 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((61 / 82) : ℂ) - ((67 / 328) : ℂ) * ζ ^ 2 - ((61 / 82) : ℂ) * ζ ^ 4 + ((623 / 656) : ℂ) * ζ ^ 6 - ((171 / 164) : ℂ) * ζ ^ 8 - ((535 / 656) : ℂ) * ζ ^ 10 + ((223 / 328) : ℂ) * ζ ^ 12 + ((17 / 16) : ℂ) * ζ ^ 14 + ((275 / 656) : ℂ) * ζ ^ 16 - ((1 / 82) : ℂ) * ζ ^ 18 + ((79 / 82) : ℂ) * ζ ^ 20 - ((69 / 82) : ℂ) * ζ ^ 22 + ((46 / 41) : ℂ) * ζ ^ 24 + ((281 / 164) : ℂ) * ζ ^ 26 - ((389 / 656) : ℂ) * ζ ^ 28 - ((207 / 656) : ℂ) * ζ ^ 30 - ((293 / 656) : ℂ) * ζ ^ 32 - ((217 / 656) : ℂ) * ζ ^ 34 + ((35 / 41) : ℂ) * ζ ^ 36 + ((95 / 656) : ℂ) * ζ ^ 38 - ((531 / 656) : ℂ) * ζ ^ 40 + ((425 / 328) : ℂ) * ζ ^ 42 + ((107 / 164) : ℂ) * ζ ^ 44 - ((701 / 656) : ℂ) * ζ ^ 46 + ((289 / 656) : ℂ) * ζ ^ 48 + ((221 / 328) : ℂ) * ζ ^ 50 + ((57 / 328) : ℂ) * ζ ^ 52 - ((75 / 656) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_0_3 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        0 3 =
      alternatingSixAmbientRow17TransformedGeneratorA
        0 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((239 / 328) : ℂ) - ((105 / 656) : ℂ) * ζ ^ 2 + ((239 / 328) : ℂ) * ζ ^ 4 - ((7 / 164) : ℂ) * ζ ^ 6 - ((115 / 328) : ℂ) * ζ ^ 8 + ((44 / 41) : ℂ) * ζ ^ 10 + ((97 / 82) : ℂ) * ζ ^ 12 - ((5 / 8) : ℂ) * ζ ^ 14 - ((327 / 656) : ℂ) * ζ ^ 16 + ((807 / 656) : ℂ) * ζ ^ 18 - ((1433 / 656) : ℂ) * ζ ^ 20 - ((387 / 328) : ℂ) * ζ ^ 22 - ((17 / 328) : ℂ) * ζ ^ 24 - ((1105 / 656) : ℂ) * ζ ^ 26 + ((281 / 328) : ℂ) * ζ ^ 28 - ((17 / 328) : ℂ) * ζ ^ 30 - ((471 / 656) : ℂ) * ζ ^ 32 + ((411 / 656) : ℂ) * ζ ^ 34 - ((197 / 656) : ℂ) * ζ ^ 36 - ((353 / 656) : ℂ) * ζ ^ 38 + ((263 / 328) : ℂ) * ζ ^ 40 + ((337 / 328) : ℂ) * ζ ^ 42 - ((145 / 656) : ℂ) * ζ ^ 44 + ((301 / 656) : ℂ) * ζ ^ 46 - ((253 / 656) : ℂ) * ζ ^ 48 - ((179 / 328) : ℂ) * ζ ^ 50 + ((503 / 656) : ℂ) * ζ ^ 52 - ((45 / 656) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_0_4 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        0 4 =
      alternatingSixAmbientRow17TransformedGeneratorA
        0 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((10 / 11) : ℂ) - ((10 / 11) : ℂ) * ζ ^ 4 + ((1033 / 176) : ℂ) * ζ ^ 8 - ((615 / 176) : ℂ) * ζ ^ 12 - ((321 / 176) : ℂ) * ζ ^ 16 - ((83 / 88) : ℂ) * ζ ^ 20 - ((45 / 22) : ℂ) * ζ ^ 24 + ((1 / 88) : ℂ) * ζ ^ 28 + ((1213 / 176) : ℂ) * ζ ^ 32 + ((39 / 44) : ℂ) * ζ ^ 36 - ((371 / 176) : ℂ) * ζ ^ 40 - ((113 / 176) : ℂ) * ζ ^ 44 - ((41 / 22) : ℂ) * ζ ^ 48 - ((465 / 176) : ℂ) * ζ ^ 52)
private theorem row17_transformedGeneratorA_0_5 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        0 5 =
      alternatingSixAmbientRow17TransformedGeneratorA
        0 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((21 / 44) : ℂ) - ((21 / 44) : ℂ) * ζ ^ 4 - ((205 / 88) : ℂ) * ζ ^ 8 + ((267 / 176) : ℂ) * ζ ^ 12 - ((201 / 88) : ℂ) * ζ ^ 16 + ((345 / 88) : ℂ) * ζ ^ 20 - ((17 / 44) : ℂ) * ζ ^ 24 + ((10 / 11) : ℂ) * ζ ^ 28 - ((61 / 44) : ℂ) * ζ ^ 32 + ((501 / 176) : ℂ) * ζ ^ 36 - ((18 / 11) : ℂ) * ζ ^ 40 + ((431 / 176) : ℂ) * ζ ^ 44 + ((7 / 44) : ℂ) * ζ ^ 48 - ((21 / 88) : ℂ) * ζ ^ 52)
private theorem row17_transformedGeneratorA_0_6 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        0 6 =
      alternatingSixAmbientRow17TransformedGeneratorA
        0 6 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((61 / 82) : ℂ) + ((67 / 328) : ℂ) * ζ ^ 2 - ((61 / 82) : ℂ) * ζ ^ 4 - ((623 / 656) : ℂ) * ζ ^ 6 - ((171 / 164) : ℂ) * ζ ^ 8 + ((535 / 656) : ℂ) * ζ ^ 10 + ((223 / 328) : ℂ) * ζ ^ 12 - ((17 / 16) : ℂ) * ζ ^ 14 + ((275 / 656) : ℂ) * ζ ^ 16 + ((1 / 82) : ℂ) * ζ ^ 18 + ((79 / 82) : ℂ) * ζ ^ 20 + ((69 / 82) : ℂ) * ζ ^ 22 + ((46 / 41) : ℂ) * ζ ^ 24 - ((281 / 164) : ℂ) * ζ ^ 26 - ((389 / 656) : ℂ) * ζ ^ 28 + ((207 / 656) : ℂ) * ζ ^ 30 - ((293 / 656) : ℂ) * ζ ^ 32 + ((217 / 656) : ℂ) * ζ ^ 34 + ((35 / 41) : ℂ) * ζ ^ 36 - ((95 / 656) : ℂ) * ζ ^ 38 - ((531 / 656) : ℂ) * ζ ^ 40 - ((425 / 328) : ℂ) * ζ ^ 42 + ((107 / 164) : ℂ) * ζ ^ 44 + ((701 / 656) : ℂ) * ζ ^ 46 + ((289 / 656) : ℂ) * ζ ^ 48 - ((221 / 328) : ℂ) * ζ ^ 50 + ((57 / 328) : ℂ) * ζ ^ 52 + ((75 / 656) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_0_7 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        0 7 =
      alternatingSixAmbientRow17TransformedGeneratorA
        0 7 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((239 / 328) : ℂ) + ((105 / 656) : ℂ) * ζ ^ 2 + ((239 / 328) : ℂ) * ζ ^ 4 + ((7 / 164) : ℂ) * ζ ^ 6 - ((115 / 328) : ℂ) * ζ ^ 8 - ((44 / 41) : ℂ) * ζ ^ 10 + ((97 / 82) : ℂ) * ζ ^ 12 + ((5 / 8) : ℂ) * ζ ^ 14 - ((327 / 656) : ℂ) * ζ ^ 16 - ((807 / 656) : ℂ) * ζ ^ 18 - ((1433 / 656) : ℂ) * ζ ^ 20 + ((387 / 328) : ℂ) * ζ ^ 22 - ((17 / 328) : ℂ) * ζ ^ 24 + ((1105 / 656) : ℂ) * ζ ^ 26 + ((281 / 328) : ℂ) * ζ ^ 28 + ((17 / 328) : ℂ) * ζ ^ 30 - ((471 / 656) : ℂ) * ζ ^ 32 - ((411 / 656) : ℂ) * ζ ^ 34 - ((197 / 656) : ℂ) * ζ ^ 36 + ((353 / 656) : ℂ) * ζ ^ 38 + ((263 / 328) : ℂ) * ζ ^ 40 - ((337 / 328) : ℂ) * ζ ^ 42 - ((145 / 656) : ℂ) * ζ ^ 44 - ((301 / 656) : ℂ) * ζ ^ 46 - ((253 / 656) : ℂ) * ζ ^ 48 + ((179 / 328) : ℂ) * ζ ^ 50 + ((503 / 656) : ℂ) * ζ ^ 52 + ((45 / 656) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_1_0 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        1 0 =
      alternatingSixAmbientRow17TransformedGeneratorA
        1 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((29 / 16) : ℂ) + ((29 / 16) : ℂ) * ζ ^ 4 + ((29 / 16) : ℂ) * ζ ^ 8 - ((3 / 8) : ℂ) * ζ ^ 12 - ((25 / 8) : ℂ) * ζ ^ 16 + ((13 / 8) : ℂ) * ζ ^ 20 - ((17 / 16) : ℂ) * ζ ^ 24 + ((5 / 2) : ℂ) * ζ ^ 32 + ((5 / 2) : ℂ) * ζ ^ 36 - ((19 / 8) : ℂ) * ζ ^ 40 + ((11 / 16) : ℂ) * ζ ^ 44 - ((3 / 4) : ℂ) * ζ ^ 48 - ((25 / 16) : ℂ) * ζ ^ 52)
private theorem row17_transformedGeneratorA_1_1 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        1 1 =
      alternatingSixAmbientRow17TransformedGeneratorA
        1 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((7 / 8) : ℂ) + ((7 / 8) : ℂ) * ζ ^ 4 - ((47 / 16) : ℂ) * ζ ^ 8 + ((5 / 2) : ℂ) * ζ ^ 12 + ((5 / 8) : ℂ) * ζ ^ 16 + ((23 / 16) : ℂ) * ζ ^ 20 - ((1 / 16) : ℂ) * ζ ^ 28 - (4 : ℂ) * ζ ^ 32 - ((15 / 16) : ℂ) * ζ ^ 36 + ((3 / 4) : ℂ) * ζ ^ 40 + ((3 / 16) : ℂ) * ζ ^ 44 + ((15 / 8) : ℂ) * ζ ^ 48 + ((9 / 8) : ℂ) * ζ ^ 52)
private theorem row17_transformedGeneratorA_1_2 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        1 2 =
      alternatingSixAmbientRow17TransformedGeneratorA
        1 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((9 / 16) : ℂ) + ((11 / 8) : ℂ) * ζ ^ 2 + ((9 / 16) : ℂ) * ζ ^ 4 - ((23 / 16) : ℂ) * ζ ^ 6 + ((775 / 328) : ℂ) * ζ ^ 8 + ((1003 / 656) : ℂ) * ζ ^ 10 - ((239 / 656) : ℂ) * ζ ^ 12 + ((637 / 328) : ℂ) * ζ ^ 14 - ((479 / 656) : ℂ) * ζ ^ 16 - ((32 / 41) : ℂ) * ζ ^ 18 + ((411 / 328) : ℂ) * ζ ^ 20 - ((1117 / 656) : ℂ) * ζ ^ 22 - ((177 / 656) : ℂ) * ζ ^ 24 + ((307 / 656) : ℂ) * ζ ^ 26 - ((1371 / 656) : ℂ) * ζ ^ 28 - ((731 / 656) : ℂ) * ζ ^ 30 + ((1077 / 656) : ℂ) * ζ ^ 32 - ((837 / 656) : ℂ) * ζ ^ 34 - ((589 / 656) : ℂ) * ζ ^ 36 + ((2331 / 656) : ℂ) * ζ ^ 38 - ((1 / 2) : ℂ) * ζ ^ 40 - ((437 / 656) : ℂ) * ζ ^ 42 + ((1259 / 656) : ℂ) * ζ ^ 44 - ((3 / 16) : ℂ) * ζ ^ 46 - ((125 / 656) : ℂ) * ζ ^ 48 + ((345 / 328) : ℂ) * ζ ^ 50 + ((19 / 328) : ℂ) * ζ ^ 52 - ((681 / 656) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_1_3 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        1 3 =
      alternatingSixAmbientRow17TransformedGeneratorA
        1 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((21 / 16) : ℂ) - ((21 / 16) : ℂ) * ζ ^ 4 + ((3 / 8) : ℂ) * ζ ^ 6 - ((1489 / 656) : ℂ) * ζ ^ 8 - ((1317 / 656) : ℂ) * ζ ^ 10 + ((61 / 82) : ℂ) * ζ ^ 12 + ((169 / 328) : ℂ) * ζ ^ 14 + ((1041 / 656) : ℂ) * ζ ^ 16 + ((275 / 656) : ℂ) * ζ ^ 18 + ((263 / 328) : ℂ) * ζ ^ 20 + ((281 / 656) : ℂ) * ζ ^ 22 + ((119 / 164) : ℂ) * ζ ^ 24 + ((217 / 656) : ℂ) * ζ ^ 26 + ((93 / 328) : ℂ) * ζ ^ 28 + ((1103 / 656) : ℂ) * ζ ^ 30 - ((879 / 656) : ℂ) * ζ ^ 32 - ((31 / 82) : ℂ) * ζ ^ 34 - ((829 / 656) : ℂ) * ζ ^ 36 - ((379 / 328) : ℂ) * ζ ^ 38 + ((9 / 16) : ℂ) * ζ ^ 40 + ((20 / 41) : ℂ) * ζ ^ 42 - ((327 / 656) : ℂ) * ζ ^ 44 - ((19 / 16) : ℂ) * ζ ^ 46 + ((53 / 164) : ℂ) * ζ ^ 48 - ((61 / 82) : ℂ) * ζ ^ 50 + ((195 / 656) : ℂ) * ζ ^ 52 + ((313 / 656) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_1_4 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        1 4 =
      alternatingSixAmbientRow17TransformedGeneratorA
        1 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((119 / 176) : ℂ) + ((119 / 176) : ℂ) * ζ ^ 4 + ((237 / 176) : ℂ) * ζ ^ 8 - ((3 / 22) : ℂ) * ζ ^ 12 - ((13 / 4) : ℂ) * ζ ^ 16 + ((107 / 88) : ℂ) * ζ ^ 20 - ((523 / 176) : ℂ) * ζ ^ 24 + ((245 / 88) : ℂ) * ζ ^ 28 + ((423 / 88) : ℂ) * ζ ^ 32 + ((131 / 88) : ℂ) * ζ ^ 36 - ((123 / 88) : ℂ) * ζ ^ 40 - ((239 / 176) : ℂ) * ζ ^ 44 - ((189 / 88) : ℂ) * ζ ^ 48 - ((169 / 176) : ℂ) * ζ ^ 52)
private theorem row17_transformedGeneratorA_1_5 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        1 5 =
      alternatingSixAmbientRow17TransformedGeneratorA
        1 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((37 / 44) : ℂ) + ((37 / 44) : ℂ) * ζ ^ 4 + ((7 / 176) : ℂ) * ζ ^ 8 - ((51 / 44) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 16 - ((557 / 176) : ℂ) * ζ ^ 20 + ((14 / 11) : ℂ) * ζ ^ 24 - ((301 / 176) : ℂ) * ζ ^ 28 + ((191 / 88) : ℂ) * ζ ^ 32 - ((149 / 176) : ℂ) * ζ ^ 36 + ((49 / 88) : ℂ) * ζ ^ 40 + ((273 / 176) : ℂ) * ζ ^ 44 - ((127 / 88) : ℂ) * ζ ^ 48 + ((41 / 44) : ℂ) * ζ ^ 52)
private theorem row17_transformedGeneratorA_1_6 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        1 6 =
      alternatingSixAmbientRow17TransformedGeneratorA
        1 6 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((9 / 16) : ℂ) - ((11 / 8) : ℂ) * ζ ^ 2 + ((9 / 16) : ℂ) * ζ ^ 4 + ((23 / 16) : ℂ) * ζ ^ 6 + ((775 / 328) : ℂ) * ζ ^ 8 - ((1003 / 656) : ℂ) * ζ ^ 10 - ((239 / 656) : ℂ) * ζ ^ 12 - ((637 / 328) : ℂ) * ζ ^ 14 - ((479 / 656) : ℂ) * ζ ^ 16 + ((32 / 41) : ℂ) * ζ ^ 18 + ((411 / 328) : ℂ) * ζ ^ 20 + ((1117 / 656) : ℂ) * ζ ^ 22 - ((177 / 656) : ℂ) * ζ ^ 24 - ((307 / 656) : ℂ) * ζ ^ 26 - ((1371 / 656) : ℂ) * ζ ^ 28 + ((731 / 656) : ℂ) * ζ ^ 30 + ((1077 / 656) : ℂ) * ζ ^ 32 + ((837 / 656) : ℂ) * ζ ^ 34 - ((589 / 656) : ℂ) * ζ ^ 36 - ((2331 / 656) : ℂ) * ζ ^ 38 - ((1 / 2) : ℂ) * ζ ^ 40 + ((437 / 656) : ℂ) * ζ ^ 42 + ((1259 / 656) : ℂ) * ζ ^ 44 + ((3 / 16) : ℂ) * ζ ^ 46 - ((125 / 656) : ℂ) * ζ ^ 48 - ((345 / 328) : ℂ) * ζ ^ 50 + ((19 / 328) : ℂ) * ζ ^ 52 + ((681 / 656) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_1_7 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        1 7 =
      alternatingSixAmbientRow17TransformedGeneratorA
        1 7 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((21 / 16) : ℂ) - ((21 / 16) : ℂ) * ζ ^ 4 - ((3 / 8) : ℂ) * ζ ^ 6 - ((1489 / 656) : ℂ) * ζ ^ 8 + ((1317 / 656) : ℂ) * ζ ^ 10 + ((61 / 82) : ℂ) * ζ ^ 12 - ((169 / 328) : ℂ) * ζ ^ 14 + ((1041 / 656) : ℂ) * ζ ^ 16 - ((275 / 656) : ℂ) * ζ ^ 18 + ((263 / 328) : ℂ) * ζ ^ 20 - ((281 / 656) : ℂ) * ζ ^ 22 + ((119 / 164) : ℂ) * ζ ^ 24 - ((217 / 656) : ℂ) * ζ ^ 26 + ((93 / 328) : ℂ) * ζ ^ 28 - ((1103 / 656) : ℂ) * ζ ^ 30 - ((879 / 656) : ℂ) * ζ ^ 32 + ((31 / 82) : ℂ) * ζ ^ 34 - ((829 / 656) : ℂ) * ζ ^ 36 + ((379 / 328) : ℂ) * ζ ^ 38 + ((9 / 16) : ℂ) * ζ ^ 40 - ((20 / 41) : ℂ) * ζ ^ 42 - ((327 / 656) : ℂ) * ζ ^ 44 + ((19 / 16) : ℂ) * ζ ^ 46 + ((53 / 164) : ℂ) * ζ ^ 48 + ((61 / 82) : ℂ) * ζ ^ 50 + ((195 / 656) : ℂ) * ζ ^ 52 - ((313 / 656) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_2_0 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        2 0 =
      alternatingSixAmbientRow17TransformedGeneratorA
        2 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((11 / 16) : ℂ) + ((1 / 8) : ℂ) * ζ ^ 2 - ((11 / 16) : ℂ) * ζ ^ 4 + ((7 / 8) : ℂ) * ζ ^ 6 - ((17 / 16) : ℂ) * ζ ^ 8 + ((1 / 16) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 12 - ((5 / 16) : ℂ) * ζ ^ 14 + ζ ^ 16 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 - ((5 / 16) : ℂ) * ζ ^ 22 + ((1 / 8) : ℂ) * ζ ^ 24 - ((21 / 16) : ℂ) * ζ ^ 26 + ((19 / 16) : ℂ) * ζ ^ 28 - ((1 / 4) : ℂ) * ζ ^ 30 - ((23 / 16) : ℂ) * ζ ^ 32 + ((11 / 8) : ℂ) * ζ ^ 34 - ((3 / 4) : ℂ) * ζ ^ 36 - ((1 / 4) : ℂ) * ζ ^ 38 + ((9 / 16) : ℂ) * ζ ^ 40 + ((3 / 4) : ℂ) * ζ ^ 42 + ((5 / 8) : ℂ) * ζ ^ 44 + ((17 / 16) : ℂ) * ζ ^ 46 - ((17 / 16) : ℂ) * ζ ^ 48 - ((9 / 4) : ℂ) * ζ ^ 50 + ((13 / 16) : ℂ) * ζ ^ 52 - ((1 / 16) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_2_1 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        2 1 =
      alternatingSixAmbientRow17TransformedGeneratorA
        2 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((11 / 8) : ℂ) + ((3 / 2) : ℂ) * ζ ^ 2 - ((11 / 8) : ℂ) * ζ ^ 4 - ((41 / 16) : ℂ) * ζ ^ 6 - ((5 / 8) : ℂ) * ζ ^ 8 + ((15 / 8) : ℂ) * ζ ^ 10 + ((1 / 16) : ℂ) * ζ ^ 12 + ((27 / 16) : ℂ) * ζ ^ 14 - ((5 / 8) : ℂ) * ζ ^ 16 - ((13 / 16) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 20 - ((3 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 24 - ((13 / 8) : ℂ) * ζ ^ 26 + ((3 / 16) : ℂ) * ζ ^ 28 - ((5 / 16) : ℂ) * ζ ^ 30 - ((3 / 16) : ℂ) * ζ ^ 32 - ((5 / 16) : ℂ) * ζ ^ 34 + ((3 / 4) : ℂ) * ζ ^ 36 + ((35 / 16) : ℂ) * ζ ^ 38 - ((13 / 16) : ℂ) * ζ ^ 40 - ((5 / 16) : ℂ) * ζ ^ 42 + ((13 / 16) : ℂ) * ζ ^ 44 + ((1 / 2) : ℂ) * ζ ^ 46 - ((3 / 8) : ℂ) * ζ ^ 48 - ((1 / 16) : ℂ) * ζ ^ 50 - ((11 / 16) : ℂ) * ζ ^ 52 - ((1 / 16) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_2_2 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        2 2 =
      alternatingSixAmbientRow17TransformedGeneratorA
        2 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((291 / 656) : ℂ) - ((99 / 82) : ℂ) * ζ ^ 2 - ((767 / 656) : ℂ) * ζ ^ 4 + ((53 / 656) : ℂ) * ζ ^ 6 - ((39 / 82) : ℂ) * ζ ^ 8 + ((679 / 656) : ℂ) * ζ ^ 10 + ((527 / 656) : ℂ) * ζ ^ 12 + ((107 / 82) : ℂ) * ζ ^ 14 - ((75 / 164) : ℂ) * ζ ^ 16 + ((49 / 164) : ℂ) * ζ ^ 18 - ((217 / 328) : ℂ) * ζ ^ 20 - ((12 / 41) : ℂ) * ζ ^ 22 + ((103 / 328) : ℂ) * ζ ^ 24 - ((791 / 328) : ℂ) * ζ ^ 26 + ((209 / 164) : ℂ) * ζ ^ 28 - ((43 / 41) : ℂ) * ζ ^ 30 - ((755 / 656) : ℂ) * ζ ^ 32 + ((93 / 41) : ℂ) * ζ ^ 34 - ((239 / 328) : ℂ) * ζ ^ 36 + ((21 / 164) : ℂ) * ζ ^ 38 + ((1335 / 656) : ℂ) * ζ ^ 40 + ((1153 / 656) : ℂ) * ζ ^ 42 - ((1671 / 656) : ℂ) * ζ ^ 44 - ((11 / 164) : ℂ) * ζ ^ 46 + ((3 / 4) : ℂ) * ζ ^ 48 - ((483 / 164) : ℂ) * ζ ^ 50 + ((13 / 328) : ℂ) * ζ ^ 52 - ((419 / 656) : ℂ) * ζ ^ 54 - ((3 / 2) : ℂ) * ζ ^ 56)
private theorem row17_transformedGeneratorA_2_3 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        2 3 =
      alternatingSixAmbientRow17TransformedGeneratorA
        2 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((301 / 656) : ℂ) + ((25 / 656) : ℂ) * ζ ^ 2 + ((307 / 328) : ℂ) * ζ ^ 4 - ((595 / 328) : ℂ) * ζ ^ 6 + ((231 / 656) : ℂ) * ζ ^ 8 + ((68 / 41) : ℂ) * ζ ^ 10 - ((133 / 328) : ℂ) * ζ ^ 12 - ((54 / 41) : ℂ) * ζ ^ 14 - ((385 / 656) : ℂ) * ζ ^ 16 - ((261 / 328) : ℂ) * ζ ^ 18 + ((1 / 328) : ℂ) * ζ ^ 20 + ((45 / 164) : ℂ) * ζ ^ 22 - ((53 / 328) : ℂ) * ζ ^ 24 - ((46 / 41) : ℂ) * ζ ^ 26 + ((27 / 164) : ℂ) * ζ ^ 28 - ((93 / 656) : ℂ) * ζ ^ 30 + ((737 / 328) : ℂ) * ζ ^ 32 + ((327 / 656) : ℂ) * ζ ^ 34 + ((121 / 164) : ℂ) * ζ ^ 36 + ((591 / 328) : ℂ) * ζ ^ 38 - ((153 / 328) : ℂ) * ζ ^ 40 - ((653 / 656) : ℂ) * ζ ^ 42 - ((609 / 656) : ℂ) * ζ ^ 44 + ((59 / 164) : ℂ) * ζ ^ 46 - ζ ^ 48 + ((489 / 656) : ℂ) * ζ ^ 50 - ((33 / 164) : ℂ) * ζ ^ 52 - ((891 / 656) : ℂ) * ζ ^ 54 + ((3 / 4) : ℂ) * ζ ^ 56)
private theorem row17_transformedGeneratorA_2_4 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        2 4 =
      alternatingSixAmbientRow17TransformedGeneratorA
        2 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((153 / 176) : ℂ) + ((221 / 88) : ℂ) * ζ ^ 2 - ((153 / 176) : ℂ) * ζ ^ 4 + ((19 / 44) : ℂ) * ζ ^ 6 - ((433 / 176) : ℂ) * ζ ^ 8 - ((227 / 176) : ℂ) * ζ ^ 10 + ((17 / 11) : ℂ) * ζ ^ 12 - ((813 / 176) : ℂ) * ζ ^ 14 + ((151 / 88) : ℂ) * ζ ^ 16 + ((3 / 4) : ℂ) * ζ ^ 18 - ((41 / 88) : ℂ) * ζ ^ 20 + ((567 / 176) : ℂ) * ζ ^ 22 + ((141 / 88) : ℂ) * ζ ^ 24 + ((1355 / 176) : ℂ) * ζ ^ 26 - ((13 / 176) : ℂ) * ζ ^ 28 + ((257 / 88) : ℂ) * ζ ^ 30 - ((859 / 176) : ℂ) * ζ ^ 32 - ((401 / 88) : ℂ) * ζ ^ 34 - ((21 / 88) : ℂ) * ζ ^ 36 - ((719 / 88) : ℂ) * ζ ^ 38 + ((219 / 176) : ℂ) * ζ ^ 40 - ((217 / 88) : ℂ) * ζ ^ 42 + ((21 / 44) : ℂ) * ζ ^ 44 + ((21 / 176) : ℂ) * ζ ^ 46 + ((211 / 176) : ℂ) * ζ ^ 48 + ((195 / 88) : ℂ) * ζ ^ 50 + ((271 / 176) : ℂ) * ζ ^ 52 + ((725 / 176) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_2_5 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        2 5 =
      alternatingSixAmbientRow17TransformedGeneratorA
        2 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((6 / 11) : ℂ) - ((1 / 11) : ℂ) * ζ ^ 2 - ((6 / 11) : ℂ) * ζ ^ 4 - ((421 / 176) : ℂ) * ζ ^ 6 - ((17 / 88) : ℂ) * ζ ^ 8 + ((105 / 88) : ℂ) * ζ ^ 10 + ((255 / 176) : ℂ) * ζ ^ 12 + ((421 / 176) : ℂ) * ζ ^ 14 - ((9 / 88) : ℂ) * ζ ^ 16 - ((1 / 16) : ℂ) * ζ ^ 18 + ((5 / 22) : ℂ) * ζ ^ 20 - ((101 / 88) : ℂ) * ζ ^ 22 + ((19 / 44) : ℂ) * ζ ^ 24 - ((41 / 88) : ℂ) * ζ ^ 26 - ((83 / 176) : ℂ) * ζ ^ 28 - ((537 / 176) : ℂ) * ζ ^ 30 - ((179 / 176) : ℂ) * ζ ^ 32 + ((487 / 176) : ℂ) * ζ ^ 34 - ((129 / 88) : ℂ) * ζ ^ 36 + ((185 / 176) : ℂ) * ζ ^ 38 + ((217 / 176) : ℂ) * ζ ^ 40 + ((359 / 176) : ℂ) * ζ ^ 42 - ((265 / 176) : ℂ) * ζ ^ 44 - ((183 / 88) : ℂ) * ζ ^ 46 + ((10 / 11) : ℂ) * ζ ^ 48 - ((337 / 176) : ℂ) * ζ ^ 50 + ((43 / 176) : ℂ) * ζ ^ 52 + ((41 / 176) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_2_6 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        2 6 =
      alternatingSixAmbientRow17TransformedGeneratorA
        2 6 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((379 / 656) : ℂ) + ((237 / 82) : ℂ) * ζ ^ 2 + ((97 / 656) : ℂ) * ζ ^ 4 - ((1723 / 656) : ℂ) * ζ ^ 6 - ((689 / 164) : ℂ) * ζ ^ 8 + ((297 / 656) : ℂ) * ζ ^ 10 + ((1409 / 656) : ℂ) * ζ ^ 12 + ((196 / 41) : ℂ) * ζ ^ 14 + ((403 / 328) : ℂ) * ζ ^ 16 - ((617 / 164) : ℂ) * ζ ^ 18 - ((43 / 41) : ℂ) * ζ ^ 20 - ((121 / 164) : ℂ) * ζ ^ 22 + ((553 / 328) : ℂ) * ζ ^ 24 - ((133 / 328) : ℂ) * ζ ^ 26 - ((15 / 82) : ℂ) * ζ ^ 28 - ((577 / 328) : ℂ) * ζ ^ 30 - ((825 / 656) : ℂ) * ζ ^ 32 + ((219 / 164) : ℂ) * ζ ^ 34 - ((91 / 164) : ℂ) * ζ ^ 36 + ((709 / 328) : ℂ) * ζ ^ 38 - ((169 / 656) : ℂ) * ζ ^ 40 + ((1429 / 656) : ℂ) * ζ ^ 42 + ((989 / 656) : ℂ) * ζ ^ 44 - ((165 / 82) : ℂ) * ζ ^ 46 - ((19 / 82) : ℂ) * ζ ^ 48 - ((639 / 328) : ℂ) * ζ ^ 50 + ((93 / 164) : ℂ) * ζ ^ 52 - ((1139 / 656) : ℂ) * ζ ^ 54 + ((3 / 2) : ℂ) * ζ ^ 56)
private theorem row17_transformedGeneratorA_2_7 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        2 7 =
      alternatingSixAmbientRow17TransformedGeneratorA
        2 7 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((445 / 656) : ℂ) - ((117 / 656) : ℂ) * ζ ^ 2 + ((33 / 164) : ℂ) * ζ ^ 4 - ((29 / 328) : ℂ) * ζ ^ 6 + ((585 / 656) : ℂ) * ζ ^ 8 - ((15 / 41) : ℂ) * ζ ^ 10 - ((213 / 164) : ℂ) * ζ ^ 12 - ((117 / 328) : ℂ) * ζ ^ 14 + ((213 / 656) : ℂ) * ζ ^ 16 + ((65 / 82) : ℂ) * ζ ^ 18 + ((999 / 328) : ℂ) * ζ ^ 20 - ((547 / 328) : ℂ) * ζ ^ 22 - ((29 / 328) : ℂ) * ζ ^ 24 - ((93 / 41) : ℂ) * ζ ^ 26 - ((487 / 328) : ℂ) * ζ ^ 28 + ((513 / 656) : ℂ) * ζ ^ 30 - ((63 / 328) : ℂ) * ζ ^ 32 + ((665 / 656) : ℂ) * ζ ^ 34 - ((19 / 328) : ℂ) * ζ ^ 36 + ((61 / 164) : ℂ) * ζ ^ 38 - ((67 / 82) : ℂ) * ζ ^ 40 + ((513 / 656) : ℂ) * ζ ^ 42 + ((823 / 656) : ℂ) * ζ ^ 44 + ((137 / 328) : ℂ) * ζ ^ 46 + ((389 / 328) : ℂ) * ζ ^ 48 - ((37 / 656) : ℂ) * ζ ^ 50 - ((323 / 328) : ℂ) * ζ ^ 52 - ((667 / 656) : ℂ) * ζ ^ 54 - ((3 / 4) : ℂ) * ζ ^ 56)
private theorem row17_transformedGeneratorA_3_0 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        3 0 =
      alternatingSixAmbientRow17TransformedGeneratorA
        3 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((1 / 8) : ℂ) * ζ ^ 2 - ((1 / 4) : ℂ) * ζ ^ 6 - ((5 / 16) : ℂ) * ζ ^ 8 + ((3 / 16) : ℂ) * ζ ^ 10 - ((7 / 16) : ℂ) * ζ ^ 12 - ((1 / 16) : ℂ) * ζ ^ 14 + ((35 / 16) : ℂ) * ζ ^ 16 - ((5 / 8) : ℂ) * ζ ^ 18 - ζ ^ 20 + ((5 / 16) : ℂ) * ζ ^ 22 + ((5 / 16) : ℂ) * ζ ^ 24 + ((19 / 16) : ℂ) * ζ ^ 26 - ((11 / 16) : ℂ) * ζ ^ 28 - ((1 / 8) : ℂ) * ζ ^ 30 - ((1 / 4) : ℂ) * ζ ^ 32 - ζ ^ 34 - (2 : ℂ) * ζ ^ 36 + ((1 / 8) : ℂ) * ζ ^ 38 + ((5 / 4) : ℂ) * ζ ^ 40 + ((7 / 8) : ℂ) * ζ ^ 42 - ((1 / 4) : ℂ) * ζ ^ 44 - ((33 / 16) : ℂ) * ζ ^ 46 + ((11 / 16) : ℂ) * ζ ^ 48 + ((19 / 8) : ℂ) * ζ ^ 50 + ((11 / 16) : ℂ) * ζ ^ 52 - ((5 / 16) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_3_1 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        3 1 =
      alternatingSixAmbientRow17TransformedGeneratorA
        3 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((1 / 8) : ℂ) - ((9 / 8) : ℂ) * ζ ^ 2 + ((1 / 8) : ℂ) * ζ ^ 4 + ((19 / 16) : ℂ) * ζ ^ 6 + ((21 / 16) : ℂ) * ζ ^ 8 - ((3 / 8) : ℂ) * ζ ^ 10 - ((3 / 2) : ℂ) * ζ ^ 12 - ((23 / 16) : ℂ) * ζ ^ 14 + ((3 / 8) : ℂ) * ζ ^ 16 + ((15 / 16) : ℂ) * ζ ^ 18 - ((9 / 16) : ℂ) * ζ ^ 20 - ((1 / 8) : ℂ) * ζ ^ 24 + ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 28 - ((5 / 16) : ℂ) * ζ ^ 30 + ((17 / 16) : ℂ) * ζ ^ 32 + ((7 / 16) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 36 - ((15 / 16) : ℂ) * ζ ^ 38 - ((3 / 16) : ℂ) * ζ ^ 40 + ((15 / 16) : ℂ) * ζ ^ 42 + ((1 / 16) : ℂ) * ζ ^ 44 - ((13 / 8) : ℂ) * ζ ^ 46 - ((3 / 8) : ℂ) * ζ ^ 48 + ((1 / 16) : ℂ) * ζ ^ 50 - ((5 / 16) : ℂ) * ζ ^ 52 - ((11 / 16) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_3_2 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        3 2 =
      alternatingSixAmbientRow17TransformedGeneratorA
        3 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((29 / 328) : ℂ) - ((197 / 164) : ℂ) * ζ ^ 2 + ((17 / 164) : ℂ) * ζ ^ 4 + ((409 / 656) : ℂ) * ζ ^ 6 - ((601 / 328) : ℂ) * ζ ^ 8 + ((281 / 656) : ℂ) * ζ ^ 10 - ((161 / 328) : ℂ) * ζ ^ 12 - ((1633 / 656) : ℂ) * ζ ^ 14 + ζ ^ 16 + ((16 / 41) : ℂ) * ζ ^ 18 - ((33 / 328) : ℂ) * ζ ^ 20 + ((719 / 656) : ℂ) * ζ ^ 22 - ((363 / 656) : ℂ) * ζ ^ 24 - ((493 / 656) : ℂ) * ζ ^ 26 + ((28 / 41) : ℂ) * ζ ^ 28 - ((107 / 328) : ℂ) * ζ ^ 30 - ((409 / 656) : ℂ) * ζ ^ 32 + ((397 / 328) : ℂ) * ζ ^ 34 + ((1 / 656) : ℂ) * ζ ^ 36 - ((405 / 328) : ℂ) * ζ ^ 38 + ((75 / 328) : ℂ) * ζ ^ 40 - ((211 / 328) : ℂ) * ζ ^ 42 - ((16 / 41) : ℂ) * ζ ^ 44 + ((44 / 41) : ℂ) * ζ ^ 46 + ((301 / 328) : ℂ) * ζ ^ 48 + ((133 / 328) : ℂ) * ζ ^ 50 - ((1 / 2) : ℂ) * ζ ^ 52 - ((13 / 656) : ℂ) * ζ ^ 54 + ((129 / 328) : ℂ) * ζ ^ 56)
private theorem row17_transformedGeneratorA_3_3 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        3 3 =
      alternatingSixAmbientRow17TransformedGeneratorA
        3 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((61 / 164) : ℂ) - ((97 / 328) : ℂ) * ζ ^ 2 + ((131 / 656) : ℂ) * ζ ^ 4 + ((217 / 328) : ℂ) * ζ ^ 6 + ((279 / 328) : ℂ) * ζ ^ 8 + ((595 / 656) : ℂ) * ζ ^ 10 - ((31 / 328) : ℂ) * ζ ^ 12 - ((83 / 164) : ℂ) * ζ ^ 14 - ((15 / 16) : ℂ) * ζ ^ 16 + ((577 / 328) : ℂ) * ζ ^ 18 - ((97 / 656) : ℂ) * ζ ^ 20 - ((569 / 656) : ℂ) * ζ ^ 22 + ((5 / 164) : ℂ) * ζ ^ 24 + ((47 / 164) : ℂ) * ζ ^ 26 - ((105 / 164) : ℂ) * ζ ^ 28 - ((261 / 328) : ℂ) * ζ ^ 30 - ((135 / 328) : ℂ) * ζ ^ 32 + ((33 / 164) : ℂ) * ζ ^ 34 + ((117 / 164) : ℂ) * ζ ^ 36 - ((35 / 656) : ℂ) * ζ ^ 38 + ((49 / 656) : ℂ) * ζ ^ 40 - ((163 / 656) : ℂ) * ζ ^ 42 + ((609 / 656) : ℂ) * ζ ^ 44 + ((203 / 328) : ℂ) * ζ ^ 46 + ((107 / 656) : ℂ) * ζ ^ 48 - ((521 / 656) : ℂ) * ζ ^ 50 + ((3 / 8) : ℂ) * ζ ^ 52 + ((189 / 656) : ℂ) * ζ ^ 54 - ((21 / 328) : ℂ) * ζ ^ 56)
private theorem row17_transformedGeneratorA_3_4 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        3 4 =
      alternatingSixAmbientRow17TransformedGeneratorA
        3 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((7 / 44) : ℂ) - ((149 / 88) : ℂ) * ζ ^ 2 - ((7 / 44) : ℂ) * ζ ^ 4 + ((13 / 88) : ℂ) * ζ ^ 6 + ((131 / 176) : ℂ) * ζ ^ 8 - ((1 / 176) : ℂ) * ζ ^ 10 - ((205 / 176) : ℂ) * ζ ^ 12 + ((515 / 176) : ℂ) * ζ ^ 14 + ((205 / 176) : ℂ) * ζ ^ 16 + ((19 / 88) : ℂ) * ζ ^ 18 - ((221 / 88) : ℂ) * ζ ^ 20 - ((259 / 176) : ℂ) * ζ ^ 22 + ((159 / 176) : ℂ) * ζ ^ 24 - ((261 / 176) : ℂ) * ζ ^ 26 + ((65 / 176) : ℂ) * ζ ^ 28 - ((27 / 22) : ℂ) * ζ ^ 30 + ((41 / 22) : ℂ) * ζ ^ 32 + ((19 / 22) : ℂ) * ζ ^ 34 - ((7 / 22) : ℂ) * ζ ^ 36 + ((21 / 22) : ℂ) * ζ ^ 38 - ((19 / 44) : ℂ) * ζ ^ 40 + ((117 / 44) : ℂ) * ζ ^ 42 - ((45 / 44) : ℂ) * ζ ^ 44 - ((201 / 176) : ℂ) * ζ ^ 46 - ((257 / 176) : ℂ) * ζ ^ 48 + ((61 / 22) : ℂ) * ζ ^ 50 - ((9 / 16) : ℂ) * ζ ^ 52 + ((85 / 176) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_3_5 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        3 5 =
      alternatingSixAmbientRow17TransformedGeneratorA
        3 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((13 / 88) : ℂ) - ((29 / 88) : ℂ) * ζ ^ 2 + ((13 / 88) : ℂ) * ζ ^ 4 + ((199 / 176) : ℂ) * ζ ^ 6 - ((113 / 176) : ℂ) * ζ ^ 8 + ((81 / 88) : ℂ) * ζ ^ 10 + ((17 / 88) : ℂ) * ζ ^ 12 - ((413 / 176) : ℂ) * ζ ^ 14 + ((5 / 88) : ℂ) * ζ ^ 16 + ((125 / 176) : ℂ) * ζ ^ 18 + ((357 / 176) : ℂ) * ζ ^ 20 + ((13 / 88) : ℂ) * ζ ^ 22 - ((119 / 88) : ℂ) * ζ ^ 24 - ((61 / 44) : ℂ) * ζ ^ 26 + ((81 / 88) : ℂ) * ζ ^ 28 + ((111 / 176) : ℂ) * ζ ^ 30 - ((347 / 176) : ℂ) * ζ ^ 32 - ((61 / 176) : ℂ) * ζ ^ 34 - ((7 / 88) : ℂ) * ζ ^ 36 - ((189 / 176) : ℂ) * ζ ^ 38 + ((69 / 176) : ℂ) * ζ ^ 40 - ((37 / 176) : ℂ) * ζ ^ 42 + ((43 / 176) : ℂ) * ζ ^ 44 + ((7 / 11) : ℂ) * ζ ^ 46 + ((115 / 88) : ℂ) * ζ ^ 48 - ((131 / 176) : ℂ) * ζ ^ 50 - ((5 / 16) : ℂ) * ζ ^ 52 - ((185 / 176) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_3_6 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        3 6 =
      alternatingSixAmbientRow17TransformedGeneratorA
        3 6 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((115 / 328) : ℂ) - ((65 / 82) : ℂ) * ζ ^ 2 + ((13 / 82) : ℂ) * ζ ^ 4 + ((721 / 656) : ℂ) * ζ ^ 6 + ((119 / 328) : ℂ) * ζ ^ 8 + ((199 / 656) : ℂ) * ζ ^ 10 - ((135 / 164) : ℂ) * ζ ^ 12 - ((1315 / 656) : ℂ) * ζ ^ 14 + ((305 / 328) : ℂ) * ζ ^ 16 + ((221 / 164) : ℂ) * ζ ^ 18 + ((47 / 41) : ℂ) * ζ ^ 20 - ((295 / 656) : ℂ) * ζ ^ 22 - ((947 / 656) : ℂ) * ζ ^ 24 - ((715 / 656) : ℂ) * ζ ^ 26 + ((50 / 41) : ℂ) * ζ ^ 28 + ((34 / 41) : ℂ) * ζ ^ 30 - ((491 / 656) : ℂ) * ζ ^ 32 - ((303 / 328) : ℂ) * ζ ^ 34 - ((465 / 656) : ℂ) * ζ ^ 36 + ((49 / 41) : ℂ) * ζ ^ 38 + ((279 / 328) : ℂ) * ζ ^ 40 - ((115 / 82) : ℂ) * ζ ^ 42 - ((7 / 41) : ℂ) * ζ ^ 44 + ((30 / 41) : ℂ) * ζ ^ 46 + ((191 / 328) : ℂ) * ζ ^ 48 + ((151 / 164) : ℂ) * ζ ^ 50 + ((27 / 328) : ℂ) * ζ ^ 52 - ((709 / 656) : ℂ) * ζ ^ 54 - ((129 / 328) : ℂ) * ζ ^ 56)
private theorem row17_transformedGeneratorA_3_7 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        3 7 =
      alternatingSixAmbientRow17TransformedGeneratorA
        3 7 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((55 / 164) : ℂ) - ((197 / 328) : ℂ) * ζ ^ 2 + ((333 / 656) : ℂ) * ζ ^ 4 + ((327 / 328) : ℂ) * ζ ^ 6 + ((253 / 164) : ℂ) * ζ ^ 8 - ((799 / 656) : ℂ) * ζ ^ 10 + ((1 / 164) : ℂ) * ζ ^ 12 - ((87 / 328) : ℂ) * ζ ^ 14 - ((741 / 656) : ℂ) * ζ ^ 16 + ((95 / 82) : ℂ) * ζ ^ 18 - ((869 / 656) : ℂ) * ζ ^ 20 + ((479 / 656) : ℂ) * ζ ^ 22 - ((17 / 164) : ℂ) * ζ ^ 24 + ((95 / 82) : ℂ) * ζ ^ 26 + ((35 / 328) : ℂ) * ζ ^ 28 - ((9 / 328) : ℂ) * ζ ^ 30 + ((29 / 328) : ℂ) * ζ ^ 32 + ((69 / 164) : ℂ) * ζ ^ 34 + ((537 / 328) : ℂ) * ζ ^ 36 - ((1063 / 656) : ℂ) * ζ ^ 38 + ((15 / 656) : ℂ) * ζ ^ 40 - ((593 / 656) : ℂ) * ζ ^ 42 - ((387 / 656) : ℂ) * ζ ^ 44 - ((5 / 82) : ℂ) * ζ ^ 46 + ((221 / 656) : ℂ) * ζ ^ 48 - ((679 / 656) : ℂ) * ζ ^ 50 + ((1 / 41) : ℂ) * ζ ^ 52 + ((493 / 656) : ℂ) * ζ ^ 54 + ((21 / 328) : ℂ) * ζ ^ 56)
private theorem row17_transformedGeneratorA_4_0 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        4 0 =
      alternatingSixAmbientRow17TransformedGeneratorA
        4 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((3 / 8) : ℂ) + ((3 / 8) : ℂ) * ζ ^ 4 + ((37 / 16) : ℂ) * ζ ^ 8 - ((5 / 16) : ℂ) * ζ ^ 12 - ((25 / 16) : ℂ) * ζ ^ 16 - ((3 / 8) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24 - ((5 / 8) : ℂ) * ζ ^ 28 + ((35 / 16) : ℂ) * ζ ^ 32 + ((3 / 2) : ℂ) * ζ ^ 36 - ((13 / 16) : ℂ) * ζ ^ 40 - ((7 / 16) : ℂ) * ζ ^ 44 + ((1 / 4) : ℂ) * ζ ^ 48 - ((17 / 16) : ℂ) * ζ ^ 52)
private theorem row17_transformedGeneratorA_4_1 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        4 1 =
      alternatingSixAmbientRow17TransformedGeneratorA
        4 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 + ((9 / 8) : ℂ) * ζ ^ 8 - ((1 / 16) : ℂ) * ζ ^ 12 - ζ ^ 20 - ζ ^ 24 - ((1 / 8) : ℂ) * ζ ^ 28 - ((3 / 4) : ℂ) * ζ ^ 32 - ((7 / 16) : ℂ) * ζ ^ 36 + ((5 / 8) : ℂ) * ζ ^ 40 - ((7 / 16) : ℂ) * ζ ^ 44 + ((5 / 8) : ℂ) * ζ ^ 48 + ((5 / 8) : ℂ) * ζ ^ 52)
private theorem row17_transformedGeneratorA_4_2 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        4 2 =
      alternatingSixAmbientRow17TransformedGeneratorA
        4 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((135 / 328) : ℂ) + ((131 / 328) : ℂ) * ζ ^ 2 + ((135 / 328) : ℂ) * ζ ^ 4 - ((567 / 656) : ℂ) * ζ ^ 6 + ((48 / 41) : ℂ) * ζ ^ 8 - ((103 / 656) : ℂ) * ζ ^ 10 - ((175 / 328) : ℂ) * ζ ^ 12 + ((191 / 656) : ℂ) * ζ ^ 14 - ((1141 / 656) : ℂ) * ζ ^ 16 - ((10 / 41) : ℂ) * ζ ^ 18 - ((3 / 328) : ℂ) * ζ ^ 20 - ((165 / 164) : ℂ) * ζ ^ 22 - ((47 / 82) : ℂ) * ζ ^ 24 + ((56 / 41) : ℂ) * ζ ^ 26 - ((327 / 656) : ℂ) * ζ ^ 28 - ((259 / 656) : ℂ) * ζ ^ 30 + ((1873 / 656) : ℂ) * ζ ^ 32 - ((395 / 656) : ℂ) * ζ ^ 34 + ((141 / 328) : ℂ) * ζ ^ 36 + ((1239 / 656) : ℂ) * ζ ^ 38 - ((635 / 656) : ℂ) * ζ ^ 40 - ((7 / 8) : ℂ) * ζ ^ 42 + ((127 / 328) : ℂ) * ζ ^ 44 - ((575 / 656) : ℂ) * ζ ^ 46 - ((629 / 656) : ℂ) * ζ ^ 48 + ((53 / 164) : ℂ) * ζ ^ 50 - ((32 / 41) : ℂ) * ζ ^ 52 - ((645 / 656) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_4_3 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        4 3 =
      alternatingSixAmbientRow17TransformedGeneratorA
        4 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((5 / 41) : ℂ) + ((395 / 656) : ℂ) * ζ ^ 2 + ((5 / 41) : ℂ) * ζ ^ 4 - ((21 / 82) : ℂ) * ζ ^ 6 - ((73 / 328) : ℂ) * ζ ^ 8 - ((19 / 82) : ℂ) * ζ ^ 10 - ((269 / 328) : ℂ) * ζ ^ 12 + ((1 / 82) : ℂ) * ζ ^ 14 + ((611 / 656) : ℂ) * ζ ^ 16 + ((27 / 656) : ℂ) * ζ ^ 18 - ((471 / 656) : ℂ) * ζ ^ 20 + ((65 / 164) : ℂ) * ζ ^ 22 - ((285 / 328) : ℂ) * ζ ^ 24 - ((143 / 656) : ℂ) * ζ ^ 26 + ((19 / 41) : ℂ) * ζ ^ 28 + ((40 / 41) : ℂ) * ζ ^ 30 - ((877 / 656) : ℂ) * ζ ^ 32 - ((73 / 656) : ℂ) * ζ ^ 34 - ((249 / 656) : ℂ) * ζ ^ 36 - ((585 / 656) : ℂ) * ζ ^ 38 + ((79 / 164) : ℂ) * ζ ^ 40 + ((3 / 4) : ℂ) * ζ ^ 42 - ((69 / 656) : ℂ) * ζ ^ 44 - ((263 / 656) : ℂ) * ζ ^ 46 + ((131 / 656) : ℂ) * ζ ^ 48 - ((21 / 82) : ℂ) * ζ ^ 50 + ((275 / 656) : ℂ) * ζ ^ 52 + ((269 / 656) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_4_4 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        4 4 =
      alternatingSixAmbientRow17TransformedGeneratorA
        4 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((5 / 88) : ℂ) + ((5 / 88) : ℂ) * ζ ^ 4 + ((273 / 176) : ℂ) * ζ ^ 8 - ((57 / 176) : ℂ) * ζ ^ 12 + ((13 / 176) : ℂ) * ζ ^ 16 + ((125 / 88) : ℂ) * ζ ^ 20 - ((9 / 44) : ℂ) * ζ ^ 24 + ((3 / 22) : ℂ) * ζ ^ 28 + ((505 / 176) : ℂ) * ζ ^ 32 - ((9 / 22) : ℂ) * ζ ^ 36 - ((67 / 176) : ℂ) * ζ ^ 40 - ((5 / 16) : ℂ) * ζ ^ 44 - ((47 / 88) : ℂ) * ζ ^ 48 - ((7 / 16) : ℂ) * ζ ^ 52)
private theorem row17_transformedGeneratorA_4_5 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        4 5 =
      alternatingSixAmbientRow17TransformedGeneratorA
        4 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((57 / 44) : ℂ) + ((57 / 44) : ℂ) * ζ ^ 4 + ((63 / 88) : ℂ) * ζ ^ 8 - ((193 / 176) : ℂ) * ζ ^ 12 - ((173 / 88) : ℂ) * ζ ^ 16 - ((21 / 88) : ℂ) * ζ ^ 20 - ((71 / 44) : ℂ) * ζ ^ 24 + ((3 / 88) : ℂ) * ζ ^ 28 + ((301 / 88) : ℂ) * ζ ^ 32 + ((15 / 176) : ℂ) * ζ ^ 36 - ((73 / 88) : ℂ) * ζ ^ 40 + ((9 / 16) : ℂ) * ζ ^ 44 - ((87 / 44) : ℂ) * ζ ^ 48 - ((1 / 4) : ℂ) * ζ ^ 52)
private theorem row17_transformedGeneratorA_4_6 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        4 6 =
      alternatingSixAmbientRow17TransformedGeneratorA
        4 6 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((135 / 328) : ℂ) - ((131 / 328) : ℂ) * ζ ^ 2 + ((135 / 328) : ℂ) * ζ ^ 4 + ((567 / 656) : ℂ) * ζ ^ 6 + ((48 / 41) : ℂ) * ζ ^ 8 + ((103 / 656) : ℂ) * ζ ^ 10 - ((175 / 328) : ℂ) * ζ ^ 12 - ((191 / 656) : ℂ) * ζ ^ 14 - ((1141 / 656) : ℂ) * ζ ^ 16 + ((10 / 41) : ℂ) * ζ ^ 18 - ((3 / 328) : ℂ) * ζ ^ 20 + ((165 / 164) : ℂ) * ζ ^ 22 - ((47 / 82) : ℂ) * ζ ^ 24 - ((56 / 41) : ℂ) * ζ ^ 26 - ((327 / 656) : ℂ) * ζ ^ 28 + ((259 / 656) : ℂ) * ζ ^ 30 + ((1873 / 656) : ℂ) * ζ ^ 32 + ((395 / 656) : ℂ) * ζ ^ 34 + ((141 / 328) : ℂ) * ζ ^ 36 - ((1239 / 656) : ℂ) * ζ ^ 38 - ((635 / 656) : ℂ) * ζ ^ 40 + ((7 / 8) : ℂ) * ζ ^ 42 + ((127 / 328) : ℂ) * ζ ^ 44 + ((575 / 656) : ℂ) * ζ ^ 46 - ((629 / 656) : ℂ) * ζ ^ 48 - ((53 / 164) : ℂ) * ζ ^ 50 - ((32 / 41) : ℂ) * ζ ^ 52 + ((645 / 656) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_4_7 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        4 7 =
      alternatingSixAmbientRow17TransformedGeneratorA
        4 7 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((5 / 41) : ℂ) - ((395 / 656) : ℂ) * ζ ^ 2 + ((5 / 41) : ℂ) * ζ ^ 4 + ((21 / 82) : ℂ) * ζ ^ 6 - ((73 / 328) : ℂ) * ζ ^ 8 + ((19 / 82) : ℂ) * ζ ^ 10 - ((269 / 328) : ℂ) * ζ ^ 12 - ((1 / 82) : ℂ) * ζ ^ 14 + ((611 / 656) : ℂ) * ζ ^ 16 - ((27 / 656) : ℂ) * ζ ^ 18 - ((471 / 656) : ℂ) * ζ ^ 20 - ((65 / 164) : ℂ) * ζ ^ 22 - ((285 / 328) : ℂ) * ζ ^ 24 + ((143 / 656) : ℂ) * ζ ^ 26 + ((19 / 41) : ℂ) * ζ ^ 28 - ((40 / 41) : ℂ) * ζ ^ 30 - ((877 / 656) : ℂ) * ζ ^ 32 + ((73 / 656) : ℂ) * ζ ^ 34 - ((249 / 656) : ℂ) * ζ ^ 36 + ((585 / 656) : ℂ) * ζ ^ 38 + ((79 / 164) : ℂ) * ζ ^ 40 - ((3 / 4) : ℂ) * ζ ^ 42 - ((69 / 656) : ℂ) * ζ ^ 44 + ((263 / 656) : ℂ) * ζ ^ 46 + ((131 / 656) : ℂ) * ζ ^ 48 + ((21 / 82) : ℂ) * ζ ^ 50 + ((275 / 656) : ℂ) * ζ ^ 52 - ((269 / 656) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_5_0 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        5 0 =
      alternatingSixAmbientRow17TransformedGeneratorA
        5 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((29 / 16) : ℂ) - ((29 / 16) : ℂ) * ζ ^ 4 - ((3 / 16) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 16 - ((5 / 8) : ℂ) * ζ ^ 20 + ((7 / 16) : ℂ) * ζ ^ 24 + ((11 / 8) : ℂ) * ζ ^ 28 - (2 : ℂ) * ζ ^ 32 + ((3 / 2) : ℂ) * ζ ^ 36 - ((1 / 8) : ℂ) * ζ ^ 40 - ((3 / 16) : ℂ) * ζ ^ 44 - ((5 / 8) : ℂ) * ζ ^ 48 + ((3 / 16) : ℂ) * ζ ^ 52)
private theorem row17_transformedGeneratorA_5_1 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        5 1 =
      alternatingSixAmbientRow17TransformedGeneratorA
        5 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((9 / 8) : ℂ) - ((9 / 8) : ℂ) * ζ ^ 4 + ((21 / 16) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 12 - ((3 / 8) : ℂ) * ζ ^ 16 - ((5 / 16) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24 + ((9 / 16) : ℂ) * ζ ^ 28 + ((15 / 8) : ℂ) * ζ ^ 32 + ((7 / 16) : ℂ) * ζ ^ 36 - ((3 / 8) : ℂ) * ζ ^ 40 - ((5 / 16) : ℂ) * ζ ^ 44 - ((9 / 8) : ℂ) * ζ ^ 48 - ((1 / 2) : ℂ) * ζ ^ 52)
private theorem row17_transformedGeneratorA_5_2 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        5 2 =
      alternatingSixAmbientRow17TransformedGeneratorA
        5 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((141 / 656) : ℂ) - ((293 / 328) : ℂ) * ζ ^ 2 - ((141 / 656) : ℂ) * ζ ^ 4 + ((743 / 656) : ℂ) * ζ ^ 6 - ((341 / 328) : ℂ) * ζ ^ 8 - ((573 / 656) : ℂ) * ζ ^ 10 + ((813 / 656) : ℂ) * ζ ^ 12 - ((355 / 164) : ℂ) * ζ ^ 14 - ((499 / 656) : ℂ) * ζ ^ 16 + ((265 / 164) : ℂ) * ζ ^ 18 - ((473 / 164) : ℂ) * ζ ^ 20 + ((183 / 656) : ℂ) * ζ ^ 22 + ((1487 / 656) : ℂ) * ζ ^ 24 - ((529 / 656) : ℂ) * ζ ^ 26 + ((3 / 16) : ℂ) * ζ ^ 28 + ((1489 / 656) : ℂ) * ζ ^ 30 - ((177 / 656) : ℂ) * ζ ^ 32 - ((563 / 656) : ℂ) * ζ ^ 34 + ((1053 / 656) : ℂ) * ζ ^ 36 - ((737 / 656) : ℂ) * ζ ^ 38 - ((95 / 164) : ℂ) * ζ ^ 40 - ((61 / 656) : ℂ) * ζ ^ 42 - ((891 / 656) : ℂ) * ζ ^ 44 - ((101 / 656) : ℂ) * ζ ^ 46 - ((859 / 656) : ℂ) * ζ ^ 48 - ((22 / 41) : ℂ) * ζ ^ 50 + ((59 / 164) : ℂ) * ζ ^ 52 - ((15 / 656) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_5_3 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        5 3 =
      alternatingSixAmbientRow17TransformedGeneratorA
        5 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((19 / 656) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 - ((19 / 656) : ℂ) * ζ ^ 4 - ((101 / 328) : ℂ) * ζ ^ 6 + ((255 / 656) : ℂ) * ζ ^ 8 + ((99 / 656) : ℂ) * ζ ^ 10 - ((39 / 328) : ℂ) * ζ ^ 12 - ((49 / 164) : ℂ) * ζ ^ 14 - ((37 / 656) : ℂ) * ζ ^ 16 - ((717 / 656) : ℂ) * ζ ^ 18 + ((141 / 82) : ℂ) * ζ ^ 20 + ((815 / 656) : ℂ) * ζ ^ 22 - ((107 / 164) : ℂ) * ζ ^ 24 + ((355 / 656) : ℂ) * ζ ^ 26 + ((1 / 4) : ℂ) * ζ ^ 28 - ((599 / 656) : ℂ) * ζ ^ 30 + ((1091 / 656) : ℂ) * ζ ^ 32 + ((49 / 82) : ℂ) * ζ ^ 34 - ((713 / 656) : ℂ) * ζ ^ 36 - ((135 / 328) : ℂ) * ζ ^ 38 - ((433 / 656) : ℂ) * ζ ^ 40 - ((375 / 328) : ℂ) * ζ ^ 42 + ((105 / 656) : ℂ) * ζ ^ 44 + ((333 / 656) : ℂ) * ζ ^ 46 - ((135 / 164) : ℂ) * ζ ^ 48 + ((165 / 328) : ℂ) * ζ ^ 50 - ((457 / 656) : ℂ) * ζ ^ 52 - ((9 / 656) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_5_4 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        5 4 =
      alternatingSixAmbientRow17TransformedGeneratorA
        5 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((351 / 176) : ℂ) - ((351 / 176) : ℂ) * ζ ^ 4 - ((547 / 176) : ℂ) * ζ ^ 8 + ((137 / 88) : ℂ) * ζ ^ 12 + ((161 / 88) : ℂ) * ζ ^ 16 + ((21 / 8) : ℂ) * ζ ^ 20 + ((205 / 176) : ℂ) * ζ ^ 24 - ((155 / 44) : ℂ) * ζ ^ 28 - ((751 / 88) : ℂ) * ζ ^ 32 - ((75 / 88) : ℂ) * ζ ^ 36 + ((199 / 88) : ℂ) * ζ ^ 40 + ((599 / 176) : ℂ) * ζ ^ 44 + ((223 / 44) : ℂ) * ζ ^ 48 + ((367 / 176) : ℂ) * ζ ^ 52)
private theorem row17_transformedGeneratorA_5_5 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        5 5 =
      alternatingSixAmbientRow17TransformedGeneratorA
        5 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((1 / 22) : ℂ) - ((1 / 22) : ℂ) * ζ ^ 4 + ((75 / 176) : ℂ) * ζ ^ 8 + ((23 / 22) : ℂ) * ζ ^ 12 - ((39 / 44) : ℂ) * ζ ^ 16 - ((23 / 16) : ℂ) * ζ ^ 20 + ((63 / 44) : ℂ) * ζ ^ 24 - ((23 / 176) : ℂ) * ζ ^ 28 + ((39 / 22) : ℂ) * ζ ^ 32 + ((177 / 176) : ℂ) * ζ ^ 36 - ((59 / 44) : ℂ) * ζ ^ 40 - ((359 / 176) : ℂ) * ζ ^ 44 - ((103 / 88) : ℂ) * ζ ^ 48 - ((27 / 88) : ℂ) * ζ ^ 52)
private theorem row17_transformedGeneratorA_5_6 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        5 6 =
      alternatingSixAmbientRow17TransformedGeneratorA
        5 6 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((141 / 656) : ℂ) + ((293 / 328) : ℂ) * ζ ^ 2 - ((141 / 656) : ℂ) * ζ ^ 4 - ((743 / 656) : ℂ) * ζ ^ 6 - ((341 / 328) : ℂ) * ζ ^ 8 + ((573 / 656) : ℂ) * ζ ^ 10 + ((813 / 656) : ℂ) * ζ ^ 12 + ((355 / 164) : ℂ) * ζ ^ 14 - ((499 / 656) : ℂ) * ζ ^ 16 - ((265 / 164) : ℂ) * ζ ^ 18 - ((473 / 164) : ℂ) * ζ ^ 20 - ((183 / 656) : ℂ) * ζ ^ 22 + ((1487 / 656) : ℂ) * ζ ^ 24 + ((529 / 656) : ℂ) * ζ ^ 26 + ((3 / 16) : ℂ) * ζ ^ 28 - ((1489 / 656) : ℂ) * ζ ^ 30 - ((177 / 656) : ℂ) * ζ ^ 32 + ((563 / 656) : ℂ) * ζ ^ 34 + ((1053 / 656) : ℂ) * ζ ^ 36 + ((737 / 656) : ℂ) * ζ ^ 38 - ((95 / 164) : ℂ) * ζ ^ 40 + ((61 / 656) : ℂ) * ζ ^ 42 - ((891 / 656) : ℂ) * ζ ^ 44 + ((101 / 656) : ℂ) * ζ ^ 46 - ((859 / 656) : ℂ) * ζ ^ 48 + ((22 / 41) : ℂ) * ζ ^ 50 + ((59 / 164) : ℂ) * ζ ^ 52 + ((15 / 656) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_5_7 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        5 7 =
      alternatingSixAmbientRow17TransformedGeneratorA
        5 7 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((19 / 656) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 - ((19 / 656) : ℂ) * ζ ^ 4 + ((101 / 328) : ℂ) * ζ ^ 6 + ((255 / 656) : ℂ) * ζ ^ 8 - ((99 / 656) : ℂ) * ζ ^ 10 - ((39 / 328) : ℂ) * ζ ^ 12 + ((49 / 164) : ℂ) * ζ ^ 14 - ((37 / 656) : ℂ) * ζ ^ 16 + ((717 / 656) : ℂ) * ζ ^ 18 + ((141 / 82) : ℂ) * ζ ^ 20 - ((815 / 656) : ℂ) * ζ ^ 22 - ((107 / 164) : ℂ) * ζ ^ 24 - ((355 / 656) : ℂ) * ζ ^ 26 + ((1 / 4) : ℂ) * ζ ^ 28 + ((599 / 656) : ℂ) * ζ ^ 30 + ((1091 / 656) : ℂ) * ζ ^ 32 - ((49 / 82) : ℂ) * ζ ^ 34 - ((713 / 656) : ℂ) * ζ ^ 36 + ((135 / 328) : ℂ) * ζ ^ 38 - ((433 / 656) : ℂ) * ζ ^ 40 + ((375 / 328) : ℂ) * ζ ^ 42 + ((105 / 656) : ℂ) * ζ ^ 44 - ((333 / 656) : ℂ) * ζ ^ 46 - ((135 / 164) : ℂ) * ζ ^ 48 - ((165 / 328) : ℂ) * ζ ^ 50 - ((457 / 656) : ℂ) * ζ ^ 52 + ((9 / 656) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_6_0 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        6 0 =
      alternatingSixAmbientRow17TransformedGeneratorA
        6 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((11 / 16) : ℂ) - ((1 / 8) : ℂ) * ζ ^ 2 - ((11 / 16) : ℂ) * ζ ^ 4 - ((7 / 8) : ℂ) * ζ ^ 6 - ((17 / 16) : ℂ) * ζ ^ 8 - ((1 / 16) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 12 + ((5 / 16) : ℂ) * ζ ^ 14 + ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 + ((5 / 16) : ℂ) * ζ ^ 22 + ((1 / 8) : ℂ) * ζ ^ 24 + ((21 / 16) : ℂ) * ζ ^ 26 + ((19 / 16) : ℂ) * ζ ^ 28 + ((1 / 4) : ℂ) * ζ ^ 30 - ((23 / 16) : ℂ) * ζ ^ 32 - ((11 / 8) : ℂ) * ζ ^ 34 - ((3 / 4) : ℂ) * ζ ^ 36 + ((1 / 4) : ℂ) * ζ ^ 38 + ((9 / 16) : ℂ) * ζ ^ 40 - ((3 / 4) : ℂ) * ζ ^ 42 + ((5 / 8) : ℂ) * ζ ^ 44 - ((17 / 16) : ℂ) * ζ ^ 46 - ((17 / 16) : ℂ) * ζ ^ 48 + ((9 / 4) : ℂ) * ζ ^ 50 + ((13 / 16) : ℂ) * ζ ^ 52 + ((1 / 16) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_6_1 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        6 1 =
      alternatingSixAmbientRow17TransformedGeneratorA
        6 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((11 / 8) : ℂ) - ((3 / 2) : ℂ) * ζ ^ 2 - ((11 / 8) : ℂ) * ζ ^ 4 + ((41 / 16) : ℂ) * ζ ^ 6 - ((5 / 8) : ℂ) * ζ ^ 8 - ((15 / 8) : ℂ) * ζ ^ 10 + ((1 / 16) : ℂ) * ζ ^ 12 - ((27 / 16) : ℂ) * ζ ^ 14 - ((5 / 8) : ℂ) * ζ ^ 16 + ((13 / 16) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 20 + ((3 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 24 + ((13 / 8) : ℂ) * ζ ^ 26 + ((3 / 16) : ℂ) * ζ ^ 28 + ((5 / 16) : ℂ) * ζ ^ 30 - ((3 / 16) : ℂ) * ζ ^ 32 + ((5 / 16) : ℂ) * ζ ^ 34 + ((3 / 4) : ℂ) * ζ ^ 36 - ((35 / 16) : ℂ) * ζ ^ 38 - ((13 / 16) : ℂ) * ζ ^ 40 + ((5 / 16) : ℂ) * ζ ^ 42 + ((13 / 16) : ℂ) * ζ ^ 44 - ((1 / 2) : ℂ) * ζ ^ 46 - ((3 / 8) : ℂ) * ζ ^ 48 + ((1 / 16) : ℂ) * ζ ^ 50 - ((11 / 16) : ℂ) * ζ ^ 52 + ((1 / 16) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_6_2 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        6 2 =
      alternatingSixAmbientRow17TransformedGeneratorA
        6 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((379 / 656) : ℂ) - ((237 / 82) : ℂ) * ζ ^ 2 + ((97 / 656) : ℂ) * ζ ^ 4 + ((1723 / 656) : ℂ) * ζ ^ 6 - ((689 / 164) : ℂ) * ζ ^ 8 - ((297 / 656) : ℂ) * ζ ^ 10 + ((1409 / 656) : ℂ) * ζ ^ 12 - ((196 / 41) : ℂ) * ζ ^ 14 + ((403 / 328) : ℂ) * ζ ^ 16 + ((617 / 164) : ℂ) * ζ ^ 18 - ((43 / 41) : ℂ) * ζ ^ 20 + ((121 / 164) : ℂ) * ζ ^ 22 + ((553 / 328) : ℂ) * ζ ^ 24 + ((133 / 328) : ℂ) * ζ ^ 26 - ((15 / 82) : ℂ) * ζ ^ 28 + ((577 / 328) : ℂ) * ζ ^ 30 - ((825 / 656) : ℂ) * ζ ^ 32 - ((219 / 164) : ℂ) * ζ ^ 34 - ((91 / 164) : ℂ) * ζ ^ 36 - ((709 / 328) : ℂ) * ζ ^ 38 - ((169 / 656) : ℂ) * ζ ^ 40 - ((1429 / 656) : ℂ) * ζ ^ 42 + ((989 / 656) : ℂ) * ζ ^ 44 + ((165 / 82) : ℂ) * ζ ^ 46 - ((19 / 82) : ℂ) * ζ ^ 48 + ((639 / 328) : ℂ) * ζ ^ 50 + ((93 / 164) : ℂ) * ζ ^ 52 + ((1139 / 656) : ℂ) * ζ ^ 54 + ((3 / 2) : ℂ) * ζ ^ 56)
private theorem row17_transformedGeneratorA_6_3 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        6 3 =
      alternatingSixAmbientRow17TransformedGeneratorA
        6 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((445 / 656) : ℂ) + ((117 / 656) : ℂ) * ζ ^ 2 + ((33 / 164) : ℂ) * ζ ^ 4 + ((29 / 328) : ℂ) * ζ ^ 6 + ((585 / 656) : ℂ) * ζ ^ 8 + ((15 / 41) : ℂ) * ζ ^ 10 - ((213 / 164) : ℂ) * ζ ^ 12 + ((117 / 328) : ℂ) * ζ ^ 14 + ((213 / 656) : ℂ) * ζ ^ 16 - ((65 / 82) : ℂ) * ζ ^ 18 + ((999 / 328) : ℂ) * ζ ^ 20 + ((547 / 328) : ℂ) * ζ ^ 22 - ((29 / 328) : ℂ) * ζ ^ 24 + ((93 / 41) : ℂ) * ζ ^ 26 - ((487 / 328) : ℂ) * ζ ^ 28 - ((513 / 656) : ℂ) * ζ ^ 30 - ((63 / 328) : ℂ) * ζ ^ 32 - ((665 / 656) : ℂ) * ζ ^ 34 - ((19 / 328) : ℂ) * ζ ^ 36 - ((61 / 164) : ℂ) * ζ ^ 38 - ((67 / 82) : ℂ) * ζ ^ 40 - ((513 / 656) : ℂ) * ζ ^ 42 + ((823 / 656) : ℂ) * ζ ^ 44 - ((137 / 328) : ℂ) * ζ ^ 46 + ((389 / 328) : ℂ) * ζ ^ 48 + ((37 / 656) : ℂ) * ζ ^ 50 - ((323 / 328) : ℂ) * ζ ^ 52 + ((667 / 656) : ℂ) * ζ ^ 54 - ((3 / 4) : ℂ) * ζ ^ 56)
private theorem row17_transformedGeneratorA_6_4 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        6 4 =
      alternatingSixAmbientRow17TransformedGeneratorA
        6 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((153 / 176) : ℂ) - ((221 / 88) : ℂ) * ζ ^ 2 - ((153 / 176) : ℂ) * ζ ^ 4 - ((19 / 44) : ℂ) * ζ ^ 6 - ((433 / 176) : ℂ) * ζ ^ 8 + ((227 / 176) : ℂ) * ζ ^ 10 + ((17 / 11) : ℂ) * ζ ^ 12 + ((813 / 176) : ℂ) * ζ ^ 14 + ((151 / 88) : ℂ) * ζ ^ 16 - ((3 / 4) : ℂ) * ζ ^ 18 - ((41 / 88) : ℂ) * ζ ^ 20 - ((567 / 176) : ℂ) * ζ ^ 22 + ((141 / 88) : ℂ) * ζ ^ 24 - ((1355 / 176) : ℂ) * ζ ^ 26 - ((13 / 176) : ℂ) * ζ ^ 28 - ((257 / 88) : ℂ) * ζ ^ 30 - ((859 / 176) : ℂ) * ζ ^ 32 + ((401 / 88) : ℂ) * ζ ^ 34 - ((21 / 88) : ℂ) * ζ ^ 36 + ((719 / 88) : ℂ) * ζ ^ 38 + ((219 / 176) : ℂ) * ζ ^ 40 + ((217 / 88) : ℂ) * ζ ^ 42 + ((21 / 44) : ℂ) * ζ ^ 44 - ((21 / 176) : ℂ) * ζ ^ 46 + ((211 / 176) : ℂ) * ζ ^ 48 - ((195 / 88) : ℂ) * ζ ^ 50 + ((271 / 176) : ℂ) * ζ ^ 52 - ((725 / 176) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_6_5 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        6 5 =
      alternatingSixAmbientRow17TransformedGeneratorA
        6 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((6 / 11) : ℂ) + ((1 / 11) : ℂ) * ζ ^ 2 - ((6 / 11) : ℂ) * ζ ^ 4 + ((421 / 176) : ℂ) * ζ ^ 6 - ((17 / 88) : ℂ) * ζ ^ 8 - ((105 / 88) : ℂ) * ζ ^ 10 + ((255 / 176) : ℂ) * ζ ^ 12 - ((421 / 176) : ℂ) * ζ ^ 14 - ((9 / 88) : ℂ) * ζ ^ 16 + ((1 / 16) : ℂ) * ζ ^ 18 + ((5 / 22) : ℂ) * ζ ^ 20 + ((101 / 88) : ℂ) * ζ ^ 22 + ((19 / 44) : ℂ) * ζ ^ 24 + ((41 / 88) : ℂ) * ζ ^ 26 - ((83 / 176) : ℂ) * ζ ^ 28 + ((537 / 176) : ℂ) * ζ ^ 30 - ((179 / 176) : ℂ) * ζ ^ 32 - ((487 / 176) : ℂ) * ζ ^ 34 - ((129 / 88) : ℂ) * ζ ^ 36 - ((185 / 176) : ℂ) * ζ ^ 38 + ((217 / 176) : ℂ) * ζ ^ 40 - ((359 / 176) : ℂ) * ζ ^ 42 - ((265 / 176) : ℂ) * ζ ^ 44 + ((183 / 88) : ℂ) * ζ ^ 46 + ((10 / 11) : ℂ) * ζ ^ 48 + ((337 / 176) : ℂ) * ζ ^ 50 + ((43 / 176) : ℂ) * ζ ^ 52 - ((41 / 176) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_6_6 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        6 6 =
      alternatingSixAmbientRow17TransformedGeneratorA
        6 6 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((291 / 656) : ℂ) + ((99 / 82) : ℂ) * ζ ^ 2 - ((767 / 656) : ℂ) * ζ ^ 4 - ((53 / 656) : ℂ) * ζ ^ 6 - ((39 / 82) : ℂ) * ζ ^ 8 - ((679 / 656) : ℂ) * ζ ^ 10 + ((527 / 656) : ℂ) * ζ ^ 12 - ((107 / 82) : ℂ) * ζ ^ 14 - ((75 / 164) : ℂ) * ζ ^ 16 - ((49 / 164) : ℂ) * ζ ^ 18 - ((217 / 328) : ℂ) * ζ ^ 20 + ((12 / 41) : ℂ) * ζ ^ 22 + ((103 / 328) : ℂ) * ζ ^ 24 + ((791 / 328) : ℂ) * ζ ^ 26 + ((209 / 164) : ℂ) * ζ ^ 28 + ((43 / 41) : ℂ) * ζ ^ 30 - ((755 / 656) : ℂ) * ζ ^ 32 - ((93 / 41) : ℂ) * ζ ^ 34 - ((239 / 328) : ℂ) * ζ ^ 36 - ((21 / 164) : ℂ) * ζ ^ 38 + ((1335 / 656) : ℂ) * ζ ^ 40 - ((1153 / 656) : ℂ) * ζ ^ 42 - ((1671 / 656) : ℂ) * ζ ^ 44 + ((11 / 164) : ℂ) * ζ ^ 46 + ((3 / 4) : ℂ) * ζ ^ 48 + ((483 / 164) : ℂ) * ζ ^ 50 + ((13 / 328) : ℂ) * ζ ^ 52 + ((419 / 656) : ℂ) * ζ ^ 54 - ((3 / 2) : ℂ) * ζ ^ 56)
private theorem row17_transformedGeneratorA_6_7 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        6 7 =
      alternatingSixAmbientRow17TransformedGeneratorA
        6 7 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((301 / 656) : ℂ) - ((25 / 656) : ℂ) * ζ ^ 2 + ((307 / 328) : ℂ) * ζ ^ 4 + ((595 / 328) : ℂ) * ζ ^ 6 + ((231 / 656) : ℂ) * ζ ^ 8 - ((68 / 41) : ℂ) * ζ ^ 10 - ((133 / 328) : ℂ) * ζ ^ 12 + ((54 / 41) : ℂ) * ζ ^ 14 - ((385 / 656) : ℂ) * ζ ^ 16 + ((261 / 328) : ℂ) * ζ ^ 18 + ((1 / 328) : ℂ) * ζ ^ 20 - ((45 / 164) : ℂ) * ζ ^ 22 - ((53 / 328) : ℂ) * ζ ^ 24 + ((46 / 41) : ℂ) * ζ ^ 26 + ((27 / 164) : ℂ) * ζ ^ 28 + ((93 / 656) : ℂ) * ζ ^ 30 + ((737 / 328) : ℂ) * ζ ^ 32 - ((327 / 656) : ℂ) * ζ ^ 34 + ((121 / 164) : ℂ) * ζ ^ 36 - ((591 / 328) : ℂ) * ζ ^ 38 - ((153 / 328) : ℂ) * ζ ^ 40 + ((653 / 656) : ℂ) * ζ ^ 42 - ((609 / 656) : ℂ) * ζ ^ 44 - ((59 / 164) : ℂ) * ζ ^ 46 - ζ ^ 48 - ((489 / 656) : ℂ) * ζ ^ 50 - ((33 / 164) : ℂ) * ζ ^ 52 + ((891 / 656) : ℂ) * ζ ^ 54 + ((3 / 4) : ℂ) * ζ ^ 56)
private theorem row17_transformedGeneratorA_7_0 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        7 0 =
      alternatingSixAmbientRow17TransformedGeneratorA
        7 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((1 / 8) : ℂ) * ζ ^ 2 + ((1 / 4) : ℂ) * ζ ^ 6 - ((5 / 16) : ℂ) * ζ ^ 8 - ((3 / 16) : ℂ) * ζ ^ 10 - ((7 / 16) : ℂ) * ζ ^ 12 + ((1 / 16) : ℂ) * ζ ^ 14 + ((35 / 16) : ℂ) * ζ ^ 16 + ((5 / 8) : ℂ) * ζ ^ 18 - ζ ^ 20 - ((5 / 16) : ℂ) * ζ ^ 22 + ((5 / 16) : ℂ) * ζ ^ 24 - ((19 / 16) : ℂ) * ζ ^ 26 - ((11 / 16) : ℂ) * ζ ^ 28 + ((1 / 8) : ℂ) * ζ ^ 30 - ((1 / 4) : ℂ) * ζ ^ 32 + ζ ^ 34 - (2 : ℂ) * ζ ^ 36 - ((1 / 8) : ℂ) * ζ ^ 38 + ((5 / 4) : ℂ) * ζ ^ 40 - ((7 / 8) : ℂ) * ζ ^ 42 - ((1 / 4) : ℂ) * ζ ^ 44 + ((33 / 16) : ℂ) * ζ ^ 46 + ((11 / 16) : ℂ) * ζ ^ 48 - ((19 / 8) : ℂ) * ζ ^ 50 + ((11 / 16) : ℂ) * ζ ^ 52 + ((5 / 16) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_7_1 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        7 1 =
      alternatingSixAmbientRow17TransformedGeneratorA
        7 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((1 / 8) : ℂ) + ((9 / 8) : ℂ) * ζ ^ 2 + ((1 / 8) : ℂ) * ζ ^ 4 - ((19 / 16) : ℂ) * ζ ^ 6 + ((21 / 16) : ℂ) * ζ ^ 8 + ((3 / 8) : ℂ) * ζ ^ 10 - ((3 / 2) : ℂ) * ζ ^ 12 + ((23 / 16) : ℂ) * ζ ^ 14 + ((3 / 8) : ℂ) * ζ ^ 16 - ((15 / 16) : ℂ) * ζ ^ 18 - ((9 / 16) : ℂ) * ζ ^ 20 - ((1 / 8) : ℂ) * ζ ^ 24 - ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 28 + ((5 / 16) : ℂ) * ζ ^ 30 + ((17 / 16) : ℂ) * ζ ^ 32 - ((7 / 16) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 36 + ((15 / 16) : ℂ) * ζ ^ 38 - ((3 / 16) : ℂ) * ζ ^ 40 - ((15 / 16) : ℂ) * ζ ^ 42 + ((1 / 16) : ℂ) * ζ ^ 44 + ((13 / 8) : ℂ) * ζ ^ 46 - ((3 / 8) : ℂ) * ζ ^ 48 - ((1 / 16) : ℂ) * ζ ^ 50 - ((5 / 16) : ℂ) * ζ ^ 52 + ((11 / 16) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_7_2 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        7 2 =
      alternatingSixAmbientRow17TransformedGeneratorA
        7 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((115 / 328) : ℂ) + ((65 / 82) : ℂ) * ζ ^ 2 + ((13 / 82) : ℂ) * ζ ^ 4 - ((721 / 656) : ℂ) * ζ ^ 6 + ((119 / 328) : ℂ) * ζ ^ 8 - ((199 / 656) : ℂ) * ζ ^ 10 - ((135 / 164) : ℂ) * ζ ^ 12 + ((1315 / 656) : ℂ) * ζ ^ 14 + ((305 / 328) : ℂ) * ζ ^ 16 - ((221 / 164) : ℂ) * ζ ^ 18 + ((47 / 41) : ℂ) * ζ ^ 20 + ((295 / 656) : ℂ) * ζ ^ 22 - ((947 / 656) : ℂ) * ζ ^ 24 + ((715 / 656) : ℂ) * ζ ^ 26 + ((50 / 41) : ℂ) * ζ ^ 28 - ((34 / 41) : ℂ) * ζ ^ 30 - ((491 / 656) : ℂ) * ζ ^ 32 + ((303 / 328) : ℂ) * ζ ^ 34 - ((465 / 656) : ℂ) * ζ ^ 36 - ((49 / 41) : ℂ) * ζ ^ 38 + ((279 / 328) : ℂ) * ζ ^ 40 + ((115 / 82) : ℂ) * ζ ^ 42 - ((7 / 41) : ℂ) * ζ ^ 44 - ((30 / 41) : ℂ) * ζ ^ 46 + ((191 / 328) : ℂ) * ζ ^ 48 - ((151 / 164) : ℂ) * ζ ^ 50 + ((27 / 328) : ℂ) * ζ ^ 52 + ((709 / 656) : ℂ) * ζ ^ 54 - ((129 / 328) : ℂ) * ζ ^ 56)
private theorem row17_transformedGeneratorA_7_3 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        7 3 =
      alternatingSixAmbientRow17TransformedGeneratorA
        7 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((55 / 164) : ℂ) + ((197 / 328) : ℂ) * ζ ^ 2 + ((333 / 656) : ℂ) * ζ ^ 4 - ((327 / 328) : ℂ) * ζ ^ 6 + ((253 / 164) : ℂ) * ζ ^ 8 + ((799 / 656) : ℂ) * ζ ^ 10 + ((1 / 164) : ℂ) * ζ ^ 12 + ((87 / 328) : ℂ) * ζ ^ 14 - ((741 / 656) : ℂ) * ζ ^ 16 - ((95 / 82) : ℂ) * ζ ^ 18 - ((869 / 656) : ℂ) * ζ ^ 20 - ((479 / 656) : ℂ) * ζ ^ 22 - ((17 / 164) : ℂ) * ζ ^ 24 - ((95 / 82) : ℂ) * ζ ^ 26 + ((35 / 328) : ℂ) * ζ ^ 28 + ((9 / 328) : ℂ) * ζ ^ 30 + ((29 / 328) : ℂ) * ζ ^ 32 - ((69 / 164) : ℂ) * ζ ^ 34 + ((537 / 328) : ℂ) * ζ ^ 36 + ((1063 / 656) : ℂ) * ζ ^ 38 + ((15 / 656) : ℂ) * ζ ^ 40 + ((593 / 656) : ℂ) * ζ ^ 42 - ((387 / 656) : ℂ) * ζ ^ 44 + ((5 / 82) : ℂ) * ζ ^ 46 + ((221 / 656) : ℂ) * ζ ^ 48 + ((679 / 656) : ℂ) * ζ ^ 50 + ((1 / 41) : ℂ) * ζ ^ 52 - ((493 / 656) : ℂ) * ζ ^ 54 + ((21 / 328) : ℂ) * ζ ^ 56)
private theorem row17_transformedGeneratorA_7_4 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        7 4 =
      alternatingSixAmbientRow17TransformedGeneratorA
        7 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((7 / 44) : ℂ) + ((149 / 88) : ℂ) * ζ ^ 2 - ((7 / 44) : ℂ) * ζ ^ 4 - ((13 / 88) : ℂ) * ζ ^ 6 + ((131 / 176) : ℂ) * ζ ^ 8 + ((1 / 176) : ℂ) * ζ ^ 10 - ((205 / 176) : ℂ) * ζ ^ 12 - ((515 / 176) : ℂ) * ζ ^ 14 + ((205 / 176) : ℂ) * ζ ^ 16 - ((19 / 88) : ℂ) * ζ ^ 18 - ((221 / 88) : ℂ) * ζ ^ 20 + ((259 / 176) : ℂ) * ζ ^ 22 + ((159 / 176) : ℂ) * ζ ^ 24 + ((261 / 176) : ℂ) * ζ ^ 26 + ((65 / 176) : ℂ) * ζ ^ 28 + ((27 / 22) : ℂ) * ζ ^ 30 + ((41 / 22) : ℂ) * ζ ^ 32 - ((19 / 22) : ℂ) * ζ ^ 34 - ((7 / 22) : ℂ) * ζ ^ 36 - ((21 / 22) : ℂ) * ζ ^ 38 - ((19 / 44) : ℂ) * ζ ^ 40 - ((117 / 44) : ℂ) * ζ ^ 42 - ((45 / 44) : ℂ) * ζ ^ 44 + ((201 / 176) : ℂ) * ζ ^ 46 - ((257 / 176) : ℂ) * ζ ^ 48 - ((61 / 22) : ℂ) * ζ ^ 50 - ((9 / 16) : ℂ) * ζ ^ 52 - ((85 / 176) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_7_5 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        7 5 =
      alternatingSixAmbientRow17TransformedGeneratorA
        7 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((13 / 88) : ℂ) + ((29 / 88) : ℂ) * ζ ^ 2 + ((13 / 88) : ℂ) * ζ ^ 4 - ((199 / 176) : ℂ) * ζ ^ 6 - ((113 / 176) : ℂ) * ζ ^ 8 - ((81 / 88) : ℂ) * ζ ^ 10 + ((17 / 88) : ℂ) * ζ ^ 12 + ((413 / 176) : ℂ) * ζ ^ 14 + ((5 / 88) : ℂ) * ζ ^ 16 - ((125 / 176) : ℂ) * ζ ^ 18 + ((357 / 176) : ℂ) * ζ ^ 20 - ((13 / 88) : ℂ) * ζ ^ 22 - ((119 / 88) : ℂ) * ζ ^ 24 + ((61 / 44) : ℂ) * ζ ^ 26 + ((81 / 88) : ℂ) * ζ ^ 28 - ((111 / 176) : ℂ) * ζ ^ 30 - ((347 / 176) : ℂ) * ζ ^ 32 + ((61 / 176) : ℂ) * ζ ^ 34 - ((7 / 88) : ℂ) * ζ ^ 36 + ((189 / 176) : ℂ) * ζ ^ 38 + ((69 / 176) : ℂ) * ζ ^ 40 + ((37 / 176) : ℂ) * ζ ^ 42 + ((43 / 176) : ℂ) * ζ ^ 44 - ((7 / 11) : ℂ) * ζ ^ 46 + ((115 / 88) : ℂ) * ζ ^ 48 + ((131 / 176) : ℂ) * ζ ^ 50 - ((5 / 16) : ℂ) * ζ ^ 52 + ((185 / 176) : ℂ) * ζ ^ 54)
private theorem row17_transformedGeneratorA_7_6 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        7 6 =
      alternatingSixAmbientRow17TransformedGeneratorA
        7 6 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (((29 / 328) : ℂ) + ((197 / 164) : ℂ) * ζ ^ 2 + ((17 / 164) : ℂ) * ζ ^ 4 - ((409 / 656) : ℂ) * ζ ^ 6 - ((601 / 328) : ℂ) * ζ ^ 8 - ((281 / 656) : ℂ) * ζ ^ 10 - ((161 / 328) : ℂ) * ζ ^ 12 + ((1633 / 656) : ℂ) * ζ ^ 14 + ζ ^ 16 - ((16 / 41) : ℂ) * ζ ^ 18 - ((33 / 328) : ℂ) * ζ ^ 20 - ((719 / 656) : ℂ) * ζ ^ 22 - ((363 / 656) : ℂ) * ζ ^ 24 + ((493 / 656) : ℂ) * ζ ^ 26 + ((28 / 41) : ℂ) * ζ ^ 28 + ((107 / 328) : ℂ) * ζ ^ 30 - ((409 / 656) : ℂ) * ζ ^ 32 - ((397 / 328) : ℂ) * ζ ^ 34 + ((1 / 656) : ℂ) * ζ ^ 36 + ((405 / 328) : ℂ) * ζ ^ 38 + ((75 / 328) : ℂ) * ζ ^ 40 + ((211 / 328) : ℂ) * ζ ^ 42 - ((16 / 41) : ℂ) * ζ ^ 44 - ((44 / 41) : ℂ) * ζ ^ 46 + ((301 / 328) : ℂ) * ζ ^ 48 - ((133 / 328) : ℂ) * ζ ^ 50 - ((1 / 2) : ℂ) * ζ ^ 52 + ((13 / 656) : ℂ) * ζ ^ 54 + ((129 / 328) : ℂ) * ζ ^ 56)
private theorem row17_transformedGeneratorA_7_7 :
    (alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis)
        7 7 =
      alternatingSixAmbientRow17TransformedGeneratorA
        7 7 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow17Eigenbasis,
      alternatingSixAmbientRow17EigenbasisInverse,
      alternatingSixFiveAmbient_row17_matrixA,
      alternatingSixAmbientRow17TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row17 (-((61 / 164) : ℂ) + ((97 / 328) : ℂ) * ζ ^ 2 + ((131 / 656) : ℂ) * ζ ^ 4 - ((217 / 328) : ℂ) * ζ ^ 6 + ((279 / 328) : ℂ) * ζ ^ 8 - ((595 / 656) : ℂ) * ζ ^ 10 - ((31 / 328) : ℂ) * ζ ^ 12 + ((83 / 164) : ℂ) * ζ ^ 14 - ((15 / 16) : ℂ) * ζ ^ 16 - ((577 / 328) : ℂ) * ζ ^ 18 - ((97 / 656) : ℂ) * ζ ^ 20 + ((569 / 656) : ℂ) * ζ ^ 22 + ((5 / 164) : ℂ) * ζ ^ 24 - ((47 / 164) : ℂ) * ζ ^ 26 - ((105 / 164) : ℂ) * ζ ^ 28 + ((261 / 328) : ℂ) * ζ ^ 30 - ((135 / 328) : ℂ) * ζ ^ 32 - ((33 / 164) : ℂ) * ζ ^ 34 + ((117 / 164) : ℂ) * ζ ^ 36 + ((35 / 656) : ℂ) * ζ ^ 38 + ((49 / 656) : ℂ) * ζ ^ 40 + ((163 / 656) : ℂ) * ζ ^ 42 + ((609 / 656) : ℂ) * ζ ^ 44 - ((203 / 328) : ℂ) * ζ ^ 46 + ((107 / 656) : ℂ) * ζ ^ 48 + ((521 / 656) : ℂ) * ζ ^ 50 + ((3 / 8) : ℂ) * ζ ^ 52 - ((189 / 656) : ℂ) * ζ ^ 54 - ((21 / 328) : ℂ) * ζ ^ 56)
/-- Exact conjugation formula for the row 17 first
generator. -/
theorem alternatingSixAmbientRow17TransformedGeneratorA_eq :
    alternatingSixAmbientRow17EigenbasisInverse *
        alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixAmbientRow17Eigenbasis =
      alternatingSixAmbientRow17TransformedGeneratorA := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row17_transformedGeneratorA_0_0
  · exact row17_transformedGeneratorA_0_1
  · exact row17_transformedGeneratorA_0_2
  · exact row17_transformedGeneratorA_0_3
  · exact row17_transformedGeneratorA_0_4
  · exact row17_transformedGeneratorA_0_5
  · exact row17_transformedGeneratorA_0_6
  · exact row17_transformedGeneratorA_0_7
  · exact row17_transformedGeneratorA_1_0
  · exact row17_transformedGeneratorA_1_1
  · exact row17_transformedGeneratorA_1_2
  · exact row17_transformedGeneratorA_1_3
  · exact row17_transformedGeneratorA_1_4
  · exact row17_transformedGeneratorA_1_5
  · exact row17_transformedGeneratorA_1_6
  · exact row17_transformedGeneratorA_1_7
  · exact row17_transformedGeneratorA_2_0
  · exact row17_transformedGeneratorA_2_1
  · exact row17_transformedGeneratorA_2_2
  · exact row17_transformedGeneratorA_2_3
  · exact row17_transformedGeneratorA_2_4
  · exact row17_transformedGeneratorA_2_5
  · exact row17_transformedGeneratorA_2_6
  · exact row17_transformedGeneratorA_2_7
  · exact row17_transformedGeneratorA_3_0
  · exact row17_transformedGeneratorA_3_1
  · exact row17_transformedGeneratorA_3_2
  · exact row17_transformedGeneratorA_3_3
  · exact row17_transformedGeneratorA_3_4
  · exact row17_transformedGeneratorA_3_5
  · exact row17_transformedGeneratorA_3_6
  · exact row17_transformedGeneratorA_3_7
  · exact row17_transformedGeneratorA_4_0
  · exact row17_transformedGeneratorA_4_1
  · exact row17_transformedGeneratorA_4_2
  · exact row17_transformedGeneratorA_4_3
  · exact row17_transformedGeneratorA_4_4
  · exact row17_transformedGeneratorA_4_5
  · exact row17_transformedGeneratorA_4_6
  · exact row17_transformedGeneratorA_4_7
  · exact row17_transformedGeneratorA_5_0
  · exact row17_transformedGeneratorA_5_1
  · exact row17_transformedGeneratorA_5_2
  · exact row17_transformedGeneratorA_5_3
  · exact row17_transformedGeneratorA_5_4
  · exact row17_transformedGeneratorA_5_5
  · exact row17_transformedGeneratorA_5_6
  · exact row17_transformedGeneratorA_5_7
  · exact row17_transformedGeneratorA_6_0
  · exact row17_transformedGeneratorA_6_1
  · exact row17_transformedGeneratorA_6_2
  · exact row17_transformedGeneratorA_6_3
  · exact row17_transformedGeneratorA_6_4
  · exact row17_transformedGeneratorA_6_5
  · exact row17_transformedGeneratorA_6_6
  · exact row17_transformedGeneratorA_6_7
  · exact row17_transformedGeneratorA_7_0
  · exact row17_transformedGeneratorA_7_1
  · exact row17_transformedGeneratorA_7_2
  · exact row17_transformedGeneratorA_7_3
  · exact row17_transformedGeneratorA_7_4
  · exact row17_transformedGeneratorA_7_5
  · exact row17_transformedGeneratorA_7_6
  · exact row17_transformedGeneratorA_7_7


end InductiveMcKay
end McKayConjecture
