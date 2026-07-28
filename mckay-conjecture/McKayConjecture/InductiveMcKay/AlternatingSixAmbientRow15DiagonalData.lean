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
# Checked diagonal data for ambient row 15

This generated module records an exact eigenbasis for the second generator
and the first generator in that basis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Eigenvalue block labels for row 15. -/
def alternatingSixAmbientRow15EigenvalueLabel :
    Fin 6 → Fin 4 :=
  ![0, 0, 1, 2, 3, 3]

/-- Second-generator eigenvalues, including their multiplicities. -/
def alternatingSixAmbientRow15GeneratorBEigenvalue :
    Fin 6 → ℂ :=
  fun i ↦
    alternatingSixOrderEightOddEigenvalue
      (alternatingSixAmbientRow15EigenvalueLabel i)

/-- Diagonal form of the row 15 second generator. -/
def alternatingSixAmbientRow15GeneratorBDiagonal :
    Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.diagonal
    alternatingSixAmbientRow15GeneratorBEigenvalue

/-- Checked eigenbasis for the row 15 second generator. -/
def alternatingSixAmbientRow15Eigenbasis :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [(-1, 0), (1, 3), (1, 7), (1, 10), (-1, 15), (-1, 19), (-1, 23), (-1, 30), (1, 31)],
      alternatingSixCyclotomicValue [(-1, 10), (1, 20), (-1, 25), (1, 30)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0), (1, 3), (1, 5), (1, 7), (1, 10), (-1, 19), (-1, 23), (-1, 25), (1, 31)],
      alternatingSixCyclotomicValue [((-18 / 73), 0), ((20 / 73), 3), ((60 / 73), 5), ((20 / 73), 7), ((19 / 73), 10), ((-59 / 73), 15), ((-20 / 73), 19), ((2 / 73), 20), ((-20 / 73), 23), ((-31 / 73), 25), ((6 / 73), 30), ((20 / 73), 31)],
      alternatingSixCyclotomicValue [((-2 / 73), 0), ((-14 / 73), 3), ((-42 / 73), 5), ((-14 / 73), 7), ((-6 / 73), 10), ((34 / 73), 15), ((14 / 73), 19), ((-16 / 73), 20), ((14 / 73), 23), ((29 / 73), 25), ((-48 / 73), 30), ((-14 / 73), 31)]],
    ![alternatingSixCyclotomicValue [(-2, 3), (1, 5), (-2, 7), (-1, 10), (1, 15), (2, 19), (1, 20), (2, 23), (-1, 25), (-2, 31)],
      alternatingSixCyclotomicValue [(1, 3), (-2, 5), (1, 7), (1, 10), (-1, 19), (-1, 20), (-1, 23), (1, 25), (1, 30), (1, 31)],
      alternatingSixCyclotomicValue [(1, 0), (-2, 10), (-1, 15), (1, 25), (2, 30)],
      alternatingSixCyclotomicValue [(-1, 5), (-1, 10), (1, 15), (1, 25), (2, 30)],
      alternatingSixCyclotomicValue [((-4 / 73), 0), ((45 / 73), 3), ((-11 / 73), 5), ((45 / 73), 7), ((-12 / 73), 10), ((-5 / 73), 15), ((-45 / 73), 19), ((-32 / 73), 20), ((-45 / 73), 23), ((58 / 73), 25), ((-23 / 73), 30), ((45 / 73), 31)],
      alternatingSixCyclotomicValue [((-41 / 73), 0), ((5 / 73), 3), ((15 / 73), 5), ((5 / 73), 7), ((23 / 73), 10), ((-33 / 73), 15), ((-5 / 73), 19), ((37 / 73), 20), ((-5 / 73), 23), ((-26 / 73), 25), ((38 / 73), 30), ((5 / 73), 31)]],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(-1, 3), (-1, 7), (1, 19), (1, 23), (-1, 31)],
      alternatingSixCyclotomicValue [(1, 25)],
      alternatingSixCyclotomicValue [(1, 3), (1, 7), (-1, 19), (-1, 23), (1, 31)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(-1, 25)]],
    ![alternatingSixCyclotomicValue [(1, 0), (-1, 3), (-1, 7), (-1, 10), (2, 15), (1, 19), (1, 23), (-1, 25), (1, 30), (-1, 31)],
      alternatingSixCyclotomicValue [(-2, 0), (2, 3), (2, 7), (2, 10), (-2, 15), (-2, 19), (-2, 23), (1, 25), (2, 31)],
      alternatingSixCyclotomicValue [(-1, 0), (-1, 3), (-1, 7), (1, 15), (1, 19), (1, 20), (1, 23), (-1, 31)],
      alternatingSixCyclotomicValue [(1, 0), (1, 5), (1, 10), (1, 15)],
      alternatingSixCyclotomicValue [((57 / 73), 0), ((-39 / 73), 3), ((-44 / 73), 5), ((-39 / 73), 7), ((25 / 73), 10), ((-20 / 73), 15), ((39 / 73), 19), ((18 / 73), 20), ((39 / 73), 23), ((13 / 73), 25), ((-19 / 73), 30), ((-39 / 73), 31)],
      alternatingSixCyclotomicValue [((-18 / 73), 0), ((20 / 73), 3), ((60 / 73), 5), ((20 / 73), 7), ((-54 / 73), 10), ((14 / 73), 15), ((-20 / 73), 19), ((2 / 73), 20), ((-20 / 73), 23), ((-31 / 73), 25), ((6 / 73), 30), ((20 / 73), 31)]],
    ![alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(-1, 3), (1, 5), (-1, 7), (1, 19), (1, 23), (1, 25), (1, 30), (-1, 31)],
      alternatingSixCyclotomicValue [(-1, 5), (1, 10), (1, 15), (1, 25)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue []],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)]]
  ]

/-- Checked inverse of the row 15 eigenbasis. -/
def alternatingSixAmbientRow15EigenbasisInverse :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((1 / 4), 3), ((1 / 4), 7), ((1 / 4), 10), ((-1 / 4), 19), ((-1 / 4), 23), ((-1 / 2), 30), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((-7 / 4), 0), ((11 / 6), 3), ((11 / 6), 5), ((11 / 6), 7), ((-5 / 3), 10), ((-5 / 12), 15), ((-11 / 6), 19), ((-11 / 6), 23), ((-5 / 3), 25), ((5 / 6), 30), ((11 / 6), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 3), ((1 / 4), 7), ((1 / 4), 10), ((-3 / 4), 15), ((-1 / 4), 19), ((1 / 2), 20), ((-1 / 4), 23), ((-1 / 2), 25), ((3 / 4), 30), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((-3 / 2), 0), ((1 / 12), 3), ((5 / 6), 5), ((1 / 12), 7), ((-17 / 12), 10), ((5 / 6), 15), ((-1 / 12), 19), ((-1 / 4), 20), ((-1 / 12), 23), ((1 / 12), 25), ((7 / 12), 30), ((1 / 12), 31)],
      alternatingSixCyclotomicValue [((3 / 4), 0), ((-3 / 4), 3), ((-1 / 2), 5), ((-3 / 4), 7), ((1 / 2), 10), ((3 / 4), 15), ((3 / 4), 19), ((-1 / 4), 20), ((3 / 4), 23), (1, 25), ((-3 / 4), 30), ((-3 / 4), 31)],
      alternatingSixCyclotomicValue [((-7 / 6), 0), ((17 / 12), 3), (1, 5), ((17 / 12), 7), ((-11 / 12), 10), ((-11 / 6), 15), ((-17 / 12), 19), ((4 / 3), 20), ((-17 / 12), 23), (-2, 25), ((11 / 6), 30), ((17 / 12), 31)]],
    ![alternatingSixCyclotomicValue [((1 / 28), 0), ((1 / 28), 3), ((-1 / 7), 5), ((1 / 28), 7), ((-1 / 28), 10), ((-5 / 28), 15), ((-1 / 28), 19), ((-5 / 28), 20), ((-1 / 28), 23), ((-1 / 28), 25), ((-9 / 28), 30), ((1 / 28), 31)],
      alternatingSixCyclotomicValue [((-5 / 28), 0), ((-43 / 84), 3), ((-31 / 84), 5), ((-43 / 84), 7), ((-17 / 42), 10), ((13 / 42), 15), ((43 / 84), 19), ((-17 / 28), 20), ((43 / 84), 23), ((29 / 84), 25), ((-19 / 84), 30), ((-43 / 84), 31)],
      alternatingSixCyclotomicValue [((-1 / 7), 0), ((2 / 7), 3), ((-1 / 28), 5), ((2 / 7), 7), ((-1 / 7), 10), ((-5 / 28), 15), ((-2 / 7), 19), ((-1 / 28), 20), ((-2 / 7), 23), ((-1 / 14), 25), ((-1 / 28), 30), ((2 / 7), 31)],
      alternatingSixCyclotomicValue [((-1 / 28), 0), ((-10 / 21), 3), ((-19 / 84), 5), ((-10 / 21), 7), ((23 / 84), 10), ((53 / 84), 15), ((10 / 21), 19), ((5 / 28), 20), ((10 / 21), 23), ((53 / 84), 25), ((-5 / 42), 30), ((-10 / 21), 31)],
      alternatingSixCyclotomicValue [((11 / 28), 0), ((1 / 7), 3), ((5 / 28), 5), ((1 / 7), 7), ((5 / 14), 10), ((1 / 28), 15), ((-1 / 7), 19), ((1 / 28), 20), ((-1 / 7), 23), ((-1 / 7), 25), ((-2 / 7), 30), ((1 / 7), 31)],
      alternatingSixCyclotomicValue [((-13 / 84), 0), ((1 / 12), 3), ((1 / 7), 5), ((1 / 12), 7), ((-61 / 84), 10), ((1 / 12), 15), ((-1 / 12), 19), ((-19 / 84), 20), ((-1 / 12), 23), ((1 / 28), 25), ((11 / 84), 30), ((1 / 12), 31)]],
    ![alternatingSixCyclotomicValue [((-3 / 28), 0), ((-1 / 14), 3), ((-1 / 7), 5), ((-1 / 14), 7), ((-1 / 4), 10), ((3 / 28), 15), ((1 / 14), 19), ((1 / 28), 20), ((1 / 14), 23), ((3 / 14), 25), ((1 / 4), 30), ((-1 / 14), 31)],
      alternatingSixCyclotomicValue [((-29 / 21), 0), ((31 / 28), 3), ((109 / 84), 5), ((31 / 28), 7), ((-4 / 3), 10), ((3 / 14), 15), ((-31 / 28), 19), ((55 / 84), 20), ((-31 / 28), 23), ((-41 / 84), 25), ((7 / 6), 30), ((31 / 28), 31)],
      alternatingSixCyclotomicValue [((-1 / 7), 0), ((11 / 28), 3), ((11 / 28), 7), ((2 / 7), 10), ((-5 / 7), 15), ((-11 / 28), 19), ((13 / 28), 20), ((-11 / 28), 23), ((-1 / 2), 25), ((9 / 28), 30), ((11 / 28), 31)],
      alternatingSixCyclotomicValue [((-5 / 12), 0), ((17 / 28), 3), ((73 / 84), 5), ((17 / 28), 7), ((-55 / 84), 10), ((13 / 28), 15), ((-17 / 28), 19), ((-5 / 12), 20), ((-17 / 28), 23), ((-2 / 21), 25), ((1 / 42), 30), ((17 / 28), 31)],
      alternatingSixCyclotomicValue [((9 / 28), 0), ((-2 / 7), 3), ((-9 / 28), 5), ((-2 / 7), 7), ((5 / 28), 15), ((2 / 7), 19), ((-17 / 28), 20), ((2 / 7), 23), ((5 / 14), 25), ((-1 / 2), 30), ((-2 / 7), 31)],
      alternatingSixCyclotomicValue [((-5 / 7), 0), ((73 / 84), 3), ((29 / 42), 5), ((73 / 84), 7), ((-17 / 84), 10), ((-71 / 84), 15), ((-73 / 84), 19), ((37 / 28), 20), ((-73 / 84), 23), ((-101 / 84), 25), ((53 / 42), 30), ((73 / 84), 31)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 28), 3), ((1 / 14), 5), ((-1 / 28), 7), ((3 / 28), 10), ((5 / 28), 15), ((1 / 28), 19), ((1 / 4), 20), ((1 / 28), 23), ((-3 / 28), 25), ((-1 / 28), 30), ((-1 / 28), 31)],
      alternatingSixCyclotomicValue [((7 / 12), 0), ((-9 / 28), 3), ((-65 / 84), 5), ((-9 / 28), 7), ((29 / 21), 10), ((-8 / 7), 15), ((9 / 28), 19), ((13 / 12), 20), ((9 / 28), 23), ((-53 / 84), 25), ((29 / 84), 30), ((-9 / 28), 31)],
      alternatingSixCyclotomicValue [((4 / 7), 0), ((-1 / 2), 3), ((-11 / 28), 5), ((-1 / 2), 7), ((1 / 7), 10), ((1 / 4), 15), ((1 / 2), 19), ((-17 / 28), 20), ((1 / 2), 23), ((5 / 7), 25), ((-13 / 28), 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((-5 / 84), 0), ((4 / 7), 3), ((19 / 84), 5), ((4 / 7), 7), ((5 / 12), 10), ((-31 / 28), 15), ((-4 / 7), 19), ((67 / 84), 20), ((-4 / 7), 23), ((-95 / 84), 25), ((2 / 3), 30), ((4 / 7), 31)],
      alternatingSixCyclotomicValue [((-3 / 4), 0), ((5 / 14), 3), ((15 / 28), 5), ((5 / 14), 7), ((-4 / 7), 10), ((-1 / 28), 15), ((-5 / 14), 19), ((1 / 4), 20), ((-5 / 14), 23), ((-3 / 7), 25), ((5 / 14), 30), ((5 / 14), 31)],
      alternatingSixCyclotomicValue [((47 / 28), 0), ((-101 / 84), 3), ((-61 / 42), 5), ((-101 / 84), 7), ((109 / 84), 10), ((1 / 84), 15), ((101 / 84), 19), ((-11 / 28), 20), ((101 / 84), 23), ((85 / 84), 25), ((-83 / 84), 30), ((-101 / 84), 31)]],
    ![alternatingSixCyclotomicValue [((1 / 28), 0), ((3 / 14), 3), ((3 / 14), 7), ((3 / 7), 10), ((3 / 7), 15), ((-3 / 14), 19), ((9 / 28), 20), ((-3 / 14), 23), ((1 / 4), 25), ((-1 / 7), 30), ((3 / 14), 31)],
      alternatingSixCyclotomicValue [((5 / 21), 0), ((3 / 7), 3), ((17 / 12), 5), ((3 / 7), 7), ((4 / 21), 10), ((19 / 14), 15), ((-3 / 7), 19), ((-29 / 42), 20), ((-3 / 7), 23), ((5 / 12), 25), ((-59 / 84), 30), ((3 / 7), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((2 / 7), 3), ((5 / 28), 5), ((2 / 7), 7), ((-5 / 14), 10), ((-3 / 7), 15), ((-2 / 7), 19), ((1 / 4), 20), ((-2 / 7), 23), ((-1 / 7), 25), ((2 / 7), 30), ((2 / 7), 31)],
      alternatingSixCyclotomicValue [((25 / 42), 0), ((-1 / 4), 3), ((-4 / 21), 5), ((-1 / 4), 7), ((-13 / 42), 10), ((1 / 4), 19), ((-31 / 21), 20), ((1 / 4), 23), ((17 / 84), 25), ((-20 / 21), 30), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 7), 0), ((-9 / 14), 3), ((-3 / 4), 5), ((-9 / 14), 7), ((-1 / 28), 10), ((3 / 14), 15), ((9 / 14), 19), ((2 / 7), 20), ((9 / 14), 23), ((1 / 2), 25), ((5 / 28), 30), ((-9 / 14), 31)],
      alternatingSixCyclotomicValue [((1 / 28), 0), ((67 / 42), 3), ((125 / 84), 5), ((67 / 42), 7), ((-23 / 42), 10), ((-19 / 84), 15), ((-67 / 42), 19), ((-5 / 28), 20), ((-67 / 42), 23), ((-29 / 42), 25), ((5 / 21), 30), ((67 / 42), 31)]],
    ![alternatingSixCyclotomicValue [((9 / 28), 0), ((1 / 14), 3), ((3 / 14), 5), ((1 / 14), 7), ((5 / 28), 10), ((-3 / 28), 15), ((-1 / 14), 19), ((-3 / 28), 20), ((-1 / 14), 23), ((-1 / 14), 25), ((3 / 28), 30), ((1 / 14), 31)],
      alternatingSixCyclotomicValue [((41 / 42), 0), ((-23 / 84), 3), ((-13 / 84), 5), ((-23 / 84), 7), ((5 / 14), 10), ((13 / 21), 15), ((23 / 84), 19), ((-95 / 84), 20), ((23 / 84), 23), ((65 / 84), 25), ((-9 / 7), 30), ((-23 / 84), 31)],
      alternatingSixCyclotomicValue [((-2 / 7), 0), ((-5 / 28), 3), ((3 / 7), 5), ((-5 / 28), 7), ((-2 / 7), 10), ((9 / 14), 15), ((5 / 28), 19), ((5 / 28), 20), ((5 / 28), 23), ((-1 / 7), 25), ((5 / 28), 30), ((-5 / 28), 31)],
      alternatingSixCyclotomicValue [((43 / 84), 0), ((-59 / 84), 3), ((-73 / 84), 5), ((-59 / 84), 7), ((-1 / 28), 10), ((1 / 84), 15), ((59 / 84), 19), ((-47 / 84), 20), ((59 / 84), 23), ((25 / 42), 25), ((-4 / 7), 30), ((-59 / 84), 31)],
      alternatingSixCyclotomicValue [((1 / 28), 0), ((-3 / 14), 3), ((-11 / 28), 5), ((-3 / 14), 7), ((3 / 14), 10), ((-5 / 28), 15), ((3 / 14), 19), ((9 / 28), 20), ((3 / 14), 23), ((3 / 14), 25), ((3 / 7), 30), ((-3 / 14), 31)],
      alternatingSixCyclotomicValue [((4 / 21), 0), ((1 / 4), 3), ((13 / 21), 5), ((1 / 4), 7), ((-31 / 84), 10), ((3 / 4), 15), ((-1 / 4), 19), ((-59 / 84), 20), ((-1 / 4), 23), ((13 / 84), 25), ((-17 / 42), 30), ((1 / 4), 31)]]
  ]

/-- The row 15 first generator in the checked diagonal basis. -/
def alternatingSixAmbientRow15TransformedGeneratorA :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((-3 / 4), 3), ((1 / 4), 5), ((-3 / 4), 7), ((-1 / 2), 10), ((3 / 4), 15), ((3 / 4), 19), ((1 / 4), 20), ((3 / 4), 23), ((-3 / 4), 25), ((1 / 4), 30), ((-3 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 2), 3), ((-1 / 2), 5), ((1 / 2), 7), ((1 / 2), 10), ((-1 / 2), 19), ((-1 / 4), 20), ((-1 / 2), 23), ((1 / 4), 25), ((1 / 2), 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 3), ((1 / 4), 7), ((1 / 4), 15), ((-1 / 4), 19), ((-1 / 4), 23), ((-1 / 4), 25), ((-1 / 4), 30), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 5), ((-1 / 4), 10), ((-1 / 2), 15), ((1 / 4), 20), ((-1 / 4), 25), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((5 / 292), 0), ((-111 / 292), 3), ((8 / 73), 5), ((-111 / 292), 7), ((22 / 73), 10), ((67 / 146), 15), ((111 / 292), 19), ((-33 / 292), 20), ((111 / 292), 23), ((-9 / 73), 25), ((-13 / 146), 30), ((-111 / 292), 31)],
      alternatingSixCyclotomicValue [((33 / 292), 0), ((3 / 73), 3), ((9 / 73), 5), ((3 / 73), 7), ((13 / 146), 10), ((-25 / 146), 15), ((-3 / 73), 19), ((45 / 292), 20), ((-3 / 73), 23), ((-77 / 292), 25), ((31 / 146), 30), ((3 / 73), 31)]],
    ![alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 4), 5), ((-1 / 2), 10), ((1 / 2), 15), ((-1 / 4), 25), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((3 / 4), 3), ((-1 / 4), 5), ((3 / 4), 7), ((3 / 4), 10), ((-1 / 2), 15), ((-3 / 4), 19), ((-1 / 4), 20), ((-3 / 4), 23), ((1 / 2), 25), ((-1 / 2), 30), ((3 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 3), ((-1 / 4), 7), ((-1 / 4), 10), ((-1 / 4), 15), ((1 / 4), 19), ((-1 / 2), 20), ((1 / 4), 23), ((1 / 2), 30), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 10), ((-1 / 4), 15), ((-1 / 4), 25), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((13 / 73), 0), ((145 / 292), 3), ((-19 / 73), 5), ((145 / 292), 7), ((-63 / 292), 10), ((-81 / 292), 15), ((-145 / 292), 19), ((51 / 292), 20), ((-145 / 292), 23), ((49 / 292), 25), ((-33 / 146), 30), ((145 / 292), 31)],
      alternatingSixCyclotomicValue [((11 / 146), 0), ((-65 / 292), 3), ((-49 / 292), 5), ((-65 / 292), 7), ((-7 / 292), 10), ((16 / 73), 15), ((65 / 292), 19), ((-43 / 292), 20), ((65 / 292), 23), ((23 / 146), 25), ((-14 / 73), 30), ((-65 / 292), 31)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 2), 3), ((-1 / 4), 5), ((1 / 2), 7), ((1 / 2), 10), ((-1 / 2), 15), ((-1 / 2), 19), ((-1 / 2), 23), ((1 / 4), 25), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((1 / 2), 0), (-1, 3), ((1 / 4), 5), (-1, 7), ((-1 / 4), 10), ((1 / 2), 15), (1, 19), ((1 / 4), 20), (1, 23), ((-1 / 4), 25), ((-1 / 2), 30), (-1, 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 3), ((-1 / 4), 5), ((-1 / 4), 7), ((-1 / 4), 10), ((1 / 4), 19), ((1 / 4), 23), ((1 / 4), 25), ((1 / 4), 30), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 3), ((-1 / 4), 7), ((-1 / 4), 15), ((1 / 4), 19), ((1 / 4), 20), ((1 / 4), 23), ((-1 / 4), 30), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((41 / 292), 0), ((-5 / 292), 3), ((-22 / 73), 5), ((-5 / 292), 7), ((123 / 292), 10), ((-113 / 292), 15), ((5 / 292), 19), ((109 / 292), 20), ((5 / 292), 23), ((-47 / 292), 25), ((35 / 292), 30), ((-5 / 292), 31)],
      alternatingSixCyclotomicValue [((-9 / 73), 0), ((10 / 73), 3), ((47 / 292), 5), ((10 / 73), 7), ((-35 / 292), 10), ((7 / 73), 15), ((-10 / 73), 19), ((-69 / 292), 20), ((-10 / 73), 23), ((11 / 292), 25), ((3 / 73), 30), ((10 / 73), 31)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 5), ((-1 / 2), 10), ((1 / 4), 25), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 3), ((1 / 4), 5), ((1 / 4), 7), ((-1 / 4), 10), ((-1 / 4), 19), ((-1 / 4), 20), ((-1 / 4), 23), ((1 / 2), 30), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 3), ((-1 / 4), 7), ((1 / 4), 10), ((1 / 4), 15), ((1 / 4), 19), ((1 / 4), 23), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 10), ((-1 / 4), 15), ((1 / 4), 25), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-29 / 146), 0), ((-41 / 292), 3), ((-25 / 146), 5), ((-41 / 292), 7), ((45 / 292), 10), ((37 / 292), 15), ((41 / 292), 19), ((47 / 292), 20), ((41 / 292), 23), ((-35 / 292), 25), ((-39 / 146), 30), ((-41 / 292), 31)],
      alternatingSixCyclotomicValue [((13 / 146), 0), ((-37 / 292), 3), ((35 / 292), 5), ((-37 / 292), 7), ((5 / 292), 10), ((-1 / 73), 15), ((37 / 292), 19), ((-11 / 292), 20), ((37 / 292), 23), ((-3 / 73), 25), ((10 / 73), 30), ((-37 / 292), 31)]],
    ![alternatingSixCyclotomicValue [((3 / 4), 0), ((-1 / 4), 3), ((1 / 4), 5), ((-1 / 4), 7), ((-1 / 2), 10), ((1 / 4), 15), ((1 / 4), 19), ((-1 / 4), 20), ((1 / 4), 23), ((-3 / 4), 25), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 3), ((-1 / 2), 5), ((1 / 4), 7), ((3 / 4), 10), ((-1 / 2), 15), ((-1 / 4), 19), ((-1 / 2), 20), ((-1 / 4), 23), ((1 / 2), 25), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 3), ((-1 / 4), 5), ((1 / 4), 7), ((-1 / 4), 10), ((-1 / 2), 15), ((-1 / 4), 19), ((-1 / 4), 20), ((-1 / 4), 23), ((1 / 2), 25), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 3), ((-1 / 4), 5), ((-1 / 4), 7), ((1 / 4), 10), ((1 / 2), 15), ((1 / 4), 19), ((1 / 4), 20), ((1 / 4), 23), ((1 / 2), 25), ((1 / 4), 30), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((4 / 73), 0), ((39 / 292), 3), ((-51 / 146), 5), ((39 / 292), 7), ((-49 / 146), 10), ((5 / 73), 15), ((-39 / 292), 19), ((-91 / 292), 20), ((-39 / 292), 23), ((15 / 73), 25), ((165 / 292), 30), ((39 / 292), 31)],
      alternatingSixCyclotomicValue [((9 / 146), 0), ((53 / 292), 3), ((-15 / 73), 5), ((53 / 292), 7), ((127 / 292), 10), ((-7 / 146), 15), ((-53 / 292), 19), ((-1 / 146), 20), ((-53 / 292), 23), ((26 / 73), 25), ((-3 / 146), 30), ((53 / 292), 31)]],
    ![alternatingSixCyclotomicValue [((3 / 4), 0), ((1 / 2), 3), ((-3 / 4), 5), ((1 / 2), 7), ((-1 / 2), 10), ((-1 / 2), 19), (-1, 20), ((-1 / 2), 23), ((-1 / 4), 25), ((1 / 2), 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 4), 5), ((3 / 4), 10), (-1, 15), ((1 / 4), 20), ((3 / 4), 25), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((3 / 4), 3), ((-3 / 4), 5), ((3 / 4), 7), ((-3 / 4), 10), ((-3 / 4), 19), ((3 / 2), 20), ((-3 / 4), 23), ((3 / 4), 25), ((-3 / 4), 30), ((3 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 3), ((1 / 4), 7), ((-1 / 4), 15), ((-1 / 4), 19), ((-1 / 4), 20), ((-1 / 4), 23), ((-1 / 4), 30), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((-71 / 292), 0), ((-59 / 292), 3), ((21 / 146), 5), ((-59 / 292), 7), ((79 / 292), 10), ((-107 / 292), 15), ((59 / 292), 19), ((89 / 292), 20), ((59 / 292), 23), ((117 / 292), 25), ((-171 / 292), 30), ((-59 / 292), 31)],
      alternatingSixCyclotomicValue [((-4 / 73), 0), ((17 / 146), 3), ((175 / 292), 5), ((17 / 146), 7), ((25 / 292), 10), ((-5 / 73), 15), ((-17 / 146), 19), ((91 / 292), 20), ((-17 / 146), 23), ((-133 / 292), 25), ((-23 / 73), 30), ((17 / 146), 31)]]
  ]

macro "close_cyclotomic_row15" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)


private theorem row15_eigenbasisInverse_mul_0_0 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        0 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((7 / 4) : ℂ) + ((49 / 12) : ℂ) * ζ ^ 3 + ((7 / 4) : ℂ) * ζ ^ 4 - ((17 / 12) : ℂ) * ζ ^ 5 - ((7 / 2) : ℂ) * ζ ^ 6 - ((53 / 12) : ℂ) * ζ ^ 8 + ((17 / 12) : ℂ) * ζ ^ 9 + ((5 / 12) : ℂ) * ζ ^ 10 + ((23 / 12) : ℂ) * ζ ^ 13 - ((47 / 12) : ℂ) * ζ ^ 14 - ((41 / 12) : ℂ) * ζ ^ 15 + ((13 / 6) : ℂ) * ζ ^ 18 + ((41 / 12) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 20 + ((7 / 2) : ℂ) * ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 23 + ((1 / 4) : ℂ) * ζ ^ 24 + ((35 / 12) : ℂ) * ζ ^ 25 + ((7 / 2) : ℂ) * ζ ^ 26 + ((13 / 12) : ℂ) * ζ ^ 28 - ((35 / 12) : ℂ) * ζ ^ 29 - ((7 / 2) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_0_1 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        0 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((11 / 6) : ℂ) - ((7 / 2) : ℂ) * ζ ^ 3 - ((11 / 6) : ℂ) * ζ ^ 4 + ((17 / 6) : ℂ) * ζ ^ 5 + ((7 / 4) : ℂ) * ζ ^ 6 + ((5 / 3) : ℂ) * ζ ^ 8 - ((17 / 6) : ℂ) * ζ ^ 9 - ((19 / 4) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 13 + ((13 / 2) : ℂ) * ζ ^ 14 + ((17 / 6) : ℂ) * ζ ^ 15 - ((35 / 12) : ℂ) * ζ ^ 18 - ((17 / 6) : ℂ) * ζ ^ 19 - ((1 / 3) : ℂ) * ζ ^ 20 - ((7 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 23 + ((1 / 3) : ℂ) * ζ ^ 24 - ((10 / 3) : ℂ) * ζ ^ 25 - ((7 / 4) : ℂ) * ζ ^ 26 + ((1 / 3) : ℂ) * ζ ^ 28 + ((10 / 3) : ℂ) * ζ ^ 29 + ((7 / 4) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_0_2 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        0 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((17 / 12) : ℂ) + ((47 / 12) : ℂ) * ζ ^ 3 + ((17 / 12) : ℂ) * ζ ^ 4 + ((11 / 4) : ℂ) * ζ ^ 5 + ((2 / 3) : ℂ) * ζ ^ 6 - ((5 / 2) : ℂ) * ζ ^ 8 - ((11 / 4) : ℂ) * ζ ^ 9 + ((5 / 2) : ℂ) * ζ ^ 10 - ((11 / 6) : ℂ) * ζ ^ 14 - ((25 / 12) : ℂ) * ζ ^ 15 - ((5 / 6) : ℂ) * ζ ^ 18 + ((25 / 12) : ℂ) * ζ ^ 19 + ((2 / 3) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 - ((3 / 2) : ℂ) * ζ ^ 23 - ((2 / 3) : ℂ) * ζ ^ 24 - ((37 / 12) : ℂ) * ζ ^ 25 - ((2 / 3) : ℂ) * ζ ^ 26 + ((11 / 12) : ℂ) * ζ ^ 28 + ((37 / 12) : ℂ) * ζ ^ 29 + ((2 / 3) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_0_3 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        0 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((8 / 3) : ℂ) + ((7 / 4) : ℂ) * ζ ^ 3 + ((8 / 3) : ℂ) * ζ ^ 4 + ((4 / 3) : ℂ) * ζ ^ 5 + ((1 / 2) : ℂ) * ζ ^ 6 - ((41 / 12) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 9 - ((13 / 12) : ℂ) * ζ ^ 10 - ((5 / 12) : ℂ) * ζ ^ 13 + ((19 / 12) : ℂ) * ζ ^ 14 - ((13 / 4) : ℂ) * ζ ^ 15 - ((2 / 3) : ℂ) * ζ ^ 18 + ((13 / 4) : ℂ) * ζ ^ 19 + ((4 / 3) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((11 / 4) : ℂ) * ζ ^ 23 - ((4 / 3) : ℂ) * ζ ^ 24 - ((47 / 12) : ℂ) * ζ ^ 25 - ((1 / 2) : ℂ) * ζ ^ 26 + ((5 / 3) : ℂ) * ζ ^ 28 + ((47 / 12) : ℂ) * ζ ^ 29 + ((1 / 2) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_0_4 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        0 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((95 / 292) : ℂ) - ((985 / 876) : ℂ) * ζ ^ 3 + ((95 / 292) : ℂ) * ζ ^ 4 + ((1067 / 876) : ℂ) * ζ ^ 5 + ((337 / 292) : ℂ) * ζ ^ 6 + ((209 / 876) : ℂ) * ζ ^ 8 - ((1067 / 876) : ℂ) * ζ ^ 9 - ((187 / 438) : ℂ) * ζ ^ 10 + ((59 / 73) : ℂ) * ζ ^ 13 + ((1385 / 876) : ℂ) * ζ ^ 14 + ((1861 / 876) : ℂ) * ζ ^ 15 - ((108 / 73) : ℂ) * ζ ^ 18 - ((1861 / 876) : ℂ) * ζ ^ 19 - ((164 / 219) : ℂ) * ζ ^ 20 - ((337 / 292) : ℂ) * ζ ^ 22 + ((649 / 438) : ℂ) * ζ ^ 23 + ((164 / 219) : ℂ) * ζ ^ 24 + ((75 / 146) : ℂ) * ζ ^ 25 - ((337 / 292) : ℂ) * ζ ^ 26 - ((133 / 292) : ℂ) * ζ ^ 28 - ((75 / 146) : ℂ) * ζ ^ 29 + ((337 / 292) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_0_5 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        0 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((163 / 876) : ℂ) - ((25 / 146) : ℂ) * ζ ^ 3 - ((163 / 876) : ℂ) * ζ ^ 4 - ((1601 / 876) : ℂ) * ζ ^ 5 + ((22 / 219) : ℂ) * ζ ^ 6 + ((737 / 876) : ℂ) * ζ ^ 8 + ((1601 / 876) : ℂ) * ζ ^ 9 + ((152 / 73) : ℂ) * ζ ^ 10 - ((1649 / 876) : ℂ) * ζ ^ 13 - ((434 / 219) : ℂ) * ζ ^ 14 - ((1385 / 438) : ℂ) * ζ ^ 15 + ((463 / 292) : ℂ) * ζ ^ 18 + ((1385 / 438) : ℂ) * ζ ^ 19 + ((1525 / 876) : ℂ) * ζ ^ 20 - ((22 / 219) : ℂ) * ζ ^ 22 - ((1031 / 438) : ℂ) * ζ ^ 23 - ((1525 / 876) : ℂ) * ζ ^ 24 - ((81 / 73) : ℂ) * ζ ^ 25 - ((22 / 219) : ℂ) * ζ ^ 26 + ((355 / 438) : ℂ) * ζ ^ 28 + ((81 / 73) : ℂ) * ζ ^ 29 + ((22 / 219) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_1_0 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        1 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((9 / 28) : ℂ) + ((5 / 84) : ℂ) * ζ ^ 3 - ((9 / 28) : ℂ) * ζ ^ 4 - ((1 / 12) : ℂ) * ζ ^ 5 + ((43 / 28) : ℂ) * ζ ^ 6 + ((53 / 84) : ℂ) * ζ ^ 8 + ((1 / 12) : ℂ) * ζ ^ 9 + ((25 / 12) : ℂ) * ζ ^ 10 + ((121 / 84) : ℂ) * ζ ^ 13 - ((23 / 42) : ℂ) * ζ ^ 14 + ((2 / 3) : ℂ) * ζ ^ 15 - ((71 / 84) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 19 + ((4 / 7) : ℂ) * ζ ^ 20 - ((43 / 28) : ℂ) * ζ ^ 22 + ((85 / 84) : ℂ) * ζ ^ 23 - ((4 / 7) : ℂ) * ζ ^ 24 + ((11 / 42) : ℂ) * ζ ^ 25 - ((43 / 28) : ℂ) * ζ ^ 26 + ((17 / 84) : ℂ) * ζ ^ 28 - ((11 / 42) : ℂ) * ζ ^ 29 + ((43 / 28) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_1_1 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        1 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((13 / 12) : ℂ) + ((13 / 14) : ℂ) * ζ ^ 3 + ((13 / 12) : ℂ) * ζ ^ 4 + ((20 / 21) : ℂ) * ζ ^ 5 - ((7 / 4) : ℂ) * ζ ^ 6 - ((71 / 84) : ℂ) * ζ ^ 8 - ((20 / 21) : ℂ) * ζ ^ 9 - ((18 / 7) : ℂ) * ζ ^ 10 - ((11 / 42) : ℂ) * ζ ^ 13 + ((23 / 28) : ℂ) * ζ ^ 14 - ((1 / 21) : ℂ) * ζ ^ 15 + ((11 / 84) : ℂ) * ζ ^ 18 + ((1 / 21) : ℂ) * ζ ^ 19 - ((101 / 84) : ℂ) * ζ ^ 20 + ((7 / 4) : ℂ) * ζ ^ 22 + ((2 / 7) : ℂ) * ζ ^ 23 + ((101 / 84) : ℂ) * ζ ^ 24 + ((19 / 21) : ℂ) * ζ ^ 25 + ((7 / 4) : ℂ) * ζ ^ 26 - ((23 / 42) : ℂ) * ζ ^ 28 - ((19 / 21) : ℂ) * ζ ^ 29 - ((7 / 4) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_1_2 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        1 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((25 / 84) : ℂ) - ((13 / 42) : ℂ) * ζ ^ 3 + ((25 / 84) : ℂ) * ζ ^ 4 + ((11 / 28) : ℂ) * ζ ^ 5 + ((1 / 3) : ℂ) * ζ ^ 6 - ((3 / 28) : ℂ) * ζ ^ 8 - ((11 / 28) : ℂ) * ζ ^ 9 - ((15 / 28) : ℂ) * ζ ^ 10 + ((11 / 14) : ℂ) * ζ ^ 13 + ((73 / 84) : ℂ) * ζ ^ 14 + ((29 / 42) : ℂ) * ζ ^ 15 - ((7 / 6) : ℂ) * ζ ^ 18 - ((29 / 42) : ℂ) * ζ ^ 19 - ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 3) : ℂ) * ζ ^ 22 + ((1 / 6) : ℂ) * ζ ^ 24 + ((10 / 21) : ℂ) * ζ ^ 25 - ((1 / 3) : ℂ) * ζ ^ 26 - ((31 / 42) : ℂ) * ζ ^ 28 - ((10 / 21) : ℂ) * ζ ^ 29 + ((1 / 3) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_1_3 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        1 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((13 / 84) : ℂ) - ((13 / 28) : ℂ) * ζ ^ 3 + ((13 / 84) : ℂ) * ζ ^ 4 - ((37 / 84) : ℂ) * ζ ^ 5 + ((9 / 28) : ℂ) * ζ ^ 6 - ((17 / 42) : ℂ) * ζ ^ 8 + ((37 / 84) : ℂ) * ζ ^ 9 + ((19 / 84) : ℂ) * ζ ^ 10 - ((17 / 42) : ℂ) * ζ ^ 13 + ((2 / 21) : ℂ) * ζ ^ 14 + ((5 / 7) : ℂ) * ζ ^ 15 - ((41 / 42) : ℂ) * ζ ^ 18 - ((5 / 7) : ℂ) * ζ ^ 19 + ((5 / 84) : ℂ) * ζ ^ 20 - ((9 / 28) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 23 - ((5 / 84) : ℂ) * ζ ^ 24 + ((29 / 21) : ℂ) * ζ ^ 25 - ((9 / 28) : ℂ) * ζ ^ 26 - ((19 / 42) : ℂ) * ζ ^ 28 - ((29 / 21) : ℂ) * ζ ^ 29 + ((9 / 28) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_1_4 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        1 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((187 / 511) : ℂ) - ((446 / 1533) : ℂ) * ζ ^ 3 - ((187 / 511) : ℂ) * ζ ^ 4 + ((829 / 6132) : ℂ) * ζ ^ 5 - ((15 / 292) : ℂ) * ζ ^ 6 + ((3763 / 6132) : ℂ) * ζ ^ 8 - ((829 / 6132) : ℂ) * ζ ^ 9 + ((3995 / 6132) : ℂ) * ζ ^ 10 - ((695 / 2044) : ℂ) * ζ ^ 13 - ((2155 / 3066) : ℂ) * ζ ^ 14 + ((431 / 6132) : ℂ) * ζ ^ 15 + ((303 / 511) : ℂ) * ζ ^ 18 - ((431 / 6132) : ℂ) * ζ ^ 19 + ((2197 / 3066) : ℂ) * ζ ^ 20 + ((15 / 292) : ℂ) * ζ ^ 22 - ((2087 / 6132) : ℂ) * ζ ^ 23 - ((2197 / 3066) : ℂ) * ζ ^ 24 - ((127 / 1022) : ℂ) * ζ ^ 25 + ((15 / 292) : ℂ) * ζ ^ 26 + ((155 / 2044) : ℂ) * ζ ^ 28 + ((127 / 1022) : ℂ) * ζ ^ 29 - ((15 / 292) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_1_5 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        1 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((143 / 3066) : ℂ) + ((937 / 2044) : ℂ) * ζ ^ 3 + ((143 / 3066) : ℂ) * ζ ^ 4 + ((991 / 3066) : ℂ) * ζ ^ 5 - ((151 / 876) : ℂ) * ζ ^ 6 - ((956 / 1533) : ℂ) * ζ ^ 8 - ((991 / 3066) : ℂ) * ζ ^ 9 - ((971 / 1022) : ℂ) * ζ ^ 10 + ((3467 / 6132) : ℂ) * ζ ^ 13 + ((4769 / 6132) : ℂ) * ζ ^ 14 + ((817 / 1533) : ℂ) * ζ ^ 15 - ((165 / 292) : ℂ) * ζ ^ 18 - ((817 / 1533) : ℂ) * ζ ^ 19 - ((713 / 3066) : ℂ) * ζ ^ 20 + ((151 / 876) : ℂ) * ζ ^ 22 + ((451 / 1533) : ℂ) * ζ ^ 23 + ((713 / 3066) : ℂ) * ζ ^ 24 + ((645 / 2044) : ℂ) * ζ ^ 25 + ((151 / 876) : ℂ) * ζ ^ 26 + ((257 / 3066) : ℂ) * ζ ^ 28 - ((645 / 2044) : ℂ) * ζ ^ 29 - ((151 / 876) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_2_0 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        2 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((1 / 84) : ℂ) + ((97 / 28) : ℂ) * ζ ^ 3 - ((1 / 84) : ℂ) * ζ ^ 4 - ((29 / 42) : ℂ) * ζ ^ 5 - ((81 / 28) : ℂ) * ζ ^ 6 - ((209 / 84) : ℂ) * ζ ^ 8 + ((29 / 42) : ℂ) * ζ ^ 9 - ((13 / 42) : ℂ) * ζ ^ 10 + ((25 / 42) : ℂ) * ζ ^ 13 - ((31 / 12) : ℂ) * ζ ^ 14 - ((7 / 4) : ℂ) * ζ ^ 15 + ((109 / 84) : ℂ) * ζ ^ 18 + ((7 / 4) : ℂ) * ζ ^ 19 + ((17 / 84) : ℂ) * ζ ^ 20 + ((81 / 28) : ℂ) * ζ ^ 22 - ((3 / 2) : ℂ) * ζ ^ 23 - ((17 / 84) : ℂ) * ζ ^ 24 + ((10 / 7) : ℂ) * ζ ^ 25 + ((81 / 28) : ℂ) * ζ ^ 26 - ((19 / 84) : ℂ) * ζ ^ 28 - ((10 / 7) : ℂ) * ζ ^ 29 - ((81 / 28) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_2_1 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        2 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((5 / 42) : ℂ) - ((29 / 12) : ℂ) * ζ ^ 3 - ((5 / 42) : ℂ) * ζ ^ 4 + ((12 / 7) : ℂ) * ζ ^ 5 + ((27 / 14) : ℂ) * ζ ^ 6 + ((79 / 84) : ℂ) * ζ ^ 8 - ((12 / 7) : ℂ) * ζ ^ 9 - ((5 / 3) : ℂ) * ζ ^ 10 + ((33 / 28) : ℂ) * ζ ^ 13 + ((151 / 42) : ℂ) * ζ ^ 14 + ((209 / 84) : ℂ) * ζ ^ 15 - ((43 / 42) : ℂ) * ζ ^ 18 - ((209 / 84) : ℂ) * ζ ^ 19 - ((4 / 21) : ℂ) * ζ ^ 20 - ((27 / 14) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 23 + ((4 / 21) : ℂ) * ζ ^ 24 - ((27 / 14) : ℂ) * ζ ^ 25 - ((27 / 14) : ℂ) * ζ ^ 26 + ((17 / 12) : ℂ) * ζ ^ 28 + ((27 / 14) : ℂ) * ζ ^ 29 + ((27 / 14) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_2_2 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        2 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((75 / 28) : ℂ) + ((41 / 28) : ℂ) * ζ ^ 3 + ((75 / 28) : ℂ) * ζ ^ 4 + ((121 / 84) : ℂ) * ζ ^ 5 - ((9 / 28) : ℂ) * ζ ^ 6 - ((295 / 84) : ℂ) * ζ ^ 8 - ((121 / 84) : ℂ) * ζ ^ 9 + ((26 / 21) : ℂ) * ζ ^ 10 - ((5 / 42) : ℂ) * ζ ^ 13 - ((131 / 84) : ℂ) * ζ ^ 14 - ((53 / 42) : ℂ) * ζ ^ 15 + ((2 / 21) : ℂ) * ζ ^ 18 + ((53 / 42) : ℂ) * ζ ^ 19 + ((37 / 42) : ℂ) * ζ ^ 20 + ((9 / 28) : ℂ) * ζ ^ 22 + ((31 / 84) : ℂ) * ζ ^ 23 - ((37 / 42) : ℂ) * ζ ^ 24 - ((101 / 42) : ℂ) * ζ ^ 25 + ((9 / 28) : ℂ) * ζ ^ 26 + ((11 / 6) : ℂ) * ζ ^ 28 + ((101 / 42) : ℂ) * ζ ^ 29 - ((9 / 28) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_2_3 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        2 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((26 / 21) : ℂ) + ((97 / 84) : ℂ) * ζ ^ 3 + ((26 / 21) : ℂ) * ζ ^ 4 + ((41 / 21) : ℂ) * ζ ^ 5 + ((9 / 28) : ℂ) * ζ ^ 6 - ((5 / 3) : ℂ) * ζ ^ 8 - ((41 / 21) : ℂ) * ζ ^ 9 + ((1 / 7) : ℂ) * ζ ^ 10 + ((95 / 84) : ℂ) * ζ ^ 13 + ((5 / 28) : ℂ) * ζ ^ 14 - ((89 / 84) : ℂ) * ζ ^ 15 + ((27 / 28) : ℂ) * ζ ^ 18 + ((89 / 84) : ℂ) * ζ ^ 19 + ((145 / 84) : ℂ) * ζ ^ 20 - ((9 / 28) : ℂ) * ζ ^ 22 - ((47 / 84) : ℂ) * ζ ^ 23 - ((145 / 84) : ℂ) * ζ ^ 24 - ((39 / 14) : ℂ) * ζ ^ 25 - ((9 / 28) : ℂ) * ζ ^ 26 + ((7 / 3) : ℂ) * ζ ^ 28 + ((39 / 14) : ℂ) * ζ ^ 29 + ((9 / 28) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_2_4 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        2 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((43 / 438) : ℂ) - ((262 / 511) : ℂ) * ζ ^ 3 - ((43 / 438) : ℂ) * ζ ^ 4 + ((2123 / 3066) : ℂ) * ζ ^ 5 + ((173 / 511) : ℂ) * ζ ^ 6 - ((1207 / 6132) : ℂ) * ζ ^ 8 - ((2123 / 3066) : ℂ) * ζ ^ 9 - ((2509 / 3066) : ℂ) * ζ ^ 10 + ((244 / 1533) : ℂ) * ζ ^ 13 + ((3547 / 3066) : ℂ) * ζ ^ 14 + ((1108 / 1533) : ℂ) * ζ ^ 15 - ((1670 / 1533) : ℂ) * ζ ^ 18 - ((1108 / 1533) : ℂ) * ζ ^ 19 - ((603 / 511) : ℂ) * ζ ^ 20 - ((173 / 511) : ℂ) * ζ ^ 22 + ((3131 / 3066) : ℂ) * ζ ^ 23 + ((603 / 511) : ℂ) * ζ ^ 24 - ((134 / 511) : ℂ) * ζ ^ 25 - ((173 / 511) : ℂ) * ζ ^ 26 - ((361 / 1022) : ℂ) * ζ ^ 28 + ((134 / 511) : ℂ) * ζ ^ 29 + ((173 / 511) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_2_5 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        2 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((256 / 1533) : ℂ) - ((136 / 1533) : ℂ) * ζ ^ 3 - ((256 / 1533) : ℂ) * ζ ^ 4 - ((4987 / 6132) : ℂ) * ζ ^ 5 + ((523 / 2044) : ℂ) * ζ ^ 6 + ((1976 / 1533) : ℂ) * ζ ^ 8 + ((4987 / 6132) : ℂ) * ζ ^ 9 + ((11747 / 6132) : ℂ) * ζ ^ 10 - ((1733 / 1533) : ℂ) * ζ ^ 13 - ((727 / 438) : ℂ) * ζ ^ 14 - ((4807 / 3066) : ℂ) * ζ ^ 15 + ((2483 / 1533) : ℂ) * ζ ^ 18 + ((4807 / 3066) : ℂ) * ζ ^ 19 + ((3309 / 2044) : ℂ) * ζ ^ 20 - ((523 / 2044) : ℂ) * ζ ^ 22 - ((3221 / 3066) : ℂ) * ζ ^ 23 - ((3309 / 2044) : ℂ) * ζ ^ 24 - ((1091 / 1533) : ℂ) * ζ ^ 25 - ((523 / 2044) : ℂ) * ζ ^ 26 + ((682 / 1533) : ℂ) * ζ ^ 28 + ((1091 / 1533) : ℂ) * ζ ^ 29 + ((523 / 2044) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_3_0 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        3 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((47 / 84) : ℂ) - ((11 / 28) : ℂ) * ζ ^ 3 + ((47 / 84) : ℂ) * ζ ^ 4 + ((107 / 84) : ℂ) * ζ ^ 5 + ((1 / 28) : ℂ) * ζ ^ 6 + ((43 / 84) : ℂ) * ζ ^ 8 - ((107 / 84) : ℂ) * ζ ^ 9 - ((149 / 84) : ℂ) * ζ ^ 10 - ((25 / 12) : ℂ) * ζ ^ 13 + ((38 / 21) : ℂ) * ζ ^ 14 + ζ ^ 15 + ((223 / 84) : ℂ) * ζ ^ 18 - ζ ^ 19 - ((4 / 3) : ℂ) * ζ ^ 20 - ((1 / 28) : ℂ) * ζ ^ 22 - ((57 / 28) : ℂ) * ζ ^ 23 + ((4 / 3) : ℂ) * ζ ^ 24 + ((11 / 14) : ℂ) * ζ ^ 25 - ((1 / 28) : ℂ) * ζ ^ 26 + ((59 / 84) : ℂ) * ζ ^ 28 - ((11 / 14) : ℂ) * ζ ^ 29 + ((1 / 28) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_3_1 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        3 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((151 / 84) : ℂ) - ((103 / 42) : ℂ) * ζ ^ 3 - ((151 / 84) : ℂ) * ζ ^ 4 - ((43 / 14) : ℂ) * ζ ^ 5 + ((37 / 28) : ℂ) * ζ ^ 6 + ((211 / 84) : ℂ) * ζ ^ 8 + ((43 / 14) : ℂ) * ζ ^ 9 + ((85 / 21) : ℂ) * ζ ^ 10 - ((1 / 7) : ℂ) * ζ ^ 13 - ((229 / 84) : ℂ) * ζ ^ 14 - ((137 / 42) : ℂ) * ζ ^ 15 - ((59 / 84) : ℂ) * ζ ^ 18 + ((137 / 42) : ℂ) * ζ ^ 19 + ((305 / 84) : ℂ) * ζ ^ 20 - ((37 / 28) : ℂ) * ζ ^ 22 + ((13 / 42) : ℂ) * ζ ^ 23 - ((305 / 84) : ℂ) * ζ ^ 24 - ((25 / 14) : ℂ) * ζ ^ 25 - ((37 / 28) : ℂ) * ζ ^ 26 + ((13 / 42) : ℂ) * ζ ^ 28 + ((25 / 14) : ℂ) * ζ ^ 29 + ((37 / 28) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_3_2 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        3 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((65 / 28) : ℂ) - ((9 / 7) : ℂ) * ζ ^ 3 - ((65 / 28) : ℂ) * ζ ^ 4 - ((269 / 84) : ℂ) * ζ ^ 5 - ((13 / 14) : ℂ) * ζ ^ 6 + ((23 / 12) : ℂ) * ζ ^ 8 + ((269 / 84) : ℂ) * ζ ^ 9 + ((59 / 84) : ℂ) * ζ ^ 10 - ((101 / 42) : ℂ) * ζ ^ 13 - ((137 / 84) : ℂ) * ζ ^ 14 - ((41 / 42) : ℂ) * ζ ^ 15 + ((115 / 42) : ℂ) * ζ ^ 18 + ((41 / 42) : ℂ) * ζ ^ 19 - ((1 / 21) : ℂ) * ζ ^ 20 + ((13 / 14) : ℂ) * ζ ^ 22 - ((61 / 42) : ℂ) * ζ ^ 23 + ((1 / 21) : ℂ) * ζ ^ 24 + ((55 / 42) : ℂ) * ζ ^ 25 + ((13 / 14) : ℂ) * ζ ^ 26 + ((22 / 21) : ℂ) * ζ ^ 28 - ((55 / 42) : ℂ) * ζ ^ 29 - ((13 / 14) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_3_3 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        3 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((31 / 84) : ℂ) - ((29 / 84) : ℂ) * ζ ^ 3 - ((31 / 84) : ℂ) * ζ ^ 4 - ((109 / 84) : ℂ) * ζ ^ 5 - ((15 / 28) : ℂ) * ζ ^ 6 + ((23 / 42) : ℂ) * ζ ^ 8 + ((109 / 84) : ℂ) * ζ ^ 9 + ((5 / 28) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 13 - ((5 / 7) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 15 + ((17 / 14) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 19 + ((1 / 84) : ℂ) * ζ ^ 20 + ((15 / 28) : ℂ) * ζ ^ 22 - ((11 / 21) : ℂ) * ζ ^ 23 - ((1 / 84) : ℂ) * ζ ^ 24 + ((8 / 7) : ℂ) * ζ ^ 25 + ((15 / 28) : ℂ) * ζ ^ 26 + ((29 / 42) : ℂ) * ζ ^ 28 - ((8 / 7) : ℂ) * ζ ^ 29 - ((15 / 28) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_3_4 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        3 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((2351 / 3066) : ℂ) + ((589 / 511) : ℂ) * ζ ^ 3 + ((2351 / 3066) : ℂ) * ζ ^ 4 + ((2941 / 6132) : ℂ) * ζ ^ 5 - ((1049 / 2044) : ℂ) * ζ ^ 6 - ((10243 / 6132) : ℂ) * ζ ^ 8 - ((2941 / 6132) : ℂ) * ζ ^ 9 - ((6155 / 6132) : ℂ) * ζ ^ 10 + ((8443 / 6132) : ℂ) * ζ ^ 13 + ((752 / 1533) : ℂ) * ζ ^ 14 + ((1849 / 6132) : ℂ) * ζ ^ 15 - ((257 / 219) : ℂ) * ζ ^ 18 - ((1849 / 6132) : ℂ) * ζ ^ 19 - ((170 / 511) : ℂ) * ζ ^ 20 + ((1049 / 2044) : ℂ) * ζ ^ 22 + ((5473 / 6132) : ℂ) * ζ ^ 23 + ((170 / 511) : ℂ) * ζ ^ 24 + ((104 / 511) : ℂ) * ζ ^ 25 + ((1049 / 2044) : ℂ) * ζ ^ 26 - ((583 / 2044) : ℂ) * ζ ^ 28 - ((104 / 511) : ℂ) * ζ ^ 29 - ((1049 / 2044) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_3_5 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        3 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((2104 / 1533) : ℂ) - ((955 / 876) : ℂ) * ζ ^ 3 - ((2104 / 1533) : ℂ) * ζ ^ 4 - ((377 / 438) : ℂ) * ζ ^ 5 + ((289 / 2044) : ℂ) * ζ ^ 6 + ((2747 / 1533) : ℂ) * ζ ^ 8 + ((377 / 438) : ℂ) * ζ ^ 9 + ((1214 / 1533) : ℂ) * ζ ^ 10 - ((7319 / 6132) : ℂ) * ζ ^ 13 - ((3989 / 6132) : ℂ) * ζ ^ 14 - ((632 / 1533) : ℂ) * ζ ^ 15 + ((3767 / 6132) : ℂ) * ζ ^ 18 + ((632 / 1533) : ℂ) * ζ ^ 19 + ((17 / 73) : ℂ) * ζ ^ 20 - ((289 / 2044) : ℂ) * ζ ^ 22 - ((941 / 3066) : ℂ) * ζ ^ 23 - ((17 / 73) : ℂ) * ζ ^ 24 - ((713 / 6132) : ℂ) * ζ ^ 25 - ((289 / 2044) : ℂ) * ζ ^ 26 + ((113 / 438) : ℂ) * ζ ^ 28 + ((713 / 6132) : ℂ) * ζ ^ 29 + ((289 / 2044) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_4_0 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        4 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((59 / 84) : ℂ) - ((15 / 7) : ℂ) * ζ ^ 3 - ((59 / 84) : ℂ) * ζ ^ 4 - ((59 / 84) : ℂ) * ζ ^ 5 - ((11 / 28) : ℂ) * ζ ^ 6 - ((127 / 84) : ℂ) * ζ ^ 8 + ((59 / 84) : ℂ) * ζ ^ 9 - ((23 / 42) : ℂ) * ζ ^ 10 - ((13 / 42) : ℂ) * ζ ^ 13 + ((13 / 84) : ℂ) * ζ ^ 14 - (2 : ℂ) * ζ ^ 15 - ((131 / 42) : ℂ) * ζ ^ 18 + (2 : ℂ) * ζ ^ 19 + ((13 / 84) : ℂ) * ζ ^ 20 + ((11 / 28) : ℂ) * ζ ^ 22 + ((45 / 28) : ℂ) * ζ ^ 23 - ((13 / 84) : ℂ) * ζ ^ 24 - ((7 / 4) : ℂ) * ζ ^ 25 + ((11 / 28) : ℂ) * ζ ^ 26 - ((17 / 21) : ℂ) * ζ ^ 28 + ((7 / 4) : ℂ) * ζ ^ 29 - ((11 / 28) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_4_1 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        4 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((97 / 84) : ℂ) + ((169 / 42) : ℂ) * ζ ^ 3 + ((97 / 84) : ℂ) * ζ ^ 4 + ((39 / 28) : ℂ) * ζ ^ 5 - ((5 / 14) : ℂ) * ζ ^ 6 - ((97 / 84) : ℂ) * ζ ^ 8 - ((39 / 28) : ℂ) * ζ ^ 9 - ((145 / 84) : ℂ) * ζ ^ 10 + ((29 / 28) : ℂ) * ζ ^ 13 + ((115 / 84) : ℂ) * ζ ^ 14 + ((137 / 42) : ℂ) * ζ ^ 15 + ((47 / 84) : ℂ) * ζ ^ 18 - ((137 / 42) : ℂ) * ζ ^ 19 - ((149 / 84) : ℂ) * ζ ^ 20 + ((5 / 14) : ℂ) * ζ ^ 22 - ((71 / 84) : ℂ) * ζ ^ 23 + ((149 / 84) : ℂ) * ζ ^ 24 + ((9 / 4) : ℂ) * ζ ^ 25 + ((5 / 14) : ℂ) * ζ ^ 26 - ((71 / 84) : ℂ) * ζ ^ 28 - ((9 / 4) : ℂ) * ζ ^ 29 - ((5 / 14) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_4_2 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        4 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((9 / 28) : ℂ) + ((43 / 28) : ℂ) * ζ ^ 3 + ((9 / 28) : ℂ) * ζ ^ 4 + ((68 / 21) : ℂ) * ζ ^ 5 + ((25 / 28) : ℂ) * ζ ^ 6 - ((1 / 42) : ℂ) * ζ ^ 8 - ((68 / 21) : ℂ) * ζ ^ 9 - ((8 / 21) : ℂ) * ζ ^ 10 + ((229 / 84) : ℂ) * ζ ^ 13 + ((107 / 84) : ℂ) * ζ ^ 14 + ((13 / 84) : ℂ) * ζ ^ 15 - ((107 / 84) : ℂ) * ζ ^ 18 - ((13 / 84) : ℂ) * ζ ^ 19 - ((25 / 42) : ℂ) * ζ ^ 20 - ((25 / 28) : ℂ) * ζ ^ 22 + ((23 / 21) : ℂ) * ζ ^ 23 + ((25 / 42) : ℂ) * ζ ^ 24 - ((83 / 84) : ℂ) * ζ ^ 25 - ((25 / 28) : ℂ) * ζ ^ 26 - ((103 / 84) : ℂ) * ζ ^ 28 + ((83 / 84) : ℂ) * ζ ^ 29 + ((25 / 28) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_4_3 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        4 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((2 / 3) : ℂ) + ((23 / 21) : ℂ) * ζ ^ 3 - ((2 / 3) : ℂ) * ζ ^ 4 + ((65 / 42) : ℂ) * ζ ^ 5 + ((1 / 2) : ℂ) * ζ ^ 6 + ((43 / 42) : ℂ) * ζ ^ 8 - ((65 / 42) : ℂ) * ζ ^ 9 - ((1 / 4) : ℂ) * ζ ^ 10 + ((43 / 84) : ℂ) * ζ ^ 13 + ((3 / 4) : ℂ) * ζ ^ 14 - ((5 / 42) : ℂ) * ζ ^ 15 - ((5 / 7) : ℂ) * ζ ^ 18 + ((5 / 42) : ℂ) * ζ ^ 19 - ((13 / 12) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 + ((19 / 42) : ℂ) * ζ ^ 23 + ((13 / 12) : ℂ) * ζ ^ 24 - ζ ^ 25 - ((1 / 2) : ℂ) * ζ ^ 26 - ((59 / 42) : ℂ) * ζ ^ 28 + ζ ^ 29 + ((1 / 2) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_4_4 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        4 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((635 / 1533) : ℂ) - ((2199 / 2044) : ℂ) * ζ ^ 3 + ((635 / 1533) : ℂ) * ζ ^ 4 - ((8227 / 6132) : ℂ) * ζ ^ 5 + ((933 / 2044) : ℂ) * ζ ^ 6 + ((721 / 876) : ℂ) * ζ ^ 8 + ((8227 / 6132) : ℂ) * ζ ^ 9 + ((212 / 1533) : ℂ) * ζ ^ 10 - ((1597 / 1533) : ℂ) * ζ ^ 13 + ((1951 / 6132) : ℂ) * ζ ^ 14 - ((1591 / 1533) : ℂ) * ζ ^ 15 + ((1469 / 1533) : ℂ) * ζ ^ 18 + ((1591 / 1533) : ℂ) * ζ ^ 19 + ((18 / 511) : ℂ) * ζ ^ 20 - ((933 / 2044) : ℂ) * ζ ^ 22 - ((1273 / 1533) : ℂ) * ζ ^ 23 - ((18 / 511) : ℂ) * ζ ^ 24 + ((8 / 511) : ℂ) * ζ ^ 25 - ((933 / 2044) : ℂ) * ζ ^ 26 + ((935 / 2044) : ℂ) * ζ ^ 28 - ((8 / 511) : ℂ) * ζ ^ 29 + ((933 / 2044) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_4_5 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        4 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((1507 / 6132) : ℂ) + ((4853 / 3066) : ℂ) * ζ ^ 3 + ((1507 / 6132) : ℂ) * ζ ^ 4 + ((1927 / 1533) : ℂ) * ζ ^ 5 - ((41 / 511) : ℂ) * ζ ^ 6 - ((677 / 1533) : ℂ) * ζ ^ 8 - ((1927 / 1533) : ℂ) * ζ ^ 9 - ((5543 / 6132) : ℂ) * ζ ^ 10 + ((4309 / 3066) : ℂ) * ζ ^ 13 + ((5051 / 6132) : ℂ) * ζ ^ 14 + ((1121 / 1533) : ℂ) * ζ ^ 15 - ((6347 / 6132) : ℂ) * ζ ^ 18 - ((1121 / 1533) : ℂ) * ζ ^ 19 - ((71 / 511) : ℂ) * ζ ^ 20 + ((41 / 511) : ℂ) * ζ ^ 22 + ((167 / 438) : ℂ) * ζ ^ 23 + ((71 / 511) : ℂ) * ζ ^ 24 + ((1349 / 6132) : ℂ) * ζ ^ 25 + ((41 / 511) : ℂ) * ζ ^ 26 - ((1073 / 3066) : ℂ) * ζ ^ 28 - ((1349 / 6132) : ℂ) * ζ ^ 29 - ((41 / 511) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_5_0 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        5 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((19 / 84) : ℂ) - ((263 / 84) : ℂ) * ζ ^ 3 - ((19 / 84) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 5 + ((37 / 28) : ℂ) * ζ ^ 6 + ((113 / 84) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 9 + ((1 / 21) : ℂ) * ζ ^ 13 + ((37 / 28) : ℂ) * ζ ^ 14 + ((1 / 12) : ℂ) * ζ ^ 15 - ((87 / 28) : ℂ) * ζ ^ 18 - ((1 / 12) : ℂ) * ζ ^ 19 + ((47 / 84) : ℂ) * ζ ^ 20 - ((37 / 28) : ℂ) * ζ ^ 22 + ((53 / 21) : ℂ) * ζ ^ 23 - ((47 / 84) : ℂ) * ζ ^ 24 - ((52 / 21) : ℂ) * ζ ^ 25 - ((37 / 28) : ℂ) * ζ ^ 26 - ((19 / 28) : ℂ) * ζ ^ 28 + ((52 / 21) : ℂ) * ζ ^ 29 + ((37 / 28) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_5_1 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        5 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((5 / 6) : ℂ) + ((331 / 84) : ℂ) * ζ ^ 3 + ((5 / 6) : ℂ) * ζ ^ 4 + ((17 / 42) : ℂ) * ζ ^ 5 - ((3 / 2) : ℂ) * ζ ^ 6 - ((73 / 28) : ℂ) * ζ ^ 8 - ((17 / 42) : ℂ) * ζ ^ 9 + ((4 / 21) : ℂ) * ζ ^ 10 - ((65 / 84) : ℂ) * ζ ^ 13 - ((71 / 42) : ℂ) * ζ ^ 14 + ((23 / 28) : ℂ) * ζ ^ 15 + ((67 / 42) : ℂ) * ζ ^ 18 - ((23 / 28) : ℂ) * ζ ^ 19 - ((47 / 21) : ℂ) * ζ ^ 20 + ((3 / 2) : ℂ) * ζ ^ 22 - ((53 / 42) : ℂ) * ζ ^ 23 + ((47 / 21) : ℂ) * ζ ^ 24 + ((59 / 21) : ℂ) * ζ ^ 25 + ((3 / 2) : ℂ) * ζ ^ 26 - ((33 / 28) : ℂ) * ζ ^ 28 - ((59 / 21) : ℂ) * ζ ^ 29 - ((3 / 2) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_5_2 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        5 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((55 / 84) : ℂ) + ((11 / 84) : ℂ) * ζ ^ 3 - ((55 / 84) : ℂ) * ζ ^ 4 + ((115 / 84) : ℂ) * ζ ^ 5 + ((11 / 12) : ℂ) * ζ ^ 6 + ((143 / 84) : ℂ) * ζ ^ 8 - ((115 / 84) : ℂ) * ζ ^ 9 - ((59 / 42) : ℂ) * ζ ^ 10 + ((73 / 42) : ℂ) * ζ ^ 13 + ((65 / 28) : ℂ) * ζ ^ 14 + ((65 / 42) : ℂ) * ζ ^ 15 - ((5 / 3) : ℂ) * ζ ^ 18 - ((65 / 42) : ℂ) * ζ ^ 19 - ((2 / 3) : ℂ) * ζ ^ 20 - ((11 / 12) : ℂ) * ζ ^ 22 + ((13 / 12) : ℂ) * ζ ^ 23 + ((2 / 3) : ℂ) * ζ ^ 24 + ((13 / 21) : ℂ) * ζ ^ 25 - ((11 / 12) : ℂ) * ζ ^ 26 - ((15 / 7) : ℂ) * ζ ^ 28 - ((13 / 21) : ℂ) * ζ ^ 29 + ((11 / 12) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_5_3 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        5 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((43 / 42) : ℂ) - ((29 / 84) : ℂ) * ζ ^ 3 - ((43 / 42) : ℂ) * ζ ^ 4 - ((3 / 14) : ℂ) * ζ ^ 5 - ((3 / 28) : ℂ) * ζ ^ 6 + ((32 / 21) : ℂ) * ζ ^ 8 + ((3 / 14) : ℂ) * ζ ^ 9 - ((23 / 42) : ℂ) * ζ ^ 10 - ((25 / 28) : ℂ) * ζ ^ 13 + ((37 / 84) : ℂ) * ζ ^ 14 + ((43 / 84) : ℂ) * ζ ^ 15 - ((101 / 84) : ℂ) * ζ ^ 18 - ((43 / 84) : ℂ) * ζ ^ 19 - ((151 / 84) : ℂ) * ζ ^ 20 + ((3 / 28) : ℂ) * ζ ^ 22 + ((7 / 12) : ℂ) * ζ ^ 23 + ((151 / 84) : ℂ) * ζ ^ 24 + ((11 / 42) : ℂ) * ζ ^ 25 + ((3 / 28) : ℂ) * ζ ^ 26 - ((18 / 7) : ℂ) * ζ ^ 28 - ((11 / 42) : ℂ) * ζ ^ 29 - ((3 / 28) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_5_4 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        5 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((464 / 1533) : ℂ) - ((535 / 1533) : ℂ) * ζ ^ 3 - ((464 / 1533) : ℂ) * ζ ^ 4 - ((668 / 511) : ℂ) * ζ ^ 5 + ((33 / 146) : ℂ) * ζ ^ 6 + ((7687 / 6132) : ℂ) * ζ ^ 8 + ((668 / 511) : ℂ) * ζ ^ 9 + ((3589 / 3066) : ℂ) * ζ ^ 10 - ((3667 / 3066) : ℂ) * ζ ^ 13 - ((1448 / 1533) : ℂ) * ζ ^ 14 - ((1678 / 1533) : ℂ) * ζ ^ 15 + ((2560 / 1533) : ℂ) * ζ ^ 18 + ((1678 / 1533) : ℂ) * ζ ^ 19 + ((2441 / 3066) : ℂ) * ζ ^ 20 - ((33 / 146) : ℂ) * ζ ^ 22 - ((804 / 511) : ℂ) * ζ ^ 23 - ((2441 / 3066) : ℂ) * ζ ^ 24 + ((187 / 1022) : ℂ) * ζ ^ 25 - ((33 / 146) : ℂ) * ζ ^ 26 + ((575 / 1022) : ℂ) * ζ ^ 28 - ((187 / 1022) : ℂ) * ζ ^ 29 + ((33 / 146) : ℂ) * ζ ^ 30)
private theorem row15_eigenbasisInverse_mul_5_5 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis)
        5 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((4577 / 3066) : ℂ) + ((2209 / 3066) : ℂ) * ζ ^ 3 + ((4577 / 3066) : ℂ) * ζ ^ 4 + ((2761 / 2044) : ℂ) * ζ ^ 5 - ((197 / 876) : ℂ) * ζ ^ 6 - ((3767 / 1533) : ℂ) * ζ ^ 8 - ((2761 / 2044) : ℂ) * ζ ^ 9 - ((10777 / 6132) : ℂ) * ζ ^ 10 + ((2696 / 1533) : ℂ) * ζ ^ 13 + ((4699 / 3066) : ℂ) * ζ ^ 14 + ((1479 / 1022) : ℂ) * ζ ^ 15 - ((731 / 438) : ℂ) * ζ ^ 18 - ((1479 / 1022) : ℂ) * ζ ^ 19 - ((9929 / 6132) : ℂ) * ζ ^ 20 + ((197 / 876) : ℂ) * ζ ^ 22 + ((1630 / 1533) : ℂ) * ζ ^ 23 + ((9929 / 6132) : ℂ) * ζ ^ 24 + ((1571 / 3066) : ℂ) * ζ ^ 25 + ((197 / 876) : ℂ) * ζ ^ 26 - ((402 / 511) : ℂ) * ζ ^ 28 - ((1571 / 3066) : ℂ) * ζ ^ 29 - ((197 / 876) : ℂ) * ζ ^ 30)
/-- The displayed row 15 matrix is a left inverse of its
eigenbasis. -/
theorem alternatingSixAmbientRow15EigenbasisInverse_mul :
    alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixAmbientRow15Eigenbasis =
      1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row15_eigenbasisInverse_mul_0_0
  · exact row15_eigenbasisInverse_mul_0_1
  · exact row15_eigenbasisInverse_mul_0_2
  · exact row15_eigenbasisInverse_mul_0_3
  · exact row15_eigenbasisInverse_mul_0_4
  · exact row15_eigenbasisInverse_mul_0_5
  · exact row15_eigenbasisInverse_mul_1_0
  · exact row15_eigenbasisInverse_mul_1_1
  · exact row15_eigenbasisInverse_mul_1_2
  · exact row15_eigenbasisInverse_mul_1_3
  · exact row15_eigenbasisInverse_mul_1_4
  · exact row15_eigenbasisInverse_mul_1_5
  · exact row15_eigenbasisInverse_mul_2_0
  · exact row15_eigenbasisInverse_mul_2_1
  · exact row15_eigenbasisInverse_mul_2_2
  · exact row15_eigenbasisInverse_mul_2_3
  · exact row15_eigenbasisInverse_mul_2_4
  · exact row15_eigenbasisInverse_mul_2_5
  · exact row15_eigenbasisInverse_mul_3_0
  · exact row15_eigenbasisInverse_mul_3_1
  · exact row15_eigenbasisInverse_mul_3_2
  · exact row15_eigenbasisInverse_mul_3_3
  · exact row15_eigenbasisInverse_mul_3_4
  · exact row15_eigenbasisInverse_mul_3_5
  · exact row15_eigenbasisInverse_mul_4_0
  · exact row15_eigenbasisInverse_mul_4_1
  · exact row15_eigenbasisInverse_mul_4_2
  · exact row15_eigenbasisInverse_mul_4_3
  · exact row15_eigenbasisInverse_mul_4_4
  · exact row15_eigenbasisInverse_mul_4_5
  · exact row15_eigenbasisInverse_mul_5_0
  · exact row15_eigenbasisInverse_mul_5_1
  · exact row15_eigenbasisInverse_mul_5_2
  · exact row15_eigenbasisInverse_mul_5_3
  · exact row15_eigenbasisInverse_mul_5_4
  · exact row15_eigenbasisInverse_mul_5_5

/-- The displayed row 15 inverse is also a right inverse. -/
theorem alternatingSixAmbientRow15Eigenbasis_mul_inverse :
    alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixAmbientRow15EigenbasisInverse_mul


private theorem row15_generatorB_mul_eigenbasis_0_0 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        0 0 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        0 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((47 / 21) : ℂ) + ((178 / 21) : ℂ) * ζ ^ 3 + ((47 / 21) : ℂ) * ζ ^ 4 - ((23 / 7) : ℂ) * ζ ^ 5 - ((53 / 7) : ℂ) * ζ ^ 6 - ((13 / 3) : ℂ) * ζ ^ 8 + ((23 / 7) : ℂ) * ζ ^ 9 + ((2 / 7) : ℂ) * ζ ^ 10 + ((103 / 21) : ℂ) * ζ ^ 13 - ((55 / 7) : ℂ) * ζ ^ 14 - ((11 / 3) : ℂ) * ζ ^ 15 + ((27 / 7) : ℂ) * ζ ^ 18 + ((11 / 3) : ℂ) * ζ ^ 19 + ((50 / 21) : ℂ) * ζ ^ 20 + ((53 / 7) : ℂ) * ζ ^ 22 - ((13 / 21) : ℂ) * ζ ^ 23 - ((50 / 21) : ℂ) * ζ ^ 24 + ((95 / 21) : ℂ) * ζ ^ 25 + ((53 / 7) : ℂ) * ζ ^ 26 + ((10 / 7) : ℂ) * ζ ^ 28 - ((95 / 21) : ℂ) * ζ ^ 29 - ((53 / 7) : ℂ) * ζ ^ 30)
private theorem row15_generatorB_mul_eigenbasis_0_1 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        0 1 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        0 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((44 / 21) : ℂ) - ((125 / 21) : ℂ) * ζ ^ 3 - ((44 / 21) : ℂ) * ζ ^ 4 + ((127 / 21) : ℂ) * ζ ^ 5 + ((29 / 7) : ℂ) * ζ ^ 6 - ((10 / 7) : ℂ) * ζ ^ 8 - ((127 / 21) : ℂ) * ζ ^ 9 - ((125 / 21) : ℂ) * ζ ^ 10 - ((47 / 21) : ℂ) * ζ ^ 13 + ((212 / 21) : ℂ) * ζ ^ 14 + (5 : ℂ) * ζ ^ 15 - ((79 / 21) : ℂ) * ζ ^ 18 - (5 : ℂ) * ζ ^ 19 - ((86 / 21) : ℂ) * ζ ^ 20 - ((29 / 7) : ℂ) * ζ ^ 22 - ((4 / 21) : ℂ) * ζ ^ 23 + ((86 / 21) : ℂ) * ζ ^ 24 - ((151 / 21) : ℂ) * ζ ^ 25 - ((29 / 7) : ℂ) * ζ ^ 26 + ((8 / 7) : ℂ) * ζ ^ 28 + ((151 / 21) : ℂ) * ζ ^ 29 + ((29 / 7) : ℂ) * ζ ^ 30)
private theorem row15_generatorB_mul_eigenbasis_0_2 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        0 2 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        0 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((11 / 3) : ℂ) + ((23 / 3) : ℂ) * ζ ^ 3 + ((11 / 3) : ℂ) * ζ ^ 4 + ((109 / 21) : ℂ) * ζ ^ 5 + ((17 / 21) : ℂ) * ζ ^ 6 - ((103 / 21) : ℂ) * ζ ^ 8 - ((109 / 21) : ℂ) * ζ ^ 9 + ((92 / 21) : ℂ) * ζ ^ 10 - ((13 / 21) : ℂ) * ζ ^ 13 - ((25 / 7) : ℂ) * ζ ^ 14 - ((71 / 21) : ℂ) * ζ ^ 15 - ((53 / 21) : ℂ) * ζ ^ 18 + ((71 / 21) : ℂ) * ζ ^ 19 + ((40 / 21) : ℂ) * ζ ^ 20 - ((17 / 21) : ℂ) * ζ ^ 22 - ((47 / 21) : ℂ) * ζ ^ 23 - ((40 / 21) : ℂ) * ζ ^ 24 - ((146 / 21) : ℂ) * ζ ^ 25 - ((17 / 21) : ℂ) * ζ ^ 26 + ((12 / 7) : ℂ) * ζ ^ 28 + ((146 / 21) : ℂ) * ζ ^ 29 + ((17 / 21) : ℂ) * ζ ^ 30)
private theorem row15_generatorB_mul_eigenbasis_0_3 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        0 3 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        0 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((115 / 21) : ℂ) + ((10 / 3) : ℂ) * ζ ^ 3 + ((115 / 21) : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 5 + ((1 / 7) : ℂ) * ζ ^ 6 - ((160 / 21) : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 9 - ((85 / 21) : ℂ) * ζ ^ 10 - ((12 / 7) : ℂ) * ζ ^ 13 + ((88 / 21) : ℂ) * ζ ^ 14 - ((116 / 21) : ℂ) * ζ ^ 15 - ((5 / 3) : ℂ) * ζ ^ 18 + ((116 / 21) : ℂ) * ζ ^ 19 + ((20 / 21) : ℂ) * ζ ^ 20 - ((1 / 7) : ℂ) * ζ ^ 22 - ((113 / 21) : ℂ) * ζ ^ 23 - ((20 / 21) : ℂ) * ζ ^ 24 - ((194 / 21) : ℂ) * ζ ^ 25 - ((1 / 7) : ℂ) * ζ ^ 26 + ((13 / 7) : ℂ) * ζ ^ 28 + ((194 / 21) : ℂ) * ζ ^ 29 - ((6 / 7) : ℂ) * ζ ^ 30 - ζ ^ 33 + ζ ^ 34 - ζ ^ 35 - ζ ^ 38 + ζ ^ 39 - ζ ^ 43 - ζ ^ 45 + ζ ^ 49 - ζ ^ 53 + ζ ^ 60 - ζ ^ 64 + ζ ^ 68 + ζ ^ 70 - ζ ^ 74)
private theorem row15_generatorB_mul_eigenbasis_0_4 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        0 4 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        0 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((1249 / 1533) : ℂ) - ((1822 / 1533) : ℂ) * ζ ^ 3 + ((1249 / 1533) : ℂ) * ζ ^ 4 + ((1412 / 511) : ℂ) * ζ ^ 5 + ((1257 / 511) : ℂ) * ζ ^ 6 + ((961 / 1533) : ℂ) * ζ ^ 8 - ((1412 / 511) : ℂ) * ζ ^ 9 + ((1583 / 1533) : ℂ) * ζ ^ 10 + ((2089 / 1533) : ℂ) * ζ ^ 13 + ((2188 / 1533) : ℂ) * ζ ^ 14 + ((962 / 219) : ℂ) * ζ ^ 15 - ((2264 / 1533) : ℂ) * ζ ^ 18 - ((962 / 219) : ℂ) * ζ ^ 19 - ((3293 / 1533) : ℂ) * ζ ^ 20 - ((1257 / 511) : ℂ) * ζ ^ 22 + ((1112 / 511) : ℂ) * ζ ^ 23 + ((3293 / 1533) : ℂ) * ζ ^ 24 + ((77 / 73) : ℂ) * ζ ^ 25 - ((1257 / 511) : ℂ) * ζ ^ 26 - ((807 / 511) : ℂ) * ζ ^ 28 - ((77 / 73) : ℂ) * ζ ^ 29 + ((1040 / 511) : ℂ) * ζ ^ 30 + ((2 / 73) : ℂ) * ζ ^ 33 + ((31 / 73) : ℂ) * ζ ^ 34 + ((6 / 73) : ℂ) * ζ ^ 35 - ((31 / 73) : ℂ) * ζ ^ 38 - ((6 / 73) : ℂ) * ζ ^ 39 - ((20 / 73) : ℂ) * ζ ^ 40 + ((6 / 73) : ℂ) * ζ ^ 43 + ((20 / 73) : ℂ) * ζ ^ 44 + ((18 / 73) : ℂ) * ζ ^ 45 - ((20 / 73) : ℂ) * ζ ^ 48 - ((18 / 73) : ℂ) * ζ ^ 49 - ((60 / 73) : ℂ) * ζ ^ 50 + ((18 / 73) : ℂ) * ζ ^ 53 + ((60 / 73) : ℂ) * ζ ^ 54 - ((19 / 73) : ℂ) * ζ ^ 55 - ((60 / 73) : ℂ) * ζ ^ 58 + ((19 / 73) : ℂ) * ζ ^ 59 + ((39 / 73) : ℂ) * ζ ^ 60 - ((19 / 73) : ℂ) * ζ ^ 63 - ((39 / 73) : ℂ) * ζ ^ 64 + ((16 / 73) : ℂ) * ζ ^ 65 + ((39 / 73) : ℂ) * ζ ^ 68 - ((16 / 73) : ℂ) * ζ ^ 69 - ((29 / 73) : ℂ) * ζ ^ 70 + ((16 / 73) : ℂ) * ζ ^ 73 + ((29 / 73) : ℂ) * ζ ^ 74 - ((25 / 73) : ℂ) * ζ ^ 75 - ((29 / 73) : ℂ) * ζ ^ 78 + ((25 / 73) : ℂ) * ζ ^ 79 + ((59 / 73) : ℂ) * ζ ^ 80 - ((25 / 73) : ℂ) * ζ ^ 83 - ((59 / 73) : ℂ) * ζ ^ 84 - ((2 / 73) : ℂ) * ζ ^ 85 + ((59 / 73) : ℂ) * ζ ^ 88 + ((2 / 73) : ℂ) * ζ ^ 89 + ((31 / 73) : ℂ) * ζ ^ 90 - ((2 / 73) : ℂ) * ζ ^ 93 - ((31 / 73) : ℂ) * ζ ^ 94 - ((6 / 73) : ℂ) * ζ ^ 95 + ((31 / 73) : ℂ) * ζ ^ 98 + ((6 / 73) : ℂ) * ζ ^ 99 + ((20 / 73) : ℂ) * ζ ^ 100 - ((6 / 73) : ℂ) * ζ ^ 103 - ((20 / 73) : ℂ) * ζ ^ 104)
private theorem row15_generatorB_mul_eigenbasis_0_5 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        0 5 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        0 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((262 / 219) : ℂ) - ((1411 / 1533) : ℂ) * ζ ^ 3 + ((262 / 219) : ℂ) * ζ ^ 4 - ((2098 / 511) : ℂ) * ζ ^ 5 + ((346 / 1533) : ℂ) * ζ ^ 6 - ((461 / 1533) : ℂ) * ζ ^ 8 + ((2098 / 511) : ℂ) * ζ ^ 9 + ((5951 / 1533) : ℂ) * ζ ^ 10 - ((6346 / 1533) : ℂ) * ζ ^ 13 - ((5605 / 1533) : ℂ) * ζ ^ 14 - ((2822 / 511) : ℂ) * ζ ^ 15 + ((4169 / 1533) : ℂ) * ζ ^ 18 + ((2822 / 511) : ℂ) * ζ ^ 19 + ((3568 / 1533) : ℂ) * ζ ^ 20 - ((346 / 1533) : ℂ) * ζ ^ 22 - ((5153 / 1533) : ℂ) * ζ ^ 23 - ((3568 / 1533) : ℂ) * ζ ^ 24 - ((3884 / 1533) : ℂ) * ζ ^ 25 - ((346 / 1533) : ℂ) * ζ ^ 26 + ((762 / 511) : ℂ) * ζ ^ 28 + ((3884 / 1533) : ℂ) * ζ ^ 29 + ((955 / 1533) : ℂ) * ζ ^ 30 - ((16 / 73) : ℂ) * ζ ^ 33 - ((29 / 73) : ℂ) * ζ ^ 34 - ((48 / 73) : ℂ) * ζ ^ 35 + ((29 / 73) : ℂ) * ζ ^ 38 + ((48 / 73) : ℂ) * ζ ^ 39 + ((14 / 73) : ℂ) * ζ ^ 40 - ((48 / 73) : ℂ) * ζ ^ 43 - ((14 / 73) : ℂ) * ζ ^ 44 + ((2 / 73) : ℂ) * ζ ^ 45 + ((14 / 73) : ℂ) * ζ ^ 48 - ((2 / 73) : ℂ) * ζ ^ 49 + ((42 / 73) : ℂ) * ζ ^ 50 + ((2 / 73) : ℂ) * ζ ^ 53 - ((42 / 73) : ℂ) * ζ ^ 54 + ((6 / 73) : ℂ) * ζ ^ 55 + ((42 / 73) : ℂ) * ζ ^ 58 - ((6 / 73) : ℂ) * ζ ^ 59 - ((20 / 73) : ℂ) * ζ ^ 60 + ((6 / 73) : ℂ) * ζ ^ 63 + ((20 / 73) : ℂ) * ζ ^ 64 + ((18 / 73) : ℂ) * ζ ^ 65 - ((20 / 73) : ℂ) * ζ ^ 68 - ((18 / 73) : ℂ) * ζ ^ 69 + ((13 / 73) : ℂ) * ζ ^ 70 + ((18 / 73) : ℂ) * ζ ^ 73 - ((13 / 73) : ℂ) * ζ ^ 74 + ((54 / 73) : ℂ) * ζ ^ 75 + ((13 / 73) : ℂ) * ζ ^ 78 - ((54 / 73) : ℂ) * ζ ^ 79 - ((34 / 73) : ℂ) * ζ ^ 80 + ((54 / 73) : ℂ) * ζ ^ 83 + ((34 / 73) : ℂ) * ζ ^ 84 + ((16 / 73) : ℂ) * ζ ^ 85 - ((34 / 73) : ℂ) * ζ ^ 88 - ((16 / 73) : ℂ) * ζ ^ 89 - ((29 / 73) : ℂ) * ζ ^ 90 + ((16 / 73) : ℂ) * ζ ^ 93 + ((29 / 73) : ℂ) * ζ ^ 94 + ((48 / 73) : ℂ) * ζ ^ 95 - ((29 / 73) : ℂ) * ζ ^ 98 - ((48 / 73) : ℂ) * ζ ^ 99 - ((14 / 73) : ℂ) * ζ ^ 100 + ((48 / 73) : ℂ) * ζ ^ 103 + ((14 / 73) : ℂ) * ζ ^ 104)
private theorem row15_generatorB_mul_eigenbasis_1_0 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        1 0 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        1 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((20 / 21) : ℂ) - ((29 / 21) : ℂ) * ζ ^ 3 - ((20 / 21) : ℂ) * ζ ^ 4 - ((64 / 21) : ℂ) * ζ ^ 5 - ((11 / 7) : ℂ) * ζ ^ 6 - ((41 / 7) : ℂ) * ζ ^ 8 + ((64 / 21) : ℂ) * ζ ^ 9 + ((43 / 21) : ℂ) * ζ ^ 10 + ζ ^ 13 - ((76 / 21) : ℂ) * ζ ^ 14 - ((17 / 3) : ℂ) * ζ ^ 15 - ((164 / 21) : ℂ) * ζ ^ 18 + ((17 / 3) : ℂ) * ζ ^ 19 - ((2 / 3) : ℂ) * ζ ^ 20 + ((11 / 7) : ℂ) * ζ ^ 22 + ((68 / 21) : ℂ) * ζ ^ 23 + ((2 / 3) : ℂ) * ζ ^ 24 - ((82 / 21) : ℂ) * ζ ^ 25 + ((11 / 7) : ℂ) * ζ ^ 26 - ((61 / 21) : ℂ) * ζ ^ 28 + ((82 / 21) : ℂ) * ζ ^ 29 - ((11 / 7) : ℂ) * ζ ^ 30)
private theorem row15_generatorB_mul_eigenbasis_1_1 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        1 1 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        1 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((31 / 7) : ℂ) + ((152 / 21) : ℂ) * ζ ^ 3 + ((31 / 7) : ℂ) * ζ ^ 4 + ((136 / 21) : ℂ) * ζ ^ 5 - ((8 / 7) : ℂ) * ζ ^ 6 - ((74 / 21) : ℂ) * ζ ^ 8 - ((136 / 21) : ℂ) * ζ ^ 9 - ((205 / 21) : ℂ) * ζ ^ 10 + ((97 / 21) : ℂ) * ζ ^ 13 + ((181 / 21) : ℂ) * ζ ^ 14 + ((200 / 21) : ℂ) * ζ ^ 15 + ((4 / 7) : ℂ) * ζ ^ 18 - ((200 / 21) : ℂ) * ζ ^ 19 - ((38 / 7) : ℂ) * ζ ^ 20 + ((8 / 7) : ℂ) * ζ ^ 22 - ((20 / 21) : ℂ) * ζ ^ 23 + ((38 / 7) : ℂ) * ζ ^ 24 + ((173 / 21) : ℂ) * ζ ^ 25 + ((8 / 7) : ℂ) * ζ ^ 26 - ((34 / 21) : ℂ) * ζ ^ 28 - ((173 / 21) : ℂ) * ζ ^ 29 - ((8 / 7) : ℂ) * ζ ^ 30)
private theorem row15_generatorB_mul_eigenbasis_1_2 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        1 2 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        1 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((101 / 21) : ℂ) + ((110 / 21) : ℂ) * ζ ^ 3 + ((101 / 21) : ℂ) * ζ ^ 4 + ((173 / 21) : ℂ) * ζ ^ 5 + ((53 / 21) : ℂ) * ζ ^ 6 - ((14 / 3) : ℂ) * ζ ^ 8 - ((173 / 21) : ℂ) * ζ ^ 9 - ((26 / 21) : ℂ) * ζ ^ 10 + ((115 / 21) : ℂ) * ζ ^ 13 + ((79 / 21) : ℂ) * ζ ^ 14 + ((16 / 7) : ℂ) * ζ ^ 15 - ((36 / 7) : ℂ) * ζ ^ 18 - ((16 / 7) : ℂ) * ζ ^ 19 - ((4 / 7) : ℂ) * ζ ^ 20 - ((53 / 21) : ℂ) * ζ ^ 22 + ((110 / 21) : ℂ) * ζ ^ 23 + ((4 / 7) : ℂ) * ζ ^ 24 - ((37 / 7) : ℂ) * ζ ^ 25 - ((53 / 21) : ℂ) * ζ ^ 26 - ((44 / 21) : ℂ) * ζ ^ 28 + ((37 / 7) : ℂ) * ζ ^ 29 + ((32 / 21) : ℂ) * ζ ^ 30 + ζ ^ 34 - (2 : ℂ) * ζ ^ 35 - ζ ^ 38 + (2 : ℂ) * ζ ^ 39 - (2 : ℂ) * ζ ^ 43)
private theorem row15_generatorB_mul_eigenbasis_1_3 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        1 3 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        1 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((11 / 7) : ℂ) + ((53 / 21) : ℂ) * ζ ^ 3 + ((11 / 7) : ℂ) * ζ ^ 4 + ((170 / 21) : ℂ) * ζ ^ 5 + ((11 / 7) : ℂ) * ζ ^ 6 - ((3 / 7) : ℂ) * ζ ^ 8 - ((170 / 21) : ℂ) * ζ ^ 9 + ((17 / 21) : ℂ) * ζ ^ 10 + ((11 / 3) : ℂ) * ζ ^ 13 + ((16 / 21) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 15 - ((23 / 21) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 19 - ((6 / 7) : ℂ) * ζ ^ 20 - ((11 / 7) : ℂ) * ζ ^ 22 + ((29 / 21) : ℂ) * ζ ^ 23 + ((6 / 7) : ℂ) * ζ ^ 24 - ((83 / 21) : ℂ) * ζ ^ 25 - ((11 / 7) : ℂ) * ζ ^ 26 - ((29 / 21) : ℂ) * ζ ^ 28 + ((83 / 21) : ℂ) * ζ ^ 29 + ((4 / 7) : ℂ) * ζ ^ 30 + ζ ^ 33 + ζ ^ 34 - ζ ^ 38 - ζ ^ 45 + ζ ^ 49 - ζ ^ 50 - ζ ^ 53 + ζ ^ 54 - ζ ^ 58 - ζ ^ 60 + ζ ^ 64 - (2 : ℂ) * ζ ^ 65 - ζ ^ 68 + (2 : ℂ) * ζ ^ 69 - (2 : ℂ) * ζ ^ 73)
private theorem row15_generatorB_mul_eigenbasis_1_4 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        1 4 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        1 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((1252 / 1533) : ℂ) - ((5977 / 1533) : ℂ) * ζ ^ 3 - ((1252 / 1533) : ℂ) * ζ ^ 4 - ((3917 / 1533) : ℂ) * ζ ^ 5 + ((766 / 511) : ℂ) * ζ ^ 6 + ((1748 / 511) : ℂ) * ζ ^ 8 + ((3917 / 1533) : ℂ) * ζ ^ 9 + ((432 / 511) : ℂ) * ζ ^ 10 - ((5758 / 1533) : ℂ) * ζ ^ 13 + ((334 / 511) : ℂ) * ζ ^ 14 - ((1476 / 511) : ℂ) * ζ ^ 15 + ((503 / 219) : ℂ) * ζ ^ 18 + ((1476 / 511) : ℂ) * ζ ^ 19 - ((1178 / 1533) : ℂ) * ζ ^ 20 - ((766 / 511) : ℂ) * ζ ^ 22 - ((3461 / 1533) : ℂ) * ζ ^ 23 + ((1178 / 1533) : ℂ) * ζ ^ 24 - ((593 / 511) : ℂ) * ζ ^ 25 - ((766 / 511) : ℂ) * ζ ^ 26 + ((582 / 511) : ℂ) * ζ ^ 28 + ((593 / 511) : ℂ) * ζ ^ 29 + ((1172 / 511) : ℂ) * ζ ^ 30 - ((32 / 73) : ℂ) * ζ ^ 33 - ((58 / 73) : ℂ) * ζ ^ 34 - ((23 / 73) : ℂ) * ζ ^ 35 + ((58 / 73) : ℂ) * ζ ^ 38 + ((23 / 73) : ℂ) * ζ ^ 39 - ((45 / 73) : ℂ) * ζ ^ 40 - ((23 / 73) : ℂ) * ζ ^ 43 + ((45 / 73) : ℂ) * ζ ^ 44 + ((4 / 73) : ℂ) * ζ ^ 45 - ((45 / 73) : ℂ) * ζ ^ 48 - ((4 / 73) : ℂ) * ζ ^ 49 + ((11 / 73) : ℂ) * ζ ^ 50 + ((4 / 73) : ℂ) * ζ ^ 53 - ((11 / 73) : ℂ) * ζ ^ 54 + ((12 / 73) : ℂ) * ζ ^ 55 + ((11 / 73) : ℂ) * ζ ^ 58 - ((12 / 73) : ℂ) * ζ ^ 59 - ((40 / 73) : ℂ) * ζ ^ 60 + ((12 / 73) : ℂ) * ζ ^ 63 + ((40 / 73) : ℂ) * ζ ^ 64 + ((36 / 73) : ℂ) * ζ ^ 65 - ((40 / 73) : ℂ) * ζ ^ 68 - ((36 / 73) : ℂ) * ζ ^ 69 - ((47 / 73) : ℂ) * ζ ^ 70 + ((36 / 73) : ℂ) * ζ ^ 73 + ((47 / 73) : ℂ) * ζ ^ 74 + ((35 / 73) : ℂ) * ζ ^ 75 - ((47 / 73) : ℂ) * ζ ^ 78 - ((35 / 73) : ℂ) * ζ ^ 79 + ((5 / 73) : ℂ) * ζ ^ 80 + ((35 / 73) : ℂ) * ζ ^ 83 - ((5 / 73) : ℂ) * ζ ^ 84 + ((32 / 73) : ℂ) * ζ ^ 85 + ((5 / 73) : ℂ) * ζ ^ 88 - ((32 / 73) : ℂ) * ζ ^ 89 - ((58 / 73) : ℂ) * ζ ^ 90 + ((32 / 73) : ℂ) * ζ ^ 93 + ((58 / 73) : ℂ) * ζ ^ 94 + ((23 / 73) : ℂ) * ζ ^ 95 - ((58 / 73) : ℂ) * ζ ^ 98 - ((23 / 73) : ℂ) * ζ ^ 99 + ((45 / 73) : ℂ) * ζ ^ 100 + ((23 / 73) : ℂ) * ζ ^ 103 - ((45 / 73) : ℂ) * ζ ^ 104)
private theorem row15_generatorB_mul_eigenbasis_1_5 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        1 5 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        1 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((1027 / 511) : ℂ) + ((751 / 219) : ℂ) * ζ ^ 3 + ((1027 / 511) : ℂ) * ζ ^ 4 + ((764 / 219) : ℂ) * ζ ^ 5 - ((353 / 1533) : ℂ) * ζ ^ 6 - ((1136 / 511) : ℂ) * ζ ^ 8 - ((764 / 219) : ℂ) * ζ ^ 9 - ((1973 / 1533) : ℂ) * ζ ^ 10 + ((2166 / 511) : ℂ) * ζ ^ 13 + ((540 / 511) : ℂ) * ζ ^ 14 + ((676 / 1533) : ℂ) * ζ ^ 15 - ((1523 / 1533) : ℂ) * ζ ^ 18 - ((676 / 1533) : ℂ) * ζ ^ 19 + ((1 / 219) : ℂ) * ζ ^ 20 + ((353 / 1533) : ℂ) * ζ ^ 22 - ((139 / 511) : ℂ) * ζ ^ 23 - ((1 / 219) : ℂ) * ζ ^ 24 + ((1676 / 1533) : ℂ) * ζ ^ 25 + ((353 / 1533) : ℂ) * ζ ^ 26 - ((233 / 219) : ℂ) * ζ ^ 28 - ((1676 / 1533) : ℂ) * ζ ^ 29 - ((899 / 1533) : ℂ) * ζ ^ 30 + ((37 / 73) : ℂ) * ζ ^ 33 + ((26 / 73) : ℂ) * ζ ^ 34 + ((38 / 73) : ℂ) * ζ ^ 35 - ((26 / 73) : ℂ) * ζ ^ 38 - ((38 / 73) : ℂ) * ζ ^ 39 - ((5 / 73) : ℂ) * ζ ^ 40 + ((38 / 73) : ℂ) * ζ ^ 43 + ((5 / 73) : ℂ) * ζ ^ 44 + ((41 / 73) : ℂ) * ζ ^ 45 - ((5 / 73) : ℂ) * ζ ^ 48 - ((41 / 73) : ℂ) * ζ ^ 49 - ((15 / 73) : ℂ) * ζ ^ 50 + ((41 / 73) : ℂ) * ζ ^ 53 + ((15 / 73) : ℂ) * ζ ^ 54 - ((23 / 73) : ℂ) * ζ ^ 55 - ((15 / 73) : ℂ) * ζ ^ 58 + ((23 / 73) : ℂ) * ζ ^ 59 + ((28 / 73) : ℂ) * ζ ^ 60 - ((23 / 73) : ℂ) * ζ ^ 63 - ((28 / 73) : ℂ) * ζ ^ 64 + ((4 / 73) : ℂ) * ζ ^ 65 + ((28 / 73) : ℂ) * ζ ^ 68 - ((4 / 73) : ℂ) * ζ ^ 69 + ((11 / 73) : ℂ) * ζ ^ 70 + ((4 / 73) : ℂ) * ζ ^ 73 - ((11 / 73) : ℂ) * ζ ^ 74 - ((61 / 73) : ℂ) * ζ ^ 75 + ((11 / 73) : ℂ) * ζ ^ 78 + ((61 / 73) : ℂ) * ζ ^ 79 + ((33 / 73) : ℂ) * ζ ^ 80 - ((61 / 73) : ℂ) * ζ ^ 83 - ((33 / 73) : ℂ) * ζ ^ 84 - ((37 / 73) : ℂ) * ζ ^ 85 + ((33 / 73) : ℂ) * ζ ^ 88 + ((37 / 73) : ℂ) * ζ ^ 89 + ((26 / 73) : ℂ) * ζ ^ 90 - ((37 / 73) : ℂ) * ζ ^ 93 - ((26 / 73) : ℂ) * ζ ^ 94 - ((38 / 73) : ℂ) * ζ ^ 95 + ((26 / 73) : ℂ) * ζ ^ 98 + ((38 / 73) : ℂ) * ζ ^ 99 + ((5 / 73) : ℂ) * ζ ^ 100 - ((38 / 73) : ℂ) * ζ ^ 103 - ((5 / 73) : ℂ) * ζ ^ 104)
private theorem row15_generatorB_mul_eigenbasis_2_0 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        2 0 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        2 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 0
private theorem row15_generatorB_mul_eigenbasis_2_1 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        2 1 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        2 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-ζ ^ 10 + ζ ^ 14)
private theorem row15_generatorB_mul_eigenbasis_2_2 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        2 2 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        2 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-ζ ^ 10 + ζ ^ 14 - ζ ^ 18 - ζ ^ 30 + ζ ^ 34 - ζ ^ 38)
private theorem row15_generatorB_mul_eigenbasis_2_3 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        2 3 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        2 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-ζ ^ 10 + ζ ^ 14 - ζ ^ 18 - ζ ^ 30 + ζ ^ 34 - ζ ^ 38 + ζ ^ 70 - ζ ^ 74)
private theorem row15_generatorB_mul_eigenbasis_2_4 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        2 4 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        2 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 0
private theorem row15_generatorB_mul_eigenbasis_2_5 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        2 5 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        2 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-ζ ^ 10 + ζ ^ 14 - ζ ^ 18 - ζ ^ 30 + ζ ^ 34 - ζ ^ 38 + ζ ^ 70 - ζ ^ 74 + ζ ^ 78 + ζ ^ 90 - ζ ^ 94 + ζ ^ 98)
private theorem row15_generatorB_mul_eigenbasis_3_0 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        3 0 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        3 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((13 / 21) : ℂ) - ((86 / 7) : ℂ) * ζ ^ 3 + ((13 / 21) : ℂ) * ζ ^ 4 + ((22 / 21) : ℂ) * ζ ^ 5 + ((46 / 7) : ℂ) * ζ ^ 6 + ((95 / 21) : ℂ) * ζ ^ 8 - ((22 / 21) : ℂ) * ζ ^ 9 - ((1 / 21) : ℂ) * ζ ^ 10 - ((8 / 3) : ℂ) * ζ ^ 13 + ((139 / 21) : ℂ) * ζ ^ 14 + ζ ^ 15 - ((172 / 21) : ℂ) * ζ ^ 18 - ζ ^ 19 - ((2 / 3) : ℂ) * ζ ^ 20 - ((46 / 7) : ℂ) * ζ ^ 22 + ((45 / 7) : ℂ) * ζ ^ 23 + ((2 / 3) : ℂ) * ζ ^ 24 - ((59 / 7) : ℂ) * ζ ^ 25 - ((46 / 7) : ℂ) * ζ ^ 26 - ((23 / 21) : ℂ) * ζ ^ 28 + ((59 / 7) : ℂ) * ζ ^ 29 + ((46 / 7) : ℂ) * ζ ^ 30)
private theorem row15_generatorB_mul_eigenbasis_3_1 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        3 1 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        3 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((19 / 21) : ℂ) + ((233 / 21) : ℂ) * ζ ^ 3 + ((19 / 21) : ℂ) * ζ ^ 4 - ((15 / 7) : ℂ) * ζ ^ 5 - ((41 / 7) : ℂ) * ζ ^ 6 - ((115 / 21) : ℂ) * ζ ^ 8 + ((15 / 7) : ℂ) * ζ ^ 9 + ((44 / 21) : ℂ) * ζ ^ 10 - ((9 / 7) : ℂ) * ζ ^ 13 - ((167 / 21) : ℂ) * ζ ^ 14 - ((32 / 21) : ℂ) * ζ ^ 15 + ((65 / 21) : ℂ) * ζ ^ 18 + ((32 / 21) : ℂ) * ζ ^ 19 - ((68 / 21) : ℂ) * ζ ^ 20 + ((41 / 7) : ℂ) * ζ ^ 22 - ((71 / 21) : ℂ) * ζ ^ 23 + ((68 / 21) : ℂ) * ζ ^ 24 + ((66 / 7) : ℂ) * ζ ^ 25 + ((41 / 7) : ℂ) * ζ ^ 26 - ((113 / 21) : ℂ) * ζ ^ 28 - ((66 / 7) : ℂ) * ζ ^ 29 - ((41 / 7) : ℂ) * ζ ^ 30)
private theorem row15_generatorB_mul_eigenbasis_3_2 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        3 2 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        3 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((36 / 7) : ℂ) - ((11 / 7) : ℂ) * ζ ^ 3 - ((36 / 7) : ℂ) * ζ ^ 4 + ((23 / 21) : ℂ) * ζ ^ 5 + ((15 / 7) : ℂ) * ζ ^ 6 + ((25 / 3) : ℂ) * ζ ^ 8 - ((23 / 21) : ℂ) * ζ ^ 9 - ((107 / 21) : ℂ) * ζ ^ 10 + ((88 / 21) : ℂ) * ζ ^ 13 + ((152 / 21) : ℂ) * ζ ^ 14 + ((85 / 21) : ℂ) * ζ ^ 15 - ((74 / 21) : ℂ) * ζ ^ 18 - ((85 / 21) : ℂ) * ζ ^ 19 - ((128 / 21) : ℂ) * ζ ^ 20 - ((15 / 7) : ℂ) * ζ ^ 22 + ((23 / 21) : ℂ) * ζ ^ 23 + ((128 / 21) : ℂ) * ζ ^ 24 + ((76 / 21) : ℂ) * ζ ^ 25 - ((15 / 7) : ℂ) * ζ ^ 26 - ((187 / 21) : ℂ) * ζ ^ 28 - ((76 / 21) : ℂ) * ζ ^ 29 + ((15 / 7) : ℂ) * ζ ^ 30 - ζ ^ 33 - ζ ^ 40 + ζ ^ 44)
private theorem row15_generatorB_mul_eigenbasis_3_3 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        3 3 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        3 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((89 / 21) : ℂ) - ((46 / 21) : ℂ) * ζ ^ 3 - ((89 / 21) : ℂ) * ζ ^ 4 - ((65 / 21) : ℂ) * ζ ^ 5 + ((3 / 7) : ℂ) * ζ ^ 6 + ((128 / 21) : ℂ) * ζ ^ 8 + ((65 / 21) : ℂ) * ζ ^ 9 - ((8 / 7) : ℂ) * ζ ^ 10 - ((8 / 3) : ℂ) * ζ ^ 13 + ((11 / 7) : ℂ) * ζ ^ 14 + ((5 / 3) : ℂ) * ζ ^ 15 - ((32 / 7) : ℂ) * ζ ^ 18 - ((5 / 3) : ℂ) * ζ ^ 19 - ((178 / 21) : ℂ) * ζ ^ 20 - ((3 / 7) : ℂ) * ζ ^ 22 + ((20 / 21) : ℂ) * ζ ^ 23 + ((178 / 21) : ℂ) * ζ ^ 24 + ((30 / 7) : ℂ) * ζ ^ 25 - ((3 / 7) : ℂ) * ζ ^ 26 - ((223 / 21) : ℂ) * ζ ^ 28 - ((30 / 7) : ℂ) * ζ ^ 29 - ((4 / 7) : ℂ) * ζ ^ 30 - ζ ^ 33 + ζ ^ 34 - ζ ^ 35 - ζ ^ 38 + ζ ^ 39 - ζ ^ 40 - ζ ^ 43 + ζ ^ 44 - ζ ^ 45 - ζ ^ 48 + ζ ^ 49 - ζ ^ 50 - ζ ^ 53 + ζ ^ 54 - ζ ^ 58)
private theorem row15_generatorB_mul_eigenbasis_3_4 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        3 4 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        3 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((650 / 1533) : ℂ) + ((352 / 511) : ℂ) * ζ ^ 3 + ((650 / 1533) : ℂ) * ζ ^ 4 - ((5281 / 1533) : ℂ) * ζ ^ 5 - ((108 / 511) : ℂ) * ζ ^ 6 + ((2722 / 1533) : ℂ) * ζ ^ 8 + ((5281 / 1533) : ℂ) * ζ ^ 9 + ((3884 / 1533) : ℂ) * ζ ^ 10 - ((2782 / 1533) : ℂ) * ζ ^ 13 - ((4208 / 1533) : ℂ) * ζ ^ 14 - ((5302 / 1533) : ℂ) * ζ ^ 15 + ((929 / 219) : ℂ) * ζ ^ 18 + ((5302 / 1533) : ℂ) * ζ ^ 19 + ((1284 / 511) : ℂ) * ζ ^ 20 + ((108 / 511) : ℂ) * ζ ^ 22 - ((6955 / 1533) : ℂ) * ζ ^ 23 - ((1284 / 511) : ℂ) * ζ ^ 24 + ((656 / 511) : ℂ) * ζ ^ 25 + ((108 / 511) : ℂ) * ζ ^ 26 + ((832 / 511) : ℂ) * ζ ^ 28 - ((656 / 511) : ℂ) * ζ ^ 29 - ((17 / 511) : ℂ) * ζ ^ 30 + ((18 / 73) : ℂ) * ζ ^ 33 - ((13 / 73) : ℂ) * ζ ^ 34 - ((19 / 73) : ℂ) * ζ ^ 35 + ((13 / 73) : ℂ) * ζ ^ 38 + ((19 / 73) : ℂ) * ζ ^ 39 + ((39 / 73) : ℂ) * ζ ^ 40 - ((19 / 73) : ℂ) * ζ ^ 43 - ((39 / 73) : ℂ) * ζ ^ 44 - ((57 / 73) : ℂ) * ζ ^ 45 + ((39 / 73) : ℂ) * ζ ^ 48 + ((57 / 73) : ℂ) * ζ ^ 49 + ((44 / 73) : ℂ) * ζ ^ 50 - ((57 / 73) : ℂ) * ζ ^ 53 - ((44 / 73) : ℂ) * ζ ^ 54 - ((25 / 73) : ℂ) * ζ ^ 55 + ((44 / 73) : ℂ) * ζ ^ 58 + ((25 / 73) : ℂ) * ζ ^ 59 + ((59 / 73) : ℂ) * ζ ^ 60 - ((25 / 73) : ℂ) * ζ ^ 63 - ((59 / 73) : ℂ) * ζ ^ 64 - ((75 / 73) : ℂ) * ζ ^ 65 + ((59 / 73) : ℂ) * ζ ^ 68 + ((75 / 73) : ℂ) * ζ ^ 69 + ((31 / 73) : ℂ) * ζ ^ 70 - ((75 / 73) : ℂ) * ζ ^ 73 - ((31 / 73) : ℂ) * ζ ^ 74 - ((6 / 73) : ℂ) * ζ ^ 75 + ((31 / 73) : ℂ) * ζ ^ 78 + ((6 / 73) : ℂ) * ζ ^ 79 + ((20 / 73) : ℂ) * ζ ^ 80 - ((6 / 73) : ℂ) * ζ ^ 83 - ((20 / 73) : ℂ) * ζ ^ 84 - ((18 / 73) : ℂ) * ζ ^ 85 + ((20 / 73) : ℂ) * ζ ^ 88 + ((18 / 73) : ℂ) * ζ ^ 89 - ((13 / 73) : ℂ) * ζ ^ 90 - ((18 / 73) : ℂ) * ζ ^ 93 + ((13 / 73) : ℂ) * ζ ^ 94 + ((19 / 73) : ℂ) * ζ ^ 95 - ((13 / 73) : ℂ) * ζ ^ 98 - ((19 / 73) : ℂ) * ζ ^ 99 - ((39 / 73) : ℂ) * ζ ^ 100 + ((19 / 73) : ℂ) * ζ ^ 103 + ((39 / 73) : ℂ) * ζ ^ 104)
private theorem row15_generatorB_mul_eigenbasis_3_5 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        3 5 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        3 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((1735 / 1533) : ℂ) + ((274 / 219) : ℂ) * ζ ^ 3 + ((1735 / 1533) : ℂ) * ζ ^ 4 + ((988 / 219) : ℂ) * ζ ^ 5 - ((377 / 511) : ℂ) * ζ ^ 6 - ((6665 / 1533) : ℂ) * ζ ^ 8 - ((988 / 219) : ℂ) * ζ ^ 9 - ((8807 / 1533) : ℂ) * ζ ^ 10 + ((8678 / 1533) : ℂ) * ζ ^ 13 + ((7676 / 1533) : ℂ) * ζ ^ 14 + ((7157 / 1533) : ℂ) * ζ ^ 15 - ((7640 / 1533) : ℂ) * ζ ^ 18 - ((7157 / 1533) : ℂ) * ζ ^ 19 - ((289 / 73) : ℂ) * ζ ^ 20 + ((377 / 511) : ℂ) * ζ ^ 22 + ((4540 / 1533) : ℂ) * ζ ^ 23 + ((289 / 73) : ℂ) * ζ ^ 24 + ((3455 / 1533) : ℂ) * ζ ^ 25 + ((377 / 511) : ℂ) * ζ ^ 26 - ((454 / 219) : ℂ) * ζ ^ 28 - ((3455 / 1533) : ℂ) * ζ ^ 29 - ((594 / 511) : ℂ) * ζ ^ 30 + ((2 / 73) : ℂ) * ζ ^ 33 + ((31 / 73) : ℂ) * ζ ^ 34 + ((6 / 73) : ℂ) * ζ ^ 35 - ((31 / 73) : ℂ) * ζ ^ 38 - ((6 / 73) : ℂ) * ζ ^ 39 - ((20 / 73) : ℂ) * ζ ^ 40 + ((6 / 73) : ℂ) * ζ ^ 43 + ((20 / 73) : ℂ) * ζ ^ 44 + ((18 / 73) : ℂ) * ζ ^ 45 - ((20 / 73) : ℂ) * ζ ^ 48 - ((18 / 73) : ℂ) * ζ ^ 49 - ((60 / 73) : ℂ) * ζ ^ 50 + ((18 / 73) : ℂ) * ζ ^ 53 + ((60 / 73) : ℂ) * ζ ^ 54 + ((54 / 73) : ℂ) * ζ ^ 55 - ((60 / 73) : ℂ) * ζ ^ 58 - ((54 / 73) : ℂ) * ζ ^ 59 - ((34 / 73) : ℂ) * ζ ^ 60 + ((54 / 73) : ℂ) * ζ ^ 63 + ((34 / 73) : ℂ) * ζ ^ 64 + ((16 / 73) : ℂ) * ζ ^ 65 - ((34 / 73) : ℂ) * ζ ^ 68 - ((16 / 73) : ℂ) * ζ ^ 69 - ((29 / 73) : ℂ) * ζ ^ 70 + ((16 / 73) : ℂ) * ζ ^ 73 + ((29 / 73) : ℂ) * ζ ^ 74 + ((48 / 73) : ℂ) * ζ ^ 75 - ((29 / 73) : ℂ) * ζ ^ 78 - ((48 / 73) : ℂ) * ζ ^ 79 - ((14 / 73) : ℂ) * ζ ^ 80 + ((48 / 73) : ℂ) * ζ ^ 83 + ((14 / 73) : ℂ) * ζ ^ 84 - ((2 / 73) : ℂ) * ζ ^ 85 - ((14 / 73) : ℂ) * ζ ^ 88 + ((2 / 73) : ℂ) * ζ ^ 89 + ((31 / 73) : ℂ) * ζ ^ 90 - ((2 / 73) : ℂ) * ζ ^ 93 - ((31 / 73) : ℂ) * ζ ^ 94 - ((6 / 73) : ℂ) * ζ ^ 95 + ((31 / 73) : ℂ) * ζ ^ 98 + ((6 / 73) : ℂ) * ζ ^ 99 + ((20 / 73) : ℂ) * ζ ^ 100 - ((6 / 73) : ℂ) * ζ ^ 103 - ((20 / 73) : ℂ) * ζ ^ 104)
private theorem row15_generatorB_mul_eigenbasis_4_0 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        4 0 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        4 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((101 / 21) : ℂ) - ((208 / 21) : ℂ) * ζ ^ 3 + ((101 / 21) : ℂ) * ζ ^ 4 + ((76 / 21) : ℂ) * ζ ^ 5 - ((2 / 7) : ℂ) * ζ ^ 6 + ((34 / 7) : ℂ) * ζ ^ 8 - ((76 / 21) : ℂ) * ζ ^ 9 - ((202 / 21) : ℂ) * ζ ^ 10 - ((57 / 7) : ℂ) * ζ ^ 13 + ((28 / 3) : ℂ) * ζ ^ 14 + ((5 / 3) : ℂ) * ζ ^ 15 + ((107 / 21) : ℂ) * ζ ^ 18 - ((5 / 3) : ℂ) * ζ ^ 19 - ((79 / 21) : ℂ) * ζ ^ 20 + ((2 / 7) : ℂ) * ζ ^ 22 - ((5 / 3) : ℂ) * ζ ^ 23 + ((79 / 21) : ℂ) * ζ ^ 24 - ((59 / 21) : ℂ) * ζ ^ 25 + ((2 / 7) : ℂ) * ζ ^ 26 + ((43 / 21) : ℂ) * ζ ^ 28 + ((59 / 21) : ℂ) * ζ ^ 29 - ((2 / 7) : ℂ) * ζ ^ 30)
private theorem row15_generatorB_mul_eigenbasis_4_1 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        4 1 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        4 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((53 / 7) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 3 - ((53 / 7) : ℂ) * ζ ^ 4 - ((229 / 21) : ℂ) * ζ ^ 5 + ((20 / 7) : ℂ) * ζ ^ 6 + ((29 / 21) : ℂ) * ζ ^ 8 + ((229 / 21) : ℂ) * ζ ^ 9 + ((46 / 3) : ℂ) * ζ ^ 10 - ((94 / 21) : ℂ) * ζ ^ 13 - ((262 / 21) : ℂ) * ζ ^ 14 - ((221 / 21) : ℂ) * ζ ^ 15 - ((12 / 7) : ℂ) * ζ ^ 18 + ((221 / 21) : ℂ) * ζ ^ 19 + ((58 / 7) : ℂ) * ζ ^ 20 - ((20 / 7) : ℂ) * ζ ^ 22 - ((10 / 3) : ℂ) * ζ ^ 23 - ((58 / 7) : ℂ) * ζ ^ 24 - ((95 / 21) : ℂ) * ζ ^ 25 - ((20 / 7) : ℂ) * ζ ^ 26 - ((8 / 3) : ℂ) * ζ ^ 28 + ((95 / 21) : ℂ) * ζ ^ 29 + ((20 / 7) : ℂ) * ζ ^ 30)
private theorem row15_generatorB_mul_eigenbasis_4_2 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        4 2 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        4 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((269 / 21) : ℂ) - ((5 / 21) : ℂ) * ζ ^ 3 - ((269 / 21) : ℂ) * ζ ^ 4 - ((146 / 21) : ℂ) * ζ ^ 5 - ((17 / 21) : ℂ) * ζ ^ 6 + ((290 / 21) : ℂ) * ζ ^ 8 + ((146 / 21) : ℂ) * ζ ^ 9 - ((4 / 21) : ℂ) * ζ ^ 10 - ((124 / 21) : ℂ) * ζ ^ 13 - ((13 / 21) : ℂ) * ζ ^ 14 - ((20 / 7) : ℂ) * ζ ^ 15 + ((27 / 7) : ℂ) * ζ ^ 18 + ((20 / 7) : ℂ) * ζ ^ 19 - ((32 / 7) : ℂ) * ζ ^ 20 + ((17 / 21) : ℂ) * ζ ^ 22 - ((149 / 21) : ℂ) * ζ ^ 23 + ((32 / 7) : ℂ) * ζ ^ 24 + ((27 / 7) : ℂ) * ζ ^ 25 + ((17 / 21) : ℂ) * ζ ^ 26 - ((7 / 3) : ℂ) * ζ ^ 28 - ((27 / 7) : ℂ) * ζ ^ 29 - ((38 / 21) : ℂ) * ζ ^ 30 + ζ ^ 34 - ζ ^ 35 - ζ ^ 38 + ζ ^ 39 - ζ ^ 40 - ζ ^ 43 + ζ ^ 44)
private theorem row15_generatorB_mul_eigenbasis_4_3 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        4 3 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        4 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((48 / 7) : ℂ) - ((11 / 21) : ℂ) * ζ ^ 3 - ((48 / 7) : ℂ) * ζ ^ 4 - ((149 / 21) : ℂ) * ζ ^ 5 - ((6 / 7) : ℂ) * ζ ^ 6 + (7 : ℂ) * ζ ^ 8 + ((149 / 21) : ℂ) * ζ ^ 9 - ((71 / 21) : ℂ) * ζ ^ 10 - ((89 / 21) : ℂ) * ζ ^ 13 + ((53 / 21) : ℂ) * ζ ^ 14 - ((41 / 21) : ℂ) * ζ ^ 15 - ((19 / 21) : ℂ) * ζ ^ 18 + ((41 / 21) : ℂ) * ζ ^ 19 - ((47 / 7) : ℂ) * ζ ^ 20 + ((6 / 7) : ℂ) * ζ ^ 22 - ((83 / 21) : ℂ) * ζ ^ 23 + ((47 / 7) : ℂ) * ζ ^ 24 + ((2 / 21) : ℂ) * ζ ^ 25 + ((6 / 7) : ℂ) * ζ ^ 26 - ((13 / 3) : ℂ) * ζ ^ 28 - ((2 / 21) : ℂ) * ζ ^ 29 - ((13 / 7) : ℂ) * ζ ^ 30 - ζ ^ 33 + ζ ^ 34 - ζ ^ 38 - ζ ^ 45 + ζ ^ 49 - ζ ^ 50 - ζ ^ 53 + ζ ^ 54 - ζ ^ 58 - ζ ^ 60 + ζ ^ 64 - ζ ^ 68)
private theorem row15_generatorB_mul_eigenbasis_4_4 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        4 4 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        4 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((880 / 219) : ℂ) + ((7423 / 1533) : ℂ) * ζ ^ 3 + ((880 / 219) : ℂ) * ζ ^ 4 + ((380 / 1533) : ℂ) * ζ ^ 5 + ((136 / 511) : ℂ) * ζ ^ 6 - ((1747 / 511) : ℂ) * ζ ^ 8 - ((380 / 1533) : ℂ) * ζ ^ 9 + ((111 / 511) : ℂ) * ζ ^ 10 + ((7075 / 1533) : ℂ) * ζ ^ 13 + ((25 / 511) : ℂ) * ζ ^ 14 + ((377 / 511) : ℂ) * ζ ^ 15 - ((1667 / 1533) : ℂ) * ζ ^ 18 - ((377 / 511) : ℂ) * ζ ^ 19 + ((386 / 1533) : ℂ) * ζ ^ 20 - ((136 / 511) : ℂ) * ζ ^ 22 - ((586 / 1533) : ℂ) * ζ ^ 23 - ((386 / 1533) : ℂ) * ζ ^ 24 + ((1475 / 511) : ℂ) * ζ ^ 25 - ((136 / 511) : ℂ) * ζ ^ 26 + ((157 / 511) : ℂ) * ζ ^ 28 - ((1475 / 511) : ℂ) * ζ ^ 29 + ((136 / 511) : ℂ) * ζ ^ 30 - ζ ^ 45 + ζ ^ 49 - ζ ^ 53 - ζ ^ 65 + ζ ^ 69 - ζ ^ 73)
private theorem row15_generatorB_mul_eigenbasis_4_5 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        4 5 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        4 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((1559 / 511) : ℂ) - ((6313 / 1533) : ℂ) * ζ ^ 3 - ((1559 / 511) : ℂ) * ζ ^ 4 - ((3113 / 1533) : ℂ) * ζ ^ 5 - ((52 / 1533) : ℂ) * ζ ^ 6 + ((909 / 511) : ℂ) * ζ ^ 8 + ((3113 / 1533) : ℂ) * ζ ^ 9 - ((766 / 1533) : ℂ) * ζ ^ 10 - ((1006 / 511) : ℂ) * ζ ^ 13 + ((34 / 73) : ℂ) * ζ ^ 14 + ((296 / 1533) : ℂ) * ζ ^ 15 - ((2797 / 1533) : ℂ) * ζ ^ 18 - ((296 / 1533) : ℂ) * ζ ^ 19 - ((3307 / 1533) : ℂ) * ζ ^ 20 + ((52 / 1533) : ℂ) * ζ ^ 22 + ((492 / 511) : ℂ) * ζ ^ 23 + ((3307 / 1533) : ℂ) * ζ ^ 24 - ((68 / 1533) : ℂ) * ζ ^ 25 + ((52 / 1533) : ℂ) * ζ ^ 26 - ((1870 / 1533) : ℂ) * ζ ^ 28 + ((68 / 1533) : ℂ) * ζ ^ 29 - ((52 / 1533) : ℂ) * ζ ^ 30)
private theorem row15_generatorB_mul_eigenbasis_5_0 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        5 0 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        5 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((83 / 21) : ℂ) + ((170 / 21) : ℂ) * ζ ^ 3 + ((83 / 21) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 5 - ((50 / 7) : ℂ) * ζ ^ 6 - ((27 / 7) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 9 - ((10 / 3) : ℂ) * ζ ^ 10 - ((3 / 7) : ℂ) * ζ ^ 13 - ((80 / 21) : ℂ) * ζ ^ 14 - ((7 / 3) : ℂ) * ζ ^ 15 + ((260 / 21) : ℂ) * ζ ^ 18 + ((7 / 3) : ℂ) * ζ ^ 19 - ((34 / 21) : ℂ) * ζ ^ 20 + ((50 / 7) : ℂ) * ζ ^ 22 - ((155 / 21) : ℂ) * ζ ^ 23 + ((34 / 21) : ℂ) * ζ ^ 24 + ((202 / 21) : ℂ) * ζ ^ 25 + ((50 / 7) : ℂ) * ζ ^ 26 + ((88 / 21) : ℂ) * ζ ^ 28 - ((202 / 21) : ℂ) * ζ ^ 29 - ((50 / 7) : ℂ) * ζ ^ 30)
private theorem row15_generatorB_mul_eigenbasis_5_1 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        5 1 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        5 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 ((9 : ℂ) - ((281 / 21) : ℂ) * ζ ^ 3 - (9 : ℂ) * ζ ^ 4 - ((31 / 21) : ℂ) * ζ ^ 5 + (7 : ℂ) * ζ ^ 6 + ((155 / 21) : ℂ) * ζ ^ 8 + ((31 / 21) : ℂ) * ζ ^ 9 + ((55 / 21) : ℂ) * ζ ^ 10 - ((55 / 21) : ℂ) * ζ ^ 13 + ((92 / 21) : ℂ) * ζ ^ 14 - ((80 / 21) : ℂ) * ζ ^ 15 - ((48 / 7) : ℂ) * ζ ^ 18 + ((80 / 21) : ℂ) * ζ ^ 19 + ((50 / 7) : ℂ) * ζ ^ 20 - (7 : ℂ) * ζ ^ 22 + ((32 / 21) : ℂ) * ζ ^ 23 - ((50 / 7) : ℂ) * ζ ^ 24 - ((314 / 21) : ℂ) * ζ ^ 25 - (7 : ℂ) * ζ ^ 26 + ((46 / 21) : ℂ) * ζ ^ 28 + ((314 / 21) : ℂ) * ζ ^ 29 + (7 : ℂ) * ζ ^ 30)
private theorem row15_generatorB_mul_eigenbasis_5_2 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        5 2 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        5 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((74 / 21) : ℂ) + ((124 / 21) : ℂ) * ζ ^ 3 - ((74 / 21) : ℂ) * ζ ^ 4 - ((68 / 21) : ℂ) * ζ ^ 5 - ((5 / 3) : ℂ) * ζ ^ 6 + ((23 / 21) : ℂ) * ζ ^ 8 + ((68 / 21) : ℂ) * ζ ^ 9 + ((164 / 21) : ℂ) * ζ ^ 10 - ((157 / 21) : ℂ) * ζ ^ 13 - ((199 / 21) : ℂ) * ζ ^ 14 - ((38 / 7) : ℂ) * ζ ^ 15 + (5 : ℂ) * ζ ^ 18 + ((38 / 7) : ℂ) * ζ ^ 19 + (2 : ℂ) * ζ ^ 20 + ((5 / 3) : ℂ) * ζ ^ 22 - ((20 / 3) : ℂ) * ζ ^ 23 - (2 : ℂ) * ζ ^ 24 - ((25 / 7) : ℂ) * ζ ^ 25 + ((5 / 3) : ℂ) * ζ ^ 26 + ((125 / 21) : ℂ) * ζ ^ 28 + ((25 / 7) : ℂ) * ζ ^ 29 - ((5 / 3) : ℂ) * ζ ^ 30)
private theorem row15_generatorB_mul_eigenbasis_5_3 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        5 3 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        5 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((12 / 7) : ℂ) + ((67 / 21) : ℂ) * ζ ^ 3 + ((12 / 7) : ℂ) * ζ ^ 4 - ((26 / 21) : ℂ) * ζ ^ 5 - ((2 / 7) : ℂ) * ζ ^ 6 - ((26 / 7) : ℂ) * ζ ^ 8 + ((26 / 21) : ℂ) * ζ ^ 9 - ((47 / 21) : ℂ) * ζ ^ 10 - ((8 / 21) : ℂ) * ζ ^ 13 + ((41 / 21) : ℂ) * ζ ^ 14 - ((137 / 21) : ℂ) * ζ ^ 15 + ((47 / 21) : ℂ) * ζ ^ 18 + ((137 / 21) : ℂ) * ζ ^ 19 + ((24 / 7) : ℂ) * ζ ^ 20 + ((2 / 7) : ℂ) * ζ ^ 22 - ((20 / 3) : ℂ) * ζ ^ 23 - ((24 / 7) : ℂ) * ζ ^ 24 - ((109 / 21) : ℂ) * ζ ^ 25 + ((2 / 7) : ℂ) * ζ ^ 26 + ((122 / 21) : ℂ) * ζ ^ 28 + ((109 / 21) : ℂ) * ζ ^ 29 - ((2 / 7) : ℂ) * ζ ^ 30 - ζ ^ 35 + ζ ^ 39 - ζ ^ 43)
private theorem row15_generatorB_mul_eigenbasis_5_4 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        5 4 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        5 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((4876 / 1533) : ℂ) + ((2512 / 1533) : ℂ) * ζ ^ 3 + ((4876 / 1533) : ℂ) * ζ ^ 4 + ((7067 / 1533) : ℂ) * ζ ^ 5 + ((121 / 73) : ℂ) * ζ ^ 6 - ((1896 / 511) : ℂ) * ζ ^ 8 - ((7067 / 1533) : ℂ) * ζ ^ 9 - ((1019 / 511) : ℂ) * ζ ^ 10 + ((8623 / 1533) : ℂ) * ζ ^ 13 + ((1866 / 511) : ℂ) * ζ ^ 14 + ((3095 / 511) : ℂ) * ζ ^ 15 - ((8774 / 1533) : ℂ) * ζ ^ 18 - ((3095 / 511) : ℂ) * ζ ^ 19 - ((3484 / 1533) : ℂ) * ζ ^ 20 - ((121 / 73) : ℂ) * ζ ^ 22 + ((7862 / 1533) : ℂ) * ζ ^ 23 + ((3484 / 1533) : ℂ) * ζ ^ 24 + ((807 / 511) : ℂ) * ζ ^ 25 - ((121 / 73) : ℂ) * ζ ^ 26 - ((960 / 511) : ℂ) * ζ ^ 28 - ((807 / 511) : ℂ) * ζ ^ 29 + ((121 / 73) : ℂ) * ζ ^ 30)
private theorem row15_generatorB_mul_eigenbasis_5_5 :
    (alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis)
        5 5 =
      (alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal)
        5 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row15_matrixB,
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15GeneratorBDiagonal,
      alternatingSixAmbientRow15GeneratorBEigenvalue,
      alternatingSixAmbientRow15EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((2004 / 511) : ℂ) - ((5569 / 1533) : ℂ) * ζ ^ 3 - ((2004 / 511) : ℂ) * ζ ^ 4 - ((9962 / 1533) : ℂ) * ζ ^ 5 + ((89 / 219) : ℂ) * ζ ^ 6 + ((2831 / 511) : ℂ) * ζ ^ 8 + ((9962 / 1533) : ℂ) * ζ ^ 9 + ((10586 / 1533) : ℂ) * ζ ^ 10 - ((3601 / 511) : ℂ) * ζ ^ 13 - ((3321 / 511) : ℂ) * ζ ^ 14 - ((9967 / 1533) : ℂ) * ζ ^ 15 + ((1184 / 219) : ℂ) * ζ ^ 18 + ((9967 / 1533) : ℂ) * ζ ^ 19 + ((4877 / 1533) : ℂ) * ζ ^ 20 - ((89 / 219) : ℂ) * ζ ^ 22 - ((2034 / 511) : ℂ) * ζ ^ 23 - ((4877 / 1533) : ℂ) * ζ ^ 24 - ((3965 / 1533) : ℂ) * ζ ^ 25 - ((89 / 219) : ℂ) * ζ ^ 26 + ((3476 / 1533) : ℂ) * ζ ^ 28 + ((3965 / 1533) : ℂ) * ζ ^ 29 + ((89 / 219) : ℂ) * ζ ^ 30 - ζ ^ 45 + ζ ^ 49 - ζ ^ 53 - ζ ^ 65 + ζ ^ 69 - ζ ^ 73)
/-- The checked row 15 basis diagonalizes the second
generator. -/
theorem alternatingSixAmbientRow15GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row15_matrixB *
        alternatingSixAmbientRow15Eigenbasis =
      alternatingSixAmbientRow15Eigenbasis *
        alternatingSixAmbientRow15GeneratorBDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row15_generatorB_mul_eigenbasis_0_0
  · exact row15_generatorB_mul_eigenbasis_0_1
  · exact row15_generatorB_mul_eigenbasis_0_2
  · exact row15_generatorB_mul_eigenbasis_0_3
  · exact row15_generatorB_mul_eigenbasis_0_4
  · exact row15_generatorB_mul_eigenbasis_0_5
  · exact row15_generatorB_mul_eigenbasis_1_0
  · exact row15_generatorB_mul_eigenbasis_1_1
  · exact row15_generatorB_mul_eigenbasis_1_2
  · exact row15_generatorB_mul_eigenbasis_1_3
  · exact row15_generatorB_mul_eigenbasis_1_4
  · exact row15_generatorB_mul_eigenbasis_1_5
  · exact row15_generatorB_mul_eigenbasis_2_0
  · exact row15_generatorB_mul_eigenbasis_2_1
  · exact row15_generatorB_mul_eigenbasis_2_2
  · exact row15_generatorB_mul_eigenbasis_2_3
  · exact row15_generatorB_mul_eigenbasis_2_4
  · exact row15_generatorB_mul_eigenbasis_2_5
  · exact row15_generatorB_mul_eigenbasis_3_0
  · exact row15_generatorB_mul_eigenbasis_3_1
  · exact row15_generatorB_mul_eigenbasis_3_2
  · exact row15_generatorB_mul_eigenbasis_3_3
  · exact row15_generatorB_mul_eigenbasis_3_4
  · exact row15_generatorB_mul_eigenbasis_3_5
  · exact row15_generatorB_mul_eigenbasis_4_0
  · exact row15_generatorB_mul_eigenbasis_4_1
  · exact row15_generatorB_mul_eigenbasis_4_2
  · exact row15_generatorB_mul_eigenbasis_4_3
  · exact row15_generatorB_mul_eigenbasis_4_4
  · exact row15_generatorB_mul_eigenbasis_4_5
  · exact row15_generatorB_mul_eigenbasis_5_0
  · exact row15_generatorB_mul_eigenbasis_5_1
  · exact row15_generatorB_mul_eigenbasis_5_2
  · exact row15_generatorB_mul_eigenbasis_5_3
  · exact row15_generatorB_mul_eigenbasis_5_4
  · exact row15_generatorB_mul_eigenbasis_5_5


private theorem row15_transformedGeneratorA_0_0 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        0 0 =
      alternatingSixAmbientRow15TransformedGeneratorA
        0 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((111 / 28) : ℂ) + ((755 / 42) : ℂ) * ζ ^ 3 + ((111 / 28) : ℂ) * ζ ^ 4 + ((421 / 84) : ℂ) * ζ ^ 5 - ((103 / 7) : ℂ) * ζ ^ 6 - ((463 / 21) : ℂ) * ζ ^ 8 - ((383 / 84) : ℂ) * ζ ^ 9 - ((386 / 21) : ℂ) * ζ ^ 10 + ((191 / 84) : ℂ) * ζ ^ 11 + ((2431 / 84) : ℂ) * ζ ^ 13 + ((11 / 3) : ℂ) * ζ ^ 14 + ((145 / 42) : ℂ) * ζ ^ 15 - ((164 / 21) : ℂ) * ζ ^ 16 + ((19 / 42) : ℂ) * ζ ^ 17 - ((152 / 21) : ℂ) * ζ ^ 18 - ((33 / 28) : ℂ) * ζ ^ 19 - ((215 / 84) : ℂ) * ζ ^ 20 - ((683 / 84) : ℂ) * ζ ^ 21 + ((103 / 7) : ℂ) * ζ ^ 22 - ((895 / 84) : ℂ) * ζ ^ 23 - ((21 / 4) : ℂ) * ζ ^ 24 - ((445 / 42) : ℂ) * ζ ^ 25 + ((751 / 28) : ℂ) * ζ ^ 26 - ((191 / 84) : ℂ) * ζ ^ 27 + ((131 / 7) : ℂ) * ζ ^ 28 - ((1 / 4) : ℂ) * ζ ^ 29 + ((104 / 21) : ℂ) * ζ ^ 30 - ((208 / 21) : ℂ) * ζ ^ 31 + ((164 / 21) : ℂ) * ζ ^ 32 - ((859 / 84) : ℂ) * ζ ^ 33 - ((635 / 84) : ℂ) * ζ ^ 34 - ((79 / 28) : ℂ) * ζ ^ 35 + ((1343 / 84) : ℂ) * ζ ^ 36 + ((253 / 28) : ℂ) * ζ ^ 37 - ((947 / 84) : ℂ) * ζ ^ 38 - ((71 / 28) : ℂ) * ζ ^ 39 - ((305 / 84) : ℂ) * ζ ^ 40 + ((253 / 28) : ℂ) * ζ ^ 41 - ((339 / 28) : ℂ) * ζ ^ 42 + ((59 / 3) : ℂ) * ζ ^ 43 + (4 : ℂ) * ζ ^ 44 - ((9 / 28) : ℂ) * ζ ^ 45 - ((339 / 28) : ℂ) * ζ ^ 46 + ((641 / 84) : ℂ) * ζ ^ 47 - ((545 / 28) : ℂ) * ζ ^ 48 - ((145 / 21) : ℂ) * ζ ^ 49 + ((85 / 14) : ℂ) * ζ ^ 50 + ((641 / 84) : ℂ) * ζ ^ 51 - ((229 / 28) : ℂ) * ζ ^ 52 + ((214 / 21) : ℂ) * ζ ^ 53 + ((169 / 28) : ℂ) * ζ ^ 54 - ((517 / 84) : ℂ) * ζ ^ 55 - ((229 / 28) : ℂ) * ζ ^ 56 - ((19 / 42) : ℂ) * ζ ^ 57 - ((83 / 84) : ℂ) * ζ ^ 58 - ((31 / 21) : ℂ) * ζ ^ 59 + ((229 / 28) : ℂ) * ζ ^ 60 + ((19 / 42) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_0_1 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        0 1 =
      alternatingSixAmbientRow15TransformedGeneratorA
        0 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((2777 / 252) : ℂ) - ((4111 / 126) : ℂ) * ζ ^ 3 - ((2777 / 252) : ℂ) * ζ ^ 4 - ((1135 / 63) : ℂ) * ζ ^ 5 + ((3839 / 126) : ℂ) * ζ ^ 6 + ((3044 / 63) : ℂ) * ζ ^ 8 + ((592 / 63) : ℂ) * ζ ^ 9 + ((3254 / 63) : ℂ) * ζ ^ 10 - ((359 / 28) : ℂ) * ζ ^ 11 - ((6649 / 84) : ℂ) * ζ ^ 13 - ((2669 / 126) : ℂ) * ζ ^ 14 - ((1411 / 42) : ℂ) * ζ ^ 15 + ((331 / 28) : ℂ) * ζ ^ 16 - ((181 / 21) : ℂ) * ζ ^ 17 + ((7939 / 252) : ℂ) * ζ ^ 18 + ((1745 / 84) : ℂ) * ζ ^ 19 + ((1460 / 63) : ℂ) * ζ ^ 20 + ((719 / 42) : ℂ) * ζ ^ 21 - ((3839 / 126) : ℂ) * ζ ^ 22 - ((452 / 63) : ℂ) * ζ ^ 23 - ((2861 / 252) : ℂ) * ζ ^ 24 + ((5465 / 252) : ℂ) * ζ ^ 25 - ((929 / 18) : ℂ) * ζ ^ 26 + ((359 / 28) : ℂ) * ζ ^ 27 - ((1363 / 252) : ℂ) * ζ ^ 28 + ((11881 / 252) : ℂ) * ζ ^ 29 - ((2873 / 252) : ℂ) * ζ ^ 30 + ((2879 / 84) : ℂ) * ζ ^ 31 - ((331 / 28) : ℂ) * ζ ^ 32 + ((1511 / 42) : ℂ) * ζ ^ 33 + ((1741 / 84) : ℂ) * ζ ^ 34 + ((178 / 7) : ℂ) * ζ ^ 35 - ((3161 / 84) : ℂ) * ζ ^ 36 - ((481 / 14) : ℂ) * ζ ^ 37 - ((565 / 84) : ℂ) * ζ ^ 38 - ((1411 / 84) : ℂ) * ζ ^ 39 - ((3263 / 84) : ℂ) * ζ ^ 40 - ((481 / 14) : ℂ) * ζ ^ 41 + ((148 / 7) : ℂ) * ζ ^ 42 + ((103 / 42) : ℂ) * ζ ^ 43 + ((174 / 7) : ℂ) * ζ ^ 44 + ((1103 / 42) : ℂ) * ζ ^ 45 + ((148 / 7) : ℂ) * ζ ^ 46 - ((901 / 42) : ℂ) * ζ ^ 47 + ((25 / 42) : ℂ) * ζ ^ 48 - ((554 / 21) : ℂ) * ζ ^ 49 - ((926 / 21) : ℂ) * ζ ^ 50 - ((901 / 42) : ℂ) * ζ ^ 51 + ((542 / 21) : ℂ) * ζ ^ 52 + ((271 / 14) : ℂ) * ζ ^ 53 + ((482 / 21) : ℂ) * ζ ^ 54 + ((115 / 3) : ℂ) * ζ ^ 55 + ((542 / 21) : ℂ) * ζ ^ 56 + ((181 / 21) : ℂ) * ζ ^ 57 - ((127 / 28) : ℂ) * ζ ^ 58 - ((709 / 42) : ℂ) * ζ ^ 59 - ((542 / 21) : ℂ) * ζ ^ 60 - ((181 / 21) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_0_2 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        0 2 =
      alternatingSixAmbientRow15TransformedGeneratorA
        0 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((421 / 126) : ℂ) - ((79 / 18) : ℂ) * ζ ^ 3 - ((421 / 126) : ℂ) * ζ ^ 4 - ((991 / 63) : ℂ) * ζ ^ 5 + ((13 / 36) : ℂ) * ζ ^ 6 + ((548 / 63) : ℂ) * ζ ^ 8 + ((187 / 9) : ℂ) * ζ ^ 9 + ((8489 / 252) : ℂ) * ζ ^ 10 + ((19 / 3) : ℂ) * ζ ^ 11 - ((265 / 42) : ℂ) * ζ ^ 13 - ((4199 / 126) : ℂ) * ζ ^ 14 - ((1187 / 42) : ℂ) * ζ ^ 15 - ((745 / 84) : ℂ) * ζ ^ 16 + ((106 / 21) : ℂ) * ζ ^ 17 + ((670 / 63) : ℂ) * ζ ^ 18 + ((1453 / 42) : ℂ) * ζ ^ 19 + ((1655 / 63) : ℂ) * ζ ^ 20 - ((653 / 84) : ℂ) * ζ ^ 21 - ((13 / 36) : ℂ) * ζ ^ 22 - ((3623 / 252) : ℂ) * ζ ^ 23 - ((1265 / 36) : ℂ) * ζ ^ 24 - ((9565 / 252) : ℂ) * ζ ^ 25 + ((230 / 63) : ℂ) * ζ ^ 26 - ((19 / 3) : ℂ) * ζ ^ 27 + ((479 / 36) : ℂ) * ζ ^ 28 - ((13 / 126) : ℂ) * ζ ^ 29 - ((751 / 126) : ℂ) * ζ ^ 30 - ((453 / 28) : ℂ) * ζ ^ 31 + ((745 / 84) : ℂ) * ζ ^ 32 + ((19 / 28) : ℂ) * ζ ^ 33 + ((31 / 3) : ℂ) * ζ ^ 34 + ((913 / 84) : ℂ) * ζ ^ 35 + ((62 / 3) : ℂ) * ζ ^ 36 + ((1501 / 84) : ℂ) * ζ ^ 37 - ((481 / 84) : ℂ) * ζ ^ 38 - ((302 / 21) : ℂ) * ζ ^ 39 - ((25 / 2) : ℂ) * ζ ^ 40 + ((1501 / 84) : ℂ) * ζ ^ 41 - ((337 / 84) : ℂ) * ζ ^ 42 + ((1553 / 84) : ℂ) * ζ ^ 43 + ((108 / 7) : ℂ) * ζ ^ 44 + ((101 / 6) : ℂ) * ζ ^ 45 - ((337 / 84) : ℂ) * ζ ^ 46 + ((827 / 84) : ℂ) * ζ ^ 47 - ((1529 / 84) : ℂ) * ζ ^ 48 - ((1219 / 84) : ℂ) * ζ ^ 49 + ((83 / 42) : ℂ) * ζ ^ 50 + ((827 / 84) : ℂ) * ζ ^ 51 - ((991 / 84) : ℂ) * ζ ^ 52 + ((19 / 12) : ℂ) * ζ ^ 53 + ((57 / 28) : ℂ) * ζ ^ 54 - ((33 / 4) : ℂ) * ζ ^ 55 - ((991 / 84) : ℂ) * ζ ^ 56 - ((106 / 21) : ℂ) * ζ ^ 57 - ((187 / 28) : ℂ) * ζ ^ 58 - ((67 / 42) : ℂ) * ζ ^ 59 + ((991 / 84) : ℂ) * ζ ^ 60 + ((106 / 21) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_0_3 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        0 3 =
      alternatingSixAmbientRow15TransformedGeneratorA
        0 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((673 / 252) : ℂ) + ((163 / 252) : ℂ) * ζ ^ 3 + ((673 / 252) : ℂ) * ζ ^ 4 - ((277 / 252) : ℂ) * ζ ^ 5 - ((635 / 252) : ℂ) * ζ ^ 6 + ((23 / 9) : ℂ) * ζ ^ 8 + ((485 / 126) : ℂ) * ζ ^ 9 - ((169 / 36) : ℂ) * ζ ^ 10 + ((13 / 12) : ℂ) * ζ ^ 11 + (13 : ℂ) * ζ ^ 13 + ((137 / 63) : ℂ) * ζ ^ 14 + ((73 / 84) : ℂ) * ζ ^ 15 - ((212 / 21) : ℂ) * ζ ^ 16 + ((11 / 4) : ℂ) * ζ ^ 17 - ((857 / 252) : ℂ) * ζ ^ 18 + ((3 / 14) : ℂ) * ζ ^ 19 - ((85 / 36) : ℂ) * ζ ^ 20 - ((82 / 21) : ℂ) * ζ ^ 21 + ((635 / 252) : ℂ) * ζ ^ 22 + ((2143 / 252) : ℂ) * ζ ^ 23 - ((1949 / 252) : ℂ) * ζ ^ 24 - ((5263 / 252) : ℂ) * ζ ^ 25 + ((91 / 18) : ℂ) * ζ ^ 26 - ((13 / 12) : ℂ) * ζ ^ 27 + ((289 / 18) : ℂ) * ζ ^ 28 + ((121 / 252) : ℂ) * ζ ^ 29 + ((2173 / 252) : ℂ) * ζ ^ 30 - ((151 / 21) : ℂ) * ζ ^ 31 + ((212 / 21) : ℂ) * ζ ^ 32 - ((1129 / 84) : ℂ) * ζ ^ 33 - ((241 / 28) : ℂ) * ζ ^ 34 - ((1075 / 84) : ℂ) * ζ ^ 35 + ((103 / 6) : ℂ) * ζ ^ 36 + ((395 / 42) : ℂ) * ζ ^ 37 + ((100 / 7) : ℂ) * ζ ^ 38 + ((653 / 84) : ℂ) * ζ ^ 39 + ((223 / 42) : ℂ) * ζ ^ 40 + ((395 / 42) : ℂ) * ζ ^ 41 - ((71 / 28) : ℂ) * ζ ^ 42 - ((27 / 4) : ℂ) * ζ ^ 43 - ((25 / 3) : ℂ) * ζ ^ 44 + ((269 / 84) : ℂ) * ζ ^ 45 - ((71 / 28) : ℂ) * ζ ^ 46 + ((171 / 28) : ℂ) * ζ ^ 47 - ((421 / 84) : ℂ) * ζ ^ 48 - ((45 / 28) : ℂ) * ζ ^ 49 + ((15 / 4) : ℂ) * ζ ^ 50 + ((171 / 28) : ℂ) * ζ ^ 51 - ((99 / 14) : ℂ) * ζ ^ 52 - ((32 / 21) : ℂ) * ζ ^ 53 - ((17 / 14) : ℂ) * ζ ^ 54 - ((99 / 28) : ℂ) * ζ ^ 55 - ((99 / 14) : ℂ) * ζ ^ 56 - ((11 / 4) : ℂ) * ζ ^ 57 - ((163 / 42) : ℂ) * ζ ^ 58 - ((18 / 7) : ℂ) * ζ ^ 59 + ((99 / 14) : ℂ) * ζ ^ 60 + ((11 / 4) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_0_4 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        0 4 =
      alternatingSixAmbientRow15TransformedGeneratorA
        0 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((26581 / 6132) : ℂ) + ((7075 / 1022) : ℂ) * ζ ^ 3 + ((26581 / 6132) : ℂ) * ζ ^ 4 + ((67241 / 6132) : ℂ) * ζ ^ 5 - ((5973 / 1022) : ℂ) * ζ ^ 6 - ((7906 / 511) : ℂ) * ζ ^ 8 - ((9341 / 1022) : ℂ) * ζ ^ 9 - ((36013 / 1533) : ℂ) * ζ ^ 10 + ((5822 / 1533) : ℂ) * ζ ^ 11 + ((25773 / 1022) : ℂ) * ζ ^ 13 + ((54107 / 3066) : ℂ) * ζ ^ 14 + ((184279 / 6132) : ℂ) * ζ ^ 15 - ((18839 / 6132) : ℂ) * ζ ^ 16 + ((11195 / 6132) : ℂ) * ζ ^ 17 - ((37651 / 1533) : ℂ) * ζ ^ 18 - ((160991 / 6132) : ℂ) * ζ ^ 19 - ((205181 / 6132) : ℂ) * ζ ^ 20 + ((7865 / 6132) : ℂ) * ζ ^ 21 + ((5973 / 1022) : ℂ) * ζ ^ 22 + ((175237 / 6132) : ℂ) * ζ ^ 23 + ((31057 / 1022) : ℂ) * ζ ^ 24 + ((62983 / 3066) : ℂ) * ζ ^ 25 + ((10813 / 2044) : ℂ) * ζ ^ 26 - ((5822 / 1533) : ℂ) * ζ ^ 27 - ((28006 / 1533) : ℂ) * ζ ^ 28 - ((61757 / 2044) : ℂ) * ζ ^ 29 - ((32633 / 2044) : ℂ) * ζ ^ 30 - ((37021 / 6132) : ℂ) * ζ ^ 31 + ((18839 / 6132) : ℂ) * ζ ^ 32 + ((11 / 21) : ℂ) * ζ ^ 33 + ((9777 / 1022) : ℂ) * ζ ^ 34 + ((1184 / 511) : ℂ) * ζ ^ 35 + ((3161 / 511) : ℂ) * ζ ^ 36 + ((2075 / 876) : ℂ) * ζ ^ 37 + ((3641 / 1022) : ℂ) * ζ ^ 38 - ((1551 / 2044) : ℂ) * ζ ^ 39 + ((32759 / 6132) : ℂ) * ζ ^ 40 + ((2075 / 876) : ℂ) * ζ ^ 41 + ((1133 / 2044) : ℂ) * ζ ^ 42 - ((21215 / 3066) : ℂ) * ζ ^ 43 - ((10835 / 2044) : ℂ) * ζ ^ 44 - ((15833 / 6132) : ℂ) * ζ ^ 45 + ((1133 / 2044) : ℂ) * ζ ^ 46 + ((13733 / 6132) : ℂ) * ζ ^ 47 + ((10414 / 1533) : ℂ) * ζ ^ 48 + ((1646 / 219) : ℂ) * ζ ^ 49 + ((14201 / 2044) : ℂ) * ζ ^ 50 + ((13733 / 6132) : ℂ) * ζ ^ 51 - ((19093 / 6132) : ℂ) * ζ ^ 52 - ((45973 / 6132) : ℂ) * ζ ^ 53 - ((7667 / 1022) : ℂ) * ζ ^ 54 - ((4249 / 876) : ℂ) * ζ ^ 55 - ((19093 / 6132) : ℂ) * ζ ^ 56 - ((11195 / 6132) : ℂ) * ζ ^ 57 + ((680 / 511) : ℂ) * ζ ^ 58 + ((8005 / 3066) : ℂ) * ζ ^ 59 + ((19093 / 6132) : ℂ) * ζ ^ 60 + ((11195 / 6132) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_0_5 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        0 5 =
      alternatingSixAmbientRow15TransformedGeneratorA
        0 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((26480 / 4599) : ℂ) - ((26897 / 2628) : ℂ) * ζ ^ 3 - ((26480 / 4599) : ℂ) * ζ ^ 4 - ((342781 / 18396) : ℂ) * ζ ^ 5 + ((67757 / 9198) : ℂ) * ζ ^ 6 + ((418421 / 18396) : ℂ) * ζ ^ 8 + ((332083 / 18396) : ℂ) * ζ ^ 9 + ((98681 / 2628) : ℂ) * ζ ^ 10 - ((8399 / 3066) : ℂ) * ζ ^ 11 - ((116531 / 3066) : ℂ) * ζ ^ 13 - ((555253 / 18396) : ℂ) * ζ ^ 14 - ((256957 / 6132) : ℂ) * ζ ^ 15 + ((12503 / 3066) : ℂ) * ζ ^ 16 - ((1783 / 3066) : ℂ) * ζ ^ 17 + ((678217 / 18396) : ℂ) * ζ ^ 18 + ((80053 / 2044) : ℂ) * ζ ^ 19 + ((205217 / 4599) : ℂ) * ζ ^ 20 - ((677 / 876) : ℂ) * ζ ^ 21 - ((67757 / 9198) : ℂ) * ζ ^ 22 - ((592115 / 18396) : ℂ) * ζ ^ 23 - ((53275 / 1314) : ℂ) * ζ ^ 24 - ((80305 / 2628) : ℂ) * ζ ^ 25 - ((154459 / 18396) : ℂ) * ζ ^ 26 + ((8399 / 3066) : ℂ) * ζ ^ 27 + ((96977 / 4599) : ℂ) * ζ ^ 28 + ((306053 / 9198) : ℂ) * ζ ^ 29 + ((92746 / 4599) : ℂ) * ζ ^ 30 + ((2648 / 1533) : ℂ) * ζ ^ 31 - ((12503 / 3066) : ℂ) * ζ ^ 32 - ((85 / 21) : ℂ) * ζ ^ 33 - ((12115 / 876) : ℂ) * ζ ^ 34 - ((15349 / 1533) : ℂ) * ζ ^ 35 - ((16459 / 3066) : ℂ) * ζ ^ 36 - ((2393 / 6132) : ℂ) * ζ ^ 37 + ((11309 / 6132) : ℂ) * ζ ^ 38 + ((9598 / 1533) : ℂ) * ζ ^ 39 + ((4927 / 1533) : ℂ) * ζ ^ 40 - ((2393 / 6132) : ℂ) * ζ ^ 41 + ((2105 / 2044) : ℂ) * ζ ^ 42 + ((1228 / 511) : ℂ) * ζ ^ 43 - ((1307 / 3066) : ℂ) * ζ ^ 44 - ((14591 / 6132) : ℂ) * ζ ^ 45 + ((2105 / 2044) : ℂ) * ζ ^ 46 + ((3103 / 3066) : ℂ) * ζ ^ 47 - ((6281 / 6132) : ℂ) * ζ ^ 48 + ((680 / 1533) : ℂ) * ζ ^ 49 + ((715 / 1533) : ℂ) * ζ ^ 50 + ((3103 / 3066) : ℂ) * ζ ^ 51 + ((1978 / 1533) : ℂ) * ζ ^ 52 - ((593 / 876) : ℂ) * ζ ^ 53 - ((9175 / 6132) : ℂ) * ζ ^ 54 + ((47 / 876) : ℂ) * ζ ^ 55 + ((1978 / 1533) : ℂ) * ζ ^ 56 + ((1783 / 3066) : ℂ) * ζ ^ 57 + ((88 / 219) : ℂ) * ζ ^ 58 - ((6535 / 6132) : ℂ) * ζ ^ 59 - ((1978 / 1533) : ℂ) * ζ ^ 60 - ((1783 / 3066) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_1_0 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        1 0 =
      alternatingSixAmbientRow15TransformedGeneratorA
        1 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((128 / 147) : ℂ) - ((2777 / 588) : ℂ) * ζ ^ 3 + ((128 / 147) : ℂ) * ζ ^ 4 + ((379 / 294) : ℂ) * ζ ^ 5 + ((5987 / 588) : ℂ) * ζ ^ 6 + ((1495 / 588) : ℂ) * ζ ^ 8 - ((5437 / 588) : ℂ) * ζ ^ 9 + ((2041 / 294) : ℂ) * ζ ^ 10 - ((57 / 14) : ℂ) * ζ ^ 11 - ((10589 / 588) : ℂ) * ζ ^ 13 + ((635 / 196) : ℂ) * ζ ^ 14 + ((205 / 294) : ℂ) * ζ ^ 15 + ((2785 / 588) : ℂ) * ζ ^ 16 - ((4679 / 588) : ℂ) * ζ ^ 17 - ((337 / 49) : ℂ) * ζ ^ 18 - ((701 / 147) : ℂ) * ζ ^ 19 - ((401 / 196) : ℂ) * ζ ^ 20 + ((8321 / 588) : ℂ) * ζ ^ 21 - ((5987 / 588) : ℂ) * ζ ^ 22 + ((339 / 196) : ℂ) * ζ ^ 23 + ((997 / 147) : ℂ) * ζ ^ 24 + ((2945 / 84) : ℂ) * ζ ^ 25 - ((2001 / 196) : ℂ) * ζ ^ 26 + ((57 / 14) : ℂ) * ζ ^ 27 + ((869 / 588) : ℂ) * ζ ^ 28 + ((1315 / 49) : ℂ) * ζ ^ 29 + ((5 / 12) : ℂ) * ζ ^ 30 + ((8299 / 588) : ℂ) * ζ ^ 31 - ((2785 / 588) : ℂ) * ζ ^ 32 + ((649 / 196) : ℂ) * ζ ^ 33 + ((409 / 42) : ℂ) * ζ ^ 34 + ((3655 / 588) : ℂ) * ζ ^ 35 - ((1874 / 147) : ℂ) * ζ ^ 36 - ((5893 / 196) : ℂ) * ζ ^ 37 + ((3799 / 588) : ℂ) * ζ ^ 38 - ((12 / 49) : ℂ) * ζ ^ 39 - ((53 / 49) : ℂ) * ζ ^ 40 - ((5893 / 196) : ℂ) * ζ ^ 41 + ((4 / 147) : ℂ) * ζ ^ 42 - ((1406 / 147) : ℂ) * ζ ^ 43 - ((215 / 98) : ℂ) * ζ ^ 44 - ((907 / 84) : ℂ) * ζ ^ 45 + ((4 / 147) : ℂ) * ζ ^ 46 - ((5905 / 588) : ℂ) * ζ ^ 47 + ((4225 / 588) : ℂ) * ζ ^ 48 + ((1328 / 147) : ℂ) * ζ ^ 49 - ((17 / 294) : ℂ) * ζ ^ 50 - ((5905 / 588) : ℂ) * ζ ^ 51 + ((673 / 84) : ℂ) * ζ ^ 52 + ((2050 / 147) : ℂ) * ζ ^ 53 + ((3 / 98) : ℂ) * ζ ^ 54 + ((1426 / 147) : ℂ) * ζ ^ 55 + ((673 / 84) : ℂ) * ζ ^ 56 + ((4679 / 588) : ℂ) * ζ ^ 57 + ((271 / 588) : ℂ) * ζ ^ 58 + ((67 / 196) : ℂ) * ζ ^ 59 - ((673 / 84) : ℂ) * ζ ^ 60 - ((4679 / 588) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_1_1 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        1 1 =
      alternatingSixAmbientRow15TransformedGeneratorA
        1 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((373 / 441) : ℂ) + ((1418 / 441) : ℂ) * ζ ^ 3 - ((373 / 441) : ℂ) * ζ ^ 4 - ((3551 / 1764) : ℂ) * ζ ^ 5 - ((7409 / 882) : ℂ) * ζ ^ 6 - ((979 / 882) : ℂ) * ζ ^ 8 + ((2003 / 252) : ℂ) * ζ ^ 9 - ((4679 / 1764) : ℂ) * ζ ^ 10 + ((41 / 21) : ℂ) * ζ ^ 11 + ((1595 / 294) : ℂ) * ζ ^ 13 - ((10139 / 1764) : ℂ) * ζ ^ 14 - ((95 / 12) : ℂ) * ζ ^ 15 - ((65 / 196) : ℂ) * ζ ^ 16 + ((1745 / 294) : ℂ) * ζ ^ 17 + ((10267 / 882) : ℂ) * ζ ^ 18 + ((829 / 84) : ℂ) * ζ ^ 19 + ((22795 / 1764) : ℂ) * ζ ^ 20 - ((527 / 84) : ℂ) * ζ ^ 21 + ((7409 / 882) : ℂ) * ζ ^ 22 - ((10525 / 1764) : ℂ) * ζ ^ 23 - ((835 / 63) : ℂ) * ζ ^ 24 - ((12962 / 441) : ℂ) * ζ ^ 25 + ((995 / 126) : ℂ) * ζ ^ 26 - ((41 / 21) : ℂ) * ζ ^ 27 + ((1513 / 1764) : ℂ) * ζ ^ 28 - ((22039 / 1764) : ℂ) * ζ ^ 29 + ((1958 / 441) : ℂ) * ζ ^ 30 - ((773 / 98) : ℂ) * ζ ^ 31 + ((65 / 196) : ℂ) * ζ ^ 32 - ((4493 / 588) : ℂ) * ζ ^ 33 - ((3923 / 294) : ℂ) * ζ ^ 34 - ((151 / 21) : ℂ) * ζ ^ 35 + ((3281 / 294) : ℂ) * ζ ^ 36 + ((10669 / 588) : ℂ) * ζ ^ 37 - ((911 / 588) : ℂ) * ζ ^ 38 + ((943 / 294) : ℂ) * ζ ^ 39 + ((279 / 28) : ℂ) * ζ ^ 40 + ((10669 / 588) : ℂ) * ζ ^ 41 + ((74 / 147) : ℂ) * ζ ^ 42 + ((59 / 588) : ℂ) * ζ ^ 43 + ((313 / 588) : ℂ) * ζ ^ 44 + ((1453 / 196) : ℂ) * ζ ^ 45 + ((74 / 147) : ℂ) * ζ ^ 46 + ((1745 / 294) : ℂ) * ζ ^ 47 - ((458 / 147) : ℂ) * ζ ^ 48 - ((89 / 49) : ℂ) * ζ ^ 49 + ((2123 / 294) : ℂ) * ζ ^ 50 + ((1745 / 294) : ℂ) * ζ ^ 51 - ((6367 / 588) : ℂ) * ζ ^ 52 - ((8795 / 588) : ℂ) * ζ ^ 53 - ((757 / 98) : ℂ) * ζ ^ 54 - ((1538 / 147) : ℂ) * ζ ^ 55 - ((6367 / 588) : ℂ) * ζ ^ 56 - ((1745 / 294) : ℂ) * ζ ^ 57 + ((23 / 84) : ℂ) * ζ ^ 58 + ((1331 / 294) : ℂ) * ζ ^ 59 + ((6367 / 588) : ℂ) * ζ ^ 60 + ((1745 / 294) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_1_2 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        1 2 =
      alternatingSixAmbientRow15TransformedGeneratorA
        1 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((4639 / 1764) : ℂ) - ((4909 / 1764) : ℂ) * ζ ^ 3 - ((4639 / 1764) : ℂ) * ζ ^ 4 - ((1196 / 441) : ℂ) * ζ ^ 5 + ((4051 / 882) : ℂ) * ζ ^ 6 + ((6229 / 1764) : ℂ) * ζ ^ 8 + ((3011 / 1764) : ℂ) * ζ ^ 9 + ((14671 / 1764) : ℂ) * ζ ^ 10 - ((307 / 84) : ℂ) * ζ ^ 11 - ((613 / 588) : ℂ) * ζ ^ 13 - ((6569 / 1764) : ℂ) * ζ ^ 14 - ((503 / 84) : ℂ) * ζ ^ 15 - ((1033 / 196) : ℂ) * ζ ^ 16 - ((197 / 196) : ℂ) * ζ ^ 17 - ((3839 / 882) : ℂ) * ζ ^ 18 + ((7 / 3) : ℂ) * ζ ^ 19 - ((6791 / 1764) : ℂ) * ζ ^ 20 - ((1573 / 588) : ℂ) * ζ ^ 21 - ((4051 / 882) : ℂ) * ζ ^ 22 + ((8291 / 1764) : ℂ) * ζ ^ 23 - ((179 / 126) : ℂ) * ζ ^ 24 - ((404 / 441) : ℂ) * ζ ^ 25 - ((35 / 9) : ℂ) * ζ ^ 26 + ((307 / 84) : ℂ) * ζ ^ 27 + ((1831 / 1764) : ℂ) * ζ ^ 28 + ((7535 / 1764) : ℂ) * ζ ^ 29 - ((163 / 252) : ℂ) * ζ ^ 30 + ((1145 / 147) : ℂ) * ζ ^ 31 + ((1033 / 196) : ℂ) * ζ ^ 32 + ((601 / 588) : ℂ) * ζ ^ 33 + ((1165 / 196) : ℂ) * ζ ^ 34 + ((285 / 98) : ℂ) * ζ ^ 35 + ((5497 / 588) : ℂ) * ζ ^ 36 + ((391 / 588) : ℂ) * ζ ^ 37 + ((1377 / 196) : ℂ) * ζ ^ 38 - ((17 / 7) : ℂ) * ζ ^ 39 + ((1777 / 196) : ℂ) * ζ ^ 40 + ((391 / 588) : ℂ) * ζ ^ 41 - ((69 / 98) : ℂ) * ζ ^ 42 - ((3575 / 294) : ℂ) * ζ ^ 43 - ((1508 / 147) : ℂ) * ζ ^ 44 - ((737 / 84) : ℂ) * ζ ^ 45 - ((69 / 98) : ℂ) * ζ ^ 46 - ((2431 / 588) : ℂ) * ζ ^ 47 + ((709 / 294) : ℂ) * ζ ^ 48 + ((601 / 147) : ℂ) * ζ ^ 49 + ((1220 / 147) : ℂ) * ζ ^ 50 - ((2431 / 588) : ℂ) * ζ ^ 51 - ((1199 / 294) : ℂ) * ζ ^ 52 - ((403 / 84) : ℂ) * ζ ^ 53 - ((319 / 42) : ℂ) * ζ ^ 54 - ((107 / 28) : ℂ) * ζ ^ 55 - ((1199 / 294) : ℂ) * ζ ^ 56 + ((197 / 196) : ℂ) * ζ ^ 57 + ((23 / 42) : ℂ) * ζ ^ 58 + ((2339 / 294) : ℂ) * ζ ^ 59 + ((1199 / 294) : ℂ) * ζ ^ 60 - ((197 / 196) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_1_3 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        1 3 =
      alternatingSixAmbientRow15TransformedGeneratorA
        1 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((1697 / 882) : ℂ) - ((6133 / 1764) : ℂ) * ζ ^ 3 - ((1697 / 882) : ℂ) * ζ ^ 4 - ((5027 / 1764) : ℂ) * ζ ^ 5 + ((4205 / 1764) : ℂ) * ζ ^ 6 + ((1951 / 441) : ℂ) * ζ ^ 8 + ((158 / 63) : ℂ) * ζ ^ 9 + ((10009 / 1764) : ℂ) * ζ ^ 10 - ((1117 / 588) : ℂ) * ζ ^ 11 - ((3229 / 588) : ℂ) * ζ ^ 13 - ((1451 / 441) : ℂ) * ζ ^ 14 - ((877 / 147) : ℂ) * ζ ^ 15 - ((1417 / 588) : ℂ) * ζ ^ 16 - ((67 / 196) : ℂ) * ζ ^ 17 - ((1213 / 441) : ℂ) * ζ ^ 18 + ((797 / 196) : ℂ) * ζ ^ 19 - ((152 / 63) : ℂ) * ζ ^ 20 + ((509 / 147) : ℂ) * ζ ^ 21 - ((4205 / 1764) : ℂ) * ζ ^ 22 + ((14195 / 1764) : ℂ) * ζ ^ 23 + ((5 / 1764) : ℂ) * ζ ^ 24 + ((12601 / 1764) : ℂ) * ζ ^ 25 - ((2125 / 882) : ℂ) * ζ ^ 26 + ((1117 / 588) : ℂ) * ζ ^ 27 - ((3986 / 441) : ℂ) * ζ ^ 28 - ((2875 / 1764) : ℂ) * ζ ^ 29 - ((2536 / 441) : ℂ) * ζ ^ 30 + ((465 / 98) : ℂ) * ζ ^ 31 + ((1417 / 588) : ℂ) * ζ ^ 32 + ((269 / 98) : ℂ) * ζ ^ 33 + ((1192 / 147) : ℂ) * ζ ^ 34 + ((5315 / 588) : ℂ) * ζ ^ 35 + ((4793 / 588) : ℂ) * ζ ^ 36 - ((1219 / 294) : ℂ) * ζ ^ 37 - ((137 / 84) : ℂ) * ζ ^ 38 - ((4759 / 588) : ℂ) * ζ ^ 39 + ((814 / 147) : ℂ) * ζ ^ 40 - ((1219 / 294) : ℂ) * ζ ^ 41 + ((5 / 196) : ℂ) * ζ ^ 42 - ((6631 / 588) : ℂ) * ζ ^ 43 - ((1297 / 588) : ℂ) * ζ ^ 44 - ((515 / 294) : ℂ) * ζ ^ 45 + ((5 / 196) : ℂ) * ζ ^ 46 - ((239 / 84) : ℂ) * ζ ^ 47 + ((85 / 42) : ℂ) * ζ ^ 48 + ((222 / 49) : ℂ) * ζ ^ 49 + ((821 / 84) : ℂ) * ζ ^ 50 - ((239 / 84) : ℂ) * ζ ^ 51 - ((844 / 147) : ℂ) * ζ ^ 52 - ((3917 / 588) : ℂ) * ζ ^ 53 - ((2881 / 294) : ℂ) * ζ ^ 54 - ((1453 / 294) : ℂ) * ζ ^ 55 - ((844 / 147) : ℂ) * ζ ^ 56 + ((67 / 196) : ℂ) * ζ ^ 57 + ((17 / 14) : ℂ) * ζ ^ 58 + ((4579 / 588) : ℂ) * ζ ^ 59 + ((844 / 147) : ℂ) * ζ ^ 60 - ((67 / 196) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_1_4 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        1 4 =
      alternatingSixAmbientRow15TransformedGeneratorA
        1 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((5697 / 7154) : ℂ) - ((14303 / 42924) : ℂ) * ζ ^ 3 + ((5697 / 7154) : ℂ) * ζ ^ 4 - ((13921 / 21462) : ℂ) * ζ ^ 5 - ((32957 / 42924) : ℂ) * ζ ^ 6 + ((17343 / 7154) : ℂ) * ζ ^ 8 + ((11573 / 7154) : ℂ) * ζ ^ 9 - ((143 / 7154) : ℂ) * ζ ^ 10 - ((35167 / 42924) : ℂ) * ζ ^ 11 + ((39895 / 21462) : ℂ) * ζ ^ 13 - ((32099 / 42924) : ℂ) * ζ ^ 14 - ((45583 / 21462) : ℂ) * ζ ^ 15 - ((63323 / 42924) : ℂ) * ζ ^ 16 + ((10399 / 10731) : ℂ) * ζ ^ 17 + ((51591 / 14308) : ℂ) * ζ ^ 18 + ((55999 / 42924) : ℂ) * ζ ^ 19 - ((3791 / 6132) : ℂ) * ζ ^ 20 - ((17509 / 10731) : ℂ) * ζ ^ 21 + ((32957 / 42924) : ℂ) * ζ ^ 22 + ((79717 / 42924) : ℂ) * ζ ^ 23 - ((6131 / 7154) : ℂ) * ζ ^ 24 - ((10334 / 3577) : ℂ) * ζ ^ 25 + ((3149 / 21462) : ℂ) * ζ ^ 26 + ((35167 / 42924) : ℂ) * ζ ^ 27 - ((185153 / 42924) : ℂ) * ζ ^ 28 - ((48901 / 10731) : ℂ) * ζ ^ 29 - ((7359 / 2044) : ℂ) * ζ ^ 30 + ((53161 / 42924) : ℂ) * ζ ^ 31 + ((63323 / 42924) : ℂ) * ζ ^ 32 + ((246097 / 42924) : ℂ) * ζ ^ 33 + ((31641 / 14308) : ℂ) * ζ ^ 34 + ((156797 / 21462) : ℂ) * ζ ^ 35 + ((62701 / 42924) : ℂ) * ζ ^ 36 + ((12769 / 3577) : ℂ) * ζ ^ 37 - ((114573 / 14308) : ℂ) * ζ ^ 38 - ((330767 / 42924) : ℂ) * ζ ^ 39 - ((356485 / 42924) : ℂ) * ζ ^ 40 + ((12769 / 3577) : ℂ) * ζ ^ 41 + ((26659 / 42924) : ℂ) * ζ ^ 42 + ((931 / 146) : ℂ) * ζ ^ 43 + ((73135 / 10731) : ℂ) * ζ ^ 44 + ((189901 / 21462) : ℂ) * ζ ^ 45 + ((26659 / 42924) : ℂ) * ζ ^ 46 - ((2999 / 7154) : ℂ) * ζ ^ 47 - ((97831 / 21462) : ℂ) * ζ ^ 48 - ((26189 / 3066) : ℂ) * ζ ^ 49 - ((228329 / 42924) : ℂ) * ζ ^ 50 - ((2999 / 7154) : ℂ) * ζ ^ 51 + ((311 / 21462) : ℂ) * ζ ^ 52 + ((6259 / 21462) : ℂ) * ζ ^ 53 + ((14405 / 3066) : ℂ) * ζ ^ 54 + ((42163 / 21462) : ℂ) * ζ ^ 55 + ((311 / 21462) : ℂ) * ζ ^ 56 - ((10399 / 10731) : ℂ) * ζ ^ 57 - ((901 / 3577) : ℂ) * ζ ^ 58 - ((2369 / 1533) : ℂ) * ζ ^ 59 - ((311 / 21462) : ℂ) * ζ ^ 60 + ((10399 / 10731) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_1_5 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        1 5 =
      alternatingSixAmbientRow15TransformedGeneratorA
        1 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((17263 / 32193) : ℂ) + ((42383 / 32193) : ℂ) * ζ ^ 3 - ((17263 / 32193) : ℂ) * ζ ^ 4 + ((128227 / 128772) : ℂ) * ζ ^ 5 - ((32062 / 32193) : ℂ) * ζ ^ 6 - ((668231 / 128772) : ℂ) * ζ ^ 8 - ((9799 / 32193) : ℂ) * ζ ^ 9 - ((101029 / 64386) : ℂ) * ζ ^ 10 + ((57959 / 21462) : ℂ) * ζ ^ 11 + ((19904 / 3577) : ℂ) * ζ ^ 13 + ((36905 / 64386) : ℂ) * ζ ^ 14 + ((18486 / 3577) : ℂ) * ζ ^ 15 - ((6357 / 7154) : ℂ) * ζ ^ 16 + ((29677 / 42924) : ℂ) * ζ ^ 17 - ((329897 / 64386) : ℂ) * ζ ^ 18 - ((52957 / 21462) : ℂ) * ζ ^ 19 - ((140489 / 128772) : ℂ) * ζ ^ 20 - ((26227 / 14308) : ℂ) * ζ ^ 21 + ((32062 / 32193) : ℂ) * ζ ^ 22 - ((44615 / 64386) : ℂ) * ζ ^ 23 + ((26063 / 128772) : ℂ) * ζ ^ 24 - ((217549 / 64386) : ℂ) * ζ ^ 25 + ((94561 / 32193) : ℂ) * ζ ^ 26 - ((57959 / 21462) : ℂ) * ζ ^ 27 + ((97645 / 18396) : ℂ) * ζ ^ 28 - ((335131 / 128772) : ℂ) * ζ ^ 29 + ((682721 / 128772) : ℂ) * ζ ^ 30 - ((245489 / 42924) : ℂ) * ζ ^ 31 + ((6357 / 7154) : ℂ) * ζ ^ 32 - ((188323 / 21462) : ℂ) * ζ ^ 33 - ((26713 / 6132) : ℂ) * ζ ^ 34 - ((31601 / 3066) : ℂ) * ζ ^ 35 + ((22543 / 6132) : ℂ) * ζ ^ 36 + ((138035 / 42924) : ℂ) * ζ ^ 37 + ((187531 / 21462) : ℂ) * ζ ^ 38 + ((428761 / 42924) : ℂ) * ζ ^ 39 + ((45180 / 3577) : ℂ) * ζ ^ 40 + ((138035 / 42924) : ℂ) * ζ ^ 41 - ((20833 / 10731) : ℂ) * ζ ^ 42 - ((99257 / 14308) : ℂ) * ζ ^ 43 - ((460643 / 42924) : ℂ) * ζ ^ 44 - ((33885 / 3577) : ℂ) * ζ ^ 45 - ((20833 / 10731) : ℂ) * ζ ^ 46 + ((129571 / 42924) : ℂ) * ζ ^ 47 + ((43153 / 14308) : ℂ) * ζ ^ 48 + ((387293 / 42924) : ℂ) * ζ ^ 49 + ((361741 / 42924) : ℂ) * ζ ^ 50 + ((129571 / 42924) : ℂ) * ζ ^ 51 - ((119659 / 42924) : ℂ) * ζ ^ 52 - ((5996 / 1533) : ℂ) * ζ ^ 53 - ((92803 / 14308) : ℂ) * ζ ^ 54 - ((8273 / 1533) : ℂ) * ζ ^ 55 - ((119659 / 42924) : ℂ) * ζ ^ 56 - ((29677 / 42924) : ℂ) * ζ ^ 57 + ((1952 / 3577) : ℂ) * ζ ^ 58 + ((102073 / 42924) : ℂ) * ζ ^ 59 + ((119659 / 42924) : ℂ) * ζ ^ 60 + ((29677 / 42924) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_2_0 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        2 0 =
      alternatingSixAmbientRow15TransformedGeneratorA
        2 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((145 / 126) : ℂ) + ((1019 / 252) : ℂ) * ζ ^ 3 + ((145 / 126) : ℂ) * ζ ^ 4 + ((10589 / 1764) : ℂ) * ζ ^ 5 - ((905 / 126) : ℂ) * ζ ^ 6 - ((1646 / 147) : ℂ) * ζ ^ 8 - ((479 / 441) : ℂ) * ζ ^ 9 - ((8215 / 588) : ℂ) * ζ ^ 10 + ((14951 / 1764) : ℂ) * ζ ^ 11 + ((723 / 28) : ℂ) * ζ ^ 13 + ((11975 / 1764) : ℂ) * ζ ^ 14 + ((21305 / 1764) : ℂ) * ζ ^ 15 - ((6721 / 1764) : ℂ) * ζ ^ 16 + ((59 / 12) : ℂ) * ζ ^ 17 - ((176 / 21) : ℂ) * ζ ^ 18 - ((353 / 98) : ℂ) * ζ ^ 19 + ((881 / 588) : ℂ) * ζ ^ 20 - ((1469 / 294) : ℂ) * ζ ^ 21 + ((905 / 126) : ℂ) * ζ ^ 22 - ((101 / 588) : ℂ) * ζ ^ 23 - ((2341 / 441) : ℂ) * ζ ^ 24 - ((11051 / 441) : ℂ) * ζ ^ 25 + ((2145 / 196) : ℂ) * ζ ^ 26 - ((14951 / 1764) : ℂ) * ζ ^ 27 + ((1850 / 441) : ℂ) * ζ ^ 28 - ((4162 / 441) : ℂ) * ζ ^ 29 + ((9197 / 882) : ℂ) * ζ ^ 30 - ((2011 / 147) : ℂ) * ζ ^ 31 + ((6721 / 1764) : ℂ) * ζ ^ 32 - ((251 / 28) : ℂ) * ζ ^ 33 - ((8143 / 588) : ℂ) * ζ ^ 34 - ((1409 / 882) : ℂ) * ζ ^ 35 + ((1713 / 196) : ℂ) * ζ ^ 36 + ((2180 / 147) : ℂ) * ζ ^ 37 - ((2621 / 441) : ℂ) * ζ ^ 38 + ((2147 / 441) : ℂ) * ζ ^ 39 - ((2083 / 882) : ℂ) * ζ ^ 40 + ((2180 / 147) : ℂ) * ζ ^ 41 - ((6635 / 1764) : ℂ) * ζ ^ 42 + ((20845 / 1764) : ℂ) * ζ ^ 43 + ((2047 / 588) : ℂ) * ζ ^ 44 + ((25331 / 1764) : ℂ) * ζ ^ 45 - ((6635 / 1764) : ℂ) * ζ ^ 46 + ((9181 / 1764) : ℂ) * ζ ^ 47 - ((18625 / 1764) : ℂ) * ζ ^ 48 - ((16799 / 1764) : ℂ) * ζ ^ 49 - ((3587 / 1764) : ℂ) * ζ ^ 50 + ((9181 / 1764) : ℂ) * ζ ^ 51 - ((2174 / 441) : ℂ) * ζ ^ 52 - ((2171 / 588) : ℂ) * ζ ^ 53 + ((5111 / 882) : ℂ) * ζ ^ 54 - ((299 / 98) : ℂ) * ζ ^ 55 - ((2174 / 441) : ℂ) * ζ ^ 56 - ((59 / 12) : ℂ) * ζ ^ 57 - ((745 / 882) : ℂ) * ζ ^ 58 - ((3799 / 1764) : ℂ) * ζ ^ 59 + ((2174 / 441) : ℂ) * ζ ^ 60 + ((59 / 12) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_2_1 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        2 1 =
      alternatingSixAmbientRow15TransformedGeneratorA
        2 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((3289 / 588) : ℂ) - ((1497 / 98) : ℂ) * ζ ^ 3 - ((3289 / 588) : ℂ) * ζ ^ 4 - ((14275 / 882) : ℂ) * ζ ^ 5 + ((10813 / 588) : ℂ) * ζ ^ 6 + ((53975 / 1764) : ℂ) * ζ ^ 8 + ((13553 / 1764) : ℂ) * ζ ^ 9 + ((69775 / 1764) : ℂ) * ζ ^ 10 - ((22489 / 1764) : ℂ) * ζ ^ 11 - ((23600 / 441) : ℂ) * ζ ^ 13 - ((9334 / 441) : ℂ) * ζ ^ 14 - ((51553 / 1764) : ℂ) * ζ ^ 15 + ((2707 / 588) : ℂ) * ζ ^ 16 - ((4999 / 588) : ℂ) * ζ ^ 17 + ((21781 / 882) : ℂ) * ζ ^ 18 + ((346 / 21) : ℂ) * ζ ^ 19 + ((1042 / 147) : ℂ) * ζ ^ 20 + ((2645 / 441) : ℂ) * ζ ^ 21 - ((10813 / 588) : ℂ) * ζ ^ 22 - ((5629 / 882) : ℂ) * ζ ^ 23 - ((487 / 196) : ℂ) * ζ ^ 24 + ((15943 / 588) : ℂ) * ζ ^ 25 - ((26407 / 882) : ℂ) * ζ ^ 26 + ((22489 / 1764) : ℂ) * ζ ^ 27 - ((17 / 126) : ℂ) * ζ ^ 28 + ((52733 / 1764) : ℂ) * ζ ^ 29 - ((1369 / 84) : ℂ) * ζ ^ 30 + ((10442 / 441) : ℂ) * ζ ^ 31 - ((2707 / 588) : ℂ) * ζ ^ 32 + ((6619 / 252) : ℂ) * ζ ^ 33 + ((40813 / 1764) : ℂ) * ζ ^ 34 + ((10025 / 588) : ℂ) * ζ ^ 35 - ((21491 / 882) : ℂ) * ζ ^ 36 - ((20287 / 882) : ℂ) * ζ ^ 37 - ((3488 / 441) : ℂ) * ζ ^ 38 - ((1585 / 84) : ℂ) * ζ ^ 39 - ((11651 / 441) : ℂ) * ζ ^ 40 - ((20287 / 882) : ℂ) * ζ ^ 41 + ((20375 / 1764) : ℂ) * ζ ^ 42 + ((337 / 196) : ℂ) * ζ ^ 43 + ((4966 / 441) : ℂ) * ζ ^ 44 + ((3067 / 588) : ℂ) * ζ ^ 45 + ((20375 / 1764) : ℂ) * ζ ^ 46 - ((19279 / 1764) : ℂ) * ζ ^ 47 - ((73 / 441) : ℂ) * ζ ^ 48 - ((28615 / 1764) : ℂ) * ζ ^ 49 - ((21691 / 882) : ℂ) * ζ ^ 50 - ((19279 / 1764) : ℂ) * ζ ^ 51 + ((34861 / 1764) : ℂ) * ζ ^ 52 + ((32251 / 1764) : ℂ) * ζ ^ 53 + ((7669 / 588) : ℂ) * ζ ^ 54 + ((9962 / 441) : ℂ) * ζ ^ 55 + ((34861 / 1764) : ℂ) * ζ ^ 56 + ((4999 / 588) : ℂ) * ζ ^ 57 - ((3485 / 1764) : ℂ) * ζ ^ 58 - ((20569 / 1764) : ℂ) * ζ ^ 59 - ((34861 / 1764) : ℂ) * ζ ^ 60 - ((4999 / 588) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_2_2 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        2 2 =
      alternatingSixAmbientRow15TransformedGeneratorA
        2 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((9119 / 1764) : ℂ) - ((270 / 49) : ℂ) * ζ ^ 3 - ((9119 / 1764) : ℂ) * ζ ^ 4 - ((106 / 9) : ℂ) * ζ ^ 5 - ((4951 / 1764) : ℂ) * ζ ^ 6 + ((502 / 63) : ℂ) * ζ ^ 8 + ((6875 / 441) : ℂ) * ζ ^ 9 + ((24499 / 1764) : ℂ) * ζ ^ 10 + ((946 / 147) : ℂ) * ζ ^ 11 - ((2435 / 882) : ℂ) * ζ ^ 13 - ((14725 / 882) : ℂ) * ζ ^ 14 - ((691 / 49) : ℂ) * ζ ^ 15 - ((781 / 294) : ℂ) * ζ ^ 16 + ((1681 / 441) : ℂ) * ζ ^ 17 + ((9823 / 882) : ℂ) * ζ ^ 18 + ((3019 / 147) : ℂ) * ζ ^ 19 + ((23953 / 1764) : ℂ) * ζ ^ 20 - ((787 / 588) : ℂ) * ζ ^ 21 + ((4951 / 1764) : ℂ) * ζ ^ 22 - ((2470 / 441) : ℂ) * ζ ^ 23 - ((28639 / 1764) : ℂ) * ζ ^ 24 - ((383 / 21) : ℂ) * ζ ^ 25 + ((2467 / 441) : ℂ) * ζ ^ 26 - ((946 / 147) : ℂ) * ζ ^ 27 + ((977 / 294) : ℂ) * ζ ^ 28 - ((3511 / 588) : ℂ) * ζ ^ 29 + ((4699 / 1764) : ℂ) * ζ ^ 30 - ((11807 / 882) : ℂ) * ζ ^ 31 + ((781 / 294) : ℂ) * ζ ^ 32 - ((1639 / 588) : ℂ) * ζ ^ 33 - ((4733 / 1764) : ℂ) * ζ ^ 34 + ((1480 / 441) : ℂ) * ζ ^ 35 + ((13499 / 1764) : ℂ) * ζ ^ 36 + ((15809 / 1764) : ℂ) * ζ ^ 37 - ((565 / 63) : ℂ) * ζ ^ 38 - ((3415 / 882) : ℂ) * ζ ^ 39 - ((496 / 147) : ℂ) * ζ ^ 40 + ((15809 / 1764) : ℂ) * ζ ^ 41 - ((1639 / 588) : ℂ) * ζ ^ 42 + ((17347 / 1764) : ℂ) * ζ ^ 43 + ((10079 / 1764) : ℂ) * ζ ^ 44 + ((1859 / 196) : ℂ) * ζ ^ 45 - ((1639 / 588) : ℂ) * ζ ^ 46 + ((6131 / 882) : ℂ) * ζ ^ 47 - ((17363 / 1764) : ℂ) * ζ ^ 48 - ((1411 / 441) : ℂ) * ζ ^ 49 - ((937 / 1764) : ℂ) * ζ ^ 50 + ((6131 / 882) : ℂ) * ζ ^ 51 - ((1259 / 252) : ℂ) * ζ ^ 52 - ((69 / 196) : ℂ) * ζ ^ 53 + ((2927 / 882) : ℂ) * ζ ^ 54 - ((9775 / 1764) : ℂ) * ζ ^ 55 - ((1259 / 252) : ℂ) * ζ ^ 56 - ((1681 / 441) : ℂ) * ζ ^ 57 - ((3053 / 882) : ℂ) * ζ ^ 58 - ((829 / 588) : ℂ) * ζ ^ 59 + ((1259 / 252) : ℂ) * ζ ^ 60 + ((1681 / 441) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_2_3 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        2 3 =
      alternatingSixAmbientRow15TransformedGeneratorA
        2 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((767 / 588) : ℂ) + ((101 / 294) : ℂ) * ζ ^ 3 - ((767 / 588) : ℂ) * ζ ^ 4 - ((184 / 49) : ℂ) * ζ ^ 5 - ((823 / 294) : ℂ) * ζ ^ 6 + ((17 / 7) : ℂ) * ζ ^ 8 + ((3403 / 588) : ℂ) * ζ ^ 9 - ((473 / 98) : ℂ) * ζ ^ 10 + ((1231 / 588) : ℂ) * ζ ^ 11 + ((797 / 84) : ℂ) * ζ ^ 13 + ((298 / 147) : ℂ) * ζ ^ 14 + ((2768 / 441) : ℂ) * ζ ^ 15 - ((929 / 196) : ℂ) * ζ ^ 16 + ((1195 / 588) : ℂ) * ζ ^ 17 - ((3937 / 882) : ℂ) * ζ ^ 18 - ((7379 / 1764) : ℂ) * ζ ^ 19 - ((3517 / 441) : ℂ) * ζ ^ 20 - ((233 / 63) : ℂ) * ζ ^ 21 + ((823 / 294) : ℂ) * ζ ^ 22 + ((4829 / 1764) : ℂ) * ζ ^ 23 + ((5707 / 1764) : ℂ) * ζ ^ 24 - ((293 / 49) : ℂ) * ζ ^ 25 + ((2977 / 588) : ℂ) * ζ ^ 26 - ((1231 / 588) : ℂ) * ζ ^ 27 + ((2903 / 1764) : ℂ) * ζ ^ 28 - ((1249 / 126) : ℂ) * ζ ^ 29 + ((1510 / 147) : ℂ) * ζ ^ 30 - ((12295 / 1764) : ℂ) * ζ ^ 31 + ((929 / 196) : ℂ) * ζ ^ 32 - ((7337 / 588) : ℂ) * ζ ^ 33 - ((6355 / 588) : ℂ) * ζ ^ 34 - ((11015 / 882) : ℂ) * ζ ^ 35 + ((10915 / 1764) : ℂ) * ζ ^ 36 + ((6847 / 882) : ℂ) * ζ ^ 37 + ((1219 / 196) : ℂ) * ζ ^ 38 + ((5707 / 588) : ℂ) * ζ ^ 39 + ((15301 / 1764) : ℂ) * ζ ^ 40 + ((6847 / 882) : ℂ) * ζ ^ 41 - ((1331 / 588) : ℂ) * ζ ^ 42 - ((12191 / 1764) : ℂ) * ζ ^ 43 - ((1759 / 147) : ℂ) * ζ ^ 44 - ((6205 / 1764) : ℂ) * ζ ^ 45 - ((1331 / 588) : ℂ) * ζ ^ 46 + ((4301 / 882) : ℂ) * ζ ^ 47 + ((127 / 294) : ℂ) * ζ ^ 48 + ((6851 / 1764) : ℂ) * ζ ^ 49 + ((907 / 588) : ℂ) * ζ ^ 50 + ((4301 / 882) : ℂ) * ζ ^ 51 - ((1277 / 882) : ℂ) * ζ ^ 52 - ((4015 / 1764) : ℂ) * ζ ^ 53 + ((106 / 147) : ℂ) * ζ ^ 54 - ((4355 / 1764) : ℂ) * ζ ^ 55 - ((1277 / 882) : ℂ) * ζ ^ 56 - ((1195 / 588) : ℂ) * ζ ^ 57 - ((415 / 441) : ℂ) * ζ ^ 58 - ((4247 / 1764) : ℂ) * ζ ^ 59 + ((1277 / 882) : ℂ) * ζ ^ 60 + ((1195 / 588) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_2_4 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        2 4 =
      alternatingSixAmbientRow15TransformedGeneratorA
        2 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((281173 / 128772) : ℂ) + ((754195 / 128772) : ℂ) * ζ ^ 3 + ((281173 / 128772) : ℂ) * ζ ^ 4 + ((392885 / 64386) : ℂ) * ζ ^ 5 - ((144842 / 32193) : ℂ) * ζ ^ 6 - ((113696 / 10731) : ℂ) * ζ ^ 8 - ((683953 / 128772) : ℂ) * ζ ^ 9 - ((129965 / 9198) : ℂ) * ζ ^ 10 + ((330259 / 128772) : ℂ) * ζ ^ 11 + ((148691 / 9198) : ℂ) * ζ ^ 13 + ((620071 / 64386) : ℂ) * ζ ^ 14 + ((2473697 / 128772) : ℂ) * ζ ^ 15 - ((159349 / 128772) : ℂ) * ζ ^ 16 + ((11313 / 14308) : ℂ) * ζ ^ 17 - ((186286 / 10731) : ℂ) * ζ ^ 18 - ((1071719 / 64386) : ℂ) * ζ ^ 19 - ((463109 / 21462) : ℂ) * ζ ^ 20 + ((61889 / 64386) : ℂ) * ζ ^ 21 + ((144842 / 32193) : ℂ) * ζ ^ 22 + ((234009 / 14308) : ℂ) * ζ ^ 23 + ((2619305 / 128772) : ℂ) * ζ ^ 24 + ((414367 / 21462) : ℂ) * ζ ^ 25 + ((104443 / 18396) : ℂ) * ζ ^ 26 - ((330259 / 128772) : ℂ) * ζ ^ 27 - ((1676537 / 128772) : ℂ) * ζ ^ 28 - ((1486663 / 64386) : ℂ) * ζ ^ 29 - ((871837 / 64386) : ℂ) * ζ ^ 30 - ((66189 / 14308) : ℂ) * ζ ^ 31 + ((159349 / 128772) : ℂ) * ζ ^ 32 + ((68221 / 32193) : ℂ) * ζ ^ 33 + ((1316039 / 128772) : ℂ) * ζ ^ 34 + ((199007 / 42924) : ℂ) * ζ ^ 35 + ((119248 / 32193) : ℂ) * ζ ^ 36 + ((2852 / 4599) : ℂ) * ζ ^ 37 + ((27221 / 64386) : ℂ) * ζ ^ 38 - ((133051 / 32193) : ℂ) * ζ ^ 39 + ((203197 / 64386) : ℂ) * ζ ^ 40 + ((2852 / 4599) : ℂ) * ζ ^ 41 - ((151733 / 128772) : ℂ) * ζ ^ 42 - ((143105 / 64386) : ℂ) * ζ ^ 43 - ((20675 / 10731) : ℂ) * ζ ^ 44 - ((481067 / 128772) : ℂ) * ζ ^ 45 - ((151733 / 128772) : ℂ) * ζ ^ 46 + ((132721 / 64386) : ℂ) * ζ ^ 47 + ((432305 / 128772) : ℂ) * ζ ^ 48 + ((12833 / 2044) : ℂ) * ζ ^ 49 + ((836911 / 128772) : ℂ) * ζ ^ 50 + ((132721 / 64386) : ℂ) * ζ ^ 51 - ((105881 / 42924) : ℂ) * ζ ^ 52 - ((423037 / 128772) : ℂ) * ζ ^ 53 - ((4693 / 882) : ℂ) * ζ ^ 54 - ((585443 / 128772) : ℂ) * ζ ^ 55 - ((105881 / 42924) : ℂ) * ζ ^ 56 - ((11313 / 14308) : ℂ) * ζ ^ 57 + ((27305 / 42924) : ℂ) * ζ ^ 58 + ((106667 / 42924) : ℂ) * ζ ^ 59 + ((105881 / 42924) : ℂ) * ζ ^ 60 + ((11313 / 14308) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_2_5 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        2 5 =
      alternatingSixAmbientRow15TransformedGeneratorA
        2 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((163337 / 42924) : ℂ) - ((849173 / 128772) : ℂ) * ζ ^ 3 - ((163337 / 42924) : ℂ) * ζ ^ 4 - ((210359 / 21462) : ℂ) * ζ ^ 5 + ((129509 / 32193) : ℂ) * ζ ^ 6 + ((482494 / 32193) : ℂ) * ζ ^ 8 + ((578005 / 64386) : ℂ) * ζ ^ 9 + ((2822425 / 128772) : ℂ) * ζ ^ 10 - ((55105 / 14308) : ℂ) * ζ ^ 11 - ((815714 / 32193) : ℂ) * ζ ^ 13 - ((2304389 / 128772) : ℂ) * ζ ^ 14 - ((37385 / 1314) : ℂ) * ζ ^ 15 + ((58703 / 21462) : ℂ) * ζ ^ 16 - ((26536 / 32193) : ℂ) * ζ ^ 17 + ((552523 / 21462) : ℂ) * ζ ^ 18 + ((3167785 / 128772) : ℂ) * ζ ^ 19 + ((924874 / 32193) : ℂ) * ζ ^ 20 - ((30785 / 128772) : ℂ) * ζ ^ 21 - ((129509 / 32193) : ℂ) * ζ ^ 22 - ((310091 / 14308) : ℂ) * ζ ^ 23 - ((1673639 / 64386) : ℂ) * ζ ^ 24 - ((173669 / 7154) : ℂ) * ζ ^ 25 - ((242303 / 42924) : ℂ) * ζ ^ 26 + ((55105 / 14308) : ℂ) * ζ ^ 27 + ((2175479 / 128772) : ℂ) * ζ ^ 28 + ((3732121 / 128772) : ℂ) * ζ ^ 29 + ((708503 / 42924) : ℂ) * ζ ^ 30 + ((202193 / 42924) : ℂ) * ζ ^ 31 - ((58703 / 21462) : ℂ) * ζ ^ 32 - ((393583 / 64386) : ℂ) * ζ ^ 33 - ((129739 / 9198) : ℂ) * ζ ^ 34 - ((159675 / 14308) : ℂ) * ζ ^ 35 - ((7513 / 1533) : ℂ) * ζ ^ 36 - ((2881 / 2044) : ℂ) * ζ ^ 37 + ((231547 / 64386) : ℂ) * ζ ^ 38 + ((12521 / 1533) : ℂ) * ζ ^ 39 + ((249575 / 64386) : ℂ) * ζ ^ 40 - ((2881 / 2044) : ℂ) * ζ ^ 41 + ((29839 / 18396) : ℂ) * ζ ^ 42 - ((311383 / 128772) : ℂ) * ζ ^ 43 - ((212903 / 64386) : ℂ) * ζ ^ 44 - ((84907 / 42924) : ℂ) * ζ ^ 45 + ((29839 / 18396) : ℂ) * ζ ^ 46 - ((18439 / 21462) : ℂ) * ζ ^ 47 + ((77603 / 64386) : ℂ) * ζ ^ 48 + ((416 / 4599) : ℂ) * ζ ^ 49 - ((61267 / 128772) : ℂ) * ζ ^ 50 - ((18439 / 21462) : ℂ) * ζ ^ 51 + ((15493 / 7154) : ℂ) * ζ ^ 52 - ((995 / 21462) : ℂ) * ζ ^ 53 - ((337 / 294) : ℂ) * ζ ^ 54 + ((97679 / 64386) : ℂ) * ζ ^ 55 + ((15493 / 7154) : ℂ) * ζ ^ 56 + ((26536 / 32193) : ℂ) * ζ ^ 57 + ((35515 / 64386) : ℂ) * ζ ^ 58 - ((21181 / 32193) : ℂ) * ζ ^ 59 - ((15493 / 7154) : ℂ) * ζ ^ 60 - ((26536 / 32193) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_3_0 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        3 0 =
      alternatingSixAmbientRow15TransformedGeneratorA
        3 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((718 / 441) : ℂ) + ((16271 / 1764) : ℂ) * ζ ^ 3 - ((718 / 441) : ℂ) * ζ ^ 4 - ((3049 / 441) : ℂ) * ζ ^ 5 - ((26149 / 1764) : ℂ) * ζ ^ 6 - ((6679 / 588) : ℂ) * ζ ^ 8 + ((27007 / 1764) : ℂ) * ζ ^ 9 + ((758 / 147) : ℂ) * ζ ^ 10 + ((11365 / 882) : ℂ) * ζ ^ 11 + ((11341 / 588) : ℂ) * ζ ^ 13 - ((5035 / 252) : ℂ) * ζ ^ 14 - ((4903 / 441) : ℂ) * ζ ^ 15 - ((11029 / 1764) : ℂ) * ζ ^ 16 + ((4937 / 588) : ℂ) * ζ ^ 17 + ((1444 / 147) : ℂ) * ζ ^ 18 + ((7057 / 294) : ℂ) * ζ ^ 19 + ((8825 / 588) : ℂ) * ζ ^ 20 - ((3979 / 588) : ℂ) * ζ ^ 21 + ((26149 / 1764) : ℂ) * ζ ^ 22 - ((9397 / 588) : ℂ) * ζ ^ 23 - ((9376 / 441) : ℂ) * ζ ^ 24 - ((52781 / 1764) : ℂ) * ζ ^ 25 + ((4271 / 196) : ℂ) * ζ ^ 26 - ((11365 / 882) : ℂ) * ζ ^ 27 + ((17189 / 1764) : ℂ) * ζ ^ 28 - ((24011 / 882) : ℂ) * ζ ^ 29 - ((13235 / 1764) : ℂ) * ζ ^ 30 - ((16615 / 588) : ℂ) * ζ ^ 31 + ((11029 / 1764) : ℂ) * ζ ^ 32 - ((8305 / 588) : ℂ) * ζ ^ 33 - ((52 / 147) : ℂ) * ζ ^ 34 + ((7037 / 1764) : ℂ) * ζ ^ 35 + ((2461 / 98) : ℂ) * ζ ^ 36 + ((1979 / 84) : ℂ) * ζ ^ 37 - ((18149 / 1764) : ℂ) * ζ ^ 38 - ((5711 / 882) : ℂ) * ζ ^ 39 + ((4049 / 882) : ℂ) * ζ ^ 40 + ((1979 / 84) : ℂ) * ζ ^ 41 - ((6145 / 882) : ℂ) * ζ ^ 42 + ((2927 / 126) : ℂ) * ζ ^ 43 + ((2357 / 294) : ℂ) * ζ ^ 44 + ((15311 / 1764) : ℂ) * ζ ^ 45 - ((6145 / 882) : ℂ) * ζ ^ 46 + ((27115 / 1764) : ℂ) * ζ ^ 47 - ((40393 / 1764) : ℂ) * ζ ^ 48 + ((1187 / 882) : ℂ) * ζ ^ 49 + ((18869 / 882) : ℂ) * ζ ^ 50 + ((27115 / 1764) : ℂ) * ζ ^ 51 - ((33269 / 1764) : ℂ) * ζ ^ 52 - ((1066 / 147) : ℂ) * ζ ^ 53 - ((6362 / 441) : ℂ) * ζ ^ 54 - ((3770 / 147) : ℂ) * ζ ^ 55 - ((33269 / 1764) : ℂ) * ζ ^ 56 - ((4937 / 588) : ℂ) * ζ ^ 57 - ((5555 / 1764) : ℂ) * ζ ^ 58 + ((18125 / 1764) : ℂ) * ζ ^ 59 + ((33269 / 1764) : ℂ) * ζ ^ 60 + ((4937 / 588) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_3_1 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        3 1 =
      alternatingSixAmbientRow15TransformedGeneratorA
        3 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((73 / 21) : ℂ) + ((635 / 147) : ℂ) * ζ ^ 3 + ((73 / 21) : ℂ) * ζ ^ 4 + ((31195 / 1764) : ℂ) * ζ ^ 5 - ((337 / 98) : ℂ) * ζ ^ 6 - ((13757 / 882) : ℂ) * ζ ^ 8 - ((32089 / 1764) : ℂ) * ζ ^ 9 - ((77249 / 1764) : ℂ) * ζ ^ 10 + ((836 / 441) : ℂ) * ζ ^ 11 + ((30857 / 882) : ℂ) * ζ ^ 13 + ((10169 / 252) : ℂ) * ζ ^ 14 + ((93161 / 1764) : ℂ) * ζ ^ 15 - ((911 / 588) : ℂ) * ζ ^ 16 - ((149 / 294) : ℂ) * ζ ^ 17 - ((19144 / 441) : ℂ) * ζ ^ 18 - ((611 / 12) : ℂ) * ζ ^ 19 - ((29147 / 588) : ℂ) * ζ ^ 20 - ((1711 / 1764) : ℂ) * ζ ^ 21 + ((337 / 98) : ℂ) * ζ ^ 22 + ((9013 / 252) : ℂ) * ζ ^ 23 + ((2353 / 49) : ℂ) * ζ ^ 24 + ((4372 / 147) : ℂ) * ζ ^ 25 + ((2749 / 441) : ℂ) * ζ ^ 26 - ((836 / 441) : ℂ) * ζ ^ 27 - ((34849 / 1764) : ℂ) * ζ ^ 28 - ((6973 / 252) : ℂ) * ζ ^ 29 - ((379 / 98) : ℂ) * ζ ^ 30 - ((31 / 441) : ℂ) * ζ ^ 31 + ((911 / 588) : ℂ) * ζ ^ 32 + ((12409 / 1764) : ℂ) * ζ ^ 33 + ((2843 / 882) : ℂ) * ζ ^ 34 - ((353 / 49) : ℂ) * ζ ^ 35 - ((3340 / 441) : ℂ) * ζ ^ 36 - ((11 / 252) : ℂ) * ζ ^ 37 + ((8053 / 1764) : ℂ) * ζ ^ 38 + ((1606 / 147) : ℂ) * ζ ^ 39 + ((565 / 1764) : ℂ) * ζ ^ 40 - ((11 / 252) : ℂ) * ζ ^ 41 - ((2465 / 882) : ℂ) * ζ ^ 42 - ((5339 / 588) : ℂ) * ζ ^ 43 - ((19391 / 1764) : ℂ) * ζ ^ 44 + ((1223 / 588) : ℂ) * ζ ^ 45 - ((2465 / 882) : ℂ) * ζ ^ 46 - ((115 / 63) : ℂ) * ζ ^ 47 + ((2921 / 441) : ℂ) * ζ ^ 48 - ((256 / 63) : ℂ) * ζ ^ 49 - ((6674 / 441) : ℂ) * ζ ^ 50 - ((115 / 63) : ℂ) * ζ ^ 51 + ((2299 / 252) : ℂ) * ζ ^ 52 + ((9685 / 1764) : ℂ) * ζ ^ 53 + ((251 / 14) : ℂ) * ζ ^ 54 + ((7079 / 441) : ℂ) * ζ ^ 55 + ((2299 / 252) : ℂ) * ζ ^ 56 + ((149 / 294) : ℂ) * ζ ^ 57 - ((7001 / 1764) : ℂ) * ζ ^ 58 - ((6274 / 441) : ℂ) * ζ ^ 59 - ((2299 / 252) : ℂ) * ζ ^ 60 - ((149 / 294) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_3_2 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        3 2 =
      alternatingSixAmbientRow15TransformedGeneratorA
        3 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((17191 / 1764) : ℂ) + ((9857 / 588) : ℂ) * ζ ^ 3 + ((17191 / 1764) : ℂ) * ζ ^ 4 + ((9503 / 441) : ℂ) * ζ ^ 5 - ((58 / 9) : ℂ) * ζ ^ 6 - ((48101 / 1764) : ℂ) * ζ ^ 8 - ((5941 / 252) : ℂ) * ζ ^ 9 - ((48779 / 1764) : ℂ) * ζ ^ 10 - ((69 / 196) : ℂ) * ζ ^ 11 + ((21377 / 1764) : ℂ) * ζ ^ 13 + ((37411 / 1764) : ℂ) * ζ ^ 14 + ((12793 / 588) : ℂ) * ζ ^ 15 + ((6547 / 588) : ℂ) * ζ ^ 16 - ((3575 / 1764) : ℂ) * ζ ^ 17 - ((580 / 63) : ℂ) * ζ ^ 18 - ((3250 / 147) : ℂ) * ζ ^ 19 - ((9215 / 1764) : ℂ) * ζ ^ 20 + ((1091 / 196) : ℂ) * ζ ^ 21 + ((58 / 9) : ℂ) * ζ ^ 22 + ((1247 / 1764) : ℂ) * ζ ^ 23 + ((7214 / 441) : ℂ) * ζ ^ 24 + ((799 / 98) : ℂ) * ζ ^ 25 + ((4775 / 882) : ℂ) * ζ ^ 26 + ((69 / 196) : ℂ) * ζ ^ 27 + ((2215 / 196) : ℂ) * ζ ^ 28 + ((5629 / 588) : ℂ) * ζ ^ 29 - ((1661 / 1764) : ℂ) * ζ ^ 30 - ((520 / 441) : ℂ) * ζ ^ 31 - ((6547 / 588) : ℂ) * ζ ^ 32 - ((3139 / 588) : ℂ) * ζ ^ 33 - ((11525 / 1764) : ℂ) * ζ ^ 34 + ((3989 / 882) : ℂ) * ζ ^ 35 - ((5263 / 252) : ℂ) * ζ ^ 36 - ((16969 / 1764) : ℂ) * ζ ^ 37 - ((22297 / 1764) : ℂ) * ζ ^ 38 - ((2825 / 441) : ℂ) * ζ ^ 39 - ((10789 / 588) : ℂ) * ζ ^ 40 - ((16969 / 1764) : ℂ) * ζ ^ 41 + ((101 / 98) : ℂ) * ζ ^ 42 + ((18353 / 882) : ℂ) * ζ ^ 43 + ((8702 / 441) : ℂ) * ζ ^ 44 + ((11321 / 588) : ℂ) * ζ ^ 45 + ((101 / 98) : ℂ) * ζ ^ 46 + ((2701 / 1764) : ℂ) * ζ ^ 47 - ((13873 / 882) : ℂ) * ζ ^ 48 - ((15647 / 882) : ℂ) * ζ ^ 49 - ((8014 / 441) : ℂ) * ζ ^ 50 + ((2701 / 1764) : ℂ) * ζ ^ 51 + ((4300 / 441) : ℂ) * ζ ^ 52 + ((3947 / 196) : ℂ) * ζ ^ 53 + ((15119 / 882) : ℂ) * ζ ^ 54 + ((20345 / 1764) : ℂ) * ζ ^ 55 + ((4300 / 441) : ℂ) * ζ ^ 56 + ((3575 / 1764) : ℂ) * ζ ^ 57 - ((3181 / 441) : ℂ) * ζ ^ 58 - ((3841 / 294) : ℂ) * ζ ^ 59 - ((4300 / 441) : ℂ) * ζ ^ 60 - ((3575 / 1764) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_3_3 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        3 3 =
      alternatingSixAmbientRow15TransformedGeneratorA
        3 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((613 / 98) : ℂ) + ((1515 / 196) : ℂ) * ζ ^ 3 + ((613 / 98) : ℂ) * ζ ^ 4 + ((8705 / 588) : ℂ) * ζ ^ 5 - ((139 / 196) : ℂ) * ζ ^ 6 - ((2924 / 147) : ℂ) * ζ ^ 8 - ((2389 / 147) : ℂ) * ζ ^ 9 - ((8879 / 588) : ℂ) * ζ ^ 10 + ((853 / 588) : ℂ) * ζ ^ 11 + ((6047 / 588) : ℂ) * ζ ^ 13 + ((4231 / 294) : ℂ) * ζ ^ 14 + ((4418 / 441) : ℂ) * ζ ^ 15 + ((1723 / 196) : ℂ) * ζ ^ 16 - ((851 / 588) : ℂ) * ζ ^ 17 + ((193 / 441) : ℂ) * ζ ^ 18 - ((2159 / 252) : ℂ) * ζ ^ 19 + ((5897 / 441) : ℂ) * ζ ^ 20 - ((1445 / 441) : ℂ) * ζ ^ 21 + ((139 / 196) : ℂ) * ζ ^ 22 - ((30691 / 1764) : ℂ) * ζ ^ 23 - ((8081 / 1764) : ℂ) * ζ ^ 24 - ((11927 / 588) : ℂ) * ζ ^ 25 - ((37 / 147) : ℂ) * ζ ^ 26 - ((853 / 588) : ℂ) * ζ ^ 27 + ((21985 / 882) : ℂ) * ζ ^ 28 + ((45319 / 1764) : ℂ) * ζ ^ 29 + ((2594 / 147) : ℂ) * ζ ^ 30 - ((1763 / 882) : ℂ) * ζ ^ 31 - ((1723 / 196) : ℂ) * ζ ^ 32 - ((1445 / 98) : ℂ) * ζ ^ 33 - ((1893 / 98) : ℂ) * ζ ^ 34 - ((12799 / 1764) : ℂ) * ζ ^ 35 - ((31883 / 1764) : ℂ) * ζ ^ 36 + ((337 / 882) : ℂ) * ζ ^ 37 - ((603 / 196) : ℂ) * ζ ^ 38 + ((1599 / 196) : ℂ) * ζ ^ 39 - ((14221 / 882) : ℂ) * ζ ^ 40 + ((337 / 882) : ℂ) * ζ ^ 41 + ((565 / 588) : ℂ) * ζ ^ 42 + ((38557 / 1764) : ℂ) * ζ ^ 43 + ((1313 / 84) : ℂ) * ζ ^ 44 + ((18577 / 882) : ℂ) * ζ ^ 45 + ((565 / 588) : ℂ) * ζ ^ 46 + ((967 / 1764) : ℂ) * ζ ^ 47 - ((3175 / 147) : ℂ) * ζ ^ 48 - ((12010 / 441) : ℂ) * ζ ^ 49 - ((4913 / 196) : ℂ) * ζ ^ 50 + ((967 / 1764) : ℂ) * ζ ^ 51 + ((4094 / 441) : ℂ) * ζ ^ 52 + ((42887 / 1764) : ℂ) * ζ ^ 53 + ((7087 / 294) : ℂ) * ζ ^ 54 + ((13655 / 882) : ℂ) * ζ ^ 55 + ((4094 / 441) : ℂ) * ζ ^ 56 + ((851 / 588) : ℂ) * ζ ^ 57 - ((8963 / 882) : ℂ) * ζ ^ 58 - ((28277 / 1764) : ℂ) * ζ ^ 59 - ((4094 / 441) : ℂ) * ζ ^ 60 - ((851 / 588) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_3_4 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        3 4 =
      alternatingSixAmbientRow15TransformedGeneratorA
        3 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((158917 / 64386) : ℂ) - ((824093 / 128772) : ℂ) * ζ ^ 3 - ((158917 / 64386) : ℂ) * ζ ^ 4 - ((4757 / 4599) : ℂ) * ζ ^ 5 + ((894937 / 128772) : ℂ) * ζ ^ 6 + ((57261 / 7154) : ℂ) * ζ ^ 8 - ((90695 / 64386) : ℂ) * ζ ^ 9 + ((298223 / 32193) : ℂ) * ζ ^ 10 - ((441827 / 128772) : ℂ) * ζ ^ 11 - ((982195 / 64386) : ℂ) * ζ ^ 13 - ((42565 / 18396) : ℂ) * ζ ^ 14 - ((541061 / 64386) : ℂ) * ζ ^ 15 + ((558071 / 128772) : ℂ) * ζ ^ 16 - ((17477 / 7154) : ℂ) * ζ ^ 17 + ((403465 / 42924) : ℂ) * ζ ^ 18 + ((640295 / 128772) : ℂ) * ζ ^ 19 + ((583169 / 42924) : ℂ) * ζ ^ 20 - ((52921 / 64386) : ℂ) * ζ ^ 21 - ((894937 / 128772) : ℂ) * ζ ^ 22 - ((11867 / 876) : ℂ) * ζ ^ 23 - ((297859 / 32193) : ℂ) * ζ ^ 24 - ((93707 / 7154) : ℂ) * ζ ^ 25 - ((451309 / 64386) : ℂ) * ζ ^ 26 + ((441827 / 128772) : ℂ) * ζ ^ 27 + ((2095717 / 128772) : ℂ) * ζ ^ 28 + ((867100 / 32193) : ℂ) * ζ ^ 29 + ((3273265 / 128772) : ℂ) * ζ ^ 30 + ((1055 / 196) : ℂ) * ζ ^ 31 - ((558071 / 128772) : ℂ) * ζ ^ 32 - ((2015873 / 128772) : ℂ) * ζ ^ 33 - ((2386009 / 128772) : ℂ) * ζ ^ 34 - ((78317 / 3066) : ℂ) * ζ ^ 35 - ((917093 / 128772) : ℂ) * ζ ^ 36 - ((261665 / 64386) : ℂ) * ζ ^ 37 + ((433339 / 18396) : ℂ) * ζ ^ 38 + ((442685 / 18396) : ℂ) * ζ ^ 39 + ((3051227 / 128772) : ℂ) * ζ ^ 40 - ((261665 / 64386) : ℂ) * ζ ^ 41 + ((7681 / 128772) : ℂ) * ζ ^ 42 - ((719038 / 32193) : ℂ) * ζ ^ 43 - ((67909 / 3066) : ℂ) * ζ ^ 44 - ((189199 / 9198) : ℂ) * ζ ^ 45 + ((7681 / 128772) : ℂ) * ζ ^ 46 - ((62827 / 32193) : ℂ) * ζ ^ 47 + ((549095 / 32193) : ℂ) * ζ ^ 48 + ((22783 / 1533) : ℂ) * ζ ^ 49 + ((834205 / 128772) : ℂ) * ζ ^ 50 - ((62827 / 32193) : ℂ) * ζ ^ 51 + ((59837 / 21462) : ℂ) * ζ ^ 52 - ((294167 / 64386) : ℂ) * ζ ^ 53 - ((420943 / 64386) : ℂ) * ζ ^ 54 + ((47063 / 64386) : ℂ) * ζ ^ 55 + ((59837 / 21462) : ℂ) * ζ ^ 56 + ((17477 / 7154) : ℂ) * ζ ^ 57 + ((3407 / 1533) : ℂ) * ζ ^ 58 + ((26197 / 21462) : ℂ) * ζ ^ 59 - ((59837 / 21462) : ℂ) * ζ ^ 60 - ((17477 / 7154) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_3_5 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        3 5 =
      alternatingSixAmbientRow15TransformedGeneratorA
        3 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((7793 / 3577) : ℂ) + ((158548 / 32193) : ℂ) * ζ ^ 3 + ((7793 / 3577) : ℂ) * ζ ^ 4 + ((140983 / 42924) : ℂ) * ζ ^ 5 - ((187949 / 64386) : ℂ) * ζ ^ 6 - ((479333 / 128772) : ℂ) * ζ ^ 8 - ((33161 / 9198) : ℂ) * ζ ^ 9 - ((309299 / 32193) : ℂ) * ζ ^ 10 - ((18497 / 10731) : ℂ) * ζ ^ 11 + ((56135 / 9198) : ℂ) * ζ ^ 13 + ((430649 / 64386) : ℂ) * ζ ^ 14 + ((247337 / 32193) : ℂ) * ζ ^ 15 - ((28573 / 21462) : ℂ) * ζ ^ 16 - ((41305 / 128772) : ℂ) * ζ ^ 17 - ((175103 / 21462) : ℂ) * ζ ^ 18 - ((302828 / 32193) : ℂ) * ζ ^ 19 - ((1760891 / 128772) : ℂ) * ζ ^ 20 + ((350701 / 128772) : ℂ) * ζ ^ 21 + ((187949 / 64386) : ℂ) * ζ ^ 22 + ((138338 / 10731) : ℂ) * ζ ^ 23 + ((1589453 / 128772) : ℂ) * ζ ^ 24 + ((69379 / 3066) : ℂ) * ζ ^ 25 - ((377 / 7154) : ℂ) * ζ ^ 26 + ((18497 / 10731) : ℂ) * ζ ^ 27 - ((2747911 / 128772) : ℂ) * ζ ^ 28 - ((2315387 / 128772) : ℂ) * ζ ^ 29 - ((448017 / 14308) : ℂ) * ζ ^ 30 + ((3817 / 588) : ℂ) * ζ ^ 31 + ((28573 / 21462) : ℂ) * ζ ^ 32 + ((946693 / 32193) : ℂ) * ζ ^ 33 + ((467653 / 18396) : ℂ) * ζ ^ 34 + ((404084 / 10731) : ℂ) * ζ ^ 35 - ((15593 / 6132) : ℂ) * ζ ^ 36 - ((144437 / 42924) : ℂ) * ζ ^ 37 - ((1068436 / 32193) : ℂ) * ζ ^ 38 - ((1485671 / 42924) : ℂ) * ζ ^ 39 - ((181220 / 4599) : ℂ) * ζ ^ 40 - ((144437 / 42924) : ℂ) * ζ ^ 41 + ((95671 / 32193) : ℂ) * ζ ^ 42 + ((3537707 / 128772) : ℂ) * ζ ^ 43 + ((4403831 / 128772) : ℂ) * ζ ^ 44 + ((624149 / 21462) : ℂ) * ζ ^ 45 + ((95671 / 32193) : ℂ) * ζ ^ 46 - ((204653 / 42924) : ℂ) * ζ ^ 47 - ((2207825 / 128772) : ℂ) * ζ ^ 48 - ((3476803 / 128772) : ℂ) * ζ ^ 49 - ((2678131 / 128772) : ℂ) * ζ ^ 50 - ((204653 / 42924) : ℂ) * ζ ^ 51 + ((166297 / 42924) : ℂ) * ζ ^ 52 + ((39353 / 3577) : ℂ) * ζ ^ 53 + ((109307 / 6132) : ℂ) * ζ ^ 54 + ((751127 / 64386) : ℂ) * ζ ^ 55 + ((166297 / 42924) : ℂ) * ζ ^ 56 + ((41305 / 128772) : ℂ) * ζ ^ 57 - ((114082 / 32193) : ℂ) * ζ ^ 58 - ((888295 / 128772) : ℂ) * ζ ^ 59 - ((166297 / 42924) : ℂ) * ζ ^ 60 - ((41305 / 128772) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_4_0 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        4 0 =
      alternatingSixAmbientRow15TransformedGeneratorA
        4 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((953 / 1764) : ℂ) - ((5681 / 441) : ℂ) * ζ ^ 3 - ((953 / 1764) : ℂ) * ζ ^ 4 + ((3011 / 882) : ℂ) * ζ ^ 5 + ((37609 / 1764) : ℂ) * ζ ^ 6 + ((6575 / 588) : ℂ) * ζ ^ 8 - ((2497 / 441) : ℂ) * ζ ^ 9 + ((515 / 98) : ℂ) * ζ ^ 10 - ((14159 / 1764) : ℂ) * ζ ^ 11 - ((503 / 147) : ℂ) * ζ ^ 13 + ((28339 / 1764) : ℂ) * ζ ^ 14 + ((5023 / 441) : ℂ) * ζ ^ 15 + ((16369 / 1764) : ℂ) * ζ ^ 16 - ((661 / 294) : ℂ) * ζ ^ 17 - ((674 / 49) : ℂ) * ζ ^ 18 - ((233 / 12) : ℂ) * ζ ^ 19 - ((1217 / 147) : ℂ) * ζ ^ 20 - ((5027 / 588) : ℂ) * ζ ^ 21 - ((37609 / 1764) : ℂ) * ζ ^ 22 + ((3226 / 147) : ℂ) * ζ ^ 23 + ((30973 / 1764) : ℂ) * ζ ^ 24 - ((2591 / 882) : ℂ) * ζ ^ 25 - ((3131 / 98) : ℂ) * ζ ^ 26 + ((14159 / 1764) : ℂ) * ζ ^ 27 - ((4513 / 882) : ℂ) * ζ ^ 28 + ((13897 / 1764) : ℂ) * ζ ^ 29 + ((14753 / 1764) : ℂ) * ζ ^ 30 + ((1811 / 294) : ℂ) * ζ ^ 31 - ((16369 / 1764) : ℂ) * ζ ^ 32 + ((5735 / 588) : ℂ) * ζ ^ 33 + ((1369 / 588) : ℂ) * ζ ^ 34 - ((3209 / 252) : ℂ) * ζ ^ 35 - ((369 / 14) : ℂ) * ζ ^ 36 + ((2383 / 588) : ℂ) * ζ ^ 37 + ((21089 / 1764) : ℂ) * ζ ^ 38 + ((5011 / 1764) : ℂ) * ζ ^ 39 - ((4240 / 441) : ℂ) * ζ ^ 40 + ((2383 / 588) : ℂ) * ζ ^ 41 + ((18749 / 1764) : ℂ) * ζ ^ 42 - ((29353 / 1764) : ℂ) * ζ ^ 43 + ((89 / 49) : ℂ) * ζ ^ 44 - ((4049 / 1764) : ℂ) * ζ ^ 45 + ((18749 / 1764) : ℂ) * ζ ^ 46 + ((3293 / 1764) : ℂ) * ζ ^ 47 + ((15641 / 882) : ℂ) * ζ ^ 48 - ((4741 / 441) : ℂ) * ζ ^ 49 - ((34393 / 1764) : ℂ) * ζ ^ 50 + ((3293 / 1764) : ℂ) * ζ ^ 51 + ((30125 / 1764) : ℂ) * ζ ^ 52 - ((985 / 147) : ℂ) * ζ ^ 53 + ((3911 / 441) : ℂ) * ζ ^ 54 + ((1355 / 147) : ℂ) * ζ ^ 55 + ((30125 / 1764) : ℂ) * ζ ^ 56 + ((661 / 294) : ℂ) * ζ ^ 57 + ((409 / 126) : ℂ) * ζ ^ 58 - ((19553 / 1764) : ℂ) * ζ ^ 59 - ((30125 / 1764) : ℂ) * ζ ^ 60 - ((661 / 294) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_4_1 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        4 1 =
      alternatingSixAmbientRow15TransformedGeneratorA
        4 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((841 / 294) : ℂ) + ((5489 / 588) : ℂ) * ζ ^ 3 + ((841 / 294) : ℂ) * ζ ^ 4 - ((4255 / 441) : ℂ) * ζ ^ 5 - ((44 / 7) : ℂ) * ζ ^ 6 + ((11603 / 882) : ℂ) * ζ ^ 8 + ((2026 / 441) : ℂ) * ζ ^ 9 + ((39497 / 1764) : ℂ) * ζ ^ 10 - ((2507 / 441) : ℂ) * ζ ^ 11 - ((15628 / 441) : ℂ) * ζ ^ 13 - ((50585 / 1764) : ℂ) * ζ ^ 14 - ((38509 / 882) : ℂ) * ζ ^ 15 - ((3655 / 588) : ℂ) * ζ ^ 16 - ((743 / 147) : ℂ) * ζ ^ 17 + ((53113 / 1764) : ℂ) * ζ ^ 18 + ((1595 / 42) : ℂ) * ζ ^ 19 + ((5475 / 196) : ℂ) * ζ ^ 20 + ((17599 / 1764) : ℂ) * ζ ^ 21 + ((44 / 7) : ℂ) * ζ ^ 22 - ((62731 / 1764) : ℂ) * ζ ^ 23 - ((5020 / 147) : ℂ) * ζ ^ 24 + ((1459 / 196) : ℂ) * ζ ^ 25 + ((18233 / 1764) : ℂ) * ζ ^ 26 + ((2507 / 441) : ℂ) * ζ ^ 27 + ((8261 / 882) : ℂ) * ζ ^ 28 + ((14491 / 441) : ℂ) * ζ ^ 29 + ((2699 / 588) : ℂ) * ζ ^ 30 + ((11651 / 882) : ℂ) * ζ ^ 31 + ((3655 / 588) : ℂ) * ζ ^ 32 - ((7781 / 882) : ℂ) * ζ ^ 33 - ((430 / 63) : ℂ) * ζ ^ 34 + ((3799 / 588) : ℂ) * ζ ^ 35 + ((11771 / 882) : ℂ) * ζ ^ 36 - ((35431 / 1764) : ℂ) * ζ ^ 37 - ((6241 / 1764) : ℂ) * ζ ^ 38 - ((2717 / 588) : ℂ) * ζ ^ 39 + ((3463 / 882) : ℂ) * ζ ^ 40 - ((35431 / 1764) : ℂ) * ζ ^ 41 - ((7145 / 1764) : ℂ) * ζ ^ 42 + ((34 / 7) : ℂ) * ζ ^ 43 - ((2657 / 882) : ℂ) * ζ ^ 44 - ((2315 / 147) : ℂ) * ζ ^ 45 - ((7145 / 1764) : ℂ) * ζ ^ 46 - ((6637 / 882) : ℂ) * ζ ^ 47 - ((209 / 1764) : ℂ) * ζ ^ 48 + ((27547 / 1764) : ℂ) * ζ ^ 49 + ((10039 / 882) : ℂ) * ζ ^ 50 - ((6637 / 882) : ℂ) * ζ ^ 51 - ((12577 / 1764) : ℂ) * ζ ^ 52 + ((5864 / 441) : ℂ) * ζ ^ 53 - ((1437 / 196) : ℂ) * ζ ^ 54 - ((3665 / 441) : ℂ) * ζ ^ 55 - ((12577 / 1764) : ℂ) * ζ ^ 56 + ((743 / 147) : ℂ) * ζ ^ 57 + ((10547 / 1764) : ℂ) * ζ ^ 58 + ((13967 / 882) : ℂ) * ζ ^ 59 + ((12577 / 1764) : ℂ) * ζ ^ 60 - ((743 / 147) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_4_2 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        4 2 =
      alternatingSixAmbientRow15TransformedGeneratorA
        4 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((605 / 126) : ℂ) - ((4673 / 294) : ℂ) * ζ ^ 3 - ((605 / 126) : ℂ) * ζ ^ 4 - ((24737 / 1764) : ℂ) * ζ ^ 5 + ((15235 / 1764) : ℂ) * ζ ^ 6 + ((11483 / 441) : ℂ) * ζ ^ 8 + ((29821 / 1764) : ℂ) * ζ ^ 9 + ((1891 / 126) : ℂ) * ζ ^ 10 + ((530 / 147) : ℂ) * ζ ^ 11 - ((20 / 9) : ℂ) * ζ ^ 13 - ((11239 / 1764) : ℂ) * ζ ^ 14 - ((1739 / 294) : ℂ) * ζ ^ 15 - ((793 / 147) : ℂ) * ζ ^ 16 + ((1271 / 441) : ℂ) * ζ ^ 17 + ((11593 / 1764) : ℂ) * ζ ^ 18 + ((933 / 98) : ℂ) * ζ ^ 19 + ((131 / 36) : ℂ) * ζ ^ 20 - ((3091 / 588) : ℂ) * ζ ^ 21 - ((15235 / 1764) : ℂ) * ζ ^ 22 + ((4051 / 1764) : ℂ) * ζ ^ 23 - ((15935 / 1764) : ℂ) * ζ ^ 24 - ((1394 / 147) : ℂ) * ζ ^ 25 - ((19519 / 1764) : ℂ) * ζ ^ 26 - ((530 / 147) : ℂ) * ζ ^ 27 - ((2654 / 147) : ℂ) * ζ ^ 28 - ((2561 / 196) : ℂ) * ζ ^ 29 + ((12323 / 1764) : ℂ) * ζ ^ 30 - ((1952 / 441) : ℂ) * ζ ^ 31 + ((793 / 147) : ℂ) * ζ ^ 32 - ((47 / 6) : ℂ) * ζ ^ 33 - ((7 / 9) : ℂ) * ζ ^ 34 - ((2131 / 441) : ℂ) * ζ ^ 35 + ((18493 / 1764) : ℂ) * ζ ^ 36 + ((19441 / 1764) : ℂ) * ζ ^ 37 + ((3881 / 882) : ℂ) * ζ ^ 38 + ((3359 / 441) : ℂ) * ζ ^ 39 + ((839 / 84) : ℂ) * ζ ^ 40 + ((19441 / 1764) : ℂ) * ζ ^ 41 + ((17 / 7) : ℂ) * ζ ^ 42 - ((28321 / 1764) : ℂ) * ζ ^ 43 - ((1297 / 126) : ℂ) * ζ ^ 44 - ((1075 / 98) : ℂ) * ζ ^ 45 + ((17 / 7) : ℂ) * ζ ^ 46 + ((362 / 441) : ℂ) * ζ ^ 47 + ((37151 / 1764) : ℂ) * ζ ^ 48 + ((20245 / 1764) : ℂ) * ζ ^ 49 + ((2248 / 441) : ℂ) * ζ ^ 50 + ((362 / 441) : ℂ) * ζ ^ 51 - ((8977 / 1764) : ℂ) * ζ ^ 52 - ((3643 / 294) : ℂ) * ζ ^ 53 - ((3319 / 441) : ℂ) * ζ ^ 54 - ((12629 / 1764) : ℂ) * ζ ^ 55 - ((8977 / 1764) : ℂ) * ζ ^ 56 - ((1271 / 441) : ℂ) * ζ ^ 57 + ((4558 / 441) : ℂ) * ζ ^ 58 + ((3727 / 588) : ℂ) * ζ ^ 59 + ((8977 / 1764) : ℂ) * ζ ^ 60 + ((1271 / 441) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_4_3 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        4 3 =
      alternatingSixAmbientRow15TransformedGeneratorA
        4 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((268 / 49) : ℂ) - ((1472 / 147) : ℂ) * ζ ^ 3 - ((268 / 49) : ℂ) * ζ ^ 4 - ((7193 / 588) : ℂ) * ζ ^ 5 + ((123 / 98) : ℂ) * ζ ^ 6 + ((1431 / 98) : ℂ) * ζ ^ 8 + ((2089 / 147) : ℂ) * ζ ^ 9 + ((639 / 49) : ℂ) * ζ ^ 10 - ((517 / 588) : ℂ) * ζ ^ 11 - ((5765 / 588) : ℂ) * ζ ^ 13 - ((165 / 14) : ℂ) * ζ ^ 14 - ((2437 / 882) : ℂ) * ζ ^ 15 - ((1231 / 196) : ℂ) * ζ ^ 16 + ((1163 / 588) : ℂ) * ζ ^ 17 - ((4519 / 1764) : ℂ) * ζ ^ 18 + ((3323 / 1764) : ℂ) * ζ ^ 19 - ((21557 / 1764) : ℂ) * ζ ^ 20 + ((191 / 441) : ℂ) * ζ ^ 21 - ((123 / 98) : ℂ) * ζ ^ 22 + ((1823 / 126) : ℂ) * ζ ^ 23 + ((5239 / 882) : ℂ) * ζ ^ 24 + ((65 / 4) : ℂ) * ζ ^ 25 - ((79 / 42) : ℂ) * ζ ^ 26 + ((517 / 588) : ℂ) * ζ ^ 27 - ((37127 / 1764) : ℂ) * ζ ^ 28 - ((48835 / 1764) : ℂ) * ζ ^ 29 - ((493 / 49) : ℂ) * ζ ^ 30 - ((593 / 1764) : ℂ) * ζ ^ 31 + ((1231 / 196) : ℂ) * ζ ^ 32 + ((1294 / 147) : ℂ) * ζ ^ 33 + ((449 / 42) : ℂ) * ζ ^ 34 + ((227 / 126) : ℂ) * ζ ^ 35 + ((17057 / 1764) : ℂ) * ζ ^ 36 + ((3107 / 882) : ℂ) * ζ ^ 37 + ((1303 / 588) : ℂ) * ζ ^ 38 - ((2291 / 588) : ℂ) * ζ ^ 39 + ((3047 / 441) : ℂ) * ζ ^ 40 + ((3107 / 882) : ℂ) * ζ ^ 41 + ((92 / 147) : ℂ) * ζ ^ 42 - ((8801 / 882) : ℂ) * ζ ^ 43 - ((1921 / 196) : ℂ) * ζ ^ 44 - ((131 / 9) : ℂ) * ζ ^ 45 + ((92 / 147) : ℂ) * ζ ^ 46 + ((536 / 441) : ℂ) * ζ ^ 47 + ((13051 / 588) : ℂ) * ζ ^ 48 + ((341 / 18) : ℂ) * ζ ^ 49 + ((1871 / 196) : ℂ) * ζ ^ 50 + ((536 / 441) : ℂ) * ζ ^ 51 - ((61 / 18) : ℂ) * ζ ^ 52 - ((21821 / 1764) : ℂ) * ζ ^ 53 - ((5981 / 588) : ℂ) * ζ ^ 54 - ((21319 / 1764) : ℂ) * ζ ^ 55 - ((61 / 18) : ℂ) * ζ ^ 56 - ((1163 / 588) : ℂ) * ζ ^ 57 + ((10655 / 882) : ℂ) * ζ ^ 58 + ((19175 / 1764) : ℂ) * ζ ^ 59 + ((61 / 18) : ℂ) * ζ ^ 60 + ((1163 / 588) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_4_4 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        4 4 =
      alternatingSixAmbientRow15TransformedGeneratorA
        4 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((24217 / 32193) : ℂ) + ((3799 / 1314) : ℂ) * ζ ^ 3 - ((24217 / 32193) : ℂ) * ζ ^ 4 - ((183451 / 128772) : ℂ) * ζ ^ 5 - ((197752 / 32193) : ℂ) * ζ ^ 6 - ((126811 / 42924) : ℂ) * ζ ^ 8 + ((111754 / 32193) : ℂ) * ζ ^ 9 - ((86540 / 32193) : ℂ) * ζ ^ 10 + ((557033 / 128772) : ℂ) * ζ ^ 11 + ((561559 / 64386) : ℂ) * ζ ^ 13 - ((111212 / 32193) : ℂ) * ζ ^ 14 + ((336127 / 128772) : ℂ) * ζ ^ 15 - ((498929 / 128772) : ℂ) * ζ ^ 16 + ((29285 / 14308) : ℂ) * ζ ^ 17 - ((3691 / 14308) : ℂ) * ζ ^ 18 + ((15779 / 9198) : ℂ) * ζ ^ 19 - ((218983 / 42924) : ℂ) * ζ ^ 20 + ((22399 / 9198) : ℂ) * ζ ^ 21 + ((197752 / 32193) : ℂ) * ζ ^ 22 + ((73323 / 14308) : ℂ) * ζ ^ 23 + ((39505 / 32193) : ℂ) * ζ ^ 24 + ((23151 / 2044) : ℂ) * ζ ^ 25 + ((698945 / 128772) : ℂ) * ζ ^ 26 - ((557033 / 128772) : ℂ) * ζ ^ 27 - ((47671 / 4599) : ℂ) * ζ ^ 28 - ((2726317 / 128772) : ℂ) * ζ ^ 29 - ((15803 / 882) : ℂ) * ζ ^ 30 - ((82737 / 14308) : ℂ) * ζ ^ 31 + ((498929 / 128772) : ℂ) * ζ ^ 32 + ((1233473 / 128772) : ℂ) * ζ ^ 33 + ((1424167 / 128772) : ℂ) * ζ ^ 34 + ((183353 / 10731) : ℂ) * ζ ^ 35 + ((744641 / 128772) : ℂ) * ζ ^ 36 + ((53386 / 32193) : ℂ) * ζ ^ 37 - ((603325 / 32193) : ℂ) * ζ ^ 38 - ((1830803 / 128772) : ℂ) * ζ ^ 39 - ((548480 / 32193) : ℂ) * ζ ^ 40 + ((53386 / 32193) : ℂ) * ζ ^ 41 + ((92063 / 128772) : ℂ) * ζ ^ 42 + ((2223517 / 128772) : ℂ) * ζ ^ 43 + ((646901 / 42924) : ℂ) * ζ ^ 44 + ((1612235 / 128772) : ℂ) * ζ ^ 45 + ((92063 / 128772) : ℂ) * ζ ^ 46 + ((6700 / 4599) : ℂ) * ζ ^ 47 - ((233111 / 18396) : ℂ) * ζ ^ 48 - ((36739 / 6132) : ℂ) * ζ ^ 49 - ((15529 / 2628) : ℂ) * ζ ^ 50 + ((6700 / 4599) : ℂ) * ζ ^ 51 - ((20476 / 10731) : ℂ) * ζ ^ 52 + ((121456 / 32193) : ℂ) * ζ ^ 53 + ((334429 / 64386) : ℂ) * ζ ^ 54 - ((67967 / 64386) : ℂ) * ζ ^ 55 - ((20476 / 10731) : ℂ) * ζ ^ 56 - ((29285 / 14308) : ℂ) * ζ ^ 57 - ((117485 / 42924) : ℂ) * ζ ^ 58 - ((8611 / 21462) : ℂ) * ζ ^ 59 + ((20476 / 10731) : ℂ) * ζ ^ 60 + ((29285 / 14308) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_4_5 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        4 5 =
      alternatingSixAmbientRow15TransformedGeneratorA
        4 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((2791 / 2044) : ℂ) - ((54101 / 64386) : ℂ) * ζ ^ 3 + ((2791 / 2044) : ℂ) * ζ ^ 4 + ((81449 / 42924) : ℂ) * ζ ^ 5 + ((157673 / 64386) : ℂ) * ζ ^ 6 - ((94853 / 64386) : ℂ) * ζ ^ 8 - ((284777 / 128772) : ℂ) * ζ ^ 9 - ((10399 / 4599) : ℂ) * ζ ^ 10 - ((12359 / 14308) : ℂ) * ζ ^ 11 - ((53029 / 128772) : ℂ) * ζ ^ 13 + ((303259 / 64386) : ℂ) * ζ ^ 14 - ((202861 / 64386) : ℂ) * ζ ^ 15 + ((75437 / 42924) : ℂ) * ζ ^ 16 - ((20215 / 64386) : ℂ) * ζ ^ 17 - ((77345 / 42924) : ℂ) * ζ ^ 18 + ((294491 / 128772) : ℂ) * ζ ^ 19 + ((123122 / 32193) : ℂ) * ζ ^ 20 - ((35653 / 32193) : ℂ) * ζ ^ 21 - ((157673 / 64386) : ℂ) * ζ ^ 22 - ((253835 / 42924) : ℂ) * ζ ^ 23 - ((266177 / 128772) : ℂ) * ζ ^ 24 - ((92041 / 7154) : ℂ) * ζ ^ 25 - ((164 / 1533) : ℂ) * ζ ^ 26 + ((12359 / 14308) : ℂ) * ζ ^ 27 + ((384238 / 32193) : ℂ) * ζ ^ 28 + ((125479 / 9198) : ℂ) * ζ ^ 29 + ((4229 / 196) : ℂ) * ζ ^ 30 - ((34441 / 42924) : ℂ) * ζ ^ 31 - ((75437 / 42924) : ℂ) * ζ ^ 32 - ((1349519 / 64386) : ℂ) * ζ ^ 33 - ((44113 / 2628) : ℂ) * ζ ^ 34 - ((485155 / 21462) : ℂ) * ζ ^ 35 + ((4931 / 6132) : ℂ) * ζ ^ 36 + ((5146 / 10731) : ℂ) * ζ ^ 37 + ((1519613 / 64386) : ℂ) * ζ ^ 38 + ((861715 / 42924) : ℂ) * ζ ^ 39 + ((856538 / 32193) : ℂ) * ζ ^ 40 + ((5146 / 10731) : ℂ) * ζ ^ 41 - ((150785 / 64386) : ℂ) * ζ ^ 42 - ((1256443 / 64386) : ℂ) * ζ ^ 43 - ((58571 / 2628) : ℂ) * ζ ^ 44 - ((9192 / 511) : ℂ) * ζ ^ 45 - ((150785 / 64386) : ℂ) * ζ ^ 46 + ((35759 / 21462) : ℂ) * ζ ^ 47 + ((1764401 / 128772) : ℂ) * ζ ^ 48 + ((523228 / 32193) : ℂ) * ζ ^ 49 + ((1623199 / 128772) : ℂ) * ζ ^ 50 + ((35759 / 21462) : ℂ) * ζ ^ 51 - ((54977 / 21462) : ℂ) * ζ ^ 52 - ((86367 / 14308) : ℂ) * ζ ^ 53 - ((440543 / 42924) : ℂ) * ζ ^ 54 - ((1018651 / 128772) : ℂ) * ζ ^ 55 - ((54977 / 21462) : ℂ) * ζ ^ 56 + ((20215 / 64386) : ℂ) * ζ ^ 57 + ((221891 / 64386) : ℂ) * ζ ^ 58 + ((114871 / 18396) : ℂ) * ζ ^ 59 + ((54977 / 21462) : ℂ) * ζ ^ 60 - ((20215 / 64386) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_5_0 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        5 0 =
      alternatingSixAmbientRow15TransformedGeneratorA
        5 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((221 / 882) : ℂ) - ((19945 / 1764) : ℂ) * ζ ^ 3 - ((221 / 882) : ℂ) * ζ ^ 4 - ((1003 / 1764) : ℂ) * ζ ^ 5 + ((14461 / 882) : ℂ) * ζ ^ 6 + ((2998 / 147) : ℂ) * ζ ^ 8 - ((2111 / 441) : ℂ) * ζ ^ 9 + ((4741 / 588) : ℂ) * ζ ^ 10 - ((4357 / 252) : ℂ) * ζ ^ 11 - ((13051 / 588) : ℂ) * ζ ^ 13 + ((14699 / 1764) : ℂ) * ζ ^ 14 - ((3511 / 1764) : ℂ) * ζ ^ 15 + ((9395 / 1764) : ℂ) * ζ ^ 16 - ((3149 / 588) : ℂ) * ζ ^ 17 + ((281 / 147) : ℂ) * ζ ^ 18 - ((2249 / 147) : ℂ) * ζ ^ 19 - ((7495 / 588) : ℂ) * ζ ^ 20 - ((117 / 49) : ℂ) * ζ ^ 21 - ((14461 / 882) : ℂ) * ζ ^ 22 + ((10777 / 588) : ℂ) * ζ ^ 23 + ((7970 / 441) : ℂ) * ζ ^ 24 + ((1339 / 63) : ℂ) * ζ ^ 25 - ((5311 / 196) : ℂ) * ζ ^ 26 + ((4357 / 252) : ℂ) * ζ ^ 27 - ((6253 / 441) : ℂ) * ζ ^ 28 + ((7489 / 882) : ℂ) * ζ ^ 29 + ((155 / 126) : ℂ) * ζ ^ 30 + ((4090 / 147) : ℂ) * ζ ^ 31 - ((9395 / 1764) : ℂ) * ζ ^ 32 + ((11629 / 588) : ℂ) * ζ ^ 33 + ((125 / 28) : ℂ) * ζ ^ 34 - ((3796 / 441) : ℂ) * ζ ^ 35 - ((12409 / 588) : ℂ) * ζ ^ 36 - ((2447 / 294) : ℂ) * ζ ^ 37 + ((4309 / 441) : ℂ) * ζ ^ 38 + ((1633 / 882) : ℂ) * ζ ^ 39 - ((506 / 441) : ℂ) * ζ ^ 40 - ((2447 / 294) : ℂ) * ζ ^ 41 + ((18877 / 1764) : ℂ) * ζ ^ 42 - ((44951 / 1764) : ℂ) * ζ ^ 43 - ((5471 / 588) : ℂ) * ζ ^ 44 - ((3085 / 252) : ℂ) * ζ ^ 45 + ((18877 / 1764) : ℂ) * ζ ^ 46 - ((18581 / 1764) : ℂ) * ζ ^ 47 + ((46343 / 1764) : ℂ) * ζ ^ 48 - ((1511 / 1764) : ℂ) * ζ ^ 49 - ((34049 / 1764) : ℂ) * ζ ^ 50 - ((18581 / 1764) : ℂ) * ζ ^ 51 + ((142 / 9) : ℂ) * ζ ^ 52 - ((1765 / 588) : ℂ) * ζ ^ 53 + ((3793 / 441) : ℂ) * ζ ^ 54 + ((5585 / 294) : ℂ) * ζ ^ 55 + ((142 / 9) : ℂ) * ζ ^ 56 + ((3149 / 588) : ℂ) * ζ ^ 57 + ((1558 / 441) : ℂ) * ζ ^ 58 - ((14929 / 1764) : ℂ) * ζ ^ 59 - ((142 / 9) : ℂ) * ζ ^ 60 - ((3149 / 588) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_5_1 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        5 1 =
      alternatingSixAmbientRow15TransformedGeneratorA
        5 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((7075 / 1764) : ℂ) + ((11741 / 882) : ℂ) * ζ ^ 3 + ((7075 / 1764) : ℂ) * ζ ^ 4 + ((1061 / 294) : ℂ) * ζ ^ 5 - ((23147 / 1764) : ℂ) * ζ ^ 6 - ((26939 / 1764) : ℂ) * ζ ^ 8 - ((15 / 28) : ℂ) * ζ ^ 9 - ((1493 / 588) : ℂ) * ζ ^ 10 + ((2243 / 252) : ℂ) * ζ ^ 11 + ((4687 / 441) : ℂ) * ζ ^ 13 - ((4667 / 441) : ℂ) * ζ ^ 14 - ((3457 / 252) : ℂ) * ζ ^ 15 - ((1601 / 588) : ℂ) * ζ ^ 16 + ((1807 / 588) : ℂ) * ζ ^ 17 + ((1054 / 147) : ℂ) * ζ ^ 18 + ((475 / 21) : ℂ) * ζ ^ 19 + ((24097 / 882) : ℂ) * ζ ^ 20 + ((157 / 126) : ℂ) * ζ ^ 21 + ((23147 / 1764) : ℂ) * ζ ^ 22 - ((10453 / 441) : ℂ) * ζ ^ 23 - ((7571 / 252) : ℂ) * ζ ^ 24 - ((42565 / 1764) : ℂ) * ζ ^ 25 + ((470 / 21) : ℂ) * ζ ^ 26 - ((2243 / 252) : ℂ) * ζ ^ 27 + ((14477 / 882) : ℂ) * ζ ^ 28 + ((4079 / 588) : ℂ) * ζ ^ 29 + ((16147 / 1764) : ℂ) * ζ ^ 30 - ((13865 / 882) : ℂ) * ζ ^ 31 + ((1601 / 588) : ℂ) * ζ ^ 32 - ((45263 / 1764) : ℂ) * ζ ^ 33 - ((22961 / 1764) : ℂ) * ζ ^ 34 - ((223 / 84) : ℂ) * ζ ^ 35 + ((9164 / 441) : ℂ) * ζ ^ 36 + ((2161 / 441) : ℂ) * ζ ^ 37 + ((2158 / 441) : ℂ) * ζ ^ 38 + ((2785 / 588) : ℂ) * ζ ^ 39 + ((2033 / 126) : ℂ) * ζ ^ 40 + ((2161 / 441) : ℂ) * ζ ^ 41 - ((16333 / 1764) : ℂ) * ζ ^ 42 + ((1423 / 196) : ℂ) * ζ ^ 43 - ((353 / 441) : ℂ) * ζ ^ 44 - ((2883 / 196) : ℂ) * ζ ^ 45 - ((16333 / 1764) : ℂ) * ζ ^ 46 + ((12029 / 1764) : ℂ) * ζ ^ 47 - ((1474 / 441) : ℂ) * ζ ^ 48 + ((38987 / 1764) : ℂ) * ζ ^ 49 + ((14335 / 441) : ℂ) * ζ ^ 50 + ((12029 / 1764) : ℂ) * ζ ^ 51 - ((31853 / 1764) : ℂ) * ζ ^ 52 - ((15551 / 1764) : ℂ) * ζ ^ 53 - ((13669 / 588) : ℂ) * ζ ^ 54 - ((12427 / 441) : ℂ) * ζ ^ 55 - ((31853 / 1764) : ℂ) * ζ ^ 56 - ((1807 / 588) : ℂ) * ζ ^ 57 + ((1429 / 252) : ℂ) * ζ ^ 58 + ((37679 / 1764) : ℂ) * ζ ^ 59 + ((31853 / 1764) : ℂ) * ζ ^ 60 + ((1807 / 588) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_5_2 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        5 2 =
      alternatingSixAmbientRow15TransformedGeneratorA
        5 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((1585 / 1764) : ℂ) - ((6421 / 882) : ℂ) * ζ ^ 3 - ((1585 / 1764) : ℂ) * ζ ^ 4 - ((1916 / 441) : ℂ) * ζ ^ 5 + ((3775 / 588) : ℂ) * ζ ^ 6 + ((2381 / 147) : ℂ) * ζ ^ 8 + ((524 / 147) : ℂ) * ζ ^ 9 + ((3119 / 588) : ℂ) * ζ ^ 10 - ((17 / 7) : ℂ) * ζ ^ 11 - ((2155 / 441) : ℂ) * ζ ^ 13 + ((164 / 147) : ℂ) * ζ ^ 14 + ((29 / 21) : ℂ) * ζ ^ 15 - ((943 / 294) : ℂ) * ζ ^ 16 - ((344 / 441) : ℂ) * ζ ^ 17 - ((40 / 49) : ℂ) * ζ ^ 18 - ((80 / 21) : ℂ) * ζ ^ 19 - ((3797 / 588) : ℂ) * ζ ^ 20 - ((913 / 588) : ℂ) * ζ ^ 21 - ((3775 / 588) : ℂ) * ζ ^ 22 + ((47 / 98) : ℂ) * ζ ^ 23 + ((13 / 4) : ℂ) * ζ ^ 24 + ((10249 / 882) : ℂ) * ζ ^ 25 - ((373 / 42) : ℂ) * ζ ^ 26 + ((17 / 7) : ℂ) * ζ ^ 27 - ((8272 / 441) : ℂ) * ζ ^ 28 - ((14981 / 1764) : ℂ) * ζ ^ 29 + ((173 / 252) : ℂ) * ζ ^ 30 + ((5977 / 882) : ℂ) * ζ ^ 31 + ((943 / 294) : ℂ) * ζ ^ 32 + ((4177 / 588) : ℂ) * ζ ^ 33 + ((5773 / 1764) : ℂ) * ζ ^ 34 - ((4757 / 441) : ℂ) * ζ ^ 35 + ((6851 / 1764) : ℂ) * ζ ^ 36 - ((13 / 1764) : ℂ) * ζ ^ 37 + ((6431 / 441) : ℂ) * ζ ^ 38 + ((1601 / 126) : ℂ) * ζ ^ 39 + ((3721 / 294) : ℂ) * ζ ^ 40 - ((13 / 1764) : ℂ) * ζ ^ 41 + ((1447 / 588) : ℂ) * ζ ^ 42 - ((32603 / 1764) : ℂ) * ζ ^ 43 - ((26791 / 1764) : ℂ) * ζ ^ 44 - ((559 / 28) : ℂ) * ζ ^ 45 + ((1447 / 588) : ℂ) * ζ ^ 46 - ((3835 / 882) : ℂ) * ζ ^ 47 + ((40855 / 1764) : ℂ) * ζ ^ 48 + ((14863 / 882) : ℂ) * ζ ^ 49 + ((18353 / 1764) : ℂ) * ζ ^ 50 - ((3835 / 882) : ℂ) * ζ ^ 51 - ((1193 / 1764) : ℂ) * ζ ^ 52 - ((1259 / 84) : ℂ) * ζ ^ 53 - ((1621 / 126) : ℂ) * ζ ^ 54 - ((547 / 252) : ℂ) * ζ ^ 55 - ((1193 / 1764) : ℂ) * ζ ^ 56 + ((344 / 441) : ℂ) * ζ ^ 57 + ((638 / 63) : ℂ) * ζ ^ 58 + ((3833 / 588) : ℂ) * ζ ^ 59 + ((1193 / 1764) : ℂ) * ζ ^ 60 - ((344 / 441) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_5_3 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        5 3 =
      alternatingSixAmbientRow15TransformedGeneratorA
        5 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((4751 / 1764) : ℂ) - ((2783 / 441) : ℂ) * ζ ^ 3 - ((4751 / 1764) : ℂ) * ζ ^ 4 - ((3700 / 441) : ℂ) * ζ ^ 5 + ((937 / 441) : ℂ) * ζ ^ 6 + ((4973 / 441) : ℂ) * ζ ^ 8 + ((2053 / 252) : ℂ) * ζ ^ 9 + ((11983 / 882) : ℂ) * ζ ^ 10 - ((967 / 588) : ℂ) * ζ ^ 11 - ((9013 / 588) : ℂ) * ζ ^ 13 - ((10109 / 882) : ℂ) * ζ ^ 14 - ((4051 / 441) : ℂ) * ζ ^ 15 - ((965 / 588) : ℂ) * ζ ^ 16 - ((143 / 588) : ℂ) * ζ ^ 17 + ((2911 / 882) : ℂ) * ζ ^ 18 + ((13303 / 1764) : ℂ) * ζ ^ 19 - ((272 / 63) : ℂ) * ζ ^ 20 + ((1549 / 441) : ℂ) * ζ ^ 21 - ((937 / 441) : ℂ) * ζ ^ 22 + ((4393 / 588) : ℂ) * ζ ^ 23 + ((4721 / 1764) : ℂ) * ζ ^ 24 + ((9608 / 441) : ℂ) * ζ ^ 25 - ((6001 / 1764) : ℂ) * ζ ^ 26 + ((967 / 588) : ℂ) * ζ ^ 27 - ((35129 / 1764) : ℂ) * ζ ^ 28 - ((14831 / 882) : ℂ) * ζ ^ 29 - ((9335 / 441) : ℂ) * ζ ^ 30 + ((7451 / 1764) : ℂ) * ζ ^ 31 + ((965 / 588) : ℂ) * ζ ^ 32 + ((14393 / 588) : ℂ) * ζ ^ 33 + ((4315 / 196) : ℂ) * ζ ^ 34 + ((4721 / 441) : ℂ) * ζ ^ 35 + ((6589 / 1764) : ℂ) * ζ ^ 36 - ((3527 / 882) : ℂ) * ζ ^ 37 - ((127 / 84) : ℂ) * ζ ^ 38 - ((1915 / 196) : ℂ) * ζ ^ 39 + ((3373 / 1764) : ℂ) * ζ ^ 40 - ((3527 / 882) : ℂ) * ζ ^ 41 + ((751 / 588) : ℂ) * ζ ^ 42 - ((6473 / 1764) : ℂ) * ζ ^ 43 - ((143 / 98) : ℂ) * ζ ^ 44 - ((27859 / 1764) : ℂ) * ζ ^ 45 + ((751 / 588) : ℂ) * ζ ^ 46 - ((325 / 126) : ℂ) * ζ ^ 47 + ((134 / 7) : ℂ) * ζ ^ 48 + ((33197 / 1764) : ℂ) * ζ ^ 49 + ((55 / 4) : ℂ) * ζ ^ 50 - ((325 / 126) : ℂ) * ζ ^ 51 - ((1847 / 882) : ℂ) * ζ ^ 52 - ((27121 / 1764) : ℂ) * ζ ^ 53 - ((2209 / 147) : ℂ) * ζ ^ 54 - ((14237 / 1764) : ℂ) * ζ ^ 55 - ((1847 / 882) : ℂ) * ζ ^ 56 + ((143 / 588) : ℂ) * ζ ^ 57 + ((89 / 9) : ℂ) * ζ ^ 58 + ((18787 / 1764) : ℂ) * ζ ^ 59 + ((1847 / 882) : ℂ) * ζ ^ 60 - ((143 / 588) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_5_4 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        5 4 =
      alternatingSixAmbientRow15TransformedGeneratorA
        5 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (((172229 / 128772) : ℂ) - ((110381 / 128772) : ℂ) * ζ ^ 3 - ((172229 / 128772) : ℂ) * ζ ^ 4 - ((153392 / 32193) : ℂ) * ζ ^ 5 - ((67147 / 64386) : ℂ) * ζ ^ 6 + ((10560 / 3577) : ℂ) * ζ ^ 8 + ((701549 / 128772) : ℂ) * ζ ^ 9 + ((222104 / 32193) : ℂ) * ζ ^ 10 + ((217069 / 128772) : ℂ) * ζ ^ 11 - ((271945 / 64386) : ℂ) * ζ ^ 13 - ((511355 / 64386) : ℂ) * ζ ^ 14 - ((1055665 / 128772) : ℂ) * ζ ^ 15 - ((208753 / 128772) : ℂ) * ζ ^ 16 + ((29327 / 42924) : ℂ) * ζ ^ 17 + ((49463 / 7154) : ℂ) * ζ ^ 18 + ((636367 / 64386) : ℂ) * ζ ^ 19 + ((11143 / 1022) : ℂ) * ζ ^ 20 + ((48043 / 32193) : ℂ) * ζ ^ 21 + ((67147 / 64386) : ℂ) * ζ ^ 22 - ((245845 / 42924) : ℂ) * ζ ^ 23 - ((1612771 / 128772) : ℂ) * ζ ^ 24 - ((34823 / 10731) : ℂ) * ζ ^ 25 + ((70219 / 128772) : ℂ) * ζ ^ 26 - ((217069 / 128772) : ℂ) * ζ ^ 27 + ((175843 / 128772) : ℂ) * ζ ^ 28 + ((41081 / 64386) : ℂ) * ζ ^ 29 - ((70255 / 9198) : ℂ) * ζ ^ 30 - ((85639 / 42924) : ℂ) * ζ ^ 31 + ((208753 / 128772) : ℂ) * ζ ^ 32 + ((502349 / 64386) : ℂ) * ζ ^ 33 + ((785201 / 128772) : ℂ) * ζ ^ 34 + ((583837 / 42924) : ℂ) * ζ ^ 35 + ((125999 / 64386) : ℂ) * ζ ^ 36 - ((8105 / 64386) : ℂ) * ζ ^ 37 - ((1028329 / 64386) : ℂ) * ζ ^ 38 - ((787145 / 64386) : ℂ) * ζ ^ 39 - ((1194083 / 64386) : ℂ) * ζ ^ 40 - ((8105 / 64386) : ℂ) * ζ ^ 41 + ((64075 / 128772) : ℂ) * ζ ^ 42 + ((11945 / 657) : ℂ) * ζ ^ 43 + ((123481 / 7154) : ℂ) * ζ ^ 44 + ((1990447 / 128772) : ℂ) * ζ ^ 45 + ((64075 / 128772) : ℂ) * ζ ^ 46 + ((9962 / 32193) : ℂ) * ζ ^ 47 - ((2041699 / 128772) : ℂ) * ζ ^ 48 - ((25751 / 2044) : ℂ) * ζ ^ 49 - ((986129 / 128772) : ℂ) * ζ ^ 50 + ((9962 / 32193) : ℂ) * ζ ^ 51 - ((4805 / 14308) : ℂ) * ζ ^ 52 + ((973817 / 128772) : ℂ) * ζ ^ 53 + ((65861 / 9198) : ℂ) * ζ ^ 54 + ((238339 / 128772) : ℂ) * ζ ^ 55 - ((4805 / 14308) : ℂ) * ζ ^ 56 - ((29327 / 42924) : ℂ) * ζ ^ 57 - ((111889 / 42924) : ℂ) * ζ ^ 58 - ((13247 / 6132) : ℂ) * ζ ^ 59 + ((4805 / 14308) : ℂ) * ζ ^ 60 + ((29327 / 42924) : ℂ) * ζ ^ 61)
private theorem row15_transformedGeneratorA_5_5 :
    (alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis)
        5 5 =
      alternatingSixAmbientRow15TransformedGeneratorA
        5 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow15Eigenbasis,
      alternatingSixAmbientRow15EigenbasisInverse,
      alternatingSixFiveAmbient_row15_matrixA,
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row15 (-((325975 / 128772) : ℂ) + ((297953 / 128772) : ℂ) * ζ ^ 3 + ((325975 / 128772) : ℂ) * ζ ^ 4 + ((398665 / 64386) : ℂ) * ζ ^ 5 - ((18163 / 21462) : ℂ) * ζ ^ 6 - ((95833 / 10731) : ℂ) * ζ ^ 8 - ((61576 / 10731) : ℂ) * ζ ^ 9 - ((629057 / 42924) : ℂ) * ζ ^ 10 + ((123385 / 42924) : ℂ) * ζ ^ 11 + ((1009823 / 64386) : ℂ) * ζ ^ 13 + ((197577 / 14308) : ℂ) * ζ ^ 14 + ((1073659 / 64386) : ℂ) * ζ ^ 15 - ((11059 / 21462) : ℂ) * ζ ^ 16 + ((29209 / 64386) : ℂ) * ζ ^ 17 - ((1017067 / 64386) : ℂ) * ζ ^ 18 - ((1777163 / 128772) : ℂ) * ζ ^ 19 - ((53219 / 3577) : ℂ) * ζ ^ 20 - ((83873 / 128772) : ℂ) * ζ ^ 21 + ((18163 / 21462) : ℂ) * ζ ^ 22 + ((1247041 / 128772) : ℂ) * ζ ^ 23 + ((308255 / 21462) : ℂ) * ζ ^ 24 + ((368089 / 64386) : ℂ) * ζ ^ 25 + ((450539 / 128772) : ℂ) * ζ ^ 26 - ((123385 / 42924) : ℂ) * ζ ^ 27 - ((10277 / 18396) : ℂ) * ζ ^ 28 - ((1170559 / 128772) : ℂ) * ζ ^ 29 + ((1128835 / 128772) : ℂ) * ζ ^ 30 - ((235345 / 42924) : ℂ) * ζ ^ 31 + ((11059 / 21462) : ℂ) * ζ ^ 32 - ((467417 / 32193) : ℂ) * ζ ^ 33 - ((32009 / 4599) : ℂ) * ζ ^ 34 - ((99271 / 6132) : ℂ) * ζ ^ 35 + ((11551 / 3066) : ℂ) * ζ ^ 36 + ((22301 / 14308) : ℂ) * ζ ^ 37 + ((671366 / 32193) : ℂ) * ζ ^ 38 + ((353161 / 21462) : ℂ) * ζ ^ 39 + ((1474265 / 64386) : ℂ) * ζ ^ 40 + ((22301 / 14308) : ℂ) * ζ ^ 41 - ((341561 / 128772) : ℂ) * ζ ^ 42 - ((2333011 / 128772) : ℂ) * ζ ^ 43 - ((649024 / 32193) : ℂ) * ζ ^ 44 - ((252257 / 14308) : ℂ) * ζ ^ 45 - ((341561 / 128772) : ℂ) * ζ ^ 46 + ((9330 / 3577) : ℂ) * ζ ^ 47 + ((832121 / 64386) : ℂ) * ζ ^ 48 + ((575819 / 32193) : ℂ) * ζ ^ 49 + ((1654175 / 128772) : ℂ) * ζ ^ 50 + ((9330 / 3577) : ℂ) * ζ ^ 51 - ((11633 / 3577) : ℂ) * ζ ^ 52 - ((7199 / 1022) : ℂ) * ζ ^ 53 - ((72923 / 7154) : ℂ) * ζ ^ 54 - ((35810 / 4599) : ℂ) * ζ ^ 55 - ((11633 / 3577) : ℂ) * ζ ^ 56 - ((29209 / 64386) : ℂ) * ζ ^ 57 + ((157513 / 64386) : ℂ) * ζ ^ 58 + ((166700 / 32193) : ℂ) * ζ ^ 59 + ((11633 / 3577) : ℂ) * ζ ^ 60 + ((29209 / 64386) : ℂ) * ζ ^ 61)
/-- Exact conjugation formula for the row 15 first
generator. -/
theorem alternatingSixAmbientRow15TransformedGeneratorA_eq :
    alternatingSixAmbientRow15EigenbasisInverse *
        alternatingSixFiveAmbient_row15_matrixA *
        alternatingSixAmbientRow15Eigenbasis =
      alternatingSixAmbientRow15TransformedGeneratorA := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row15_transformedGeneratorA_0_0
  · exact row15_transformedGeneratorA_0_1
  · exact row15_transformedGeneratorA_0_2
  · exact row15_transformedGeneratorA_0_3
  · exact row15_transformedGeneratorA_0_4
  · exact row15_transformedGeneratorA_0_5
  · exact row15_transformedGeneratorA_1_0
  · exact row15_transformedGeneratorA_1_1
  · exact row15_transformedGeneratorA_1_2
  · exact row15_transformedGeneratorA_1_3
  · exact row15_transformedGeneratorA_1_4
  · exact row15_transformedGeneratorA_1_5
  · exact row15_transformedGeneratorA_2_0
  · exact row15_transformedGeneratorA_2_1
  · exact row15_transformedGeneratorA_2_2
  · exact row15_transformedGeneratorA_2_3
  · exact row15_transformedGeneratorA_2_4
  · exact row15_transformedGeneratorA_2_5
  · exact row15_transformedGeneratorA_3_0
  · exact row15_transformedGeneratorA_3_1
  · exact row15_transformedGeneratorA_3_2
  · exact row15_transformedGeneratorA_3_3
  · exact row15_transformedGeneratorA_3_4
  · exact row15_transformedGeneratorA_3_5
  · exact row15_transformedGeneratorA_4_0
  · exact row15_transformedGeneratorA_4_1
  · exact row15_transformedGeneratorA_4_2
  · exact row15_transformedGeneratorA_4_3
  · exact row15_transformedGeneratorA_4_4
  · exact row15_transformedGeneratorA_4_5
  · exact row15_transformedGeneratorA_5_0
  · exact row15_transformedGeneratorA_5_1
  · exact row15_transformedGeneratorA_5_2
  · exact row15_transformedGeneratorA_5_3
  · exact row15_transformedGeneratorA_5_4
  · exact row15_transformedGeneratorA_5_5


end InductiveMcKay
end McKayConjecture
