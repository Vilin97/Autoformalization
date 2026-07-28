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
# Checked diagonal data for ambient row 12

This generated module records an exact eigenbasis for the second generator
and the first generator in that basis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Eigenvalue block labels for row 12. -/
def alternatingSixAmbientRow12EigenvalueLabel :
    Fin 6 → Fin 4 :=
  ![0, 1, 1, 2, 2, 3]

/-- Second-generator eigenvalues, including their multiplicities. -/
def alternatingSixAmbientRow12GeneratorBEigenvalue :
    Fin 6 → ℂ :=
  fun i ↦
    alternatingSixOrderEightOddEigenvalue
      (alternatingSixAmbientRow12EigenvalueLabel i)

/-- Diagonal form of the row 12 second generator. -/
def alternatingSixAmbientRow12GeneratorBDiagonal :
    Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.diagonal
    alternatingSixAmbientRow12GeneratorBEigenvalue

/-- Checked eigenbasis for the row 12 second generator. -/
def alternatingSixAmbientRow12Eigenbasis :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((1 / 2), 3), ((1 / 2), 5), ((1 / 2), 7), ((1 / 2), 10), ((1 / 2), 15), ((-1 / 2), 19), ((-1 / 2), 20), ((-1 / 2), 23), ((1 / 2), 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [(1, 0), (-1, 5), (-1, 10), (-1, 15), (-1, 20), (1, 25)],
      alternatingSixCyclotomicValue [((-1 / 2), 3), ((-1 / 2), 5), ((-1 / 2), 7), ((1 / 2), 10), ((1 / 2), 15), ((1 / 2), 19), ((1 / 2), 20), ((1 / 2), 23), ((-1 / 2), 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((21 / 73), 0), ((65 / 73), 3), ((27 / 73), 5), ((65 / 73), 7), ((-7 / 73), 10), ((-1 / 73), 15), ((-65 / 73), 19), ((-43 / 73), 20), ((-65 / 73), 23), ((-24 / 73), 25), ((-10 / 73), 30), ((65 / 73), 31)],
      alternatingSixCyclotomicValue [((-8 / 73), 0), ((-53 / 146), 3), ((-31 / 146), 5), ((-53 / 146), 7), ((-19 / 146), 10), ((39 / 146), 15), ((53 / 146), 19), ((-75 / 146), 20), ((53 / 146), 23), ((30 / 73), 25), ((25 / 146), 30), ((-53 / 146), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 3), ((-1 / 2), 5), ((-1 / 2), 7), ((-1 / 2), 10), ((1 / 2), 15), ((1 / 2), 19), ((1 / 2), 20), ((1 / 2), 23), (1, 25), ((-1 / 2), 30), ((-1 / 2), 31)]],
    ![alternatingSixCyclotomicValue [(-1, 0), ((1 / 2), 3), ((-1 / 2), 5), ((1 / 2), 7), ((-1 / 2), 10), ((1 / 2), 15), ((-1 / 2), 19), ((1 / 2), 20), ((-1 / 2), 23), ((1 / 2), 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [(1, 0), (1, 3), (1, 5), (1, 7), (1, 10), (-1, 19), (-1, 23), (1, 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 3), ((1 / 2), 7), ((-1 / 2), 10), (-1, 15), ((-1 / 2), 19), ((-1 / 2), 20), ((-1 / 2), 23), ((-1 / 2), 25), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((15 / 73), 0), ((-37 / 73), 3), ((-12 / 73), 5), ((-37 / 73), 7), ((-5 / 73), 10), ((41 / 73), 15), ((37 / 73), 19), ((-62 / 73), 20), ((37 / 73), 23), ((35 / 73), 25), ((-28 / 73), 30), ((-37 / 73), 31)],
      alternatingSixCyclotomicValue [((145 / 146), 0), ((-163 / 146), 3), ((-58 / 73), 5), ((-163 / 146), 7), ((49 / 146), 10), ((40 / 73), 15), ((163 / 146), 19), ((-137 / 146), 20), ((163 / 146), 23), ((95 / 146), 25), ((-38 / 73), 30), ((-163 / 146), 31)],
      alternatingSixCyclotomicValue [(1, 0), ((1 / 2), 3), ((1 / 2), 5), ((1 / 2), 7), ((-1 / 2), 10), ((1 / 2), 15), ((-1 / 2), 19), ((-1 / 2), 20), ((-1 / 2), 23), ((1 / 2), 30), ((1 / 2), 31)]],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(-1, 0), (-2, 3), (-1, 5), (-2, 7), (1, 15), (2, 19), (1, 20), (2, 23), (1, 25), (1, 30), (-2, 31)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 2), 3), ((1 / 2), 7), ((1 / 2), 10), ((-1 / 2), 19), ((1 / 2), 20), ((-1 / 2), 23), ((-1 / 2), 25), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((48 / 73), 0), ((-60 / 73), 3), ((-53 / 73), 5), ((-60 / 73), 7), ((-16 / 73), 10), ((29 / 73), 15), ((60 / 73), 19), ((-67 / 73), 20), ((60 / 73), 23), ((39 / 73), 25), ((-2 / 73), 30), ((-60 / 73), 31)],
      alternatingSixCyclotomicValue [((99 / 146), 0), ((-69 / 146), 3), ((-25 / 73), 5), ((-69 / 146), 7), ((113 / 146), 10), ((-18 / 73), 15), ((69 / 146), 19), ((-15 / 146), 20), ((69 / 146), 23), ((85 / 146), 25), ((-34 / 73), 30), ((-69 / 146), 31)],
      alternatingSixCyclotomicValue [(1, 0), (1, 10), (-1, 20), (-1, 30)]],
    ![alternatingSixCyclotomicValue [(-1, 3), (-1, 7), (1, 15), (1, 19), (1, 23), (-1, 31)],
      alternatingSixCyclotomicValue [(-1, 20), (-1, 25), (-1, 30)],
      alternatingSixCyclotomicValue [(-1, 3), (-1, 7), (1, 19), (1, 23), (-1, 31)],
      alternatingSixCyclotomicValue [((20 / 73), 0), ((-25 / 73), 3), ((-16 / 73), 5), ((-25 / 73), 7), ((42 / 73), 10), ((6 / 73), 15), ((25 / 73), 19), ((39 / 73), 20), ((25 / 73), 23), ((-2 / 73), 25), ((-13 / 73), 30), ((-25 / 73), 31)],
      alternatingSixCyclotomicValue [((48 / 73), 0), ((13 / 73), 3), ((20 / 73), 5), ((13 / 73), 7), ((-16 / 73), 10), ((-44 / 73), 15), ((-13 / 73), 19), ((6 / 73), 20), ((-13 / 73), 23), ((-34 / 73), 25), ((-2 / 73), 30), ((13 / 73), 31)],
      alternatingSixCyclotomicValue [(-1, 20)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 3), ((1 / 2), 5), ((-1 / 2), 7), ((1 / 2), 10), ((1 / 2), 15), ((1 / 2), 19), ((1 / 2), 20), ((1 / 2), 23), ((1 / 2), 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [((-1 / 2), 3), ((1 / 2), 5), ((-1 / 2), 7), ((1 / 2), 10), ((1 / 2), 15), ((1 / 2), 19), ((1 / 2), 20), ((1 / 2), 23), ((-1 / 2), 30), ((-1 / 2), 31)]],
    ![alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)]]
  ]

/-- Checked inverse of the row 12 eigenbasis. -/
def alternatingSixAmbientRow12EigenbasisInverse :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((-5 / 146), 0), ((79 / 584), 3), ((237 / 584), 5), ((79 / 584), 7), ((13 / 584), 10), ((-25 / 584), 15), ((-79 / 584), 19), ((59 / 584), 20), ((-79 / 584), 23), ((-37 / 146), 25), ((-115 / 584), 30), ((79 / 584), 31)],
      alternatingSixCyclotomicValue [((-55 / 584), 0), ((53 / 584), 3), ((43 / 292), 5), ((53 / 584), 7), ((127 / 584), 10), ((-20 / 73), 15), ((-53 / 584), 19), ((-75 / 584), 20), ((-53 / 584), 23), ((-115 / 584), 25), ((-19 / 73), 30), ((53 / 584), 31)],
      alternatingSixCyclotomicValue [((-4 / 73), 0), ((-5 / 584), 3), ((-15 / 584), 5), ((-5 / 584), 7), ((-23 / 584), 10), ((33 / 584), 15), ((5 / 584), 19), ((-37 / 584), 20), ((5 / 584), 23), ((13 / 292), 25), ((-111 / 584), 30), ((-5 / 584), 31)],
      alternatingSixCyclotomicValue [((-79 / 292), 0), ((-21 / 146), 3), ((5 / 73), 5), ((-21 / 146), 7), ((-9 / 146), 10), ((-11 / 73), 15), ((21 / 146), 19), ((25 / 292), 20), ((21 / 146), 23), ((-59 / 292), 25), ((1 / 146), 30), ((-21 / 146), 31)],
      alternatingSixCyclotomicValue [((-67 / 584), 0), ((-13 / 73), 3), ((-93 / 584), 5), ((-13 / 73), 7), ((41 / 146), 10), ((117 / 584), 15), ((13 / 73), 19), ((6 / 73), 20), ((13 / 73), 23), ((205 / 584), 25), ((71 / 584), 30), ((-13 / 73), 31)],
      alternatingSixCyclotomicValue [((159 / 292), 0), ((91 / 292), 3), ((27 / 146), 5), ((91 / 292), 7), ((39 / 292), 10), ((-75 / 292), 15), ((-91 / 292), 19), ((-115 / 292), 20), ((-91 / 292), 23), ((-79 / 292), 25), ((-53 / 292), 30), ((91 / 292), 31)]],
    ![alternatingSixCyclotomicValue [((-9 / 292), 0), ((5 / 146), 3), ((-159 / 584), 5), ((5 / 146), 7), ((-127 / 584), 10), ((-59 / 584), 15), ((-5 / 146), 19), ((221 / 584), 20), ((-5 / 146), 23), ((-31 / 584), 25), ((225 / 584), 30), ((5 / 146), 31)],
      alternatingSixCyclotomicValue [((133 / 584), 0), ((55 / 584), 3), ((19 / 584), 5), ((55 / 584), 7), ((107 / 584), 10), ((-217 / 584), 15), ((-55 / 584), 19), ((-31 / 584), 20), ((-55 / 584), 23), ((19 / 73), 25), ((63 / 292), 30), ((55 / 584), 31)],
      alternatingSixCyclotomicValue [((-131 / 584), 0), ((105 / 584), 3), ((169 / 584), 5), ((105 / 584), 7), ((-87 / 292), 10), ((37 / 584), 15), ((-105 / 584), 19), ((-43 / 146), 20), ((-105 / 584), 23), ((19 / 292), 25), ((141 / 584), 30), ((105 / 584), 31)],
      alternatingSixCyclotomicValue [((53 / 292), 0), ((3 / 146), 3), ((9 / 146), 5), ((3 / 146), 7), ((-15 / 73), 10), ((-25 / 292), 15), ((-3 / 146), 19), ((59 / 292), 20), ((-3 / 146), 23), ((-75 / 292), 25), ((-21 / 146), 30), ((3 / 146), 31)],
      alternatingSixCyclotomicValue [((385 / 584), 0), ((-79 / 584), 3), ((-155 / 292), 5), ((-79 / 584), 7), ((-43 / 292), 10), ((-97 / 292), 15), ((79 / 584), 19), ((-33 / 146), 20), ((79 / 584), 23), ((75 / 584), 25), ((-31 / 584), 30), ((-79 / 584), 31)],
      alternatingSixCyclotomicValue [((19 / 292), 0), ((15 / 73), 3), ((-28 / 73), 5), ((15 / 73), 7), ((57 / 292), 10), ((21 / 146), 15), ((-15 / 73), 19), ((79 / 292), 20), ((-15 / 73), 23), ((53 / 292), 25), ((91 / 292), 30), ((15 / 73), 31)]],
    ![alternatingSixCyclotomicValue [((13 / 292), 0), ((-37 / 584), 3), ((35 / 584), 5), ((-37 / 584), 7), ((5 / 584), 10), ((215 / 584), 15), ((37 / 584), 19), ((135 / 584), 20), ((37 / 584), 23), ((67 / 292), 25), ((259 / 584), 30), ((-37 / 584), 31)],
      alternatingSixCyclotomicValue [((35 / 584), 0), ((99 / 584), 3), ((28 / 73), 5), ((99 / 584), 7), ((105 / 584), 10), ((-21 / 146), 15), ((-99 / 584), 19), ((-85 / 584), 20), ((-99 / 584), 23), ((-33 / 584), 25), ((-9 / 146), 30), ((99 / 584), 31)],
      alternatingSixCyclotomicValue [((25 / 146), 0), ((-249 / 584), 3), ((129 / 584), 5), ((-249 / 584), 7), ((81 / 584), 10), ((125 / 584), 15), ((249 / 584), 19), ((-149 / 584), 20), ((249 / 584), 23), ((5 / 292), 25), ((-9 / 584), 30), ((-249 / 584), 31)],
      alternatingSixCyclotomicValue [((37 / 292), 0), ((-33 / 292), 3), ((-99 / 292), 5), ((-33 / 292), 7), ((-27 / 73), 10), ((-45 / 292), 15), ((33 / 292), 19), ((-69 / 292), 20), ((33 / 292), 23), ((11 / 292), 25), ((3 / 73), 30), ((-33 / 292), 31)],
      alternatingSixCyclotomicValue [((-183 / 584), 0), ((-5 / 73), 3), ((-193 / 584), 5), ((-5 / 73), 7), ((-165 / 292), 10), ((-247 / 584), 15), ((5 / 73), 19), ((71 / 292), 20), ((5 / 73), 23), ((135 / 584), 25), ((353 / 584), 30), ((-5 / 73), 31)],
      alternatingSixCyclotomicValue [((151 / 292), 0), ((181 / 292), 3), ((105 / 292), 5), ((181 / 292), 7), ((22 / 73), 10), ((-3 / 73), 15), ((-181 / 292), 19), ((10 / 73), 20), ((-181 / 292), 23), ((-9 / 73), 25), ((-13 / 146), 30), ((181 / 292), 31)]],
    ![alternatingSixCyclotomicValue [((-47 / 292), 0), ((-37 / 292), 3), ((-3 / 584), 5), ((-37 / 292), 7), ((83 / 584), 10), ((-81 / 584), 15), ((37 / 292), 19), ((-241 / 584), 20), ((37 / 292), 23), ((-97 / 584), 25), ((-139 / 584), 30), ((-37 / 292), 31)],
      alternatingSixCyclotomicValue [((-295 / 584), 0), ((-313 / 584), 3), ((-355 / 584), 5), ((-313 / 584), 7), ((-301 / 584), 10), ((343 / 584), 15), ((313 / 584), 19), ((195 / 584), 20), ((313 / 584), 23), ((10 / 73), 25), ((37 / 292), 30), ((-313 / 584), 31)],
      alternatingSixCyclotomicValue [((-19 / 584), 0), ((13 / 584), 3), ((-107 / 584), 5), ((13 / 584), 7), ((2 / 73), 10), ((31 / 584), 15), ((-13 / 584), 19), ((143 / 292), 20), ((-13 / 584), 23), ((-63 / 292), 25), ((-91 / 584), 30), ((13 / 584), 31)],
      alternatingSixCyclotomicValue [((1 / 292), 0), ((-139 / 292), 3), ((21 / 292), 5), ((-139 / 292), 7), ((149 / 292), 10), ((101 / 146), 15), ((139 / 292), 19), ((2 / 73), 20), ((139 / 292), 23), ((95 / 292), 25), ((97 / 292), 30), ((-139 / 292), 31)],
      alternatingSixCyclotomicValue [((437 / 584), 0), ((285 / 584), 3), ((245 / 292), 5), ((285 / 584), 7), ((181 / 292), 10), ((45 / 292), 15), ((-285 / 584), 19), ((-77 / 292), 20), ((-285 / 584), 23), ((-387 / 584), 25), ((-389 / 584), 30), ((285 / 584), 31)],
      alternatingSixCyclotomicValue [((-209 / 292), 0), ((-111 / 146), 3), ((-155 / 292), 5), ((-111 / 146), 7), ((-131 / 146), 10), ((-97 / 292), 15), ((111 / 146), 19), ((-33 / 146), 20), ((111 / 146), 23), ((37 / 146), 25), ((47 / 146), 30), ((-111 / 146), 31)]],
    ![alternatingSixCyclotomicValue [((-27 / 292), 0), ((133 / 584), 3), ((-185 / 584), 5), ((133 / 584), 7), ((-89 / 584), 10), ((-323 / 584), 15), ((-133 / 584), 19), ((-67 / 584), 20), ((-133 / 584), 23), ((-5 / 146), 25), ((-55 / 584), 30), ((133 / 584), 31)],
      alternatingSixCyclotomicValue [((107 / 584), 0), ((-273 / 584), 3), ((-81 / 292), 5), ((-273 / 584), 7), ((-117 / 584), 10), ((19 / 73), 15), ((273 / 584), 19), ((53 / 584), 20), ((273 / 584), 23), ((91 / 584), 25), ((189 / 292), 30), ((-273 / 584), 31)],
      alternatingSixCyclotomicValue [((-7 / 146), 0), ((169 / 584), 3), ((69 / 584), 5), ((169 / 584), 7), ((-157 / 584), 10), ((-35 / 584), 15), ((-169 / 584), 19), ((-151 / 584), 20), ((-169 / 584), 23), ((-4 / 73), 25), ((131 / 584), 30), ((169 / 584), 31)],
      alternatingSixCyclotomicValue [((159 / 292), 0), ((41 / 73), 3), ((27 / 146), 5), ((41 / 73), 7), ((28 / 73), 10), ((-1 / 146), 15), ((-41 / 73), 19), ((31 / 292), 20), ((-41 / 73), 23), ((67 / 292), 25), ((5 / 73), 30), ((41 / 73), 31)],
      alternatingSixCyclotomicValue [((425 / 584), 0), ((16 / 73), 3), ((165 / 584), 5), ((16 / 73), 7), ((17 / 292), 10), ((-217 / 584), 15), ((-16 / 73), 19), ((-125 / 292), 20), ((-16 / 73), 23), ((-213 / 584), 25), ((-239 / 584), 30), ((16 / 73), 31)],
      alternatingSixCyclotomicValue [((-89 / 292), 0), ((-185 / 292), 3), ((-95 / 146), 5), ((-185 / 292), 7), ((-121 / 292), 10), ((53 / 292), 15), ((185 / 292), 19), ((237 / 292), 20), ((185 / 292), 23), ((159 / 292), 25), ((127 / 292), 30), ((-185 / 292), 31)]],
    ![alternatingSixCyclotomicValue [((6 / 73), 0), ((-175 / 584), 3), ((-87 / 584), 5), ((-175 / 584), 7), ((71 / 584), 10), ((133 / 584), 15), ((175 / 584), 19), ((-127 / 584), 20), ((175 / 584), 23), ((17 / 292), 25), ((-89 / 584), 30), ((-175 / 584), 31)],
      alternatingSixCyclotomicValue [((-87 / 584), 0), ((121 / 584), 3), ((-37 / 146), 5), ((121 / 584), 7), ((-115 / 584), 10), ((23 / 146), 15), ((-121 / 584), 19), ((107 / 584), 20), ((-121 / 584), 23), ((57 / 584), 25), ((-95 / 292), 30), ((121 / 584), 31)],
      alternatingSixCyclotomicValue [((-5 / 73), 0), ((85 / 584), 3), ((-183 / 584), 5), ((85 / 584), 7), ((99 / 584), 10), ((-123 / 584), 15), ((-85 / 584), 19), ((337 / 584), 20), ((-85 / 584), 23), ((-1 / 146), 25), ((-11 / 584), 30), ((85 / 584), 31)],
      alternatingSixCyclotomicValue [((-117 / 292), 0), ((-89 / 292), 3), ((25 / 292), 5), ((-89 / 292), 7), ((7 / 146), 10), ((91 / 292), 15), ((89 / 292), 19), ((13 / 292), 20), ((89 / 292), 23), ((-19 / 292), 25), ((-17 / 146), 30), ((-89 / 292), 31)],
      alternatingSixCyclotomicValue [((-175 / 584), 0), ((2 / 73), 3), ((121 / 584), 5), ((2 / 73), 7), ((33 / 146), 10), ((347 / 584), 15), ((-2 / 73), 19), ((15 / 146), 20), ((-2 / 73), 23), ((-127 / 584), 25), ((-185 / 584), 30), ((2 / 73), 31)],
      alternatingSixCyclotomicValue [((71 / 292), 0), ((-87 / 292), 3), ((31 / 292), 5), ((-87 / 292), 7), ((-3 / 146), 10), ((17 / 146), 15), ((87 / 292), 19), ((-81 / 146), 20), ((87 / 292), 23), ((-11 / 73), 25), ((-12 / 73), 30), ((-87 / 292), 31)]]
  ]

/-- The row 12 first generator in the checked diagonal basis. -/
def alternatingSixAmbientRow12TransformedGeneratorA :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((1 / 4), 5), ((-1 / 4), 10), ((1 / 4), 15)],
      alternatingSixCyclotomicValue [((-1 / 4), 3), ((1 / 2), 5), ((-1 / 4), 7), ((1 / 2), 10), ((1 / 2), 15), ((1 / 4), 19), ((1 / 4), 23), ((-1 / 4), 25), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 3), ((1 / 4), 7), ((-1 / 4), 15), ((-1 / 4), 19), ((-1 / 4), 20), ((-1 / 4), 23), ((-1 / 4), 30), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((19 / 146), 0), ((-11 / 292), 3), ((-59 / 146), 5), ((-11 / 292), 7), ((9 / 73), 10), ((13 / 146), 15), ((11 / 292), 19), ((-25 / 146), 20), ((11 / 292), 23), ((113 / 292), 25), ((-8 / 73), 30), ((-11 / 292), 31)],
      alternatingSixCyclotomicValue [((31 / 146), 0), ((-41 / 292), 3), ((-35 / 292), 5), ((-41 / 292), 7), ((101 / 292), 10), ((1 / 73), 15), ((41 / 292), 19), ((13 / 146), 20), ((41 / 292), 23), ((23 / 292), 25), ((-33 / 292), 30), ((-41 / 292), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 3), ((1 / 4), 7), ((-1 / 4), 19), ((1 / 4), 20), ((-1 / 4), 23), ((1 / 4), 31)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 3), ((-1 / 2), 7), ((1 / 4), 15), ((1 / 2), 19), ((1 / 2), 23), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 2), 10), ((-1 / 4), 15)],
      alternatingSixCyclotomicValue [((1 / 4), 3), ((-1 / 4), 5), ((1 / 4), 7), ((-1 / 4), 15), ((-1 / 4), 19), ((-1 / 4), 23), ((1 / 4), 25), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((31 / 292), 0), ((4 / 73), 3), ((23 / 73), 5), ((4 / 73), 7), ((7 / 146), 10), ((75 / 292), 15), ((-4 / 73), 19), ((-15 / 73), 20), ((-4 / 73), 23), ((12 / 73), 25), ((-63 / 146), 30), ((4 / 73), 31)],
      alternatingSixCyclotomicValue [((4 / 73), 0), ((-93 / 292), 3), ((-21 / 146), 5), ((-93 / 292), 7), ((23 / 73), 10), ((17 / 146), 15), ((93 / 292), 19), ((-71 / 292), 20), ((93 / 292), 23), ((159 / 292), 25), ((-171 / 292), 30), ((-93 / 292), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 20), ((1 / 4), 25)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 20), ((1 / 4), 25), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), (1, 3), ((1 / 2), 5), (1, 7), ((-1 / 4), 10), ((-1 / 2), 15), (-1, 19), ((-1 / 4), 20), (-1, 23), (1, 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 3), ((-1 / 4), 5), ((1 / 4), 7), ((-1 / 4), 10), ((-1 / 4), 19), ((-1 / 4), 23), ((1 / 4), 25), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((99 / 292), 0), ((75 / 146), 3), ((-25 / 146), 5), ((75 / 146), 7), ((113 / 292), 10), ((-91 / 146), 15), ((-75 / 146), 19), ((-15 / 292), 20), ((-75 / 146), 23), ((-67 / 146), 25), ((-17 / 73), 30), ((75 / 146), 31)],
      alternatingSixCyclotomicValue [((-69 / 292), 0), ((17 / 73), 3), ((13 / 146), 5), ((17 / 73), 7), ((23 / 292), 10), ((-101 / 292), 15), ((-17 / 73), 19), ((55 / 146), 20), ((-17 / 73), 23), ((-161 / 292), 25), ((79 / 146), 30), ((17 / 73), 31)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 4), 3), ((1 / 4), 5), ((-1 / 4), 7), ((-1 / 4), 10), ((1 / 4), 15), ((1 / 4), 19), ((1 / 4), 23), ((-1 / 4), 25), ((-1 / 4), 31)]],
    ![alternatingSixCyclotomicValue [((3 / 4), 3), ((3 / 4), 7), ((-3 / 4), 15), ((-3 / 4), 19), ((-3 / 4), 23), ((3 / 4), 25), ((3 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 3), ((1 / 2), 5), ((-1 / 4), 7), ((3 / 4), 15), ((1 / 4), 19), ((1 / 4), 23), ((1 / 4), 25), ((1 / 4), 30), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 10), ((-1 / 2), 20), ((1 / 2), 25), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-11 / 146), 0), ((-9 / 292), 3), ((-35 / 146), 5), ((-9 / 292), 7), ((14 / 73), 10), ((-65 / 292), 15), ((9 / 292), 19), ((13 / 73), 20), ((9 / 292), 23), ((-27 / 292), 25), ((7 / 292), 30), ((-9 / 292), 31)],
      alternatingSixCyclotomicValue [((16 / 73), 0), ((33 / 146), 3), ((51 / 292), 5), ((33 / 146), 7), ((-35 / 146), 10), ((-83 / 292), 15), ((-33 / 146), 19), ((2 / 73), 20), ((-33 / 146), 23), ((13 / 73), 25), ((23 / 146), 30), ((33 / 146), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 10), ((1 / 4), 25), ((-1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 4), 5), ((1 / 4), 10), ((1 / 4), 15)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 4), 3), ((-1 / 2), 5), ((1 / 4), 7), ((1 / 2), 10), ((1 / 2), 15), ((-1 / 4), 19), ((1 / 2), 20), ((-1 / 4), 23), ((3 / 4), 25), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 3), ((-1 / 4), 7), ((1 / 2), 10), ((-1 / 4), 15), ((1 / 4), 19), ((-1 / 4), 20), ((1 / 4), 23), ((-1 / 2), 25), ((-1 / 4), 30), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((-19 / 73), 0), ((95 / 292), 3), ((45 / 146), 5), ((95 / 292), 7), ((-18 / 73), 10), ((47 / 146), 15), ((-95 / 292), 19), ((25 / 73), 20), ((-95 / 292), 23), ((-7 / 292), 25), ((16 / 73), 30), ((95 / 292), 31)],
      alternatingSixCyclotomicValue [((11 / 146), 0), ((9 / 292), 3), ((-3 / 292), 5), ((9 / 292), 7), ((-129 / 292), 10), ((-2 / 73), 15), ((-9 / 292), 19), ((-13 / 73), 20), ((-9 / 292), 23), ((27 / 292), 25), ((-7 / 292), 30), ((9 / 292), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 3), ((1 / 4), 7), ((-1 / 4), 19), ((-1 / 4), 20), ((-1 / 4), 23), ((1 / 2), 30), ((1 / 4), 31)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 20), ((1 / 4), 25)],
      alternatingSixCyclotomicValue [((-3 / 4), 0), ((-1 / 2), 5), ((-3 / 4), 10), ((-1 / 2), 15), ((-1 / 4), 20), ((-1 / 2), 25)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 3), ((1 / 4), 5), ((-1 / 4), 7), ((-1 / 4), 10), ((1 / 2), 15), ((1 / 4), 19), ((1 / 2), 20), ((1 / 4), 23), ((1 / 4), 25), ((1 / 2), 30), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((-61 / 292), 0), ((29 / 146), 3), ((39 / 146), 5), ((29 / 146), 7), ((-77 / 292), 10), ((31 / 146), 15), ((-29 / 146), 19), ((-35 / 292), 20), ((-29 / 146), 23), ((7 / 73), 25), ((9 / 73), 30), ((29 / 146), 31)],
      alternatingSixCyclotomicValue [((-15 / 292), 0), ((-9 / 73), 3), ((3 / 73), 5), ((-9 / 73), 7), ((5 / 292), 10), ((105 / 292), 15), ((9 / 73), 19), ((-21 / 73), 20), ((9 / 73), 23), ((111 / 292), 25), ((-59 / 146), 30), ((-9 / 73), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 3), ((1 / 4), 5), ((-1 / 4), 7), ((1 / 4), 10), ((1 / 4), 15), ((1 / 4), 19), ((1 / 4), 23), ((-1 / 4), 25), ((-1 / 4), 31)]]
  ]

macro "close_cyclotomic_row12" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)


private theorem row12_eigenbasisInverse_mul_0_0 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        0 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((211 / 584) : ℂ) + ((283 / 584) : ℂ) * ζ ^ 3 + ((211 / 584) : ℂ) * ζ ^ 4 + ((3 / 292) : ℂ) * ζ ^ 5 + ((101 / 292) : ℂ) * ζ ^ 6 - ((41 / 292) : ℂ) * ζ ^ 8 - ((3 / 292) : ℂ) * ζ ^ 9 + ((83 / 292) : ℂ) * ζ ^ 10 - ((9 / 584) : ℂ) * ζ ^ 13 + ((9 / 146) : ℂ) * ζ ^ 14 + ((59 / 292) : ℂ) * ζ ^ 15 + ((33 / 584) : ℂ) * ζ ^ 18 - ((59 / 292) : ℂ) * ζ ^ 19 + ((9 / 292) : ℂ) * ζ ^ 20 - ((101 / 292) : ℂ) * ζ ^ 22 - ((29 / 584) : ℂ) * ζ ^ 23 - ((9 / 292) : ℂ) * ζ ^ 24 + ((159 / 584) : ℂ) * ζ ^ 25 - ((101 / 292) : ℂ) * ζ ^ 26 - ((49 / 292) : ℂ) * ζ ^ 28 - ((159 / 584) : ℂ) * ζ ^ 29 + ((101 / 292) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_0_1 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        0 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((55 / 292) : ℂ) + ((21 / 292) : ℂ) * ζ ^ 3 + ((55 / 292) : ℂ) * ζ ^ 4 + ((121 / 292) : ℂ) * ζ ^ 5 + ((63 / 584) : ℂ) * ζ ^ 6 - ((15 / 584) : ℂ) * ζ ^ 8 - ((121 / 292) : ℂ) * ζ ^ 9 + ((3 / 8) : ℂ) * ζ ^ 10 + ((389 / 584) : ℂ) * ζ ^ 13 - ((39 / 146) : ℂ) * ζ ^ 14 - ((85 / 584) : ℂ) * ζ ^ 15 - ((91 / 584) : ℂ) * ζ ^ 18 + ((85 / 584) : ℂ) * ζ ^ 19 - ((53 / 292) : ℂ) * ζ ^ 20 - ((63 / 584) : ℂ) * ζ ^ 22 - ((43 / 292) : ℂ) * ζ ^ 23 + ((53 / 292) : ℂ) * ζ ^ 24 - ((149 / 584) : ℂ) * ζ ^ 25 - ((63 / 584) : ℂ) * ζ ^ 26 - ((115 / 584) : ℂ) * ζ ^ 28 + ((149 / 584) : ℂ) * ζ ^ 29 + ((63 / 584) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_0_2 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        0 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((659 / 1168) : ℂ) + ((555 / 1168) : ℂ) * ζ ^ 3 - ((659 / 1168) : ℂ) * ζ ^ 4 + ((135 / 1168) : ℂ) * ζ ^ 5 + ((137 / 1168) : ℂ) * ζ ^ 6 + ((167 / 584) : ℂ) * ζ ^ 8 - ((135 / 1168) : ℂ) * ζ ^ 9 - ((91 / 1168) : ℂ) * ζ ^ 10 + ((319 / 1168) : ℂ) * ζ ^ 13 + ((57 / 292) : ℂ) * ζ ^ 14 + ((661 / 1168) : ℂ) * ζ ^ 15 - ((11 / 292) : ℂ) * ζ ^ 18 - ((661 / 1168) : ℂ) * ζ ^ 19 - ((33 / 292) : ℂ) * ζ ^ 20 - ((137 / 1168) : ℂ) * ζ ^ 22 + ((411 / 1168) : ℂ) * ζ ^ 23 + ((33 / 292) : ℂ) * ζ ^ 24 + ((235 / 1168) : ℂ) * ζ ^ 25 - ((137 / 1168) : ℂ) * ζ ^ 26 + ((115 / 1168) : ℂ) * ζ ^ 28 - ((235 / 1168) : ℂ) * ζ ^ 29 + ((137 / 1168) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_0_3 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        0 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((1354 / 5329) : ℂ) - ((453 / 42632) : ℂ) * ζ ^ 3 + ((1354 / 5329) : ℂ) * ζ ^ 4 + ((1951 / 21316) : ℂ) * ζ ^ 5 + ((2787 / 21316) : ℂ) * ζ ^ 6 + ((4397 / 42632) : ℂ) * ζ ^ 8 - ((1951 / 21316) : ℂ) * ζ ^ 9 + ((17713 / 42632) : ℂ) * ζ ^ 10 - ((969 / 21316) : ℂ) * ζ ^ 13 - ((12139 / 42632) : ℂ) * ζ ^ 14 + ((1329 / 42632) : ℂ) * ζ ^ 15 + ((23673 / 42632) : ℂ) * ζ ^ 18 - ((1329 / 42632) : ℂ) * ζ ^ 19 + ((9619 / 42632) : ℂ) * ζ ^ 20 - ((2787 / 21316) : ℂ) * ζ ^ 22 - ((715 / 42632) : ℂ) * ζ ^ 23 - ((9619 / 42632) : ℂ) * ζ ^ 24 - ((3537 / 42632) : ℂ) * ζ ^ 25 - ((2787 / 21316) : ℂ) * ζ ^ 26 + ((697 / 5329) : ℂ) * ζ ^ 28 + ((3537 / 42632) : ℂ) * ζ ^ 29 + ((2787 / 21316) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_0_4 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        0 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((20437 / 85264) : ℂ) + ((32559 / 85264) : ℂ) * ζ ^ 3 - ((20437 / 85264) : ℂ) * ζ ^ 4 + ((29081 / 85264) : ℂ) * ζ ^ 5 - ((14665 / 85264) : ℂ) * ζ ^ 6 - ((7887 / 42632) : ℂ) * ζ ^ 8 - ((29081 / 85264) : ℂ) * ζ ^ 9 - ((6651 / 85264) : ℂ) * ζ ^ 10 + ((11561 / 85264) : ℂ) * ζ ^ 13 - ((4007 / 42632) : ℂ) * ζ ^ 14 - ((26135 / 85264) : ℂ) * ζ ^ 15 + ((15541 / 42632) : ℂ) * ζ ^ 18 + ((26135 / 85264) : ℂ) * ζ ^ 19 - ((5145 / 21316) : ℂ) * ζ ^ 20 + ((14665 / 85264) : ℂ) * ζ ^ 22 - ((27303 / 85264) : ℂ) * ζ ^ 23 + ((5145 / 21316) : ℂ) * ζ ^ 24 - ((37257 / 85264) : ℂ) * ζ ^ 25 + ((14665 / 85264) : ℂ) * ζ ^ 26 + ((16209 / 85264) : ℂ) * ζ ^ 28 + ((37257 / 85264) : ℂ) * ζ ^ 29 - ((14665 / 85264) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_0_5 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        0 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((231 / 584) : ℂ) + ((123 / 292) : ℂ) * ζ ^ 3 - ((231 / 584) : ℂ) * ζ ^ 4 + ((16 / 73) : ℂ) * ζ ^ 5 + ((39 / 584) : ℂ) * ζ ^ 6 + ((137 / 584) : ℂ) * ζ ^ 8 - ((16 / 73) : ℂ) * ζ ^ 9 + ((71 / 584) : ℂ) * ζ ^ 10 - ((5 / 146) : ℂ) * ζ ^ 13 - ((4 / 73) : ℂ) * ζ ^ 14 - ((93 / 292) : ℂ) * ζ ^ 15 - ((41 / 584) : ℂ) * ζ ^ 18 + ((93 / 292) : ℂ) * ζ ^ 19 + ((8 / 73) : ℂ) * ζ ^ 20 - ((39 / 584) : ℂ) * ζ ^ 22 - ((227 / 584) : ℂ) * ζ ^ 23 - ((8 / 73) : ℂ) * ζ ^ 24 + ((5 / 292) : ℂ) * ζ ^ 25 - ((39 / 584) : ℂ) * ζ ^ 26 + ((57 / 584) : ℂ) * ζ ^ 28 - ((5 / 292) : ℂ) * ζ ^ 29 + ((39 / 584) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_1_0 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        1 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((95 / 584) : ℂ) - ((22 / 73) : ℂ) * ζ ^ 3 + ((95 / 584) : ℂ) * ζ ^ 4 - ((63 / 292) : ℂ) * ζ ^ 5 + ((65 / 584) : ℂ) * ζ ^ 6 - ((103 / 584) : ℂ) * ζ ^ 8 + ((63 / 292) : ℂ) * ζ ^ 9 - ((55 / 584) : ℂ) * ζ ^ 10 - ((15 / 292) : ℂ) * ζ ^ 13 + ((15 / 73) : ℂ) * ζ ^ 14 + ((77 / 584) : ℂ) * ζ ^ 15 - ((9 / 146) : ℂ) * ζ ^ 18 - ((77 / 584) : ℂ) * ζ ^ 19 - ((13 / 584) : ℂ) * ζ ^ 20 - ((65 / 584) : ℂ) * ζ ^ 22 + ((49 / 292) : ℂ) * ζ ^ 23 + ((13 / 584) : ℂ) * ζ ^ 24 - ((273 / 584) : ℂ) * ζ ^ 25 - ((65 / 584) : ℂ) * ζ ^ 26 + ((20 / 73) : ℂ) * ζ ^ 28 + ((273 / 584) : ℂ) * ζ ^ 29 + ((65 / 584) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_1_1 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        1 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((47 / 584) : ℂ) + ((143 / 292) : ℂ) * ζ ^ 3 - ((47 / 584) : ℂ) * ζ ^ 4 - ((337 / 584) : ℂ) * ζ ^ 5 - ((155 / 584) : ℂ) * ζ ^ 6 - ((171 / 292) : ℂ) * ζ ^ 8 + ((337 / 584) : ℂ) * ζ ^ 9 + ((1 / 8) : ℂ) * ζ ^ 10 + ((153 / 584) : ℂ) * ζ ^ 13 - ((57 / 146) : ℂ) * ζ ^ 14 + ((63 / 146) : ℂ) * ζ ^ 15 - ((133 / 584) : ℂ) * ζ ^ 18 - ((63 / 146) : ℂ) * ζ ^ 19 + ((9 / 146) : ℂ) * ζ ^ 20 + ((155 / 584) : ℂ) * ζ ^ 22 + ((319 / 292) : ℂ) * ζ ^ 23 - ((9 / 146) : ℂ) * ζ ^ 24 + ((63 / 584) : ℂ) * ζ ^ 25 + ((155 / 584) : ℂ) * ζ ^ 26 + ((225 / 584) : ℂ) * ζ ^ 28 - ((63 / 584) : ℂ) * ζ ^ 29 - ((155 / 584) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_1_2 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        1 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((47 / 292) : ℂ) + ((49 / 584) : ℂ) * ζ ^ 3 + ((47 / 292) : ℂ) * ζ ^ 4 - ((35 / 146) : ℂ) * ζ ^ 5 + ((29 / 292) : ℂ) * ζ ^ 6 + ((67 / 1168) : ℂ) * ζ ^ 8 + ((35 / 146) : ℂ) * ζ ^ 9 - ((15 / 292) : ℂ) * ζ ^ 10 + ((45 / 584) : ℂ) * ζ ^ 13 + ((11 / 73) : ℂ) * ζ ^ 14 + ((177 / 584) : ℂ) * ζ ^ 15 - ((171 / 1168) : ℂ) * ζ ^ 18 - ((177 / 584) : ℂ) * ζ ^ 19 - ((293 / 584) : ℂ) * ζ ^ 20 - ((29 / 292) : ℂ) * ζ ^ 22 - ((59 / 292) : ℂ) * ζ ^ 23 + ((293 / 584) : ℂ) * ζ ^ 24 - ((95 / 584) : ℂ) * ζ ^ 25 - ((29 / 292) : ℂ) * ζ ^ 26 - ((225 / 1168) : ℂ) * ζ ^ 28 + ((95 / 584) : ℂ) * ζ ^ 29 + ((29 / 292) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_1_3 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        1 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((12777 / 21316) : ℂ) - ((123 / 42632) : ℂ) * ζ ^ 3 - ((12777 / 21316) : ℂ) * ζ ^ 4 - ((13687 / 42632) : ℂ) * ζ ^ 5 - ((7335 / 42632) : ℂ) * ζ ^ 6 - ((2401 / 42632) : ℂ) * ζ ^ 8 + ((13687 / 42632) : ℂ) * ζ ^ 9 - ((4184 / 5329) : ℂ) * ζ ^ 10 - ((3513 / 10658) : ℂ) * ζ ^ 13 + ((26137 / 42632) : ℂ) * ζ ^ 14 - ((1180 / 5329) : ℂ) * ζ ^ 15 - ((3112 / 5329) : ℂ) * ζ ^ 18 + ((1180 / 5329) : ℂ) * ζ ^ 19 - ((4315 / 42632) : ℂ) * ζ ^ 20 + ((7335 / 42632) : ℂ) * ζ ^ 22 + ((2605 / 42632) : ℂ) * ζ ^ 23 + ((4315 / 42632) : ℂ) * ζ ^ 24 - ((1497 / 42632) : ℂ) * ζ ^ 25 + ((7335 / 42632) : ℂ) * ζ ^ 26 - ((621 / 5329) : ℂ) * ζ ^ 28 + ((1497 / 42632) : ℂ) * ζ ^ 29 - ((7335 / 42632) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_1_4 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        1 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((2791 / 10658) : ℂ) + ((1737 / 5329) : ℂ) * ζ ^ 3 - ((2791 / 10658) : ℂ) * ζ ^ 4 - ((5649 / 42632) : ℂ) * ζ ^ 5 - ((8479 / 42632) : ℂ) * ζ ^ 6 + ((5163 / 85264) : ℂ) * ζ ^ 8 + ((5649 / 42632) : ℂ) * ζ ^ 9 - ((13567 / 42632) : ℂ) * ζ ^ 10 + ((337 / 42632) : ℂ) * ζ ^ 13 + ((636 / 5329) : ℂ) * ζ ^ 14 + ((15523 / 42632) : ℂ) * ζ ^ 15 + ((7855 / 85264) : ℂ) * ζ ^ 18 - ((15523 / 42632) : ℂ) * ζ ^ 19 + ((959 / 42632) : ℂ) * ζ ^ 20 + ((8479 / 42632) : ℂ) * ζ ^ 22 + ((3607 / 10658) : ℂ) * ζ ^ 23 - ((959 / 42632) : ℂ) * ζ ^ 24 + ((13811 / 21316) : ℂ) * ζ ^ 25 + ((8479 / 42632) : ℂ) * ζ ^ 26 - ((13203 / 85264) : ℂ) * ζ ^ 28 - ((13811 / 21316) : ℂ) * ζ ^ 29 - ((8479 / 42632) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_1_5 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        1 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((5 / 73) : ℂ) + ((163 / 584) : ℂ) * ζ ^ 3 - ((5 / 73) : ℂ) * ζ ^ 4 + ((29 / 73) : ℂ) * ζ ^ 5 + ((57 / 584) : ℂ) * ζ ^ 6 + ((131 / 292) : ℂ) * ζ ^ 8 - ((29 / 73) : ℂ) * ζ ^ 9 + ((21 / 292) : ℂ) * ζ ^ 10 + ((105 / 146) : ℂ) * ζ ^ 13 + ((15 / 584) : ℂ) * ζ ^ 14 + ((475 / 584) : ℂ) * ζ ^ 15 + ((29 / 292) : ℂ) * ζ ^ 18 - ((475 / 584) : ℂ) * ζ ^ 19 - ((249 / 584) : ℂ) * ζ ^ 20 - ((57 / 584) : ℂ) * ζ ^ 22 + ((241 / 584) : ℂ) * ζ ^ 23 + ((249 / 584) : ℂ) * ζ ^ 24 + ((41 / 292) : ℂ) * ζ ^ 25 - ((57 / 584) : ℂ) * ζ ^ 26 - ((175 / 584) : ℂ) * ζ ^ 28 - ((41 / 292) : ℂ) * ζ ^ 29 + ((57 / 584) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_2_0 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        2 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((267 / 584) : ℂ) + ((311 / 584) : ℂ) * ζ ^ 3 - ((267 / 584) : ℂ) * ζ ^ 4 - ((55 / 292) : ℂ) * ζ ^ 5 + ((117 / 584) : ℂ) * ζ ^ 6 + ((603 / 584) : ℂ) * ζ ^ 8 + ((55 / 292) : ℂ) * ζ ^ 9 - ((99 / 584) : ℂ) * ζ ^ 10 + ((119 / 292) : ℂ) * ζ ^ 13 + ((27 / 73) : ℂ) * ζ ^ 14 - ((11 / 292) : ℂ) * ζ ^ 15 + ((125 / 584) : ℂ) * ζ ^ 18 + ((11 / 292) : ℂ) * ζ ^ 19 + ((327 / 584) : ℂ) * ζ ^ 20 - ((117 / 584) : ℂ) * ζ ^ 22 + ((59 / 292) : ℂ) * ζ ^ 23 - ((327 / 584) : ℂ) * ζ ^ 24 + ((39 / 292) : ℂ) * ζ ^ 25 - ((117 / 584) : ℂ) * ζ ^ 26 + ((36 / 73) : ℂ) * ζ ^ 28 - ((39 / 292) : ℂ) * ζ ^ 29 + ((117 / 584) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_2_1 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        2 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((111 / 292) : ℂ) + ((53 / 292) : ℂ) * ζ ^ 3 + ((111 / 292) : ℂ) * ζ ^ 4 - ((77 / 292) : ℂ) * ζ ^ 5 + ((597 / 584) : ℂ) * ζ ^ 6 + ((129 / 584) : ℂ) * ζ ^ 8 + ((77 / 292) : ℂ) * ζ ^ 9 + ((5 / 8) : ℂ) * ζ ^ 10 - ((75 / 584) : ℂ) * ζ ^ 13 + ((29 / 73) : ℂ) * ζ ^ 14 + ((147 / 584) : ℂ) * ζ ^ 15 - ((181 / 584) : ℂ) * ζ ^ 18 - ((147 / 584) : ℂ) * ζ ^ 19 + ((30 / 73) : ℂ) * ζ ^ 20 - ((597 / 584) : ℂ) * ζ ^ 22 + ((107 / 292) : ℂ) * ζ ^ 23 - ((30 / 73) : ℂ) * ζ ^ 24 + ((201 / 584) : ℂ) * ζ ^ 25 - ((597 / 584) : ℂ) * ζ ^ 26 - ((33 / 584) : ℂ) * ζ ^ 28 - ((201 / 584) : ℂ) * ζ ^ 29 + ((597 / 584) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_2_2 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        2 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((499 / 1168) : ℂ) + ((337 / 1168) : ℂ) * ζ ^ 3 + ((499 / 1168) : ℂ) * ζ ^ 4 + ((299 / 1168) : ℂ) * ζ ^ 5 + ((19 / 1168) : ℂ) * ζ ^ 6 + ((63 / 292) : ℂ) * ζ ^ 8 - ((299 / 1168) : ℂ) * ζ ^ 9 + ((403 / 1168) : ℂ) * ζ ^ 10 + ((527 / 1168) : ℂ) * ζ ^ 13 - ((24 / 73) : ℂ) * ζ ^ 14 + ((389 / 1168) : ℂ) * ζ ^ 15 + ((87 / 584) : ℂ) * ζ ^ 18 - ((389 / 1168) : ℂ) * ζ ^ 19 - ((13 / 73) : ℂ) * ζ ^ 20 - ((19 / 1168) : ℂ) * ζ ^ 22 - ((89 / 1168) : ℂ) * ζ ^ 23 + ((13 / 73) : ℂ) * ζ ^ 24 + ((315 / 1168) : ℂ) * ζ ^ 25 - ((19 / 1168) : ℂ) * ζ ^ 26 - ((259 / 1168) : ℂ) * ζ ^ 28 - ((315 / 1168) : ℂ) * ζ ^ 29 + ((19 / 1168) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_2_3 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        2 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((751 / 5329) : ℂ) - ((22939 / 42632) : ℂ) * ζ ^ 3 + ((751 / 5329) : ℂ) * ζ ^ 4 - ((3491 / 10658) : ℂ) * ζ ^ 5 + ((5261 / 21316) : ℂ) * ζ ^ 6 - ((2745 / 42632) : ℂ) * ζ ^ 8 + ((3491 / 10658) : ℂ) * ζ ^ 9 - ((16581 / 42632) : ℂ) * ζ ^ 10 - ((2001 / 5329) : ℂ) * ζ ^ 13 + ((27103 / 42632) : ℂ) * ζ ^ 14 - ((42469 / 42632) : ℂ) * ζ ^ 15 - ((8269 / 42632) : ℂ) * ζ ^ 18 + ((42469 / 42632) : ℂ) * ζ ^ 19 - ((5431 / 42632) : ℂ) * ζ ^ 20 - ((5261 / 21316) : ℂ) * ζ ^ 22 - ((8597 / 42632) : ℂ) * ζ ^ 23 + ((5431 / 42632) : ℂ) * ζ ^ 24 - ((17061 / 42632) : ℂ) * ζ ^ 25 - ((5261 / 21316) : ℂ) * ζ ^ 26 - ((469 / 10658) : ℂ) * ζ ^ 28 + ((17061 / 42632) : ℂ) * ζ ^ 29 + ((5261 / 21316) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_2_4 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        2 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((65755 / 85264) : ℂ) + ((24753 / 85264) : ℂ) * ζ ^ 3 - ((65755 / 85264) : ℂ) * ζ ^ 4 + ((49437 / 85264) : ℂ) * ζ ^ 5 + ((1289 / 85264) : ℂ) * ζ ^ 6 + ((3203 / 21316) : ℂ) * ζ ^ 8 - ((49437 / 85264) : ℂ) * ζ ^ 9 - ((1873 / 85264) : ℂ) * ζ ^ 10 + ((381 / 85264) : ℂ) * ζ ^ 13 + ((1581 / 42632) : ℂ) * ζ ^ 14 + ((9265 / 85264) : ℂ) * ζ ^ 15 + ((2677 / 21316) : ℂ) * ζ ^ 18 - ((9265 / 85264) : ℂ) * ζ ^ 19 + ((5265 / 21316) : ℂ) * ζ ^ 20 - ((1289 / 85264) : ℂ) * ζ ^ 22 + ((14813 / 85264) : ℂ) * ζ ^ 23 - ((5265 / 21316) : ℂ) * ζ ^ 24 - ((2133 / 85264) : ℂ) * ζ ^ 25 - ((1289 / 85264) : ℂ) * ζ ^ 26 + ((9727 / 85264) : ℂ) * ζ ^ 28 + ((2133 / 85264) : ℂ) * ζ ^ 29 + ((1289 / 85264) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_2_5 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        2 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((437 / 584) : ℂ) + ((77 / 146) : ℂ) * ζ ^ 3 - ((437 / 584) : ℂ) * ζ ^ 4 + ((119 / 146) : ℂ) * ζ ^ 5 + ((11 / 73) : ℂ) * ζ ^ 6 + ((169 / 146) : ℂ) * ζ ^ 8 - ((119 / 146) : ℂ) * ζ ^ 9 + ((213 / 292) : ℂ) * ζ ^ 10 + ((391 / 584) : ℂ) * ζ ^ 13 - ((169 / 292) : ℂ) * ζ ^ 14 + ((13 / 146) : ℂ) * ζ ^ 15 + ((411 / 584) : ℂ) * ζ ^ 18 - ((13 / 146) : ℂ) * ζ ^ 19 - ((127 / 584) : ℂ) * ζ ^ 20 - ((11 / 73) : ℂ) * ζ ^ 22 + ((49 / 292) : ℂ) * ζ ^ 23 + ((127 / 584) : ℂ) * ζ ^ 24 - ((13 / 584) : ℂ) * ζ ^ 25 - ((11 / 73) : ℂ) * ζ ^ 26 - ((315 / 584) : ℂ) * ζ ^ 28 + ((13 / 584) : ℂ) * ζ ^ 29 + ((11 / 73) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_3_0 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        3 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((123 / 584) : ℂ) - ((273 / 292) : ℂ) * ζ ^ 3 + ((123 / 584) : ℂ) * ζ ^ 4 + ((91 / 146) : ℂ) * ζ ^ 5 - ((29 / 292) : ℂ) * ζ ^ 6 - ((327 / 584) : ℂ) * ζ ^ 8 - ((91 / 146) : ℂ) * ζ ^ 9 + ((459 / 584) : ℂ) * ζ ^ 10 + ((19 / 292) : ℂ) * ζ ^ 13 - ((517 / 584) : ℂ) * ζ ^ 14 - ((263 / 584) : ℂ) * ζ ^ 15 - ((47 / 146) : ℂ) * ζ ^ 18 + ((263 / 584) : ℂ) * ζ ^ 19 - ((111 / 292) : ℂ) * ζ ^ 20 + ((29 / 292) : ℂ) * ζ ^ 22 - ((101 / 292) : ℂ) * ζ ^ 23 + ((111 / 292) : ℂ) * ζ ^ 24 + ((83 / 584) : ℂ) * ζ ^ 25 + ((29 / 292) : ℂ) * ζ ^ 26 - ((227 / 584) : ℂ) * ζ ^ 28 - ((83 / 584) : ℂ) * ζ ^ 29 - ((29 / 292) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_3_1 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        3 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((67 / 584) : ℂ) - ((93 / 146) : ℂ) * ζ ^ 3 - ((67 / 584) : ℂ) * ζ ^ 4 + ((57 / 584) : ℂ) * ζ ^ 5 - ((339 / 584) : ℂ) * ζ ^ 6 - ((163 / 292) : ℂ) * ζ ^ 8 - ((57 / 584) : ℂ) * ζ ^ 9 - ((9 / 8) : ℂ) * ζ ^ 10 - ((515 / 584) : ℂ) * ζ ^ 13 + ((159 / 292) : ℂ) * ζ ^ 14 - ((91 / 73) : ℂ) * ζ ^ 15 - ((289 / 584) : ℂ) * ζ ^ 18 + ((91 / 73) : ℂ) * ζ ^ 19 - ((417 / 292) : ℂ) * ζ ^ 20 + ((339 / 584) : ℂ) * ζ ^ 22 - ((185 / 146) : ℂ) * ζ ^ 23 + ((417 / 292) : ℂ) * ζ ^ 24 - ((547 / 584) : ℂ) * ζ ^ 25 + ((339 / 584) : ℂ) * ζ ^ 26 - ((285 / 584) : ℂ) * ζ ^ 28 + ((547 / 584) : ℂ) * ζ ^ 29 - ((339 / 584) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_3_2 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        3 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((35 / 73) : ℂ) - ((393 / 584) : ℂ) * ζ ^ 3 + ((35 / 73) : ℂ) * ζ ^ 4 - ((139 / 584) : ℂ) * ζ ^ 5 + ((165 / 584) : ℂ) * ζ ^ 6 - ((1029 / 1168) : ℂ) * ζ ^ 8 + ((139 / 584) : ℂ) * ζ ^ 9 - ((27 / 146) : ℂ) * ζ ^ 10 - ((495 / 584) : ℂ) * ζ ^ 13 + ((273 / 584) : ℂ) * ζ ^ 14 - ((207 / 292) : ℂ) * ζ ^ 15 - ((17 / 1168) : ℂ) * ζ ^ 18 + ((207 / 292) : ℂ) * ζ ^ 19 + ((21 / 146) : ℂ) * ζ ^ 20 - ((165 / 584) : ℂ) * ζ ^ 22 + ((57 / 584) : ℂ) * ζ ^ 23 - ((21 / 146) : ℂ) * ζ ^ 24 + ((12 / 73) : ℂ) * ζ ^ 25 - ((165 / 584) : ℂ) * ζ ^ 26 + ((139 / 1168) : ℂ) * ζ ^ 28 - ((12 / 73) : ℂ) * ζ ^ 29 + ((165 / 584) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_3_3 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        3 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((9001 / 21316) : ℂ) + ((15515 / 42632) : ℂ) * ζ ^ 3 + ((9001 / 21316) : ℂ) * ζ ^ 4 + ((28063 / 42632) : ℂ) * ζ ^ 5 + ((12941 / 42632) : ℂ) * ζ ^ 6 + ((5825 / 42632) : ℂ) * ζ ^ 8 - ((28063 / 42632) : ℂ) * ζ ^ 9 + ((27511 / 21316) : ℂ) * ζ ^ 10 + ((3298 / 5329) : ℂ) * ζ ^ 13 - ((42081 / 42632) : ℂ) * ζ ^ 14 + ((14033 / 21316) : ℂ) * ζ ^ 15 + ((1382 / 5329) : ℂ) * ζ ^ 18 - ((14033 / 21316) : ℂ) * ζ ^ 19 + ((11549 / 42632) : ℂ) * ζ ^ 20 - ((12941 / 42632) : ℂ) * ζ ^ 22 - ((1499 / 42632) : ℂ) * ζ ^ 23 - ((11549 / 42632) : ℂ) * ζ ^ 24 - ((1929 / 42632) : ℂ) * ζ ^ 25 - ((12941 / 42632) : ℂ) * ζ ^ 26 - ((1511 / 21316) : ℂ) * ζ ^ 28 + ((1929 / 42632) : ℂ) * ζ ^ 29 + ((12941 / 42632) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_3_4 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        3 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((25997 / 21316) : ℂ) - ((19999 / 21316) : ℂ) * ζ ^ 3 + ((25997 / 21316) : ℂ) * ζ ^ 4 - ((16271 / 21316) : ℂ) * ζ ^ 5 + ((2926 / 5329) : ℂ) * ζ ^ 6 - ((10657 / 85264) : ℂ) * ζ ^ 8 + ((16271 / 21316) : ℂ) * ζ ^ 9 - ((5523 / 42632) : ℂ) * ζ ^ 10 - ((8671 / 42632) : ℂ) * ζ ^ 13 + ((28931 / 42632) : ℂ) * ζ ^ 14 - ((1844 / 5329) : ℂ) * ζ ^ 15 - ((58227 / 85264) : ℂ) * ζ ^ 18 + ((1844 / 5329) : ℂ) * ζ ^ 19 + ((593 / 10658) : ℂ) * ζ ^ 20 - ((2926 / 5329) : ℂ) * ζ ^ 22 - ((11467 / 42632) : ℂ) * ζ ^ 23 - ((593 / 10658) : ℂ) * ζ ^ 24 - ((14397 / 42632) : ℂ) * ζ ^ 25 - ((2926 / 5329) : ℂ) * ζ ^ 26 - ((3687 / 85264) : ℂ) * ζ ^ 28 + ((14397 / 42632) : ℂ) * ζ ^ 29 + ((2926 / 5329) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_3_5 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        3 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((183 / 146) : ℂ) - ((1063 / 584) : ℂ) * ζ ^ 3 + ((183 / 146) : ℂ) * ζ ^ 4 - ((327 / 292) : ℂ) * ζ ^ 5 - ((131 / 292) : ℂ) * ζ ^ 6 - ((565 / 292) : ℂ) * ζ ^ 8 + ((327 / 292) : ℂ) * ζ ^ 9 - ((76 / 73) : ℂ) * ζ ^ 10 - ((339 / 292) : ℂ) * ζ ^ 13 + ((173 / 292) : ℂ) * ζ ^ 14 - ((553 / 584) : ℂ) * ζ ^ 15 - ((123 / 146) : ℂ) * ζ ^ 18 + ((553 / 584) : ℂ) * ζ ^ 19 + ((23 / 73) : ℂ) * ζ ^ 20 + ((131 / 292) : ℂ) * ζ ^ 22 + ((269 / 584) : ℂ) * ζ ^ 23 - ((23 / 73) : ℂ) * ζ ^ 24 - ((13 / 292) : ℂ) * ζ ^ 25 + ((131 / 292) : ℂ) * ζ ^ 26 + ((49 / 73) : ℂ) * ζ ^ 28 + ((13 / 292) : ℂ) * ζ ^ 29 - ((131 / 292) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_4_0 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        4 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((285 / 584) : ℂ) - ((601 / 584) : ℂ) * ζ ^ 3 + ((285 / 584) : ℂ) * ζ ^ 4 - ((43 / 292) : ℂ) * ζ ^ 5 - ((231 / 292) : ℂ) * ζ ^ 6 - ((191 / 292) : ℂ) * ζ ^ 8 + ((43 / 292) : ℂ) * ζ ^ 9 - ((48 / 73) : ℂ) * ζ ^ 10 - ((163 / 584) : ℂ) * ζ ^ 13 - ((39 / 292) : ℂ) * ζ ^ 14 + ((3 / 146) : ℂ) * ζ ^ 15 - ((35 / 584) : ℂ) * ζ ^ 18 - ((3 / 146) : ℂ) * ζ ^ 19 + ((17 / 292) : ℂ) * ζ ^ 20 + ((231 / 292) : ℂ) * ζ ^ 22 - ((71 / 584) : ℂ) * ζ ^ 23 - ((17 / 292) : ℂ) * ζ ^ 24 - ((235 / 584) : ℂ) * ζ ^ 25 + ((231 / 292) : ℂ) * ζ ^ 26 + ((21 / 292) : ℂ) * ζ ^ 28 + ((235 / 584) : ℂ) * ζ ^ 29 - ((231 / 292) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_4_1 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        4 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((253 / 292) : ℂ) - ((9 / 292) : ℂ) * ζ ^ 3 - ((253 / 292) : ℂ) * ζ ^ 4 - ((31 / 292) : ℂ) * ζ ^ 5 - ((611 / 584) : ℂ) * ζ ^ 6 - ((369 / 584) : ℂ) * ζ ^ 8 + ((31 / 292) : ℂ) * ζ ^ 9 - ((7 / 8) : ℂ) * ζ ^ 10 - ((271 / 584) : ℂ) * ζ ^ 13 - ((25 / 146) : ℂ) * ζ ^ 14 - ((193 / 584) : ℂ) * ζ ^ 15 - ((253 / 584) : ℂ) * ζ ^ 18 + ((193 / 584) : ℂ) * ζ ^ 19 - ((19 / 292) : ℂ) * ζ ^ 20 + ((611 / 584) : ℂ) * ζ ^ 22 - ((65 / 292) : ℂ) * ζ ^ 23 + ((19 / 292) : ℂ) * ζ ^ 24 + ((43 / 584) : ℂ) * ζ ^ 25 + ((611 / 584) : ℂ) * ζ ^ 26 + ((91 / 584) : ℂ) * ζ ^ 28 - ((43 / 584) : ℂ) * ζ ^ 29 - ((611 / 584) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_4_2 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        4 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((491 / 1168) : ℂ) - ((801 / 1168) : ℂ) * ζ ^ 3 + ((491 / 1168) : ℂ) * ζ ^ 4 - ((475 / 1168) : ℂ) * ζ ^ 5 - ((893 / 1168) : ℂ) * ζ ^ 6 - ((187 / 292) : ℂ) * ζ ^ 8 + ((475 / 1168) : ℂ) * ζ ^ 9 - ((1421 / 1168) : ℂ) * ζ ^ 10 - ((533 / 1168) : ℂ) * ζ ^ 13 + ((33 / 73) : ℂ) * ζ ^ 14 - ((909 / 1168) : ℂ) * ζ ^ 15 - ((147 / 584) : ℂ) * ζ ^ 18 + ((909 / 1168) : ℂ) * ζ ^ 19 + ((35 / 292) : ℂ) * ζ ^ 20 + ((893 / 1168) : ℂ) * ζ ^ 22 - ((489 / 1168) : ℂ) * ζ ^ 23 - ((35 / 292) : ℂ) * ζ ^ 24 - ((351 / 1168) : ℂ) * ζ ^ 25 + ((893 / 1168) : ℂ) * ζ ^ 26 + ((55 / 1168) : ℂ) * ζ ^ 28 + ((351 / 1168) : ℂ) * ζ ^ 29 - ((893 / 1168) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_4_3 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        4 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((4564 / 5329) : ℂ) + ((8975 / 42632) : ℂ) * ζ ^ 3 - ((4564 / 5329) : ℂ) * ζ ^ 4 + ((607 / 5329) : ℂ) * ζ ^ 5 + ((203 / 21316) : ℂ) * ζ ^ 6 + ((16303 / 42632) : ℂ) * ζ ^ 8 - ((607 / 5329) : ℂ) * ζ ^ 9 + ((1419 / 42632) : ℂ) * ζ ^ 10 + ((9363 / 21316) : ℂ) * ζ ^ 13 - ((1013 / 42632) : ℂ) * ζ ^ 14 + ((1683 / 42632) : ℂ) * ζ ^ 15 - ((27457 / 42632) : ℂ) * ζ ^ 18 - ((1683 / 42632) : ℂ) * ζ ^ 19 + ((2093 / 42632) : ℂ) * ζ ^ 20 - ((203 / 21316) : ℂ) * ζ ^ 22 + ((15553 / 42632) : ℂ) * ζ ^ 23 - ((2093 / 42632) : ℂ) * ζ ^ 24 + ((24709 / 42632) : ℂ) * ζ ^ 25 - ((203 / 21316) : ℂ) * ζ ^ 26 - ((1352 / 5329) : ℂ) * ζ ^ 28 - ((24709 / 42632) : ℂ) * ζ ^ 29 + ((203 / 21316) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_4_4 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        4 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((67117 / 85264) : ℂ) - ((51893 / 85264) : ℂ) * ζ ^ 3 + ((67117 / 85264) : ℂ) * ζ ^ 4 - ((55429 / 85264) : ℂ) * ζ ^ 5 + ((34317 / 85264) : ℂ) * ζ ^ 6 - ((161 / 21316) : ℂ) * ζ ^ 8 + ((55429 / 85264) : ℂ) * ζ ^ 9 + ((7731 / 85264) : ℂ) * ζ ^ 10 - ((22287 / 85264) : ℂ) * ζ ^ 13 + ((13293 / 42632) : ℂ) * ζ ^ 14 - ((521 / 85264) : ℂ) * ζ ^ 15 - ((3076 / 5329) : ℂ) * ζ ^ 18 + ((521 / 85264) : ℂ) * ζ ^ 19 - ((1299 / 21316) : ℂ) * ζ ^ 20 - ((34317 / 85264) : ℂ) * ζ ^ 22 + ((35249 / 85264) : ℂ) * ζ ^ 23 + ((1299 / 21316) : ℂ) * ζ ^ 24 + ((55429 / 85264) : ℂ) * ζ ^ 25 - ((34317 / 85264) : ℂ) * ζ ^ 26 - ((39171 / 85264) : ℂ) * ζ ^ 28 - ((55429 / 85264) : ℂ) * ζ ^ 29 + ((34317 / 85264) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_4_5 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        4 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((99 / 584) : ℂ) - ((303 / 292) : ℂ) * ζ ^ 3 + ((99 / 584) : ℂ) * ζ ^ 4 - ((45 / 146) : ℂ) * ζ ^ 5 - ((267 / 584) : ℂ) * ζ ^ 6 - ((309 / 584) : ℂ) * ζ ^ 8 + ((45 / 146) : ℂ) * ζ ^ 9 - ((531 / 584) : ℂ) * ζ ^ 10 + ((23 / 146) : ℂ) * ζ ^ 13 + ((33 / 73) : ℂ) * ζ ^ 14 + ((23 / 73) : ℂ) * ζ ^ 15 - ((191 / 584) : ℂ) * ζ ^ 18 - ((23 / 73) : ℂ) * ζ ^ 19 - ((45 / 292) : ℂ) * ζ ^ 20 + ((267 / 584) : ℂ) * ζ ^ 22 + ((139 / 584) : ℂ) * ζ ^ 23 + ((45 / 292) : ℂ) * ζ ^ 24 + ((25 / 146) : ℂ) * ζ ^ 25 + ((267 / 584) : ℂ) * ζ ^ 26 + ((205 / 584) : ℂ) * ζ ^ 28 - ((25 / 146) : ℂ) * ζ ^ 29 - ((267 / 584) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_5_0 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        5 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((229 / 584) : ℂ) + ((7 / 584) : ℂ) * ζ ^ 3 - ((229 / 584) : ℂ) * ζ ^ 4 + ((95 / 292) : ℂ) * ζ ^ 5 + ((143 / 584) : ℂ) * ζ ^ 6 - ((139 / 584) : ℂ) * ζ ^ 8 - ((95 / 292) : ℂ) * ζ ^ 9 + ((317 / 584) : ℂ) * ζ ^ 10 - ((33 / 292) : ℂ) * ζ ^ 13 - ((87 / 292) : ℂ) * ζ ^ 14 - ((27 / 146) : ℂ) * ζ ^ 15 - ((123 / 584) : ℂ) * ζ ^ 18 + ((27 / 146) : ℂ) * ζ ^ 19 - ((379 / 584) : ℂ) * ζ ^ 20 - ((143 / 584) : ℂ) * ζ ^ 22 - ((9 / 292) : ℂ) * ζ ^ 23 + ((379 / 584) : ℂ) * ζ ^ 24 - ((1 / 292) : ℂ) * ζ ^ 25 - ((143 / 584) : ℂ) * ζ ^ 26 - ((29 / 73) : ℂ) * ζ ^ 28 + ((1 / 292) : ℂ) * ζ ^ 29 + ((143 / 584) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_5_1 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        5 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((87 / 292) : ℂ) - ((65 / 292) : ℂ) * ζ ^ 3 + ((87 / 292) : ℂ) * ζ ^ 4 - ((13 / 292) : ℂ) * ζ ^ 5 - ((49 / 584) : ℂ) * ζ ^ 6 + ((255 / 584) : ℂ) * ζ ^ 8 + ((13 / 292) : ℂ) * ζ ^ 9 - ((1 / 8) : ℂ) * ζ ^ 10 - ((43 / 584) : ℂ) * ζ ^ 13 + ((3 / 73) : ℂ) * ζ ^ 14 + ((131 / 584) : ℂ) * ζ ^ 15 + ((525 / 584) : ℂ) * ζ ^ 18 - ((131 / 584) : ℂ) * ζ ^ 19 - ((12 / 73) : ℂ) * ζ ^ 20 + ((49 / 584) : ℂ) * ζ ^ 22 + ((1 / 292) : ℂ) * ζ ^ 23 + ((12 / 73) : ℂ) * ζ ^ 24 - ((95 / 584) : ℂ) * ζ ^ 25 + ((49 / 584) : ℂ) * ζ ^ 26 + ((57 / 584) : ℂ) * ζ ^ 28 + ((95 / 584) : ℂ) * ζ ^ 29 - ((49 / 584) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_5_2 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        5 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((331 / 1168) : ℂ) - ((91 / 1168) : ℂ) * ζ ^ 3 - ((331 / 1168) : ℂ) * ζ ^ 4 + ((41 / 1168) : ℂ) * ζ ^ 5 + ((737 / 1168) : ℂ) * ζ ^ 6 + ((81 / 584) : ℂ) * ζ ^ 8 - ((41 / 1168) : ℂ) * ζ ^ 9 + ((1109 / 1168) : ℂ) * ζ ^ 10 - ((313 / 1168) : ℂ) * ζ ^ 13 - ((93 / 292) : ℂ) * ζ ^ 14 - ((141 / 1168) : ℂ) * ζ ^ 15 + ((41 / 292) : ℂ) * ζ ^ 18 + ((141 / 1168) : ℂ) * ζ ^ 19 + ((25 / 146) : ℂ) * ζ ^ 20 - ((737 / 1168) : ℂ) * ζ ^ 22 + ((167 / 1168) : ℂ) * ζ ^ 23 - ((25 / 146) : ℂ) * ζ ^ 24 - ((199 / 1168) : ℂ) * ζ ^ 25 - ((737 / 1168) : ℂ) * ζ ^ 26 + ((89 / 1168) : ℂ) * ζ ^ 28 + ((199 / 1168) : ℂ) * ζ ^ 29 + ((737 / 1168) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_5_3 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        5 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((2459 / 5329) : ℂ) + ((14417 / 42632) : ℂ) * ζ ^ 3 + ((2459 / 5329) : ℂ) * ζ ^ 4 + ((2603 / 21316) : ℂ) * ζ ^ 5 - ((8251 / 21316) : ℂ) * ζ ^ 6 - ((17955 / 42632) : ℂ) * ζ ^ 8 - ((2603 / 21316) : ℂ) * ζ ^ 9 - ((2551 / 42632) : ℂ) * ζ ^ 10 - ((195 / 10658) : ℂ) * ζ ^ 13 - ((13951 / 42632) : ℂ) * ζ ^ 14 + ((39457 / 42632) : ℂ) * ζ ^ 15 + ((12053 / 42632) : ℂ) * ζ ^ 18 - ((39457 / 42632) : ℂ) * ζ ^ 19 - ((6281 / 42632) : ℂ) * ζ ^ 20 + ((8251 / 21316) : ℂ) * ζ ^ 22 - ((6241 / 42632) : ℂ) * ζ ^ 23 + ((6281 / 42632) : ℂ) * ζ ^ 24 - ((4111 / 42632) : ℂ) * ζ ^ 25 + ((8251 / 21316) : ℂ) * ζ ^ 26 + ((1779 / 10658) : ℂ) * ζ ^ 28 + ((4111 / 42632) : ℂ) * ζ ^ 29 - ((8251 / 21316) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_5_4 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        5 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((19075 / 85264) : ℂ) - ((5419 / 85264) : ℂ) * ζ ^ 3 + ((19075 / 85264) : ℂ) * ζ ^ 4 - ((23089 / 85264) : ℂ) * ζ ^ 5 - ((20941 / 85264) : ℂ) * ζ ^ 6 + ((1803 / 42632) : ℂ) * ζ ^ 8 + ((23089 / 85264) : ℂ) * ζ ^ 9 + ((793 / 85264) : ℂ) * ζ ^ 10 + ((10345 / 85264) : ℂ) * ζ ^ 13 - ((10867 / 42632) : ℂ) * ζ ^ 14 + ((17391 / 85264) : ℂ) * ζ ^ 15 + ((3713 / 42632) : ℂ) * ζ ^ 18 - ((17391 / 85264) : ℂ) * ζ ^ 19 + ((1179 / 21316) : ℂ) * ζ ^ 20 + ((20941 / 85264) : ℂ) * ζ ^ 22 - ((22759 / 85264) : ℂ) * ζ ^ 23 - ((1179 / 21316) : ℂ) * ζ ^ 24 - ((16039 / 85264) : ℂ) * ζ ^ 25 + ((20941 / 85264) : ℂ) * ζ ^ 26 + ((13235 / 85264) : ℂ) * ζ ^ 28 + ((16039 / 85264) : ℂ) * ζ ^ 29 - ((20941 / 85264) : ℂ) * ζ ^ 30)
private theorem row12_eigenbasisInverse_mul_5_5 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis)
        5 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((569 / 584) : ℂ) + ((13 / 146) : ℂ) * ζ ^ 3 + ((569 / 584) : ℂ) * ζ ^ 4 - ((53 / 73) : ℂ) * ζ ^ 5 + ((35 / 146) : ℂ) * ζ ^ 6 - ((63 / 73) : ℂ) * ζ ^ 8 + ((53 / 73) : ℂ) * ζ ^ 9 + ((17 / 292) : ℂ) * ζ ^ 10 - ((463 / 584) : ℂ) * ζ ^ 13 + ((53 / 292) : ℂ) * ζ ^ 14 - ((25 / 292) : ℂ) * ζ ^ 15 - ((179 / 584) : ℂ) * ζ ^ 18 + ((25 / 292) : ℂ) * ζ ^ 19 + ((153 / 584) : ℂ) * ζ ^ 20 - ((35 / 146) : ℂ) * ζ ^ 22 - ((5 / 292) : ℂ) * ζ ^ 23 - ((153 / 584) : ℂ) * ζ ^ 24 - ((97 / 584) : ℂ) * ζ ^ 25 - ((35 / 146) : ℂ) * ζ ^ 26 + ((53 / 584) : ℂ) * ζ ^ 28 + ((97 / 584) : ℂ) * ζ ^ 29 + ((35 / 146) : ℂ) * ζ ^ 30)
/-- The displayed row 12 matrix is a left inverse of its
eigenbasis. -/
theorem alternatingSixAmbientRow12EigenbasisInverse_mul :
    alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixAmbientRow12Eigenbasis =
      1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row12_eigenbasisInverse_mul_0_0
  · exact row12_eigenbasisInverse_mul_0_1
  · exact row12_eigenbasisInverse_mul_0_2
  · exact row12_eigenbasisInverse_mul_0_3
  · exact row12_eigenbasisInverse_mul_0_4
  · exact row12_eigenbasisInverse_mul_0_5
  · exact row12_eigenbasisInverse_mul_1_0
  · exact row12_eigenbasisInverse_mul_1_1
  · exact row12_eigenbasisInverse_mul_1_2
  · exact row12_eigenbasisInverse_mul_1_3
  · exact row12_eigenbasisInverse_mul_1_4
  · exact row12_eigenbasisInverse_mul_1_5
  · exact row12_eigenbasisInverse_mul_2_0
  · exact row12_eigenbasisInverse_mul_2_1
  · exact row12_eigenbasisInverse_mul_2_2
  · exact row12_eigenbasisInverse_mul_2_3
  · exact row12_eigenbasisInverse_mul_2_4
  · exact row12_eigenbasisInverse_mul_2_5
  · exact row12_eigenbasisInverse_mul_3_0
  · exact row12_eigenbasisInverse_mul_3_1
  · exact row12_eigenbasisInverse_mul_3_2
  · exact row12_eigenbasisInverse_mul_3_3
  · exact row12_eigenbasisInverse_mul_3_4
  · exact row12_eigenbasisInverse_mul_3_5
  · exact row12_eigenbasisInverse_mul_4_0
  · exact row12_eigenbasisInverse_mul_4_1
  · exact row12_eigenbasisInverse_mul_4_2
  · exact row12_eigenbasisInverse_mul_4_3
  · exact row12_eigenbasisInverse_mul_4_4
  · exact row12_eigenbasisInverse_mul_4_5
  · exact row12_eigenbasisInverse_mul_5_0
  · exact row12_eigenbasisInverse_mul_5_1
  · exact row12_eigenbasisInverse_mul_5_2
  · exact row12_eigenbasisInverse_mul_5_3
  · exact row12_eigenbasisInverse_mul_5_4
  · exact row12_eigenbasisInverse_mul_5_5

/-- The displayed row 12 inverse is also a right inverse. -/
theorem alternatingSixAmbientRow12Eigenbasis_mul_inverse :
    alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixAmbientRow12EigenbasisInverse_mul


private theorem row12_generatorB_mul_eigenbasis_0_0 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        0 0 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        0 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((181 / 146) : ℂ) + ((85 / 146) : ℂ) * ζ ^ 3 + ((181 / 146) : ℂ) * ζ ^ 4 - ((77 / 73) : ℂ) * ζ ^ 5 + ((47 / 146) : ℂ) * ζ ^ 6 - ((67 / 73) : ℂ) * ζ ^ 8 + ((77 / 73) : ℂ) * ζ ^ 9 + ((95 / 146) : ℂ) * ζ ^ 10 - ((207 / 146) : ℂ) * ζ ^ 13 - ((24 / 73) : ℂ) * ζ ^ 14 + ((159 / 146) : ℂ) * ζ ^ 15 + ((29 / 146) : ℂ) * ζ ^ 18 - ((159 / 146) : ℂ) * ζ ^ 19 - ((85 / 73) : ℂ) * ζ ^ 20 - ((47 / 146) : ℂ) * ζ ^ 22 + ((209 / 146) : ℂ) * ζ ^ 23 + ((85 / 73) : ℂ) * ζ ^ 24 - ((139 / 146) : ℂ) * ζ ^ 25 - ((47 / 146) : ℂ) * ζ ^ 26 - ((137 / 146) : ℂ) * ζ ^ 28 + ((139 / 146) : ℂ) * ζ ^ 29 + ((47 / 146) : ℂ) * ζ ^ 30)
private theorem row12_generatorB_mul_eigenbasis_0_1 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        0 1 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        0 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((122 / 73) : ℂ) + ((45 / 73) : ℂ) * ζ ^ 3 - ((122 / 73) : ℂ) * ζ ^ 4 - ((64 / 73) : ℂ) * ζ ^ 5 - ((115 / 73) : ℂ) * ζ ^ 6 + ((239 / 146) : ℂ) * ζ ^ 8 + ((64 / 73) : ℂ) * ζ ^ 9 + (2 : ℂ) * ζ ^ 10 + ((130 / 73) : ℂ) * ζ ^ 13 - ((261 / 73) : ℂ) * ζ ^ 14 + ((300 / 73) : ℂ) * ζ ^ 15 + ((827 / 146) : ℂ) * ζ ^ 18 - ((300 / 73) : ℂ) * ζ ^ 19 + ((263 / 146) : ℂ) * ζ ^ 20 + ((115 / 73) : ℂ) * ζ ^ 22 + ((431 / 146) : ℂ) * ζ ^ 23 - ((263 / 146) : ℂ) * ζ ^ 24 + ((221 / 73) : ℂ) * ζ ^ 25 + ((115 / 73) : ℂ) * ζ ^ 26 + ((247 / 73) : ℂ) * ζ ^ 28 - ((221 / 73) : ℂ) * ζ ^ 29 - ((188 / 73) : ℂ) * ζ ^ 30 + ζ ^ 33 + ζ ^ 34 - ζ ^ 38)
private theorem row12_generatorB_mul_eigenbasis_0_2 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        0 2 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        0 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((27 / 292) : ℂ) + ((209 / 292) : ℂ) * ζ ^ 3 + ((27 / 292) : ℂ) * ζ ^ 4 + ((185 / 292) : ℂ) * ζ ^ 5 + ((85 / 292) : ℂ) * ζ ^ 6 + ((455 / 292) : ℂ) * ζ ^ 8 - ((185 / 292) : ℂ) * ζ ^ 9 + ((827 / 292) : ℂ) * ζ ^ 10 - ((255 / 292) : ℂ) * ζ ^ 13 - ((371 / 146) : ℂ) * ζ ^ 14 - ((565 / 292) : ℂ) * ζ ^ 15 + ((229 / 292) : ℂ) * ζ ^ 18 + ((565 / 292) : ℂ) * ζ ^ 19 + ((44 / 73) : ℂ) * ζ ^ 20 - ((85 / 292) : ℂ) * ζ ^ 22 - ((183 / 292) : ℂ) * ζ ^ 23 - ((44 / 73) : ℂ) * ζ ^ 24 - ((727 / 292) : ℂ) * ζ ^ 25 - ((85 / 292) : ℂ) * ζ ^ 26 - ((14 / 73) : ℂ) * ζ ^ 28 + ((727 / 292) : ℂ) * ζ ^ 29 + ((85 / 292) : ℂ) * ζ ^ 30 - ((1 / 2) : ℂ) * ζ ^ 33 + ((1 / 2) : ℂ) * ζ ^ 35 - ((1 / 2) : ℂ) * ζ ^ 39 - ((1 / 2) : ℂ) * ζ ^ 40 + ((1 / 2) : ℂ) * ζ ^ 43 + ((1 / 2) : ℂ) * ζ ^ 44)
private theorem row12_generatorB_mul_eigenbasis_0_3 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        0 3 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        0 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((2512 / 5329) : ℂ) - ((5830 / 5329) : ℂ) * ζ ^ 3 + ((2512 / 5329) : ℂ) * ζ ^ 4 - ((29025 / 10658) : ℂ) * ζ ^ 5 - ((9264 / 5329) : ℂ) * ζ ^ 6 - ((30561 / 10658) : ℂ) * ζ ^ 8 + ((29025 / 10658) : ℂ) * ζ ^ 9 - ((23659 / 5329) : ℂ) * ζ ^ 10 - ((3234 / 5329) : ℂ) * ζ ^ 13 + ((14395 / 5329) : ℂ) * ζ ^ 14 + ((13777 / 10658) : ℂ) * ζ ^ 15 - ((19081 / 10658) : ℂ) * ζ ^ 18 - ((13777 / 10658) : ℂ) * ζ ^ 19 - ((20247 / 10658) : ℂ) * ζ ^ 20 + ((9264 / 5329) : ℂ) * ζ ^ 22 + ((1659 / 10658) : ℂ) * ζ ^ 23 + ((20247 / 10658) : ℂ) * ζ ^ 24 + ((13549 / 10658) : ℂ) * ζ ^ 25 + ((9264 / 5329) : ℂ) * ζ ^ 26 + ((541 / 5329) : ℂ) * ζ ^ 28 - ((13549 / 10658) : ℂ) * ζ ^ 29 - ((13936 / 5329) : ℂ) * ζ ^ 30 + ((7 / 73) : ℂ) * ζ ^ 33 + ((64 / 73) : ℂ) * ζ ^ 34 + ((22 / 73) : ℂ) * ζ ^ 35 - ((64 / 73) : ℂ) * ζ ^ 38 - ((22 / 73) : ℂ) * ζ ^ 39 - ((3 / 73) : ℂ) * ζ ^ 40 + ((22 / 73) : ℂ) * ζ ^ 43 + ((3 / 73) : ℂ) * ζ ^ 44 + ((17 / 73) : ℂ) * ζ ^ 45 - ((3 / 73) : ℂ) * ζ ^ 48 - ((17 / 73) : ℂ) * ζ ^ 49 + ((1 / 73) : ℂ) * ζ ^ 50 + ((17 / 73) : ℂ) * ζ ^ 53 - ((1 / 73) : ℂ) * ζ ^ 54 + ((43 / 73) : ℂ) * ζ ^ 55 + ((1 / 73) : ℂ) * ζ ^ 58 - ((43 / 73) : ℂ) * ζ ^ 59 + ((24 / 73) : ℂ) * ζ ^ 60 + ((43 / 73) : ℂ) * ζ ^ 63 - ((24 / 73) : ℂ) * ζ ^ 64 + ((10 / 73) : ℂ) * ζ ^ 65 + ((24 / 73) : ℂ) * ζ ^ 68 - ((10 / 73) : ℂ) * ζ ^ 69 + ((65 / 73) : ℂ) * ζ ^ 70 + ((10 / 73) : ℂ) * ζ ^ 73 - ((65 / 73) : ℂ) * ζ ^ 74)
private theorem row12_generatorB_mul_eigenbasis_0_4 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        0 4 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        0 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((72931 / 21316) : ℂ) - ((18081 / 21316) : ℂ) * ζ ^ 3 - ((72931 / 21316) : ℂ) * ζ ^ 4 - ((12081 / 21316) : ℂ) * ζ ^ 5 - ((29089 / 21316) : ℂ) * ζ ^ 6 + ((46363 / 21316) : ℂ) * ζ ^ 8 + ((12081 / 21316) : ℂ) * ζ ^ 9 + ((21935 / 21316) : ℂ) * ζ ^ 10 + ((26755 / 21316) : ℂ) * ζ ^ 13 - ((12756 / 5329) : ℂ) * ζ ^ 14 + ((43047 / 21316) : ℂ) * ζ ^ 15 + ((29489 / 21316) : ℂ) * ζ ^ 18 - ((43047 / 21316) : ℂ) * ζ ^ 19 - ((2046 / 5329) : ℂ) * ζ ^ 20 + ((29089 / 21316) : ℂ) * ζ ^ 22 + ((19541 / 21316) : ℂ) * ζ ^ 23 + ((2046 / 5329) : ℂ) * ζ ^ 24 + ((24929 / 21316) : ℂ) * ζ ^ 25 + ((29089 / 21316) : ℂ) * ζ ^ 26 - ((512 / 5329) : ℂ) * ζ ^ 28 - ((24929 / 21316) : ℂ) * ζ ^ 29 - ((27045 / 21316) : ℂ) * ζ ^ 30 + ((19 / 146) : ℂ) * ζ ^ 33 - ((7 / 73) : ℂ) * ζ ^ 34 + ((91 / 146) : ℂ) * ζ ^ 35 + ((7 / 73) : ℂ) * ζ ^ 38 - ((91 / 146) : ℂ) * ζ ^ 39 - ((29 / 146) : ℂ) * ζ ^ 40 + ((91 / 146) : ℂ) * ζ ^ 43 + ((29 / 146) : ℂ) * ζ ^ 44 - ((3 / 73) : ℂ) * ζ ^ 45 - ((29 / 146) : ℂ) * ζ ^ 48 + ((3 / 73) : ℂ) * ζ ^ 49 - ((39 / 146) : ℂ) * ζ ^ 50 - ((3 / 73) : ℂ) * ζ ^ 53 + ((39 / 146) : ℂ) * ζ ^ 54 + ((75 / 146) : ℂ) * ζ ^ 55 - ((39 / 146) : ℂ) * ζ ^ 58 - ((75 / 146) : ℂ) * ζ ^ 59 - ((30 / 73) : ℂ) * ζ ^ 60 + ((75 / 146) : ℂ) * ζ ^ 63 + ((30 / 73) : ℂ) * ζ ^ 64 - ((25 / 146) : ℂ) * ζ ^ 65 - ((30 / 73) : ℂ) * ζ ^ 68 + ((25 / 146) : ℂ) * ζ ^ 69 - ((53 / 146) : ℂ) * ζ ^ 70 - ((25 / 146) : ℂ) * ζ ^ 73 + ((53 / 146) : ℂ) * ζ ^ 74)
private theorem row12_generatorB_mul_eigenbasis_0_5 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        0 5 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        0 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((495 / 146) : ℂ) + ((475 / 146) : ℂ) * ζ ^ 3 - ((495 / 146) : ℂ) * ζ ^ 4 + ((158 / 73) : ℂ) * ζ ^ 5 + ((167 / 146) : ℂ) * ζ ^ 6 + ((371 / 73) : ℂ) * ζ ^ 8 - ((158 / 73) : ℂ) * ζ ^ 9 + ((50 / 73) : ℂ) * ζ ^ 10 + ((343 / 146) : ℂ) * ζ ^ 13 + ((67 / 146) : ℂ) * ζ ^ 14 + ((124 / 73) : ℂ) * ζ ^ 15 - ((67 / 146) : ℂ) * ζ ^ 18 - ((124 / 73) : ℂ) * ζ ^ 19 + ((79 / 73) : ℂ) * ζ ^ 20 - ((167 / 146) : ℂ) * ζ ^ 22 - ((165 / 73) : ℂ) * ζ ^ 23 - ((79 / 73) : ℂ) * ζ ^ 24 + ((11 / 146) : ℂ) * ζ ^ 25 - ((167 / 146) : ℂ) * ζ ^ 26 - ((3 / 146) : ℂ) * ζ ^ 28 - ((11 / 146) : ℂ) * ζ ^ 29 + ((313 / 146) : ℂ) * ζ ^ 30 + ((1 / 2) : ℂ) * ζ ^ 33 - ζ ^ 34 - ((1 / 2) : ℂ) * ζ ^ 35 + ζ ^ 38 + ((1 / 2) : ℂ) * ζ ^ 39 + ((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 43 - ((1 / 2) : ℂ) * ζ ^ 44 + ((1 / 2) : ℂ) * ζ ^ 48 + ((1 / 2) : ℂ) * ζ ^ 50 - ((1 / 2) : ℂ) * ζ ^ 54 + ((1 / 2) : ℂ) * ζ ^ 55 + ((1 / 2) : ℂ) * ζ ^ 58 - ((1 / 2) : ℂ) * ζ ^ 59 + ((1 / 2) : ℂ) * ζ ^ 63 - ((1 / 2) : ℂ) * ζ ^ 65 + ((1 / 2) : ℂ) * ζ ^ 69 - ((1 / 2) : ℂ) * ζ ^ 70 - ((1 / 2) : ℂ) * ζ ^ 73 + ((1 / 2) : ℂ) * ζ ^ 74 + ζ ^ 75 - ((1 / 2) : ℂ) * ζ ^ 78 - ζ ^ 79 - ((1 / 2) : ℂ) * ζ ^ 80 + ζ ^ 83 + ((1 / 2) : ℂ) * ζ ^ 84 - ((1 / 2) : ℂ) * ζ ^ 85 - ((1 / 2) : ℂ) * ζ ^ 88 + ((1 / 2) : ℂ) * ζ ^ 89 - ζ ^ 90 - ((1 / 2) : ℂ) * ζ ^ 93 + ζ ^ 94 + ((1 / 2) : ℂ) * ζ ^ 95 - ζ ^ 98 - ((1 / 2) : ℂ) * ζ ^ 99 - ((1 / 2) : ℂ) * ζ ^ 100 + ((1 / 2) : ℂ) * ζ ^ 103 + ((1 / 2) : ℂ) * ζ ^ 104)
private theorem row12_generatorB_mul_eigenbasis_1_0 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        1 0 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        1 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((63 / 146) : ℂ) + ((153 / 146) : ℂ) * ζ ^ 3 + ((63 / 146) : ℂ) * ζ ^ 4 - ((29 / 146) : ℂ) * ζ ^ 5 - ((3 / 146) : ℂ) * ζ ^ 6 + ((40 / 73) : ℂ) * ζ ^ 8 + ((29 / 146) : ℂ) * ζ ^ 9 + ((171 / 146) : ℂ) * ζ ^ 10 + ((40 / 73) : ℂ) * ζ ^ 13 - ((87 / 73) : ℂ) * ζ ^ 14 + ((165 / 73) : ℂ) * ζ ^ 15 + ((23 / 146) : ℂ) * ζ ^ 18 - ((165 / 73) : ℂ) * ζ ^ 19 + ((205 / 146) : ℂ) * ζ ^ 20 + ((3 / 146) : ℂ) * ζ ^ 22 + ((55 / 146) : ℂ) * ζ ^ 23 - ((205 / 146) : ℂ) * ζ ^ 24 - ((1 / 73) : ℂ) * ζ ^ 25 + ((3 / 146) : ℂ) * ζ ^ 26 + ((30 / 73) : ℂ) * ζ ^ 28 + ((1 / 73) : ℂ) * ζ ^ 29 - ((3 / 146) : ℂ) * ζ ^ 30)
private theorem row12_generatorB_mul_eigenbasis_1_1 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        1 1 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        1 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((59 / 73) : ℂ) - ((65 / 73) : ℂ) * ζ ^ 3 - ((59 / 73) : ℂ) * ζ ^ 4 - ((86 / 73) : ℂ) * ζ ^ 5 + ((12 / 73) : ℂ) * ζ ^ 6 - ((183 / 146) : ℂ) * ζ ^ 8 + ((86 / 73) : ℂ) * ζ ^ 9 - (2 : ℂ) * ζ ^ 10 - ((481 / 146) : ℂ) * ζ ^ 13 + ((158 / 73) : ℂ) * ζ ^ 14 - ((161 / 146) : ℂ) * ζ ^ 15 - ((497 / 146) : ℂ) * ζ ^ 18 + ((161 / 146) : ℂ) * ζ ^ 19 - ((23 / 146) : ℂ) * ζ ^ 20 - ((12 / 73) : ℂ) * ζ ^ 22 - ((217 / 146) : ℂ) * ζ ^ 23 + ((23 / 146) : ℂ) * ζ ^ 24 + ((51 / 146) : ℂ) * ζ ^ 25 - ((12 / 73) : ℂ) * ζ ^ 26 - ((8 / 73) : ℂ) * ζ ^ 28 - ((51 / 146) : ℂ) * ζ ^ 29 + ((12 / 73) : ℂ) * ζ ^ 30 + ζ ^ 40 - ζ ^ 44)
private theorem row12_generatorB_mul_eigenbasis_1_2 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        1 2 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        1 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((39 / 292) : ℂ) + ((137 / 146) : ℂ) * ζ ^ 3 - ((39 / 292) : ℂ) * ζ ^ 4 - ((105 / 292) : ℂ) * ζ ^ 5 - ((139 / 292) : ℂ) * ζ ^ 6 + ((77 / 73) : ℂ) * ζ ^ 8 + ((105 / 292) : ℂ) * ζ ^ 9 + ((87 / 292) : ℂ) * ζ ^ 10 + ((99 / 146) : ℂ) * ζ ^ 13 - ((113 / 146) : ℂ) * ζ ^ 14 + ((297 / 292) : ℂ) * ζ ^ 15 + ((41 / 73) : ℂ) * ζ ^ 18 - ((297 / 292) : ℂ) * ζ ^ 19 + ((173 / 146) : ℂ) * ζ ^ 20 + ((139 / 292) : ℂ) * ζ ^ 22 - ((13 / 73) : ℂ) * ζ ^ 23 - ((173 / 146) : ℂ) * ζ ^ 24 + ((239 / 292) : ℂ) * ζ ^ 25 + ((139 / 292) : ℂ) * ζ ^ 26 + ((235 / 292) : ℂ) * ζ ^ 28 - ((239 / 292) : ℂ) * ζ ^ 29 + ((7 / 292) : ℂ) * ζ ^ 30 + ((1 / 2) : ℂ) * ζ ^ 33 - ((1 / 2) : ℂ) * ζ ^ 34 + ((1 / 2) : ℂ) * ζ ^ 38 + ((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 44)
private theorem row12_generatorB_mul_eigenbasis_1_3 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        1 3 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        1 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((6881 / 5329) : ℂ) - ((6169 / 10658) : ℂ) * ζ ^ 3 - ((6881 / 5329) : ℂ) * ζ ^ 4 + ((1435 / 5329) : ℂ) * ζ ^ 5 + ((5473 / 5329) : ℂ) * ζ ^ 6 + ((14895 / 10658) : ℂ) * ζ ^ 8 - ((1435 / 5329) : ℂ) * ζ ^ 9 - ((2553 / 5329) : ℂ) * ζ ^ 10 + ((1727 / 5329) : ℂ) * ζ ^ 13 + ((8026 / 5329) : ℂ) * ζ ^ 14 - ((6095 / 10658) : ℂ) * ζ ^ 15 - ((7511 / 10658) : ℂ) * ζ ^ 18 + ((6095 / 10658) : ℂ) * ζ ^ 19 + ((3647 / 10658) : ℂ) * ζ ^ 20 - ((5473 / 5329) : ℂ) * ζ ^ 22 + ((493 / 5329) : ℂ) * ζ ^ 23 - ((3647 / 10658) : ℂ) * ζ ^ 24 + ((3627 / 10658) : ℂ) * ζ ^ 25 - ((5473 / 5329) : ℂ) * ζ ^ 26 - ((1406 / 5329) : ℂ) * ζ ^ 28 - ((3627 / 10658) : ℂ) * ζ ^ 29 + ((5181 / 5329) : ℂ) * ζ ^ 30 + ((5 / 73) : ℂ) * ζ ^ 33 + ((4 / 73) : ℂ) * ζ ^ 34 + ((47 / 73) : ℂ) * ζ ^ 35 - ((4 / 73) : ℂ) * ζ ^ 38 - ((47 / 73) : ℂ) * ζ ^ 39 - ((23 / 73) : ℂ) * ζ ^ 40 + ((47 / 73) : ℂ) * ζ ^ 43 + ((23 / 73) : ℂ) * ζ ^ 44 + ((33 / 73) : ℂ) * ζ ^ 45 - ((23 / 73) : ℂ) * ζ ^ 48 - ((33 / 73) : ℂ) * ζ ^ 49 - ((41 / 73) : ℂ) * ζ ^ 50 + ((33 / 73) : ℂ) * ζ ^ 53 + ((41 / 73) : ℂ) * ζ ^ 54 + ((62 / 73) : ℂ) * ζ ^ 55 - ((41 / 73) : ℂ) * ζ ^ 58 - ((62 / 73) : ℂ) * ζ ^ 59 - ((35 / 73) : ℂ) * ζ ^ 60 + ((62 / 73) : ℂ) * ζ ^ 63 + ((35 / 73) : ℂ) * ζ ^ 64 + ((28 / 73) : ℂ) * ζ ^ 65 - ((35 / 73) : ℂ) * ζ ^ 68 - ((28 / 73) : ℂ) * ζ ^ 69 - ((37 / 73) : ℂ) * ζ ^ 70 + ((28 / 73) : ℂ) * ζ ^ 73 + ((37 / 73) : ℂ) * ζ ^ 74)
private theorem row12_generatorB_mul_eigenbasis_1_4 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        1 4 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        1 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((9249 / 21316) : ℂ) - ((12469 / 5329) : ℂ) * ζ ^ 3 - ((9249 / 21316) : ℂ) * ζ ^ 4 - ((27907 / 21316) : ℂ) * ζ ^ 5 + ((17019 / 21316) : ℂ) * ζ ^ 6 + ((6037 / 10658) : ℂ) * ζ ^ 8 + ((27907 / 21316) : ℂ) * ζ ^ 9 - ((813 / 21316) : ℂ) * ζ ^ 10 - ((5389 / 5329) : ℂ) * ζ ^ 13 + ((4458 / 5329) : ℂ) * ζ ^ 14 - ((28599 / 21316) : ℂ) * ζ ^ 15 + ((1523 / 10658) : ℂ) * ζ ^ 18 + ((28599 / 21316) : ℂ) * ζ ^ 19 + ((5935 / 10658) : ℂ) * ζ ^ 20 - ((17019 / 21316) : ℂ) * ζ ^ 22 - ((1547 / 5329) : ℂ) * ζ ^ 23 - ((5935 / 10658) : ℂ) * ζ ^ 24 + ((1919 / 21316) : ℂ) * ζ ^ 25 - ((17019 / 21316) : ℂ) * ζ ^ 26 + ((6081 / 21316) : ℂ) * ζ ^ 28 - ((1919 / 21316) : ℂ) * ζ ^ 29 + ((29137 / 21316) : ℂ) * ζ ^ 30 - ((49 / 146) : ℂ) * ζ ^ 33 - ((83 / 146) : ℂ) * ζ ^ 34 - ((4 / 73) : ℂ) * ζ ^ 35 + ((83 / 146) : ℂ) * ζ ^ 38 + ((4 / 73) : ℂ) * ζ ^ 39 + ((21 / 146) : ℂ) * ζ ^ 40 - ((4 / 73) : ℂ) * ζ ^ 43 - ((21 / 146) : ℂ) * ζ ^ 44 + ((27 / 146) : ℂ) * ζ ^ 45 + ((21 / 146) : ℂ) * ζ ^ 48 - ((27 / 146) : ℂ) * ζ ^ 49 - ((40 / 73) : ℂ) * ζ ^ 50 + ((27 / 146) : ℂ) * ζ ^ 53 + ((40 / 73) : ℂ) * ζ ^ 54 + ((137 / 146) : ℂ) * ζ ^ 55 - ((40 / 73) : ℂ) * ζ ^ 58 - ((137 / 146) : ℂ) * ζ ^ 59 - ((95 / 146) : ℂ) * ζ ^ 60 + ((137 / 146) : ℂ) * ζ ^ 63 + ((95 / 146) : ℂ) * ζ ^ 64 + ((38 / 73) : ℂ) * ζ ^ 65 - ((95 / 146) : ℂ) * ζ ^ 68 - ((38 / 73) : ℂ) * ζ ^ 69 - ((163 / 146) : ℂ) * ζ ^ 70 + ((38 / 73) : ℂ) * ζ ^ 73 + ((163 / 146) : ℂ) * ζ ^ 74)
private theorem row12_generatorB_mul_eigenbasis_1_5 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        1 5 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        1 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((161 / 146) : ℂ) - ((120 / 73) : ℂ) * ζ ^ 3 - ((161 / 146) : ℂ) * ζ ^ 4 + ((87 / 146) : ℂ) * ζ ^ 5 - ((79 / 146) : ℂ) * ζ ^ 6 + ((40 / 73) : ℂ) * ζ ^ 8 - ((87 / 146) : ℂ) * ζ ^ 9 - ((39 / 146) : ℂ) * ζ ^ 10 + ((24 / 73) : ℂ) * ζ ^ 13 - ((20 / 73) : ℂ) * ζ ^ 14 - ((123 / 146) : ℂ) * ζ ^ 15 - ((53 / 73) : ℂ) * ζ ^ 18 + ((123 / 146) : ℂ) * ζ ^ 19 + ((40 / 73) : ℂ) * ζ ^ 20 + ((79 / 146) : ℂ) * ζ ^ 22 - ((5 / 73) : ℂ) * ζ ^ 23 - ((40 / 73) : ℂ) * ζ ^ 24 - ((97 / 146) : ℂ) * ζ ^ 25 + ((79 / 146) : ℂ) * ζ ^ 26 + ((53 / 146) : ℂ) * ζ ^ 28 + ((97 / 146) : ℂ) * ζ ^ 29 - ((79 / 146) : ℂ) * ζ ^ 30 - ((1 / 2) : ℂ) * ζ ^ 33 + ((1 / 2) : ℂ) * ζ ^ 35 - ((1 / 2) : ℂ) * ζ ^ 39 - ((1 / 2) : ℂ) * ζ ^ 40 + ((1 / 2) : ℂ) * ζ ^ 43 + ((1 / 2) : ℂ) * ζ ^ 44 - ζ ^ 45 - ((1 / 2) : ℂ) * ζ ^ 48 + ζ ^ 49 - ((1 / 2) : ℂ) * ζ ^ 50 - ζ ^ 53 + ((1 / 2) : ℂ) * ζ ^ 54 + ((1 / 2) : ℂ) * ζ ^ 55 - ((1 / 2) : ℂ) * ζ ^ 58 - ((1 / 2) : ℂ) * ζ ^ 59 - ζ ^ 60 + ((1 / 2) : ℂ) * ζ ^ 63 + ζ ^ 64 - ((1 / 2) : ℂ) * ζ ^ 65 - ζ ^ 68 + ((1 / 2) : ℂ) * ζ ^ 69 - ((1 / 2) : ℂ) * ζ ^ 70 - ((1 / 2) : ℂ) * ζ ^ 73 + ((1 / 2) : ℂ) * ζ ^ 74 - ((1 / 2) : ℂ) * ζ ^ 78 - ((1 / 2) : ℂ) * ζ ^ 80 + ((1 / 2) : ℂ) * ζ ^ 84 + ((1 / 2) : ℂ) * ζ ^ 85 - ((1 / 2) : ℂ) * ζ ^ 88 - ((1 / 2) : ℂ) * ζ ^ 89 + ((1 / 2) : ℂ) * ζ ^ 93 - ((1 / 2) : ℂ) * ζ ^ 95 + ((1 / 2) : ℂ) * ζ ^ 99 + ((1 / 2) : ℂ) * ζ ^ 100 - ((1 / 2) : ℂ) * ζ ^ 103 - ((1 / 2) : ℂ) * ζ ^ 104)
private theorem row12_generatorB_mul_eigenbasis_2_0 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        2 0 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        2 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((81 / 146) : ℂ) + ((55 / 292) : ℂ) * ζ ^ 3 - ((81 / 146) : ℂ) * ζ ^ 4 + ((85 / 292) : ℂ) * ζ ^ 5 + ((101 / 73) : ℂ) * ζ ^ 6 + ((201 / 292) : ℂ) * ζ ^ 8 - ((85 / 292) : ℂ) * ζ ^ 9 + ((156 / 73) : ℂ) * ζ ^ 10 - ((91 / 292) : ℂ) * ζ ^ 13 - ((55 / 73) : ℂ) * ζ ^ 14 + ((163 / 292) : ℂ) * ζ ^ 15 - ((299 / 292) : ℂ) * ζ ^ 18 - ((163 / 292) : ℂ) * ζ ^ 19 + ((91 / 146) : ℂ) * ζ ^ 20 - ((101 / 73) : ℂ) * ζ ^ 22 + ((15 / 292) : ℂ) * ζ ^ 23 - ((91 / 146) : ℂ) * ζ ^ 24 + ((245 / 292) : ℂ) * ζ ^ 25 - ((101 / 73) : ℂ) * ζ ^ 26 - ((123 / 292) : ℂ) * ζ ^ 28 - ((245 / 292) : ℂ) * ζ ^ 29 + ((101 / 73) : ℂ) * ζ ^ 30)
private theorem row12_generatorB_mul_eigenbasis_2_1 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        2 1 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        2 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((401 / 146) : ℂ) - ((31 / 146) : ℂ) * ζ ^ 3 - ((401 / 146) : ℂ) * ζ ^ 4 - ((123 / 146) : ℂ) * ζ ^ 5 - ((375 / 146) : ℂ) * ζ ^ 6 - ((161 / 146) : ℂ) * ζ ^ 8 + ((123 / 146) : ℂ) * ζ ^ 9 - ζ ^ 10 + ((12 / 73) : ℂ) * ζ ^ 13 - ((229 / 146) : ℂ) * ζ ^ 14 - ((79 / 73) : ℂ) * ζ ^ 15 + ((55 / 146) : ℂ) * ζ ^ 18 + ((79 / 73) : ℂ) * ζ ^ 19 - ((199 / 73) : ℂ) * ζ ^ 20 + ((375 / 146) : ℂ) * ζ ^ 22 - ((159 / 146) : ℂ) * ζ ^ 23 + ((199 / 73) : ℂ) * ζ ^ 24 - ((149 / 146) : ℂ) * ζ ^ 25 + ((375 / 146) : ℂ) * ζ ^ 26 - ((21 / 73) : ℂ) * ζ ^ 28 + ((149 / 146) : ℂ) * ζ ^ 29 - ((521 / 146) : ℂ) * ζ ^ 30 - ζ ^ 33 + ζ ^ 34 - ζ ^ 35 - ζ ^ 38 + ζ ^ 39 - (2 : ℂ) * ζ ^ 40 - ζ ^ 43 + (2 : ℂ) * ζ ^ 44)
private theorem row12_generatorB_mul_eigenbasis_2_2 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        2 2 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        2 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((1 / 146) : ℂ) - ((29 / 292) : ℂ) * ζ ^ 3 - ((1 / 146) : ℂ) * ζ ^ 4 - ((21 / 73) : ℂ) * ζ ^ 5 + ((89 / 73) : ℂ) * ζ ^ 6 + ((167 / 146) : ℂ) * ζ ^ 8 + ((21 / 73) : ℂ) * ζ ^ 9 + ((137 / 146) : ℂ) * ζ ^ 10 - ((23 / 146) : ℂ) * ζ ^ 13 + ((41 / 146) : ℂ) * ζ ^ 14 - ((217 / 146) : ℂ) * ζ ^ 15 + ((197 / 146) : ℂ) * ζ ^ 18 + ((217 / 146) : ℂ) * ζ ^ 19 + ((153 / 146) : ℂ) * ζ ^ 20 - ((89 / 73) : ℂ) * ζ ^ 22 - ((173 / 292) : ℂ) * ζ ^ 23 - ((153 / 146) : ℂ) * ζ ^ 24 - ((65 / 146) : ℂ) * ζ ^ 25 - ((89 / 73) : ℂ) * ζ ^ 26 - ((31 / 292) : ℂ) * ζ ^ 28 + ((65 / 146) : ℂ) * ζ ^ 29 + ((251 / 146) : ℂ) * ζ ^ 30 - ((1 / 2) : ℂ) * ζ ^ 33 - ((1 / 2) : ℂ) * ζ ^ 34 + ((1 / 2) : ℂ) * ζ ^ 38 + ((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 44)
private theorem row12_generatorB_mul_eigenbasis_2_3 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        2 3 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        2 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((5155 / 10658) : ℂ) + ((686 / 5329) : ℂ) * ζ ^ 3 - ((5155 / 10658) : ℂ) * ζ ^ 4 + ((5163 / 5329) : ℂ) * ζ ^ 5 - ((352 / 5329) : ℂ) * ζ ^ 6 - ((5093 / 10658) : ℂ) * ζ ^ 8 - ((5163 / 5329) : ℂ) * ζ ^ 9 + ((8953 / 10658) : ℂ) * ζ ^ 10 + ((5163 / 5329) : ℂ) * ζ ^ 13 - ((9657 / 10658) : ℂ) * ζ ^ 14 + ((3081 / 10658) : ℂ) * ζ ^ 15 + ((3379 / 10658) : ℂ) * ζ ^ 18 - ((3081 / 10658) : ℂ) * ζ ^ 19 + ((5239 / 10658) : ℂ) * ζ ^ 20 + ((352 / 5329) : ℂ) * ζ ^ 22 - ((3168 / 5329) : ℂ) * ζ ^ 23 - ((5239 / 10658) : ℂ) * ζ ^ 24 - ((325 / 10658) : ℂ) * ζ ^ 25 + ((352 / 5329) : ℂ) * ζ ^ 26 + ((4686 / 5329) : ℂ) * ζ ^ 28 + ((325 / 10658) : ℂ) * ζ ^ 29 + ((1911 / 5329) : ℂ) * ζ ^ 30 + ((16 / 73) : ℂ) * ζ ^ 33 - ((31 / 73) : ℂ) * ζ ^ 34 + ((19 / 73) : ℂ) * ζ ^ 35 + ((31 / 73) : ℂ) * ζ ^ 38 - ((19 / 73) : ℂ) * ζ ^ 39 + ((14 / 73) : ℂ) * ζ ^ 40 + ((19 / 73) : ℂ) * ζ ^ 43 - ((14 / 73) : ℂ) * ζ ^ 44 + ((18 / 73) : ℂ) * ζ ^ 45 + ((14 / 73) : ℂ) * ζ ^ 48 - ((18 / 73) : ℂ) * ζ ^ 49 - ((29 / 73) : ℂ) * ζ ^ 50 + ((18 / 73) : ℂ) * ζ ^ 53 + ((29 / 73) : ℂ) * ζ ^ 54 + ((67 / 73) : ℂ) * ζ ^ 55 - ((29 / 73) : ℂ) * ζ ^ 58 - ((67 / 73) : ℂ) * ζ ^ 59 - ((39 / 73) : ℂ) * ζ ^ 60 + ((67 / 73) : ℂ) * ζ ^ 63 + ((39 / 73) : ℂ) * ζ ^ 64 + ((2 / 73) : ℂ) * ζ ^ 65 - ((39 / 73) : ℂ) * ζ ^ 68 - ((2 / 73) : ℂ) * ζ ^ 69 - ((60 / 73) : ℂ) * ζ ^ 70 + ((2 / 73) : ℂ) * ζ ^ 73 + ((60 / 73) : ℂ) * ζ ^ 74)
private theorem row12_generatorB_mul_eigenbasis_2_4 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        2 4 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        2 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((2225 / 10658) : ℂ) - ((1313 / 21316) : ℂ) * ζ ^ 3 - ((2225 / 10658) : ℂ) * ζ ^ 4 - ((3406 / 5329) : ℂ) * ζ ^ 5 + ((515 / 10658) : ℂ) * ζ ^ 6 + ((1311 / 10658) : ℂ) * ζ ^ 8 + ((3406 / 5329) : ℂ) * ζ ^ 9 - ((2849 / 5329) : ℂ) * ζ ^ 10 - ((778 / 5329) : ℂ) * ζ ^ 13 + ((6213 / 10658) : ℂ) * ζ ^ 14 - ((3632 / 5329) : ℂ) * ζ ^ 15 + ((941 / 10658) : ℂ) * ζ ^ 18 + ((3632 / 5329) : ℂ) * ζ ^ 19 - ((5072 / 5329) : ℂ) * ζ ^ 20 - ((515 / 10658) : ℂ) * ζ ^ 22 - ((5257 / 21316) : ℂ) * ζ ^ 23 + ((5072 / 5329) : ℂ) * ζ ^ 24 - ((9321 / 10658) : ℂ) * ζ ^ 25 - ((515 / 10658) : ℂ) * ζ ^ 26 + ((6719 / 21316) : ℂ) * ζ ^ 28 + ((9321 / 10658) : ℂ) * ζ ^ 29 + ((4090 / 5329) : ℂ) * ζ ^ 30 - ((113 / 146) : ℂ) * ζ ^ 33 - ((105 / 146) : ℂ) * ζ ^ 34 - ((42 / 73) : ℂ) * ζ ^ 35 + ((105 / 146) : ℂ) * ζ ^ 38 + ((42 / 73) : ℂ) * ζ ^ 39 - ((35 / 146) : ℂ) * ζ ^ 40 - ((42 / 73) : ℂ) * ζ ^ 43 + ((35 / 146) : ℂ) * ζ ^ 44 - ((45 / 146) : ℂ) * ζ ^ 45 - ((35 / 146) : ℂ) * ζ ^ 48 + ((45 / 146) : ℂ) * ζ ^ 49 + ((18 / 73) : ℂ) * ζ ^ 50 - ((45 / 146) : ℂ) * ζ ^ 53 - ((18 / 73) : ℂ) * ζ ^ 54 + ((15 / 146) : ℂ) * ζ ^ 55 + ((18 / 73) : ℂ) * ζ ^ 58 - ((15 / 146) : ℂ) * ζ ^ 59 - ((85 / 146) : ℂ) * ζ ^ 60 + ((15 / 146) : ℂ) * ζ ^ 63 + ((85 / 146) : ℂ) * ζ ^ 64 + ((34 / 73) : ℂ) * ζ ^ 65 - ((85 / 146) : ℂ) * ζ ^ 68 - ((34 / 73) : ℂ) * ζ ^ 69 - ((69 / 146) : ℂ) * ζ ^ 70 + ((34 / 73) : ℂ) * ζ ^ 73 + ((69 / 146) : ℂ) * ζ ^ 74)
private theorem row12_generatorB_mul_eigenbasis_2_5 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        2 5 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        2 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((61 / 146) : ℂ) - ((19 / 292) : ℂ) * ζ ^ 3 + ((61 / 146) : ℂ) * ζ ^ 4 + ((37 / 292) : ℂ) * ζ ^ 5 + ((39 / 146) : ℂ) * ζ ^ 6 - ((383 / 292) : ℂ) * ζ ^ 8 - ((37 / 292) : ℂ) * ζ ^ 9 - ((75 / 146) : ℂ) * ζ ^ 10 + ((33 / 292) : ℂ) * ζ ^ 13 + ((57 / 73) : ℂ) * ζ ^ 14 + ((139 / 292) : ℂ) * ζ ^ 15 - ((447 / 292) : ℂ) * ζ ^ 18 - ((139 / 292) : ℂ) * ζ ^ 19 - ((41 / 73) : ℂ) * ζ ^ 20 - ((39 / 146) : ℂ) * ζ ^ 22 + ((57 / 292) : ℂ) * ζ ^ 23 + ((41 / 73) : ℂ) * ζ ^ 24 - ((53 / 292) : ℂ) * ζ ^ 25 - ((39 / 146) : ℂ) * ζ ^ 26 - ((251 / 292) : ℂ) * ζ ^ 28 + ((53 / 292) : ℂ) * ζ ^ 29 + ((39 / 146) : ℂ) * ζ ^ 30 - ζ ^ 33 - ζ ^ 35 + ζ ^ 39 - ζ ^ 43 - ζ ^ 45 + ζ ^ 49 - ζ ^ 53 - ζ ^ 55 + ζ ^ 59 - ζ ^ 63 + ζ ^ 85 - ζ ^ 89 + ζ ^ 93 + ζ ^ 95 - ζ ^ 99 + ζ ^ 103)
private theorem row12_generatorB_mul_eigenbasis_3_0 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        3 0 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        3 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((275 / 146) : ℂ) - ((53 / 292) : ℂ) * ζ ^ 3 - ((275 / 146) : ℂ) * ζ ^ 4 - ((281 / 292) : ℂ) * ζ ^ 5 - ((23 / 73) : ℂ) * ζ ^ 6 + ((239 / 292) : ℂ) * ζ ^ 8 + ((281 / 292) : ℂ) * ζ ^ 9 - ((149 / 73) : ℂ) * ζ ^ 10 - ((53 / 292) : ℂ) * ζ ^ 13 + ((126 / 73) : ℂ) * ζ ^ 14 - ((611 / 292) : ℂ) * ζ ^ 15 - ((341 / 292) : ℂ) * ζ ^ 18 + ((611 / 292) : ℂ) * ζ ^ 19 - ((93 / 146) : ℂ) * ζ ^ 20 + ((23 / 73) : ℂ) * ζ ^ 22 - ((41 / 292) : ℂ) * ζ ^ 23 + ((93 / 146) : ℂ) * ζ ^ 24 + ((547 / 292) : ℂ) * ζ ^ 25 + ((23 / 73) : ℂ) * ζ ^ 26 + ((15 / 292) : ℂ) * ζ ^ 28 - ((547 / 292) : ℂ) * ζ ^ 29 - ((23 / 73) : ℂ) * ζ ^ 30)
private theorem row12_generatorB_mul_eigenbasis_3_1 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        3 1 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        3 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((113 / 146) : ℂ) - ((363 / 146) : ℂ) * ζ ^ 3 + ((113 / 146) : ℂ) * ζ ^ 4 + ((15 / 146) : ℂ) * ζ ^ 5 - ((35 / 73) : ℂ) * ζ ^ 6 + ((41 / 146) : ℂ) * ζ ^ 8 - ((15 / 146) : ℂ) * ζ ^ 9 - ((1 / 2) : ℂ) * ζ ^ 10 + ((11 / 73) : ℂ) * ζ ^ 13 + ((3 / 146) : ℂ) * ζ ^ 14 - ((42 / 73) : ℂ) * ζ ^ 15 + ((239 / 146) : ℂ) * ζ ^ 18 + ((42 / 73) : ℂ) * ζ ^ 19 - ((231 / 146) : ℂ) * ζ ^ 20 + ((35 / 73) : ℂ) * ζ ^ 22 - ((9 / 73) : ℂ) * ζ ^ 23 + ((231 / 146) : ℂ) * ζ ^ 24 + ((125 / 146) : ℂ) * ζ ^ 25 + ((35 / 73) : ℂ) * ζ ^ 26 - ((75 / 146) : ℂ) * ζ ^ 28 - ((125 / 146) : ℂ) * ζ ^ 29 + ((38 / 73) : ℂ) * ζ ^ 30 + ζ ^ 33 - ζ ^ 34 + ζ ^ 35 + ζ ^ 38 - ζ ^ 39 + ζ ^ 43)
private theorem row12_generatorB_mul_eigenbasis_3_2 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        3 2 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        3 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((153 / 146) : ℂ) - ((142 / 73) : ℂ) * ζ ^ 3 - ((153 / 146) : ℂ) * ζ ^ 4 - ((74 / 73) : ℂ) * ζ ^ 5 + ((39 / 73) : ℂ) * ζ ^ 6 + ((110 / 73) : ℂ) * ζ ^ 8 + ((74 / 73) : ℂ) * ζ ^ 9 + ((83 / 146) : ℂ) * ζ ^ 10 + ((43 / 292) : ℂ) * ζ ^ 13 - ((5 / 146) : ℂ) * ζ ^ 14 - ((205 / 146) : ℂ) * ζ ^ 15 + ((211 / 146) : ℂ) * ζ ^ 18 + ((205 / 146) : ℂ) * ζ ^ 19 + ((49 / 146) : ℂ) * ζ ^ 20 - ((39 / 73) : ℂ) * ζ ^ 22 + ((15 / 146) : ℂ) * ζ ^ 23 - ((49 / 146) : ℂ) * ζ ^ 24 + ((28 / 73) : ℂ) * ζ ^ 25 - ((39 / 73) : ℂ) * ζ ^ 26 - ((71 / 292) : ℂ) * ζ ^ 28 - ((28 / 73) : ℂ) * ζ ^ 29 + ((39 / 73) : ℂ) * ζ ^ 30 - ζ ^ 40 + ζ ^ 44)
private theorem row12_generatorB_mul_eigenbasis_3_3 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        3 3 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        3 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((9467 / 10658) : ℂ) - ((819 / 5329) : ℂ) * ζ ^ 3 + ((9467 / 10658) : ℂ) * ζ ^ 4 + ((9277 / 5329) : ℂ) * ζ ^ 5 - ((1150 / 5329) : ℂ) * ζ ^ 6 - ((22657 / 10658) : ℂ) * ζ ^ 8 - ((9277 / 5329) : ℂ) * ζ ^ 9 + ((3048 / 5329) : ℂ) * ζ ^ 10 + ((1685 / 5329) : ℂ) * ζ ^ 13 - ((4198 / 5329) : ℂ) * ζ ^ 14 - ((18583 / 10658) : ℂ) * ζ ^ 15 - ((437 / 10658) : ℂ) * ζ ^ 18 + ((18583 / 10658) : ℂ) * ζ ^ 19 - ((16471 / 10658) : ℂ) * ζ ^ 20 + ((1150 / 5329) : ℂ) * ζ ^ 22 - ((9093 / 10658) : ℂ) * ζ ^ 23 + ((16471 / 10658) : ℂ) * ζ ^ 24 - ((23883 / 10658) : ℂ) * ζ ^ 25 + ((1150 / 5329) : ℂ) * ζ ^ 26 + ((2288 / 5329) : ℂ) * ζ ^ 28 + ((23883 / 10658) : ℂ) * ζ ^ 29 + ((237 / 5329) : ℂ) * ζ ^ 30 - ((42 / 73) : ℂ) * ζ ^ 33 - ((19 / 73) : ℂ) * ζ ^ 34 - ((59 / 73) : ℂ) * ζ ^ 35 + ((19 / 73) : ℂ) * ζ ^ 38 + ((59 / 73) : ℂ) * ζ ^ 39 + ((18 / 73) : ℂ) * ζ ^ 40 - ((59 / 73) : ℂ) * ζ ^ 43 - ((18 / 73) : ℂ) * ζ ^ 44 - ((29 / 73) : ℂ) * ζ ^ 45 + ((18 / 73) : ℂ) * ζ ^ 48 + ((29 / 73) : ℂ) * ζ ^ 49 - ((6 / 73) : ℂ) * ζ ^ 50 - ((29 / 73) : ℂ) * ζ ^ 53 + ((6 / 73) : ℂ) * ζ ^ 54 - ((39 / 73) : ℂ) * ζ ^ 55 - ((6 / 73) : ℂ) * ζ ^ 58 + ((39 / 73) : ℂ) * ζ ^ 59 + ((2 / 73) : ℂ) * ζ ^ 60 - ((39 / 73) : ℂ) * ζ ^ 63 - ((2 / 73) : ℂ) * ζ ^ 64 + ((13 / 73) : ℂ) * ζ ^ 65 + ((2 / 73) : ℂ) * ζ ^ 68 - ((13 / 73) : ℂ) * ζ ^ 69 - ((25 / 73) : ℂ) * ζ ^ 70 + ((13 / 73) : ℂ) * ζ ^ 73 + ((25 / 73) : ℂ) * ζ ^ 74)
private theorem row12_generatorB_mul_eigenbasis_3_4 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        3 4 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        3 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((2091 / 10658) : ℂ) - ((1201 / 10658) : ℂ) * ζ ^ 3 + ((2091 / 10658) : ℂ) * ζ ^ 4 + ((15067 / 5329) : ℂ) * ζ ^ 5 + ((16307 / 10658) : ℂ) * ζ ^ 6 - ((4401 / 10658) : ℂ) * ζ ^ 8 - ((15067 / 5329) : ℂ) * ζ ^ 9 + ((8089 / 5329) : ℂ) * ζ ^ 10 + ((6613 / 21316) : ℂ) * ζ ^ 13 + ((129 / 10658) : ℂ) * ζ ^ 14 - ((4327 / 5329) : ℂ) * ζ ^ 15 - ((8597 / 10658) : ℂ) * ζ ^ 18 + ((4327 / 5329) : ℂ) * ζ ^ 19 + ((3040 / 5329) : ℂ) * ζ ^ 20 - ((16307 / 10658) : ℂ) * ζ ^ 22 - ((1261 / 5329) : ℂ) * ζ ^ 23 - ((3040 / 5329) : ℂ) * ζ ^ 24 - ((5796 / 5329) : ℂ) * ζ ^ 25 - ((16307 / 10658) : ℂ) * ζ ^ 26 + ((7759 / 21316) : ℂ) * ζ ^ 28 + ((5796 / 5329) : ℂ) * ζ ^ 29 + ((20833 / 10658) : ℂ) * ζ ^ 30 + ((16 / 73) : ℂ) * ζ ^ 33 - ((31 / 73) : ℂ) * ζ ^ 34 - ((54 / 73) : ℂ) * ζ ^ 35 + ((31 / 73) : ℂ) * ζ ^ 38 + ((54 / 73) : ℂ) * ζ ^ 39 + ((14 / 73) : ℂ) * ζ ^ 40 - ((54 / 73) : ℂ) * ζ ^ 43 - ((14 / 73) : ℂ) * ζ ^ 44 + ((18 / 73) : ℂ) * ζ ^ 45 + ((14 / 73) : ℂ) * ζ ^ 48 - ((18 / 73) : ℂ) * ζ ^ 49 + ((44 / 73) : ℂ) * ζ ^ 50 + ((18 / 73) : ℂ) * ζ ^ 53 - ((44 / 73) : ℂ) * ζ ^ 54 - ((6 / 73) : ℂ) * ζ ^ 55 + ((44 / 73) : ℂ) * ζ ^ 58 + ((6 / 73) : ℂ) * ζ ^ 59 + ((34 / 73) : ℂ) * ζ ^ 60 - ((6 / 73) : ℂ) * ζ ^ 63 - ((34 / 73) : ℂ) * ζ ^ 64 + ((2 / 73) : ℂ) * ζ ^ 65 + ((34 / 73) : ℂ) * ζ ^ 68 - ((2 / 73) : ℂ) * ζ ^ 69 + ((13 / 73) : ℂ) * ζ ^ 70 + ((2 / 73) : ℂ) * ζ ^ 73 - ((13 / 73) : ℂ) * ζ ^ 74)
private theorem row12_generatorB_mul_eigenbasis_3_5 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        3 5 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        3 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((135 / 146) : ℂ) - ((571 / 292) : ℂ) * ζ ^ 3 + ((135 / 146) : ℂ) * ζ ^ 4 - ((33 / 292) : ℂ) * ζ ^ 5 + ((27 / 73) : ℂ) * ζ ^ 6 - ((199 / 292) : ℂ) * ζ ^ 8 + ((33 / 292) : ℂ) * ζ ^ 9 + ((212 / 73) : ℂ) * ζ ^ 10 + ((377 / 292) : ℂ) * ζ ^ 13 - ((185 / 73) : ℂ) * ζ ^ 14 - ((49 / 292) : ℂ) * ζ ^ 15 + ((667 / 292) : ℂ) * ζ ^ 18 + ((49 / 292) : ℂ) * ζ ^ 19 + ((78 / 73) : ℂ) * ζ ^ 20 - ((27 / 73) : ℂ) * ζ ^ 22 + ((399 / 292) : ℂ) * ζ ^ 23 - ((78 / 73) : ℂ) * ζ ^ 24 - ((225 / 292) : ℂ) * ζ ^ 25 - ((27 / 73) : ℂ) * ζ ^ 26 - ((151 / 292) : ℂ) * ζ ^ 28 + ((225 / 292) : ℂ) * ζ ^ 29 + ((27 / 73) : ℂ) * ζ ^ 30 - ζ ^ 33 + ζ ^ 65 - ζ ^ 69 + ζ ^ 73 + ζ ^ 85 - ζ ^ 89 + ζ ^ 93)
private theorem row12_generatorB_mul_eigenbasis_4_0 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        4 0 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        4 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((27 / 146) : ℂ) - ((143 / 146) : ℂ) * ζ ^ 3 + ((27 / 146) : ℂ) * ζ ^ 4 - ((75 / 146) : ℂ) * ζ ^ 5 - ((13 / 292) : ℂ) * ζ ^ 6 - ((35 / 73) : ℂ) * ζ ^ 8 + ((75 / 146) : ℂ) * ζ ^ 9 - ((177 / 146) : ℂ) * ζ ^ 10 - ((108 / 73) : ℂ) * ζ ^ 13 + ((341 / 292) : ℂ) * ζ ^ 14 - ((161 / 146) : ℂ) * ζ ^ 15 - ((42 / 73) : ℂ) * ζ ^ 18 + ((161 / 146) : ℂ) * ζ ^ 19 - ((523 / 292) : ℂ) * ζ ^ 20 + ((13 / 292) : ℂ) * ζ ^ 22 + ((107 / 146) : ℂ) * ζ ^ 23 + ((523 / 292) : ℂ) * ζ ^ 24 - ((53 / 146) : ℂ) * ζ ^ 25 + ((13 / 292) : ℂ) * ζ ^ 26 - ((251 / 292) : ℂ) * ζ ^ 28 + ((53 / 146) : ℂ) * ζ ^ 29 - ((13 / 292) : ℂ) * ζ ^ 30)
private theorem row12_generatorB_mul_eigenbasis_4_1 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        4 1 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        4 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((61 / 146) : ℂ) - ((7 / 73) : ℂ) * ζ ^ 3 - ((61 / 146) : ℂ) * ζ ^ 4 - ((105 / 146) : ℂ) * ζ ^ 5 - ((313 / 146) : ℂ) * ζ ^ 6 - ((141 / 146) : ℂ) * ζ ^ 8 + ((105 / 146) : ℂ) * ζ ^ 9 + ((1 / 2) : ℂ) * ζ ^ 10 + ((211 / 146) : ℂ) * ζ ^ 13 - ((193 / 73) : ℂ) * ζ ^ 14 + ((223 / 146) : ℂ) * ζ ^ 15 + ((517 / 146) : ℂ) * ζ ^ 18 - ((223 / 146) : ℂ) * ζ ^ 19 - ((31 / 73) : ℂ) * ζ ^ 20 + ((313 / 146) : ℂ) * ζ ^ 22 + ((136 / 73) : ℂ) * ζ ^ 23 + ((31 / 73) : ℂ) * ζ ^ 24 + ((37 / 73) : ℂ) * ζ ^ 25 + ((313 / 146) : ℂ) * ζ ^ 26 + ((80 / 73) : ℂ) * ζ ^ 28 - ((37 / 73) : ℂ) * ζ ^ 29 - ((313 / 146) : ℂ) * ζ ^ 30)
private theorem row12_generatorB_mul_eigenbasis_4_2 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        4 2 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        4 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((49 / 146) : ℂ) - ((185 / 292) : ℂ) * ζ ^ 3 + ((49 / 146) : ℂ) * ζ ^ 4 + ((87 / 146) : ℂ) * ζ ^ 5 + ((111 / 146) : ℂ) * ζ ^ 6 + ((33 / 73) : ℂ) * ζ ^ 8 - ((87 / 146) : ℂ) * ζ ^ 9 + ((149 / 146) : ℂ) * ζ ^ 10 - ((41 / 146) : ℂ) * ζ ^ 13 - ((19 / 73) : ℂ) * ζ ^ 14 - ((171 / 146) : ℂ) * ζ ^ 15 + ((39 / 292) : ℂ) * ζ ^ 18 + ((171 / 146) : ℂ) * ζ ^ 19 - ((51 / 146) : ℂ) * ζ ^ 20 - ((111 / 146) : ℂ) * ζ ^ 22 + ((41 / 146) : ℂ) * ζ ^ 23 + ((51 / 146) : ℂ) * ζ ^ 24 - ((50 / 73) : ℂ) * ζ ^ 25 - ((111 / 146) : ℂ) * ζ ^ 26 - ((7 / 146) : ℂ) * ζ ^ 28 + ((50 / 73) : ℂ) * ζ ^ 29 + ((111 / 146) : ℂ) * ζ ^ 30)
private theorem row12_generatorB_mul_eigenbasis_4_3 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        4 3 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        4 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((4570 / 5329) : ℂ) + ((881 / 10658) : ℂ) * ζ ^ 3 + ((4570 / 5329) : ℂ) * ζ ^ 4 - ((4203 / 5329) : ℂ) * ζ ^ 5 - ((8521 / 5329) : ℂ) * ζ ^ 6 - ((31931 / 10658) : ℂ) * ζ ^ 8 + ((4203 / 5329) : ℂ) * ζ ^ 9 - ((14129 / 10658) : ℂ) * ζ ^ 10 - ((9793 / 10658) : ℂ) * ζ ^ 13 - ((2913 / 10658) : ℂ) * ζ ^ 14 - ((3947 / 10658) : ℂ) * ζ ^ 15 - ((40 / 5329) : ℂ) * ζ ^ 18 + ((3947 / 10658) : ℂ) * ζ ^ 19 - ((7781 / 10658) : ℂ) * ζ ^ 20 + ((8521 / 5329) : ℂ) * ζ ^ 22 - ((7631 / 5329) : ℂ) * ζ ^ 23 + ((7781 / 10658) : ℂ) * ζ ^ 24 - ((6267 / 10658) : ℂ) * ζ ^ 25 + ((8521 / 5329) : ℂ) * ζ ^ 26 + ((5417 / 10658) : ℂ) * ζ ^ 28 + ((6267 / 10658) : ℂ) * ζ ^ 29 - ((8521 / 5329) : ℂ) * ζ ^ 30 - ζ ^ 35 + ζ ^ 39 - ζ ^ 43)
private theorem row12_generatorB_mul_eigenbasis_4_4 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        4 4 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        4 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((6315 / 10658) : ℂ) + ((13967 / 21316) : ℂ) * ζ ^ 3 - ((6315 / 10658) : ℂ) * ζ ^ 4 + ((5126 / 5329) : ℂ) * ζ ^ 5 - ((6109 / 10658) : ℂ) * ζ ^ 6 - ((145 / 10658) : ℂ) * ζ ^ 8 - ((5126 / 5329) : ℂ) * ζ ^ 9 + ((7471 / 5329) : ℂ) * ζ ^ 10 + ((5783 / 5329) : ℂ) * ζ ^ 13 - ((21051 / 10658) : ℂ) * ζ ^ 14 + ((14953 / 10658) : ℂ) * ζ ^ 15 + ((18961 / 21316) : ℂ) * ζ ^ 18 - ((14953 / 10658) : ℂ) * ζ ^ 19 + ((3686 / 5329) : ℂ) * ζ ^ 20 + ((6109 / 10658) : ℂ) * ζ ^ 22 - ((2275 / 10658) : ℂ) * ζ ^ 23 - ((3686 / 5329) : ℂ) * ζ ^ 24 - ((235 / 5329) : ℂ) * ζ ^ 25 + ((6109 / 10658) : ℂ) * ζ ^ 26 + ((4635 / 10658) : ℂ) * ζ ^ 28 + ((235 / 5329) : ℂ) * ζ ^ 29 - ((6109 / 10658) : ℂ) * ζ ^ 30)
private theorem row12_generatorB_mul_eigenbasis_4_5 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        4 5 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        4 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((2 / 73) : ℂ) + ((105 / 73) : ℂ) * ζ ^ 3 + ((2 / 73) : ℂ) * ζ ^ 4 + ((76 / 73) : ℂ) * ζ ^ 5 + ((193 / 292) : ℂ) * ζ ^ 6 + ((149 / 146) : ℂ) * ζ ^ 8 - ((76 / 73) : ℂ) * ζ ^ 9 + ((171 / 146) : ℂ) * ζ ^ 10 + ((323 / 146) : ℂ) * ζ ^ 13 - ((149 / 292) : ℂ) * ζ ^ 14 + ((281 / 146) : ℂ) * ζ ^ 15 + ((111 / 146) : ℂ) * ζ ^ 18 - ((281 / 146) : ℂ) * ζ ^ 19 + ((225 / 292) : ℂ) * ζ ^ 20 - ((193 / 292) : ℂ) * ζ ^ 22 + ((27 / 146) : ℂ) * ζ ^ 23 - ((225 / 292) : ℂ) * ζ ^ 24 + ((167 / 146) : ℂ) * ζ ^ 25 - ((193 / 292) : ℂ) * ζ ^ 26 + ((35 / 292) : ℂ) * ζ ^ 28 - ((167 / 146) : ℂ) * ζ ^ 29 + ((193 / 292) : ℂ) * ζ ^ 30 + ((1 / 2) : ℂ) * ζ ^ 33 - ((1 / 2) : ℂ) * ζ ^ 35 + ((1 / 2) : ℂ) * ζ ^ 39 + ((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 43 - ((1 / 2) : ℂ) * ζ ^ 44 + ((1 / 2) : ℂ) * ζ ^ 48 - ((1 / 2) : ℂ) * ζ ^ 50 + ((1 / 2) : ℂ) * ζ ^ 54 - ((1 / 2) : ℂ) * ζ ^ 55 - ((1 / 2) : ℂ) * ζ ^ 58 + ((1 / 2) : ℂ) * ζ ^ 59 - ((1 / 2) : ℂ) * ζ ^ 63 - ((1 / 2) : ℂ) * ζ ^ 65 + ((1 / 2) : ℂ) * ζ ^ 69 - ((1 / 2) : ℂ) * ζ ^ 70 - ((1 / 2) : ℂ) * ζ ^ 73 + ((1 / 2) : ℂ) * ζ ^ 74 - ((1 / 2) : ℂ) * ζ ^ 78 - ((1 / 2) : ℂ) * ζ ^ 80 + ((1 / 2) : ℂ) * ζ ^ 84 - ((1 / 2) : ℂ) * ζ ^ 85 - ((1 / 2) : ℂ) * ζ ^ 88 + ((1 / 2) : ℂ) * ζ ^ 89 - ((1 / 2) : ℂ) * ζ ^ 93 + ((1 / 2) : ℂ) * ζ ^ 95 - ((1 / 2) : ℂ) * ζ ^ 99 - ((1 / 2) : ℂ) * ζ ^ 100 + ((1 / 2) : ℂ) * ζ ^ 103 + ((1 / 2) : ℂ) * ζ ^ 104)
private theorem row12_generatorB_mul_eigenbasis_5_0 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        5 0 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        5 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((93 / 146) : ℂ) + ((59 / 146) : ℂ) * ζ ^ 3 + ((93 / 146) : ℂ) * ζ ^ 4 - ((117 / 73) : ℂ) * ζ ^ 5 - ((207 / 292) : ℂ) * ζ ^ 6 + ((59 / 146) : ℂ) * ζ ^ 8 + ((117 / 73) : ℂ) * ζ ^ 9 - ((98 / 73) : ℂ) * ζ ^ 10 - ((80 / 73) : ℂ) * ζ ^ 13 + ((185 / 292) : ℂ) * ζ ^ 14 - ((38 / 73) : ℂ) * ζ ^ 15 + ((27 / 146) : ℂ) * ζ ^ 18 + ((38 / 73) : ℂ) * ζ ^ 19 + ((275 / 292) : ℂ) * ζ ^ 20 + ((207 / 292) : ℂ) * ζ ^ 22 + ((18 / 73) : ℂ) * ζ ^ 23 - ((275 / 292) : ℂ) * ζ ^ 24 - ((71 / 73) : ℂ) * ζ ^ 25 + ((207 / 292) : ℂ) * ζ ^ 26 + ((125 / 292) : ℂ) * ζ ^ 28 + ((71 / 73) : ℂ) * ζ ^ 29 - ((207 / 292) : ℂ) * ζ ^ 30)
private theorem row12_generatorB_mul_eigenbasis_5_1 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        5 1 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        5 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((129 / 146) : ℂ) + ((57 / 73) : ℂ) * ζ ^ 3 - ((129 / 146) : ℂ) * ζ ^ 4 - ((21 / 146) : ℂ) * ζ ^ 5 + ((25 / 146) : ℂ) * ζ ^ 6 + ((1 / 146) : ℂ) * ζ ^ 8 + ((21 / 146) : ℂ) * ζ ^ 9 + ((3 / 2) : ℂ) * ζ ^ 10 + ((116 / 73) : ℂ) * ζ ^ 13 - ((97 / 73) : ℂ) * ζ ^ 14 + ((88 / 73) : ℂ) * ζ ^ 15 + ((45 / 146) : ℂ) * ζ ^ 18 - ((88 / 73) : ℂ) * ζ ^ 19 + ((169 / 73) : ℂ) * ζ ^ 20 - ((25 / 146) : ℂ) * ζ ^ 22 + ((144 / 73) : ℂ) * ζ ^ 23 - ((169 / 73) : ℂ) * ζ ^ 24 + ((263 / 146) : ℂ) * ζ ^ 25 - ((25 / 146) : ℂ) * ζ ^ 26 + ((89 / 73) : ℂ) * ζ ^ 28 - ((263 / 146) : ℂ) * ζ ^ 29 + ((25 / 146) : ℂ) * ζ ^ 30)
private theorem row12_generatorB_mul_eigenbasis_5_2 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        5 2 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        5 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((39 / 146) : ℂ) + ((91 / 146) : ℂ) * ζ ^ 3 + ((39 / 146) : ℂ) * ζ ^ 4 - ((41 / 146) : ℂ) * ζ ^ 5 - ((40 / 73) : ℂ) * ζ ^ 6 + ((333 / 292) : ℂ) * ζ ^ 8 + ((41 / 146) : ℂ) * ζ ^ 9 - ((87 / 146) : ℂ) * ζ ^ 10 - ((31 / 292) : ℂ) * ζ ^ 13 + ((7 / 146) : ℂ) * ζ ^ 14 - ((5 / 146) : ℂ) * ζ ^ 15 + ((55 / 146) : ℂ) * ζ ^ 18 + ((5 / 146) : ℂ) * ζ ^ 19 - ((27 / 73) : ℂ) * ζ ^ 20 + ((40 / 73) : ℂ) * ζ ^ 22 - ((115 / 292) : ℂ) * ζ ^ 23 + ((27 / 73) : ℂ) * ζ ^ 24 - ((93 / 146) : ℂ) * ζ ^ 25 + ((40 / 73) : ℂ) * ζ ^ 26 - ((105 / 292) : ℂ) * ζ ^ 28 + ((93 / 146) : ℂ) * ζ ^ 29 - ((40 / 73) : ℂ) * ζ ^ 30)
private theorem row12_generatorB_mul_eigenbasis_5_3 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        5 3 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        5 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((3831 / 5329) : ℂ) - ((2883 / 5329) : ℂ) * ζ ^ 3 - ((3831 / 5329) : ℂ) * ζ ^ 4 - ((3039 / 10658) : ℂ) * ζ ^ 5 - ((142 / 5329) : ℂ) * ζ ^ 6 - ((8839 / 10658) : ℂ) * ζ ^ 8 + ((3039 / 10658) : ℂ) * ζ ^ 9 - ((18477 / 10658) : ℂ) * ζ ^ 10 + ((4261 / 10658) : ℂ) * ζ ^ 13 + ((18193 / 10658) : ℂ) * ζ ^ 14 - ((16791 / 10658) : ℂ) * ζ ^ 15 - ((8330 / 5329) : ℂ) * ζ ^ 18 + ((16791 / 10658) : ℂ) * ζ ^ 19 - ((359 / 10658) : ℂ) * ζ ^ 20 + ((142 / 5329) : ℂ) * ζ ^ 22 + ((2919 / 10658) : ℂ) * ζ ^ 23 + ((359 / 10658) : ℂ) * ζ ^ 24 - ((2655 / 10658) : ℂ) * ζ ^ 25 + ((142 / 5329) : ℂ) * ζ ^ 26 - ((581 / 10658) : ℂ) * ζ ^ 28 + ((2655 / 10658) : ℂ) * ζ ^ 29 - ((142 / 5329) : ℂ) * ζ ^ 30)
private theorem row12_generatorB_mul_eigenbasis_5_4 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        5 4 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        5 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((13381 / 10658) : ℂ) + ((3229 / 10658) : ℂ) * ζ ^ 3 - ((13381 / 10658) : ℂ) * ζ ^ 4 + ((4938 / 5329) : ℂ) * ζ ^ 5 + ((1966 / 5329) : ℂ) * ζ ^ 6 + ((745 / 21316) : ℂ) * ζ ^ 8 - ((4938 / 5329) : ℂ) * ζ ^ 9 - ((3645 / 5329) : ℂ) * ζ ^ 10 + ((23183 / 21316) : ℂ) * ζ ^ 13 + ((5611 / 5329) : ℂ) * ζ ^ 14 - ((455 / 10658) : ℂ) * ζ ^ 15 - ((3411 / 10658) : ℂ) * ζ ^ 18 + ((455 / 10658) : ℂ) * ζ ^ 19 - ((555 / 10658) : ℂ) * ζ ^ 20 - ((1966 / 5329) : ℂ) * ζ ^ 22 + ((2813 / 21316) : ℂ) * ζ ^ 23 + ((555 / 10658) : ℂ) * ζ ^ 24 + ((6987 / 10658) : ℂ) * ζ ^ 25 - ((1966 / 5329) : ℂ) * ζ ^ 26 - ((4643 / 21316) : ℂ) * ζ ^ 28 - ((6987 / 10658) : ℂ) * ζ ^ 29 + ((1966 / 5329) : ℂ) * ζ ^ 30 - ζ ^ 35 + ζ ^ 39 - ζ ^ 43)
private theorem row12_generatorB_mul_eigenbasis_5_5 :
    (alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis)
        5 5 =
      (alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal)
        5 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row12_matrixB,
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12GeneratorBDiagonal,
      alternatingSixAmbientRow12GeneratorBEigenvalue,
      alternatingSixAmbientRow12EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((58 / 73) : ℂ) + ((115 / 146) : ℂ) * ζ ^ 3 - ((58 / 73) : ℂ) * ζ ^ 4 + ((337 / 146) : ℂ) * ζ ^ 5 - ((49 / 292) : ℂ) * ζ ^ 6 + ((139 / 73) : ℂ) * ζ ^ 8 - ((337 / 146) : ℂ) * ζ ^ 9 + ((5 / 146) : ℂ) * ζ ^ 10 + ((415 / 146) : ℂ) * ζ ^ 13 - ((59 / 292) : ℂ) * ζ ^ 14 + ((50 / 73) : ℂ) * ζ ^ 15 + ((33 / 73) : ℂ) * ζ ^ 18 - ((50 / 73) : ℂ) * ζ ^ 19 - ((101 / 292) : ℂ) * ζ ^ 20 + ((49 / 292) : ℂ) * ζ ^ 22 + ((10 / 73) : ℂ) * ζ ^ 23 + ((101 / 292) : ℂ) * ζ ^ 24 + ((24 / 73) : ℂ) * ζ ^ 25 + ((49 / 292) : ℂ) * ζ ^ 26 - ((285 / 292) : ℂ) * ζ ^ 28 - ((24 / 73) : ℂ) * ζ ^ 29 - ((49 / 292) : ℂ) * ζ ^ 30 - ζ ^ 45 + ζ ^ 49 - ζ ^ 53 - ζ ^ 65 + ζ ^ 69 - ζ ^ 73)
/-- The checked row 12 basis diagonalizes the second
generator. -/
theorem alternatingSixAmbientRow12GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row12_matrixB *
        alternatingSixAmbientRow12Eigenbasis =
      alternatingSixAmbientRow12Eigenbasis *
        alternatingSixAmbientRow12GeneratorBDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row12_generatorB_mul_eigenbasis_0_0
  · exact row12_generatorB_mul_eigenbasis_0_1
  · exact row12_generatorB_mul_eigenbasis_0_2
  · exact row12_generatorB_mul_eigenbasis_0_3
  · exact row12_generatorB_mul_eigenbasis_0_4
  · exact row12_generatorB_mul_eigenbasis_0_5
  · exact row12_generatorB_mul_eigenbasis_1_0
  · exact row12_generatorB_mul_eigenbasis_1_1
  · exact row12_generatorB_mul_eigenbasis_1_2
  · exact row12_generatorB_mul_eigenbasis_1_3
  · exact row12_generatorB_mul_eigenbasis_1_4
  · exact row12_generatorB_mul_eigenbasis_1_5
  · exact row12_generatorB_mul_eigenbasis_2_0
  · exact row12_generatorB_mul_eigenbasis_2_1
  · exact row12_generatorB_mul_eigenbasis_2_2
  · exact row12_generatorB_mul_eigenbasis_2_3
  · exact row12_generatorB_mul_eigenbasis_2_4
  · exact row12_generatorB_mul_eigenbasis_2_5
  · exact row12_generatorB_mul_eigenbasis_3_0
  · exact row12_generatorB_mul_eigenbasis_3_1
  · exact row12_generatorB_mul_eigenbasis_3_2
  · exact row12_generatorB_mul_eigenbasis_3_3
  · exact row12_generatorB_mul_eigenbasis_3_4
  · exact row12_generatorB_mul_eigenbasis_3_5
  · exact row12_generatorB_mul_eigenbasis_4_0
  · exact row12_generatorB_mul_eigenbasis_4_1
  · exact row12_generatorB_mul_eigenbasis_4_2
  · exact row12_generatorB_mul_eigenbasis_4_3
  · exact row12_generatorB_mul_eigenbasis_4_4
  · exact row12_generatorB_mul_eigenbasis_4_5
  · exact row12_generatorB_mul_eigenbasis_5_0
  · exact row12_generatorB_mul_eigenbasis_5_1
  · exact row12_generatorB_mul_eigenbasis_5_2
  · exact row12_generatorB_mul_eigenbasis_5_3
  · exact row12_generatorB_mul_eigenbasis_5_4
  · exact row12_generatorB_mul_eigenbasis_5_5


private theorem row12_transformedGeneratorA_0_0 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        0 0 =
      alternatingSixAmbientRow12TransformedGeneratorA
        0 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((321 / 1168) : ℂ) - ((635 / 1168) : ℂ) * ζ ^ 3 - ((321 / 1168) : ℂ) * ζ ^ 4 - ((901 / 1168) : ℂ) * ζ ^ 5 - ((157 / 584) : ℂ) * ζ ^ 6 + ((29 / 73) : ℂ) * ζ ^ 8 + ((141 / 292) : ℂ) * ζ ^ 9 - ((683 / 1168) : ℂ) * ζ ^ 10 - ((113 / 584) : ℂ) * ζ ^ 11 - ((74 / 73) : ℂ) * ζ ^ 13 + ((369 / 1168) : ℂ) * ζ ^ 14 - ((945 / 584) : ℂ) * ζ ^ 15 - ((59 / 1168) : ℂ) * ζ ^ 16 - ((337 / 1168) : ℂ) * ζ ^ 17 - ((363 / 1168) : ℂ) * ζ ^ 18 + ((104 / 73) : ℂ) * ζ ^ 19 + ((339 / 1168) : ℂ) * ζ ^ 20 + ((449 / 584) : ℂ) * ζ ^ 21 + ((157 / 584) : ℂ) * ζ ^ 22 - ((11 / 1168) : ℂ) * ζ ^ 23 - ((199 / 584) : ℂ) * ζ ^ 24 + ((1831 / 1168) : ℂ) * ζ ^ 25 + ((527 / 1168) : ℂ) * ζ ^ 26 + ((113 / 584) : ℂ) * ζ ^ 27 - ((9 / 16) : ℂ) * ζ ^ 28 + ((1089 / 1168) : ℂ) * ζ ^ 29 - ((61 / 292) : ℂ) * ζ ^ 30 + ((50 / 73) : ℂ) * ζ ^ 31 + ((59 / 1168) : ℂ) * ζ ^ 32 - ((961 / 1168) : ℂ) * ζ ^ 33 + ((143 / 1168) : ℂ) * ζ ^ 34 + ((627 / 1168) : ℂ) * ζ ^ 35 + ((479 / 1168) : ℂ) * ζ ^ 36 - ((393 / 292) : ℂ) * ζ ^ 37 - ((71 / 292) : ℂ) * ζ ^ 38 - ((279 / 1168) : ℂ) * ζ ^ 39 + ((67 / 1168) : ℂ) * ζ ^ 40 - ((393 / 292) : ℂ) * ζ ^ 41 - ((213 / 1168) : ℂ) * ζ ^ 42 - ((1473 / 1168) : ℂ) * ζ ^ 43 + ((147 / 584) : ℂ) * ζ ^ 44 - ((303 / 584) : ℂ) * ζ ^ 45 - ((213 / 1168) : ℂ) * ζ ^ 46 - ((287 / 584) : ℂ) * ζ ^ 47 - ((1103 / 1168) : ℂ) * ζ ^ 48 + ((415 / 584) : ℂ) * ζ ^ 49 + ((157 / 584) : ℂ) * ζ ^ 50 - ((287 / 584) : ℂ) * ζ ^ 51 - ((105 / 292) : ℂ) * ζ ^ 52 + ((171 / 1168) : ℂ) * ζ ^ 53 - ((101 / 1168) : ℂ) * ζ ^ 54 + ((105 / 584) : ℂ) * ζ ^ 55 - ((105 / 292) : ℂ) * ζ ^ 56 + ((337 / 1168) : ℂ) * ζ ^ 57 - ((233 / 584) : ℂ) * ζ ^ 58 + ((91 / 292) : ℂ) * ζ ^ 59 + ((105 / 292) : ℂ) * ζ ^ 60 - ((337 / 1168) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_0_1 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        0 1 =
      alternatingSixAmbientRow12TransformedGeneratorA
        0 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((51 / 584) : ℂ) + ((167 / 584) : ℂ) * ζ ^ 3 + ((51 / 584) : ℂ) * ζ ^ 4 - ((137 / 146) : ℂ) * ζ ^ 5 + ((661 / 1168) : ℂ) * ζ ^ 6 + ((809 / 1168) : ℂ) * ζ ^ 8 + ((1529 / 1168) : ℂ) * ζ ^ 9 + ((307 / 1168) : ℂ) * ζ ^ 10 + ((1145 / 1168) : ℂ) * ζ ^ 11 + ((1819 / 1168) : ℂ) * ζ ^ 13 + ((177 / 584) : ℂ) * ζ ^ 14 + ((499 / 584) : ℂ) * ζ ^ 15 + ((347 / 584) : ℂ) * ζ ^ 16 + ((433 / 1168) : ℂ) * ζ ^ 17 + ((763 / 1168) : ℂ) * ζ ^ 18 + ((147 / 1168) : ℂ) * ζ ^ 19 + ((1467 / 584) : ℂ) * ζ ^ 20 - ((19 / 1168) : ℂ) * ζ ^ 21 - ((661 / 1168) : ℂ) * ζ ^ 22 + ((1945 / 1168) : ℂ) * ζ ^ 23 - ((140 / 73) : ℂ) * ζ ^ 24 + ((1341 / 1168) : ℂ) * ζ ^ 25 - ((725 / 1168) : ℂ) * ζ ^ 26 - ((1145 / 1168) : ℂ) * ζ ^ 27 + ((145 / 292) : ℂ) * ζ ^ 28 - ((1979 / 584) : ℂ) * ζ ^ 29 + ((417 / 292) : ℂ) * ζ ^ 30 - ((2553 / 1168) : ℂ) * ζ ^ 31 - ((347 / 584) : ℂ) * ζ ^ 32 - ((1149 / 1168) : ℂ) * ζ ^ 33 - ((1071 / 1168) : ℂ) * ζ ^ 34 - ((55 / 73) : ℂ) * ζ ^ 35 - ((1695 / 1168) : ℂ) * ζ ^ 36 + ((885 / 1168) : ℂ) * ζ ^ 37 - ((1621 / 1168) : ℂ) * ζ ^ 38 + ((617 / 1168) : ℂ) * ζ ^ 39 - ((689 / 292) : ℂ) * ζ ^ 40 + ((885 / 1168) : ℂ) * ζ ^ 41 + ((4 / 73) : ℂ) * ζ ^ 42 - ((2139 / 1168) : ℂ) * ζ ^ 43 + ((2449 / 1168) : ℂ) * ζ ^ 44 - ((1931 / 1168) : ℂ) * ζ ^ 45 + ((4 / 73) : ℂ) * ζ ^ 46 + ((88 / 73) : ℂ) * ζ ^ 47 - ((1311 / 1168) : ℂ) * ζ ^ 48 + ((1389 / 584) : ℂ) * ζ ^ 49 - ((2839 / 1168) : ℂ) * ζ ^ 50 + ((88 / 73) : ℂ) * ζ ^ 51 + ((1001 / 1168) : ℂ) * ζ ^ 52 - ((2017 / 1168) : ℂ) * ζ ^ 53 + ((2775 / 1168) : ℂ) * ζ ^ 54 - ((2049 / 1168) : ℂ) * ζ ^ 55 + ((1001 / 1168) : ℂ) * ζ ^ 56 - ((433 / 1168) : ℂ) * ζ ^ 57 + ((17 / 292) : ℂ) * ζ ^ 58 + ((641 / 1168) : ℂ) * ζ ^ 59 - ((1001 / 1168) : ℂ) * ζ ^ 60 + ((433 / 1168) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_0_2 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        0 2 =
      alternatingSixAmbientRow12TransformedGeneratorA
        0 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((5 / 32) : ℂ) - ((401 / 584) : ℂ) * ζ ^ 3 + ((5 / 32) : ℂ) * ζ ^ 4 - ((651 / 2336) : ℂ) * ζ ^ 5 - ((17 / 1168) : ℂ) * ζ ^ 6 + ((353 / 2336) : ℂ) * ζ ^ 8 + ((3 / 73) : ℂ) * ζ ^ 9 + ((45 / 2336) : ℂ) * ζ ^ 10 - ((1023 / 2336) : ℂ) * ζ ^ 11 - ((351 / 584) : ℂ) * ζ ^ 13 - ((79 / 2336) : ℂ) * ζ ^ 14 + ((79 / 1168) : ℂ) * ζ ^ 15 - ((617 / 2336) : ℂ) * ζ ^ 16 - ((555 / 2336) : ℂ) * ζ ^ 17 + ((953 / 2336) : ℂ) * ζ ^ 18 - ((1181 / 2336) : ℂ) * ζ ^ 19 + ((229 / 2336) : ℂ) * ζ ^ 20 + ((69 / 584) : ℂ) * ζ ^ 21 + ((17 / 1168) : ℂ) * ζ ^ 22 - ((2497 / 2336) : ℂ) * ζ ^ 23 - ((423 / 1168) : ℂ) * ζ ^ 24 - ((43 / 1168) : ℂ) * ζ ^ 25 - ((755 / 2336) : ℂ) * ζ ^ 26 + ((1023 / 2336) : ℂ) * ζ ^ 27 - ((2839 / 2336) : ℂ) * ζ ^ 28 + ((923 / 584) : ℂ) * ζ ^ 29 - ((615 / 584) : ℂ) * ζ ^ 30 + ((2361 / 2336) : ℂ) * ζ ^ 31 + ((617 / 2336) : ℂ) * ζ ^ 32 - ((3799 / 2336) : ℂ) * ζ ^ 33 + ((1637 / 2336) : ℂ) * ζ ^ 34 - ((2891 / 2336) : ℂ) * ζ ^ 35 + ((421 / 1168) : ℂ) * ζ ^ 36 - ((693 / 1168) : ℂ) * ζ ^ 37 - ((1037 / 1168) : ℂ) * ζ ^ 38 + ((1603 / 1168) : ℂ) * ζ ^ 39 - ((1617 / 2336) : ℂ) * ζ ^ 40 - ((693 / 1168) : ℂ) * ζ ^ 41 + ((789 / 2336) : ℂ) * ζ ^ 42 - ((535 / 2336) : ℂ) * ζ ^ 43 + ((1225 / 2336) : ℂ) * ζ ^ 44 - ((1873 / 2336) : ℂ) * ζ ^ 45 + ((789 / 2336) : ℂ) * ζ ^ 46 - ((669 / 1168) : ℂ) * ζ ^ 47 + ((387 / 1168) : ℂ) * ζ ^ 48 + ((1039 / 2336) : ℂ) * ζ ^ 49 + ((199 / 2336) : ℂ) * ζ ^ 50 - ((669 / 1168) : ℂ) * ζ ^ 51 - ((225 / 2336) : ℂ) * ζ ^ 52 + ((19 / 32) : ℂ) * ζ ^ 53 - ((247 / 584) : ℂ) * ζ ^ 54 + ((1031 / 2336) : ℂ) * ζ ^ 55 - ((225 / 2336) : ℂ) * ζ ^ 56 + ((555 / 2336) : ℂ) * ζ ^ 57 + ((83 / 1168) : ℂ) * ζ ^ 58 + ((307 / 2336) : ℂ) * ζ ^ 59 + ((225 / 2336) : ℂ) * ζ ^ 60 - ((555 / 2336) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_0_3 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        0 3 =
      alternatingSixAmbientRow12TransformedGeneratorA
        0 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((3397 / 42632) : ℂ) + ((20125 / 85264) : ℂ) * ζ ^ 3 + ((3397 / 42632) : ℂ) * ζ ^ 4 + ((14915 / 42632) : ℂ) * ζ ^ 5 + ((20275 / 85264) : ℂ) * ζ ^ 6 - ((4363 / 85264) : ℂ) * ζ ^ 8 - ((3901 / 10658) : ℂ) * ζ ^ 9 - ((15959 / 42632) : ℂ) * ζ ^ 10 - ((37525 / 85264) : ℂ) * ζ ^ 11 - ((17045 / 21316) : ℂ) * ζ ^ 13 + ((52193 / 85264) : ℂ) * ζ ^ 14 - ((76565 / 42632) : ℂ) * ζ ^ 15 + ((3835 / 42632) : ℂ) * ζ ^ 16 - ((689 / 42632) : ℂ) * ζ ^ 17 - ((93351 / 85264) : ℂ) * ζ ^ 18 + ((115605 / 85264) : ℂ) * ζ ^ 19 - ((14865 / 42632) : ℂ) * ζ ^ 20 + ((3319 / 21316) : ℂ) * ζ ^ 21 - ((20275 / 85264) : ℂ) * ζ ^ 22 + ((5533 / 85264) : ℂ) * ζ ^ 23 + ((4675 / 10658) : ℂ) * ζ ^ 24 - ((1779 / 85264) : ℂ) * ζ ^ 25 - ((4881 / 85264) : ℂ) * ζ ^ 26 + ((37525 / 85264) : ℂ) * ζ ^ 27 - ((36153 / 42632) : ℂ) * ζ ^ 28 + ((23323 / 85264) : ℂ) * ζ ^ 29 + ((120917 / 85264) : ℂ) * ζ ^ 30 + ((3175 / 5329) : ℂ) * ζ ^ 31 - ((3835 / 42632) : ℂ) * ζ ^ 32 + ((5966 / 5329) : ℂ) * ζ ^ 33 - ((5328 / 5329) : ℂ) * ζ ^ 34 + ((148543 / 85264) : ℂ) * ζ ^ 35 + ((4477 / 85264) : ℂ) * ζ ^ 36 - ((1002 / 5329) : ℂ) * ζ ^ 37 + ((2913 / 85264) : ℂ) * ζ ^ 38 - ((172793 / 85264) : ℂ) * ζ ^ 39 + ((34811 / 42632) : ℂ) * ζ ^ 40 - ((1002 / 5329) : ℂ) * ζ ^ 41 - ((7697 / 42632) : ℂ) * ζ ^ 42 + ((373 / 584) : ℂ) * ζ ^ 43 - ((49805 / 85264) : ℂ) * ζ ^ 44 + ((55297 / 85264) : ℂ) * ζ ^ 45 - ((7697 / 42632) : ℂ) * ζ ^ 46 - ((13275 / 85264) : ℂ) * ζ ^ 47 - ((13629 / 85264) : ℂ) * ζ ^ 48 - ((44777 / 85264) : ℂ) * ζ ^ 49 - ((2299 / 21316) : ℂ) * ζ ^ 50 - ((13275 / 85264) : ℂ) * ζ ^ 51 - ((12147 / 85264) : ℂ) * ζ ^ 52 - ((677 / 21316) : ℂ) * ζ ^ 53 + ((12295 / 42632) : ℂ) * ζ ^ 54 + ((1513 / 85264) : ℂ) * ζ ^ 55 - ((12147 / 85264) : ℂ) * ζ ^ 56 + ((689 / 42632) : ℂ) * ζ ^ 57 + ((1985 / 42632) : ℂ) * ζ ^ 58 + ((5881 / 42632) : ℂ) * ζ ^ 59 + ((12147 / 85264) : ℂ) * ζ ^ 60 - ((689 / 42632) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_0_4 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        0 4 =
      alternatingSixAmbientRow12TransformedGeneratorA
        0 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((74995 / 170528) : ℂ) + ((11873 / 85264) : ℂ) * ζ ^ 3 + ((74995 / 170528) : ℂ) * ζ ^ 4 + ((133767 / 170528) : ℂ) * ζ ^ 5 + ((22213 / 42632) : ℂ) * ζ ^ 6 + ((203299 / 170528) : ℂ) * ζ ^ 8 - ((8793 / 10658) : ℂ) * ζ ^ 9 + ((260835 / 170528) : ℂ) * ζ ^ 10 - ((135517 / 170528) : ℂ) * ζ ^ 11 - ((8715 / 21316) : ℂ) * ζ ^ 13 - ((171983 / 170528) : ℂ) * ζ ^ 14 - ((24251 / 42632) : ℂ) * ζ ^ 15 - ((2239 / 170528) : ℂ) * ζ ^ 16 - ((6921 / 170528) : ℂ) * ζ ^ 17 + ((161655 / 170528) : ℂ) * ζ ^ 18 - ((38513 / 170528) : ℂ) * ζ ^ 19 + ((140317 / 170528) : ℂ) * ζ ^ 20 + ((353 / 42632) : ℂ) * ζ ^ 21 - ((22213 / 42632) : ℂ) * ζ ^ 22 + ((90959 / 170528) : ℂ) * ζ ^ 23 - ((35639 / 42632) : ℂ) * ζ ^ 24 - ((9829 / 42632) : ℂ) * ζ ^ 25 - ((117701 / 170528) : ℂ) * ζ ^ 26 + ((135517 / 170528) : ℂ) * ζ ^ 27 - ((107731 / 170528) : ℂ) * ζ ^ 28 + ((41127 / 85264) : ℂ) * ζ ^ 29 + ((1369 / 85264) : ℂ) * ζ ^ 30 + ((187119 / 170528) : ℂ) * ζ ^ 31 + ((2239 / 170528) : ℂ) * ζ ^ 32 - ((23509 / 170528) : ℂ) * ζ ^ 33 + ((57265 / 170528) : ℂ) * ζ ^ 34 - ((42091 / 170528) : ℂ) * ζ ^ 35 + ((4263 / 21316) : ℂ) * ζ ^ 36 - ((7627 / 85264) : ℂ) * ζ ^ 37 - ((4465 / 5329) : ℂ) * ζ ^ 38 - ((1307 / 5329) : ℂ) * ζ ^ 39 - ((129233 / 170528) : ℂ) * ζ ^ 40 - ((7627 / 85264) : ℂ) * ζ ^ 41 + ((28849 / 170528) : ℂ) * ζ ^ 42 - ((835 / 2336) : ℂ) * ζ ^ 43 + ((158859 / 170528) : ℂ) * ζ ^ 44 - ((25275 / 170528) : ℂ) * ζ ^ 45 + ((28849 / 170528) : ℂ) * ζ ^ 46 - ((25801 / 85264) : ℂ) * ζ ^ 47 - ((46273 / 85264) : ℂ) * ζ ^ 48 + ((12845 / 170528) : ℂ) * ζ ^ 49 - ((102351 / 170528) : ℂ) * ζ ^ 50 - ((25801 / 85264) : ℂ) * ζ ^ 51 - ((31865 / 170528) : ℂ) * ζ ^ 52 + ((34729 / 170528) : ℂ) * ζ ^ 53 + ((36751 / 85264) : ℂ) * ζ ^ 54 + ((20125 / 170528) : ℂ) * ζ ^ 55 - ((31865 / 170528) : ℂ) * ζ ^ 56 + ((6921 / 170528) : ℂ) * ζ ^ 57 + ((1717 / 85264) : ℂ) * ζ ^ 58 + ((31477 / 170528) : ℂ) * ζ ^ 59 + ((31865 / 170528) : ℂ) * ζ ^ 60 - ((6921 / 170528) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_0_5 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        0 5 =
      alternatingSixAmbientRow12TransformedGeneratorA
        0 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((99 / 1168) : ℂ) - ((495 / 584) : ℂ) * ζ ^ 3 + ((99 / 1168) : ℂ) * ζ ^ 4 + ((351 / 1168) : ℂ) * ζ ^ 5 + ((3 / 146) : ℂ) * ζ ^ 6 + ((2237 / 1168) : ℂ) * ζ ^ 8 - ((449 / 1168) : ℂ) * ζ ^ 9 + ((25 / 16) : ℂ) * ζ ^ 10 + ((507 / 1168) : ℂ) * ζ ^ 11 + ((117 / 73) : ℂ) * ζ ^ 13 - ((1801 / 1168) : ℂ) * ζ ^ 14 + ((637 / 1168) : ℂ) * ζ ^ 15 + ((135 / 1168) : ℂ) * ζ ^ 16 - ((49 / 584) : ℂ) * ζ ^ 17 + ((993 / 584) : ℂ) * ζ ^ 18 - ((65 / 584) : ℂ) * ζ ^ 19 + ((541 / 1168) : ℂ) * ζ ^ 20 + ((199 / 584) : ℂ) * ζ ^ 21 - ((3 / 146) : ℂ) * ζ ^ 22 + ((1053 / 1168) : ℂ) * ζ ^ 23 - ((203 / 584) : ℂ) * ζ ^ 24 - ((181 / 584) : ℂ) * ζ ^ 25 + ((3 / 73) : ℂ) * ζ ^ 26 - ((507 / 1168) : ℂ) * ζ ^ 27 - ((3063 / 1168) : ℂ) * ζ ^ 28 + ((337 / 292) : ℂ) * ζ ^ 29 - ((447 / 292) : ℂ) * ζ ^ 30 - ((489 / 1168) : ℂ) * ζ ^ 31 - ((135 / 1168) : ℂ) * ζ ^ 32 - ((1945 / 584) : ℂ) * ζ ^ 33 + ((471 / 292) : ℂ) * ζ ^ 34 + ((41 / 292) : ℂ) * ζ ^ 35 - ((151 / 584) : ℂ) * ζ ^ 36 - ((297 / 584) : ℂ) * ζ ^ 37 - ((543 / 292) : ℂ) * ζ ^ 38 + ((361 / 1168) : ℂ) * ζ ^ 39 - ((313 / 584) : ℂ) * ζ ^ 40 - ((297 / 584) : ℂ) * ζ ^ 41 - ((9 / 146) : ℂ) * ζ ^ 42 - ((389 / 1168) : ℂ) * ζ ^ 43 + ((297 / 584) : ℂ) * ζ ^ 44 - ((279 / 1168) : ℂ) * ζ ^ 45 - ((9 / 146) : ℂ) * ζ ^ 46 - ((9 / 584) : ℂ) * ζ ^ 47 + ((129 / 146) : ℂ) * ζ ^ 48 + ((481 / 1168) : ℂ) * ζ ^ 49 + ((10 / 73) : ℂ) * ζ ^ 50 - ((9 / 584) : ℂ) * ζ ^ 51 + ((167 / 1168) : ℂ) * ζ ^ 52 + ((629 / 584) : ℂ) * ζ ^ 53 - ((11 / 146) : ℂ) * ζ ^ 54 - ((113 / 1168) : ℂ) * ζ ^ 55 + ((167 / 1168) : ℂ) * ζ ^ 56 + ((49 / 584) : ℂ) * ζ ^ 57 + ((1 / 2) : ℂ) * ζ ^ 58 + ((131 / 1168) : ℂ) * ζ ^ 59 - ((167 / 1168) : ℂ) * ζ ^ 60 - ((49 / 584) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_1_0 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        1 0 =
      alternatingSixAmbientRow12TransformedGeneratorA
        1 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((637 / 1168) : ℂ) + ((505 / 1168) : ℂ) * ζ ^ 3 + ((637 / 1168) : ℂ) * ζ ^ 4 + ((1 / 292) : ℂ) * ζ ^ 5 + ((19 / 73) : ℂ) * ζ ^ 6 + ((1215 / 1168) : ℂ) * ζ ^ 8 + ((5 / 73) : ℂ) * ζ ^ 9 + ((451 / 584) : ℂ) * ζ ^ 10 + ((297 / 292) : ℂ) * ζ ^ 11 - ((887 / 1168) : ℂ) * ζ ^ 13 - ((299 / 584) : ℂ) * ζ ^ 14 + ((2697 / 1168) : ℂ) * ζ ^ 15 + ((49 / 1168) : ℂ) * ζ ^ 16 + ((21 / 292) : ℂ) * ζ ^ 17 + ((617 / 584) : ℂ) * ζ ^ 18 - ((1509 / 1168) : ℂ) * ζ ^ 19 + ((61 / 146) : ℂ) * ζ ^ 20 + ((397 / 1168) : ℂ) * ζ ^ 21 - ((19 / 73) : ℂ) * ζ ^ 22 - ((491 / 1168) : ℂ) * ζ ^ 23 - ((439 / 1168) : ℂ) * ζ ^ 24 - ((3 / 16) : ℂ) * ζ ^ 25 - ((1537 / 1168) : ℂ) * ζ ^ 26 - ((297 / 292) : ℂ) * ζ ^ 27 - ((399 / 1168) : ℂ) * ζ ^ 28 + ((7 / 73) : ℂ) * ζ ^ 29 - ((579 / 584) : ℂ) * ζ ^ 30 - ((1397 / 1168) : ℂ) * ζ ^ 31 - ((49 / 1168) : ℂ) * ζ ^ 32 + ((37 / 146) : ℂ) * ζ ^ 33 + ((229 / 1168) : ℂ) * ζ ^ 34 - ((1081 / 1168) : ℂ) * ζ ^ 35 - ((543 / 1168) : ℂ) * ζ ^ 36 - ((229 / 1168) : ℂ) * ζ ^ 37 + ((1305 / 1168) : ℂ) * ζ ^ 38 + ((515 / 292) : ℂ) * ζ ^ 39 - ((901 / 584) : ℂ) * ζ ^ 40 - ((229 / 1168) : ℂ) * ζ ^ 41 + ((1233 / 1168) : ℂ) * ζ ^ 42 + ((163 / 1168) : ℂ) * ζ ^ 43 + ((1357 / 1168) : ℂ) * ζ ^ 44 + ((235 / 1168) : ℂ) * ζ ^ 45 + ((1233 / 1168) : ℂ) * ζ ^ 46 + ((209 / 1168) : ℂ) * ζ ^ 47 + ((335 / 584) : ℂ) * ζ ^ 48 + ((165 / 584) : ℂ) * ζ ^ 49 - ((613 / 1168) : ℂ) * ζ ^ 50 + ((209 / 1168) : ℂ) * ζ ^ 51 + ((247 / 584) : ℂ) * ζ ^ 52 + ((363 / 1168) : ℂ) * ζ ^ 53 - ((155 / 292) : ℂ) * ζ ^ 54 - ((57 / 146) : ℂ) * ζ ^ 55 + ((247 / 584) : ℂ) * ζ ^ 56 - ((21 / 292) : ℂ) * ζ ^ 57 + ((75 / 146) : ℂ) * ζ ^ 58 + ((247 / 1168) : ℂ) * ζ ^ 59 - ((247 / 584) : ℂ) * ζ ^ 60 + ((21 / 292) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_1_1 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        1 1 =
      alternatingSixAmbientRow12TransformedGeneratorA
        1 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((205 / 584) : ℂ) + ((103 / 584) : ℂ) * ζ ^ 3 - ((205 / 584) : ℂ) * ζ ^ 4 - ((39 / 292) : ℂ) * ζ ^ 5 + ((59 / 292) : ℂ) * ζ ^ 6 - ((707 / 1168) : ℂ) * ζ ^ 8 + ((45 / 146) : ℂ) * ζ ^ 9 + ((545 / 584) : ℂ) * ζ ^ 10 - ((11 / 146) : ℂ) * ζ ^ 11 - ((263 / 1168) : ℂ) * ζ ^ 13 - ((427 / 584) : ℂ) * ζ ^ 14 - ((309 / 292) : ℂ) * ζ ^ 15 - ((321 / 584) : ℂ) * ζ ^ 16 + ((51 / 292) : ℂ) * ζ ^ 17 - ((2413 / 1168) : ℂ) * ζ ^ 18 + ((287 / 292) : ℂ) * ζ ^ 19 - ((601 / 292) : ℂ) * ζ ^ 20 - ((275 / 584) : ℂ) * ζ ^ 21 - ((59 / 292) : ℂ) * ζ ^ 22 - ((49 / 73) : ℂ) * ζ ^ 23 + ((881 / 584) : ℂ) * ζ ^ 24 - ((1499 / 584) : ℂ) * ζ ^ 25 - ((465 / 1168) : ℂ) * ζ ^ 26 + ((11 / 146) : ℂ) * ζ ^ 27 - ((2485 / 1168) : ℂ) * ζ ^ 28 + ((153 / 146) : ℂ) * ζ ^ 29 - ((1207 / 584) : ℂ) * ζ ^ 30 + ((39 / 292) : ℂ) * ζ ^ 31 + ((321 / 584) : ℂ) * ζ ^ 32 + ((1017 / 1168) : ℂ) * ζ ^ 33 + ((2421 / 1168) : ℂ) * ζ ^ 34 + ((283 / 584) : ℂ) * ζ ^ 35 + ((829 / 584) : ℂ) * ζ ^ 36 + ((479 / 584) : ℂ) * ζ ^ 37 + ((697 / 584) : ℂ) * ζ ^ 38 - ((293 / 584) : ℂ) * ζ ^ 39 + ((1437 / 1168) : ℂ) * ζ ^ 40 + ((479 / 584) : ℂ) * ζ ^ 41 + ((229 / 1168) : ℂ) * ζ ^ 42 + ((807 / 584) : ℂ) * ζ ^ 43 - ((1063 / 1168) : ℂ) * ζ ^ 44 + ((184 / 73) : ℂ) * ζ ^ 45 + ((229 / 1168) : ℂ) * ζ ^ 46 - ((17 / 292) : ℂ) * ζ ^ 47 + ((1237 / 1168) : ℂ) * ζ ^ 48 - ((1543 / 584) : ℂ) * ζ ^ 49 + ((2543 / 1168) : ℂ) * ζ ^ 50 - ((17 / 292) : ℂ) * ζ ^ 51 - ((127 / 146) : ℂ) * ζ ^ 52 + ((765 / 1168) : ℂ) * ζ ^ 53 - ((693 / 292) : ℂ) * ζ ^ 54 + ((437 / 584) : ℂ) * ζ ^ 55 - ((127 / 146) : ℂ) * ζ ^ 56 - ((51 / 292) : ℂ) * ζ ^ 57 - ((117 / 584) : ℂ) * ζ ^ 58 - ((403 / 584) : ℂ) * ζ ^ 59 + ((127 / 146) : ℂ) * ζ ^ 60 + ((51 / 292) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_1_2 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        1 2 =
      alternatingSixAmbientRow12TransformedGeneratorA
        1 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((883 / 2336) : ℂ) - ((189 / 584) : ℂ) * ζ ^ 3 + ((883 / 2336) : ℂ) * ζ ^ 4 + ((423 / 1168) : ℂ) * ζ ^ 5 + ((145 / 584) : ℂ) * ζ ^ 6 + ((2187 / 2336) : ℂ) * ζ ^ 8 - ((687 / 2336) : ℂ) * ζ ^ 9 + ((399 / 1168) : ℂ) * ζ ^ 10 + ((1465 / 2336) : ℂ) * ζ ^ 11 - ((267 / 1168) : ℂ) * ζ ^ 13 - ((109 / 1168) : ℂ) * ζ ^ 14 + ((285 / 2336) : ℂ) * ζ ^ 15 - ((339 / 2336) : ℂ) * ζ ^ 16 + ((159 / 2336) : ℂ) * ζ ^ 17 + ((1363 / 2336) : ℂ) * ζ ^ 18 + ((295 / 584) : ℂ) * ζ ^ 19 - ((1647 / 2336) : ℂ) * ζ ^ 20 + ((445 / 1168) : ℂ) * ζ ^ 21 - ((145 / 584) : ℂ) * ζ ^ 22 - ((1125 / 2336) : ℂ) * ζ ^ 23 + ((327 / 584) : ℂ) * ζ ^ 24 + ((1681 / 2336) : ℂ) * ζ ^ 25 - ((2045 / 2336) : ℂ) * ζ ^ 26 - ((1465 / 2336) : ℂ) * ζ ^ 27 + ((387 / 2336) : ℂ) * ζ ^ 28 - ((1745 / 2336) : ℂ) * ζ ^ 29 + ((773 / 2336) : ℂ) * ζ ^ 30 - ((2273 / 2336) : ℂ) * ζ ^ 31 + ((339 / 2336) : ℂ) * ζ ^ 32 + ((2841 / 2336) : ℂ) * ζ ^ 33 - ((829 / 1168) : ℂ) * ζ ^ 34 + ((79 / 73) : ℂ) * ζ ^ 35 - ((57 / 146) : ℂ) * ζ ^ 36 - ((143 / 584) : ℂ) * ζ ^ 37 + ((519 / 584) : ℂ) * ζ ^ 38 - ((1871 / 2336) : ℂ) * ζ ^ 39 - ((1573 / 2336) : ℂ) * ζ ^ 40 - ((143 / 584) : ℂ) * ζ ^ 41 + ((1465 / 2336) : ℂ) * ζ ^ 42 + ((3103 / 2336) : ℂ) * ζ ^ 43 - ((17 / 2336) : ℂ) * ζ ^ 44 + ((649 / 1168) : ℂ) * ζ ^ 45 + ((1465 / 2336) : ℂ) * ζ ^ 46 + ((101 / 292) : ℂ) * ζ ^ 47 - ((427 / 1168) : ℂ) * ζ ^ 48 - ((45 / 1168) : ℂ) * ζ ^ 49 - ((447 / 584) : ℂ) * ζ ^ 50 + ((101 / 292) : ℂ) * ζ ^ 51 + ((1251 / 2336) : ℂ) * ζ ^ 52 - ((667 / 2336) : ℂ) * ζ ^ 53 + ((323 / 2336) : ℂ) * ζ ^ 54 + ((51 / 1168) : ℂ) * ζ ^ 55 + ((1251 / 2336) : ℂ) * ζ ^ 56 - ((159 / 2336) : ℂ) * ζ ^ 57 - ((75 / 584) : ℂ) * ζ ^ 58 - ((455 / 1168) : ℂ) * ζ ^ 59 - ((1251 / 2336) : ℂ) * ζ ^ 60 + ((159 / 2336) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_1_3 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        1 3 =
      alternatingSixAmbientRow12TransformedGeneratorA
        1 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((12913 / 42632) : ℂ) - ((6511 / 21316) : ℂ) * ζ ^ 3 - ((12913 / 42632) : ℂ) * ζ ^ 4 - ((66017 / 85264) : ℂ) * ζ ^ 5 + ((4485 / 21316) : ℂ) * ζ ^ 6 - ((31933 / 85264) : ℂ) * ζ ^ 8 + ((72345 / 85264) : ℂ) * ζ ^ 9 + ((23795 / 21316) : ℂ) * ζ ^ 10 + ((607 / 1168) : ℂ) * ζ ^ 11 - ((31513 / 85264) : ℂ) * ζ ^ 13 - ((9655 / 10658) : ℂ) * ζ ^ 14 - ((3031 / 42632) : ℂ) * ζ ^ 15 + ((37287 / 85264) : ℂ) * ζ ^ 16 + ((791 / 10658) : ℂ) * ζ ^ 17 + ((28677 / 21316) : ℂ) * ζ ^ 18 + ((50373 / 85264) : ℂ) * ζ ^ 19 + ((36861 / 21316) : ℂ) * ζ ^ 20 + ((28551 / 85264) : ℂ) * ζ ^ 21 - ((4485 / 21316) : ℂ) * ζ ^ 22 + ((1896 / 5329) : ℂ) * ζ ^ 23 - ((1509 / 1168) : ℂ) * ζ ^ 24 - ((41047 / 21316) : ℂ) * ζ ^ 25 - ((41857 / 42632) : ℂ) * ζ ^ 26 - ((607 / 1168) : ℂ) * ζ ^ 27 - ((50317 / 85264) : ℂ) * ζ ^ 28 + ((154771 / 85264) : ℂ) * ζ ^ 29 + ((55909 / 85264) : ℂ) * ζ ^ 30 - ((81 / 584) : ℂ) * ζ ^ 31 - ((37287 / 85264) : ℂ) * ζ ^ 32 - ((25873 / 42632) : ℂ) * ζ ^ 33 - ((103743 / 85264) : ℂ) * ζ ^ 34 - ((52995 / 42632) : ℂ) * ζ ^ 35 - ((29569 / 42632) : ℂ) * ζ ^ 36 - ((15895 / 85264) : ℂ) * ζ ^ 37 + ((2543 / 10658) : ℂ) * ζ ^ 38 + ((91393 / 42632) : ℂ) * ζ ^ 39 - ((63215 / 85264) : ℂ) * ζ ^ 40 - ((15895 / 85264) : ℂ) * ζ ^ 41 + ((32887 / 42632) : ℂ) * ζ ^ 42 - ((94807 / 85264) : ℂ) * ζ ^ 43 + ((78651 / 85264) : ℂ) * ζ ^ 44 + ((83 / 85264) : ℂ) * ζ ^ 45 + ((32887 / 42632) : ℂ) * ζ ^ 46 - ((445 / 1168) : ℂ) * ζ ^ 47 + ((25357 / 42632) : ℂ) * ζ ^ 48 + ((10281 / 21316) : ℂ) * ζ ^ 49 - ((62775 / 85264) : ℂ) * ζ ^ 50 - ((445 / 1168) : ℂ) * ζ ^ 51 + ((21851 / 85264) : ℂ) * ζ ^ 52 - ((13763 / 42632) : ℂ) * ζ ^ 53 - ((2999 / 85264) : ℂ) * ζ ^ 54 + ((37531 / 85264) : ℂ) * ζ ^ 55 + ((21851 / 85264) : ℂ) * ζ ^ 56 - ((791 / 10658) : ℂ) * ζ ^ 57 - ((1641 / 42632) : ℂ) * ζ ^ 58 - ((2523 / 42632) : ℂ) * ζ ^ 59 - ((21851 / 85264) : ℂ) * ζ ^ 60 + ((791 / 10658) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_1_4 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        1 4 =
      alternatingSixAmbientRow12TransformedGeneratorA
        1 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((65083 / 170528) : ℂ) + ((10693 / 42632) : ℂ) * ζ ^ 3 - ((65083 / 170528) : ℂ) * ζ ^ 4 - ((4367 / 85264) : ℂ) * ζ ^ 5 + ((7625 / 21316) : ℂ) * ζ ^ 6 - ((32843 / 170528) : ℂ) * ζ ^ 8 - ((16649 / 170528) : ℂ) * ζ ^ 9 - ((13337 / 21316) : ℂ) * ζ ^ 10 - ((23 / 2336) : ℂ) * ζ ^ 11 - ((4205 / 5329) : ℂ) * ζ ^ 13 + ((10481 / 10658) : ℂ) * ζ ^ 14 - ((134203 / 170528) : ℂ) * ζ ^ 15 + ((141879 / 170528) : ℂ) * ζ ^ 16 - ((25383 / 170528) : ℂ) * ζ ^ 17 - ((127411 / 170528) : ℂ) * ζ ^ 18 + ((33131 / 42632) : ℂ) * ζ ^ 19 + ((101291 / 170528) : ℂ) * ζ ^ 20 + ((13933 / 85264) : ℂ) * ζ ^ 21 - ((7625 / 21316) : ℂ) * ζ ^ 22 - ((26419 / 170528) : ℂ) * ζ ^ 23 + ((139 / 584) : ℂ) * ζ ^ 24 + ((45543 / 170528) : ℂ) * ζ ^ 25 - ((123011 / 170528) : ℂ) * ζ ^ 26 + ((23 / 2336) : ℂ) * ζ ^ 27 - ((80031 / 170528) : ℂ) * ζ ^ 28 + ((134621 / 170528) : ℂ) * ζ ^ 29 + ((251763 / 170528) : ℂ) * ζ ^ 30 + ((1051 / 2336) : ℂ) * ζ ^ 31 - ((141879 / 170528) : ℂ) * ζ ^ 32 + ((275365 / 170528) : ℂ) * ζ ^ 33 - ((126387 / 85264) : ℂ) * ζ ^ 34 + ((10793 / 21316) : ℂ) * ζ ^ 35 - ((110147 / 85264) : ℂ) * ζ ^ 36 - ((9829 / 21316) : ℂ) * ζ ^ 37 + ((7493 / 85264) : ℂ) * ζ ^ 38 - ((12979 / 170528) : ℂ) * ζ ^ 39 + ((192603 / 170528) : ℂ) * ζ ^ 40 - ((9829 / 21316) : ℂ) * ζ ^ 41 + ((62011 / 170528) : ℂ) * ζ ^ 42 - ((13701 / 170528) : ℂ) * ζ ^ 43 - ((129139 / 170528) : ℂ) * ζ ^ 44 - ((14795 / 85264) : ℂ) * ζ ^ 45 + ((62011 / 170528) : ℂ) * ζ ^ 46 - ((257 / 584) : ℂ) * ζ ^ 47 + ((5731 / 5329) : ℂ) * ζ ^ 48 + ((3345 / 85264) : ℂ) * ζ ^ 49 - ((3565 / 85264) : ℂ) * ζ ^ 50 - ((257 / 584) : ℂ) * ζ ^ 51 + ((78415 / 170528) : ℂ) * ζ ^ 52 - ((1557 / 170528) : ℂ) * ζ ^ 53 - ((54881 / 170528) : ℂ) * ζ ^ 54 + ((51837 / 85264) : ℂ) * ζ ^ 55 + ((78415 / 170528) : ℂ) * ζ ^ 56 + ((25383 / 170528) : ℂ) * ζ ^ 57 + ((4077 / 42632) : ℂ) * ζ ^ 58 - ((14315 / 85264) : ℂ) * ζ ^ 59 - ((78415 / 170528) : ℂ) * ζ ^ 60 - ((25383 / 170528) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_1_5 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        1 5 =
      alternatingSixAmbientRow12TransformedGeneratorA
        1 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((139 / 1168) : ℂ) + ((363 / 1168) : ℂ) * ζ ^ 3 - ((139 / 1168) : ℂ) * ζ ^ 4 + ((351 / 584) : ℂ) * ζ ^ 5 + ((225 / 584) : ℂ) * ζ ^ 6 + ((143 / 292) : ℂ) * ζ ^ 8 - ((201 / 292) : ℂ) * ζ ^ 9 - ((721 / 1168) : ℂ) * ζ ^ 10 + ((205 / 1168) : ℂ) * ζ ^ 11 - ((2053 / 1168) : ℂ) * ζ ^ 13 + ((1171 / 1168) : ℂ) * ζ ^ 14 + ((1 / 1168) : ℂ) * ζ ^ 15 - ((353 / 1168) : ℂ) * ζ ^ 16 - ((51 / 584) : ℂ) * ζ ^ 17 - ((335 / 146) : ℂ) * ζ ^ 18 + ((51 / 292) : ℂ) * ζ ^ 19 - ((681 / 584) : ℂ) * ζ ^ 20 - ((133 / 584) : ℂ) * ζ ^ 21 - ((225 / 584) : ℂ) * ζ ^ 22 - ((107 / 292) : ℂ) * ζ ^ 23 + ((1009 / 1168) : ℂ) * ζ ^ 24 + ((1243 / 1168) : ℂ) * ζ ^ 25 - ((549 / 1168) : ℂ) * ζ ^ 26 - ((205 / 1168) : ℂ) * ζ ^ 27 + ((7 / 146) : ℂ) * ζ ^ 28 - ((897 / 1168) : ℂ) * ζ ^ 29 + ((7 / 146) : ℂ) * ζ ^ 30 - ((473 / 1168) : ℂ) * ζ ^ 31 + ((353 / 1168) : ℂ) * ζ ^ 32 + ((4479 / 1168) : ℂ) * ζ ^ 33 + ((295 / 1168) : ℂ) * ζ ^ 34 + ((1253 / 1168) : ℂ) * ζ ^ 35 + ((59 / 584) : ℂ) * ζ ^ 36 + ((31 / 584) : ℂ) * ζ ^ 37 + ((1569 / 584) : ℂ) * ζ ^ 38 - ((329 / 292) : ℂ) * ζ ^ 39 - ((745 / 1168) : ℂ) * ζ ^ 40 + ((31 / 584) : ℂ) * ζ ^ 41 + ((99 / 1168) : ℂ) * ζ ^ 42 + ((221 / 292) : ℂ) * ζ ^ 43 + ((157 / 1168) : ℂ) * ζ ^ 44 + ((11 / 1168) : ℂ) * ζ ^ 45 + ((99 / 1168) : ℂ) * ζ ^ 46 + ((67 / 292) : ℂ) * ζ ^ 47 + ((121 / 584) : ℂ) * ζ ^ 48 - ((481 / 1168) : ℂ) * ζ ^ 49 + ((9 / 292) : ℂ) * ζ ^ 50 + ((67 / 292) : ℂ) * ζ ^ 51 + ((235 / 1168) : ℂ) * ζ ^ 52 - ((1135 / 1168) : ℂ) * ζ ^ 53 - ((135 / 1168) : ℂ) * ζ ^ 54 + ((189 / 584) : ℂ) * ζ ^ 55 + ((235 / 1168) : ℂ) * ζ ^ 56 + ((51 / 584) : ℂ) * ζ ^ 57 - ((147 / 292) : ℂ) * ζ ^ 58 - ((323 / 584) : ℂ) * ζ ^ 59 - ((235 / 1168) : ℂ) * ζ ^ 60 - ((51 / 584) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_2_0 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        2 0 =
      alternatingSixAmbientRow12TransformedGeneratorA
        2 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((347 / 1168) : ℂ) + ((225 / 1168) : ℂ) * ζ ^ 3 - ((347 / 1168) : ℂ) * ζ ^ 4 + ((837 / 1168) : ℂ) * ζ ^ 5 - ((719 / 584) : ℂ) * ζ ^ 6 + ((183 / 292) : ℂ) * ζ ^ 8 - ((911 / 584) : ℂ) * ζ ^ 9 - ((373 / 1168) : ℂ) * ζ ^ 10 + ((295 / 584) : ℂ) * ζ ^ 11 - ((1 / 73) : ℂ) * ζ ^ 13 - ((1065 / 1168) : ℂ) * ζ ^ 14 + ((209 / 292) : ℂ) * ζ ^ 15 + ((49 / 1168) : ℂ) * ζ ^ 16 - ((985 / 1168) : ℂ) * ζ ^ 17 + ((2027 / 1168) : ℂ) * ζ ^ 18 - ((123 / 584) : ℂ) * ζ ^ 19 - ((393 / 1168) : ℂ) * ζ ^ 20 + ((23 / 292) : ℂ) * ζ ^ 21 + ((719 / 584) : ℂ) * ζ ^ 22 + ((671 / 1168) : ℂ) * ζ ^ 23 + ((221 / 584) : ℂ) * ζ ^ 24 + ((1585 / 1168) : ℂ) * ζ ^ 25 + ((1871 / 1168) : ℂ) * ζ ^ 26 - ((295 / 584) : ℂ) * ζ ^ 27 - ((1567 / 1168) : ℂ) * ζ ^ 28 + ((4417 / 1168) : ℂ) * ζ ^ 29 - ((287 / 292) : ℂ) * ζ ^ 30 - ((135 / 292) : ℂ) * ζ ^ 31 - ((49 / 1168) : ℂ) * ζ ^ 32 + ((1399 / 1168) : ℂ) * ζ ^ 33 + ((143 / 1168) : ℂ) * ζ ^ 34 - ((397 / 1168) : ℂ) * ζ ^ 35 + ((833 / 1168) : ℂ) * ζ ^ 36 - ((1031 / 584) : ℂ) * ζ ^ 37 - ((191 / 584) : ℂ) * ζ ^ 38 + ((1037 / 1168) : ℂ) * ζ ^ 39 - ((787 / 1168) : ℂ) * ζ ^ 40 - ((1031 / 584) : ℂ) * ζ ^ 41 - ((433 / 1168) : ℂ) * ζ ^ 42 - ((129 / 1168) : ℂ) * ζ ^ 43 + ((859 / 584) : ℂ) * ζ ^ 44 - ((1453 / 584) : ℂ) * ζ ^ 45 - ((433 / 1168) : ℂ) * ζ ^ 46 - ((25 / 584) : ℂ) * ζ ^ 47 + ((705 / 1168) : ℂ) * ζ ^ 48 + ((257 / 292) : ℂ) * ζ ^ 49 - ((159 / 584) : ℂ) * ζ ^ 50 - ((25 / 584) : ℂ) * ζ ^ 51 - ((441 / 584) : ℂ) * ζ ^ 52 + ((1995 / 1168) : ℂ) * ζ ^ 53 + ((751 / 1168) : ℂ) * ζ ^ 54 - ((79 / 146) : ℂ) * ζ ^ 55 - ((441 / 584) : ℂ) * ζ ^ 56 + ((985 / 1168) : ℂ) * ζ ^ 57 + ((63 / 584) : ℂ) * ζ ^ 58 + ((341 / 584) : ℂ) * ζ ^ 59 + ((441 / 584) : ℂ) * ζ ^ 60 - ((985 / 1168) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_2_1 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        2 1 =
      alternatingSixAmbientRow12TransformedGeneratorA
        2 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((227 / 584) : ℂ) + ((203 / 584) : ℂ) * ζ ^ 3 + ((227 / 584) : ℂ) * ζ ^ 4 - ((43 / 73) : ℂ) * ζ ^ 5 + ((841 / 1168) : ℂ) * ζ ^ 6 + ((131 / 1168) : ℂ) * ζ ^ 8 + ((611 / 1168) : ℂ) * ζ ^ 9 + ((895 / 1168) : ℂ) * ζ ^ 10 + ((81 / 1168) : ℂ) * ζ ^ 11 - ((125 / 1168) : ℂ) * ζ ^ 13 - ((27 / 584) : ℂ) * ζ ^ 14 - ((569 / 584) : ℂ) * ζ ^ 15 + ((231 / 146) : ℂ) * ζ ^ 16 - ((77 / 1168) : ℂ) * ζ ^ 17 + ((977 / 1168) : ℂ) * ζ ^ 18 + ((1219 / 1168) : ℂ) * ζ ^ 19 + ((237 / 292) : ℂ) * ζ ^ 20 + ((581 / 1168) : ℂ) * ζ ^ 21 - ((841 / 1168) : ℂ) * ζ ^ 22 - ((831 / 1168) : ℂ) * ζ ^ 23 + ((225 / 292) : ℂ) * ζ ^ 24 + ((419 / 1168) : ℂ) * ζ ^ 25 + ((171 / 1168) : ℂ) * ζ ^ 26 - ((81 / 1168) : ℂ) * ζ ^ 27 - ((115 / 584) : ℂ) * ζ ^ 28 + ((39 / 73) : ℂ) * ζ ^ 29 + ((124 / 73) : ℂ) * ζ ^ 30 + ((79 / 1168) : ℂ) * ζ ^ 31 - ((231 / 146) : ℂ) * ζ ^ 32 + ((603 / 1168) : ℂ) * ζ ^ 33 - ((131 / 1168) : ℂ) * ζ ^ 34 + ((839 / 292) : ℂ) * ζ ^ 35 - ((2021 / 1168) : ℂ) * ζ ^ 36 - ((735 / 1168) : ℂ) * ζ ^ 37 + ((297 / 1168) : ℂ) * ζ ^ 38 - ((3115 / 1168) : ℂ) * ζ ^ 39 + ((797 / 292) : ℂ) * ζ ^ 40 - ((735 / 1168) : ℂ) * ζ ^ 41 - ((253 / 292) : ℂ) * ζ ^ 42 + ((2023 / 1168) : ℂ) * ζ ^ 43 - ((1513 / 1168) : ℂ) * ζ ^ 44 + ((2217 / 1168) : ℂ) * ζ ^ 45 - ((253 / 292) : ℂ) * ζ ^ 46 - ((10 / 73) : ℂ) * ζ ^ 47 + ((1417 / 1168) : ℂ) * ζ ^ 48 - ((895 / 584) : ℂ) * ζ ^ 49 + ((1423 / 1168) : ℂ) * ζ ^ 50 - ((10 / 73) : ℂ) * ζ ^ 51 + ((173 / 1168) : ℂ) * ζ ^ 52 + ((1395 / 1168) : ℂ) * ζ ^ 53 - ((411 / 1168) : ℂ) * ζ ^ 54 - ((399 / 1168) : ℂ) * ζ ^ 55 + ((173 / 1168) : ℂ) * ζ ^ 56 + ((77 / 1168) : ℂ) * ζ ^ 57 + ((6 / 73) : ℂ) * ζ ^ 58 + ((559 / 1168) : ℂ) * ζ ^ 59 - ((173 / 1168) : ℂ) * ζ ^ 60 - ((77 / 1168) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_2_2 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        2 2 =
      alternatingSixAmbientRow12TransformedGeneratorA
        2 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((901 / 2336) : ℂ) - ((145 / 1168) : ℂ) * ζ ^ 3 - ((901 / 2336) : ℂ) * ζ ^ 4 + ((2207 / 2336) : ℂ) * ζ ^ 5 - ((1117 / 1168) : ℂ) * ζ ^ 6 + ((1249 / 2336) : ℂ) * ζ ^ 8 - ((1691 / 1168) : ℂ) * ζ ^ 9 + ((1011 / 2336) : ℂ) * ζ ^ 10 - ((187 / 2336) : ℂ) * ζ ^ 11 + ((175 / 1168) : ℂ) * ζ ^ 13 - ((3245 / 2336) : ℂ) * ζ ^ 14 - ((81 / 584) : ℂ) * ζ ^ 15 - ((713 / 2336) : ℂ) * ζ ^ 16 - ((1175 / 2336) : ℂ) * ζ ^ 17 + ((4089 / 2336) : ℂ) * ζ ^ 18 + ((137 / 2336) : ℂ) * ζ ^ 19 + ((1349 / 2336) : ℂ) * ζ ^ 20 - ((97 / 1168) : ℂ) * ζ ^ 21 + ((1117 / 1168) : ℂ) * ζ ^ 22 - ((1113 / 2336) : ℂ) * ζ ^ 23 - ((1031 / 1168) : ℂ) * ζ ^ 24 + ((777 / 584) : ℂ) * ζ ^ 25 + ((1505 / 2336) : ℂ) * ζ ^ 26 + ((187 / 2336) : ℂ) * ζ ^ 27 - ((1255 / 2336) : ℂ) * ζ ^ 28 + ((937 / 584) : ℂ) * ζ ^ 29 + ((901 / 1168) : ℂ) * ζ ^ 30 + ((1007 / 2336) : ℂ) * ζ ^ 31 + ((713 / 2336) : ℂ) * ζ ^ 32 + ((37 / 2336) : ℂ) * ζ ^ 33 - ((4765 / 2336) : ℂ) * ζ ^ 34 + ((2979 / 2336) : ℂ) * ζ ^ 35 + ((9 / 16) : ℂ) * ζ ^ 36 - ((539 / 584) : ℂ) * ζ ^ 37 - ((209 / 1168) : ℂ) * ζ ^ 38 - ((1173 / 1168) : ℂ) * ζ ^ 39 - ((483 / 2336) : ℂ) * ζ ^ 40 - ((539 / 584) : ℂ) * ζ ^ 41 + ((729 / 2336) : ℂ) * ζ ^ 42 + ((323 / 2336) : ℂ) * ζ ^ 43 + ((371 / 2336) : ℂ) * ζ ^ 44 - ((2321 / 2336) : ℂ) * ζ ^ 45 + ((729 / 2336) : ℂ) * ζ ^ 46 - ((205 / 584) : ℂ) * ζ ^ 47 - ((599 / 1168) : ℂ) * ζ ^ 48 - ((223 / 2336) : ℂ) * ζ ^ 49 - ((1661 / 2336) : ℂ) * ζ ^ 50 - ((205 / 584) : ℂ) * ζ ^ 51 - ((601 / 2336) : ℂ) * ζ ^ 52 + ((39 / 32) : ℂ) * ζ ^ 53 + ((233 / 584) : ℂ) * ζ ^ 54 + ((981 / 2336) : ℂ) * ζ ^ 55 - ((601 / 2336) : ℂ) * ζ ^ 56 + ((1175 / 2336) : ℂ) * ζ ^ 57 - ((3 / 1168) : ℂ) * ζ ^ 58 - ((161 / 2336) : ℂ) * ζ ^ 59 + ((601 / 2336) : ℂ) * ζ ^ 60 - ((1175 / 2336) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_2_3 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        2 3 =
      alternatingSixAmbientRow12TransformedGeneratorA
        2 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((23185 / 42632) : ℂ) + ((71061 / 85264) : ℂ) * ζ ^ 3 + ((23185 / 42632) : ℂ) * ζ ^ 4 - ((177 / 5329) : ℂ) * ζ ^ 5 + ((7039 / 85264) : ℂ) * ζ ^ 6 - ((66663 / 85264) : ℂ) * ζ ^ 8 + ((1891 / 42632) : ℂ) * ζ ^ 9 - ((10663 / 21316) : ℂ) * ζ ^ 10 - ((17465 / 85264) : ℂ) * ζ ^ 11 + ((1597 / 5329) : ℂ) * ζ ^ 13 + ((49691 / 85264) : ℂ) * ζ ^ 14 + ((10651 / 21316) : ℂ) * ζ ^ 15 + ((15977 / 42632) : ℂ) * ζ ^ 16 + ((475 / 42632) : ℂ) * ζ ^ 17 - ((59341 / 85264) : ℂ) * ζ ^ 18 - ((60069 / 85264) : ℂ) * ζ ^ 19 - ((46893 / 42632) : ℂ) * ζ ^ 20 - ((30125 / 42632) : ℂ) * ζ ^ 21 - ((7039 / 85264) : ℂ) * ζ ^ 22 + ((18403 / 85264) : ℂ) * ζ ^ 23 + ((31435 / 21316) : ℂ) * ζ ^ 24 - ((78387 / 85264) : ℂ) * ζ ^ 25 + ((54333 / 85264) : ℂ) * ζ ^ 26 + ((17465 / 85264) : ℂ) * ζ ^ 27 - ((21513 / 21316) : ℂ) * ζ ^ 28 + ((12437 / 85264) : ℂ) * ζ ^ 29 - ((40781 / 85264) : ℂ) * ζ ^ 30 - ((1006 / 5329) : ℂ) * ζ ^ 31 - ((15977 / 42632) : ℂ) * ζ ^ 32 - ((10723 / 42632) : ℂ) * ζ ^ 33 + ((13649 / 10658) : ℂ) * ζ ^ 34 - ((151151 / 85264) : ℂ) * ζ ^ 35 - ((53727 / 85264) : ℂ) * ζ ^ 36 + ((31075 / 42632) : ℂ) * ζ ^ 37 - ((91161 / 85264) : ℂ) * ζ ^ 38 + ((100125 / 85264) : ℂ) * ζ ^ 39 - ((1527 / 5329) : ℂ) * ζ ^ 40 + ((31075 / 42632) : ℂ) * ζ ^ 41 - ((15343 / 21316) : ℂ) * ζ ^ 42 - ((31199 / 42632) : ℂ) * ζ ^ 43 + ((34613 / 85264) : ℂ) * ζ ^ 44 - ((16473 / 85264) : ℂ) * ζ ^ 45 - ((15343 / 21316) : ℂ) * ζ ^ 46 + ((33561 / 85264) : ℂ) * ζ ^ 47 + ((25889 / 85264) : ℂ) * ζ ^ 48 - ((41877 / 85264) : ℂ) * ζ ^ 49 + ((32823 / 42632) : ℂ) * ζ ^ 50 + ((33561 / 85264) : ℂ) * ζ ^ 51 + ((21773 / 85264) : ℂ) * ζ ^ 52 - ((1523 / 21316) : ℂ) * ζ ^ 53 - ((2137 / 42632) : ℂ) * ζ ^ 54 - ((23851 / 85264) : ℂ) * ζ ^ 55 + ((21773 / 85264) : ℂ) * ζ ^ 56 - ((475 / 42632) : ℂ) * ζ ^ 57 + ((3619 / 42632) : ℂ) * ζ ^ 58 - ((4855 / 42632) : ℂ) * ζ ^ 59 - ((21773 / 85264) : ℂ) * ζ ^ 60 + ((475 / 42632) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_2_4 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        2 4 =
      alternatingSixAmbientRow12TransformedGeneratorA
        2 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((53875 / 170528) : ℂ) + ((7363 / 21316) : ℂ) * ζ ^ 3 - ((53875 / 170528) : ℂ) * ζ ^ 4 + ((31389 / 170528) : ℂ) * ζ ^ 5 - ((28827 / 42632) : ℂ) * ζ ^ 6 + ((131435 / 170528) : ℂ) * ζ ^ 8 + ((27575 / 85264) : ℂ) * ζ ^ 9 - ((40903 / 170528) : ℂ) * ζ ^ 10 + ((10995 / 170528) : ℂ) * ζ ^ 11 + ((120557 / 85264) : ℂ) * ζ ^ 13 - ((74405 / 170528) : ℂ) * ζ ^ 14 + ((31863 / 85264) : ℂ) * ζ ^ 15 - ((11411 / 170528) : ℂ) * ζ ^ 16 + ((86539 / 170528) : ℂ) * ζ ^ 17 + ((179195 / 170528) : ℂ) * ζ ^ 18 - ((52731 / 170528) : ℂ) * ζ ^ 19 - ((48483 / 170528) : ℂ) * ζ ^ 20 - ((42035 / 85264) : ℂ) * ζ ^ 21 + ((28827 / 42632) : ℂ) * ζ ^ 22 + ((143683 / 170528) : ℂ) * ζ ^ 23 + ((2317 / 10658) : ℂ) * ζ ^ 24 - ((61357 / 85264) : ℂ) * ζ ^ 25 + ((137735 / 170528) : ℂ) * ζ ^ 26 - ((10995 / 170528) : ℂ) * ζ ^ 27 + ((122785 / 170528) : ℂ) * ζ ^ 28 - ((240295 / 85264) : ℂ) * ζ ^ 29 + ((44605 / 42632) : ℂ) * ζ ^ 30 - ((153867 / 170528) : ℂ) * ζ ^ 31 + ((11411 / 170528) : ℂ) * ζ ^ 32 + ((169831 / 170528) : ℂ) * ζ ^ 33 - ((271301 / 170528) : ℂ) * ζ ^ 34 + ((163075 / 170528) : ℂ) * ζ ^ 35 - ((42441 / 42632) : ℂ) * ζ ^ 36 + ((64287 / 42632) : ℂ) * ζ ^ 37 - ((18187 / 42632) : ℂ) * ζ ^ 38 - ((36869 / 21316) : ℂ) * ζ ^ 39 + ((92105 / 170528) : ℂ) * ζ ^ 40 + ((64287 / 42632) : ℂ) * ζ ^ 41 - ((22427 / 170528) : ℂ) * ζ ^ 42 + ((166799 / 170528) : ℂ) * ζ ^ 43 - ((284691 / 170528) : ℂ) * ζ ^ 44 + ((302121 / 170528) : ℂ) * ζ ^ 45 - ((22427 / 170528) : ℂ) * ζ ^ 46 + ((17859 / 21316) : ℂ) * ζ ^ 47 + ((51899 / 85264) : ℂ) * ζ ^ 48 - ((213113 / 170528) : ℂ) * ζ ^ 49 - ((13735 / 170528) : ℂ) * ζ ^ 50 + ((17859 / 21316) : ℂ) * ζ ^ 51 + ((181175 / 170528) : ℂ) * ζ ^ 52 - ((213187 / 170528) : ℂ) * ζ ^ 53 + ((18081 / 85264) : ℂ) * ζ ^ 54 - ((76481 / 170528) : ℂ) * ζ ^ 55 + ((181175 / 170528) : ℂ) * ζ ^ 56 - ((86539 / 170528) : ℂ) * ζ ^ 57 + ((12451 / 85264) : ℂ) * ζ ^ 58 - ((66391 / 170528) : ℂ) * ζ ^ 59 - ((181175 / 170528) : ℂ) * ζ ^ 60 + ((86539 / 170528) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_2_5 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        2 5 =
      alternatingSixAmbientRow12TransformedGeneratorA
        2 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((225 / 1168) : ℂ) + ((355 / 584) : ℂ) * ζ ^ 3 + ((225 / 1168) : ℂ) * ζ ^ 4 + ((329 / 1168) : ℂ) * ζ ^ 5 - ((84 / 73) : ℂ) * ζ ^ 6 + ((951 / 1168) : ℂ) * ζ ^ 8 - ((741 / 1168) : ℂ) * ζ ^ 9 - ((215 / 1168) : ℂ) * ζ ^ 10 + ((593 / 1168) : ℂ) * ζ ^ 11 - ((169 / 584) : ℂ) * ζ ^ 13 - ((1129 / 1168) : ℂ) * ζ ^ 14 + ((785 / 1168) : ℂ) * ζ ^ 15 + ((711 / 1168) : ℂ) * ζ ^ 16 - ((103 / 292) : ℂ) * ζ ^ 17 + ((609 / 292) : ℂ) * ζ ^ 18 - ((12 / 73) : ℂ) * ζ ^ 19 + ((903 / 1168) : ℂ) * ζ ^ 20 + ((163 / 292) : ℂ) * ζ ^ 21 + ((84 / 73) : ℂ) * ζ ^ 22 + ((323 / 1168) : ℂ) * ζ ^ 23 - ((12 / 73) : ℂ) * ζ ^ 24 + ((203 / 146) : ℂ) * ζ ^ 25 + ((977 / 584) : ℂ) * ζ ^ 26 - ((593 / 1168) : ℂ) * ζ ^ 27 + ((273 / 1168) : ℂ) * ζ ^ 28 + ((375 / 292) : ℂ) * ζ ^ 29 + ((551 / 292) : ℂ) * ζ ^ 30 - ((485 / 1168) : ℂ) * ζ ^ 31 - ((711 / 1168) : ℂ) * ζ ^ 32 + ((885 / 292) : ℂ) * ζ ^ 33 - ((1469 / 584) : ℂ) * ζ ^ 34 + ((783 / 584) : ℂ) * ζ ^ 35 - ((245 / 584) : ℂ) * ζ ^ 36 - ((369 / 292) : ℂ) * ζ ^ 37 + ((927 / 584) : ℂ) * ζ ^ 38 - ((865 / 1168) : ℂ) * ζ ^ 39 + ((9 / 146) : ℂ) * ζ ^ 40 - ((369 / 292) : ℂ) * ζ ^ 41 - ((305 / 584) : ℂ) * ζ ^ 42 + ((1621 / 1168) : ℂ) * ζ ^ 43 + ((215 / 292) : ℂ) * ζ ^ 44 - ((83 / 1168) : ℂ) * ζ ^ 45 - ((305 / 584) : ℂ) * ζ ^ 46 - ((27 / 292) : ℂ) * ζ ^ 47 + ((195 / 292) : ℂ) * ζ ^ 48 - ((89 / 1168) : ℂ) * ζ ^ 49 - ((187 / 584) : ℂ) * ζ ^ 50 - ((27 / 292) : ℂ) * ζ ^ 51 - ((221 / 1168) : ℂ) * ζ ^ 52 + ((123 / 292) : ℂ) * ζ ^ 53 + ((123 / 146) : ℂ) * ζ ^ 54 + ((141 / 1168) : ℂ) * ζ ^ 55 - ((221 / 1168) : ℂ) * ζ ^ 56 + ((103 / 292) : ℂ) * ζ ^ 57 + ((3 / 73) : ℂ) * ζ ^ 58 - ((33 / 1168) : ℂ) * ζ ^ 59 + ((221 / 1168) : ℂ) * ζ ^ 60 - ((103 / 292) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_3_0 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        3 0 =
      alternatingSixAmbientRow12TransformedGeneratorA
        3 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((311 / 1168) : ℂ) - ((689 / 1168) : ℂ) * ζ ^ 3 - ((311 / 1168) : ℂ) * ζ ^ 4 + ((33 / 146) : ℂ) * ζ ^ 5 - ((225 / 584) : ℂ) * ζ ^ 6 - ((1601 / 1168) : ℂ) * ζ ^ 8 + ((255 / 584) : ℂ) * ζ ^ 9 - ((293 / 584) : ℂ) * ζ ^ 10 - ((973 / 584) : ℂ) * ζ ^ 11 - ((647 / 1168) : ℂ) * ζ ^ 13 + ((17 / 146) : ℂ) * ζ ^ 14 - ((2211 / 1168) : ℂ) * ζ ^ 15 - ((1093 / 1168) : ℂ) * ζ ^ 16 + ((387 / 584) : ℂ) * ζ ^ 17 - ((1713 / 584) : ℂ) * ζ ^ 18 + ((265 / 1168) : ℂ) * ζ ^ 19 - ((435 / 292) : ℂ) * ζ ^ 20 - ((989 / 1168) : ℂ) * ζ ^ 21 + ((225 / 584) : ℂ) * ζ ^ 22 - ((83 / 1168) : ℂ) * ζ ^ 23 + ((647 / 1168) : ℂ) * ζ ^ 24 - ((2973 / 1168) : ℂ) * ζ ^ 25 + ((1315 / 1168) : ℂ) * ζ ^ 26 + ((973 / 584) : ℂ) * ζ ^ 27 + ((1357 / 1168) : ℂ) * ζ ^ 28 - ((665 / 292) : ℂ) * ζ ^ 29 + ((1 / 292) : ℂ) * ζ ^ 30 + ((1561 / 1168) : ℂ) * ζ ^ 31 + ((1093 / 1168) : ℂ) * ζ ^ 32 + ((13 / 292) : ℂ) * ζ ^ 33 + ((411 / 1168) : ℂ) * ζ ^ 34 - ((243 / 1168) : ℂ) * ζ ^ 35 + ((155 / 1168) : ℂ) * ζ ^ 36 + ((2537 / 1168) : ℂ) * ζ ^ 37 - ((393 / 1168) : ℂ) * ζ ^ 38 - ((261 / 146) : ℂ) * ζ ^ 39 + ((399 / 584) : ℂ) * ζ ^ 40 + ((2537 / 1168) : ℂ) * ζ ^ 41 - ((865 / 1168) : ℂ) * ζ ^ 42 + ((127 / 1168) : ℂ) * ζ ^ 43 - ((2829 / 1168) : ℂ) * ζ ^ 44 + ((3123 / 1168) : ℂ) * ζ ^ 45 - ((865 / 1168) : ℂ) * ζ ^ 46 + ((385 / 1168) : ℂ) * ζ ^ 47 + ((317 / 584) : ℂ) * ζ ^ 48 - ((641 / 292) : ℂ) * ζ ^ 49 + ((1305 / 1168) : ℂ) * ζ ^ 50 + ((385 / 1168) : ℂ) * ζ ^ 51 + ((469 / 584) : ℂ) * ζ ^ 52 - ((1287 / 1168) : ℂ) * ζ ^ 53 - ((55 / 146) : ℂ) * ζ ^ 54 - ((123 / 584) : ℂ) * ζ ^ 55 + ((469 / 584) : ℂ) * ζ ^ 56 - ((387 / 584) : ℂ) * ζ ^ 57 - ((51 / 292) : ℂ) * ζ ^ 58 - ((139 / 1168) : ℂ) * ζ ^ 59 - ((469 / 584) : ℂ) * ζ ^ 60 + ((387 / 584) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_3_1 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        3 1 =
      alternatingSixAmbientRow12TransformedGeneratorA
        3 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((93 / 584) : ℂ) - ((931 / 584) : ℂ) * ζ ^ 3 + ((93 / 584) : ℂ) * ζ ^ 4 - ((44 / 73) : ℂ) * ζ ^ 5 - ((319 / 146) : ℂ) * ζ ^ 6 - ((735 / 1168) : ℂ) * ζ ^ 8 + ((249 / 584) : ℂ) * ζ ^ 9 - ((1429 / 584) : ℂ) * ζ ^ 10 - ((287 / 292) : ℂ) * ζ ^ 11 - ((3039 / 1168) : ℂ) * ζ ^ 13 + ((153 / 584) : ℂ) * ζ ^ 14 - ((97 / 73) : ℂ) * ζ ^ 15 - ((501 / 584) : ℂ) * ζ ^ 16 - ((103 / 584) : ℂ) * ζ ^ 17 + ((113 / 1168) : ℂ) * ζ ^ 18 + ((101 / 292) : ℂ) * ζ ^ 19 - ((287 / 292) : ℂ) * ζ ^ 20 - ((33 / 292) : ℂ) * ζ ^ 21 + ((319 / 146) : ℂ) * ζ ^ 22 + ((43 / 146) : ℂ) * ζ ^ 23 + ((1 / 8) : ℂ) * ζ ^ 24 - ((179 / 292) : ℂ) * ζ ^ 25 + ((3121 / 1168) : ℂ) * ζ ^ 26 + ((287 / 292) : ℂ) * ζ ^ 27 + ((877 / 1168) : ℂ) * ζ ^ 28 + ((455 / 292) : ℂ) * ζ ^ 29 - ((581 / 292) : ℂ) * ζ ^ 30 + ((243 / 292) : ℂ) * ζ ^ 31 + ((501 / 584) : ℂ) * ζ ^ 32 + ((413 / 1168) : ℂ) * ζ ^ 33 + ((341 / 1168) : ℂ) * ζ ^ 34 - ((555 / 292) : ℂ) * ζ ^ 35 + ((887 / 584) : ℂ) * ζ ^ 36 - ((35 / 146) : ℂ) * ζ ^ 37 - ((52 / 73) : ℂ) * ζ ^ 38 + ((56 / 73) : ℂ) * ζ ^ 39 + ((39 / 1168) : ℂ) * ζ ^ 40 - ((35 / 146) : ℂ) * ζ ^ 41 - ((569 / 1168) : ℂ) * ζ ^ 42 - ((263 / 584) : ℂ) * ζ ^ 43 - ((269 / 1168) : ℂ) * ζ ^ 44 + ((14 / 73) : ℂ) * ζ ^ 45 - ((569 / 1168) : ℂ) * ζ ^ 46 + ((11 / 73) : ℂ) * ζ ^ 47 + ((87 / 1168) : ℂ) * ζ ^ 48 - ((48 / 73) : ℂ) * ζ ^ 49 + ((1157 / 1168) : ℂ) * ζ ^ 50 + ((11 / 73) : ℂ) * ζ ^ 51 - ((193 / 292) : ℂ) * ζ ^ 52 + ((633 / 1168) : ℂ) * ζ ^ 53 - ((147 / 292) : ℂ) * ζ ^ 54 + ((451 / 584) : ℂ) * ζ ^ 55 - ((193 / 292) : ℂ) * ζ ^ 56 + ((103 / 584) : ℂ) * ζ ^ 57 + ((259 / 584) : ℂ) * ζ ^ 58 - ((539 / 584) : ℂ) * ζ ^ 59 + ((193 / 292) : ℂ) * ζ ^ 60 - ((103 / 584) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_3_2 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        3 2 =
      alternatingSixAmbientRow12TransformedGeneratorA
        3 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((575 / 2336) : ℂ) - ((181 / 1168) : ℂ) * ζ ^ 3 + ((575 / 2336) : ℂ) * ζ ^ 4 - ((679 / 1168) : ℂ) * ζ ^ 5 - ((22 / 73) : ℂ) * ζ ^ 6 - ((4265 / 2336) : ℂ) * ζ ^ 8 + ((2071 / 2336) : ℂ) * ζ ^ 9 - ((655 / 584) : ℂ) * ζ ^ 10 - ((2943 / 2336) : ℂ) * ζ ^ 11 - ((2515 / 1168) : ℂ) * ζ ^ 13 + ((479 / 584) : ℂ) * ζ ^ 14 - ((4565 / 2336) : ℂ) * ζ ^ 15 + ((989 / 2336) : ℂ) * ζ ^ 16 + ((713 / 2336) : ℂ) * ζ ^ 17 - ((1737 / 2336) : ℂ) * ζ ^ 18 + ((811 / 1168) : ℂ) * ζ ^ 19 + ((1461 / 2336) : ℂ) * ζ ^ 20 + ((1013 / 1168) : ℂ) * ζ ^ 21 + ((22 / 73) : ℂ) * ζ ^ 22 + ((2437 / 2336) : ℂ) * ζ ^ 23 - ((59 / 292) : ℂ) * ζ ^ 24 - ((1949 / 2336) : ℂ) * ζ ^ 25 + ((3017 / 2336) : ℂ) * ζ ^ 26 + ((2943 / 2336) : ℂ) * ζ ^ 27 + ((3799 / 2336) : ℂ) * ζ ^ 28 - ((303 / 2336) : ℂ) * ζ ^ 29 + ((1297 / 2336) : ℂ) * ζ ^ 30 + ((3095 / 2336) : ℂ) * ζ ^ 31 - ((989 / 2336) : ℂ) * ζ ^ 32 + ((2067 / 2336) : ℂ) * ζ ^ 33 + ((39 / 292) : ℂ) * ζ ^ 34 - ((531 / 1168) : ℂ) * ζ ^ 35 - ((459 / 584) : ℂ) * ζ ^ 36 - ((75 / 292) : ℂ) * ζ ^ 37 - ((231 / 1168) : ℂ) * ζ ^ 38 - ((1729 / 2336) : ℂ) * ζ ^ 39 + ((1783 / 2336) : ℂ) * ζ ^ 40 - ((75 / 292) : ℂ) * ζ ^ 41 - ((2313 / 2336) : ℂ) * ζ ^ 42 - ((1487 / 2336) : ℂ) * ζ ^ 43 - ((1641 / 2336) : ℂ) * ζ ^ 44 + ((1901 / 1168) : ℂ) * ζ ^ 45 - ((2313 / 2336) : ℂ) * ζ ^ 46 - ((19 / 292) : ℂ) * ζ ^ 47 - ((151 / 1168) : ℂ) * ζ ^ 48 - ((175 / 1168) : ℂ) * ζ ^ 49 + ((389 / 1168) : ℂ) * ζ ^ 50 - ((19 / 292) : ℂ) * ζ ^ 51 + ((847 / 2336) : ℂ) * ζ ^ 52 - ((2025 / 2336) : ℂ) * ζ ^ 53 + ((1535 / 2336) : ℂ) * ζ ^ 54 - ((215 / 584) : ℂ) * ζ ^ 55 + ((847 / 2336) : ℂ) * ζ ^ 56 - ((713 / 2336) : ℂ) * ζ ^ 57 + ((123 / 1168) : ℂ) * ζ ^ 58 + ((253 / 584) : ℂ) * ζ ^ 59 - ((847 / 2336) : ℂ) * ζ ^ 60 + ((713 / 2336) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_3_3 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        3 3 =
      alternatingSixAmbientRow12TransformedGeneratorA
        3 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((1951 / 42632) : ℂ) - ((11629 / 21316) : ℂ) * ζ ^ 3 - ((1951 / 42632) : ℂ) * ζ ^ 4 + ((70507 / 85264) : ℂ) * ζ ^ 5 - ((4647 / 5329) : ℂ) * ζ ^ 6 + ((135665 / 85264) : ℂ) * ζ ^ 8 - ((49375 / 85264) : ℂ) * ζ ^ 9 - ((119 / 10658) : ℂ) * ζ ^ 10 + ((58485 / 85264) : ℂ) * ζ ^ 11 + ((238539 / 85264) : ℂ) * ζ ^ 13 - ((9175 / 10658) : ℂ) * ζ ^ 14 + ((94957 / 42632) : ℂ) * ζ ^ 15 - ((160591 / 85264) : ℂ) * ζ ^ 16 + ((5283 / 21316) : ℂ) * ζ ^ 17 - ((11319 / 42632) : ℂ) * ζ ^ 18 - ((131429 / 85264) : ℂ) * ζ ^ 19 - ((7927 / 10658) : ℂ) * ζ ^ 20 - ((86933 / 85264) : ℂ) * ζ ^ 21 + ((4647 / 5329) : ℂ) * ζ ^ 22 - ((939 / 21316) : ℂ) * ζ ^ 23 - ((97175 / 85264) : ℂ) * ζ ^ 24 + ((26901 / 21316) : ℂ) * ζ ^ 25 + ((12673 / 10658) : ℂ) * ζ ^ 26 - ((58485 / 85264) : ℂ) * ζ ^ 27 + ((94251 / 85264) : ℂ) * ζ ^ 28 - ((321329 / 85264) : ℂ) * ζ ^ 29 - ((103935 / 85264) : ℂ) * ζ ^ 30 - ((54439 / 42632) : ℂ) * ζ ^ 31 + ((160591 / 85264) : ℂ) * ζ ^ 32 - ((23383 / 42632) : ℂ) * ζ ^ 33 + ((56615 / 85264) : ℂ) * ζ ^ 34 - ((2267 / 21316) : ℂ) * ζ ^ 35 + ((110417 / 42632) : ℂ) * ζ ^ 36 + ((129197 / 85264) : ℂ) * ζ ^ 37 + ((28661 / 42632) : ℂ) * ζ ^ 38 + ((2145 / 10658) : ℂ) * ζ ^ 39 - ((170123 / 85264) : ℂ) * ζ ^ 40 + ((129197 / 85264) : ℂ) * ζ ^ 41 - ((3379 / 10658) : ℂ) * ζ ^ 42 - ((3033 / 85264) : ℂ) * ζ ^ 43 + ((69775 / 85264) : ℂ) * ζ ^ 44 - ((73429 / 85264) : ℂ) * ζ ^ 45 - ((3379 / 10658) : ℂ) * ζ ^ 46 + ((50393 / 85264) : ℂ) * ζ ^ 47 - ((11187 / 21316) : ℂ) * ζ ^ 48 + ((3595 / 10658) : ℂ) * ζ ^ 49 + ((39205 / 85264) : ℂ) * ζ ^ 50 + ((50393 / 85264) : ℂ) * ζ ^ 51 - ((60243 / 85264) : ℂ) * ζ ^ 52 - ((13109 / 42632) : ℂ) * ζ ^ 53 - ((12173 / 85264) : ℂ) * ζ ^ 54 - ((24841 / 85264) : ℂ) * ζ ^ 55 - ((60243 / 85264) : ℂ) * ζ ^ 56 - ((5283 / 21316) : ℂ) * ζ ^ 57 + ((243 / 42632) : ℂ) * ζ ^ 58 - ((1597 / 5329) : ℂ) * ζ ^ 59 + ((60243 / 85264) : ℂ) * ζ ^ 60 + ((5283 / 21316) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_3_4 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        3 4 =
      alternatingSixAmbientRow12TransformedGeneratorA
        3 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((165537 / 170528) : ℂ) - ((144211 / 85264) : ℂ) * ζ ^ 3 + ((165537 / 170528) : ℂ) * ζ ^ 4 - ((143705 / 85264) : ℂ) * ζ ^ 5 - ((16675 / 42632) : ℂ) * ζ ^ 6 - ((144727 / 170528) : ℂ) * ζ ^ 8 + ((349993 / 170528) : ℂ) * ζ ^ 9 - ((45895 / 85264) : ℂ) * ζ ^ 10 + ((190281 / 170528) : ℂ) * ζ ^ 11 + ((30703 / 42632) : ℂ) * ζ ^ 13 + ((12545 / 85264) : ℂ) * ζ ^ 14 + ((160607 / 170528) : ℂ) * ζ ^ 15 - ((249573 / 170528) : ℂ) * ζ ^ 16 + ((62583 / 170528) : ℂ) * ζ ^ 17 - ((215695 / 170528) : ℂ) * ζ ^ 18 + ((14837 / 85264) : ℂ) * ζ ^ 19 - ((226681 / 170528) : ℂ) * ζ ^ 20 - ((49251 / 85264) : ℂ) * ζ ^ 21 + ((16675 / 42632) : ℂ) * ζ ^ 22 - ((102957 / 170528) : ℂ) * ζ ^ 23 - ((5723 / 42632) : ℂ) * ζ ^ 24 - ((220903 / 170528) : ℂ) * ζ ^ 25 + ((116431 / 170528) : ℂ) * ζ ^ 26 - ((190281 / 170528) : ℂ) * ζ ^ 27 - ((84919 / 170528) : ℂ) * ζ ^ 28 - ((253097 / 170528) : ℂ) * ζ ^ 29 - ((271201 / 170528) : ℂ) * ζ ^ 30 - ((109741 / 170528) : ℂ) * ζ ^ 31 + ((249573 / 170528) : ℂ) * ζ ^ 32 - ((256261 / 170528) : ℂ) * ζ ^ 33 + ((31779 / 21316) : ℂ) * ζ ^ 34 + ((7977 / 85264) : ℂ) * ζ ^ 35 + ((192727 / 85264) : ℂ) * ζ ^ 36 + ((55917 / 42632) : ℂ) * ζ ^ 37 + ((19399 / 21316) : ℂ) * ζ ^ 38 + ((254867 / 170528) : ℂ) * ζ ^ 39 - ((283705 / 170528) : ℂ) * ζ ^ 40 + ((55917 / 42632) : ℂ) * ζ ^ 41 - ((49731 / 170528) : ℂ) * ζ ^ 42 - ((89179 / 170528) : ℂ) * ζ ^ 43 + ((170013 / 170528) : ℂ) * ζ ^ 44 + ((54757 / 85264) : ℂ) * ζ ^ 45 - ((49731 / 170528) : ℂ) * ζ ^ 46 - ((20135 / 42632) : ℂ) * ζ ^ 47 - ((233 / 21316) : ℂ) * ζ ^ 48 - ((41425 / 85264) : ℂ) * ζ ^ 49 + ((33687 / 42632) : ℂ) * ζ ^ 50 - ((20135 / 42632) : ℂ) * ζ ^ 51 - ((135881 / 170528) : ℂ) * ζ ^ 52 - ((97391 / 170528) : ℂ) * ζ ^ 53 - ((85017 / 170528) : ℂ) * ζ ^ 54 + ((1643 / 5329) : ℂ) * ζ ^ 55 - ((135881 / 170528) : ℂ) * ζ ^ 56 - ((62583 / 170528) : ℂ) * ζ ^ 57 - ((19551 / 85264) : ℂ) * ζ ^ 58 + ((6991 / 42632) : ℂ) * ζ ^ 59 + ((135881 / 170528) : ℂ) * ζ ^ 60 + ((62583 / 170528) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_3_5 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        3 5 =
      alternatingSixAmbientRow12TransformedGeneratorA
        3 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((769 / 1168) : ℂ) - ((2159 / 1168) : ℂ) * ζ ^ 3 + ((769 / 1168) : ℂ) * ζ ^ 4 - ((1273 / 584) : ℂ) * ζ ^ 5 - ((193 / 146) : ℂ) * ζ ^ 6 - ((296 / 73) : ℂ) * ζ ^ 8 + ((186 / 73) : ℂ) * ζ ^ 9 - ((3289 / 1168) : ℂ) * ζ ^ 10 - ((1801 / 1168) : ℂ) * ζ ^ 11 - ((1283 / 1168) : ℂ) * ζ ^ 13 + ((1745 / 1168) : ℂ) * ζ ^ 14 - ((2743 / 1168) : ℂ) * ζ ^ 15 + ((47 / 1168) : ℂ) * ζ ^ 16 + ((215 / 584) : ℂ) * ζ ^ 17 - ((97 / 146) : ℂ) * ζ ^ 18 + ((471 / 584) : ℂ) * ζ ^ 19 + ((187 / 584) : ℂ) * ζ ^ 20 - ((53 / 292) : ℂ) * ζ ^ 21 + ((193 / 146) : ℂ) * ζ ^ 22 + ((717 / 584) : ℂ) * ζ ^ 23 - ((327 / 1168) : ℂ) * ζ ^ 24 - ((547 / 1168) : ℂ) * ζ ^ 25 + ((2457 / 1168) : ℂ) * ζ ^ 26 + ((1801 / 1168) : ℂ) * ζ ^ 27 + ((903 / 584) : ℂ) * ζ ^ 28 - ((2245 / 1168) : ℂ) * ζ ^ 29 + ((81 / 73) : ℂ) * ζ ^ 30 + ((2217 / 1168) : ℂ) * ζ ^ 31 - ((47 / 1168) : ℂ) * ζ ^ 32 - ((1437 / 1168) : ℂ) * ζ ^ 33 - ((1927 / 1168) : ℂ) * ζ ^ 34 + ((75 / 1168) : ℂ) * ζ ^ 35 + ((187 / 584) : ℂ) * ζ ^ 36 + ((67 / 73) : ℂ) * ζ ^ 37 - ((52 / 73) : ℂ) * ζ ^ 38 - ((5 / 4) : ℂ) * ζ ^ 39 + ((1621 / 1168) : ℂ) * ζ ^ 40 + ((67 / 73) : ℂ) * ζ ^ 41 - ((913 / 1168) : ℂ) * ζ ^ 42 - ((297 / 292) : ℂ) * ζ ^ 43 - ((1153 / 1168) : ℂ) * ζ ^ 44 + ((447 / 1168) : ℂ) * ζ ^ 45 - ((913 / 1168) : ℂ) * ζ ^ 46 - ((26 / 73) : ℂ) * ζ ^ 47 - ((475 / 584) : ℂ) * ζ ^ 48 + ((201 / 1168) : ℂ) * ζ ^ 49 + ((61 / 292) : ℂ) * ζ ^ 50 - ((26 / 73) : ℂ) * ζ ^ 51 - ((421 / 1168) : ℂ) * ζ ^ 52 - ((879 / 1168) : ℂ) * ζ ^ 53 + ((669 / 1168) : ℂ) * ζ ^ 54 - ((27 / 146) : ℂ) * ζ ^ 55 - ((421 / 1168) : ℂ) * ζ ^ 56 - ((215 / 584) : ℂ) * ζ ^ 57 - ((11 / 292) : ℂ) * ζ ^ 58 + ((79 / 146) : ℂ) * ζ ^ 59 + ((421 / 1168) : ℂ) * ζ ^ 60 + ((215 / 584) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_4_0 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        4 0 =
      alternatingSixAmbientRow12TransformedGeneratorA
        4 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((1277 / 1168) : ℂ) + ((179 / 1168) : ℂ) * ζ ^ 3 + ((1277 / 1168) : ℂ) * ζ ^ 4 - ((315 / 1168) : ℂ) * ζ ^ 5 + ((311 / 292) : ℂ) * ζ ^ 6 + ((12 / 73) : ℂ) * ζ ^ 8 + ((261 / 292) : ℂ) * ζ ^ 9 + ((1331 / 1168) : ℂ) * ζ ^ 10 + ((179 / 584) : ℂ) * ζ ^ 11 + ((99 / 584) : ℂ) * ζ ^ 13 - ((87 / 1168) : ℂ) * ζ ^ 14 + ((921 / 584) : ℂ) * ζ ^ 15 - ((213 / 1168) : ℂ) * ζ ^ 16 + ((729 / 1168) : ℂ) * ζ ^ 17 - ((153 / 1168) : ℂ) * ζ ^ 18 - ((371 / 292) : ℂ) * ζ ^ 19 - ((399 / 1168) : ℂ) * ζ ^ 20 + ((329 / 584) : ℂ) * ζ ^ 21 - ((311 / 292) : ℂ) * ζ ^ 22 - ((2311 / 1168) : ℂ) * ζ ^ 23 + ((93 / 584) : ℂ) * ζ ^ 24 - ((1077 / 1168) : ℂ) * ζ ^ 25 - ((2269 / 1168) : ℂ) * ζ ^ 26 - ((179 / 584) : ℂ) * ζ ^ 27 + ((229 / 1168) : ℂ) * ζ ^ 28 - ((2639 / 1168) : ℂ) * ζ ^ 29 - ((37 / 146) : ℂ) * ζ ^ 30 - ((53 / 292) : ℂ) * ζ ^ 31 + ((213 / 1168) : ℂ) * ζ ^ 32 - ((811 / 1168) : ℂ) * ζ ^ 33 + ((515 / 1168) : ℂ) * ζ ^ 34 - ((1313 / 1168) : ℂ) * ζ ^ 35 - ((373 / 1168) : ℂ) * ζ ^ 36 + ((50 / 73) : ℂ) * ζ ^ 37 + ((51 / 146) : ℂ) * ζ ^ 38 + ((1817 / 1168) : ℂ) * ζ ^ 39 + ((163 / 1168) : ℂ) * ζ ^ 40 + ((50 / 73) : ℂ) * ζ ^ 41 + ((1025 / 1168) : ℂ) * ζ ^ 42 + ((1299 / 1168) : ℂ) * ζ ^ 43 - ((481 / 584) : ℂ) * ζ ^ 44 + ((109 / 73) : ℂ) * ζ ^ 45 + ((1025 / 1168) : ℂ) * ζ ^ 46 - ((1 / 8) : ℂ) * ζ ^ 47 + ((571 / 1168) : ℂ) * ζ ^ 48 + ((93 / 292) : ℂ) * ζ ^ 49 - ((6 / 73) : ℂ) * ζ ^ 50 - ((1 / 8) : ℂ) * ζ ^ 51 + ((293 / 584) : ℂ) * ζ ^ 52 - ((709 / 1168) : ℂ) * ζ ^ 53 - ((929 / 1168) : ℂ) * ζ ^ 54 + ((631 / 584) : ℂ) * ζ ^ 55 + ((293 / 584) : ℂ) * ζ ^ 56 - ((729 / 1168) : ℂ) * ζ ^ 57 + ((367 / 584) : ℂ) * ζ ^ 58 - ((279 / 292) : ℂ) * ζ ^ 59 - ((293 / 584) : ℂ) * ζ ^ 60 + ((729 / 1168) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_4_1 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        4 1 =
      alternatingSixAmbientRow12TransformedGeneratorA
        4 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((107 / 584) : ℂ) - ((783 / 584) : ℂ) * ζ ^ 3 - ((107 / 584) : ℂ) * ζ ^ 4 + ((29 / 292) : ℂ) * ζ ^ 5 - ((1059 / 1168) : ℂ) * ζ ^ 6 - ((989 / 1168) : ℂ) * ζ ^ 8 - ((473 / 1168) : ℂ) * ζ ^ 9 - ((669 / 1168) : ℂ) * ζ ^ 10 + ((701 / 1168) : ℂ) * ζ ^ 11 - ((2153 / 1168) : ℂ) * ζ ^ 13 - ((195 / 584) : ℂ) * ζ ^ 14 - ((421 / 584) : ℂ) * ζ ^ 15 - ((405 / 292) : ℂ) * ζ ^ 16 - ((357 / 1168) : ℂ) * ζ ^ 17 - ((2147 / 1168) : ℂ) * ζ ^ 18 + ((1543 / 1168) : ℂ) * ζ ^ 19 - ((549 / 146) : ℂ) * ζ ^ 20 + ((669 / 1168) : ℂ) * ζ ^ 21 + ((1059 / 1168) : ℂ) * ζ ^ 22 - ((1889 / 1168) : ℂ) * ζ ^ 23 + ((693 / 292) : ℂ) * ζ ^ 24 - ((1353 / 1168) : ℂ) * ζ ^ 25 + ((789 / 1168) : ℂ) * ζ ^ 26 - ((701 / 1168) : ℂ) * ζ ^ 27 - ((1179 / 584) : ℂ) * ζ ^ 28 + ((1041 / 292) : ℂ) * ζ ^ 29 - ((447 / 146) : ℂ) * ζ ^ 30 + ((205 / 1168) : ℂ) * ζ ^ 31 + ((405 / 292) : ℂ) * ζ ^ 32 + ((469 / 1168) : ℂ) * ζ ^ 33 + ((2247 / 1168) : ℂ) * ζ ^ 34 - ((163 / 584) : ℂ) * ζ ^ 35 + ((3357 / 1168) : ℂ) * ζ ^ 36 - ((1383 / 1168) : ℂ) * ζ ^ 37 + ((1071 / 1168) : ℂ) * ζ ^ 38 + ((1933 / 1168) : ℂ) * ζ ^ 39 + ((647 / 584) : ℂ) * ζ ^ 40 - ((1383 / 1168) : ℂ) * ζ ^ 41 + ((135 / 584) : ℂ) * ζ ^ 42 + ((1897 / 1168) : ℂ) * ζ ^ 43 - ((1177 / 1168) : ℂ) * ζ ^ 44 + ((965 / 1168) : ℂ) * ζ ^ 45 + ((135 / 584) : ℂ) * ζ ^ 46 - ((453 / 584) : ℂ) * ζ ^ 47 + ((941 / 1168) : ℂ) * ζ ^ 48 - ((505 / 584) : ℂ) * ζ ^ 49 + ((2533 / 1168) : ℂ) * ζ ^ 50 - ((453 / 584) : ℂ) * ζ ^ 51 - ((1737 / 1168) : ℂ) * ζ ^ 52 + ((1581 / 1168) : ℂ) * ζ ^ 53 - ((2803 / 1168) : ℂ) * ζ ^ 54 + ((2699 / 1168) : ℂ) * ζ ^ 55 - ((1737 / 1168) : ℂ) * ζ ^ 56 + ((357 / 1168) : ℂ) * ζ ^ 57 + ((11 / 73) : ℂ) * ζ ^ 58 - ((1793 / 1168) : ℂ) * ζ ^ 59 + ((1737 / 1168) : ℂ) * ζ ^ 60 - ((357 / 1168) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_4_2 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        4 2 =
      alternatingSixAmbientRow12TransformedGeneratorA
        4 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((1359 / 2336) : ℂ) + ((81 / 146) : ℂ) * ζ ^ 3 + ((1359 / 2336) : ℂ) * ζ ^ 4 - ((405 / 2336) : ℂ) * ζ ^ 5 + ((1625 / 1168) : ℂ) * ζ ^ 6 + ((2333 / 2336) : ℂ) * ζ ^ 8 + ((127 / 146) : ℂ) * ζ ^ 9 + ((2329 / 2336) : ℂ) * ζ ^ 10 + ((975 / 2336) : ℂ) * ζ ^ 11 + ((165 / 146) : ℂ) * ζ ^ 13 + ((921 / 2336) : ℂ) * ζ ^ 14 + ((29 / 584) : ℂ) * ζ ^ 15 - ((901 / 2336) : ℂ) * ζ ^ 16 + ((1627 / 2336) : ℂ) * ζ ^ 17 - ((2179 / 2336) : ℂ) * ζ ^ 18 + ((859 / 2336) : ℂ) * ζ ^ 19 - ((1289 / 2336) : ℂ) * ζ ^ 20 - ((47 / 73) : ℂ) * ζ ^ 21 - ((1625 / 1168) : ℂ) * ζ ^ 22 - ((3 / 2336) : ℂ) * ζ ^ 23 + ((97 / 584) : ℂ) * ζ ^ 24 - ((1861 / 1168) : ℂ) * ζ ^ 25 - ((2855 / 2336) : ℂ) * ζ ^ 26 - ((975 / 2336) : ℂ) * ζ ^ 27 + ((1349 / 2336) : ℂ) * ζ ^ 28 - ((943 / 292) : ℂ) * ζ ^ 29 + ((139 / 146) : ℂ) * ζ ^ 30 - ((2257 / 2336) : ℂ) * ζ ^ 31 + ((901 / 2336) : ℂ) * ζ ^ 32 + ((4319 / 2336) : ℂ) * ζ ^ 33 + ((1421 / 2336) : ℂ) * ζ ^ 34 + ((2361 / 2336) : ℂ) * ζ ^ 35 + ((305 / 1168) : ℂ) * ζ ^ 36 + ((2379 / 1168) : ℂ) * ζ ^ 37 + ((1539 / 1168) : ℂ) * ζ ^ 38 - ((667 / 584) : ℂ) * ζ ^ 39 + ((153 / 2336) : ℂ) * ζ ^ 40 + ((2379 / 1168) : ℂ) * ζ ^ 41 - ((395 / 2336) : ℂ) * ζ ^ 42 + ((1539 / 2336) : ℂ) * ζ ^ 43 - ((1345 / 2336) : ℂ) * ζ ^ 44 + ((2869 / 2336) : ℂ) * ζ ^ 45 - ((395 / 2336) : ℂ) * ζ ^ 46 + ((641 / 1168) : ℂ) * ζ ^ 47 + ((9 / 1168) : ℂ) * ζ ^ 48 - ((1119 / 2336) : ℂ) * ζ ^ 49 - ((529 / 2336) : ℂ) * ζ ^ 50 + ((641 / 1168) : ℂ) * ζ ^ 51 + ((291 / 2336) : ℂ) * ζ ^ 52 - ((4435 / 2336) : ℂ) * ζ ^ 53 + ((231 / 584) : ℂ) * ζ ^ 54 - ((1741 / 2336) : ℂ) * ζ ^ 55 + ((291 / 2336) : ℂ) * ζ ^ 56 - ((1627 / 2336) : ℂ) * ζ ^ 57 - ((159 / 1168) : ℂ) * ζ ^ 58 + ((459 / 2336) : ℂ) * ζ ^ 59 - ((291 / 2336) : ℂ) * ζ ^ 60 + ((1627 / 2336) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_4_3 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        4 3 =
      alternatingSixAmbientRow12TransformedGeneratorA
        4 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((23577 / 42632) : ℂ) - ((100127 / 85264) : ℂ) * ζ ^ 3 - ((23577 / 42632) : ℂ) * ζ ^ 4 - ((4105 / 5329) : ℂ) * ζ ^ 5 - ((31 / 85264) : ℂ) * ζ ^ 6 - ((73203 / 85264) : ℂ) * ζ ^ 8 + ((3741 / 42632) : ℂ) * ζ ^ 9 + ((27269 / 42632) : ℂ) * ζ ^ 10 + ((41437 / 85264) : ℂ) * ζ ^ 11 - ((51311 / 42632) : ℂ) * ζ ^ 13 - ((54569 / 85264) : ℂ) * ζ ^ 14 + ((3464 / 5329) : ℂ) * ζ ^ 15 + ((4501 / 42632) : ℂ) * ζ ^ 16 - ((29099 / 42632) : ℂ) * ζ ^ 17 + ((154123 / 85264) : ℂ) * ζ ^ 18 - ((13987 / 85264) : ℂ) * ζ ^ 19 + ((63417 / 42632) : ℂ) * ζ ^ 20 + ((7714 / 5329) : ℂ) * ζ ^ 21 + ((31 / 85264) : ℂ) * ζ ^ 22 + ((40509 / 85264) : ℂ) * ζ ^ 23 - ((14729 / 10658) : ℂ) * ζ ^ 24 + ((238023 / 85264) : ℂ) * ζ ^ 25 - ((166567 / 85264) : ℂ) * ζ ^ 26 - ((41437 / 85264) : ℂ) * ζ ^ 27 + ((35817 / 21316) : ℂ) * ζ ^ 28 + ((234589 / 85264) : ℂ) * ζ ^ 29 - ((44695 / 85264) : ℂ) * ζ ^ 30 + ((50 / 5329) : ℂ) * ζ ^ 31 - ((4501 / 42632) : ℂ) * ζ ^ 32 - ((30055 / 42632) : ℂ) * ζ ^ 33 - ((60967 / 42632) : ℂ) * ζ ^ 34 - ((46523 / 85264) : ℂ) * ζ ^ 35 - ((27513 / 85264) : ℂ) * ζ ^ 36 - ((59955 / 21316) : ℂ) * ζ ^ 37 + ((39899 / 85264) : ℂ) * ζ ^ 38 + ((130197 / 85264) : ℂ) * ζ ^ 39 - ((646 / 5329) : ℂ) * ζ ^ 40 - ((59955 / 21316) : ℂ) * ζ ^ 41 + ((83299 / 42632) : ℂ) * ζ ^ 42 - ((7031 / 21316) : ℂ) * ζ ^ 43 + ((827 / 85264) : ℂ) * ζ ^ 44 - ((167313 / 85264) : ℂ) * ζ ^ 45 + ((83299 / 42632) : ℂ) * ζ ^ 46 - ((42237 / 85264) : ℂ) * ζ ^ 47 - ((27765 / 85264) : ℂ) * ζ ^ 48 + ((174341 / 85264) : ℂ) * ζ ^ 49 - ((73699 / 42632) : ℂ) * ζ ^ 50 - ((42237 / 85264) : ℂ) * ζ ^ 51 + ((18511 / 85264) : ℂ) * ζ ^ 52 + ((69617 / 42632) : ℂ) * ζ ^ 53 - ((1200 / 5329) : ℂ) * ζ ^ 54 + ((51637 / 85264) : ℂ) * ζ ^ 55 + ((18511 / 85264) : ℂ) * ζ ^ 56 + ((29099 / 42632) : ℂ) * ζ ^ 57 - ((7357 / 42632) : ℂ) * ζ ^ 58 - ((1175 / 10658) : ℂ) * ζ ^ 59 - ((18511 / 85264) : ℂ) * ζ ^ 60 - ((29099 / 42632) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_4_4 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        4 4 =
      alternatingSixAmbientRow12TransformedGeneratorA
        4 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((52351 / 170528) : ℂ) - ((32941 / 85264) : ℂ) * ζ ^ 3 - ((52351 / 170528) : ℂ) * ζ ^ 4 - ((169775 / 170528) : ℂ) * ζ ^ 5 + ((16709 / 42632) : ℂ) * ζ ^ 6 - ((250649 / 170528) : ℂ) * ζ ^ 8 - ((2329 / 21316) : ℂ) * ζ ^ 9 - ((145689 / 170528) : ℂ) * ζ ^ 10 + ((6893 / 170528) : ℂ) * ζ ^ 11 - ((71039 / 42632) : ℂ) * ζ ^ 13 + ((212525 / 170528) : ℂ) * ζ ^ 14 - ((79719 / 85264) : ℂ) * ζ ^ 15 + ((153133 / 170528) : ℂ) * ζ ^ 16 - ((188407 / 170528) : ℂ) * ζ ^ 17 - ((168169 / 170528) : ℂ) * ζ ^ 18 + ((166331 / 170528) : ℂ) * ζ ^ 19 - ((98085 / 170528) : ℂ) * ζ ^ 20 + ((3491 / 10658) : ℂ) * ζ ^ 21 - ((16709 / 42632) : ℂ) * ζ ^ 22 - ((120727 / 170528) : ℂ) * ζ ^ 23 + ((125609 / 85264) : ℂ) * ζ ^ 24 + ((61083 / 21316) : ℂ) * ζ ^ 25 - ((231713 / 170528) : ℂ) * ζ ^ 26 - ((6893 / 170528) : ℂ) * ζ ^ 27 - ((150047 / 170528) : ℂ) * ζ ^ 28 + ((348817 / 85264) : ℂ) * ζ ^ 29 - ((36677 / 85264) : ℂ) * ζ ^ 30 + ((46545 / 170528) : ℂ) * ζ ^ 31 - ((153133 / 170528) : ℂ) * ζ ^ 32 + ((119177 / 170528) : ℂ) * ζ ^ 33 - ((24687 / 170528) : ℂ) * ζ ^ 34 - ((75427 / 170528) : ℂ) * ζ ^ 35 - ((19569 / 42632) : ℂ) * ζ ^ 36 - ((216335 / 85264) : ℂ) * ζ ^ 37 + ((12415 / 10658) : ℂ) * ζ ^ 38 + ((67879 / 85264) : ℂ) * ζ ^ 39 + ((138333 / 170528) : ℂ) * ζ ^ 40 - ((216335 / 85264) : ℂ) * ζ ^ 41 + ((164877 / 170528) : ℂ) * ζ ^ 42 - ((47001 / 170528) : ℂ) * ζ ^ 43 + ((89657 / 170528) : ℂ) * ζ ^ 44 - ((521337 / 170528) : ℂ) * ζ ^ 45 + ((164877 / 170528) : ℂ) * ζ ^ 46 - ((26719 / 85264) : ℂ) * ζ ^ 47 + ((29213 / 85264) : ℂ) * ζ ^ 48 + ((200379 / 170528) : ℂ) * ζ ^ 49 - ((8623 / 170528) : ℂ) * ζ ^ 50 - ((26719 / 85264) : ℂ) * ζ ^ 51 - ((74857 / 170528) : ℂ) * ζ ^ 52 + ((431555 / 170528) : ℂ) * ζ ^ 53 - ((78127 / 85264) : ℂ) * ζ ^ 54 + ((61693 / 170528) : ℂ) * ζ ^ 55 - ((74857 / 170528) : ℂ) * ζ ^ 56 + ((188407 / 170528) : ℂ) * ζ ^ 57 - ((24349 / 85264) : ℂ) * ζ ^ 58 - ((8255 / 170528) : ℂ) * ζ ^ 59 + ((74857 / 170528) : ℂ) * ζ ^ 60 - ((188407 / 170528) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_4_5 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        4 5 =
      alternatingSixAmbientRow12TransformedGeneratorA
        4 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((127 / 1168) : ℂ) + ((63 / 73) : ℂ) * ζ ^ 3 - ((127 / 1168) : ℂ) * ζ ^ 4 + ((5 / 1168) : ℂ) * ζ ^ 5 + ((599 / 292) : ℂ) * ζ ^ 6 - ((925 / 1168) : ℂ) * ζ ^ 8 + ((497 / 1168) : ℂ) * ζ ^ 9 + ((303 / 1168) : ℂ) * ζ ^ 10 + ((215 / 1168) : ℂ) * ζ ^ 11 - ((76 / 73) : ℂ) * ζ ^ 13 + ((2093 / 1168) : ℂ) * ζ ^ 14 - ((1055 / 1168) : ℂ) * ζ ^ 15 - ((409 / 1168) : ℂ) * ζ ^ 16 + ((251 / 584) : ℂ) * ζ ^ 17 - ((2557 / 584) : ℂ) * ζ ^ 18 + ((635 / 584) : ℂ) * ζ ^ 19 - ((2487 / 1168) : ℂ) * ζ ^ 20 - ((97 / 292) : ℂ) * ζ ^ 21 - ((599 / 292) : ℂ) * ζ ^ 22 - ((3561 / 1168) : ℂ) * ζ ^ 23 + ((1039 / 584) : ℂ) * ζ ^ 24 - ((55 / 584) : ℂ) * ζ ^ 25 - ((2033 / 584) : ℂ) * ζ ^ 26 - ((215 / 1168) : ℂ) * ζ ^ 27 + ((867 / 1168) : ℂ) * ζ ^ 28 - ((1645 / 584) : ℂ) * ζ ^ 29 - ((661 / 584) : ℂ) * ζ ^ 30 - ((191 / 1168) : ℂ) * ζ ^ 31 + ((409 / 1168) : ℂ) * ζ ^ 32 + ((485 / 292) : ℂ) * ζ ^ 33 + ((128 / 73) : ℂ) * ζ ^ 34 + ((83 / 146) : ℂ) * ζ ^ 35 + ((107 / 584) : ℂ) * ζ ^ 36 + ((87 / 73) : ℂ) * ζ ^ 37 + ((1667 / 584) : ℂ) * ζ ^ 38 - ((425 / 1168) : ℂ) * ζ ^ 39 + ((15 / 584) : ℂ) * ζ ^ 40 + ((87 / 73) : ℂ) * ζ ^ 41 + ((835 / 584) : ℂ) * ζ ^ 42 + ((1017 / 1168) : ℂ) * ζ ^ 43 - ((317 / 584) : ℂ) * ζ ^ 44 + ((533 / 1168) : ℂ) * ζ ^ 45 + ((835 / 584) : ℂ) * ζ ^ 46 - ((3 / 146) : ℂ) * ζ ^ 47 - ((615 / 584) : ℂ) * ζ ^ 48 + ((83 / 1168) : ℂ) * ζ ^ 49 - ((369 / 584) : ℂ) * ζ ^ 50 - ((3 / 146) : ℂ) * ζ ^ 51 + ((195 / 1168) : ℂ) * ζ ^ 52 - ((1067 / 584) : ℂ) * ζ ^ 53 - ((233 / 292) : ℂ) * ζ ^ 54 - ((47 / 1168) : ℂ) * ζ ^ 55 + ((195 / 1168) : ℂ) * ζ ^ 56 - ((251 / 584) : ℂ) * ζ ^ 57 - ((607 / 584) : ℂ) * ζ ^ 58 + ((71 / 1168) : ℂ) * ζ ^ 59 - ((195 / 1168) : ℂ) * ζ ^ 60 + ((251 / 584) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_5_0 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        5 0 =
      alternatingSixAmbientRow12TransformedGeneratorA
        5 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((25 / 1168) : ℂ) + ((231 / 1168) : ℂ) * ζ ^ 3 - ((25 / 1168) : ℂ) * ζ ^ 4 - ((205 / 1168) : ℂ) * ζ ^ 5 - ((19 / 292) : ℂ) * ζ ^ 6 - ((347 / 292) : ℂ) * ζ ^ 8 + ((399 / 584) : ℂ) * ζ ^ 9 - ((859 / 1168) : ℂ) * ζ ^ 10 - ((361 / 584) : ℂ) * ζ ^ 11 + ((501 / 584) : ℂ) * ζ ^ 13 + ((783 / 1168) : ℂ) * ζ ^ 14 - ((343 / 292) : ℂ) * ζ ^ 15 + ((223 / 1168) : ℂ) * ζ ^ 16 + ((593 / 1168) : ℂ) * ζ ^ 17 - ((1511 / 1168) : ℂ) * ζ ^ 18 + ((325 / 584) : ℂ) * ζ ^ 19 + ((453 / 1168) : ℂ) * ζ ^ 20 - ((103 / 73) : ℂ) * ζ ^ 21 + ((19 / 292) : ℂ) * ζ ^ 22 + ((1651 / 1168) : ℂ) * ζ ^ 23 - ((115 / 584) : ℂ) * ζ ^ 24 - ((2923 / 1168) : ℂ) * ζ ^ 25 + ((455 / 1168) : ℂ) * ζ ^ 26 + ((361 / 584) : ℂ) * ζ ^ 27 + ((1995 / 1168) : ℂ) * ζ ^ 28 - ((2283 / 1168) : ℂ) * ζ ^ 29 + ((69 / 73) : ℂ) * ζ ^ 30 - ((3 / 73) : ℂ) * ζ ^ 31 - ((223 / 1168) : ℂ) * ζ ^ 32 + ((373 / 1168) : ℂ) * ζ ^ 33 - ((801 / 1168) : ℂ) * ζ ^ 34 + ((1083 / 1168) : ℂ) * ζ ^ 35 - ((939 / 1168) : ℂ) * ζ ^ 36 + ((1417 / 584) : ℂ) * ζ ^ 37 + ((129 / 584) : ℂ) * ζ ^ 38 - ((2575 / 1168) : ℂ) * ζ ^ 39 + ((557 / 1168) : ℂ) * ζ ^ 40 + ((1417 / 584) : ℂ) * ζ ^ 41 - ((379 / 1168) : ℂ) * ζ ^ 42 + ((303 / 1168) : ℂ) * ζ ^ 43 - ((525 / 584) : ℂ) * ζ ^ 44 + ((221 / 146) : ℂ) * ζ ^ 45 - ((379 / 1168) : ℂ) * ζ ^ 46 + ((385 / 584) : ℂ) * ζ ^ 47 - ((173 / 1168) : ℂ) * ζ ^ 48 - ((1115 / 584) : ℂ) * ζ ^ 49 + ((25 / 292) : ℂ) * ζ ^ 50 + ((385 / 584) : ℂ) * ζ ^ 51 + ((179 / 292) : ℂ) * ζ ^ 52 - ((1457 / 1168) : ℂ) * ζ ^ 53 + ((279 / 1168) : ℂ) * ζ ^ 54 - ((105 / 146) : ℂ) * ζ ^ 55 + ((179 / 292) : ℂ) * ζ ^ 56 - ((593 / 1168) : ℂ) * ζ ^ 57 - ((197 / 584) : ℂ) * ζ ^ 58 + ((35 / 584) : ℂ) * ζ ^ 59 - ((179 / 292) : ℂ) * ζ ^ 60 + ((593 / 1168) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_5_1 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        5 1 =
      alternatingSixAmbientRow12TransformedGeneratorA
        5 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((171 / 584) : ℂ) + ((413 / 584) : ℂ) * ζ ^ 3 - ((171 / 584) : ℂ) * ζ ^ 4 + ((417 / 292) : ℂ) * ζ ^ 5 - ((443 / 1168) : ℂ) * ζ ^ 6 + ((49 / 1168) : ℂ) * ζ ^ 8 - ((1667 / 1168) : ℂ) * ζ ^ 9 - ((533 / 1168) : ℂ) * ζ ^ 10 - ((1927 / 1168) : ℂ) * ζ ^ 11 + ((459 / 1168) : ℂ) * ζ ^ 13 + ((45 / 584) : ℂ) * ζ ^ 14 + ((491 / 584) : ℂ) * ζ ^ 15 - ((461 / 584) : ℂ) * ζ ^ 16 + ((1 / 1168) : ℂ) * ζ ^ 17 + ((407 / 1168) : ℂ) * ζ ^ 18 - ((2909 / 1168) : ℂ) * ζ ^ 19 + ((255 / 584) : ℂ) * ζ ^ 20 - ((1231 / 1168) : ℂ) * ζ ^ 21 + ((443 / 1168) : ℂ) * ζ ^ 22 + ((775 / 1168) : ℂ) * ζ ^ 23 - ((179 / 146) : ℂ) * ζ ^ 24 - ((407 / 1168) : ℂ) * ζ ^ 25 - ((235 / 1168) : ℂ) * ζ ^ 26 + ((1927 / 1168) : ℂ) * ζ ^ 27 + ((251 / 146) : ℂ) * ζ ^ 28 - ((415 / 584) : ℂ) * ζ ^ 29 - ((19 / 292) : ℂ) * ζ ^ 30 + ((2269 / 1168) : ℂ) * ζ ^ 31 + ((461 / 584) : ℂ) * ζ ^ 32 + ((77 / 1168) : ℂ) * ζ ^ 33 - ((1045 / 1168) : ℂ) * ζ ^ 34 - ((1075 / 584) : ℂ) * ζ ^ 35 + ((359 / 1168) : ℂ) * ζ ^ 36 + ((1233 / 1168) : ℂ) * ζ ^ 37 + ((253 / 1168) : ℂ) * ζ ^ 38 + ((565 / 1168) : ℂ) * ζ ^ 39 - ((863 / 584) : ℂ) * ζ ^ 40 + ((1233 / 1168) : ℂ) * ζ ^ 41 + ((339 / 584) : ℂ) * ζ ^ 42 - ((1781 / 1168) : ℂ) * ζ ^ 43 + ((241 / 1168) : ℂ) * ζ ^ 44 - ((1251 / 1168) : ℂ) * ζ ^ 45 + ((339 / 584) : ℂ) * ζ ^ 46 - ((171 / 584) : ℂ) * ζ ^ 47 - ((1047 / 1168) : ℂ) * ζ ^ 48 + ((11 / 584) : ℂ) * ζ ^ 49 - ((1117 / 1168) : ℂ) * ζ ^ 50 - ((171 / 584) : ℂ) * ζ ^ 51 + ((563 / 1168) : ℂ) * ζ ^ 52 - ((959 / 1168) : ℂ) * ζ ^ 53 + ((439 / 1168) : ℂ) * ζ ^ 54 - ((251 / 1168) : ℂ) * ζ ^ 55 + ((563 / 1168) : ℂ) * ζ ^ 56 - ((1 / 1168) : ℂ) * ζ ^ 57 - ((85 / 292) : ℂ) * ζ ^ 58 + ((593 / 1168) : ℂ) * ζ ^ 59 - ((563 / 1168) : ℂ) * ζ ^ 60 + ((1 / 1168) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_5_2 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        5 2 =
      alternatingSixAmbientRow12TransformedGeneratorA
        5 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((823 / 2336) : ℂ) + ((299 / 1168) : ℂ) * ζ ^ 3 - ((823 / 2336) : ℂ) * ζ ^ 4 - ((1151 / 2336) : ℂ) * ζ ^ 5 - ((491 / 1168) : ℂ) * ζ ^ 6 - ((3935 / 2336) : ℂ) * ζ ^ 8 + ((627 / 1168) : ℂ) * ζ ^ 9 - ((3385 / 2336) : ℂ) * ζ ^ 10 + ((235 / 2336) : ℂ) * ζ ^ 11 - ((793 / 1168) : ℂ) * ζ ^ 13 + ((2403 / 2336) : ℂ) * ζ ^ 14 + ((25 / 1168) : ℂ) * ζ ^ 15 + ((2231 / 2336) : ℂ) * ζ ^ 16 + ((103 / 2336) : ℂ) * ζ ^ 17 - ((2863 / 2336) : ℂ) * ζ ^ 18 + ((185 / 2336) : ℂ) * ζ ^ 19 - ((289 / 2336) : ℂ) * ζ ^ 20 + ((711 / 1168) : ℂ) * ζ ^ 21 + ((491 / 1168) : ℂ) * ζ ^ 22 + ((3613 / 2336) : ℂ) * ζ ^ 23 + ((315 / 292) : ℂ) * ζ ^ 24 + ((175 / 584) : ℂ) * ζ ^ 25 + ((2105 / 2336) : ℂ) * ζ ^ 26 - ((235 / 2336) : ℂ) * ζ ^ 27 + ((2745 / 2336) : ℂ) * ζ ^ 28 + ((13 / 292) : ℂ) * ζ ^ 29 - ((783 / 1168) : ℂ) * ζ ^ 30 - ((1111 / 2336) : ℂ) * ζ ^ 31 - ((2231 / 2336) : ℂ) * ζ ^ 32 - ((557 / 2336) : ℂ) * ζ ^ 33 + ((1707 / 2336) : ℂ) * ζ ^ 34 - ((2449 / 2336) : ℂ) * ζ ^ 35 - ((1383 / 1168) : ℂ) * ζ ^ 36 - ((38 / 73) : ℂ) * ζ ^ 37 - ((293 / 1168) : ℂ) * ζ ^ 38 + ((113 / 146) : ℂ) * ζ ^ 39 + ((1947 / 2336) : ℂ) * ζ ^ 40 - ((38 / 73) : ℂ) * ζ ^ 41 - ((1123 / 2336) : ℂ) * ζ ^ 42 - ((1327 / 2336) : ℂ) * ζ ^ 43 - ((251 / 2336) : ℂ) * ζ ^ 44 + ((1325 / 2336) : ℂ) * ζ ^ 45 - ((1123 / 2336) : ℂ) * ζ ^ 46 + ((3 / 8) : ℂ) * ζ ^ 47 + ((203 / 1168) : ℂ) * ζ ^ 48 + ((303 / 2336) : ℂ) * ζ ^ 49 + ((1991 / 2336) : ℂ) * ζ ^ 50 + ((3 / 8) : ℂ) * ζ ^ 51 + ((535 / 2336) : ℂ) * ζ ^ 52 + ((201 / 2336) : ℂ) * ζ ^ 53 - ((217 / 584) : ℂ) * ζ ^ 54 - ((271 / 2336) : ℂ) * ζ ^ 55 + ((535 / 2336) : ℂ) * ζ ^ 56 - ((103 / 2336) : ℂ) * ζ ^ 57 + ((79 / 1168) : ℂ) * ζ ^ 58 - ((605 / 2336) : ℂ) * ζ ^ 59 - ((535 / 2336) : ℂ) * ζ ^ 60 + ((103 / 2336) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_5_3 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        5 3 =
      alternatingSixAmbientRow12TransformedGeneratorA
        5 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (((3005 / 42632) : ℂ) + ((8941 / 85264) : ℂ) * ζ ^ 3 - ((3005 / 42632) : ℂ) * ζ ^ 4 + ((19341 / 42632) : ℂ) * ζ ^ 5 - ((27283 / 85264) : ℂ) * ζ ^ 6 + ((144229 / 85264) : ℂ) * ζ ^ 8 + ((2493 / 10658) : ℂ) * ζ ^ 9 + ((1252 / 5329) : ℂ) * ζ ^ 10 + ((13553 / 85264) : ℂ) * ζ ^ 11 + ((72625 / 42632) : ℂ) * ζ ^ 13 - ((47315 / 85264) : ℂ) * ζ ^ 14 + ((27551 / 42632) : ℂ) * ζ ^ 15 - ((24313 / 42632) : ℂ) * ζ ^ 16 + ((29313 / 42632) : ℂ) * ζ ^ 17 - ((1431 / 85264) : ℂ) * ζ ^ 18 - ((41549 / 85264) : ℂ) * ζ ^ 19 - ((1659 / 42632) : ℂ) * ζ ^ 20 - ((38225 / 42632) : ℂ) * ζ ^ 21 + ((27283 / 85264) : ℂ) * ζ ^ 22 - ((64445 / 85264) : ℂ) * ζ ^ 23 - ((11327 / 21316) : ℂ) * ζ ^ 24 - ((157857 / 85264) : ℂ) * ζ ^ 25 + ((117115 / 85264) : ℂ) * ζ ^ 26 - ((13553 / 85264) : ℂ) * ζ ^ 27 + ((7545 / 42632) : ℂ) * ζ ^ 28 - ((270349 / 85264) : ℂ) * ζ ^ 29 - ((35441 / 85264) : ℂ) * ζ ^ 30 - ((2219 / 5329) : ℂ) * ζ ^ 31 + ((24313 / 42632) : ℂ) * ζ ^ 32 - ((3475 / 21316) : ℂ) * ζ ^ 33 + ((48995 / 42632) : ℂ) * ζ ^ 34 + ((49131 / 85264) : ℂ) * ζ ^ 35 + ((76763 / 85264) : ℂ) * ζ ^ 36 + ((96851 / 42632) : ℂ) * ζ ^ 37 + ((48349 / 85264) : ℂ) * ζ ^ 38 - ((57529 / 85264) : ℂ) * ζ ^ 39 - ((17427 / 42632) : ℂ) * ζ ^ 40 + ((96851 / 42632) : ℂ) * ζ ^ 41 - ((11229 / 10658) : ℂ) * ζ ^ 42 + ((2254 / 5329) : ℂ) * ζ ^ 43 + ((14365 / 85264) : ℂ) * ζ ^ 44 + ((128489 / 85264) : ℂ) * ζ ^ 45 - ((11229 / 10658) : ℂ) * ζ ^ 46 + ((21951 / 85264) : ℂ) * ζ ^ 47 + ((15505 / 85264) : ℂ) * ζ ^ 48 - ((87687 / 85264) : ℂ) * ζ ^ 49 + ((22737 / 21316) : ℂ) * ζ ^ 50 + ((21951 / 85264) : ℂ) * ζ ^ 51 - ((28137 / 85264) : ℂ) * ζ ^ 52 - ((65217 / 42632) : ℂ) * ζ ^ 53 - ((279 / 21316) : ℂ) * ζ ^ 54 - ((29299 / 85264) : ℂ) * ζ ^ 55 - ((28137 / 85264) : ℂ) * ζ ^ 56 - ((29313 / 42632) : ℂ) * ζ ^ 57 + ((1753 / 42632) : ℂ) * ζ ^ 58 + ((1837 / 21316) : ℂ) * ζ ^ 59 + ((28137 / 85264) : ℂ) * ζ ^ 60 + ((29313 / 42632) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_5_4 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        5 4 =
      alternatingSixAmbientRow12TransformedGeneratorA
        5 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((31231 / 170528) : ℂ) - ((524 / 5329) : ℂ) * ζ ^ 3 + ((31231 / 170528) : ℂ) * ζ ^ 4 + ((4619 / 170528) : ℂ) * ζ ^ 5 - ((10095 / 42632) : ℂ) * ζ ^ 6 - ((84085 / 170528) : ℂ) * ζ ^ 8 + ((52085 / 85264) : ℂ) * ζ ^ 9 - ((74243 / 170528) : ℂ) * ζ ^ 10 + ((117629 / 170528) : ℂ) * ζ ^ 11 + ((56381 / 85264) : ℂ) * ζ ^ 13 + ((33863 / 170528) : ℂ) * ζ ^ 14 + ((48179 / 42632) : ℂ) * ζ ^ 15 - ((139483 / 170528) : ℂ) * ζ ^ 16 + ((108789 / 170528) : ℂ) * ζ ^ 17 - ((172681 / 170528) : ℂ) * ζ ^ 18 - ((75087 / 170528) : ℂ) * ζ ^ 19 + ((6251 / 170528) : ℂ) * ζ ^ 20 + ((13401 / 85264) : ℂ) * ζ ^ 21 + ((10095 / 42632) : ℂ) * ζ ^ 22 - ((113915 / 170528) : ℂ) * ζ ^ 23 - ((72867 / 85264) : ℂ) * ζ ^ 24 - ((163317 / 85264) : ℂ) * ζ ^ 25 + ((211679 / 170528) : ℂ) * ζ ^ 26 - ((117629 / 170528) : ℂ) * ζ ^ 27 + ((134993 / 170528) : ℂ) * ζ ^ 28 - ((149649 / 85264) : ℂ) * ζ ^ 29 - ((26951 / 42632) : ℂ) * ζ ^ 30 - ((79797 / 170528) : ℂ) * ζ ^ 31 + ((139483 / 170528) : ℂ) * ζ ^ 32 - ((265499 / 170528) : ℂ) * ζ ^ 33 + ((238723 / 170528) : ℂ) * ζ ^ 34 - ((45557 / 170528) : ℂ) * ζ ^ 35 + ((13371 / 10658) : ℂ) * ζ ^ 36 + ((23847 / 21316) : ℂ) * ζ ^ 37 + ((4247 / 42632) : ℂ) * ζ ^ 38 + ((100509 / 85264) : ℂ) * ζ ^ 39 - ((101205 / 170528) : ℂ) * ζ ^ 40 + ((23847 / 21316) : ℂ) * ζ ^ 41 - ((171299 / 170528) : ℂ) * ζ ^ 42 - ((58843 / 170528) : ℂ) * ζ ^ 43 + ((36175 / 170528) : ℂ) * ζ ^ 44 + ((244491 / 170528) : ℂ) * ζ ^ 45 - ((171299 / 170528) : ℂ) * ζ ^ 46 - ((4729 / 21316) : ℂ) * ζ ^ 47 - ((34839 / 85264) : ℂ) * ζ ^ 48 - ((111 / 170528) : ℂ) * ζ ^ 49 + ((124709 / 170528) : ℂ) * ζ ^ 50 - ((4729 / 21316) : ℂ) * ζ ^ 51 - ((74453 / 170528) : ℂ) * ζ ^ 52 - ((253097 / 170528) : ℂ) * ζ ^ 53 + ((23295 / 85264) : ℂ) * ζ ^ 54 - ((5337 / 170528) : ℂ) * ζ ^ 55 - ((74453 / 170528) : ℂ) * ζ ^ 56 - ((108789 / 170528) : ℂ) * ζ ^ 57 + ((10181 / 85264) : ℂ) * ζ ^ 58 + ((43169 / 170528) : ℂ) * ζ ^ 59 + ((74453 / 170528) : ℂ) * ζ ^ 60 + ((108789 / 170528) : ℂ) * ζ ^ 61)
private theorem row12_transformedGeneratorA_5_5 :
    (alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis)
        5 5 =
      alternatingSixAmbientRow12TransformedGeneratorA
        5 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow12Eigenbasis,
      alternatingSixAmbientRow12EigenbasisInverse,
      alternatingSixFiveAmbient_row12_matrixA,
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row12 (-((387 / 1168) : ℂ) - ((91 / 146) : ℂ) * ζ ^ 3 + ((387 / 1168) : ℂ) * ζ ^ 4 - ((1269 / 1168) : ℂ) * ζ ^ 5 - ((415 / 292) : ℂ) * ζ ^ 6 - ((31 / 16) : ℂ) * ζ ^ 8 + ((1277 / 1168) : ℂ) * ζ ^ 9 - ((2497 / 1168) : ℂ) * ζ ^ 10 - ((1315 / 1168) : ℂ) * ζ ^ 11 - ((159 / 584) : ℂ) * ζ ^ 13 + ((837 / 1168) : ℂ) * ζ ^ 14 - ((951 / 1168) : ℂ) * ζ ^ 15 - ((437 / 1168) : ℂ) * ζ ^ 16 + ((1 / 146) : ℂ) * ζ ^ 17 + ((173 / 292) : ℂ) * ζ ^ 18 - ((91 / 292) : ℂ) * ζ ^ 19 + ((1043 / 1168) : ℂ) * ζ ^ 20 - ((331 / 584) : ℂ) * ζ ^ 21 + ((415 / 292) : ℂ) * ζ ^ 22 + ((2185 / 1168) : ℂ) * ζ ^ 23 - ((185 / 146) : ℂ) * ζ ^ 24 - ((71 / 146) : ℂ) * ζ ^ 25 + ((331 / 146) : ℂ) * ζ ^ 26 + ((1315 / 1168) : ℂ) * ζ ^ 27 + ((1923 / 1168) : ℂ) * ζ ^ 28 - ((71 / 584) : ℂ) * ζ ^ 29 + ((161 / 584) : ℂ) * ζ ^ 30 + ((1165 / 1168) : ℂ) * ζ ^ 31 + ((437 / 1168) : ℂ) * ζ ^ 32 - ((795 / 584) : ℂ) * ζ ^ 33 - ((497 / 584) : ℂ) * ζ ^ 34 - ((1197 / 584) : ℂ) * ζ ^ 35 + ((289 / 584) : ℂ) * ζ ^ 36 + ((339 / 584) : ℂ) * ζ ^ 37 - ((377 / 146) : ℂ) * ζ ^ 38 + ((929 / 1168) : ℂ) * ζ ^ 39 + ((131 / 292) : ℂ) * ζ ^ 40 + ((339 / 584) : ℂ) * ζ ^ 41 - ((247 / 292) : ℂ) * ζ ^ 42 - ((2249 / 1168) : ℂ) * ζ ^ 43 - ((205 / 292) : ℂ) * ζ ^ 44 - ((171 / 1168) : ℂ) * ζ ^ 45 - ((247 / 292) : ℂ) * ζ ^ 46 + ((75 / 584) : ℂ) * ζ ^ 47 - ((291 / 584) : ℂ) * ζ ^ 48 - ((475 / 1168) : ℂ) * ζ ^ 49 + ((119 / 146) : ℂ) * ζ ^ 50 + ((75 / 584) : ℂ) * ζ ^ 51 - ((141 / 1168) : ℂ) * ζ ^ 52 + ((24 / 73) : ℂ) * ζ ^ 53 + ((9 / 292) : ℂ) * ζ ^ 54 + ((19 / 1168) : ℂ) * ζ ^ 55 - ((141 / 1168) : ℂ) * ζ ^ 56 - ((1 / 146) : ℂ) * ζ ^ 57 + ((291 / 584) : ℂ) * ζ ^ 58 - ((169 / 1168) : ℂ) * ζ ^ 59 + ((141 / 1168) : ℂ) * ζ ^ 60 + ((1 / 146) : ℂ) * ζ ^ 61)
/-- Exact conjugation formula for the row 12 first
generator. -/
theorem alternatingSixAmbientRow12TransformedGeneratorA_eq :
    alternatingSixAmbientRow12EigenbasisInverse *
        alternatingSixFiveAmbient_row12_matrixA *
        alternatingSixAmbientRow12Eigenbasis =
      alternatingSixAmbientRow12TransformedGeneratorA := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row12_transformedGeneratorA_0_0
  · exact row12_transformedGeneratorA_0_1
  · exact row12_transformedGeneratorA_0_2
  · exact row12_transformedGeneratorA_0_3
  · exact row12_transformedGeneratorA_0_4
  · exact row12_transformedGeneratorA_0_5
  · exact row12_transformedGeneratorA_1_0
  · exact row12_transformedGeneratorA_1_1
  · exact row12_transformedGeneratorA_1_2
  · exact row12_transformedGeneratorA_1_3
  · exact row12_transformedGeneratorA_1_4
  · exact row12_transformedGeneratorA_1_5
  · exact row12_transformedGeneratorA_2_0
  · exact row12_transformedGeneratorA_2_1
  · exact row12_transformedGeneratorA_2_2
  · exact row12_transformedGeneratorA_2_3
  · exact row12_transformedGeneratorA_2_4
  · exact row12_transformedGeneratorA_2_5
  · exact row12_transformedGeneratorA_3_0
  · exact row12_transformedGeneratorA_3_1
  · exact row12_transformedGeneratorA_3_2
  · exact row12_transformedGeneratorA_3_3
  · exact row12_transformedGeneratorA_3_4
  · exact row12_transformedGeneratorA_3_5
  · exact row12_transformedGeneratorA_4_0
  · exact row12_transformedGeneratorA_4_1
  · exact row12_transformedGeneratorA_4_2
  · exact row12_transformedGeneratorA_4_3
  · exact row12_transformedGeneratorA_4_4
  · exact row12_transformedGeneratorA_4_5
  · exact row12_transformedGeneratorA_5_0
  · exact row12_transformedGeneratorA_5_1
  · exact row12_transformedGeneratorA_5_2
  · exact row12_transformedGeneratorA_5_3
  · exact row12_transformedGeneratorA_5_4
  · exact row12_transformedGeneratorA_5_5


end InductiveMcKay
end McKayConjecture
