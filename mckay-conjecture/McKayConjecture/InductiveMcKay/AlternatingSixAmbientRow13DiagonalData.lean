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
# Checked diagonal data for ambient row 13

This generated module records an exact eigenbasis for the second generator
and the first generator in that basis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Eigenvalue block labels for row 13. -/
def alternatingSixAmbientRow13EigenvalueLabel :
    Fin 6 → Fin 4 :=
  ![0, 0, 1, 2, 3, 3]

/-- Second-generator eigenvalues, including their multiplicities. -/
def alternatingSixAmbientRow13GeneratorBEigenvalue :
    Fin 6 → ℂ :=
  fun i ↦
    alternatingSixOrderEightOddEigenvalue
      (alternatingSixAmbientRow13EigenvalueLabel i)

/-- Diagonal form of the row 13 second generator. -/
def alternatingSixAmbientRow13GeneratorBDiagonal :
    Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.diagonal
    alternatingSixAmbientRow13GeneratorBEigenvalue

/-- Checked eigenbasis for the row 13 second generator. -/
def alternatingSixAmbientRow13Eigenbasis :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 5), ((-1 / 2), 15), ((-1 / 2), 25), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((2 / 3), 0), ((2 / 3), 3), ((2 / 3), 7), ((2 / 3), 10), ((-1 / 3), 15), ((-2 / 3), 19), ((-1 / 3), 20), ((-2 / 3), 23), ((-1 / 3), 30), ((2 / 3), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), (1, 3), ((1 / 2), 5), (1, 7), ((-1 / 2), 15), (-1, 19), (1, 20), (-1, 23), ((-1 / 2), 25), ((-1 / 2), 30), (1, 31)],
      alternatingSixCyclotomicValue [(1, 0), ((-1 / 2), 3), ((1 / 2), 5), ((-1 / 2), 7), ((3 / 2), 10), ((1 / 2), 15), ((1 / 2), 19), ((1 / 2), 20), ((1 / 2), 23), ((-1 / 2), 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((-9 / 22), 0), ((2 / 11), 3), ((-1 / 2), 5), ((2 / 11), 7), ((1 / 11), 10), ((3 / 22), 15), ((-2 / 11), 19), ((4 / 11), 20), ((-2 / 11), 23), ((9 / 22), 25), ((1 / 22), 30), ((2 / 11), 31)],
      alternatingSixCyclotomicValue [((-7 / 11), 0), ((-1 / 11), 3), ((2 / 11), 5), ((-1 / 11), 7), ((3 / 11), 15), ((1 / 11), 19), ((3 / 11), 20), ((1 / 11), 23), ((-3 / 11), 25), ((-2 / 11), 30), ((-1 / 11), 31)]],
    ![alternatingSixCyclotomicValue [((3 / 2), 3), ((3 / 2), 5), ((3 / 2), 7), ((1 / 2), 10), ((-1 / 2), 15), ((-3 / 2), 19), ((-1 / 2), 20), ((-3 / 2), 23), (-1, 25), ((-1 / 2), 30), ((3 / 2), 31)],
      alternatingSixCyclotomicValue [((-1 / 3), 0), ((1 / 3), 5), ((1 / 3), 10), ((5 / 3), 20), ((1 / 3), 25), ((4 / 3), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 3), ((-1 / 2), 5), ((-1 / 2), 7), ((1 / 2), 10), ((1 / 2), 15), ((1 / 2), 19), ((-1 / 2), 20), ((1 / 2), 23), ((-1 / 2), 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 2), 3), ((1 / 2), 7), ((1 / 2), 10), ((-1 / 2), 19), ((-1 / 2), 20), ((-1 / 2), 23), ((-1 / 2), 25), (-1, 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((-3 / 22), 3), ((-3 / 22), 5), ((-3 / 22), 7), ((17 / 22), 10), ((-1 / 22), 15), ((3 / 22), 19), ((3 / 22), 20), ((3 / 22), 23), ((2 / 11), 25), ((-5 / 22), 30), ((-3 / 22), 31)],
      alternatingSixCyclotomicValue [((-3 / 11), 0), ((5 / 11), 3), ((5 / 11), 7), ((-3 / 11), 10), ((1 / 11), 15), ((-5 / 11), 19), ((-1 / 11), 20), ((-5 / 11), 23), ((3 / 11), 25), ((4 / 11), 30), ((5 / 11), 31)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 2), 3), (-1, 5), ((-1 / 2), 7), ((1 / 2), 10), ((1 / 2), 19), ((-1 / 2), 20), ((1 / 2), 23), ((1 / 2), 25), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [(1, 0), ((-1 / 3), 3), ((2 / 3), 5), ((-1 / 3), 7), ((-2 / 3), 10), ((2 / 3), 15), ((1 / 3), 19), (-1, 20), ((1 / 3), 23), ((-1 / 3), 25), ((1 / 3), 30), ((-1 / 3), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 3), ((1 / 2), 7), ((-1 / 2), 10), ((-1 / 2), 19), ((1 / 2), 20), ((-1 / 2), 23), ((-1 / 2), 25), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), (1, 3), ((3 / 2), 5), (1, 7), (-1, 10), ((1 / 2), 15), (-1, 19), (-1, 23), ((-1 / 2), 25), ((1 / 2), 30), (1, 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-5 / 22), 3), ((3 / 11), 5), ((-5 / 22), 7), ((-1 / 22), 10), ((1 / 11), 15), ((5 / 22), 19), ((5 / 22), 20), ((5 / 22), 23), ((3 / 22), 25), ((5 / 11), 30), ((-5 / 22), 31)],
      alternatingSixCyclotomicValue [((6 / 11), 0), ((1 / 11), 3), ((1 / 11), 7), ((-5 / 11), 10), ((-2 / 11), 15), ((-1 / 11), 19), ((2 / 11), 20), ((-1 / 11), 23), ((5 / 11), 25), ((3 / 11), 30), ((1 / 11), 31)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 0), (1, 3), ((1 / 2), 5), (1, 7), ((-1 / 2), 15), (-1, 19), (-1, 23), ((-1 / 2), 25), ((1 / 2), 30), (1, 31)],
      alternatingSixCyclotomicValue [((-1 / 3), 3), ((-1 / 3), 5), ((-1 / 3), 7), ((1 / 3), 10), ((-1 / 3), 15), ((1 / 3), 19), (1, 20), ((1 / 3), 23), ((-1 / 3), 25), ((1 / 3), 30), ((-1 / 3), 31)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 2), 5), ((-1 / 2), 15), ((1 / 2), 25), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [(1, 0), ((-1 / 2), 3), ((-1 / 2), 5), ((-1 / 2), 7), ((1 / 2), 10), ((-1 / 2), 15), ((1 / 2), 19), ((-1 / 2), 20), ((1 / 2), 23), ((-1 / 2), 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((-17 / 22), 0), ((1 / 22), 5), ((-4 / 11), 10), ((-5 / 22), 15), ((4 / 11), 20), ((1 / 22), 25), ((-5 / 22), 30)],
      alternatingSixCyclotomicValue [((-6 / 11), 3), ((-6 / 11), 5), ((-6 / 11), 7), ((1 / 11), 10), ((-2 / 11), 15), ((6 / 11), 19), ((-5 / 11), 20), ((6 / 11), 23), ((-3 / 11), 25), ((1 / 11), 30), ((-6 / 11), 31)]],
    ![alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0), (1, 10)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue []],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)]]
  ]

/-- Checked inverse of the row 13 eigenbasis. -/
def alternatingSixAmbientRow13EigenbasisInverse :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((-89 / 386), 0), ((-333 / 772), 3), ((215 / 193), 5), ((-333 / 772), 7), ((349 / 772), 10), ((-45 / 193), 15), ((333 / 772), 19), ((295 / 772), 20), ((333 / 772), 23), ((-521 / 772), 25), ((-599 / 772), 30), ((-333 / 772), 31)],
      alternatingSixCyclotomicValue [((117 / 772), 0), ((-80 / 193), 3), ((73 / 386), 5), ((-80 / 193), 7), ((-125 / 386), 10), ((263 / 386), 15), ((80 / 193), 19), ((89 / 386), 20), ((80 / 193), 23), ((-237 / 386), 25), ((37 / 772), 30), ((-80 / 193), 31)],
      alternatingSixCyclotomicValue [((-301 / 772), 0), ((-343 / 772), 3), ((-595 / 772), 5), ((-343 / 772), 7), ((-137 / 386), 10), ((331 / 772), 15), ((343 / 772), 19), ((48 / 193), 20), ((343 / 772), 23), ((-93 / 386), 25), ((-49 / 772), 30), ((-343 / 772), 31)],
      alternatingSixCyclotomicValue [((-763 / 772), 0), ((-277 / 772), 3), ((323 / 772), 5), ((-277 / 772), 7), ((441 / 772), 10), ((-301 / 772), 15), ((277 / 772), 19), ((949 / 772), 20), ((277 / 772), 23), ((28 / 193), 25), ((-585 / 386), 30), ((-277 / 772), 31)],
      alternatingSixCyclotomicValue [((-249 / 772), 0), ((-384 / 193), 3), ((585 / 772), 5), ((-384 / 193), 7), ((-107 / 193), 10), ((865 / 772), 15), ((384 / 193), 19), ((543 / 386), 20), ((384 / 193), 23), ((-847 / 772), 25), ((-633 / 772), 30), ((-384 / 193), 31)],
      alternatingSixCyclotomicValue [((-125 / 772), 0), ((-30 / 193), 3), ((341 / 386), 5), ((-30 / 193), 7), ((61 / 193), 10), ((-11 / 193), 15), ((30 / 193), 19), ((-39 / 386), 20), ((30 / 193), 23), ((-113 / 386), 25), ((231 / 772), 30), ((-30 / 193), 31)]],
    ![alternatingSixCyclotomicValue [((-221 / 772), 0), ((197 / 772), 3), ((389 / 772), 5), ((197 / 772), 7), ((279 / 386), 10), ((-629 / 772), 15), ((-197 / 772), 19), ((175 / 386), 20), ((-197 / 772), 23), ((319 / 386), 25), ((-413 / 772), 30), ((197 / 772), 31)],
      alternatingSixCyclotomicValue [((129 / 772), 0), ((-108 / 193), 3), ((112 / 193), 5), ((-108 / 193), 7), ((-241 / 772), 10), ((-1 / 193), 15), ((108 / 193), 19), ((221 / 772), 20), ((108 / 193), 23), ((-49 / 193), 25), ((-43 / 193), 30), ((-108 / 193), 31)],
      alternatingSixCyclotomicValue [((163 / 772), 0), ((-123 / 193), 3), ((403 / 772), 5), ((-123 / 193), 7), ((-119 / 772), 10), ((167 / 772), 15), ((123 / 193), 19), ((-397 / 772), 20), ((123 / 193), 23), ((-695 / 772), 25), ((-173 / 386), 30), ((-123 / 193), 31)],
      alternatingSixCyclotomicValue [((-433 / 386), 0), ((117 / 386), 3), ((79 / 772), 5), ((117 / 386), 7), ((991 / 772), 10), ((-609 / 772), 15), ((-117 / 386), 19), ((17 / 772), 20), ((-117 / 386), 23), ((653 / 772), 25), ((-711 / 772), 30), ((117 / 386), 31)],
      alternatingSixCyclotomicValue [((-809 / 772), 0), ((-877 / 772), 3), ((306 / 193), 5), ((-877 / 772), 7), ((117 / 772), 10), ((-357 / 386), 15), ((877 / 772), 19), ((559 / 772), 20), ((877 / 772), 23), ((-53 / 772), 25), ((-245 / 193), 30), ((-877 / 772), 31)],
      alternatingSixCyclotomicValue [((169 / 772), 0), ((56 / 193), 3), ((-109 / 386), 5), ((56 / 193), 7), ((-211 / 772), 10), ((-121 / 193), 15), ((-56 / 193), 19), ((107 / 772), 20), ((-56 / 193), 23), ((301 / 386), 25), ((209 / 386), 30), ((56 / 193), 31)]],
    ![alternatingSixCyclotomicValue [((-607 / 772), 0), ((1 / 193), 3), ((-95 / 386), 5), ((1 / 193), 7), ((43 / 193), 10), ((-109 / 193), 15), ((-1 / 193), 19), ((-9 / 193), 20), ((-1 / 193), 23), ((319 / 386), 25), ((-27 / 772), 30), ((1 / 193), 31)],
      alternatingSixCyclotomicValue [((-257 / 772), 0), ((-108 / 193), 3), ((112 / 193), 5), ((-108 / 193), 7), ((-12 / 193), 10), ((-1 / 193), 15), ((108 / 193), 19), ((207 / 386), 20), ((108 / 193), 23), ((-49 / 193), 25), ((-365 / 772), 30), ((-108 / 193), 31)],
      alternatingSixCyclotomicValue [((163 / 772), 0), ((-299 / 772), 3), ((403 / 772), 5), ((-299 / 772), 7), ((37 / 386), 10), ((553 / 772), 15), ((299 / 772), 19), ((91 / 386), 20), ((299 / 772), 23), ((-29 / 193), 25), ((-153 / 772), 30), ((-299 / 772), 31)],
      alternatingSixCyclotomicValue [((-120 / 193), 0), ((155 / 193), 3), ((-307 / 772), 5), ((155 / 193), 7), ((399 / 386), 10), ((-609 / 772), 15), ((-155 / 193), 19), ((-44 / 193), 20), ((-155 / 193), 23), ((653 / 772), 25), ((-259 / 386), 30), ((155 / 193), 31)],
      alternatingSixCyclotomicValue [((-154 / 193), 0), ((-105 / 772), 3), ((1031 / 772), 5), ((-105 / 772), 7), ((889 / 772), 10), ((-521 / 772), 15), ((105 / 772), 19), ((559 / 772), 20), ((105 / 772), 23), ((35 / 193), 25), ((-1173 / 772), 30), ((-105 / 772), 31)],
      alternatingSixCyclotomicValue [((-6 / 193), 0), ((417 / 772), 3), ((42 / 193), 5), ((417 / 772), 7), ((175 / 772), 10), ((-121 / 193), 15), ((-417 / 772), 19), ((-279 / 772), 20), ((-417 / 772), 23), ((23 / 772), 25), ((-161 / 772), 30), ((417 / 772), 31)]],
    ![alternatingSixCyclotomicValue [((967 / 772), 0), ((-855 / 772), 3), ((565 / 772), 5), ((-855 / 772), 7), ((-265 / 193), 10), ((941 / 772), 15), ((855 / 772), 19), ((42 / 193), 20), ((855 / 772), 23), ((-294 / 193), 25), ((319 / 772), 30), ((-855 / 772), 31)],
      alternatingSixCyclotomicValue [((749 / 772), 0), ((43 / 386), 3), ((-209 / 386), 5), ((43 / 386), 7), ((-355 / 772), 10), ((331 / 386), 15), ((-43 / 386), 19), ((-967 / 772), 20), ((-43 / 386), 23), ((-93 / 193), 25), ((265 / 193), 30), ((43 / 386), 31)],
      alternatingSixCyclotomicValue [((-53 / 772), 0), ((183 / 386), 3), ((-401 / 772), 5), ((183 / 386), 7), ((105 / 772), 10), ((57 / 772), 15), ((-183 / 386), 19), ((-399 / 772), 20), ((-183 / 386), 23), ((91 / 772), 25), ((82 / 193), 30), ((183 / 386), 31)],
      alternatingSixCyclotomicValue [((174 / 193), 0), ((-739 / 386), 3), ((1111 / 772), 5), ((-739 / 386), 7), ((-1215 / 772), 10), ((1105 / 772), 15), ((739 / 386), 19), ((757 / 772), 20), ((739 / 386), 23), ((-1439 / 772), 25), ((37 / 772), 30), ((-739 / 386), 31)],
      alternatingSixCyclotomicValue [((2167 / 772), 0), ((-861 / 772), 3), ((-77 / 193), 5), ((-861 / 772), 7), ((-1897 / 772), 10), ((1087 / 386), 15), ((861 / 772), 19), ((-1129 / 772), 20), ((861 / 772), 23), ((-1747 / 772), 25), ((500 / 193), 30), ((-861 / 772), 31)],
      alternatingSixCyclotomicValue [((305 / 772), 0), ((-201 / 386), 3), ((187 / 386), 5), ((-201 / 386), 7), ((-495 / 772), 10), ((50 / 193), 15), ((201 / 386), 19), ((337 / 772), 20), ((201 / 386), 23), ((-59 / 193), 25), ((27 / 193), 30), ((-201 / 386), 31)]],
    ![alternatingSixCyclotomicValue [((137 / 772), 0), ((2 / 193), 3), ((-95 / 193), 5), ((2 / 193), 7), ((-107 / 193), 10), ((143 / 386), 15), ((-2 / 193), 19), ((157 / 386), 20), ((-2 / 193), 23), ((59 / 386), 25), ((139 / 772), 30), ((2 / 193), 31)],
      alternatingSixCyclotomicValue [((451 / 772), 0), ((147 / 386), 3), ((-131 / 386), 5), ((147 / 386), 7), ((-24 / 193), 10), ((-197 / 386), 15), ((-147 / 386), 19), ((-165 / 386), 20), ((-147 / 386), 23), ((95 / 193), 25), ((235 / 772), 30), ((147 / 386), 31)],
      alternatingSixCyclotomicValue [((519 / 772), 0), ((367 / 772), 3), ((227 / 772), 5), ((367 / 772), 7), ((37 / 193), 10), ((-631 / 772), 15), ((-367 / 772), 19), ((-102 / 193), 20), ((-367 / 772), 23), ((77 / 386), 25), ((273 / 772), 30), ((367 / 772), 31)],
      alternatingSixCyclotomicValue [((146 / 193), 0), ((-76 / 193), 3), ((351 / 772), 5), ((-76 / 193), 7), ((-180 / 193), 10), ((133 / 772), 15), ((76 / 193), 19), ((-88 / 193), 20), ((76 / 193), 23), ((-431 / 772), 25), ((447 / 386), 30), ((-76 / 193), 31)],
      alternatingSixCyclotomicValue [((735 / 386), 0), ((755 / 772), 3), ((-447 / 772), 5), ((755 / 772), 7), ((-731 / 772), 10), ((-463 / 772), 15), ((-755 / 772), 19), ((-619 / 772), 20), ((-755 / 772), 23), ((70 / 193), 25), ((935 / 772), 30), ((755 / 772), 31)],
      alternatingSixCyclotomicValue [((-12 / 193), 0), ((-131 / 772), 3), ((-411 / 386), 5), ((-131 / 772), 7), ((-229 / 772), 10), ((95 / 386), 15), ((131 / 772), 19), ((407 / 772), 20), ((131 / 772), 23), ((239 / 772), 25), ((-515 / 772), 30), ((-131 / 772), 31)]],
    ![alternatingSixCyclotomicValue [((-373 / 386), 0), ((329 / 386), 3), ((-477 / 386), 5), ((329 / 386), 7), ((251 / 386), 10), ((-78 / 193), 15), ((-329 / 386), 19), ((-259 / 386), 20), ((-329 / 386), 23), ((269 / 386), 25), ((47 / 386), 30), ((329 / 386), 31)],
      alternatingSixCyclotomicValue [((-439 / 386), 0), ((173 / 386), 3), ((-15 / 386), 5), ((173 / 386), 7), ((149 / 193), 10), ((-329 / 386), 15), ((-173 / 386), 19), ((373 / 386), 20), ((-173 / 386), 23), ((142 / 193), 25), ((-222 / 193), 30), ((173 / 386), 31)],
      alternatingSixCyclotomicValue [((-55 / 386), 0), ((63 / 386), 3), ((-1 / 386), 5), ((63 / 386), 7), ((7 / 386), 10), ((-56 / 193), 15), ((-63 / 386), 19), ((199 / 193), 20), ((-63 / 386), 23), ((151 / 193), 25), ((9 / 386), 30), ((63 / 386), 31)],
      alternatingSixCyclotomicValue [((85 / 386), 0), ((311 / 193), 3), ((-595 / 386), 5), ((311 / 193), 7), ((56 / 193), 10), ((-124 / 193), 15), ((-311 / 193), 19), ((-387 / 386), 20), ((-311 / 193), 23), ((393 / 386), 25), ((337 / 386), 30), ((311 / 193), 31)],
      alternatingSixCyclotomicValue [((-679 / 386), 0), ((869 / 386), 3), ((-229 / 193), 5), ((869 / 386), 7), ((445 / 193), 10), ((-365 / 193), 15), ((-869 / 386), 19), ((285 / 386), 20), ((-869 / 386), 23), ((450 / 193), 25), ((-255 / 193), 30), ((869 / 386), 31)],
      alternatingSixCyclotomicValue [((149 / 386), 0), ((89 / 386), 3), ((-39 / 193), 5), ((89 / 386), 7), ((353 / 386), 10), ((71 / 193), 15), ((-89 / 386), 19), ((-111 / 193), 20), ((-89 / 386), 23), ((-183 / 386), 25), ((-263 / 386), 30), ((89 / 386), 31)]]
  ]

/-- The row 13 first generator in the checked diagonal basis. -/
def alternatingSixAmbientRow13TransformedGeneratorA :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((-1 / 2), 3), ((1 / 4), 5), ((-1 / 2), 7), ((3 / 4), 15), ((1 / 2), 19), ((1 / 4), 20), ((1 / 2), 23), ((1 / 2), 25), ((-1 / 4), 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((-5 / 12), 0), ((1 / 3), 3), ((1 / 3), 7), ((-5 / 12), 10), ((-1 / 6), 15), ((-1 / 3), 19), ((-5 / 12), 20), ((-1 / 3), 23), ((1 / 3), 30), ((1 / 3), 31)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 4), 10), ((1 / 4), 25)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 4), 5), ((-3 / 4), 10), ((1 / 2), 15), ((-1 / 4), 20), ((1 / 4), 25)],
      alternatingSixCyclotomicValue [((-4 / 11), 0), ((3 / 22), 3), ((-3 / 22), 5), ((3 / 22), 7), ((-15 / 44), 10), ((-1 / 11), 15), ((-3 / 22), 19), ((2 / 11), 20), ((-3 / 22), 23), ((13 / 44), 25), ((1 / 11), 30), ((3 / 22), 31)],
      alternatingSixCyclotomicValue [((-21 / 44), 0), ((-2 / 11), 3), ((-5 / 22), 5), ((-2 / 11), 7), ((21 / 44), 10), ((2 / 11), 19), ((3 / 44), 20), ((2 / 11), 23), ((-3 / 22), 25), ((-9 / 22), 30), ((-2 / 11), 31)]],
    ![alternatingSixCyclotomicValue [(-1, 0), ((-1 / 4), 3), ((-1 / 4), 7), ((-1 / 4), 10), ((1 / 4), 15), ((1 / 4), 19), ((1 / 2), 20), ((1 / 4), 23), ((1 / 2), 25), ((1 / 4), 30), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 2), 3), ((1 / 2), 7), ((-1 / 4), 10), ((-1 / 2), 15), ((-1 / 2), 19), ((-1 / 4), 20), ((-1 / 2), 23), ((-1 / 2), 25), ((1 / 4), 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 10), ((1 / 4), 15), ((1 / 2), 20), ((1 / 4), 25)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((3 / 4), 3), ((1 / 4), 5), ((3 / 4), 7), ((-1 / 2), 10), ((-3 / 4), 15), ((-3 / 4), 19), ((1 / 4), 20), ((-3 / 4), 23), ((-3 / 4), 25), ((1 / 2), 30), ((3 / 4), 31)],
      alternatingSixCyclotomicValue [((-19 / 44), 0), ((1 / 11), 3), ((-1 / 22), 5), ((1 / 11), 7), ((7 / 44), 10), ((-9 / 44), 15), ((-1 / 11), 19), ((7 / 22), 20), ((-1 / 11), 23), ((-15 / 44), 25), ((1 / 11), 31)],
      alternatingSixCyclotomicValue [((2 / 11), 0), ((3 / 22), 5), ((7 / 44), 10), ((-2 / 11), 15), ((-29 / 44), 20), ((3 / 22), 25), ((3 / 44), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 5), ((-1 / 4), 10), ((-1 / 4), 15)],
      alternatingSixCyclotomicValue [((1 / 3), 0), ((1 / 4), 3), ((1 / 6), 5), ((1 / 4), 7), ((1 / 6), 10), ((-1 / 4), 19), ((-1 / 6), 20), ((-1 / 4), 23), ((-1 / 12), 25), ((-1 / 3), 30), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 3), ((-1 / 4), 5), ((1 / 4), 7), ((1 / 4), 10), ((-1 / 4), 15), ((-1 / 4), 19), ((-1 / 4), 23), ((1 / 4), 25), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 3), ((-1 / 4), 5), ((-1 / 4), 7), ((-1 / 4), 10), ((1 / 4), 19), ((-1 / 4), 20), ((1 / 4), 23), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 22), 0), ((-3 / 44), 3), ((1 / 44), 5), ((-3 / 44), 7), ((7 / 44), 10), ((1 / 44), 15), ((3 / 44), 19), ((1 / 22), 20), ((3 / 44), 23), ((-3 / 44), 25), ((2 / 11), 30), ((-3 / 44), 31)],
      alternatingSixCyclotomicValue [((-3 / 22), 0), ((-5 / 44), 3), ((-1 / 11), 5), ((-5 / 44), 7), ((1 / 22), 10), ((2 / 11), 15), ((5 / 44), 19), ((1 / 22), 20), ((5 / 44), 23), ((15 / 44), 25), ((-3 / 22), 30), ((-5 / 44), 31)]],
    ![alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 4), 5), ((-1 / 2), 10), ((-1 / 4), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 6), 0), ((1 / 6), 3), ((-1 / 6), 5), ((1 / 6), 7), ((-1 / 4), 10), ((-1 / 3), 15), ((-1 / 6), 19), ((7 / 12), 20), ((-1 / 6), 23), ((1 / 3), 25), ((-1 / 4), 30), ((1 / 6), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 3), ((1 / 4), 5), ((-1 / 4), 7), ((1 / 4), 19), ((1 / 4), 20), ((1 / 4), 23), ((-1 / 4), 25), ((-1 / 4), 30), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 5), ((-1 / 4), 10), ((-1 / 4), 15)],
      alternatingSixCyclotomicValue [((7 / 44), 0), ((5 / 44), 3), ((-9 / 44), 5), ((5 / 44), 7), ((-2 / 11), 10), ((1 / 22), 15), ((-5 / 44), 19), ((-7 / 44), 20), ((-5 / 44), 23), ((5 / 44), 25), ((5 / 44), 30), ((5 / 44), 31)],
      alternatingSixCyclotomicValue [((-3 / 11), 0), ((3 / 11), 3), ((-2 / 11), 5), ((3 / 11), 7), ((15 / 44), 10), ((-3 / 22), 15), ((-3 / 11), 19), ((-7 / 44), 20), ((-3 / 11), 23), ((2 / 11), 25), ((-1 / 44), 30), ((3 / 11), 31)]],
    ![alternatingSixCyclotomicValue [((1 / 2), 3), ((-1 / 4), 5), ((1 / 2), 7), ((1 / 4), 10), ((-3 / 4), 15), ((-1 / 2), 19), ((-1 / 2), 23), ((-1 / 2), 25), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [(1, 0), ((-5 / 12), 3), ((-1 / 6), 5), ((-5 / 12), 7), ((2 / 3), 10), ((1 / 3), 15), ((5 / 12), 19), ((-1 / 2), 20), ((5 / 12), 23), ((1 / 12), 25), ((-1 / 3), 30), ((-5 / 12), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 4), 3), ((1 / 4), 5), ((-1 / 4), 7), ((1 / 4), 10), ((1 / 4), 15), ((1 / 4), 19), ((1 / 4), 23), ((-1 / 4), 25), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 4), 3), ((1 / 4), 5), ((1 / 4), 7), ((-3 / 4), 10), ((-1 / 4), 19), ((-1 / 4), 20), ((-1 / 4), 23), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((4 / 11), 0), ((-3 / 44), 3), ((9 / 44), 5), ((-3 / 44), 7), ((9 / 44), 10), ((5 / 44), 15), ((3 / 44), 19), ((3 / 44), 23), ((-17 / 44), 25), ((-5 / 22), 30), ((-3 / 44), 31)],
      alternatingSixCyclotomicValue [((-3 / 22), 0), ((9 / 44), 3), ((5 / 22), 5), ((9 / 44), 7), ((9 / 22), 10), ((-1 / 22), 15), ((-9 / 44), 19), ((-3 / 11), 20), ((-9 / 44), 23), ((-1 / 4), 25), ((-3 / 11), 30), ((9 / 44), 31)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 3), ((-1 / 4), 5), ((-1 / 4), 7), ((1 / 4), 10), ((-1 / 4), 15), ((1 / 4), 19), ((1 / 4), 20), ((1 / 4), 23), ((1 / 4), 30), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 6), 0), ((-1 / 3), 3), ((-1 / 2), 5), ((-1 / 3), 7), ((1 / 6), 10), ((1 / 6), 15), ((1 / 3), 19), ((-1 / 3), 20), ((1 / 3), 23), ((1 / 2), 25), ((-1 / 3), 30), ((-1 / 3), 31)],
      alternatingSixCyclotomicValue [((3 / 4), 3), ((3 / 4), 5), ((3 / 4), 7), ((-1 / 4), 10), ((-1 / 4), 15), ((-3 / 4), 19), ((-1 / 4), 20), ((-3 / 4), 23), ((-1 / 2), 25), ((1 / 4), 30), ((3 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 3), ((1 / 2), 5), ((1 / 4), 7), ((-1 / 4), 10), ((1 / 2), 15), ((-1 / 4), 19), ((-1 / 4), 20), ((-1 / 4), 23), ((1 / 4), 25), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((-5 / 22), 0), ((-19 / 44), 3), ((-21 / 44), 5), ((-19 / 44), 7), ((-1 / 44), 10), ((1 / 4), 15), ((19 / 44), 19), ((3 / 44), 20), ((19 / 44), 23), ((4 / 11), 25), ((15 / 44), 30), ((-19 / 44), 31)],
      alternatingSixCyclotomicValue [((-4 / 11), 0), ((-2 / 11), 3), ((1 / 22), 5), ((-2 / 11), 7), ((1 / 22), 10), ((3 / 22), 15), ((2 / 11), 19), ((2 / 11), 23), ((3 / 22), 25), ((5 / 22), 30), ((-2 / 11), 31)]]
  ]

macro "close_cyclotomic_row13" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)


private theorem row13_eigenbasisInverse_mul_0_0 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        0 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((100 / 193) : ℂ) - ((2993 / 1544) : ℂ) * ζ ^ 3 + ((100 / 193) : ℂ) * ζ ^ 4 + ((297 / 772) : ℂ) * ζ ^ 5 - ((1171 / 1544) : ℂ) * ζ ^ 6 - ((5 / 1544) : ℂ) * ζ ^ 8 - ((297 / 772) : ℂ) * ζ ^ 9 + ((21 / 386) : ℂ) * ζ ^ 10 + ((337 / 1544) : ℂ) * ζ ^ 13 - ((1255 / 1544) : ℂ) * ζ ^ 14 - ((75 / 772) : ℂ) * ζ ^ 15 + ((1659 / 1544) : ℂ) * ζ ^ 18 + ((75 / 772) : ℂ) * ζ ^ 19 - ((503 / 1544) : ℂ) * ζ ^ 20 + ((1171 / 1544) : ℂ) * ζ ^ 22 + ((2753 / 1544) : ℂ) * ζ ^ 23 + ((503 / 1544) : ℂ) * ζ ^ 24 + ((451 / 386) : ℂ) * ζ ^ 25 + ((1171 / 1544) : ℂ) * ζ ^ 26 - ((76 / 193) : ℂ) * ζ ^ 28 - ((451 / 386) : ℂ) * ζ ^ 29 - ((1171 / 1544) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_0_1 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        0 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((1751 / 2316) : ℂ) - ((1027 / 2316) : ℂ) * ζ ^ 3 + ((1751 / 2316) : ℂ) * ζ ^ 4 + ((2113 / 2316) : ℂ) * ζ ^ 5 - ((23 / 1158) : ℂ) * ζ ^ 6 - ((122 / 579) : ℂ) * ζ ^ 8 - ((2113 / 2316) : ℂ) * ζ ^ 9 - ((955 / 2316) : ℂ) * ζ ^ 10 + ((689 / 772) : ℂ) * ζ ^ 13 + ((303 / 772) : ℂ) * ζ ^ 14 + ((1427 / 2316) : ℂ) * ζ ^ 15 - ((1421 / 2316) : ℂ) * ζ ^ 18 - ((1427 / 2316) : ℂ) * ζ ^ 19 + ((49 / 579) : ℂ) * ζ ^ 20 + ((23 / 1158) : ℂ) * ζ ^ 22 - ((1 / 12) : ℂ) * ζ ^ 23 - ((49 / 579) : ℂ) * ζ ^ 24 + ((773 / 1158) : ℂ) * ζ ^ 25 + ((23 / 1158) : ℂ) * ζ ^ 26 - ((118 / 579) : ℂ) * ζ ^ 28 - ((773 / 1158) : ℂ) * ζ ^ 29 - ((23 / 1158) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_0_2 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        0 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((391 / 772) : ℂ) - ((3447 / 1544) : ℂ) * ζ ^ 3 + ((391 / 772) : ℂ) * ζ ^ 4 + ((85 / 772) : ℂ) * ζ ^ 5 - ((689 / 1544) : ℂ) * ζ ^ 6 - ((93 / 1544) : ℂ) * ζ ^ 8 - ((85 / 772) : ℂ) * ζ ^ 9 + ((69 / 386) : ℂ) * ζ ^ 10 + ((867 / 1544) : ℂ) * ζ ^ 13 - ((5 / 8) : ℂ) * ζ ^ 14 + ((335 / 772) : ℂ) * ζ ^ 15 + ((11 / 1544) : ℂ) * ζ ^ 18 - ((335 / 772) : ℂ) * ζ ^ 19 - ((253 / 1544) : ℂ) * ζ ^ 20 + ((689 / 1544) : ℂ) * ζ ^ 22 + ((585 / 1544) : ℂ) * ζ ^ 23 + ((253 / 1544) : ℂ) * ζ ^ 24 + ((227 / 386) : ℂ) * ζ ^ 25 + ((689 / 1544) : ℂ) * ζ ^ 26 - ((76 / 193) : ℂ) * ζ ^ 28 - ((227 / 386) : ℂ) * ζ ^ 29 - ((689 / 1544) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_0_3 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        0 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((553 / 386) : ℂ) - ((21 / 8) : ℂ) * ζ ^ 3 + ((553 / 386) : ℂ) * ζ ^ 4 + ((5323 / 1544) : ℂ) * ζ ^ 5 - ((99 / 386) : ℂ) * ζ ^ 6 - ((1381 / 386) : ℂ) * ζ ^ 8 - ((5323 / 1544) : ℂ) * ζ ^ 9 - ((371 / 386) : ℂ) * ζ ^ 10 - ((247 / 1544) : ℂ) * ζ ^ 13 + ((136 / 193) : ℂ) * ζ ^ 14 + ((1601 / 1544) : ℂ) * ζ ^ 15 - ((107 / 772) : ℂ) * ζ ^ 18 - ((1601 / 1544) : ℂ) * ζ ^ 19 + ((355 / 386) : ℂ) * ζ ^ 20 + ((99 / 386) : ℂ) * ζ ^ 22 + ((1183 / 1544) : ℂ) * ζ ^ 23 - ((355 / 386) : ℂ) * ζ ^ 24 - ((2615 / 1544) : ℂ) * ζ ^ 25 + ((99 / 386) : ℂ) * ζ ^ 26 + ((823 / 772) : ℂ) * ζ ^ 28 + ((2615 / 1544) : ℂ) * ζ ^ 29 - ((99 / 386) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_0_4 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        0 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((6203 / 8492) : ℂ) - ((21871 / 16984) : ℂ) * ζ ^ 3 - ((6203 / 8492) : ℂ) * ζ ^ 4 + ((2611 / 8492) : ℂ) * ζ ^ 5 + ((1343 / 16984) : ℂ) * ζ ^ 6 + ((20671 / 16984) : ℂ) * ζ ^ 8 - ((2611 / 8492) : ℂ) * ζ ^ 9 - ((5201 / 4246) : ℂ) * ζ ^ 10 + ((5191 / 16984) : ℂ) * ζ ^ 13 + ((22147 / 16984) : ℂ) * ζ ^ 14 + ((369 / 8492) : ℂ) * ζ ^ 15 - ((24737 / 16984) : ℂ) * ζ ^ 18 - ((369 / 8492) : ℂ) * ζ ^ 19 + ((9891 / 16984) : ℂ) * ζ ^ 20 - ((1343 / 16984) : ℂ) * ζ ^ 22 - ((7131 / 16984) : ℂ) * ζ ^ 23 - ((9891 / 16984) : ℂ) * ζ ^ 24 + ((380 / 2123) : ℂ) * ζ ^ 25 - ((1343 / 16984) : ℂ) * ζ ^ 26 + ((52 / 193) : ℂ) * ζ ^ 28 - ((380 / 2123) : ℂ) * ζ ^ 29 + ((1343 / 16984) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_0_5 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        0 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((1143 / 4246) : ℂ) + ((4953 / 8492) : ℂ) * ζ ^ 3 + ((1143 / 4246) : ℂ) * ζ ^ 4 + ((424 / 2123) : ℂ) * ζ ^ 5 + ((13 / 2123) : ℂ) * ζ ^ 6 - ((3953 / 8492) : ℂ) * ζ ^ 8 - ((424 / 2123) : ℂ) * ζ ^ 9 - ((107 / 2123) : ℂ) * ζ ^ 10 - ((425 / 8492) : ℂ) * ζ ^ 13 + ((120 / 2123) : ℂ) * ζ ^ 14 + ((2190 / 2123) : ℂ) * ζ ^ 15 + ((1110 / 2123) : ℂ) * ζ ^ 18 - ((2190 / 2123) : ℂ) * ζ ^ 19 + ((3581 / 8492) : ℂ) * ζ ^ 20 - ((13 / 2123) : ℂ) * ζ ^ 22 + ((3873 / 8492) : ℂ) * ζ ^ 23 - ((3581 / 8492) : ℂ) * ζ ^ 24 - ((5835 / 8492) : ℂ) * ζ ^ 25 - ((13 / 2123) : ℂ) * ζ ^ 26 + ((29 / 8492) : ℂ) * ζ ^ 28 + ((5835 / 8492) : ℂ) * ζ ^ 29 + ((13 / 2123) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_1_0 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        1 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((347 / 772) : ℂ) - ((3201 / 1544) : ℂ) * ζ ^ 3 + ((347 / 772) : ℂ) * ζ ^ 4 + ((551 / 1544) : ℂ) * ζ ^ 5 - ((42 / 193) : ℂ) * ζ ^ 6 + ((131 / 386) : ℂ) * ζ ^ 8 - ((551 / 1544) : ℂ) * ζ ^ 9 - ((117 / 772) : ℂ) * ζ ^ 10 + ((1005 / 1544) : ℂ) * ζ ^ 13 - ((51 / 772) : ℂ) * ζ ^ 14 - ((685 / 1544) : ℂ) * ζ ^ 15 - ((815 / 772) : ℂ) * ζ ^ 18 + ((685 / 1544) : ℂ) * ζ ^ 19 - ((185 / 193) : ℂ) * ζ ^ 20 + ((42 / 193) : ℂ) * ζ ^ 22 + ((1333 / 1544) : ℂ) * ζ ^ 23 + ((185 / 193) : ℂ) * ζ ^ 24 + ((1123 / 1544) : ℂ) * ζ ^ 25 + ((42 / 193) : ℂ) * ζ ^ 26 - ((63 / 772) : ℂ) * ζ ^ 28 - ((1123 / 1544) : ℂ) * ζ ^ 29 - ((42 / 193) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_1_1 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        1 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((1891 / 2316) : ℂ) + ((283 / 2316) : ℂ) * ζ ^ 3 + ((1891 / 2316) : ℂ) * ζ ^ 4 + ((1103 / 1158) : ℂ) * ζ ^ 5 + ((163 / 579) : ℂ) * ζ ^ 6 - ((3245 / 2316) : ℂ) * ζ ^ 8 - ((1103 / 1158) : ℂ) * ζ ^ 9 + ((689 / 2316) : ℂ) * ζ ^ 10 + ((605 / 386) : ℂ) * ζ ^ 13 - ((37 / 2316) : ℂ) * ζ ^ 14 - ((370 / 579) : ℂ) * ζ ^ 15 - ((257 / 386) : ℂ) * ζ ^ 18 + ((370 / 579) : ℂ) * ζ ^ 19 - ((619 / 579) : ℂ) * ζ ^ 20 - ((163 / 579) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 23 + ((619 / 579) : ℂ) * ζ ^ 24 + ((488 / 579) : ℂ) * ζ ^ 25 - ((163 / 579) : ℂ) * ζ ^ 26 - ((111 / 193) : ℂ) * ζ ^ 28 - ((488 / 579) : ℂ) * ζ ^ 29 + ((163 / 579) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_1_2 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        1 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((1213 / 772) : ℂ) - ((1633 / 1544) : ℂ) * ζ ^ 3 + ((1213 / 772) : ℂ) * ζ ^ 4 + ((519 / 1544) : ℂ) * ζ ^ 5 + ((167 / 772) : ℂ) * ζ ^ 6 - ((415 / 772) : ℂ) * ζ ^ 8 - ((519 / 1544) : ℂ) * ζ ^ 9 + ((553 / 772) : ℂ) * ζ ^ 10 + ((1817 / 1544) : ℂ) * ζ ^ 13 - ((1 / 2) : ℂ) * ζ ^ 14 - ((157 / 1544) : ℂ) * ζ ^ 15 - ((211 / 386) : ℂ) * ζ ^ 18 + ((157 / 1544) : ℂ) * ζ ^ 19 - ((179 / 193) : ℂ) * ζ ^ 20 - ((167 / 772) : ℂ) * ζ ^ 22 + ((259 / 1544) : ℂ) * ζ ^ 23 + ((179 / 193) : ℂ) * ζ ^ 24 + ((531 / 1544) : ℂ) * ζ ^ 25 - ((167 / 772) : ℂ) * ζ ^ 26 - ((63 / 772) : ℂ) * ζ ^ 28 - ((531 / 1544) : ℂ) * ζ ^ 29 + ((167 / 772) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_1_3 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        1 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((436 / 193) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 3 + ((436 / 193) : ℂ) * ζ ^ 4 + ((4127 / 1544) : ℂ) * ζ ^ 5 - ((1847 / 1544) : ℂ) * ζ ^ 6 - ((4215 / 1544) : ℂ) * ζ ^ 8 - ((4127 / 1544) : ℂ) * ζ ^ 9 - ((221 / 386) : ℂ) * ζ ^ 10 + ((861 / 772) : ℂ) * ζ ^ 13 - ((963 / 1544) : ℂ) * ζ ^ 14 - ((531 / 1544) : ℂ) * ζ ^ 15 + ((155 / 1544) : ℂ) * ζ ^ 18 + ((531 / 1544) : ℂ) * ζ ^ 19 + ((3075 / 1544) : ℂ) * ζ ^ 20 + ((1847 / 1544) : ℂ) * ζ ^ 22 - ((269 / 386) : ℂ) * ζ ^ 23 - ((3075 / 1544) : ℂ) * ζ ^ 24 - ((201 / 1544) : ℂ) * ζ ^ 25 + ((1847 / 1544) : ℂ) * ζ ^ 26 + ((561 / 772) : ℂ) * ζ ^ 28 + ((201 / 1544) : ℂ) * ζ ^ 29 - ((1847 / 1544) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_1_4 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        1 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((360 / 2123) : ℂ) - ((21719 / 16984) : ℂ) * ζ ^ 3 + ((360 / 2123) : ℂ) * ζ ^ 4 + ((19807 / 16984) : ℂ) * ζ ^ 5 + ((568 / 2123) : ℂ) * ζ ^ 6 - ((94 / 193) : ℂ) * ζ ^ 8 - ((19807 / 16984) : ℂ) * ζ ^ 9 - ((183 / 386) : ℂ) * ζ ^ 10 + ((15027 / 16984) : ℂ) * ζ ^ 13 + ((3149 / 4246) : ℂ) * ζ ^ 14 - ((17165 / 16984) : ℂ) * ζ ^ 15 - ((6261 / 8492) : ℂ) * ζ ^ 18 + ((17165 / 16984) : ℂ) * ζ ^ 19 - ((1219 / 4246) : ℂ) * ζ ^ 20 - ((568 / 2123) : ℂ) * ζ ^ 22 - ((1341 / 1544) : ℂ) * ζ ^ 23 + ((1219 / 4246) : ℂ) * ζ ^ 24 + ((3139 / 16984) : ℂ) * ζ ^ 25 - ((568 / 2123) : ℂ) * ζ ^ 26 + ((271 / 8492) : ℂ) * ζ ^ 28 - ((3139 / 16984) : ℂ) * ζ ^ 29 + ((568 / 2123) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_1_5 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        1 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((3997 / 8492) : ℂ) + ((257 / 386) : ℂ) * ζ ^ 3 - ((3997 / 8492) : ℂ) * ζ ^ 4 + ((707 / 8492) : ℂ) * ζ ^ 5 - ((4253 / 8492) : ℂ) * ζ ^ 6 + ((4767 / 8492) : ℂ) * ζ ^ 8 - ((707 / 8492) : ℂ) * ζ ^ 9 - ((12235 / 8492) : ℂ) * ζ ^ 10 - ((3131 / 8492) : ℂ) * ζ ^ 13 + ((3991 / 4246) : ℂ) * ζ ^ 14 - ((1491 / 8492) : ℂ) * ζ ^ 15 - ((3565 / 4246) : ℂ) * ζ ^ 18 + ((1491 / 8492) : ℂ) * ζ ^ 19 + ((879 / 772) : ℂ) * ζ ^ 20 + ((4253 / 8492) : ℂ) * ζ ^ 22 - ((1183 / 4246) : ℂ) * ζ ^ 23 - ((879 / 772) : ℂ) * ζ ^ 24 - ((109 / 8492) : ℂ) * ζ ^ 25 + ((4253 / 8492) : ℂ) * ζ ^ 26 - ((1611 / 8492) : ℂ) * ζ ^ 28 + ((109 / 8492) : ℂ) * ζ ^ 29 - ((4253 / 8492) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_2_0 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        2 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((77 / 386) : ℂ) - ((2429 / 1544) : ℂ) * ζ ^ 3 + ((77 / 386) : ℂ) * ζ ^ 4 - ((7 / 386) : ℂ) * ζ ^ 5 + ((243 / 1544) : ℂ) * ζ ^ 6 - ((55 / 1544) : ℂ) * ζ ^ 8 + ((7 / 386) : ℂ) * ζ ^ 9 + ((231 / 386) : ℂ) * ζ ^ 10 + ((619 / 1544) : ℂ) * ζ ^ 13 - ((681 / 1544) : ℂ) * ζ ^ 14 - ((53 / 772) : ℂ) * ζ ^ 15 - ((1051 / 1544) : ℂ) * ζ ^ 18 + ((53 / 772) : ℂ) * ζ ^ 19 - ((901 / 1544) : ℂ) * ζ ^ 20 - ((243 / 1544) : ℂ) * ζ ^ 22 + ((1333 / 1544) : ℂ) * ζ ^ 23 + ((901 / 1544) : ℂ) * ζ ^ 24 + ((465 / 772) : ℂ) * ζ ^ 25 - ((243 / 1544) : ℂ) * ζ ^ 26 - ((63 / 772) : ℂ) * ζ ^ 28 - ((465 / 772) : ℂ) * ζ ^ 29 + ((243 / 1544) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_2_1 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        2 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((45 / 193) : ℂ) - ((103 / 2316) : ℂ) * ζ ^ 3 + ((45 / 193) : ℂ) * ζ ^ 4 + ((239 / 386) : ℂ) * ζ ^ 5 - ((313 / 2316) : ℂ) * ζ ^ 6 - ((1333 / 1158) : ℂ) * ζ ^ 8 - ((239 / 386) : ℂ) * ζ ^ 9 + ((55 / 1158) : ℂ) * ζ ^ 10 + ((425 / 579) : ℂ) * ζ ^ 13 - ((141 / 772) : ℂ) * ζ ^ 14 - ((547 / 1158) : ℂ) * ζ ^ 15 - ((482 / 579) : ℂ) * ζ ^ 18 + ((547 / 1158) : ℂ) * ζ ^ 19 - ((1045 / 1158) : ℂ) * ζ ^ 20 + ((313 / 2316) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 23 + ((1045 / 1158) : ℂ) * ζ ^ 24 + ((397 / 1158) : ℂ) * ζ ^ 25 + ((313 / 2316) : ℂ) * ζ ^ 26 - ((526 / 579) : ℂ) * ζ ^ 28 - ((397 / 1158) : ℂ) * ζ ^ 29 - ((313 / 2316) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_2_2 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        2 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((703 / 386) : ℂ) - ((89 / 1544) : ℂ) * ζ ^ 3 + ((703 / 386) : ℂ) * ζ ^ 4 + ((89 / 193) : ℂ) * ζ ^ 5 + ((141 / 1544) : ℂ) * ζ ^ 6 - ((2181 / 1544) : ℂ) * ζ ^ 8 - ((89 / 193) : ℂ) * ζ ^ 9 + ((553 / 772) : ℂ) * ζ ^ 10 + ((1045 / 1544) : ℂ) * ζ ^ 13 - ((5 / 8) : ℂ) * ζ ^ 14 + ((9 / 386) : ℂ) * ζ ^ 15 - ((265 / 1544) : ℂ) * ζ ^ 18 - ((9 / 386) : ℂ) * ζ ^ 19 - ((2397 / 1544) : ℂ) * ζ ^ 20 - ((141 / 1544) : ℂ) * ζ ^ 22 - ((127 / 1544) : ℂ) * ζ ^ 23 + ((2397 / 1544) : ℂ) * ζ ^ 24 - ((603 / 772) : ℂ) * ζ ^ 25 - ((141 / 1544) : ℂ) * ζ ^ 26 - ((63 / 772) : ℂ) * ζ ^ 28 + ((603 / 772) : ℂ) * ζ ^ 29 + ((141 / 1544) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_2_3 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        2 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((1937 / 772) : ℂ) + ((15 / 8) : ℂ) * ζ ^ 3 + ((1937 / 772) : ℂ) * ζ ^ 4 + ((1811 / 1544) : ℂ) * ζ ^ 5 - ((827 / 772) : ℂ) * ζ ^ 6 - ((909 / 386) : ℂ) * ζ ^ 8 - ((1811 / 1544) : ℂ) * ζ ^ 9 - ((249 / 772) : ℂ) * ζ ^ 10 + ((1529 / 1544) : ℂ) * ζ ^ 13 - ((289 / 386) : ℂ) * ζ ^ 14 - ((1303 / 1544) : ℂ) * ζ ^ 15 + ((367 / 772) : ℂ) * ζ ^ 18 + ((1303 / 1544) : ℂ) * ζ ^ 19 + ((1055 / 772) : ℂ) * ζ ^ 20 + ((827 / 772) : ℂ) * ζ ^ 22 - ((497 / 1544) : ℂ) * ζ ^ 23 - ((1055 / 772) : ℂ) * ζ ^ 24 + ((185 / 1544) : ℂ) * ζ ^ 25 + ((827 / 772) : ℂ) * ζ ^ 26 + ((561 / 772) : ℂ) * ζ ^ 28 - ((185 / 1544) : ℂ) * ζ ^ 29 - ((827 / 772) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_2_4 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        2 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((861 / 8492) : ℂ) - ((12069 / 16984) : ℂ) * ζ ^ 3 + ((861 / 8492) : ℂ) * ζ ^ 4 + ((8281 / 4246) : ℂ) * ζ ^ 5 + ((2807 / 16984) : ℂ) * ζ ^ 6 - ((5763 / 16984) : ℂ) * ζ ^ 8 - ((8281 / 4246) : ℂ) * ζ ^ 9 + ((1847 / 4246) : ℂ) * ζ ^ 10 + ((21589 / 16984) : ℂ) * ζ ^ 13 - ((4581 / 16984) : ℂ) * ζ ^ 14 - ((674 / 2123) : ℂ) * ζ ^ 15 - ((33 / 1544) : ℂ) * ζ ^ 18 + ((674 / 2123) : ℂ) * ζ ^ 19 + ((1107 / 16984) : ℂ) * ζ ^ 20 - ((2807 / 16984) : ℂ) * ζ ^ 22 - ((5487 / 16984) : ℂ) * ζ ^ 23 - ((1107 / 16984) : ℂ) * ζ ^ 24 + ((1087 / 8492) : ℂ) * ζ ^ 25 - ((2807 / 16984) : ℂ) * ζ ^ 26 + ((1429 / 8492) : ℂ) * ζ ^ 28 - ((1087 / 8492) : ℂ) * ζ ^ 29 + ((2807 / 16984) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_2_5 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        2 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((2867 / 4246) : ℂ) + ((3213 / 4246) : ℂ) * ζ ^ 3 - ((2867 / 4246) : ℂ) * ζ ^ 4 + ((269 / 386) : ℂ) * ζ ^ 5 - ((6183 / 8492) : ℂ) * ζ ^ 6 + ((6697 / 8492) : ℂ) * ζ ^ 8 - ((269 / 386) : ℂ) * ζ ^ 9 - ((984 / 2123) : ℂ) * ζ ^ 10 + ((4203 / 8492) : ℂ) * ζ ^ 13 - ((2247 / 8492) : ℂ) * ζ ^ 14 - ((1035 / 4246) : ℂ) * ζ ^ 15 - ((375 / 8492) : ℂ) * ζ ^ 18 + ((1035 / 4246) : ℂ) * ζ ^ 19 + ((1983 / 2123) : ℂ) * ζ ^ 20 + ((6183 / 8492) : ℂ) * ζ ^ 22 - ((45 / 193) : ℂ) * ζ ^ 23 - ((1983 / 2123) : ℂ) * ζ ^ 24 + ((214 / 2123) : ℂ) * ζ ^ 25 + ((6183 / 8492) : ℂ) * ζ ^ 26 - ((2383 / 8492) : ℂ) * ζ ^ 28 - ((214 / 2123) : ℂ) * ζ ^ 29 - ((6183 / 8492) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_3_0 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        3 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((681 / 386) : ℂ) + ((3937 / 1544) : ℂ) * ζ ^ 3 - ((681 / 386) : ℂ) * ζ ^ 4 + ((2125 / 1544) : ℂ) * ζ ^ 5 - ((383 / 193) : ℂ) * ζ ^ 6 + ((643 / 772) : ℂ) * ζ ^ 8 - ((2125 / 1544) : ℂ) * ζ ^ 9 - ((346 / 193) : ℂ) * ζ ^ 10 - ((1023 / 1544) : ℂ) * ζ ^ 13 - ((37 / 193) : ℂ) * ζ ^ 14 - ((599 / 1544) : ℂ) * ζ ^ 15 + ((1809 / 772) : ℂ) * ζ ^ 18 + ((599 / 1544) : ℂ) * ζ ^ 19 + ((27 / 193) : ℂ) * ζ ^ 20 + ((383 / 193) : ℂ) * ζ ^ 22 - ((2039 / 1544) : ℂ) * ζ ^ 23 - ((27 / 193) : ℂ) * ζ ^ 24 - ((2217 / 1544) : ℂ) * ζ ^ 25 + ((383 / 193) : ℂ) * ζ ^ 26 - ((671 / 772) : ℂ) * ζ ^ 28 + ((2217 / 1544) : ℂ) * ζ ^ 29 - ((383 / 193) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_3_1 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        3 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((647 / 772) : ℂ) - ((613 / 2316) : ℂ) * ζ ^ 3 - ((647 / 772) : ℂ) * ζ ^ 4 + ((707 / 1158) : ℂ) * ζ ^ 5 - ((299 / 1158) : ℂ) * ζ ^ 6 + ((4657 / 2316) : ℂ) * ζ ^ 8 - ((707 / 1158) : ℂ) * ζ ^ 9 - ((793 / 772) : ℂ) * ζ ^ 10 - ((1715 / 1158) : ℂ) * ζ ^ 13 + ((1781 / 2316) : ℂ) * ζ ^ 14 + ((826 / 579) : ℂ) * ζ ^ 15 + ((703 / 1158) : ℂ) * ζ ^ 18 - ((826 / 579) : ℂ) * ζ ^ 19 + ((341 / 193) : ℂ) * ζ ^ 20 + ((299 / 1158) : ℂ) * ζ ^ 22 - ((5 / 12) : ℂ) * ζ ^ 23 - ((341 / 193) : ℂ) * ζ ^ 24 - ((30 / 193) : ℂ) * ζ ^ 25 + ((299 / 1158) : ℂ) * ζ ^ 26 + ((2143 / 1158) : ℂ) * ζ ^ 28 + ((30 / 193) : ℂ) * ζ ^ 29 - ((299 / 1158) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_3_2 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        3 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((1029 / 386) : ℂ) - ((1579 / 1544) : ℂ) * ζ ^ 3 - ((1029 / 386) : ℂ) * ζ ^ 4 + ((1245 / 1544) : ℂ) * ζ ^ 5 - ((715 / 772) : ℂ) * ζ ^ 6 + ((711 / 386) : ℂ) * ζ ^ 8 - ((1245 / 1544) : ℂ) * ζ ^ 9 - ((647 / 386) : ℂ) * ζ ^ 10 - ((695 / 1544) : ℂ) * ζ ^ 13 + ((3 / 4) : ℂ) * ζ ^ 14 + ((25 / 1544) : ℂ) * ζ ^ 15 + ((277 / 386) : ℂ) * ζ ^ 18 - ((25 / 1544) : ℂ) * ζ ^ 19 + ((192 / 193) : ℂ) * ζ ^ 20 + ((715 / 772) : ℂ) * ζ ^ 22 - ((501 / 1544) : ℂ) * ζ ^ 23 - ((192 / 193) : ℂ) * ζ ^ 24 + ((803 / 1544) : ℂ) * ζ ^ 25 + ((715 / 772) : ℂ) * ζ ^ 26 - ((671 / 772) : ℂ) * ζ ^ 28 - ((803 / 1544) : ℂ) * ζ ^ 29 - ((715 / 772) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_3_3 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        3 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((941 / 193) : ℂ) - ((11 / 2) : ℂ) * ζ ^ 3 - ((941 / 193) : ℂ) * ζ ^ 4 + ((3579 / 1544) : ℂ) * ζ ^ 5 + ((3151 / 1544) : ℂ) * ζ ^ 6 + ((6353 / 1544) : ℂ) * ζ ^ 8 - ((3579 / 1544) : ℂ) * ζ ^ 9 + ((197 / 772) : ℂ) * ζ ^ 10 - ((351 / 772) : ℂ) * ζ ^ 13 + ((2757 / 1544) : ℂ) * ζ ^ 14 + ((4215 / 1544) : ℂ) * ζ ^ 15 + ((113 / 1544) : ℂ) * ζ ^ 18 - ((4215 / 1544) : ℂ) * ζ ^ 19 - ((4121 / 1544) : ℂ) * ζ ^ 20 - ((3151 / 1544) : ℂ) * ζ ^ 22 + ((1031 / 772) : ℂ) * ζ ^ 23 + ((4121 / 1544) : ℂ) * ζ ^ 24 - ((3887 / 1544) : ℂ) * ζ ^ 25 - ((3151 / 1544) : ℂ) * ζ ^ 26 - ((537 / 386) : ℂ) * ζ ^ 28 + ((3887 / 1544) : ℂ) * ζ ^ 29 + ((3151 / 1544) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_3_4 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        3 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((13861 / 8492) : ℂ) + ((11739 / 16984) : ℂ) * ζ ^ 3 - ((13861 / 8492) : ℂ) * ζ ^ 4 - ((38843 / 16984) : ℂ) * ζ ^ 5 - ((1377 / 4246) : ℂ) * ζ ^ 6 + ((21553 / 8492) : ℂ) * ζ ^ 8 + ((38843 / 16984) : ℂ) * ζ ^ 9 - ((7653 / 8492) : ℂ) * ζ ^ 10 - ((31333 / 16984) : ℂ) * ζ ^ 13 + ((4899 / 8492) : ℂ) * ζ ^ 14 + ((2539 / 1544) : ℂ) * ζ ^ 15 - ((4171 / 8492) : ℂ) * ζ ^ 18 - ((2539 / 1544) : ℂ) * ζ ^ 19 + ((1236 / 2123) : ℂ) * ζ ^ 20 + ((1377 / 4246) : ℂ) * ζ ^ 22 + ((16921 / 16984) : ℂ) * ζ ^ 23 - ((1236 / 2123) : ℂ) * ζ ^ 24 - ((6221 / 16984) : ℂ) * ζ ^ 25 + ((1377 / 4246) : ℂ) * ζ ^ 26 - ((943 / 8492) : ℂ) * ζ ^ 28 + ((6221 / 16984) : ℂ) * ζ ^ 29 - ((1377 / 4246) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_3_5 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        3 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((5979 / 8492) : ℂ) + ((1025 / 4246) : ℂ) * ζ ^ 3 + ((5979 / 8492) : ℂ) * ζ ^ 4 - ((3235 / 8492) : ℂ) * ζ ^ 5 + ((10519 / 8492) : ℂ) * ζ ^ 6 - ((8543 / 8492) : ℂ) * ζ ^ 8 + ((3235 / 8492) : ℂ) * ζ ^ 9 + ((7367 / 8492) : ℂ) * ζ ^ 10 - ((11 / 772) : ℂ) * ζ ^ 13 + ((788 / 2123) : ℂ) * ζ ^ 14 + ((7923 / 8492) : ℂ) * ζ ^ 15 + ((727 / 2123) : ℂ) * ζ ^ 18 - ((7923 / 8492) : ℂ) * ζ ^ 19 - ((12505 / 8492) : ℂ) * ζ ^ 20 - ((10519 / 8492) : ℂ) * ζ ^ 22 + ((1725 / 4246) : ℂ) * ζ ^ 23 + ((12505 / 8492) : ℂ) * ζ ^ 24 - ((6761 / 8492) : ℂ) * ζ ^ 25 - ((10519 / 8492) : ℂ) * ζ ^ 26 + ((4623 / 8492) : ℂ) * ζ ^ 28 + ((6761 / 8492) : ℂ) * ζ ^ 29 + ((10519 / 8492) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_4_0 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        4 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((425 / 386) : ℂ) + ((3441 / 1544) : ℂ) * ζ ^ 3 - ((425 / 386) : ℂ) * ζ ^ 4 - ((7 / 193) : ℂ) * ζ ^ 5 - ((93 / 1544) : ℂ) * ζ ^ 6 + ((1241 / 1544) : ℂ) * ζ ^ 8 + ((7 / 193) : ℂ) * ζ ^ 9 - ((427 / 772) : ℂ) * ζ ^ 10 - ((1271 / 1544) : ℂ) * ζ ^ 13 + ((761 / 1544) : ℂ) * ζ ^ 14 - ((53 / 386) : ℂ) * ζ ^ 15 - ((1137 / 1544) : ℂ) * ζ ^ 18 + ((53 / 386) : ℂ) * ζ ^ 19 + ((321 / 1544) : ℂ) * ζ ^ 20 + ((93 / 1544) : ℂ) * ζ ^ 22 - ((2159 / 1544) : ℂ) * ζ ^ 23 - ((321 / 1544) : ℂ) * ζ ^ 24 - ((807 / 772) : ℂ) * ζ ^ 25 + ((93 / 1544) : ℂ) * ζ ^ 26 + ((65 / 193) : ℂ) * ζ ^ 28 + ((807 / 772) : ℂ) * ζ ^ 29 - ((93 / 1544) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_4_1 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        4 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((103 / 193) : ℂ) - ((133 / 772) : ℂ) * ζ ^ 3 - ((103 / 193) : ℂ) * ζ ^ 4 - ((689 / 1158) : ℂ) * ζ ^ 5 - ((47 / 2316) : ℂ) * ζ ^ 6 + ((205 / 386) : ℂ) * ζ ^ 8 + ((689 / 1158) : ℂ) * ζ ^ 9 - ((469 / 1158) : ℂ) * ζ ^ 10 - ((1195 / 1158) : ℂ) * ζ ^ 13 + ((297 / 772) : ℂ) * ζ ^ 14 - ((161 / 579) : ℂ) * ζ ^ 15 + ((581 / 1158) : ℂ) * ζ ^ 18 + ((161 / 579) : ℂ) * ζ ^ 19 + ((102 / 193) : ℂ) * ζ ^ 20 + ((47 / 2316) : ℂ) * ζ ^ 22 + ((1 / 12) : ℂ) * ζ ^ 23 - ((102 / 193) : ℂ) * ζ ^ 24 - ((57 / 386) : ℂ) * ζ ^ 25 + ((47 / 2316) : ℂ) * ζ ^ 26 + ((164 / 193) : ℂ) * ζ ^ 28 + ((57 / 386) : ℂ) * ζ ^ 29 - ((47 / 2316) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_4_2 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        4 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((717 / 386) : ℂ) + ((1173 / 1544) : ℂ) * ζ ^ 3 - ((717 / 386) : ℂ) * ζ ^ 4 - ((15 / 193) : ℂ) * ζ ^ 5 + ((89 / 1544) : ℂ) * ζ ^ 6 + ((2007 / 1544) : ℂ) * ζ ^ 8 + ((15 / 193) : ℂ) * ζ ^ 9 - ((206 / 193) : ℂ) * ζ ^ 10 - ((805 / 1544) : ℂ) * ζ ^ 13 + ((9 / 8) : ℂ) * ζ ^ 14 - ((543 / 772) : ℂ) * ζ ^ 15 - ((723 / 1544) : ℂ) * ζ ^ 18 + ((543 / 772) : ℂ) * ζ ^ 19 + ((1189 / 1544) : ℂ) * ζ ^ 20 - ((89 / 1544) : ℂ) * ζ ^ 22 - ((447 / 1544) : ℂ) * ζ ^ 23 - ((1189 / 1544) : ℂ) * ζ ^ 24 + ((145 / 772) : ℂ) * ζ ^ 25 - ((89 / 1544) : ℂ) * ζ ^ 26 + ((65 / 193) : ℂ) * ζ ^ 28 - ((145 / 772) : ℂ) * ζ ^ 29 + ((89 / 1544) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_4_3 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        4 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((2109 / 772) : ℂ) + ((7 / 8) : ℂ) * ζ ^ 3 - ((2109 / 772) : ℂ) * ζ ^ 4 - ((1975 / 1544) : ℂ) * ζ ^ 5 + ((331 / 386) : ℂ) * ζ ^ 6 + ((1463 / 386) : ℂ) * ζ ^ 8 + ((1975 / 1544) : ℂ) * ζ ^ 9 + ((81 / 772) : ℂ) * ζ ^ 10 + ((163 / 1544) : ℂ) * ζ ^ 13 + ((581 / 772) : ℂ) * ζ ^ 14 + ((289 / 1544) : ℂ) * ζ ^ 15 - ((617 / 772) : ℂ) * ζ ^ 18 - ((289 / 1544) : ℂ) * ζ ^ 19 - ((785 / 772) : ℂ) * ζ ^ 20 - ((331 / 386) : ℂ) * ζ ^ 22 - ((801 / 1544) : ℂ) * ζ ^ 23 + ((785 / 772) : ℂ) * ζ ^ 24 + ((177 / 1544) : ℂ) * ζ ^ 25 - ((331 / 386) : ℂ) * ζ ^ 26 - ((615 / 772) : ℂ) * ζ ^ 28 - ((177 / 1544) : ℂ) * ζ ^ 29 + ((331 / 386) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_4_4 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        4 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((757 / 8492) : ℂ) + ((14269 / 16984) : ℂ) * ζ ^ 3 + ((757 / 8492) : ℂ) * ζ ^ 4 - ((1755 / 2123) : ℂ) * ζ ^ 5 - ((2685 / 16984) : ℂ) * ζ ^ 6 - ((2455 / 16984) : ℂ) * ζ ^ 8 + ((1755 / 2123) : ℂ) * ζ ^ 9 + ((233 / 772) : ℂ) * ζ ^ 10 - ((9125 / 16984) : ℂ) * ζ ^ 13 - ((7811 / 16984) : ℂ) * ζ ^ 14 + ((591 / 8492) : ℂ) * ζ ^ 15 + ((12591 / 16984) : ℂ) * ζ ^ 18 - ((591 / 8492) : ℂ) * ζ ^ 19 - ((3383 / 16984) : ℂ) * ζ ^ 20 + ((2685 / 16984) : ℂ) * ζ ^ 22 + ((5817 / 16984) : ℂ) * ζ ^ 23 + ((3383 / 16984) : ℂ) * ζ ^ 24 - ((1107 / 8492) : ℂ) * ζ ^ 25 + ((2685 / 16984) : ℂ) * ζ ^ 26 - ((347 / 2123) : ℂ) * ζ ^ 28 + ((1107 / 8492) : ℂ) * ζ ^ 29 - ((2685 / 16984) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_4_5 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        4 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((137 / 4246) : ℂ) - ((261 / 2123) : ℂ) * ζ ^ 3 - ((137 / 4246) : ℂ) * ζ ^ 4 - ((1866 / 2123) : ℂ) * ζ ^ 5 + ((3653 / 8492) : ℂ) * ζ ^ 6 - ((695 / 8492) : ℂ) * ζ ^ 8 + ((1866 / 2123) : ℂ) * ζ ^ 9 - ((21 / 193) : ℂ) * ζ ^ 10 - ((6069 / 8492) : ℂ) * ζ ^ 13 + ((4577 / 8492) : ℂ) * ζ ^ 14 - ((719 / 4246) : ℂ) * ζ ^ 15 - ((4417 / 8492) : ℂ) * ζ ^ 18 + ((719 / 4246) : ℂ) * ζ ^ 19 - ((1438 / 2123) : ℂ) * ζ ^ 20 - ((3653 / 8492) : ℂ) * ζ ^ 22 + ((13 / 386) : ℂ) * ζ ^ 23 + ((1438 / 2123) : ℂ) * ζ ^ 24 + ((1049 / 4246) : ℂ) * ζ ^ 25 - ((3653 / 8492) : ℂ) * ζ ^ 26 + ((2375 / 8492) : ℂ) * ζ ^ 28 - ((1049 / 4246) : ℂ) * ζ ^ 29 + ((3653 / 8492) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_5_0 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        5 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((1015 / 772) : ℂ) - ((92 / 193) : ℂ) * ζ ^ 3 + ((1015 / 772) : ℂ) * ζ ^ 4 - ((669 / 386) : ℂ) * ζ ^ 5 + ((425 / 193) : ℂ) * ζ ^ 6 - ((905 / 772) : ℂ) * ζ ^ 8 + ((669 / 386) : ℂ) * ζ ^ 9 + ((1501 / 772) : ℂ) * ζ ^ 10 + ((9 / 772) : ℂ) * ζ ^ 13 + ((199 / 772) : ℂ) * ζ ^ 14 + ((321 / 386) : ℂ) * ζ ^ 15 - ((497 / 386) : ℂ) * ζ ^ 18 - ((321 / 386) : ℂ) * ζ ^ 19 + ((158 / 193) : ℂ) * ζ ^ 20 - ((425 / 193) : ℂ) * ζ ^ 22 + ((353 / 772) : ℂ) * ζ ^ 23 - ((158 / 193) : ℂ) * ζ ^ 24 + ((547 / 772) : ℂ) * ζ ^ 25 - ((425 / 193) : ℂ) * ζ ^ 26 + ((367 / 386) : ℂ) * ζ ^ 28 - ((547 / 772) : ℂ) * ζ ^ 29 + ((425 / 193) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_5_1 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        5 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((25 / 1158) : ℂ) + ((55 / 386) : ℂ) * ζ ^ 3 + ((25 / 1158) : ℂ) * ζ ^ 4 - ((905 / 579) : ℂ) * ζ ^ 5 - ((9 / 386) : ℂ) * ζ ^ 6 - ((353 / 579) : ℂ) * ζ ^ 8 + ((905 / 579) : ℂ) * ζ ^ 9 + ((845 / 1158) : ℂ) * ζ ^ 10 - ((50 / 579) : ℂ) * ζ ^ 13 - ((436 / 579) : ℂ) * ζ ^ 14 - ((152 / 193) : ℂ) * ζ ^ 15 + ((34 / 579) : ℂ) * ζ ^ 18 + ((152 / 193) : ℂ) * ζ ^ 19 - ((404 / 579) : ℂ) * ζ ^ 20 + ((9 / 386) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 23 + ((404 / 579) : ℂ) * ζ ^ 24 - ((398 / 579) : ℂ) * ζ ^ 25 + ((9 / 386) : ℂ) * ζ ^ 26 - ((1477 / 1158) : ℂ) * ζ ^ 28 + ((398 / 579) : ℂ) * ζ ^ 29 - ((9 / 386) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_5_2 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        5 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((845 / 772) : ℂ) + ((803 / 386) : ℂ) * ζ ^ 3 + ((845 / 772) : ℂ) * ζ ^ 4 - ((441 / 386) : ℂ) * ζ ^ 5 + ((137 / 193) : ℂ) * ζ ^ 6 - ((1007 / 772) : ℂ) * ζ ^ 8 + ((441 / 386) : ℂ) * ζ ^ 9 + ((741 / 772) : ℂ) * ζ ^ 10 - ((561 / 772) : ℂ) * ζ ^ 13 - ((1 / 4) : ℂ) * ζ ^ 14 + ((33 / 386) : ℂ) * ζ ^ 15 - ((33 / 193) : ℂ) * ζ ^ 18 - ((33 / 386) : ℂ) * ζ ^ 19 - ((13 / 193) : ℂ) * ζ ^ 20 - ((137 / 193) : ℂ) * ζ ^ 22 + ((121 / 772) : ℂ) * ζ ^ 23 + ((13 / 193) : ℂ) * ζ ^ 24 - ((667 / 772) : ℂ) * ζ ^ 25 - ((137 / 193) : ℂ) * ζ ^ 26 + ((367 / 386) : ℂ) * ζ ^ 28 + ((667 / 772) : ℂ) * ζ ^ 29 + ((137 / 193) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_5_3 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        5 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((505 / 193) : ℂ) + ((19 / 4) : ℂ) * ζ ^ 3 + ((505 / 193) : ℂ) * ζ ^ 4 - ((3853 / 772) : ℂ) * ζ ^ 5 - ((163 / 193) : ℂ) * ζ ^ 6 - ((1069 / 772) : ℂ) * ζ ^ 8 + ((3853 / 772) : ℂ) * ζ ^ 9 + ((245 / 772) : ℂ) * ζ ^ 10 - ((255 / 386) : ℂ) * ζ ^ 13 - ((897 / 772) : ℂ) * ζ ^ 14 - ((921 / 386) : ℂ) * ζ ^ 15 - ((67 / 386) : ℂ) * ζ ^ 18 + ((921 / 386) : ℂ) * ζ ^ 19 + ((523 / 772) : ℂ) * ζ ^ 20 + ((163 / 193) : ℂ) * ζ ^ 22 - ((493 / 772) : ℂ) * ζ ^ 23 - ((523 / 772) : ℂ) * ζ ^ 24 + ((511 / 193) : ℂ) * ζ ^ 25 + ((163 / 193) : ℂ) * ζ ^ 26 + ((513 / 772) : ℂ) * ζ ^ 28 - ((511 / 193) : ℂ) * ζ ^ 29 - ((163 / 193) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_5_4 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        5 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((12421 / 8492) : ℂ) + ((2495 / 4246) : ℂ) * ζ ^ 3 + ((12421 / 8492) : ℂ) * ζ ^ 4 + ((4759 / 4246) : ℂ) * ζ ^ 5 + ((241 / 4246) : ℂ) * ζ ^ 6 - ((17417 / 8492) : ℂ) * ζ ^ 8 - ((4759 / 4246) : ℂ) * ζ ^ 9 + ((11679 / 8492) : ℂ) * ζ ^ 10 + ((8153 / 8492) : ℂ) * ζ ^ 13 - ((11197 / 8492) : ℂ) * ζ ^ 14 - ((2691 / 4246) : ℂ) * ζ ^ 15 + ((2608 / 2123) : ℂ) * ζ ^ 18 + ((2691 / 4246) : ℂ) * ζ ^ 19 - ((1253 / 4246) : ℂ) * ζ ^ 20 - ((241 / 4246) : ℂ) * ζ ^ 22 - ((1085 / 8492) : ℂ) * ζ ^ 23 + ((1253 / 4246) : ℂ) * ζ ^ 24 + ((1541 / 8492) : ℂ) * ζ ^ 25 - ((241 / 4246) : ℂ) * ζ ^ 26 + ((168 / 2123) : ℂ) * ζ ^ 28 - ((1541 / 8492) : ℂ) * ζ ^ 29 + ((241 / 4246) : ℂ) * ζ ^ 30)
private theorem row13_eigenbasisInverse_mul_5_5 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis)
        5 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((991 / 4246) : ℂ) - ((1926 / 2123) : ℂ) * ζ ^ 3 - ((991 / 4246) : ℂ) * ζ ^ 4 + ((632 / 2123) : ℂ) * ζ ^ 5 - ((3133 / 4246) : ℂ) * ζ ^ 6 + ((944 / 2123) : ℂ) * ζ ^ 8 - ((632 / 2123) : ℂ) * ζ ^ 9 + ((1217 / 2123) : ℂ) * ζ ^ 10 + ((813 / 2123) : ℂ) * ζ ^ 13 - ((5567 / 4246) : ℂ) * ζ ^ 14 - ((1608 / 2123) : ℂ) * ζ ^ 15 + ((2111 / 4246) : ℂ) * ζ ^ 18 + ((1608 / 2123) : ℂ) * ζ ^ 19 + ((709 / 2123) : ℂ) * ζ ^ 20 + ((3133 / 4246) : ℂ) * ζ ^ 22 - ((271 / 2123) : ℂ) * ζ ^ 23 - ((709 / 2123) : ℂ) * ζ ^ 24 + ((3435 / 4246) : ℂ) * ζ ^ 25 + ((3133 / 4246) : ℂ) * ζ ^ 26 - ((753 / 2123) : ℂ) * ζ ^ 28 - ((3435 / 4246) : ℂ) * ζ ^ 29 - ((3133 / 4246) : ℂ) * ζ ^ 30)
/-- The displayed row 13 matrix is a left inverse of its
eigenbasis. -/
theorem alternatingSixAmbientRow13EigenbasisInverse_mul :
    alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixAmbientRow13Eigenbasis =
      1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row13_eigenbasisInverse_mul_0_0
  · exact row13_eigenbasisInverse_mul_0_1
  · exact row13_eigenbasisInverse_mul_0_2
  · exact row13_eigenbasisInverse_mul_0_3
  · exact row13_eigenbasisInverse_mul_0_4
  · exact row13_eigenbasisInverse_mul_0_5
  · exact row13_eigenbasisInverse_mul_1_0
  · exact row13_eigenbasisInverse_mul_1_1
  · exact row13_eigenbasisInverse_mul_1_2
  · exact row13_eigenbasisInverse_mul_1_3
  · exact row13_eigenbasisInverse_mul_1_4
  · exact row13_eigenbasisInverse_mul_1_5
  · exact row13_eigenbasisInverse_mul_2_0
  · exact row13_eigenbasisInverse_mul_2_1
  · exact row13_eigenbasisInverse_mul_2_2
  · exact row13_eigenbasisInverse_mul_2_3
  · exact row13_eigenbasisInverse_mul_2_4
  · exact row13_eigenbasisInverse_mul_2_5
  · exact row13_eigenbasisInverse_mul_3_0
  · exact row13_eigenbasisInverse_mul_3_1
  · exact row13_eigenbasisInverse_mul_3_2
  · exact row13_eigenbasisInverse_mul_3_3
  · exact row13_eigenbasisInverse_mul_3_4
  · exact row13_eigenbasisInverse_mul_3_5
  · exact row13_eigenbasisInverse_mul_4_0
  · exact row13_eigenbasisInverse_mul_4_1
  · exact row13_eigenbasisInverse_mul_4_2
  · exact row13_eigenbasisInverse_mul_4_3
  · exact row13_eigenbasisInverse_mul_4_4
  · exact row13_eigenbasisInverse_mul_4_5
  · exact row13_eigenbasisInverse_mul_5_0
  · exact row13_eigenbasisInverse_mul_5_1
  · exact row13_eigenbasisInverse_mul_5_2
  · exact row13_eigenbasisInverse_mul_5_3
  · exact row13_eigenbasisInverse_mul_5_4
  · exact row13_eigenbasisInverse_mul_5_5

/-- The displayed row 13 inverse is also a right inverse. -/
theorem alternatingSixAmbientRow13Eigenbasis_mul_inverse :
    alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixAmbientRow13EigenbasisInverse_mul


private theorem row13_generatorB_mul_eigenbasis_0_0 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        0 0 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        0 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((314 / 193) : ℂ) - ((847 / 386) : ℂ) * ζ ^ 3 + ((314 / 193) : ℂ) * ζ ^ 4 - ((204 / 193) : ℂ) * ζ ^ 5 + ((1087 / 386) : ℂ) * ζ ^ 6 + ((261 / 193) : ℂ) * ζ ^ 8 + ((204 / 193) : ℂ) * ζ ^ 9 + ((1305 / 386) : ℂ) * ζ ^ 10 + ((319 / 193) : ℂ) * ζ ^ 13 - ((109 / 193) : ℂ) * ζ ^ 14 + ((799 / 386) : ℂ) * ζ ^ 15 - ((619 / 386) : ℂ) * ζ ^ 18 - ((799 / 386) : ℂ) * ζ ^ 19 + ((356 / 193) : ℂ) * ζ ^ 20 - ((1087 / 386) : ℂ) * ζ ^ 22 + ((503 / 193) : ℂ) * ζ ^ 23 - ((356 / 193) : ℂ) * ζ ^ 24 + ((841 / 386) : ℂ) * ζ ^ 25 - ((1087 / 386) : ℂ) * ζ ^ 26 + ((240 / 193) : ℂ) * ζ ^ 28 - ((841 / 386) : ℂ) * ζ ^ 29 + ((1087 / 386) : ℂ) * ζ ^ 30)
private theorem row13_generatorB_mul_eigenbasis_0_1 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        0 1 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        0 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((169 / 193) : ℂ) + ((374 / 579) : ℂ) * ζ ^ 3 + ((169 / 193) : ℂ) * ζ ^ 4 - ((886 / 579) : ℂ) * ζ ^ 5 + ((134 / 193) : ℂ) * ζ ^ 6 - ((1433 / 579) : ℂ) * ζ ^ 8 + ((886 / 579) : ℂ) * ζ ^ 9 + ((231 / 193) : ℂ) * ζ ^ 10 + ((289 / 193) : ℂ) * ζ ^ 13 - ((97 / 193) : ℂ) * ζ ^ 14 - ((406 / 193) : ℂ) * ζ ^ 15 - ((991 / 579) : ℂ) * ζ ^ 18 + ((406 / 193) : ℂ) * ζ ^ 19 - ((143 / 193) : ℂ) * ζ ^ 20 - ((134 / 193) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 23 + ((143 / 193) : ℂ) * ζ ^ 24 + ((162 / 193) : ℂ) * ζ ^ 25 - ((134 / 193) : ℂ) * ζ ^ 26 - ((826 / 579) : ℂ) * ζ ^ 28 - ((162 / 193) : ℂ) * ζ ^ 29 + ((134 / 193) : ℂ) * ζ ^ 30)
private theorem row13_generatorB_mul_eigenbasis_0_2 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        0 2 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        0 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((443 / 193) : ℂ) + ((385 / 386) : ℂ) * ζ ^ 3 + ((443 / 193) : ℂ) * ζ ^ 4 - ((189 / 193) : ℂ) * ζ ^ 5 + ((483 / 386) : ℂ) * ζ ^ 6 - ((395 / 193) : ℂ) * ζ ^ 8 + ((189 / 193) : ℂ) * ζ ^ 9 + ((869 / 386) : ℂ) * ζ ^ 10 + ((59 / 193) : ℂ) * ζ ^ 13 - ζ ^ 14 + ((152 / 193) : ℂ) * ζ ^ 15 - ((415 / 386) : ℂ) * ζ ^ 18 - ((152 / 193) : ℂ) * ζ ^ 19 - ((105 / 386) : ℂ) * ζ ^ 20 - ((483 / 386) : ℂ) * ζ ^ 22 + ((493 / 386) : ℂ) * ζ ^ 23 + ((105 / 386) : ℂ) * ζ ^ 24 - ((341 / 386) : ℂ) * ζ ^ 25 - ((483 / 386) : ℂ) * ζ ^ 26 + ((673 / 386) : ℂ) * ζ ^ 28 + ((341 / 386) : ℂ) * ζ ^ 29 + ((338 / 193) : ℂ) * ζ ^ 30 - ζ ^ 33 - ((1 / 2) : ℂ) * ζ ^ 34 + ((1 / 2) : ℂ) * ζ ^ 35 + ((1 / 2) : ℂ) * ζ ^ 38 - ((1 / 2) : ℂ) * ζ ^ 39 + ζ ^ 40 + ((1 / 2) : ℂ) * ζ ^ 43 - ζ ^ 44)
private theorem row13_generatorB_mul_eigenbasis_0_3 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        0 3 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        0 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((1941 / 386) : ℂ) + (7 : ℂ) * ζ ^ 3 + ((1941 / 386) : ℂ) * ζ ^ 4 - ((1155 / 386) : ℂ) * ζ ^ 5 - ((1079 / 386) : ℂ) * ζ ^ 6 - ((1947 / 386) : ℂ) * ζ ^ 8 + ((1155 / 386) : ℂ) * ζ ^ 9 - ((44 / 193) : ℂ) * ζ ^ 10 + ((1 / 193) : ℂ) * ζ ^ 13 - ((991 / 386) : ℂ) * ζ ^ 14 - ((698 / 193) : ℂ) * ζ ^ 15 + ((54 / 193) : ℂ) * ζ ^ 18 + ((698 / 193) : ℂ) * ζ ^ 19 + ((374 / 193) : ℂ) * ζ ^ 20 + ((1079 / 386) : ℂ) * ζ ^ 22 - ((340 / 193) : ℂ) * ζ ^ 23 - ((374 / 193) : ℂ) * ζ ^ 24 + ((297 / 386) : ℂ) * ζ ^ 25 + ((1079 / 386) : ℂ) * ζ ^ 26 + ((661 / 386) : ℂ) * ζ ^ 28 - ((297 / 386) : ℂ) * ζ ^ 29 - ((1079 / 386) : ℂ) * ζ ^ 30 - ((3 / 2) : ℂ) * ζ ^ 33 - ((3 / 2) : ℂ) * ζ ^ 35 + ((3 / 2) : ℂ) * ζ ^ 39 - ((1 / 2) : ℂ) * ζ ^ 40 - ((3 / 2) : ℂ) * ζ ^ 43 + ((1 / 2) : ℂ) * ζ ^ 44 - ζ ^ 45 - ((1 / 2) : ℂ) * ζ ^ 48 + ζ ^ 49 - ((1 / 2) : ℂ) * ζ ^ 50 - ζ ^ 53 + ((1 / 2) : ℂ) * ζ ^ 54 - ((1 / 2) : ℂ) * ζ ^ 55 - ((1 / 2) : ℂ) * ζ ^ 58 + ((1 / 2) : ℂ) * ζ ^ 59 - ((1 / 2) : ℂ) * ζ ^ 63 + ((1 / 2) : ℂ) * ζ ^ 65 - ((1 / 2) : ℂ) * ζ ^ 69 - ((1 / 2) : ℂ) * ζ ^ 70 + ((1 / 2) : ℂ) * ζ ^ 73 + ((1 / 2) : ℂ) * ζ ^ 74)
private theorem row13_generatorB_mul_eigenbasis_0_4 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        0 4 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        0 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((3282 / 2123) : ℂ) - ((4451 / 4246) : ℂ) * ζ ^ 3 + ((3282 / 2123) : ℂ) * ζ ^ 4 + ((3749 / 2123) : ℂ) * ζ ^ 5 + ((2109 / 4246) : ℂ) * ζ ^ 6 - ((6062 / 2123) : ℂ) * ζ ^ 8 - ((3749 / 2123) : ℂ) * ζ ^ 9 + ((3351 / 4246) : ℂ) * ζ ^ 10 + ((323 / 193) : ℂ) * ζ ^ 13 - ((621 / 2123) : ℂ) * ζ ^ 14 - ((3166 / 2123) : ℂ) * ζ ^ 15 + ((1245 / 4246) : ℂ) * ζ ^ 18 + ((3166 / 2123) : ℂ) * ζ ^ 19 - ((45 / 386) : ℂ) * ζ ^ 20 - ((2109 / 4246) : ℂ) * ζ ^ 22 - ((2781 / 4246) : ℂ) * ζ ^ 23 + ((45 / 386) : ℂ) * ζ ^ 24 + ((5513 / 4246) : ℂ) * ζ ^ 25 - ((2109 / 4246) : ℂ) * ζ ^ 26 + ((2411 / 4246) : ℂ) * ζ ^ 28 - ((5513 / 4246) : ℂ) * ζ ^ 29 + ((1923 / 2123) : ℂ) * ζ ^ 30 + ((4 / 11) : ℂ) * ζ ^ 33 - ((9 / 22) : ℂ) * ζ ^ 34 + ((1 / 22) : ℂ) * ζ ^ 35 + ((9 / 22) : ℂ) * ζ ^ 38 - ((1 / 22) : ℂ) * ζ ^ 39 - ((2 / 11) : ℂ) * ζ ^ 40 + ((1 / 22) : ℂ) * ζ ^ 43 + ((2 / 11) : ℂ) * ζ ^ 44 + ((9 / 22) : ℂ) * ζ ^ 45 - ((2 / 11) : ℂ) * ζ ^ 48 - ((9 / 22) : ℂ) * ζ ^ 49 + ((1 / 2) : ℂ) * ζ ^ 50 + ((9 / 22) : ℂ) * ζ ^ 53 - ((1 / 2) : ℂ) * ζ ^ 54 - ((1 / 11) : ℂ) * ζ ^ 55 + ((1 / 2) : ℂ) * ζ ^ 58 + ((1 / 11) : ℂ) * ζ ^ 59 - ((7 / 22) : ℂ) * ζ ^ 60 - ((1 / 11) : ℂ) * ζ ^ 63 + ((7 / 22) : ℂ) * ζ ^ 64 + ((1 / 22) : ℂ) * ζ ^ 65 - ((7 / 22) : ℂ) * ζ ^ 68 - ((1 / 22) : ℂ) * ζ ^ 69 + ((1 / 11) : ℂ) * ζ ^ 70 + ((1 / 22) : ℂ) * ζ ^ 73 - ((1 / 11) : ℂ) * ζ ^ 74 - ((3 / 22) : ℂ) * ζ ^ 75 + ((1 / 11) : ℂ) * ζ ^ 78 + ((3 / 22) : ℂ) * ζ ^ 79 - ((3 / 22) : ℂ) * ζ ^ 80 - ((3 / 22) : ℂ) * ζ ^ 83 + ((3 / 22) : ℂ) * ζ ^ 84 - ((4 / 11) : ℂ) * ζ ^ 85 - ((3 / 22) : ℂ) * ζ ^ 88 + ((4 / 11) : ℂ) * ζ ^ 89 - ((9 / 22) : ℂ) * ζ ^ 90 - ((4 / 11) : ℂ) * ζ ^ 93 + ((9 / 22) : ℂ) * ζ ^ 94 - ((1 / 22) : ℂ) * ζ ^ 95 - ((9 / 22) : ℂ) * ζ ^ 98 + ((1 / 22) : ℂ) * ζ ^ 99 + ((2 / 11) : ℂ) * ζ ^ 100 - ((1 / 22) : ℂ) * ζ ^ 103 - ((2 / 11) : ℂ) * ζ ^ 104)
private theorem row13_generatorB_mul_eigenbasis_0_5 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        0 5 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        0 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((1114 / 2123) : ℂ) - ((1127 / 2123) : ℂ) * ζ ^ 3 - ((1114 / 2123) : ℂ) * ζ ^ 4 + ((652 / 2123) : ℂ) * ζ ^ 5 - ((2997 / 2123) : ℂ) * ζ ^ 6 + ((1719 / 2123) : ℂ) * ζ ^ 8 - ((652 / 2123) : ℂ) * ζ ^ 9 - ((2293 / 2123) : ℂ) * ζ ^ 10 - ((985 / 2123) : ℂ) * ζ ^ 13 - ((64 / 193) : ℂ) * ζ ^ 14 - ((689 / 2123) : ℂ) * ζ ^ 15 + ((50 / 2123) : ℂ) * ζ ^ 18 + ((689 / 2123) : ℂ) * ζ ^ 19 + ((5350 / 2123) : ℂ) * ζ ^ 20 + ((2997 / 2123) : ℂ) * ζ ^ 22 + ((457 / 2123) : ℂ) * ζ ^ 23 - ((5350 / 2123) : ℂ) * ζ ^ 24 + ((199 / 193) : ℂ) * ζ ^ 25 + ((2997 / 2123) : ℂ) * ζ ^ 26 + ((9 / 193) : ℂ) * ζ ^ 28 - ((199 / 193) : ℂ) * ζ ^ 29 - ((3576 / 2123) : ℂ) * ζ ^ 30 + ((3 / 11) : ℂ) * ζ ^ 33 + ((3 / 11) : ℂ) * ζ ^ 34 - ((2 / 11) : ℂ) * ζ ^ 35 - ((3 / 11) : ℂ) * ζ ^ 38 + ((2 / 11) : ℂ) * ζ ^ 39 + ((1 / 11) : ℂ) * ζ ^ 40 - ((2 / 11) : ℂ) * ζ ^ 43 - ((1 / 11) : ℂ) * ζ ^ 44 + ((7 / 11) : ℂ) * ζ ^ 45 + ((1 / 11) : ℂ) * ζ ^ 48 - ((7 / 11) : ℂ) * ζ ^ 49 - ((2 / 11) : ℂ) * ζ ^ 50 + ((7 / 11) : ℂ) * ζ ^ 53 + ((2 / 11) : ℂ) * ζ ^ 54 - ((2 / 11) : ℂ) * ζ ^ 58 - ((2 / 11) : ℂ) * ζ ^ 60 + ((2 / 11) : ℂ) * ζ ^ 64 + ((4 / 11) : ℂ) * ζ ^ 65 - ((2 / 11) : ℂ) * ζ ^ 68 - ((4 / 11) : ℂ) * ζ ^ 69 + ((1 / 11) : ℂ) * ζ ^ 70 + ((4 / 11) : ℂ) * ζ ^ 73 - ((1 / 11) : ℂ) * ζ ^ 74 + ((2 / 11) : ℂ) * ζ ^ 75 + ((1 / 11) : ℂ) * ζ ^ 78 - ((2 / 11) : ℂ) * ζ ^ 79 - ((3 / 11) : ℂ) * ζ ^ 80 + ((2 / 11) : ℂ) * ζ ^ 83 + ((3 / 11) : ℂ) * ζ ^ 84 - ((3 / 11) : ℂ) * ζ ^ 85 - ((3 / 11) : ℂ) * ζ ^ 88 + ((3 / 11) : ℂ) * ζ ^ 89 + ((3 / 11) : ℂ) * ζ ^ 90 - ((3 / 11) : ℂ) * ζ ^ 93 - ((3 / 11) : ℂ) * ζ ^ 94 + ((2 / 11) : ℂ) * ζ ^ 95 + ((3 / 11) : ℂ) * ζ ^ 98 - ((2 / 11) : ℂ) * ζ ^ 99 - ((1 / 11) : ℂ) * ζ ^ 100 + ((2 / 11) : ℂ) * ζ ^ 103 + ((1 / 11) : ℂ) * ζ ^ 104)
private theorem row13_generatorB_mul_eigenbasis_1_0 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        1 0 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        1 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((317 / 386) : ℂ) - ((241 / 386) : ℂ) * ζ ^ 3 + ((317 / 386) : ℂ) * ζ ^ 4 - ((146 / 193) : ℂ) * ζ ^ 5 + ((371 / 193) : ℂ) * ζ ^ 6 + ((33 / 386) : ℂ) * ζ ^ 8 + ((146 / 193) : ℂ) * ζ ^ 9 + ((379 / 193) : ℂ) * ζ ^ 10 - ((12 / 193) : ℂ) * ζ ^ 13 - ((8 / 193) : ℂ) * ζ ^ 14 + ((411 / 386) : ℂ) * ζ ^ 15 - ((1531 / 386) : ℂ) * ζ ^ 18 - ((411 / 386) : ℂ) * ζ ^ 19 - ((463 / 386) : ℂ) * ζ ^ 20 - ((371 / 193) : ℂ) * ζ ^ 22 + ((237 / 193) : ℂ) * ζ ^ 23 + ((463 / 386) : ℂ) * ζ ^ 24 + ((107 / 193) : ℂ) * ζ ^ 25 - ((371 / 193) : ℂ) * ζ ^ 26 + ((115 / 193) : ℂ) * ζ ^ 28 - ((107 / 193) : ℂ) * ζ ^ 29 + ((371 / 193) : ℂ) * ζ ^ 30)
private theorem row13_generatorB_mul_eigenbasis_1_1 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        1 1 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        1 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((1220 / 579) : ℂ) + ((139 / 579) : ℂ) * ζ ^ 3 + ((1220 / 579) : ℂ) * ζ ^ 4 - ((171 / 193) : ℂ) * ζ ^ 5 - ((121 / 579) : ℂ) * ζ ^ 6 - ((702 / 193) : ℂ) * ζ ^ 8 + ((171 / 193) : ℂ) * ζ ^ 9 + ((127 / 579) : ℂ) * ζ ^ 10 + ((331 / 579) : ℂ) * ζ ^ 13 - ((248 / 579) : ℂ) * ζ ^ 14 - ((1042 / 579) : ℂ) * ζ ^ 15 - ((310 / 579) : ℂ) * ζ ^ 18 + ((1042 / 579) : ℂ) * ζ ^ 19 - ((290 / 579) : ℂ) * ζ ^ 20 + ((121 / 579) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 23 + ((290 / 579) : ℂ) * ζ ^ 24 - ((43 / 193) : ℂ) * ζ ^ 25 + ((121 / 579) : ℂ) * ζ ^ 26 - ((629 / 579) : ℂ) * ζ ^ 28 + ((43 / 193) : ℂ) * ζ ^ 29 - ((121 / 579) : ℂ) * ζ ^ 30)
private theorem row13_generatorB_mul_eigenbasis_1_2 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        1 2 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        1 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((513 / 386) : ℂ) + ((285 / 386) : ℂ) * ζ ^ 3 + ((513 / 386) : ℂ) * ζ ^ 4 - ((175 / 193) : ℂ) * ζ ^ 5 + ((170 / 193) : ℂ) * ζ ^ 6 - ((467 / 386) : ℂ) * ζ ^ 8 + ((175 / 193) : ℂ) * ζ ^ 9 + ((170 / 193) : ℂ) * ζ ^ 10 - ((24 / 193) : ℂ) * ζ ^ 13 - ((369 / 386) : ℂ) * ζ ^ 15 - ((210 / 193) : ℂ) * ζ ^ 18 + ((369 / 386) : ℂ) * ζ ^ 19 - ((381 / 193) : ℂ) * ζ ^ 20 - ((170 / 193) : ℂ) * ζ ^ 22 + ((96 / 193) : ℂ) * ζ ^ 23 + ((381 / 193) : ℂ) * ζ ^ 24 - ((87 / 386) : ℂ) * ζ ^ 25 - ((170 / 193) : ℂ) * ζ ^ 26 + ((37 / 386) : ℂ) * ζ ^ 28 + ((87 / 386) : ℂ) * ζ ^ 29 + ((170 / 193) : ℂ) * ζ ^ 30 + ((1 / 2) : ℂ) * ζ ^ 33 + ((1 / 2) : ℂ) * ζ ^ 35 - ((1 / 2) : ℂ) * ζ ^ 39 - ((1 / 2) : ℂ) * ζ ^ 40 + ((1 / 2) : ℂ) * ζ ^ 43 + ((1 / 2) : ℂ) * ζ ^ 44)
private theorem row13_generatorB_mul_eigenbasis_1_3 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        1 3 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        1 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((1231 / 193) : ℂ) + ((15 / 2) : ℂ) * ζ ^ 3 + ((1231 / 193) : ℂ) * ζ ^ 4 - ((717 / 193) : ℂ) * ζ ^ 5 - ((513 / 386) : ℂ) * ζ ^ 6 - ((1331 / 386) : ℂ) * ζ ^ 8 + ((717 / 193) : ℂ) * ζ ^ 9 - ((589 / 386) : ℂ) * ζ ^ 10 - ((377 / 386) : ℂ) * ζ ^ 13 + ((38 / 193) : ℂ) * ζ ^ 14 - ((1457 / 386) : ℂ) * ζ ^ 15 - ((479 / 386) : ℂ) * ζ ^ 18 + ((1457 / 386) : ℂ) * ζ ^ 19 + ((525 / 193) : ℂ) * ζ ^ 20 + ((513 / 386) : ℂ) * ζ ^ 22 - ((937 / 386) : ℂ) * ζ ^ 23 - ((525 / 193) : ℂ) * ζ ^ 24 + ((234 / 193) : ℂ) * ζ ^ 25 + ((513 / 386) : ℂ) * ζ ^ 26 + ((369 / 386) : ℂ) * ζ ^ 28 - ((234 / 193) : ℂ) * ζ ^ 29 - ((353 / 193) : ℂ) * ζ ^ 30 - ((1 / 2) : ℂ) * ζ ^ 33 + ((1 / 2) : ℂ) * ζ ^ 34 - ((1 / 2) : ℂ) * ζ ^ 38 + ((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 44 + ((1 / 2) : ℂ) * ζ ^ 45 + ((1 / 2) : ℂ) * ζ ^ 48 - ((1 / 2) : ℂ) * ζ ^ 49 + ((1 / 2) : ℂ) * ζ ^ 53 + ((1 / 2) : ℂ) * ζ ^ 55 - ((1 / 2) : ℂ) * ζ ^ 59 + ((1 / 2) : ℂ) * ζ ^ 60 + ((1 / 2) : ℂ) * ζ ^ 63 - ((1 / 2) : ℂ) * ζ ^ 64 + ζ ^ 65 + ((1 / 2) : ℂ) * ζ ^ 68 - ζ ^ 69 + ((1 / 2) : ℂ) * ζ ^ 70 + ζ ^ 73 - ((1 / 2) : ℂ) * ζ ^ 74)
private theorem row13_generatorB_mul_eigenbasis_1_4 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        1 4 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        1 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((3869 / 4246) : ℂ) - ((247 / 4246) : ℂ) * ζ ^ 3 + ((3869 / 4246) : ℂ) * ζ ^ 4 + ((7124 / 2123) : ℂ) * ζ ^ 5 + ((258 / 2123) : ℂ) * ζ ^ 6 - ((8045 / 4246) : ℂ) * ζ ^ 8 - ((7124 / 2123) : ℂ) * ζ ^ 9 + ((3149 / 2123) : ℂ) * ζ ^ 10 + ((6242 / 2123) : ℂ) * ζ ^ 13 - ((2891 / 2123) : ℂ) * ζ ^ 14 - ((4755 / 4246) : ℂ) * ζ ^ 15 + ((2367 / 2123) : ℂ) * ζ ^ 18 + ((4755 / 4246) : ℂ) * ζ ^ 19 - ((1162 / 2123) : ℂ) * ζ ^ 20 - ((258 / 2123) : ℂ) * ζ ^ 22 - ((612 / 2123) : ℂ) * ζ ^ 23 + ((1162 / 2123) : ℂ) * ζ ^ 24 + ((1745 / 4246) : ℂ) * ζ ^ 25 - ((258 / 2123) : ℂ) * ζ ^ 26 + ((331 / 4246) : ℂ) * ζ ^ 28 - ((1745 / 4246) : ℂ) * ζ ^ 29 + ((644 / 2123) : ℂ) * ζ ^ 30 + ((3 / 22) : ℂ) * ζ ^ 33 - ((2 / 11) : ℂ) * ζ ^ 34 - ((5 / 22) : ℂ) * ζ ^ 35 + ((2 / 11) : ℂ) * ζ ^ 38 + ((5 / 22) : ℂ) * ζ ^ 39 + ((3 / 22) : ℂ) * ζ ^ 40 - ((5 / 22) : ℂ) * ζ ^ 43 - ((3 / 22) : ℂ) * ζ ^ 44 + ((3 / 22) : ℂ) * ζ ^ 48 + ((3 / 22) : ℂ) * ζ ^ 50 - ((3 / 22) : ℂ) * ζ ^ 54 - ((17 / 22) : ℂ) * ζ ^ 55 + ((3 / 22) : ℂ) * ζ ^ 58 + ((17 / 22) : ℂ) * ζ ^ 59 + ((2 / 11) : ℂ) * ζ ^ 60 - ((17 / 22) : ℂ) * ζ ^ 63 - ((2 / 11) : ℂ) * ζ ^ 64 - ((3 / 22) : ℂ) * ζ ^ 65 + ((2 / 11) : ℂ) * ζ ^ 68 + ((3 / 22) : ℂ) * ζ ^ 69 - ((1 / 22) : ℂ) * ζ ^ 70 - ((3 / 22) : ℂ) * ζ ^ 73 + ((1 / 22) : ℂ) * ζ ^ 74 - ((6 / 11) : ℂ) * ζ ^ 75 - ((1 / 22) : ℂ) * ζ ^ 78 + ((6 / 11) : ℂ) * ζ ^ 79 + ((1 / 22) : ℂ) * ζ ^ 80 - ((6 / 11) : ℂ) * ζ ^ 83 - ((1 / 22) : ℂ) * ζ ^ 84 - ((3 / 22) : ℂ) * ζ ^ 85 + ((1 / 22) : ℂ) * ζ ^ 88 + ((3 / 22) : ℂ) * ζ ^ 89 - ((2 / 11) : ℂ) * ζ ^ 90 - ((3 / 22) : ℂ) * ζ ^ 93 + ((2 / 11) : ℂ) * ζ ^ 94 + ((5 / 22) : ℂ) * ζ ^ 95 - ((2 / 11) : ℂ) * ζ ^ 98 - ((5 / 22) : ℂ) * ζ ^ 99 - ((3 / 22) : ℂ) * ζ ^ 100 + ((5 / 22) : ℂ) * ζ ^ 103 + ((3 / 22) : ℂ) * ζ ^ 104)
private theorem row13_generatorB_mul_eigenbasis_1_5 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        1 5 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        1 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((2311 / 2123) : ℂ) + ((1973 / 2123) : ℂ) * ζ ^ 3 - ((2311 / 2123) : ℂ) * ζ ^ 4 + ((425 / 2123) : ℂ) * ζ ^ 5 - ((2582 / 2123) : ℂ) * ζ ^ 6 + ((326 / 193) : ℂ) * ζ ^ 8 - ((425 / 2123) : ℂ) * ζ ^ 9 - ((1730 / 2123) : ℂ) * ζ ^ 10 - ((1248 / 2123) : ℂ) * ζ ^ 13 - ((852 / 2123) : ℂ) * ζ ^ 14 - ((1846 / 2123) : ℂ) * ζ ^ 15 - ((547 / 2123) : ℂ) * ζ ^ 18 + ((1846 / 2123) : ℂ) * ζ ^ 19 + ((4003 / 2123) : ℂ) * ζ ^ 20 + ((2582 / 2123) : ℂ) * ζ ^ 22 + ((30 / 2123) : ℂ) * ζ ^ 23 - ((4003 / 2123) : ℂ) * ζ ^ 24 + ((490 / 2123) : ℂ) * ζ ^ 25 + ((2582 / 2123) : ℂ) * ζ ^ 26 - ((423 / 2123) : ℂ) * ζ ^ 28 - ((490 / 2123) : ℂ) * ζ ^ 29 - ((2003 / 2123) : ℂ) * ζ ^ 30 - ((1 / 11) : ℂ) * ζ ^ 33 - ((3 / 11) : ℂ) * ζ ^ 34 + ((4 / 11) : ℂ) * ζ ^ 35 + ((3 / 11) : ℂ) * ζ ^ 38 - ((4 / 11) : ℂ) * ζ ^ 39 - ((5 / 11) : ℂ) * ζ ^ 40 + ((4 / 11) : ℂ) * ζ ^ 43 + ((5 / 11) : ℂ) * ζ ^ 44 + ((3 / 11) : ℂ) * ζ ^ 45 - ((5 / 11) : ℂ) * ζ ^ 48 - ((3 / 11) : ℂ) * ζ ^ 49 + ((3 / 11) : ℂ) * ζ ^ 53 + ((3 / 11) : ℂ) * ζ ^ 55 - ((3 / 11) : ℂ) * ζ ^ 59 - ((6 / 11) : ℂ) * ζ ^ 60 + ((3 / 11) : ℂ) * ζ ^ 63 + ((6 / 11) : ℂ) * ζ ^ 64 + ((4 / 11) : ℂ) * ζ ^ 65 - ((6 / 11) : ℂ) * ζ ^ 68 - ((4 / 11) : ℂ) * ζ ^ 69 - ((3 / 11) : ℂ) * ζ ^ 70 + ((4 / 11) : ℂ) * ζ ^ 73 + ((3 / 11) : ℂ) * ζ ^ 74 - ((1 / 11) : ℂ) * ζ ^ 75 - ((3 / 11) : ℂ) * ζ ^ 78 + ((1 / 11) : ℂ) * ζ ^ 79 - ((1 / 11) : ℂ) * ζ ^ 80 - ((1 / 11) : ℂ) * ζ ^ 83 + ((1 / 11) : ℂ) * ζ ^ 84 + ((1 / 11) : ℂ) * ζ ^ 85 - ((1 / 11) : ℂ) * ζ ^ 88 - ((1 / 11) : ℂ) * ζ ^ 89 - ((3 / 11) : ℂ) * ζ ^ 90 + ((1 / 11) : ℂ) * ζ ^ 93 + ((3 / 11) : ℂ) * ζ ^ 94 - ((4 / 11) : ℂ) * ζ ^ 95 - ((3 / 11) : ℂ) * ζ ^ 98 + ((4 / 11) : ℂ) * ζ ^ 99 + ((5 / 11) : ℂ) * ζ ^ 100 - ((4 / 11) : ℂ) * ζ ^ 103 - ((5 / 11) : ℂ) * ζ ^ 104)
private theorem row13_generatorB_mul_eigenbasis_2_0 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        2 0 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        2 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((519 / 386) : ℂ) + ((88 / 193) : ℂ) * ζ ^ 3 - ((519 / 386) : ℂ) * ζ ^ 4 + ((85 / 193) : ℂ) * ζ ^ 5 + ((55 / 193) : ℂ) * ζ ^ 6 + ((651 / 386) : ℂ) * ζ ^ 8 - ((85 / 193) : ℂ) * ζ ^ 9 + ((90 / 193) : ℂ) * ζ ^ 10 - ((105 / 386) : ℂ) * ζ ^ 13 - ((35 / 193) : ℂ) * ζ ^ 14 - ((78 / 193) : ℂ) * ζ ^ 15 - ((249 / 193) : ℂ) * ζ ^ 18 + ((78 / 193) : ℂ) * ζ ^ 19 - ((84 / 193) : ℂ) * ζ ^ 20 - ((55 / 193) : ℂ) * ζ ^ 22 + ((96 / 193) : ℂ) * ζ ^ 23 + ((84 / 193) : ℂ) * ζ ^ 24 + ((309 / 386) : ℂ) * ζ ^ 25 - ((55 / 193) : ℂ) * ζ ^ 26 - ((7 / 386) : ℂ) * ζ ^ 28 - ((309 / 386) : ℂ) * ζ ^ 29 + ((55 / 193) : ℂ) * ζ ^ 30)
private theorem row13_generatorB_mul_eigenbasis_2_1 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        2 1 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        2 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((183 / 193) : ℂ) - ((767 / 579) : ℂ) * ζ ^ 3 - ((183 / 193) : ℂ) * ζ ^ 4 + ((530 / 579) : ℂ) * ζ ^ 5 - ((71 / 579) : ℂ) * ζ ^ 6 - ((128 / 193) : ℂ) * ζ ^ 8 - ((530 / 579) : ℂ) * ζ ^ 9 - ((530 / 579) : ℂ) * ζ ^ 10 - ((40 / 193) : ℂ) * ζ ^ 13 + ((153 / 193) : ℂ) * ζ ^ 14 - ((249 / 193) : ℂ) * ζ ^ 15 - ((243 / 193) : ℂ) * ζ ^ 18 + ((249 / 193) : ℂ) * ζ ^ 19 - ((545 / 579) : ℂ) * ζ ^ 20 + ((71 / 579) : ℂ) * ζ ^ 22 + ((545 / 579) : ℂ) * ζ ^ 24 + ((280 / 579) : ℂ) * ζ ^ 25 + ((71 / 579) : ℂ) * ζ ^ 26 - ((74 / 579) : ℂ) * ζ ^ 28 - ((280 / 579) : ℂ) * ζ ^ 29 - ((71 / 579) : ℂ) * ζ ^ 30)
private theorem row13_generatorB_mul_eigenbasis_2_2 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        2 2 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        2 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((337 / 386) : ℂ) - ((40 / 193) : ℂ) * ζ ^ 3 - ((337 / 386) : ℂ) * ζ ^ 4 + ((127 / 193) : ℂ) * ζ ^ 5 - ((173 / 193) : ℂ) * ζ ^ 6 - ((89 / 386) : ℂ) * ζ ^ 8 - ((127 / 193) : ℂ) * ζ ^ 9 - ((173 / 193) : ℂ) * ζ ^ 10 + ((369 / 386) : ℂ) * ζ ^ 13 - ((191 / 386) : ℂ) * ζ ^ 15 - ((197 / 386) : ℂ) * ζ ^ 18 + ((191 / 386) : ℂ) * ζ ^ 19 - ((340 / 193) : ℂ) * ζ ^ 20 + ((173 / 193) : ℂ) * ζ ^ 22 - ((125 / 386) : ℂ) * ζ ^ 23 + ((340 / 193) : ℂ) * ζ ^ 24 - ((130 / 193) : ℂ) * ζ ^ 25 + ((173 / 193) : ℂ) * ζ ^ 26 - ((7 / 386) : ℂ) * ζ ^ 28 + ((130 / 193) : ℂ) * ζ ^ 29 - ((153 / 386) : ℂ) * ζ ^ 30 - ((1 / 2) : ℂ) * ζ ^ 33 - ((1 / 2) : ℂ) * ζ ^ 34 + ((1 / 2) : ℂ) * ζ ^ 38 + ((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 44)
private theorem row13_generatorB_mul_eigenbasis_2_3 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        2 3 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        2 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((54 / 193) : ℂ) + ((7 / 2) : ℂ) * ζ ^ 3 + ((54 / 193) : ℂ) * ζ ^ 4 + ((819 / 386) : ℂ) * ζ ^ 5 - ((121 / 193) : ℂ) * ζ ^ 6 - ((395 / 386) : ℂ) * ζ ^ 8 - ((819 / 386) : ℂ) * ζ ^ 9 - ((1057 / 386) : ℂ) * ζ ^ 10 + ((1125 / 386) : ℂ) * ζ ^ 13 + ((815 / 386) : ℂ) * ζ ^ 14 + ((67 / 386) : ℂ) * ζ ^ 15 - ((312 / 193) : ℂ) * ζ ^ 18 - ((67 / 386) : ℂ) * ζ ^ 19 - ((183 / 386) : ℂ) * ζ ^ 20 + ((121 / 193) : ℂ) * ζ ^ 22 - ((167 / 386) : ℂ) * ζ ^ 23 + ((183 / 386) : ℂ) * ζ ^ 24 + ((21 / 386) : ℂ) * ζ ^ 25 + ((121 / 193) : ℂ) * ζ ^ 26 - ((195 / 386) : ℂ) * ζ ^ 28 - ((21 / 386) : ℂ) * ζ ^ 29 - ((821 / 386) : ℂ) * ζ ^ 30 + ζ ^ 33 + ((3 / 2) : ℂ) * ζ ^ 34 + ((1 / 2) : ℂ) * ζ ^ 35 - ((3 / 2) : ℂ) * ζ ^ 38 - ((1 / 2) : ℂ) * ζ ^ 39 - ζ ^ 40 + ((1 / 2) : ℂ) * ζ ^ 43 + ζ ^ 44 + ((1 / 2) : ℂ) * ζ ^ 45 - ζ ^ 48 - ((1 / 2) : ℂ) * ζ ^ 49 - ((1 / 2) : ℂ) * ζ ^ 50 + ((1 / 2) : ℂ) * ζ ^ 53 + ((1 / 2) : ℂ) * ζ ^ 54 - ((1 / 2) : ℂ) * ζ ^ 58 + ((1 / 2) : ℂ) * ζ ^ 60 - ((1 / 2) : ℂ) * ζ ^ 64 - ((1 / 2) : ℂ) * ζ ^ 65 + ((1 / 2) : ℂ) * ζ ^ 68 + ((1 / 2) : ℂ) * ζ ^ 69 + ζ ^ 70 - ((1 / 2) : ℂ) * ζ ^ 73 - ζ ^ 74)
private theorem row13_generatorB_mul_eigenbasis_2_4 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        2 4 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        2 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((5823 / 4246) : ℂ) - ((673 / 2123) : ℂ) * ζ ^ 3 - ((5823 / 4246) : ℂ) * ζ ^ 4 + ((4823 / 2123) : ℂ) * ζ ^ 5 + ((212 / 2123) : ℂ) * ζ ^ 6 + ((4923 / 4246) : ℂ) * ζ ^ 8 - ((4823 / 2123) : ℂ) * ζ ^ 9 + ((2221 / 2123) : ℂ) * ζ ^ 10 + ((7429 / 4246) : ℂ) * ζ ^ 13 - ((2009 / 2123) : ℂ) * ζ ^ 14 + ((1995 / 4246) : ℂ) * ζ ^ 15 + ((2521 / 4246) : ℂ) * ζ ^ 18 - ((1995 / 4246) : ℂ) * ζ ^ 19 + ((130 / 193) : ℂ) * ζ ^ 20 - ((212 / 2123) : ℂ) * ζ ^ 22 + ((821 / 4246) : ℂ) * ζ ^ 23 - ((130 / 193) : ℂ) * ζ ^ 24 + ((1658 / 2123) : ℂ) * ζ ^ 25 - ((212 / 2123) : ℂ) * ζ ^ 26 + ((2003 / 4246) : ℂ) * ζ ^ 28 - ((1658 / 2123) : ℂ) * ζ ^ 29 + ((1003 / 4246) : ℂ) * ζ ^ 30 + ((5 / 22) : ℂ) * ζ ^ 33 - ((3 / 22) : ℂ) * ζ ^ 34 + ((5 / 11) : ℂ) * ζ ^ 35 + ((3 / 22) : ℂ) * ζ ^ 38 - ((5 / 11) : ℂ) * ζ ^ 39 + ((5 / 22) : ℂ) * ζ ^ 40 + ((5 / 11) : ℂ) * ζ ^ 43 - ((5 / 22) : ℂ) * ζ ^ 44 + ((1 / 2) : ℂ) * ζ ^ 45 + ((5 / 22) : ℂ) * ζ ^ 48 - ((1 / 2) : ℂ) * ζ ^ 49 - ((3 / 11) : ℂ) * ζ ^ 50 + ((1 / 2) : ℂ) * ζ ^ 53 + ((3 / 11) : ℂ) * ζ ^ 54 + ((1 / 22) : ℂ) * ζ ^ 55 - ((3 / 11) : ℂ) * ζ ^ 58 - ((1 / 22) : ℂ) * ζ ^ 59 + ((3 / 22) : ℂ) * ζ ^ 60 + ((1 / 22) : ℂ) * ζ ^ 63 - ((3 / 22) : ℂ) * ζ ^ 64 + ((3 / 11) : ℂ) * ζ ^ 65 + ((3 / 22) : ℂ) * ζ ^ 68 - ((3 / 11) : ℂ) * ζ ^ 69 - ((9 / 22) : ℂ) * ζ ^ 70 + ((3 / 11) : ℂ) * ζ ^ 73 + ((9 / 22) : ℂ) * ζ ^ 74 - ((9 / 22) : ℂ) * ζ ^ 75 - ((9 / 22) : ℂ) * ζ ^ 78 + ((9 / 22) : ℂ) * ζ ^ 79 - ((1 / 11) : ℂ) * ζ ^ 80 - ((9 / 22) : ℂ) * ζ ^ 83 + ((1 / 11) : ℂ) * ζ ^ 84 - ((5 / 22) : ℂ) * ζ ^ 85 - ((1 / 11) : ℂ) * ζ ^ 88 + ((5 / 22) : ℂ) * ζ ^ 89 - ((3 / 22) : ℂ) * ζ ^ 90 - ((5 / 22) : ℂ) * ζ ^ 93 + ((3 / 22) : ℂ) * ζ ^ 94 - ((5 / 11) : ℂ) * ζ ^ 95 - ((3 / 22) : ℂ) * ζ ^ 98 + ((5 / 11) : ℂ) * ζ ^ 99 - ((5 / 22) : ℂ) * ζ ^ 100 - ((5 / 11) : ℂ) * ζ ^ 103 + ((5 / 22) : ℂ) * ζ ^ 104)
private theorem row13_generatorB_mul_eigenbasis_2_5 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        2 5 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        2 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((3621 / 2123) : ℂ) + ((3831 / 2123) : ℂ) * ζ ^ 3 - ((3621 / 2123) : ℂ) * ζ ^ 4 + ((1594 / 2123) : ℂ) * ζ ^ 5 - ((247 / 2123) : ℂ) * ζ ^ 6 + ((3192 / 2123) : ℂ) * ζ ^ 8 - ((1594 / 2123) : ℂ) * ζ ^ 9 - ((476 / 2123) : ℂ) * ζ ^ 10 + ((1488 / 2123) : ℂ) * ζ ^ 13 + ((229 / 2123) : ℂ) * ζ ^ 14 + ((1622 / 2123) : ℂ) * ζ ^ 15 + ((912 / 2123) : ℂ) * ζ ^ 18 - ((1622 / 2123) : ℂ) * ζ ^ 19 + ((698 / 2123) : ℂ) * ζ ^ 20 + ((247 / 2123) : ℂ) * ζ ^ 22 + ((469 / 2123) : ℂ) * ζ ^ 23 - ((698 / 2123) : ℂ) * ζ ^ 24 - ((124 / 2123) : ℂ) * ζ ^ 25 + ((247 / 2123) : ℂ) * ζ ^ 26 - ((186 / 2123) : ℂ) * ζ ^ 28 + ((124 / 2123) : ℂ) * ζ ^ 29 + ((718 / 2123) : ℂ) * ζ ^ 30 + ((2 / 11) : ℂ) * ζ ^ 33 - ((5 / 11) : ℂ) * ζ ^ 34 + ((3 / 11) : ℂ) * ζ ^ 35 + ((5 / 11) : ℂ) * ζ ^ 38 - ((3 / 11) : ℂ) * ζ ^ 39 - ((1 / 11) : ℂ) * ζ ^ 40 + ((3 / 11) : ℂ) * ζ ^ 43 + ((1 / 11) : ℂ) * ζ ^ 44 - ((6 / 11) : ℂ) * ζ ^ 45 - ((1 / 11) : ℂ) * ζ ^ 48 + ((6 / 11) : ℂ) * ζ ^ 49 - ((6 / 11) : ℂ) * ζ ^ 53 + ((5 / 11) : ℂ) * ζ ^ 55 - ((5 / 11) : ℂ) * ζ ^ 59 + ((1 / 11) : ℂ) * ζ ^ 60 + ((5 / 11) : ℂ) * ζ ^ 63 - ((1 / 11) : ℂ) * ζ ^ 64 - ((8 / 11) : ℂ) * ζ ^ 65 + ((1 / 11) : ℂ) * ζ ^ 68 + ((8 / 11) : ℂ) * ζ ^ 69 - ((5 / 11) : ℂ) * ζ ^ 70 - ((8 / 11) : ℂ) * ζ ^ 73 + ((5 / 11) : ℂ) * ζ ^ 74 + ((2 / 11) : ℂ) * ζ ^ 75 - ((5 / 11) : ℂ) * ζ ^ 78 - ((2 / 11) : ℂ) * ζ ^ 79 + ((2 / 11) : ℂ) * ζ ^ 80 + ((2 / 11) : ℂ) * ζ ^ 83 - ((2 / 11) : ℂ) * ζ ^ 84 - ((2 / 11) : ℂ) * ζ ^ 85 + ((2 / 11) : ℂ) * ζ ^ 88 + ((2 / 11) : ℂ) * ζ ^ 89 - ((5 / 11) : ℂ) * ζ ^ 90 - ((2 / 11) : ℂ) * ζ ^ 93 + ((5 / 11) : ℂ) * ζ ^ 94 - ((3 / 11) : ℂ) * ζ ^ 95 - ((5 / 11) : ℂ) * ζ ^ 98 + ((3 / 11) : ℂ) * ζ ^ 99 + ((1 / 11) : ℂ) * ζ ^ 100 - ((3 / 11) : ℂ) * ζ ^ 103 - ((1 / 11) : ℂ) * ζ ^ 104)
private theorem row13_generatorB_mul_eigenbasis_3_0 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        3 0 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        3 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((1431 / 386) : ℂ) - ((1298 / 193) : ℂ) * ζ ^ 3 + ((1431 / 386) : ℂ) * ζ ^ 4 - ((481 / 386) : ℂ) * ζ ^ 5 + ((597 / 386) : ℂ) * ζ ^ 6 - ((483 / 386) : ℂ) * ζ ^ 8 + ((481 / 386) : ℂ) * ζ ^ 9 + ((1205 / 386) : ℂ) * ζ ^ 10 + ((825 / 386) : ℂ) * ζ ^ 13 - ((304 / 193) : ℂ) * ζ ^ 14 + ((371 / 386) : ℂ) * ζ ^ 15 - ((471 / 386) : ℂ) * ζ ^ 18 - ((371 / 386) : ℂ) * ζ ^ 19 + ((81 / 193) : ℂ) * ζ ^ 20 - ((597 / 386) : ℂ) * ζ ^ 22 + ((1221 / 386) : ℂ) * ζ ^ 23 - ((81 / 193) : ℂ) * ζ ^ 24 + ((399 / 193) : ℂ) * ζ ^ 25 - ((597 / 386) : ℂ) * ζ ^ 26 + ((441 / 386) : ℂ) * ζ ^ 28 - ((399 / 193) : ℂ) * ζ ^ 29 + ((597 / 386) : ℂ) * ζ ^ 30)
private theorem row13_generatorB_mul_eigenbasis_3_1 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        3 1 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        3 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((335 / 193) : ℂ) + ((281 / 193) : ℂ) * ζ ^ 3 + ((335 / 193) : ℂ) * ζ ^ 4 - ((580 / 579) : ℂ) * ζ ^ 5 + ((140 / 193) : ℂ) * ζ ^ 6 - ((1670 / 579) : ℂ) * ζ ^ 8 + ((580 / 579) : ℂ) * ζ ^ 9 + ((1159 / 579) : ℂ) * ζ ^ 10 + ((590 / 193) : ℂ) * ζ ^ 13 - ((739 / 579) : ℂ) * ζ ^ 14 - ((610 / 579) : ℂ) * ζ ^ 15 - ((586 / 579) : ℂ) * ζ ^ 18 + ((610 / 579) : ℂ) * ζ ^ 19 - ((1177 / 579) : ℂ) * ζ ^ 20 - ((140 / 193) : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 23 + ((1177 / 579) : ℂ) * ζ ^ 24 + ((1081 / 579) : ℂ) * ζ ^ 25 - ((140 / 193) : ℂ) * ζ ^ 26 - ((1514 / 579) : ℂ) * ζ ^ 28 - ((1081 / 579) : ℂ) * ζ ^ 29 + ((140 / 193) : ℂ) * ζ ^ 30)
private theorem row13_generatorB_mul_eigenbasis_3_2 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        3 2 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        3 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((2317 / 386) : ℂ) + ((11 / 193) : ℂ) * ζ ^ 3 + ((2317 / 386) : ℂ) * ζ ^ 4 - ((369 / 386) : ℂ) * ζ ^ 5 + ((761 / 386) : ℂ) * ζ ^ 6 - ((1341 / 386) : ℂ) * ζ ^ 8 + ((369 / 386) : ℂ) * ζ ^ 9 + ((1533 / 386) : ℂ) * ζ ^ 10 + ((299 / 386) : ℂ) * ζ ^ 13 - (2 : ℂ) * ζ ^ 14 + ((130 / 193) : ℂ) * ζ ^ 15 - ((327 / 386) : ℂ) * ζ ^ 18 - ((130 / 193) : ℂ) * ζ ^ 19 - ((199 / 386) : ℂ) * ζ ^ 20 - ((761 / 386) : ℂ) * ζ ^ 22 + ((174 / 193) : ℂ) * ζ ^ 23 + ((199 / 386) : ℂ) * ζ ^ 24 - ((109 / 193) : ℂ) * ζ ^ 25 - ((761 / 386) : ℂ) * ζ ^ 26 + ((317 / 193) : ℂ) * ζ ^ 28 + ((109 / 193) : ℂ) * ζ ^ 29 + ((284 / 193) : ℂ) * ζ ^ 30 + ((1 / 2) : ℂ) * ζ ^ 34 - ((1 / 2) : ℂ) * ζ ^ 35 - ((1 / 2) : ℂ) * ζ ^ 38 + ((1 / 2) : ℂ) * ζ ^ 39 - ((1 / 2) : ℂ) * ζ ^ 43)
private theorem row13_generatorB_mul_eigenbasis_3_3 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        3 3 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        3 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((1809 / 193) : ℂ) + (3 : ℂ) * ζ ^ 3 + ((1809 / 193) : ℂ) * ζ ^ 4 - ((226 / 193) : ℂ) * ζ ^ 5 - ((1545 / 386) : ℂ) * ζ ^ 6 - ((3679 / 386) : ℂ) * ζ ^ 8 + ((226 / 193) : ℂ) * ζ ^ 9 + ((199 / 386) : ℂ) * ζ ^ 10 - ((237 / 386) : ℂ) * ζ ^ 13 - ((872 / 193) : ℂ) * ζ ^ 14 - ((856 / 193) : ℂ) * ζ ^ 15 + ((356 / 193) : ℂ) * ζ ^ 18 + ((856 / 193) : ℂ) * ζ ^ 19 + ((1879 / 386) : ℂ) * ζ ^ 20 + ((1545 / 386) : ℂ) * ζ ^ 22 - ((673 / 386) : ℂ) * ζ ^ 23 - ((1879 / 386) : ℂ) * ζ ^ 24 + ((400 / 193) : ℂ) * ζ ^ 25 + ((1545 / 386) : ℂ) * ζ ^ 26 + ((1091 / 386) : ℂ) * ζ ^ 28 - ((400 / 193) : ℂ) * ζ ^ 29 - ((1159 / 386) : ℂ) * ζ ^ 30 - ((1 / 2) : ℂ) * ζ ^ 33 - ζ ^ 34 - ((1 / 2) : ℂ) * ζ ^ 35 + ζ ^ 38 + ((1 / 2) : ℂ) * ζ ^ 39 + ((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 43 - ((1 / 2) : ℂ) * ζ ^ 44 + ((1 / 2) : ℂ) * ζ ^ 48 + ((1 / 2) : ℂ) * ζ ^ 50 - ((1 / 2) : ℂ) * ζ ^ 54 + ((1 / 2) : ℂ) * ζ ^ 55 + ((1 / 2) : ℂ) * ζ ^ 58 - ((1 / 2) : ℂ) * ζ ^ 59 + ((1 / 2) : ℂ) * ζ ^ 63 + ((1 / 2) : ℂ) * ζ ^ 65 - ((1 / 2) : ℂ) * ζ ^ 69 - ((1 / 2) : ℂ) * ζ ^ 70 + ((1 / 2) : ℂ) * ζ ^ 73 + ((1 / 2) : ℂ) * ζ ^ 74)
private theorem row13_generatorB_mul_eigenbasis_3_4 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        3 4 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        3 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((13273 / 4246) : ℂ) - ((5272 / 2123) : ℂ) * ζ ^ 3 + ((13273 / 4246) : ℂ) * ζ ^ 4 + ((8551 / 4246) : ℂ) * ζ ^ 5 + ((3203 / 4246) : ℂ) * ζ ^ 6 - ((18333 / 4246) : ℂ) * ζ ^ 8 - ((8551 / 4246) : ℂ) * ζ ^ 9 + ((2513 / 4246) : ℂ) * ζ ^ 10 + ((4437 / 4246) : ℂ) * ζ ^ 13 + ((345 / 2123) : ℂ) * ζ ^ 14 - ((6390 / 2123) : ℂ) * ζ ^ 15 - ((1335 / 4246) : ℂ) * ζ ^ 18 + ((6390 / 2123) : ℂ) * ζ ^ 19 - ((4743 / 4246) : ℂ) * ζ ^ 20 - ((3203 / 4246) : ℂ) * ζ ^ 22 - ((4921 / 2123) : ℂ) * ζ ^ 23 + ((4743 / 4246) : ℂ) * ζ ^ 24 + ((1889 / 2123) : ℂ) * ζ ^ 25 - ((3203 / 4246) : ℂ) * ζ ^ 26 - ((80 / 2123) : ℂ) * ζ ^ 28 - ((1889 / 2123) : ℂ) * ζ ^ 29 + ((1698 / 2123) : ℂ) * ζ ^ 30 + ((4 / 11) : ℂ) * ζ ^ 33 - ((1 / 22) : ℂ) * ζ ^ 34 - ((5 / 22) : ℂ) * ζ ^ 35 + ((1 / 22) : ℂ) * ζ ^ 38 + ((5 / 22) : ℂ) * ζ ^ 39 - ((5 / 22) : ℂ) * ζ ^ 43 + ((17 / 22) : ℂ) * ζ ^ 45 - ((17 / 22) : ℂ) * ζ ^ 49 - ((1 / 22) : ℂ) * ζ ^ 50 + ((17 / 22) : ℂ) * ζ ^ 53 + ((1 / 22) : ℂ) * ζ ^ 54 + ((4 / 11) : ℂ) * ζ ^ 55 - ((1 / 22) : ℂ) * ζ ^ 58 - ((4 / 11) : ℂ) * ζ ^ 59 + ((5 / 22) : ℂ) * ζ ^ 60 + ((4 / 11) : ℂ) * ζ ^ 63 - ((5 / 22) : ℂ) * ζ ^ 64 + ((9 / 22) : ℂ) * ζ ^ 65 + ((5 / 22) : ℂ) * ζ ^ 68 - ((9 / 22) : ℂ) * ζ ^ 69 - ((1 / 11) : ℂ) * ζ ^ 70 + ((9 / 22) : ℂ) * ζ ^ 73 + ((1 / 11) : ℂ) * ζ ^ 74 + ((13 / 22) : ℂ) * ζ ^ 75 - ((1 / 11) : ℂ) * ζ ^ 78 - ((13 / 22) : ℂ) * ζ ^ 79 + ((5 / 22) : ℂ) * ζ ^ 80 + ((13 / 22) : ℂ) * ζ ^ 83 - ((5 / 22) : ℂ) * ζ ^ 84 - ((4 / 11) : ℂ) * ζ ^ 85 + ((5 / 22) : ℂ) * ζ ^ 88 + ((4 / 11) : ℂ) * ζ ^ 89 - ((1 / 22) : ℂ) * ζ ^ 90 - ((4 / 11) : ℂ) * ζ ^ 93 + ((1 / 22) : ℂ) * ζ ^ 94 + ((5 / 22) : ℂ) * ζ ^ 95 - ((1 / 22) : ℂ) * ζ ^ 98 - ((5 / 22) : ℂ) * ζ ^ 99 + ((5 / 22) : ℂ) * ζ ^ 103)
private theorem row13_generatorB_mul_eigenbasis_3_5 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        3 5 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        3 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((105 / 193) : ℂ) - ((2612 / 2123) : ℂ) * ζ ^ 3 + ((105 / 193) : ℂ) * ζ ^ 4 + ((903 / 2123) : ℂ) * ζ ^ 5 - ((4897 / 2123) : ℂ) * ζ ^ 6 + ((36 / 193) : ℂ) * ζ ^ 8 - ((903 / 2123) : ℂ) * ζ ^ 9 - ((5717 / 2123) : ℂ) * ζ ^ 10 + ((247 / 2123) : ℂ) * ζ ^ 13 + ((820 / 2123) : ℂ) * ζ ^ 14 - ((2405 / 2123) : ℂ) * ζ ^ 15 - ((293 / 193) : ℂ) * ζ ^ 18 + ((2405 / 2123) : ℂ) * ζ ^ 19 + ((6399 / 2123) : ℂ) * ζ ^ 20 + ((4897 / 2123) : ℂ) * ζ ^ 22 - ((1369 / 2123) : ℂ) * ζ ^ 23 - ((6399 / 2123) : ℂ) * ζ ^ 24 + ((1829 / 2123) : ℂ) * ζ ^ 25 + ((4897 / 2123) : ℂ) * ζ ^ 26 - ((1985 / 2123) : ℂ) * ζ ^ 28 - ((1829 / 2123) : ℂ) * ζ ^ 29 - ((5476 / 2123) : ℂ) * ζ ^ 30 - ((5 / 11) : ℂ) * ζ ^ 33 + ((3 / 11) : ℂ) * ζ ^ 34 + ((1 / 11) : ℂ) * ζ ^ 35 - ((3 / 11) : ℂ) * ζ ^ 38 - ((1 / 11) : ℂ) * ζ ^ 39 + ((6 / 11) : ℂ) * ζ ^ 40 + ((1 / 11) : ℂ) * ζ ^ 43 - ((6 / 11) : ℂ) * ζ ^ 44 + ((6 / 11) : ℂ) * ζ ^ 48 + ((6 / 11) : ℂ) * ζ ^ 50 - ((6 / 11) : ℂ) * ζ ^ 54 - ((1 / 11) : ℂ) * ζ ^ 55 + ((6 / 11) : ℂ) * ζ ^ 58 + ((1 / 11) : ℂ) * ζ ^ 59 + ((8 / 11) : ℂ) * ζ ^ 60 - ((1 / 11) : ℂ) * ζ ^ 63 - ((8 / 11) : ℂ) * ζ ^ 64 + ((5 / 11) : ℂ) * ζ ^ 65 + ((8 / 11) : ℂ) * ζ ^ 68 - ((5 / 11) : ℂ) * ζ ^ 69 + ((9 / 11) : ℂ) * ζ ^ 70 + ((5 / 11) : ℂ) * ζ ^ 73 - ((9 / 11) : ℂ) * ζ ^ 74 - ((2 / 11) : ℂ) * ζ ^ 75 + ((9 / 11) : ℂ) * ζ ^ 78 + ((2 / 11) : ℂ) * ζ ^ 79 + ((2 / 11) : ℂ) * ζ ^ 80 - ((2 / 11) : ℂ) * ζ ^ 83 - ((2 / 11) : ℂ) * ζ ^ 84 + ((5 / 11) : ℂ) * ζ ^ 85 + ((2 / 11) : ℂ) * ζ ^ 88 - ((5 / 11) : ℂ) * ζ ^ 89 + ((3 / 11) : ℂ) * ζ ^ 90 + ((5 / 11) : ℂ) * ζ ^ 93 - ((3 / 11) : ℂ) * ζ ^ 94 - ((1 / 11) : ℂ) * ζ ^ 95 + ((3 / 11) : ℂ) * ζ ^ 98 + ((1 / 11) : ℂ) * ζ ^ 99 - ((6 / 11) : ℂ) * ζ ^ 100 - ((1 / 11) : ℂ) * ζ ^ 103 + ((6 / 11) : ℂ) * ζ ^ 104)
private theorem row13_generatorB_mul_eigenbasis_4_0 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        4 0 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        4 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((523 / 193) : ℂ) - ((199 / 386) : ℂ) * ζ ^ 3 - ((523 / 193) : ℂ) * ζ ^ 4 + ((1025 / 386) : ℂ) * ζ ^ 5 - ((1789 / 386) : ℂ) * ζ ^ 6 + ((569 / 193) : ℂ) * ζ ^ 8 - ((1025 / 386) : ℂ) * ζ ^ 9 - ((1401 / 386) : ℂ) * ζ ^ 10 - ((3 / 386) : ℂ) * ζ ^ 13 - ((194 / 193) : ℂ) * ζ ^ 14 - ((300 / 193) : ℂ) * ζ ^ 15 + ((1425 / 386) : ℂ) * ζ ^ 18 + ((300 / 193) : ℂ) * ζ ^ 19 - ((41 / 193) : ℂ) * ζ ^ 20 + ((1789 / 386) : ℂ) * ζ ^ 22 + ((102 / 193) : ℂ) * ζ ^ 23 + ((41 / 193) : ℂ) * ζ ^ 24 + ((134 / 193) : ℂ) * ζ ^ 25 + ((1789 / 386) : ℂ) * ζ ^ 26 - ((695 / 386) : ℂ) * ζ ^ 28 - ((134 / 193) : ℂ) * ζ ^ 29 - ((1789 / 386) : ℂ) * ζ ^ 30)
private theorem row13_generatorB_mul_eigenbasis_4_1 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        4 1 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        4 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((110 / 193) : ℂ) - ((248 / 579) : ℂ) * ζ ^ 3 - ((110 / 193) : ℂ) * ζ ^ 4 + ((630 / 193) : ℂ) * ζ ^ 5 + ((3 / 193) : ℂ) * ζ ^ 6 + ((443 / 193) : ℂ) * ζ ^ 8 - ((630 / 193) : ℂ) * ζ ^ 9 - ((1504 / 579) : ℂ) * ζ ^ 10 - ((31 / 579) : ℂ) * ζ ^ 13 + ((1513 / 579) : ℂ) * ζ ^ 14 + ((883 / 579) : ℂ) * ζ ^ 15 - ((859 / 579) : ℂ) * ζ ^ 18 - ((883 / 579) : ℂ) * ζ ^ 19 + ((197 / 193) : ℂ) * ζ ^ 20 - ((3 / 193) : ℂ) * ζ ^ 22 - (2 : ℂ) * ζ ^ 23 - ((197 / 193) : ℂ) * ζ ^ 24 + ((260 / 193) : ℂ) * ζ ^ 25 - ((3 / 193) : ℂ) * ζ ^ 26 + ((400 / 193) : ℂ) * ζ ^ 28 - ((260 / 193) : ℂ) * ζ ^ 29 + ((3 / 193) : ℂ) * ζ ^ 30)
private theorem row13_generatorB_mul_eigenbasis_4_2 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        4 2 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        4 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((366 / 193) : ℂ) - ((2015 / 386) : ℂ) * ζ ^ 3 - ((366 / 193) : ℂ) * ζ ^ 4 + ((1259 / 386) : ℂ) * ζ ^ 5 - ((633 / 386) : ℂ) * ζ ^ 6 + ((393 / 193) : ℂ) * ζ ^ 8 - ((1259 / 386) : ℂ) * ζ ^ 9 - ((633 / 386) : ℂ) * ζ ^ 10 + ((573 / 386) : ℂ) * ζ ^ 13 - ((11 / 193) : ℂ) * ζ ^ 15 + ((237 / 386) : ℂ) * ζ ^ 18 + ((11 / 193) : ℂ) * ζ ^ 19 + ((73 / 193) : ℂ) * ζ ^ 20 + ((633 / 386) : ℂ) * ζ ^ 22 - ((181 / 193) : ℂ) * ζ ^ 23 - ((73 / 193) : ℂ) * ζ ^ 24 + ((272 / 193) : ℂ) * ζ ^ 25 + ((633 / 386) : ℂ) * ζ ^ 26 - ((695 / 386) : ℂ) * ζ ^ 28 - ((272 / 193) : ℂ) * ζ ^ 29 - ((633 / 386) : ℂ) * ζ ^ 30)
private theorem row13_generatorB_mul_eigenbasis_4_3 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        4 3 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        4 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((1767 / 386) : ℂ) - (11 : ℂ) * ζ ^ 3 - ((1767 / 386) : ℂ) * ζ ^ 4 + ((4501 / 386) : ℂ) * ζ ^ 5 + ((925 / 386) : ℂ) * ζ ^ 6 + ((339 / 193) : ℂ) * ζ ^ 8 - ((4501 / 386) : ℂ) * ζ ^ 9 - ((725 / 386) : ℂ) * ζ ^ 10 + ((749 / 386) : ℂ) * ζ ^ 13 + ((825 / 193) : ℂ) * ζ ^ 14 + ((886 / 193) : ℂ) * ζ ^ 15 - ((42 / 193) : ℂ) * ζ ^ 18 - ((886 / 193) : ℂ) * ζ ^ 19 - ((303 / 386) : ℂ) * ζ ^ 20 - ((925 / 386) : ℂ) * ζ ^ 22 + ((243 / 193) : ℂ) * ζ ^ 23 + ((303 / 386) : ℂ) * ζ ^ 24 - ((2933 / 386) : ℂ) * ζ ^ 25 - ((925 / 386) : ℂ) * ζ ^ 26 + ((11 / 193) : ℂ) * ζ ^ 28 + ((2933 / 386) : ℂ) * ζ ^ 29 + ((925 / 386) : ℂ) * ζ ^ 30 - ζ ^ 33 - ζ ^ 35 + ζ ^ 39 - ζ ^ 43 - ζ ^ 45 + ζ ^ 49 - ζ ^ 53)
private theorem row13_generatorB_mul_eigenbasis_4_4 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        4 4 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        4 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((6477 / 2123) : ℂ) - ((391 / 386) : ℂ) * ζ ^ 3 - ((6477 / 2123) : ℂ) * ζ ^ 4 - ((7097 / 4246) : ℂ) * ζ ^ 5 - ((997 / 4246) : ℂ) * ζ ^ 6 + ((9497 / 2123) : ℂ) * ζ ^ 8 + ((7097 / 4246) : ℂ) * ζ ^ 9 - ((13543 / 4246) : ℂ) * ζ ^ 10 - ((4133 / 4246) : ℂ) * ζ ^ 13 + ((6273 / 2123) : ℂ) * ζ ^ 14 + ((4371 / 2123) : ℂ) * ζ ^ 15 - ((12677 / 4246) : ℂ) * ζ ^ 18 - ((4371 / 2123) : ℂ) * ζ ^ 19 + ((3184 / 2123) : ℂ) * ζ ^ 20 + ((997 / 4246) : ℂ) * ζ ^ 22 + ((1564 / 2123) : ℂ) * ζ ^ 23 - ((3184 / 2123) : ℂ) * ζ ^ 24 - ((675 / 2123) : ℂ) * ζ ^ 25 + ((997 / 4246) : ℂ) * ζ ^ 26 + ((2285 / 4246) : ℂ) * ζ ^ 28 + ((675 / 2123) : ℂ) * ζ ^ 29 - ((997 / 4246) : ℂ) * ζ ^ 30 - ζ ^ 45 + ζ ^ 49 - ζ ^ 53 - ζ ^ 65 + ζ ^ 69 - ζ ^ 73)
private theorem row13_generatorB_mul_eigenbasis_4_5 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        4 5 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        4 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((2003 / 2123) : ℂ) + ((3793 / 2123) : ℂ) * ζ ^ 3 + ((2003 / 2123) : ℂ) * ζ ^ 4 - ((357 / 2123) : ℂ) * ζ ^ 5 + ((4068 / 2123) : ℂ) * ζ ^ 6 - ((297 / 193) : ℂ) * ζ ^ 8 + ((357 / 2123) : ℂ) * ζ ^ 9 + ((411 / 2123) : ℂ) * ζ ^ 10 - ((542 / 2123) : ℂ) * ζ ^ 13 + ((3657 / 2123) : ℂ) * ζ ^ 14 + ((4160 / 2123) : ℂ) * ζ ^ 15 + ((53 / 193) : ℂ) * ζ ^ 18 - ((4160 / 2123) : ℂ) * ζ ^ 19 - ((2660 / 2123) : ℂ) * ζ ^ 20 - ((4068 / 2123) : ℂ) * ζ ^ 22 + ((1789 / 2123) : ℂ) * ζ ^ 23 + ((2660 / 2123) : ℂ) * ζ ^ 24 - ((4040 / 2123) : ℂ) * ζ ^ 25 - ((4068 / 2123) : ℂ) * ζ ^ 26 + ((1660 / 2123) : ℂ) * ζ ^ 28 + ((4040 / 2123) : ℂ) * ζ ^ 29 + ((4068 / 2123) : ℂ) * ζ ^ 30)
private theorem row13_generatorB_mul_eigenbasis_5_0 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        5 0 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        5 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((177 / 386) : ℂ) - ((744 / 193) : ℂ) * ζ ^ 3 + ((177 / 386) : ℂ) * ζ ^ 4 - ((280 / 193) : ℂ) * ζ ^ 5 + ((35 / 386) : ℂ) * ζ ^ 6 + ((251 / 386) : ℂ) * ζ ^ 8 + ((280 / 193) : ℂ) * ζ ^ 9 + ((145 / 386) : ℂ) * ζ ^ 10 + ((14 / 193) : ℂ) * ζ ^ 13 - ((55 / 193) : ℂ) * ζ ^ 14 + ((3 / 386) : ℂ) * ζ ^ 15 - ((1141 / 386) : ℂ) * ζ ^ 18 - ((3 / 386) : ℂ) * ζ ^ 19 - ((457 / 386) : ℂ) * ζ ^ 20 - ((35 / 386) : ℂ) * ζ ^ 22 + ((605 / 386) : ℂ) * ζ ^ 23 + ((457 / 386) : ℂ) * ζ ^ 24 + ((229 / 193) : ℂ) * ζ ^ 25 - ((35 / 386) : ℂ) * ζ ^ 26 + ((91 / 193) : ℂ) * ζ ^ 28 - ((229 / 193) : ℂ) * ζ ^ 29 + ((35 / 386) : ℂ) * ζ ^ 30)
private theorem row13_generatorB_mul_eigenbasis_5_1 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        5 1 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        5 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((126 / 193) : ℂ) + ((449 / 579) : ℂ) * ζ ^ 3 + ((126 / 193) : ℂ) * ζ ^ 4 + ((695 / 579) : ℂ) * ζ ^ 5 - ((28 / 193) : ℂ) * ζ ^ 6 - ((1403 / 579) : ℂ) * ζ ^ 8 - ((695 / 579) : ℂ) * ζ ^ 9 - ((502 / 579) : ℂ) * ζ ^ 10 + ((997 / 579) : ℂ) * ζ ^ 13 + ((418 / 579) : ℂ) * ζ ^ 14 - ((1036 / 579) : ℂ) * ζ ^ 15 - ((925 / 579) : ℂ) * ζ ^ 18 + ((1036 / 579) : ℂ) * ζ ^ 19 - ((884 / 579) : ℂ) * ζ ^ 20 + ((28 / 193) : ℂ) * ζ ^ 22 - ζ ^ 23 + ((884 / 579) : ℂ) * ζ ^ 24 + ((211 / 193) : ℂ) * ζ ^ 25 + ((28 / 193) : ℂ) * ζ ^ 26 - ((195 / 193) : ℂ) * ζ ^ 28 - ((211 / 193) : ℂ) * ζ ^ 29 - ((28 / 193) : ℂ) * ζ ^ 30)
private theorem row13_generatorB_mul_eigenbasis_5_2 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        5 2 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        5 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((849 / 386) : ℂ) - ((118 / 193) : ℂ) * ζ ^ 3 + ((849 / 386) : ℂ) * ζ ^ 4 + ((172 / 193) : ℂ) * ζ ^ 5 + ((311 / 386) : ℂ) * ζ ^ 6 - ((581 / 386) : ℂ) * ζ ^ 8 - ((172 / 193) : ℂ) * ζ ^ 9 + ((311 / 386) : ℂ) * ζ ^ 10 + ((221 / 193) : ℂ) * ζ ^ 13 - ((631 / 386) : ℂ) * ζ ^ 15 - ((475 / 386) : ℂ) * ζ ^ 18 + ((631 / 386) : ℂ) * ζ ^ 19 - ((655 / 386) : ℂ) * ζ ^ 20 - ((311 / 386) : ℂ) * ζ ^ 22 - ((31 / 386) : ℂ) * ζ ^ 23 + ((655 / 386) : ℂ) * ζ ^ 24 - ((94 / 193) : ℂ) * ζ ^ 25 - ((311 / 386) : ℂ) * ζ ^ 26 + ((91 / 193) : ℂ) * ζ ^ 28 + ((94 / 193) : ℂ) * ζ ^ 29 + ((311 / 386) : ℂ) * ζ ^ 30)
private theorem row13_generatorB_mul_eigenbasis_5_3 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        5 3 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        5 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((1298 / 193) : ℂ) + (5 : ℂ) * ζ ^ 3 + ((1298 / 193) : ℂ) * ζ ^ 4 + ((547 / 193) : ℂ) * ζ ^ 5 - ((463 / 386) : ℂ) * ζ ^ 6 - ((848 / 193) : ℂ) * ζ ^ 8 - ((547 / 193) : ℂ) * ζ ^ 9 - ((348 / 193) : ℂ) * ζ ^ 10 + ((429 / 193) : ℂ) * ζ ^ 13 + ((233 / 386) : ℂ) * ζ ^ 14 - ((485 / 193) : ℂ) * ζ ^ 15 - ((181 / 386) : ℂ) * ζ ^ 18 + ((485 / 193) : ℂ) * ζ ^ 19 + ((835 / 193) : ℂ) * ζ ^ 20 + ((463 / 386) : ℂ) * ζ ^ 22 - ((531 / 193) : ℂ) * ζ ^ 23 - ((835 / 193) : ℂ) * ζ ^ 24 - ((80 / 193) : ℂ) * ζ ^ 25 + ((463 / 386) : ℂ) * ζ ^ 26 + ((631 / 386) : ℂ) * ζ ^ 28 + ((80 / 193) : ℂ) * ζ ^ 29 - ((463 / 386) : ℂ) * ζ ^ 30 - ζ ^ 35 + ζ ^ 39 - ζ ^ 43)
private theorem row13_generatorB_mul_eigenbasis_5_4 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        5 4 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        5 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((665 / 4246) : ℂ) - ((3153 / 2123) : ℂ) * ζ ^ 3 + ((665 / 4246) : ℂ) * ζ ^ 4 + ((7000 / 2123) : ℂ) * ζ ^ 5 + ((749 / 4246) : ℂ) * ζ ^ 6 - ((3899 / 4246) : ℂ) * ζ ^ 8 - ((7000 / 2123) : ℂ) * ζ ^ 9 + ((1659 / 4246) : ℂ) * ζ ^ 10 + ((5327 / 2123) : ℂ) * ζ ^ 13 - ((455 / 2123) : ℂ) * ζ ^ 14 - ((7673 / 4246) : ℂ) * ζ ^ 15 - ((119 / 4246) : ℂ) * ζ ^ 18 + ((7673 / 4246) : ℂ) * ζ ^ 19 - ((1599 / 4246) : ℂ) * ζ ^ 20 - ((749 / 4246) : ℂ) * ζ ^ 22 - ((4941 / 4246) : ℂ) * ζ ^ 23 + ((1599 / 4246) : ℂ) * ζ ^ 24 + ((317 / 2123) : ℂ) * ζ ^ 25 - ((749 / 4246) : ℂ) * ζ ^ 26 + ((788 / 2123) : ℂ) * ζ ^ 28 - ((317 / 2123) : ℂ) * ζ ^ 29 + ((749 / 4246) : ℂ) * ζ ^ 30)
private theorem row13_generatorB_mul_eigenbasis_5_5 :
    (alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis)
        5 5 =
      (alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal)
        5 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row13_matrixB,
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13GeneratorBDiagonal,
      alternatingSixAmbientRow13GeneratorBEigenvalue,
      alternatingSixAmbientRow13EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((2933 / 2123) : ℂ) + ((4421 / 2123) : ℂ) * ζ ^ 3 - ((2933 / 2123) : ℂ) * ζ ^ 4 + ((2174 / 2123) : ℂ) * ζ ^ 5 - ((2263 / 2123) : ℂ) * ζ ^ 6 + ((3279 / 2123) : ℂ) * ζ ^ 8 - ((2174 / 2123) : ℂ) * ζ ^ 9 - ((4801 / 2123) : ℂ) * ζ ^ 10 + ((684 / 2123) : ℂ) * ζ ^ 13 + ((2538 / 2123) : ℂ) * ζ ^ 14 - ((870 / 2123) : ℂ) * ζ ^ 15 - ((2868 / 2123) : ℂ) * ζ ^ 18 + ((870 / 2123) : ℂ) * ζ ^ 19 + ((3854 / 2123) : ℂ) * ζ ^ 20 + ((2263 / 2123) : ℂ) * ζ ^ 22 - ((807 / 2123) : ℂ) * ζ ^ 23 - ((3854 / 2123) : ℂ) * ζ ^ 24 + ((329 / 2123) : ℂ) * ζ ^ 25 + ((2263 / 2123) : ℂ) * ζ ^ 26 - ((375 / 2123) : ℂ) * ζ ^ 28 - ((329 / 2123) : ℂ) * ζ ^ 29 - ((2263 / 2123) : ℂ) * ζ ^ 30 - ζ ^ 45 + ζ ^ 49 - ζ ^ 53 - ζ ^ 65 + ζ ^ 69 - ζ ^ 73)
/-- The checked row 13 basis diagonalizes the second
generator. -/
theorem alternatingSixAmbientRow13GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row13_matrixB *
        alternatingSixAmbientRow13Eigenbasis =
      alternatingSixAmbientRow13Eigenbasis *
        alternatingSixAmbientRow13GeneratorBDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row13_generatorB_mul_eigenbasis_0_0
  · exact row13_generatorB_mul_eigenbasis_0_1
  · exact row13_generatorB_mul_eigenbasis_0_2
  · exact row13_generatorB_mul_eigenbasis_0_3
  · exact row13_generatorB_mul_eigenbasis_0_4
  · exact row13_generatorB_mul_eigenbasis_0_5
  · exact row13_generatorB_mul_eigenbasis_1_0
  · exact row13_generatorB_mul_eigenbasis_1_1
  · exact row13_generatorB_mul_eigenbasis_1_2
  · exact row13_generatorB_mul_eigenbasis_1_3
  · exact row13_generatorB_mul_eigenbasis_1_4
  · exact row13_generatorB_mul_eigenbasis_1_5
  · exact row13_generatorB_mul_eigenbasis_2_0
  · exact row13_generatorB_mul_eigenbasis_2_1
  · exact row13_generatorB_mul_eigenbasis_2_2
  · exact row13_generatorB_mul_eigenbasis_2_3
  · exact row13_generatorB_mul_eigenbasis_2_4
  · exact row13_generatorB_mul_eigenbasis_2_5
  · exact row13_generatorB_mul_eigenbasis_3_0
  · exact row13_generatorB_mul_eigenbasis_3_1
  · exact row13_generatorB_mul_eigenbasis_3_2
  · exact row13_generatorB_mul_eigenbasis_3_3
  · exact row13_generatorB_mul_eigenbasis_3_4
  · exact row13_generatorB_mul_eigenbasis_3_5
  · exact row13_generatorB_mul_eigenbasis_4_0
  · exact row13_generatorB_mul_eigenbasis_4_1
  · exact row13_generatorB_mul_eigenbasis_4_2
  · exact row13_generatorB_mul_eigenbasis_4_3
  · exact row13_generatorB_mul_eigenbasis_4_4
  · exact row13_generatorB_mul_eigenbasis_4_5
  · exact row13_generatorB_mul_eigenbasis_5_0
  · exact row13_generatorB_mul_eigenbasis_5_1
  · exact row13_generatorB_mul_eigenbasis_5_2
  · exact row13_generatorB_mul_eigenbasis_5_3
  · exact row13_generatorB_mul_eigenbasis_5_4
  · exact row13_generatorB_mul_eigenbasis_5_5


private theorem row13_transformedGeneratorA_0_0 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        0 0 =
      alternatingSixAmbientRow13TransformedGeneratorA
        0 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((155 / 772) : ℂ) - ((1763 / 772) : ℂ) * ζ ^ 3 - ((155 / 772) : ℂ) * ζ ^ 4 - ((1259 / 386) : ℂ) * ζ ^ 5 - ((1239 / 772) : ℂ) * ζ ^ 6 - ((27253 / 1544) : ℂ) * ζ ^ 8 + ((4507 / 386) : ℂ) * ζ ^ 9 - ((2907 / 1544) : ℂ) * ζ ^ 10 - ((1263 / 386) : ℂ) * ζ ^ 11 + ((12141 / 1544) : ℂ) * ζ ^ 13 + ((429 / 1544) : ℂ) * ζ ^ 14 - ((5673 / 1544) : ℂ) * ζ ^ 15 + ((15389 / 1544) : ℂ) * ζ ^ 16 + ((1624 / 193) : ℂ) * ζ ^ 17 + ((15275 / 1544) : ℂ) * ζ ^ 18 + ((621 / 1544) : ℂ) * ζ ^ 19 + ((7535 / 1544) : ℂ) * ζ ^ 20 - ((6291 / 772) : ℂ) * ζ ^ 21 + ((1239 / 772) : ℂ) * ζ ^ 22 - ((1947 / 1544) : ℂ) * ζ ^ 23 + ((3927 / 772) : ℂ) * ζ ^ 24 - ((42553 / 1544) : ℂ) * ζ ^ 25 - ((6211 / 1544) : ℂ) * ζ ^ 26 + ((1263 / 386) : ℂ) * ζ ^ 27 + ((6985 / 1544) : ℂ) * ζ ^ 28 - ((47981 / 1544) : ℂ) * ζ ^ 29 + ((3067 / 1544) : ℂ) * ζ ^ 30 + ((14679 / 1544) : ℂ) * ζ ^ 31 - ((15389 / 1544) : ℂ) * ζ ^ 32 + ((11647 / 1544) : ℂ) * ζ ^ 33 - ((7117 / 772) : ℂ) * ζ ^ 34 + ((13651 / 1544) : ℂ) * ζ ^ 35 - ((8197 / 772) : ℂ) * ζ ^ 36 + ((19283 / 772) : ℂ) * ζ ^ 37 + ((939 / 772) : ℂ) * ζ ^ 38 - ((2269 / 386) : ℂ) * ζ ^ 39 + ((10123 / 1544) : ℂ) * ζ ^ 40 + ((19283 / 772) : ℂ) * ζ ^ 41 + ((8689 / 1544) : ℂ) * ζ ^ 42 - ((10693 / 1544) : ℂ) * ζ ^ 43 + ((4261 / 1544) : ℂ) * ζ ^ 44 + ((13137 / 772) : ℂ) * ζ ^ 45 + ((8689 / 1544) : ℂ) * ζ ^ 46 - ((9627 / 1544) : ℂ) * ζ ^ 47 - ((768 / 193) : ℂ) * ζ ^ 48 - ((1609 / 193) : ℂ) * ζ ^ 49 - ((1294 / 193) : ℂ) * ζ ^ 50 - ((9627 / 1544) : ℂ) * ζ ^ 51 + ((1005 / 1544) : ℂ) * ζ ^ 52 - ((31283 / 1544) : ℂ) * ζ ^ 53 + ((1663 / 1544) : ℂ) * ζ ^ 54 - ((1085 / 772) : ℂ) * ζ ^ 55 + ((1005 / 1544) : ℂ) * ζ ^ 56 - ((1624 / 193) : ℂ) * ζ ^ 57 + ((243 / 1544) : ℂ) * ζ ^ 58 + ((11797 / 1544) : ℂ) * ζ ^ 59 - ((1005 / 1544) : ℂ) * ζ ^ 60 + ((1624 / 193) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_0_1 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        0 1 =
      alternatingSixAmbientRow13TransformedGeneratorA
        0 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((129 / 193) : ℂ) - ((1928 / 579) : ℂ) * ζ ^ 3 - ((129 / 193) : ℂ) * ζ ^ 4 - ((929 / 1158) : ℂ) * ζ ^ 5 + ((4013 / 2316) : ℂ) * ζ ^ 6 - ((5333 / 1158) : ℂ) * ζ ^ 8 + ((532 / 579) : ℂ) * ζ ^ 9 + ((1699 / 772) : ℂ) * ζ ^ 10 - ((308 / 579) : ℂ) * ζ ^ 11 + ((131 / 1158) : ℂ) * ζ ^ 13 - ((271 / 579) : ℂ) * ζ ^ 14 - ((2449 / 1158) : ℂ) * ζ ^ 15 + ((6019 / 772) : ℂ) * ζ ^ 16 + ((45 / 386) : ℂ) * ζ ^ 17 - ((6529 / 2316) : ℂ) * ζ ^ 18 + ((611 / 386) : ℂ) * ζ ^ 19 + ((10201 / 2316) : ℂ) * ζ ^ 20 - ((1583 / 2316) : ℂ) * ζ ^ 21 - ((4013 / 2316) : ℂ) * ζ ^ 22 + ((887 / 772) : ℂ) * ζ ^ 23 + ((1964 / 579) : ℂ) * ζ ^ 24 - ((2756 / 579) : ℂ) * ζ ^ 25 + ((2671 / 579) : ℂ) * ζ ^ 26 + ((308 / 579) : ℂ) * ζ ^ 27 - ((9281 / 1158) : ℂ) * ζ ^ 28 + ((2607 / 772) : ℂ) * ζ ^ 29 + ((11165 / 1158) : ℂ) * ζ ^ 30 - ((2605 / 1158) : ℂ) * ζ ^ 31 - ((6019 / 772) : ℂ) * ζ ^ 32 - ((808 / 579) : ℂ) * ζ ^ 33 - ((905 / 579) : ℂ) * ζ ^ 34 + ((8897 / 2316) : ℂ) * ζ ^ 35 - ((2083 / 386) : ℂ) * ζ ^ 36 + ((11 / 12) : ℂ) * ζ ^ 37 - ((2225 / 1158) : ℂ) * ζ ^ 38 - ((16571 / 2316) : ℂ) * ζ ^ 39 + ((1969 / 772) : ℂ) * ζ ^ 40 + ((11 / 12) : ℂ) * ζ ^ 41 - ((4899 / 772) : ℂ) * ζ ^ 42 + ((1223 / 1158) : ℂ) * ζ ^ 43 + ((5903 / 772) : ℂ) * ζ ^ 44 - ((1087 / 1158) : ℂ) * ζ ^ 45 - ((4899 / 772) : ℂ) * ζ ^ 46 + ((3221 / 1158) : ℂ) * ζ ^ 47 + ((8041 / 2316) : ℂ) * ζ ^ 48 + ((377 / 772) : ℂ) * ζ ^ 49 + ((512 / 193) : ℂ) * ζ ^ 50 + ((3221 / 1158) : ℂ) * ζ ^ 51 - ((1853 / 772) : ℂ) * ζ ^ 52 - ((155 / 579) : ℂ) * ζ ^ 53 + ((2851 / 772) : ℂ) * ζ ^ 54 - ((710 / 579) : ℂ) * ζ ^ 55 - ((1853 / 772) : ℂ) * ζ ^ 56 - ((45 / 386) : ℂ) * ζ ^ 57 + ((1575 / 772) : ℂ) * ζ ^ 58 - ((1801 / 1158) : ℂ) * ζ ^ 59 + ((1853 / 772) : ℂ) * ζ ^ 60 + ((45 / 386) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_0_2 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        0 2 =
      alternatingSixAmbientRow13TransformedGeneratorA
        0 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((1115 / 772) : ℂ) - ((1345 / 772) : ℂ) * ζ ^ 3 - ((1115 / 772) : ℂ) * ζ ^ 4 - ((4233 / 772) : ℂ) * ζ ^ 5 + ((1824 / 193) : ℂ) * ζ ^ 6 - ((18297 / 1544) : ℂ) * ζ ^ 8 + ((7731 / 772) : ℂ) * ζ ^ 9 + ((8619 / 1544) : ℂ) * ζ ^ 10 + ((119 / 193) : ℂ) * ζ ^ 11 + ((7477 / 1544) : ℂ) * ζ ^ 13 + ((5973 / 1544) : ℂ) * ζ ^ 14 + ((4451 / 1544) : ℂ) * ζ ^ 15 + ((8601 / 1544) : ℂ) * ζ ^ 16 + ((1749 / 386) : ℂ) * ζ ^ 17 + ((625 / 1544) : ℂ) * ζ ^ 18 - ((3499 / 1544) : ℂ) * ζ ^ 19 + ((4855 / 1544) : ℂ) * ζ ^ 20 - ((2619 / 772) : ℂ) * ζ ^ 21 - ((1824 / 193) : ℂ) * ζ ^ 22 - ((5595 / 1544) : ℂ) * ζ ^ 23 + ((1873 / 772) : ℂ) * ζ ^ 24 - ((28291 / 1544) : ℂ) * ζ ^ 25 - ((14309 / 1544) : ℂ) * ζ ^ 26 - ((119 / 193) : ℂ) * ζ ^ 27 - ((609 / 1544) : ℂ) * ζ ^ 28 - ((18923 / 1544) : ℂ) * ζ ^ 29 + ((7729 / 1544) : ℂ) * ζ ^ 30 + ((5559 / 1544) : ℂ) * ζ ^ 31 - ((8601 / 1544) : ℂ) * ζ ^ 32 + ((8961 / 1544) : ℂ) * ζ ^ 33 + ((3573 / 772) : ℂ) * ζ ^ 34 + ((17211 / 1544) : ℂ) * ζ ^ 35 - ((3607 / 772) : ℂ) * ζ ^ 36 + ((9615 / 772) : ℂ) * ζ ^ 37 + ((1885 / 772) : ℂ) * ζ ^ 38 - ((2437 / 386) : ℂ) * ζ ^ 39 + ((4723 / 1544) : ℂ) * ζ ^ 40 + ((9615 / 772) : ℂ) * ζ ^ 41 - ((283 / 1544) : ℂ) * ζ ^ 42 - ((9423 / 1544) : ℂ) * ζ ^ 43 + ((5265 / 1544) : ℂ) * ζ ^ 44 + ((3191 / 386) : ℂ) * ζ ^ 45 - ((283 / 1544) : ℂ) * ζ ^ 46 - ((6511 / 1544) : ℂ) * ζ ^ 47 - ((236 / 193) : ℂ) * ζ ^ 48 - ((2005 / 772) : ℂ) * ζ ^ 49 - ((173 / 386) : ℂ) * ζ ^ 50 - ((6511 / 1544) : ℂ) * ζ ^ 51 - ((1387 / 1544) : ℂ) * ζ ^ 52 - ((13875 / 1544) : ℂ) * ζ ^ 53 + ((975 / 1544) : ℂ) * ζ ^ 54 - ((313 / 386) : ℂ) * ζ ^ 55 - ((1387 / 1544) : ℂ) * ζ ^ 56 - ((1749 / 386) : ℂ) * ζ ^ 57 + ((243 / 1544) : ℂ) * ζ ^ 58 + ((7763 / 1544) : ℂ) * ζ ^ 59 + ((1387 / 1544) : ℂ) * ζ ^ 60 + ((1749 / 386) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_0_3 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        0 3 =
      alternatingSixAmbientRow13TransformedGeneratorA
        0 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((697 / 386) : ℂ) - ((7907 / 772) : ℂ) * ζ ^ 3 - ((697 / 386) : ℂ) * ζ ^ 4 - ((4163 / 386) : ℂ) * ζ ^ 5 + ((43 / 2) : ℂ) * ζ ^ 6 - ((13463 / 772) : ℂ) * ζ ^ 8 + ((6775 / 772) : ℂ) * ζ ^ 9 + ((35977 / 1544) : ℂ) * ζ ^ 10 + ((5993 / 1544) : ℂ) * ζ ^ 11 - ((458 / 193) : ℂ) * ζ ^ 13 - ((2781 / 1544) : ℂ) * ζ ^ 14 + ((773 / 1544) : ℂ) * ζ ^ 15 + ((2307 / 193) : ℂ) * ζ ^ 16 - ((1551 / 772) : ℂ) * ζ ^ 17 - ((39267 / 1544) : ℂ) * ζ ^ 18 + ((1305 / 386) : ℂ) * ζ ^ 19 + ((45 / 1544) : ℂ) * ζ ^ 20 - ((2255 / 1544) : ℂ) * ζ ^ 21 - ((43 / 2) : ℂ) * ζ ^ 22 + ((362 / 193) : ℂ) * ζ ^ 23 + ((18411 / 1544) : ℂ) * ζ ^ 24 + ((14903 / 1544) : ℂ) * ζ ^ 25 - ((13475 / 772) : ℂ) * ζ ^ 26 - ((5993 / 1544) : ℂ) * ζ ^ 27 + ((10149 / 772) : ℂ) * ζ ^ 28 + ((727 / 772) : ℂ) * ζ ^ 29 + ((4563 / 1544) : ℂ) * ζ ^ 30 - ((9879 / 1544) : ℂ) * ζ ^ 31 - ((2307 / 193) : ℂ) * ζ ^ 32 + ((1894 / 193) : ℂ) * ζ ^ 33 + ((34879 / 1544) : ℂ) * ζ ^ 34 + ((1305 / 386) : ℂ) * ζ ^ 35 - ((31095 / 1544) : ℂ) * ζ ^ 36 - ((3949 / 1544) : ℂ) * ζ ^ 37 + ((13069 / 772) : ℂ) * ζ ^ 38 - ((3113 / 1544) : ℂ) * ζ ^ 39 + ((16771 / 1544) : ℂ) * ζ ^ 40 - ((3949 / 1544) : ℂ) * ζ ^ 41 - ((3123 / 772) : ℂ) * ζ ^ 42 - ((5391 / 1544) : ℂ) * ζ ^ 43 - ((5477 / 772) : ℂ) * ζ ^ 44 - ((3765 / 772) : ℂ) * ζ ^ 45 - ((3123 / 772) : ℂ) * ζ ^ 46 + ((1943 / 772) : ℂ) * ζ ^ 47 - ((989 / 386) : ℂ) * ζ ^ 48 - ((929 / 1544) : ℂ) * ζ ^ 49 + ((12695 / 1544) : ℂ) * ζ ^ 50 + ((1943 / 772) : ℂ) * ζ ^ 51 + ((12639 / 1544) : ℂ) * ζ ^ 52 + ((1093 / 386) : ℂ) * ζ ^ 53 - ((6449 / 1544) : ℂ) * ζ ^ 54 - ((3927 / 1544) : ℂ) * ζ ^ 55 + ((12639 / 1544) : ℂ) * ζ ^ 56 + ((1551 / 772) : ℂ) * ζ ^ 57 - ((4963 / 1544) : ℂ) * ζ ^ 58 + ((41 / 1544) : ℂ) * ζ ^ 59 - ((12639 / 1544) : ℂ) * ζ ^ 60 - ((1551 / 772) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_0_4 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        0 4 =
      alternatingSixAmbientRow13TransformedGeneratorA
        0 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((623 / 8492) : ℂ) - ((18827 / 4246) : ℂ) * ζ ^ 3 - ((623 / 8492) : ℂ) * ζ ^ 4 - ((65 / 193) : ℂ) * ζ ^ 5 + ((15475 / 8492) : ℂ) * ζ ^ 6 - ((49883 / 16984) : ℂ) * ζ ^ 8 + ((1413 / 4246) : ℂ) * ζ ^ 9 + ((86997 / 16984) : ℂ) * ζ ^ 10 - ((13269 / 8492) : ℂ) * ζ ^ 11 + ((10319 / 16984) : ℂ) * ζ ^ 13 - ((56047 / 16984) : ℂ) * ζ ^ 14 - ((58943 / 16984) : ℂ) * ζ ^ 15 + ((18875 / 16984) : ℂ) * ζ ^ 16 - ((17 / 4246) : ℂ) * ζ ^ 17 - ((54035 / 16984) : ℂ) * ζ ^ 18 + ((32405 / 16984) : ℂ) * ζ ^ 19 - ((6419 / 16984) : ℂ) * ζ ^ 20 - ((287 / 2123) : ℂ) * ζ ^ 21 - ((15475 / 8492) : ℂ) * ζ ^ 22 - ((17125 / 16984) : ℂ) * ζ ^ 23 + ((12647 / 8492) : ℂ) * ζ ^ 24 - ((47035 / 16984) : ℂ) * ζ ^ 25 + ((34801 / 16984) : ℂ) * ζ ^ 26 + ((13269 / 8492) : ℂ) * ζ ^ 27 - ((39867 / 16984) : ℂ) * ζ ^ 28 + ((45147 / 16984) : ℂ) * ζ ^ 29 + ((23103 / 16984) : ℂ) * ζ ^ 30 + ((64399 / 16984) : ℂ) * ζ ^ 31 - ((18875 / 16984) : ℂ) * ζ ^ 32 - ((18471 / 16984) : ℂ) * ζ ^ 33 + ((36799 / 8492) : ℂ) * ζ ^ 34 + ((176007 / 16984) : ℂ) * ζ ^ 35 - ((3775 / 2123) : ℂ) * ζ ^ 36 + ((270 / 2123) : ℂ) * ζ ^ 37 + ((10595 / 8492) : ℂ) * ζ ^ 38 - ((41171 / 4246) : ℂ) * ζ ^ 39 - ((3155 / 1544) : ℂ) * ζ ^ 40 + ((270 / 2123) : ℂ) * ζ ^ 41 - ((65751 / 16984) : ℂ) * ζ ^ 42 - ((6877 / 16984) : ℂ) * ζ ^ 43 + ((42255 / 16984) : ℂ) * ζ ^ 44 - ((9754 / 2123) : ℂ) * ζ ^ 45 - ((65751 / 16984) : ℂ) * ζ ^ 46 - ((37861 / 16984) : ℂ) * ζ ^ 47 + ((19189 / 8492) : ℂ) * ζ ^ 48 + ((9450 / 2123) : ℂ) * ζ ^ 49 + ((20283 / 4246) : ℂ) * ζ ^ 50 - ((37861 / 16984) : ℂ) * ζ ^ 51 + ((11325 / 16984) : ℂ) * ζ ^ 52 + ((22307 / 16984) : ℂ) * ζ ^ 53 - ((15381 / 16984) : ℂ) * ζ ^ 54 + ((4390 / 2123) : ℂ) * ζ ^ 55 + ((11325 / 16984) : ℂ) * ζ ^ 56 + ((17 / 4246) : ℂ) * ζ ^ 57 - ((837 / 1544) : ℂ) * ζ ^ 58 + ((2741 / 16984) : ℂ) * ζ ^ 59 - ((11325 / 16984) : ℂ) * ζ ^ 60 - ((17 / 4246) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_0_5 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        0 5 =
      alternatingSixAmbientRow13TransformedGeneratorA
        0 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((1269 / 4246) : ℂ) + ((1487 / 4246) : ℂ) * ζ ^ 3 - ((1269 / 4246) : ℂ) * ζ ^ 4 + ((7765 / 4246) : ℂ) * ζ ^ 5 - ((16829 / 4246) : ℂ) * ζ ^ 6 + ((34423 / 8492) : ℂ) * ζ ^ 8 - ((19009 / 4246) : ℂ) * ζ ^ 9 - ((6286 / 2123) : ℂ) * ζ ^ 10 - ((9359 / 8492) : ℂ) * ζ ^ 11 - ((6445 / 2123) : ℂ) * ζ ^ 13 - ((387 / 386) : ℂ) * ζ ^ 14 - ((16121 / 4246) : ℂ) * ζ ^ 15 - ((16641 / 4246) : ℂ) * ζ ^ 16 - ((5622 / 2123) : ℂ) * ζ ^ 17 - ((26481 / 8492) : ℂ) * ζ ^ 18 + ((22883 / 8492) : ℂ) * ζ ^ 19 - ((33969 / 8492) : ℂ) * ζ ^ 20 - ((571 / 2123) : ℂ) * ζ ^ 21 + ((16829 / 4246) : ℂ) * ζ ^ 22 + ((3045 / 4246) : ℂ) * ζ ^ 23 + ((687 / 8492) : ℂ) * ζ ^ 24 + ((19707 / 2123) : ℂ) * ζ ^ 25 + ((16103 / 2123) : ℂ) * ζ ^ 26 + ((9359 / 8492) : ℂ) * ζ ^ 27 + ((3302 / 2123) : ℂ) * ζ ^ 28 + ((13454 / 2123) : ℂ) * ζ ^ 29 + ((33445 / 8492) : ℂ) * ζ ^ 30 - ((21225 / 8492) : ℂ) * ζ ^ 31 + ((16641 / 4246) : ℂ) * ζ ^ 32 + ((708 / 193) : ℂ) * ζ ^ 33 - ((36349 / 8492) : ℂ) * ζ ^ 34 - ((9523 / 2123) : ℂ) * ζ ^ 35 + ((4688 / 2123) : ℂ) * ζ ^ 36 - ((10673 / 2123) : ℂ) * ζ ^ 37 - ((3809 / 4246) : ℂ) * ζ ^ 38 - ((1851 / 8492) : ℂ) * ζ ^ 39 - ((7394 / 2123) : ℂ) * ζ ^ 40 - ((10673 / 2123) : ℂ) * ζ ^ 41 - ((15377 / 4246) : ℂ) * ζ ^ 42 - ((521 / 2123) : ℂ) * ζ ^ 43 - ((4559 / 2123) : ℂ) * ζ ^ 44 - ((29751 / 4246) : ℂ) * ζ ^ 45 - ((15377 / 4246) : ℂ) * ζ ^ 46 + ((7646 / 2123) : ℂ) * ζ ^ 47 - ((7309 / 8492) : ℂ) * ζ ^ 48 + ((6121 / 4246) : ℂ) * ζ ^ 49 + ((107 / 44) : ℂ) * ζ ^ 50 + ((7646 / 2123) : ℂ) * ζ ^ 51 + ((7265 / 4246) : ℂ) * ζ ^ 52 + ((20659 / 4246) : ℂ) * ζ ^ 53 + ((10103 / 8492) : ℂ) * ζ ^ 54 - ((4243 / 2123) : ℂ) * ζ ^ 55 + ((7265 / 4246) : ℂ) * ζ ^ 56 + ((5622 / 2123) : ℂ) * ζ ^ 57 + ((1099 / 2123) : ℂ) * ζ ^ 58 - ((3403 / 2123) : ℂ) * ζ ^ 59 - ((7265 / 4246) : ℂ) * ζ ^ 60 - ((5622 / 2123) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_1_0 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        1 0 =
      alternatingSixAmbientRow13TransformedGeneratorA
        1 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((9 / 772) : ℂ) + ((3613 / 1544) : ℂ) * ζ ^ 3 - ((9 / 772) : ℂ) * ζ ^ 4 - ((1585 / 1544) : ℂ) * ζ ^ 5 - ((4823 / 1544) : ℂ) * ζ ^ 6 - ((3375 / 1544) : ℂ) * ζ ^ 8 + ((989 / 193) : ℂ) * ζ ^ 9 - ((3353 / 772) : ℂ) * ζ ^ 10 - ((2743 / 772) : ℂ) * ζ ^ 11 - ((120 / 193) : ℂ) * ζ ^ 13 + ((1883 / 1544) : ℂ) * ζ ^ 14 - ((7131 / 1544) : ℂ) * ζ ^ 15 + ((7749 / 1544) : ℂ) * ζ ^ 16 + ((6327 / 1544) : ℂ) * ζ ^ 17 + ((5549 / 1544) : ℂ) * ζ ^ 18 + ((1645 / 1544) : ℂ) * ζ ^ 19 + ((229 / 193) : ℂ) * ζ ^ 20 - ((1371 / 772) : ℂ) * ζ ^ 21 + ((4823 / 1544) : ℂ) * ζ ^ 22 - ((49 / 193) : ℂ) * ζ ^ 23 + ((5917 / 1544) : ℂ) * ζ ^ 24 - ((11515 / 772) : ℂ) * ζ ^ 25 + ((1899 / 386) : ℂ) * ζ ^ 26 + ((2743 / 772) : ℂ) * ζ ^ 27 - ((9515 / 1544) : ℂ) * ζ ^ 28 - ((8837 / 772) : ℂ) * ζ ^ 29 + ((1774 / 193) : ℂ) * ζ ^ 30 + ((5117 / 772) : ℂ) * ζ ^ 31 - ((7749 / 1544) : ℂ) * ζ ^ 32 + ((1829 / 772) : ℂ) * ζ ^ 33 - ((8121 / 772) : ℂ) * ζ ^ 34 + ((3607 / 772) : ℂ) * ζ ^ 35 - ((7033 / 1544) : ℂ) * ζ ^ 36 + ((3849 / 386) : ℂ) * ζ ^ 37 - ((3569 / 1544) : ℂ) * ζ ^ 38 - ((994 / 193) : ℂ) * ζ ^ 39 + ((3533 / 1544) : ℂ) * ζ ^ 40 + ((3849 / 386) : ℂ) * ζ ^ 41 - ((2773 / 1544) : ℂ) * ζ ^ 42 - ((2377 / 772) : ℂ) * ζ ^ 43 + ((1233 / 386) : ℂ) * ζ ^ 44 + ((18831 / 1544) : ℂ) * ζ ^ 45 - ((2773 / 1544) : ℂ) * ζ ^ 46 - ((1187 / 386) : ℂ) * ζ ^ 47 + ((215 / 193) : ℂ) * ζ ^ 48 - ((8919 / 1544) : ℂ) * ζ ^ 49 + ((661 / 1544) : ℂ) * ζ ^ 50 - ((1187 / 386) : ℂ) * ζ ^ 51 - ((179 / 386) : ℂ) * ζ ^ 52 - ((6515 / 772) : ℂ) * ζ ^ 53 + ((264 / 193) : ℂ) * ζ ^ 54 - ((219 / 772) : ℂ) * ζ ^ 55 - ((179 / 386) : ℂ) * ζ ^ 56 - ((6327 / 1544) : ℂ) * ζ ^ 57 + ((333 / 193) : ℂ) * ζ ^ 58 + ((2593 / 772) : ℂ) * ζ ^ 59 + ((179 / 386) : ℂ) * ζ ^ 60 + ((6327 / 1544) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_1_1 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        1 1 =
      alternatingSixAmbientRow13TransformedGeneratorA
        1 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((359 / 579) : ℂ) - ((3599 / 2316) : ℂ) * ζ ^ 3 - ((359 / 579) : ℂ) * ζ ^ 4 - ((1831 / 1158) : ℂ) * ζ ^ 5 + ((340 / 193) : ℂ) * ζ ^ 6 - ((2312 / 579) : ℂ) * ζ ^ 8 + ((335 / 193) : ℂ) * ζ ^ 9 + ((2015 / 579) : ℂ) * ζ ^ 10 - ((3869 / 2316) : ℂ) * ζ ^ 11 + ((2339 / 579) : ℂ) * ζ ^ 13 - ((995 / 579) : ℂ) * ζ ^ 14 - ((1435 / 193) : ℂ) * ζ ^ 15 + ((4661 / 772) : ℂ) * ζ ^ 16 + ((179 / 1158) : ℂ) * ζ ^ 17 - ((11711 / 2316) : ℂ) * ζ ^ 18 + ((13351 / 2316) : ℂ) * ζ ^ 19 + ((2207 / 579) : ℂ) * ζ ^ 20 - ((7015 / 2316) : ℂ) * ζ ^ 21 - ((340 / 193) : ℂ) * ζ ^ 22 + ((7297 / 2316) : ℂ) * ζ ^ 23 + ((5155 / 2316) : ℂ) * ζ ^ 24 - ((2737 / 579) : ℂ) * ζ ^ 25 + ((3727 / 2316) : ℂ) * ζ ^ 26 + ((3869 / 2316) : ℂ) * ζ ^ 27 - ((11545 / 2316) : ℂ) * ζ ^ 28 + ((595 / 772) : ℂ) * ζ ^ 29 + ((2935 / 2316) : ℂ) * ζ ^ 30 + ((1703 / 2316) : ℂ) * ζ ^ 31 - ((4661 / 772) : ℂ) * ζ ^ 32 + ((325 / 2316) : ℂ) * ζ ^ 33 + ((746 / 193) : ℂ) * ζ ^ 34 + ((35 / 12) : ℂ) * ζ ^ 35 - ((2925 / 386) : ℂ) * ζ ^ 36 + ((2577 / 772) : ℂ) * ζ ^ 37 + ((2191 / 1158) : ℂ) * ζ ^ 38 - ((6395 / 1158) : ℂ) * ζ ^ 39 - ((9883 / 2316) : ℂ) * ζ ^ 40 + ((2577 / 772) : ℂ) * ζ ^ 41 - ((7807 / 2316) : ℂ) * ζ ^ 42 - ((481 / 193) : ℂ) * ζ ^ 43 + ((20299 / 2316) : ℂ) * ζ ^ 44 - ((2569 / 772) : ℂ) * ζ ^ 45 - ((7807 / 2316) : ℂ) * ζ ^ 46 + ((361 / 386) : ℂ) * ζ ^ 47 + ((95 / 193) : ℂ) * ζ ^ 48 + ((352 / 579) : ℂ) * ζ ^ 49 + ((4423 / 579) : ℂ) * ζ ^ 50 + ((361 / 386) : ℂ) * ζ ^ 51 + ((1189 / 772) : ℂ) * ζ ^ 52 - ((947 / 1158) : ℂ) * ζ ^ 53 - ((3295 / 772) : ℂ) * ζ ^ 54 + ((507 / 386) : ℂ) * ζ ^ 55 + ((1189 / 772) : ℂ) * ζ ^ 56 - ((179 / 1158) : ℂ) * ζ ^ 57 - ((2105 / 2316) : ℂ) * ζ ^ 58 - ((434 / 193) : ℂ) * ζ ^ 59 - ((1189 / 772) : ℂ) * ζ ^ 60 + ((179 / 1158) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_1_2 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        1 2 =
      alternatingSixAmbientRow13TransformedGeneratorA
        1 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((1239 / 386) : ℂ) + ((2093 / 1544) : ℂ) * ζ ^ 3 - ((1239 / 386) : ℂ) * ζ ^ 4 + ((1655 / 1544) : ℂ) * ζ ^ 5 + ((5529 / 1544) : ℂ) * ζ ^ 6 - ((9359 / 1544) : ℂ) * ζ ^ 8 + ((443 / 193) : ℂ) * ζ ^ 9 - ((2025 / 772) : ℂ) * ζ ^ 10 - ((82 / 193) : ℂ) * ζ ^ 11 + ((2355 / 772) : ℂ) * ζ ^ 13 + ((9579 / 1544) : ℂ) * ζ ^ 14 - ((7467 / 1544) : ℂ) * ζ ^ 15 + ((8047 / 1544) : ℂ) * ζ ^ 16 + ((5199 / 1544) : ℂ) * ζ ^ 17 + ((6867 / 1544) : ℂ) * ζ ^ 18 + ((6811 / 1544) : ℂ) * ζ ^ 19 + ((1593 / 386) : ℂ) * ζ ^ 20 - ((2335 / 772) : ℂ) * ζ ^ 21 - ((5529 / 1544) : ℂ) * ζ ^ 22 - ((903 / 772) : ℂ) * ζ ^ 23 + ((1675 / 1544) : ℂ) * ζ ^ 24 - ((13867 / 772) : ℂ) * ζ ^ 25 - ((841 / 386) : ℂ) * ζ ^ 26 + ((82 / 193) : ℂ) * ζ ^ 27 - ((16909 / 1544) : ℂ) * ζ ^ 28 - ((4065 / 772) : ℂ) * ζ ^ 29 + ((1401 / 386) : ℂ) * ζ ^ 30 + ((1197 / 193) : ℂ) * ζ ^ 31 - ((8047 / 1544) : ℂ) * ζ ^ 32 + ((363 / 193) : ℂ) * ζ ^ 33 + ((1045 / 772) : ℂ) * ζ ^ 34 + ((9023 / 772) : ℂ) * ζ ^ 35 - ((4327 / 1544) : ℂ) * ζ ^ 36 + ((3767 / 386) : ℂ) * ζ ^ 37 + ((5311 / 1544) : ℂ) * ζ ^ 38 - ((4891 / 772) : ℂ) * ζ ^ 39 + ((1793 / 1544) : ℂ) * ζ ^ 40 + ((3767 / 386) : ℂ) * ζ ^ 41 - ((2165 / 1544) : ℂ) * ζ ^ 42 - ((3237 / 772) : ℂ) * ζ ^ 43 + ((4987 / 772) : ℂ) * ζ ^ 44 + ((3927 / 1544) : ℂ) * ζ ^ 45 - ((2165 / 1544) : ℂ) * ζ ^ 46 - ((1115 / 193) : ℂ) * ζ ^ 47 - ((307 / 772) : ℂ) * ζ ^ 48 + ((1801 / 1544) : ℂ) * ζ ^ 49 + ((1235 / 1544) : ℂ) * ζ ^ 50 - ((1115 / 193) : ℂ) * ζ ^ 51 - ((465 / 193) : ℂ) * ζ ^ 52 - ((4353 / 772) : ℂ) * ζ ^ 53 + ((465 / 772) : ℂ) * ζ ^ 54 + ((425 / 193) : ℂ) * ζ ^ 55 - ((465 / 193) : ℂ) * ζ ^ 56 - ((5199 / 1544) : ℂ) * ζ ^ 57 + ((333 / 193) : ℂ) * ζ ^ 58 + ((690 / 193) : ℂ) * ζ ^ 59 + ((465 / 193) : ℂ) * ζ ^ 60 + ((5199 / 1544) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_1_3 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        1 3 =
      alternatingSixAmbientRow13TransformedGeneratorA
        1 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((4529 / 1544) : ℂ) - ((2679 / 772) : ℂ) * ζ ^ 3 - ((4529 / 1544) : ℂ) * ζ ^ 4 - ((7285 / 1544) : ℂ) * ζ ^ 5 + ((2523 / 193) : ℂ) * ζ ^ 6 - ((15337 / 1544) : ℂ) * ζ ^ 8 + ((187 / 386) : ℂ) * ζ ^ 9 + ((11263 / 772) : ℂ) * ζ ^ 10 + ((1935 / 386) : ℂ) * ζ ^ 11 - ((2013 / 1544) : ℂ) * ζ ^ 13 - ((1171 / 772) : ℂ) * ζ ^ 14 - ((17425 / 1544) : ℂ) * ζ ^ 15 + ((153 / 772) : ℂ) * ζ ^ 16 - ((6537 / 1544) : ℂ) * ζ ^ 17 - ((2101 / 193) : ℂ) * ζ ^ 18 + ((25165 / 1544) : ℂ) * ζ ^ 19 - ((23485 / 1544) : ℂ) * ζ ^ 20 - ((633 / 772) : ℂ) * ζ ^ 21 - ((2523 / 193) : ℂ) * ζ ^ 22 + ((4507 / 386) : ℂ) * ζ ^ 23 + ((23791 / 1544) : ℂ) * ζ ^ 24 + ((3935 / 1544) : ℂ) * ζ ^ 25 - ((17155 / 1544) : ℂ) * ζ ^ 26 - ((1935 / 386) : ℂ) * ζ ^ 27 + ((6327 / 1544) : ℂ) * ζ ^ 28 + ((34021 / 1544) : ℂ) * ζ ^ 29 - ((137 / 193) : ℂ) * ζ ^ 30 - ((11409 / 772) : ℂ) * ζ ^ 31 - ((153 / 772) : ℂ) * ζ ^ 32 - ((171 / 1544) : ℂ) * ζ ^ 33 + ((24309 / 1544) : ℂ) * ζ ^ 34 + ((1095 / 193) : ℂ) * ζ ^ 35 - ((7585 / 1544) : ℂ) * ζ ^ 36 - ((1476 / 193) : ℂ) * ζ ^ 37 + ((11099 / 1544) : ℂ) * ζ ^ 38 - ((8049 / 772) : ℂ) * ζ ^ 39 + ((3653 / 772) : ℂ) * ζ ^ 40 - ((1476 / 193) : ℂ) * ζ ^ 41 - ((3029 / 1544) : ℂ) * ζ ^ 42 - ((4215 / 772) : ℂ) * ζ ^ 43 - ((14279 / 1544) : ℂ) * ζ ^ 44 - ((9041 / 1544) : ℂ) * ζ ^ 45 - ((3029 / 1544) : ℂ) * ζ ^ 46 + ((7539 / 772) : ℂ) * ζ ^ 47 - ((4205 / 1544) : ℂ) * ζ ^ 48 - ((5299 / 1544) : ℂ) * ζ ^ 49 + ((6353 / 1544) : ℂ) * ζ ^ 50 + ((7539 / 772) : ℂ) * ζ ^ 51 + ((7279 / 1544) : ℂ) * ζ ^ 52 + ((16667 / 1544) : ℂ) * ζ ^ 53 - ((831 / 386) : ℂ) * ζ ^ 54 - ((7089 / 772) : ℂ) * ζ ^ 55 + ((7279 / 1544) : ℂ) * ζ ^ 56 + ((6537 / 1544) : ℂ) * ζ ^ 57 - ((335 / 1544) : ℂ) * ζ ^ 58 - ((225 / 386) : ℂ) * ζ ^ 59 - ((7279 / 1544) : ℂ) * ζ ^ 60 - ((6537 / 1544) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_1_4 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        1 4 =
      alternatingSixAmbientRow13TransformedGeneratorA
        1 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((14139 / 8492) : ℂ) + ((11739 / 16984) : ℂ) * ζ ^ 3 + ((14139 / 8492) : ℂ) * ζ ^ 4 + ((34851 / 16984) : ℂ) * ζ ^ 5 - ((49523 / 16984) : ℂ) * ζ ^ 6 + ((36089 / 16984) : ℂ) * ζ ^ 8 - ((12459 / 8492) : ℂ) * ζ ^ 9 - ((898 / 193) : ℂ) * ζ ^ 10 - ((15325 / 8492) : ℂ) * ζ ^ 11 + ((5905 / 4246) : ℂ) * ζ ^ 13 + ((29501 / 16984) : ℂ) * ζ ^ 14 - ((92739 / 16984) : ℂ) * ζ ^ 15 - ((6055 / 16984) : ℂ) * ζ ^ 16 + ((903 / 1544) : ℂ) * ζ ^ 17 - ((25053 / 16984) : ℂ) * ζ ^ 18 + ((62089 / 16984) : ℂ) * ζ ^ 19 + ((11167 / 2123) : ℂ) * ζ ^ 20 - ((8047 / 8492) : ℂ) * ζ ^ 21 + ((49523 / 16984) : ℂ) * ζ ^ 22 - ((31399 / 8492) : ℂ) * ζ ^ 23 - ((95391 / 16984) : ℂ) * ζ ^ 24 + ((231 / 386) : ℂ) * ζ ^ 25 + ((11422 / 2123) : ℂ) * ζ ^ 26 + ((15325 / 8492) : ℂ) * ζ ^ 27 - ((99699 / 16984) : ℂ) * ζ ^ 28 - ((10732 / 2123) : ℂ) * ζ ^ 29 - ((1180 / 2123) : ℂ) * ζ ^ 30 + ((40969 / 8492) : ℂ) * ζ ^ 31 + ((6055 / 16984) : ℂ) * ζ ^ 32 + ((10597 / 8492) : ℂ) * ζ ^ 33 + ((885 / 8492) : ℂ) * ζ ^ 34 + ((8465 / 2123) : ℂ) * ζ ^ 35 - ((7065 / 16984) : ℂ) * ζ ^ 36 + ((4495 / 2123) : ℂ) * ζ ^ 37 + ((19709 / 16984) : ℂ) * ζ ^ 38 - ((23541 / 8492) : ℂ) * ζ ^ 39 - ((112713 / 16984) : ℂ) * ζ ^ 40 + ((4495 / 2123) : ℂ) * ζ ^ 41 - ((41853 / 16984) : ℂ) * ζ ^ 42 - ((21753 / 8492) : ℂ) * ζ ^ 43 + ((46769 / 8492) : ℂ) * ζ ^ 44 - ((3053 / 1544) : ℂ) * ζ ^ 45 - ((41853 / 16984) : ℂ) * ζ ^ 46 - ((6411 / 2123) : ℂ) * ζ ^ 47 - ((1933 / 4246) : ℂ) * ζ ^ 48 + ((37355 / 16984) : ℂ) * ζ ^ 49 + ((90647 / 16984) : ℂ) * ζ ^ 50 - ((6411 / 2123) : ℂ) * ζ ^ 51 + ((1640 / 2123) : ℂ) * ζ ^ 52 - ((2995 / 4246) : ℂ) * ζ ^ 53 - ((24397 / 8492) : ℂ) * ζ ^ 54 + ((5485 / 2123) : ℂ) * ζ ^ 55 + ((1640 / 2123) : ℂ) * ζ ^ 56 - ((903 / 1544) : ℂ) * ζ ^ 57 - ((2507 / 8492) : ℂ) * ζ ^ 58 + ((926 / 2123) : ℂ) * ζ ^ 59 - ((1640 / 2123) : ℂ) * ζ ^ 60 + ((903 / 1544) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_1_5 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        1 5 =
      alternatingSixAmbientRow13TransformedGeneratorA
        1 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((667 / 4246) : ℂ) - ((6081 / 8492) : ℂ) * ζ ^ 3 - ((667 / 4246) : ℂ) * ζ ^ 4 - ((7675 / 8492) : ℂ) * ζ ^ 5 - ((6373 / 8492) : ℂ) * ζ ^ 6 + ((23809 / 8492) : ℂ) * ζ ^ 8 - ((5315 / 2123) : ℂ) * ζ ^ 9 + ((6971 / 4246) : ℂ) * ζ ^ 10 + ((540 / 193) : ℂ) * ζ ^ 11 - ((33637 / 4246) : ℂ) * ζ ^ 13 - ((20315 / 8492) : ℂ) * ζ ^ 14 + ((5219 / 4246) : ℂ) * ζ ^ 15 - ((9060 / 2123) : ℂ) * ζ ^ 16 - ((28935 / 8492) : ℂ) * ζ ^ 17 - ((10155 / 4246) : ℂ) * ζ ^ 18 + ((6661 / 4246) : ℂ) * ζ ^ 19 - ((24507 / 8492) : ℂ) * ζ ^ 20 - ((2083 / 2123) : ℂ) * ζ ^ 21 + ((6373 / 8492) : ℂ) * ζ ^ 22 + ((63215 / 8492) : ℂ) * ζ ^ 23 - ((11733 / 8492) : ℂ) * ζ ^ 24 + ((69631 / 8492) : ℂ) * ζ ^ 25 + ((3968 / 2123) : ℂ) * ζ ^ 26 - ((540 / 193) : ℂ) * ζ ^ 27 + ((40479 / 8492) : ℂ) * ζ ^ 28 + ((95647 / 8492) : ℂ) * ζ ^ 29 - ((1057 / 8492) : ℂ) * ζ ^ 30 - ((96905 / 8492) : ℂ) * ζ ^ 31 + ((9060 / 2123) : ℂ) * ζ ^ 32 + ((9281 / 2123) : ℂ) * ζ ^ 33 + ((4183 / 8492) : ℂ) * ζ ^ 34 - ((11417 / 2123) : ℂ) * ζ ^ 35 + ((331 / 193) : ℂ) * ζ ^ 36 - ((24769 / 4246) : ℂ) * ζ ^ 37 - ((19585 / 8492) : ℂ) * ζ ^ 38 - ((3717 / 8492) : ℂ) * ζ ^ 39 - ((253 / 772) : ℂ) * ζ ^ 40 - ((24769 / 4246) : ℂ) * ζ ^ 41 - ((9499 / 8492) : ℂ) * ζ ^ 42 - ((4479 / 2123) : ℂ) * ζ ^ 43 - ((55133 / 8492) : ℂ) * ζ ^ 44 - ((27123 / 8492) : ℂ) * ζ ^ 45 - ((9499 / 8492) : ℂ) * ζ ^ 46 + ((73145 / 8492) : ℂ) * ζ ^ 47 - ((1311 / 8492) : ℂ) * ζ ^ 48 - ((39079 / 8492) : ℂ) * ζ ^ 49 + ((16179 / 8492) : ℂ) * ζ ^ 50 + ((73145 / 8492) : ℂ) * ζ ^ 51 + ((5419 / 2123) : ℂ) * ζ ^ 52 + ((52299 / 8492) : ℂ) * ζ ^ 53 - ((1670 / 2123) : ℂ) * ζ ^ 54 - ((27035 / 4246) : ℂ) * ζ ^ 55 + ((5419 / 2123) : ℂ) * ζ ^ 56 + ((28935 / 8492) : ℂ) * ζ ^ 57 - ((1197 / 4246) : ℂ) * ζ ^ 58 - ((19075 / 8492) : ℂ) * ζ ^ 59 - ((5419 / 2123) : ℂ) * ζ ^ 60 - ((28935 / 8492) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_2_0 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        2 0 =
      alternatingSixAmbientRow13TransformedGeneratorA
        2 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((415 / 386) : ℂ) + ((860 / 193) : ℂ) * ζ ^ 3 - ((415 / 386) : ℂ) * ζ ^ 4 + ((4751 / 1544) : ℂ) * ζ ^ 5 - ((7571 / 1544) : ℂ) * ζ ^ 6 + ((12149 / 1544) : ℂ) * ζ ^ 8 - ((843 / 193) : ℂ) * ζ ^ 9 + ((1753 / 1544) : ℂ) * ζ ^ 10 - ((7641 / 1544) : ℂ) * ζ ^ 11 - ((4863 / 1544) : ℂ) * ζ ^ 13 - ((2331 / 386) : ℂ) * ζ ^ 14 + ((723 / 1544) : ℂ) * ζ ^ 15 - ((2191 / 386) : ℂ) * ζ ^ 16 - ((1993 / 1544) : ℂ) * ζ ^ 17 + ((10915 / 1544) : ℂ) * ζ ^ 18 - ((2091 / 386) : ℂ) * ζ ^ 19 - ((1001 / 193) : ℂ) * ζ ^ 20 + ((745 / 772) : ℂ) * ζ ^ 21 + ((7571 / 1544) : ℂ) * ζ ^ 22 + ((7333 / 1544) : ℂ) * ζ ^ 23 - ((189 / 386) : ℂ) * ζ ^ 24 - ((2577 / 772) : ℂ) * ζ ^ 25 + ((1637 / 193) : ℂ) * ζ ^ 26 + ((7641 / 1544) : ℂ) * ζ ^ 27 - ((5313 / 772) : ℂ) * ζ ^ 28 + ((9301 / 772) : ℂ) * ζ ^ 29 - ((4823 / 1544) : ℂ) * ζ ^ 30 + ((8863 / 1544) : ℂ) * ζ ^ 31 + ((2191 / 386) : ℂ) * ζ ^ 32 - ((1449 / 1544) : ℂ) * ζ ^ 33 + ((2777 / 1544) : ℂ) * ζ ^ 34 - ((5593 / 772) : ℂ) * ζ ^ 35 + ((15085 / 1544) : ℂ) * ζ ^ 36 - ((1369 / 386) : ℂ) * ζ ^ 37 - ((8435 / 1544) : ℂ) * ζ ^ 38 + ((4767 / 1544) : ℂ) * ζ ^ 39 - ((1021 / 193) : ℂ) * ζ ^ 40 - ((1369 / 386) : ℂ) * ζ ^ 41 - ((5525 / 1544) : ℂ) * ζ ^ 42 - ((6419 / 1544) : ℂ) * ζ ^ 43 + ((5725 / 1544) : ℂ) * ζ ^ 44 - ((927 / 772) : ℂ) * ζ ^ 45 - ((5525 / 1544) : ℂ) * ζ ^ 46 - ((611 / 772) : ℂ) * ζ ^ 47 - ((547 / 193) : ℂ) * ζ ^ 48 - ((321 / 772) : ℂ) * ζ ^ 49 + ((3009 / 772) : ℂ) * ζ ^ 50 - ((611 / 772) : ℂ) * ζ ^ 51 - ((6321 / 1544) : ℂ) * ζ ^ 52 + ((5681 / 1544) : ℂ) * ζ ^ 53 - ((493 / 1544) : ℂ) * ζ ^ 54 + ((3527 / 1544) : ℂ) * ζ ^ 55 - ((6321 / 1544) : ℂ) * ζ ^ 56 + ((1993 / 1544) : ℂ) * ζ ^ 57 + ((4851 / 1544) : ℂ) * ζ ^ 58 - ((2305 / 1544) : ℂ) * ζ ^ 59 + ((6321 / 1544) : ℂ) * ζ ^ 60 - ((1993 / 1544) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_2_1 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        2 1 =
      alternatingSixAmbientRow13TransformedGeneratorA
        2 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((151 / 386) : ℂ) - ((1925 / 1158) : ℂ) * ζ ^ 3 - ((151 / 386) : ℂ) * ζ ^ 4 + ((4537 / 2316) : ℂ) * ζ ^ 5 - ((1411 / 1158) : ℂ) * ζ ^ 6 + ((797 / 772) : ℂ) * ζ ^ 8 - ((939 / 386) : ℂ) * ζ ^ 9 + ((6277 / 2316) : ℂ) * ζ ^ 10 - ((242 / 579) : ℂ) * ζ ^ 11 + ((865 / 1158) : ℂ) * ζ ^ 13 - ((3033 / 772) : ℂ) * ζ ^ 14 + ((1863 / 772) : ℂ) * ζ ^ 15 + ((49 / 1158) : ℂ) * ζ ^ 16 - ((1097 / 2316) : ℂ) * ζ ^ 17 + ((1151 / 2316) : ℂ) * ζ ^ 18 - ((6557 / 2316) : ℂ) * ζ ^ 19 + ((5795 / 2316) : ℂ) * ζ ^ 20 - ((2021 / 1158) : ℂ) * ζ ^ 21 + ((1411 / 1158) : ℂ) * ζ ^ 22 + ((676 / 193) : ℂ) * ζ ^ 23 - ((1899 / 772) : ℂ) * ζ ^ 24 + ((1585 / 2316) : ℂ) * ζ ^ 25 + ((135 / 772) : ℂ) * ζ ^ 26 + ((242 / 579) : ℂ) * ζ ^ 27 + ((561 / 772) : ℂ) * ζ ^ 28 + ((955 / 2316) : ℂ) * ζ ^ 29 - ((6173 / 2316) : ℂ) * ζ ^ 30 + ((583 / 772) : ℂ) * ζ ^ 31 - ((49 / 1158) : ℂ) * ζ ^ 32 + ((1495 / 772) : ℂ) * ζ ^ 33 + ((467 / 1158) : ℂ) * ζ ^ 34 + ((2497 / 772) : ℂ) * ζ ^ 35 - ((693 / 386) : ℂ) * ζ ^ 36 + ((154 / 193) : ℂ) * ζ ^ 37 + ((4345 / 1158) : ℂ) * ζ ^ 38 - ((3839 / 1158) : ℂ) * ζ ^ 39 - ((11393 / 2316) : ℂ) * ζ ^ 40 + ((154 / 193) : ℂ) * ζ ^ 41 + ((2417 / 2316) : ℂ) * ζ ^ 42 + ((275 / 579) : ℂ) * ζ ^ 43 + ((2477 / 772) : ℂ) * ζ ^ 44 - ((2947 / 386) : ℂ) * ζ ^ 45 + ((2417 / 2316) : ℂ) * ζ ^ 46 - ((781 / 2316) : ℂ) * ζ ^ 47 + ((1423 / 2316) : ℂ) * ζ ^ 48 + ((5723 / 1158) : ℂ) * ζ ^ 49 + ((2513 / 1158) : ℂ) * ζ ^ 50 - ((781 / 2316) : ℂ) * ζ ^ 51 + ((1015 / 579) : ℂ) * ζ ^ 52 + ((1697 / 2316) : ℂ) * ζ ^ 53 - ((2481 / 772) : ℂ) * ζ ^ 54 + ((127 / 386) : ℂ) * ζ ^ 55 + ((1015 / 579) : ℂ) * ζ ^ 56 + ((1097 / 2316) : ℂ) * ζ ^ 57 - ((2351 / 772) : ℂ) * ζ ^ 58 + ((19 / 2316) : ℂ) * ζ ^ 59 - ((1015 / 579) : ℂ) * ζ ^ 60 - ((1097 / 2316) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_2_2 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        2 2 =
      alternatingSixAmbientRow13TransformedGeneratorA
        2 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((2785 / 772) : ℂ) + ((453 / 772) : ℂ) * ζ ^ 3 - ((2785 / 772) : ℂ) * ζ ^ 4 + ((10393 / 1544) : ℂ) * ζ ^ 5 - ((6335 / 1544) : ℂ) * ζ ^ 6 - ((1629 / 1544) : ℂ) * ζ ^ 8 - ((4987 / 772) : ℂ) * ζ ^ 9 - ((5675 / 1544) : ℂ) * ζ ^ 10 - ((3223 / 1544) : ℂ) * ζ ^ 11 - ((4589 / 1544) : ℂ) * ζ ^ 13 - ((165 / 386) : ℂ) * ζ ^ 14 + ((651 / 1544) : ℂ) * ζ ^ 15 - ((173 / 386) : ℂ) * ζ ^ 16 + ((419 / 1544) : ℂ) * ζ ^ 17 + ((13353 / 1544) : ℂ) * ζ ^ 18 - ((1937 / 772) : ℂ) * ζ ^ 19 + ((3523 / 772) : ℂ) * ζ ^ 20 - ((2035 / 772) : ℂ) * ζ ^ 21 + ((6335 / 1544) : ℂ) * ζ ^ 22 + ((6089 / 1544) : ℂ) * ζ ^ 23 - ((3869 / 772) : ℂ) * ζ ^ 24 - ((1538 / 193) : ℂ) * ζ ^ 25 + ((2885 / 772) : ℂ) * ζ ^ 26 + ((3223 / 1544) : ℂ) * ζ ^ 27 - ((6139 / 772) : ℂ) * ζ ^ 28 + ((715 / 193) : ℂ) * ζ ^ 29 - ((5845 / 1544) : ℂ) * ζ ^ 30 + ((7203 / 1544) : ℂ) * ζ ^ 31 + ((173 / 386) : ℂ) * ζ ^ 32 + ((2217 / 1544) : ℂ) * ζ ^ 33 - ((1055 / 1544) : ℂ) * ζ ^ 34 + ((1397 / 386) : ℂ) * ζ ^ 35 + ((5483 / 1544) : ℂ) * ζ ^ 36 + ((1227 / 386) : ℂ) * ζ ^ 37 - ((3715 / 1544) : ℂ) * ζ ^ 38 - ((4831 / 1544) : ℂ) * ζ ^ 39 - ((121 / 772) : ℂ) * ζ ^ 40 + ((1227 / 386) : ℂ) * ζ ^ 41 + ((565 / 1544) : ℂ) * ζ ^ 42 - ((5171 / 1544) : ℂ) * ζ ^ 43 + ((4341 / 1544) : ℂ) * ζ ^ 44 - ((3239 / 772) : ℂ) * ζ ^ 45 + ((565 / 1544) : ℂ) * ζ ^ 46 - ((995 / 386) : ℂ) * ζ ^ 47 - ((362 / 193) : ℂ) * ζ ^ 48 + ((1623 / 772) : ℂ) * ζ ^ 49 - ((787 / 772) : ℂ) * ζ ^ 50 - ((995 / 386) : ℂ) * ζ ^ 51 - ((4791 / 1544) : ℂ) * ζ ^ 52 + ((1081 / 1544) : ℂ) * ζ ^ 53 + ((1009 / 1544) : ℂ) * ζ ^ 54 + ((1779 / 1544) : ℂ) * ζ ^ 55 - ((4791 / 1544) : ℂ) * ζ ^ 56 - ((419 / 1544) : ℂ) * ζ ^ 57 + ((4851 / 1544) : ℂ) * ζ ^ 58 + ((2201 / 1544) : ℂ) * ζ ^ 59 + ((4791 / 1544) : ℂ) * ζ ^ 60 + ((419 / 1544) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_2_3 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        2 3 =
      alternatingSixAmbientRow13TransformedGeneratorA
        2 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((3337 / 772) : ℂ) - ((5769 / 1544) : ℂ) * ζ ^ 3 - ((3337 / 772) : ℂ) * ζ ^ 4 + ((4473 / 386) : ℂ) * ζ ^ 5 + ((749 / 772) : ℂ) * ζ ^ 6 + ((407 / 1544) : ℂ) * ζ ^ 8 - ((20407 / 1544) : ℂ) * ζ ^ 9 + ((21399 / 1544) : ℂ) * ζ ^ 10 + ((997 / 386) : ℂ) * ζ ^ 11 - ((9719 / 1544) : ℂ) * ζ ^ 13 - ((19901 / 1544) : ℂ) * ζ ^ 14 + ((11363 / 772) : ℂ) * ζ ^ 15 - ((9795 / 1544) : ℂ) * ζ ^ 16 - ((2515 / 1544) : ℂ) * ζ ^ 17 + ((2031 / 386) : ℂ) * ζ ^ 18 - ((9369 / 772) : ℂ) * ζ ^ 19 - ((605 / 772) : ℂ) * ζ ^ 20 + ((5125 / 1544) : ℂ) * ζ ^ 21 - ((749 / 772) : ℂ) * ζ ^ 22 + ((10125 / 772) : ℂ) * ζ ^ 23 - ((8585 / 1544) : ℂ) * ζ ^ 24 - ((3721 / 1544) : ℂ) * ζ ^ 25 + ((445 / 772) : ℂ) * ζ ^ 26 - ((997 / 386) : ℂ) * ζ ^ 27 + ((3749 / 772) : ℂ) * ζ ^ 28 + ((2992 / 193) : ℂ) * ζ ^ 29 - ((11339 / 1544) : ℂ) * ζ ^ 30 - ((14393 / 1544) : ℂ) * ζ ^ 31 + ((9795 / 1544) : ℂ) * ζ ^ 32 + ((4749 / 772) : ℂ) * ζ ^ 33 + ((15225 / 1544) : ℂ) * ζ ^ 34 - ((9859 / 772) : ℂ) * ζ ^ 35 + ((5101 / 772) : ℂ) * ζ ^ 36 - ((10155 / 1544) : ℂ) * ζ ^ 37 - ((353 / 772) : ℂ) * ζ ^ 38 + ((13301 / 1544) : ℂ) * ζ ^ 39 - ((14087 / 1544) : ℂ) * ζ ^ 40 - ((10155 / 1544) : ℂ) * ζ ^ 41 - ((597 / 386) : ℂ) * ζ ^ 42 - ((5677 / 1544) : ℂ) * ζ ^ 43 + ((4699 / 1544) : ℂ) * ζ ^ 44 - ((4003 / 1544) : ℂ) * ζ ^ 45 - ((597 / 386) : ℂ) * ζ ^ 46 + ((10405 / 1544) : ℂ) * ζ ^ 47 - ((6727 / 1544) : ℂ) * ζ ^ 48 + ((2049 / 772) : ℂ) * ζ ^ 49 + ((5437 / 1544) : ℂ) * ζ ^ 50 + ((10405 / 1544) : ℂ) * ζ ^ 51 - ((407 / 1544) : ℂ) * ζ ^ 52 + ((5075 / 1544) : ℂ) * ζ ^ 53 - ((3049 / 1544) : ℂ) * ζ ^ 54 - ((2409 / 1544) : ℂ) * ζ ^ 55 - ((407 / 1544) : ℂ) * ζ ^ 56 + ((2515 / 1544) : ℂ) * ζ ^ 57 + ((2275 / 1544) : ℂ) * ζ ^ 58 - ((1999 / 386) : ℂ) * ζ ^ 59 + ((407 / 1544) : ℂ) * ζ ^ 60 - ((2515 / 1544) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_2_4 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        2 4 =
      alternatingSixAmbientRow13TransformedGeneratorA
        2 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((4005 / 8492) : ℂ) + ((31943 / 8492) : ℂ) * ζ ^ 3 - ((4005 / 8492) : ℂ) * ζ ^ 4 + ((53875 / 16984) : ℂ) * ζ ^ 5 - ((82999 / 16984) : ℂ) * ζ ^ 6 + ((102429 / 16984) : ℂ) * ζ ^ 8 - ((6181 / 2123) : ℂ) * ζ ^ 9 - ((94679 / 16984) : ℂ) * ζ ^ 10 - ((901 / 16984) : ℂ) * ζ ^ 11 + ((1701 / 1544) : ℂ) * ζ ^ 13 + ((1460 / 2123) : ℂ) * ζ ^ 14 - ((21457 / 16984) : ℂ) * ζ ^ 15 - ((9367 / 8492) : ℂ) * ζ ^ 16 + ((4427 / 16984) : ℂ) * ζ ^ 17 + ((104187 / 16984) : ℂ) * ζ ^ 18 + ((5139 / 4246) : ℂ) * ζ ^ 19 + ((5821 / 4246) : ℂ) * ζ ^ 20 - ((2598 / 2123) : ℂ) * ζ ^ 21 + ((82999 / 16984) : ℂ) * ζ ^ 22 - ((10207 / 16984) : ℂ) * ζ ^ 23 - ((21009 / 8492) : ℂ) * ζ ^ 24 - ((6003 / 4246) : ℂ) * ζ ^ 25 + ((9569 / 2123) : ℂ) * ζ ^ 26 + ((901 / 16984) : ℂ) * ζ ^ 27 - ((12534 / 2123) : ℂ) * ζ ^ 28 - ((11667 / 8492) : ℂ) * ζ ^ 29 - ((20767 / 16984) : ℂ) * ζ ^ 30 + ((19795 / 16984) : ℂ) * ζ ^ 31 + ((9367 / 8492) : ℂ) * ζ ^ 32 + ((15173 / 16984) : ℂ) * ζ ^ 33 - ((68679 / 16984) : ℂ) * ζ ^ 34 + ((26251 / 8492) : ℂ) * ζ ^ 35 + ((1725 / 1544) : ℂ) * ζ ^ 36 + ((14819 / 8492) : ℂ) * ζ ^ 37 - ((31805 / 16984) : ℂ) * ζ ^ 38 - ((34509 / 16984) : ℂ) * ζ ^ 39 - ((12449 / 8492) : ℂ) * ζ ^ 40 + ((14819 / 8492) : ℂ) * ζ ^ 41 + ((6447 / 16984) : ℂ) * ζ ^ 42 + ((33199 / 16984) : ℂ) * ζ ^ 43 + ((6405 / 16984) : ℂ) * ζ ^ 44 - ((7459 / 4246) : ℂ) * ζ ^ 45 + ((6447 / 16984) : ℂ) * ζ ^ 46 - ((9447 / 8492) : ℂ) * ζ ^ 47 + ((1069 / 772) : ℂ) * ζ ^ 48 + ((8953 / 8492) : ℂ) * ζ ^ 49 + ((846 / 2123) : ℂ) * ζ ^ 50 - ((9447 / 8492) : ℂ) * ζ ^ 51 - ((241 / 16984) : ℂ) * ζ ^ 52 - ((14119 / 16984) : ℂ) * ζ ^ 53 - ((13215 / 16984) : ℂ) * ζ ^ 54 + ((15933 / 16984) : ℂ) * ζ ^ 55 - ((241 / 16984) : ℂ) * ζ ^ 56 - ((4427 / 16984) : ℂ) * ζ ^ 57 - ((691 / 16984) : ℂ) * ζ ^ 58 + ((2961 / 16984) : ℂ) * ζ ^ 59 + ((241 / 16984) : ℂ) * ζ ^ 60 + ((4427 / 16984) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_2_5 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        2 5 =
      alternatingSixAmbientRow13TransformedGeneratorA
        2 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((3403 / 8492) : ℂ) - ((1223 / 2123) : ℂ) * ζ ^ 3 + ((3403 / 8492) : ℂ) * ζ ^ 4 - ((3358 / 2123) : ℂ) * ζ ^ 5 + ((24027 / 8492) : ℂ) * ζ ^ 6 + ((1253 / 772) : ℂ) * ζ ^ 8 + ((879 / 4246) : ℂ) * ζ ^ 9 + ((24749 / 8492) : ℂ) * ζ ^ 10 + ((14183 / 4246) : ℂ) * ζ ^ 11 - ((27297 / 8492) : ℂ) * ζ ^ 13 - ((361 / 4246) : ℂ) * ζ ^ 14 + ((21063 / 8492) : ℂ) * ζ ^ 15 - ((3631 / 8492) : ℂ) * ζ ^ 16 - ((5837 / 4246) : ℂ) * ζ ^ 17 - ((2531 / 2123) : ℂ) * ζ ^ 18 + ((7303 / 8492) : ℂ) * ζ ^ 19 - ((18619 / 8492) : ℂ) * ζ ^ 20 + ((12333 / 8492) : ℂ) * ζ ^ 21 - ((24027 / 8492) : ℂ) * ζ ^ 22 + ((27365 / 8492) : ℂ) * ζ ^ 23 + ((3747 / 2123) : ℂ) * ζ ^ 24 + ((30345 / 8492) : ℂ) * ζ ^ 25 - ((4622 / 2123) : ℂ) * ζ ^ 26 - ((14183 / 4246) : ℂ) * ζ ^ 27 + ((19837 / 8492) : ℂ) * ζ ^ 28 + ((13008 / 2123) : ℂ) * ζ ^ 29 + ((679 / 8492) : ℂ) * ζ ^ 30 - ((17239 / 2123) : ℂ) * ζ ^ 31 + ((3631 / 8492) : ℂ) * ζ ^ 32 + ((13373 / 4246) : ℂ) * ζ ^ 33 + ((28887 / 8492) : ℂ) * ζ ^ 34 - ((19399 / 4246) : ℂ) * ζ ^ 35 - ((8713 / 8492) : ℂ) * ζ ^ 36 - ((35681 / 8492) : ℂ) * ζ ^ 37 + ((1561 / 772) : ℂ) * ζ ^ 38 + ((13287 / 4246) : ℂ) * ζ ^ 39 - ((13181 / 8492) : ℂ) * ζ ^ 40 - ((35681 / 8492) : ℂ) * ζ ^ 41 - ((5539 / 8492) : ℂ) * ζ ^ 42 - ((1357 / 2123) : ℂ) * ζ ^ 43 - ((127 / 386) : ℂ) * ζ ^ 44 - ((1048 / 2123) : ℂ) * ζ ^ 45 - ((5539 / 8492) : ℂ) * ζ ^ 46 + ((1845 / 386) : ℂ) * ζ ^ 47 - ((470 / 2123) : ℂ) * ζ ^ 48 - ((6823 / 8492) : ℂ) * ζ ^ 49 + ((12119 / 4246) : ℂ) * ζ ^ 50 + ((1845 / 386) : ℂ) * ζ ^ 51 + ((3086 / 2123) : ℂ) * ζ ^ 52 + ((1297 / 772) : ℂ) * ζ ^ 53 - ((18699 / 8492) : ℂ) * ζ ^ 54 - ((16057 / 8492) : ℂ) * ζ ^ 55 + ((3086 / 2123) : ℂ) * ζ ^ 56 + ((5837 / 4246) : ℂ) * ζ ^ 57 - ((3545 / 4246) : ℂ) * ζ ^ 58 - ((24533 / 8492) : ℂ) * ζ ^ 59 - ((3086 / 2123) : ℂ) * ζ ^ 60 - ((5837 / 4246) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_3_0 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        3 0 =
      alternatingSixAmbientRow13TransformedGeneratorA
        3 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((2839 / 772) : ℂ) - ((1197 / 1544) : ℂ) * ζ ^ 3 - ((2839 / 772) : ℂ) * ζ ^ 4 + ((11163 / 1544) : ℂ) * ζ ^ 5 + ((6025 / 1544) : ℂ) * ζ ^ 6 - ((17381 / 1544) : ℂ) * ζ ^ 8 - ((2685 / 772) : ℂ) * ζ ^ 9 + ((5387 / 772) : ℂ) * ζ ^ 10 - ((2915 / 772) : ℂ) * ζ ^ 11 + ((10731 / 772) : ℂ) * ζ ^ 13 - ((4749 / 1544) : ℂ) * ζ ^ 14 - ((13887 / 1544) : ℂ) * ζ ^ 15 + ((14183 / 1544) : ℂ) * ζ ^ 16 + ((5793 / 1544) : ℂ) * ζ ^ 17 - ((317 / 1544) : ℂ) * ζ ^ 18 + ((8057 / 1544) : ℂ) * ζ ^ 19 + ((1867 / 772) : ℂ) * ζ ^ 20 - ((4141 / 772) : ℂ) * ζ ^ 21 - ((6025 / 1544) : ℂ) * ζ ^ 22 - ((1750 / 193) : ℂ) * ζ ^ 23 + ((10449 / 1544) : ℂ) * ζ ^ 24 - ((10907 / 772) : ℂ) * ζ ^ 25 - ((1966 / 193) : ℂ) * ζ ^ 26 + ((2915 / 772) : ℂ) * ζ ^ 27 + ((7461 / 1544) : ℂ) * ζ ^ 28 - ((10613 / 772) : ℂ) * ζ ^ 29 - ((8609 / 772) : ℂ) * ζ ^ 30 + ((4199 / 386) : ℂ) * ζ ^ 31 - ((14183 / 1544) : ℂ) * ζ ^ 32 + ((1489 / 772) : ℂ) * ζ ^ 33 + ((3385 / 386) : ℂ) * ζ ^ 34 + ((6031 / 772) : ℂ) * ζ ^ 35 - ((19927 / 1544) : ℂ) * ζ ^ 36 + ((4967 / 386) : ℂ) * ζ ^ 37 + ((4943 / 1544) : ℂ) * ζ ^ 38 - ((3463 / 772) : ℂ) * ζ ^ 39 + ((15887 / 1544) : ℂ) * ζ ^ 40 + ((4967 / 386) : ℂ) * ζ ^ 41 + ((9703 / 1544) : ℂ) * ζ ^ 42 - ((229 / 193) : ℂ) * ζ ^ 43 - ((931 / 193) : ℂ) * ζ ^ 44 + ((12297 / 1544) : ℂ) * ζ ^ 45 + ((9703 / 1544) : ℂ) * ζ ^ 46 - ((5483 / 772) : ℂ) * ζ ^ 47 + ((858 / 193) : ℂ) * ζ ^ 48 - ((8993 / 1544) : ℂ) * ζ ^ 49 - ((2519 / 1544) : ℂ) * ζ ^ 50 - ((5483 / 772) : ℂ) * ζ ^ 51 + ((718 / 193) : ℂ) * ζ ^ 52 - ((3027 / 386) : ℂ) * ζ ^ 53 - ((898 / 193) : ℂ) * ζ ^ 54 + ((2367 / 772) : ℂ) * ζ ^ 55 + ((718 / 193) : ℂ) * ζ ^ 56 - ((5793 / 1544) : ℂ) * ζ ^ 57 - ((3675 / 772) : ℂ) * ζ ^ 58 + ((779 / 193) : ℂ) * ζ ^ 59 - ((718 / 193) : ℂ) * ζ ^ 60 + ((5793 / 1544) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_3_1 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        3 1 =
      alternatingSixAmbientRow13TransformedGeneratorA
        3 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((725 / 386) : ℂ) + ((281 / 772) : ℂ) * ζ ^ 3 - ((725 / 386) : ℂ) * ζ ^ 4 + ((2278 / 579) : ℂ) * ζ ^ 5 + ((293 / 386) : ℂ) * ζ ^ 6 + ((68 / 579) : ℂ) * ζ ^ 8 - ((5327 / 1158) : ℂ) * ζ ^ 9 - ((2797 / 1158) : ℂ) * ζ ^ 10 + ((3797 / 2316) : ℂ) * ζ ^ 11 - ((5209 / 1158) : ℂ) * ζ ^ 13 + ((1838 / 579) : ℂ) * ζ ^ 14 + ((477 / 386) : ℂ) * ζ ^ 15 - ((5627 / 2316) : ℂ) * ζ ^ 16 - ((257 / 386) : ℂ) * ζ ^ 17 + ((1281 / 772) : ℂ) * ζ ^ 18 + ((935 / 2316) : ℂ) * ζ ^ 19 - ((3131 / 1158) : ℂ) * ζ ^ 20 + ((13445 / 2316) : ℂ) * ζ ^ 21 - ((293 / 386) : ℂ) * ζ ^ 22 - ((15317 / 2316) : ℂ) * ζ ^ 23 + ((635 / 2316) : ℂ) * ζ ^ 24 + ((8549 / 1158) : ℂ) * ζ ^ 25 + ((5081 / 2316) : ℂ) * ζ ^ 26 - ((3797 / 2316) : ℂ) * ζ ^ 27 - ((11809 / 2316) : ℂ) * ζ ^ 28 + ((5599 / 2316) : ℂ) * ζ ^ 29 + ((24533 / 2316) : ℂ) * ζ ^ 30 - ((6407 / 2316) : ℂ) * ζ ^ 31 + ((5627 / 2316) : ℂ) * ζ ^ 32 + ((8029 / 2316) : ℂ) * ζ ^ 33 - ((1328 / 193) : ℂ) * ζ ^ 34 - ((16511 / 2316) : ℂ) * ζ ^ 35 + ((5572 / 579) : ℂ) * ζ ^ 36 - ((16529 / 2316) : ℂ) * ζ ^ 37 - ((4040 / 579) : ℂ) * ζ ^ 38 + ((8849 / 1158) : ℂ) * ζ ^ 39 + ((1015 / 772) : ℂ) * ζ ^ 40 - ((16529 / 2316) : ℂ) * ζ ^ 41 - ((6839 / 2316) : ℂ) * ζ ^ 42 + ((2281 / 579) : ℂ) * ζ ^ 43 + ((2663 / 772) : ℂ) * ζ ^ 44 + ((17729 / 2316) : ℂ) * ζ ^ 45 - ((6839 / 2316) : ℂ) * ζ ^ 46 + ((435 / 386) : ℂ) * ζ ^ 47 - ((1454 / 579) : ℂ) * ζ ^ 48 - ((614 / 193) : ℂ) * ζ ^ 49 - ((2549 / 579) : ℂ) * ζ ^ 50 + ((435 / 386) : ℂ) * ζ ^ 51 - ((16661 / 2316) : ℂ) * ζ ^ 52 - ((469 / 579) : ℂ) * ζ ^ 53 + ((17035 / 2316) : ℂ) * ζ ^ 54 - ((517 / 579) : ℂ) * ζ ^ 55 - ((16661 / 2316) : ℂ) * ζ ^ 56 + ((257 / 386) : ℂ) * ζ ^ 57 + ((15233 / 2316) : ℂ) * ζ ^ 58 - ((271 / 1158) : ℂ) * ζ ^ 59 + ((16661 / 2316) : ℂ) * ζ ^ 60 - ((257 / 386) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_3_2 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        3 2 =
      alternatingSixAmbientRow13TransformedGeneratorA
        3 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((295 / 386) : ℂ) - ((7553 / 1544) : ℂ) * ζ ^ 3 - ((295 / 386) : ℂ) * ζ ^ 4 - ((5221 / 1544) : ℂ) * ζ ^ 5 + ((10565 / 1544) : ℂ) * ζ ^ 6 - ((6957 / 1544) : ℂ) * ζ ^ 8 + ((2349 / 772) : ℂ) * ζ ^ 9 + ((9911 / 772) : ℂ) * ζ ^ 10 - ((589 / 386) : ℂ) * ζ ^ 11 + ((1869 / 193) : ℂ) * ζ ^ 13 - ((9257 / 1544) : ℂ) * ζ ^ 14 + ((4309 / 1544) : ℂ) * ζ ^ 15 - ((115 / 1544) : ℂ) * ζ ^ 16 - ((523 / 1544) : ℂ) * ζ ^ 17 - ((19743 / 1544) : ℂ) * ζ ^ 18 - ((6665 / 1544) : ℂ) * ζ ^ 19 - ((10267 / 772) : ℂ) * ζ ^ 20 + ((3023 / 772) : ℂ) * ζ ^ 21 - ((10565 / 1544) : ℂ) * ζ ^ 22 - ((4291 / 772) : ℂ) * ζ ^ 23 + ((20419 / 1544) : ℂ) * ζ ^ 24 + ((4561 / 772) : ℂ) * ζ ^ 25 - ((1447 / 386) : ℂ) * ζ ^ 26 + ((589 / 386) : ℂ) * ζ ^ 27 + ((20275 / 1544) : ℂ) * ζ ^ 28 + ((31 / 772) : ℂ) * ζ ^ 29 + ((5795 / 772) : ℂ) * ζ ^ 30 + ((55 / 772) : ℂ) * ζ ^ 31 + ((115 / 1544) : ℂ) * ζ ^ 32 - ((451 / 193) : ℂ) * ζ ^ 33 + ((469 / 193) : ℂ) * ζ ^ 34 - ((5971 / 772) : ℂ) * ζ ^ 35 - ((6141 / 1544) : ℂ) * ζ ^ 36 - ((1773 / 386) : ℂ) * ζ ^ 37 - ((805 / 1544) : ℂ) * ζ ^ 38 + ((1835 / 386) : ℂ) * ζ ^ 39 - ((301 / 1544) : ℂ) * ζ ^ 40 - ((1773 / 386) : ℂ) * ζ ^ 41 - ((4777 / 1544) : ℂ) * ζ ^ 42 + ((287 / 386) : ℂ) * ζ ^ 43 - ((3035 / 772) : ℂ) * ζ ^ 44 + ((9621 / 1544) : ℂ) * ζ ^ 45 - ((4777 / 1544) : ℂ) * ζ ^ 46 + ((1123 / 772) : ℂ) * ζ ^ 47 + ((3249 / 772) : ℂ) * ζ ^ 48 - ((4621 / 1544) : ℂ) * ζ ^ 49 + ((4479 / 1544) : ℂ) * ζ ^ 50 + ((1123 / 772) : ℂ) * ζ ^ 51 + ((782 / 193) : ℂ) * ζ ^ 52 + ((237 / 193) : ℂ) * ζ ^ 53 + ((149 / 772) : ℂ) * ζ ^ 54 + ((45 / 193) : ℂ) * ζ ^ 55 + ((782 / 193) : ℂ) * ζ ^ 56 + ((523 / 1544) : ℂ) * ζ ^ 57 - ((3675 / 772) : ℂ) * ζ ^ 58 - ((1303 / 772) : ℂ) * ζ ^ 59 - ((782 / 193) : ℂ) * ζ ^ 60 - ((523 / 1544) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_3_3 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        3 3 =
      alternatingSixAmbientRow13TransformedGeneratorA
        3 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((13001 / 1544) : ℂ) - ((1796 / 193) : ℂ) * ζ ^ 3 - ((13001 / 1544) : ℂ) * ζ ^ 4 + ((13751 / 1544) : ℂ) * ζ ^ 5 + ((4623 / 772) : ℂ) * ζ ^ 6 - ((24983 / 1544) : ℂ) * ζ ^ 8 - ((1167 / 386) : ℂ) * ζ ^ 9 + ((331 / 193) : ℂ) * ζ ^ 10 + ((111 / 193) : ℂ) * ζ ^ 11 + ((29801 / 1544) : ℂ) * ζ ^ 13 + ((3299 / 772) : ℂ) * ζ ^ 14 - ((1927 / 1544) : ℂ) * ζ ^ 15 + ((3612 / 193) : ℂ) * ζ ^ 16 + ((9083 / 1544) : ℂ) * ζ ^ 17 - ((4803 / 386) : ℂ) * ζ ^ 18 + ((2815 / 1544) : ℂ) * ζ ^ 19 - ((2195 / 1544) : ℂ) * ζ ^ 20 - ((1189 / 772) : ℂ) * ζ ^ 21 - ((4623 / 772) : ℂ) * ζ ^ 22 - ((1881 / 386) : ℂ) * ζ ^ 23 + ((31091 / 1544) : ℂ) * ζ ^ 24 - ((39787 / 1544) : ℂ) * ζ ^ 25 - ((18461 / 1544) : ℂ) * ζ ^ 26 - ((111 / 193) : ℂ) * ζ ^ 27 + ((12199 / 1544) : ℂ) * ζ ^ 28 - ((17089 / 1544) : ℂ) * ζ ^ 29 - ((3213 / 772) : ℂ) * ζ ^ 30 + ((5765 / 772) : ℂ) * ζ ^ 31 - ((3612 / 193) : ℂ) * ζ ^ 32 - ((15455 / 1544) : ℂ) * ζ ^ 33 + ((6457 / 1544) : ℂ) * ζ ^ 34 + ((1029 / 193) : ℂ) * ζ ^ 35 - ((33787 / 1544) : ℂ) * ζ ^ 36 + ((2568 / 193) : ℂ) * ζ ^ 37 + ((8933 / 1544) : ℂ) * ζ ^ 38 + ((2537 / 772) : ℂ) * ζ ^ 39 + ((7067 / 386) : ℂ) * ζ ^ 40 + ((2568 / 193) : ℂ) * ζ ^ 41 + ((9215 / 1544) : ℂ) * ζ ^ 42 - ((359 / 772) : ℂ) * ζ ^ 43 - ((4263 / 1544) : ℂ) * ζ ^ 44 + ((32551 / 1544) : ℂ) * ζ ^ 45 + ((9215 / 1544) : ℂ) * ζ ^ 46 - ((6209 / 772) : ℂ) * ζ ^ 47 + ((7715 / 1544) : ℂ) * ζ ^ 48 - ((16763 / 1544) : ℂ) * ζ ^ 49 - ((4451 / 1544) : ℂ) * ζ ^ 50 - ((6209 / 772) : ℂ) * ζ ^ 51 + ((4891 / 1544) : ℂ) * ζ ^ 52 - ((17455 / 1544) : ℂ) * ζ ^ 53 - ((1191 / 386) : ℂ) * ζ ^ 54 + ((1697 / 772) : ℂ) * ζ ^ 55 + ((4891 / 1544) : ℂ) * ζ ^ 56 - ((9083 / 1544) : ℂ) * ζ ^ 57 - ((5541 / 1544) : ℂ) * ζ ^ 58 + ((1128 / 193) : ℂ) * ζ ^ 59 - ((4891 / 1544) : ℂ) * ζ ^ 60 + ((9083 / 1544) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_3_4 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        3 4 =
      alternatingSixAmbientRow13TransformedGeneratorA
        3 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((44393 / 8492) : ℂ) - ((99427 / 16984) : ℂ) * ζ ^ 3 - ((44393 / 8492) : ℂ) * ζ ^ 4 - ((59769 / 16984) : ℂ) * ζ ^ 5 + ((165029 / 16984) : ℂ) * ζ ^ 6 - ((94285 / 16984) : ℂ) * ζ ^ 8 + ((9385 / 4246) : ℂ) * ζ ^ 9 + ((14324 / 2123) : ℂ) * ζ ^ 10 + ((7949 / 8492) : ℂ) * ζ ^ 11 + ((37295 / 8492) : ℂ) * ζ ^ 13 + ((50437 / 16984) : ℂ) * ζ ^ 14 + ((8759 / 1544) : ℂ) * ζ ^ 15 + ((21623 / 16984) : ℂ) * ζ ^ 16 - ((22229 / 16984) : ℂ) * ζ ^ 17 - ((211319 / 16984) : ℂ) * ζ ^ 18 - ((80451 / 16984) : ℂ) * ζ ^ 19 - ((28129 / 8492) : ℂ) * ζ ^ 20 + ((14385 / 8492) : ℂ) * ζ ^ 21 - ((165029 / 16984) : ℂ) * ζ ^ 22 - ((7061 / 8492) : ℂ) * ζ ^ 23 + ((77881 / 16984) : ℂ) * ζ ^ 24 + ((25627 / 4246) : ℂ) * ζ ^ 25 - ((16635 / 2123) : ℂ) * ζ ^ 26 - ((7949 / 8492) : ℂ) * ζ ^ 27 + ((83081 / 16984) : ℂ) * ζ ^ 28 + ((14909 / 4246) : ℂ) * ζ ^ 29 + ((87509 / 8492) : ℂ) * ζ ^ 30 - ((961 / 386) : ℂ) * ζ ^ 31 - ((21623 / 16984) : ℂ) * ζ ^ 32 - ((20181 / 8492) : ℂ) * ζ ^ 33 + ((2745 / 2123) : ℂ) * ζ ^ 34 - ((1865 / 386) : ℂ) * ζ ^ 35 - ((2395 / 16984) : ℂ) * ζ ^ 36 - ((18307 / 4246) : ℂ) * ζ ^ 37 + ((118133 / 16984) : ℂ) * ζ ^ 38 + ((17893 / 4246) : ℂ) * ζ ^ 39 - ((23795 / 16984) : ℂ) * ζ ^ 40 - ((18307 / 4246) : ℂ) * ζ ^ 41 - ((31949 / 16984) : ℂ) * ζ ^ 42 - ((6271 / 4246) : ℂ) * ζ ^ 43 + ((32323 / 8492) : ℂ) * ζ ^ 44 - ((34389 / 16984) : ℂ) * ζ ^ 45 - ((31949 / 16984) : ℂ) * ζ ^ 46 + ((13193 / 8492) : ℂ) * ζ ^ 47 - ((2338 / 2123) : ℂ) * ζ ^ 48 + ((18701 / 16984) : ℂ) * ζ ^ 49 + ((9875 / 16984) : ℂ) * ζ ^ 50 + ((13193 / 8492) : ℂ) * ζ ^ 51 - ((437 / 386) : ℂ) * ζ ^ 52 + ((36723 / 8492) : ℂ) * ζ ^ 53 + ((11037 / 8492) : ℂ) * ζ ^ 54 - ((575 / 4246) : ℂ) * ζ ^ 55 - ((437 / 386) : ℂ) * ζ ^ 56 + ((22229 / 16984) : ℂ) * ζ ^ 57 + ((337 / 2123) : ℂ) * ζ ^ 58 - ((12043 / 8492) : ℂ) * ζ ^ 59 + ((437 / 386) : ℂ) * ζ ^ 60 - ((22229 / 16984) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_3_5 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        3 5 =
      alternatingSixAmbientRow13TransformedGeneratorA
        3 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((81 / 386) : ℂ) + ((36033 / 8492) : ℂ) * ζ ^ 3 - ((81 / 386) : ℂ) * ζ ^ 4 + ((19193 / 8492) : ℂ) * ζ ^ 5 - ((18393 / 8492) : ℂ) * ζ ^ 6 - ((5235 / 8492) : ℂ) * ζ ^ 8 + ((1119 / 2123) : ℂ) * ζ ^ 9 - ((9816 / 2123) : ℂ) * ζ ^ 10 - ((18761 / 4246) : ℂ) * ζ ^ 11 + ((20447 / 4246) : ℂ) * ζ ^ 13 + ((20871 / 8492) : ℂ) * ζ ^ 14 - ((9263 / 4246) : ℂ) * ζ ^ 15 + ((3901 / 2123) : ℂ) * ζ ^ 16 + ((23669 / 8492) : ℂ) * ζ ^ 17 + ((5417 / 2123) : ℂ) * ζ ^ 18 - ((4749 / 2123) : ℂ) * ζ ^ 19 + ((50177 / 8492) : ℂ) * ζ ^ 20 + ((369 / 2123) : ℂ) * ζ ^ 21 + ((18393 / 8492) : ℂ) * ζ ^ 22 - ((57177 / 8492) : ℂ) * ζ ^ 23 - ((3143 / 772) : ℂ) * ζ ^ 24 - ((62415 / 8492) : ℂ) * ζ ^ 25 - ((1310 / 2123) : ℂ) * ζ ^ 26 + ((18761 / 4246) : ℂ) * ζ ^ 27 - ((9997 / 8492) : ℂ) * ζ ^ 28 - ((78123 / 8492) : ℂ) * ζ ^ 29 - ((25863 / 8492) : ℂ) * ζ ^ 30 + ((9291 / 772) : ℂ) * ζ ^ 31 - ((3901 / 2123) : ℂ) * ζ ^ 32 - ((6415 / 2123) : ℂ) * ζ ^ 33 - ((16163 / 8492) : ℂ) * ζ ^ 34 + ((14149 / 4246) : ℂ) * ζ ^ 35 + ((2303 / 2123) : ℂ) * ζ ^ 36 + ((22931 / 4246) : ℂ) * ζ ^ 37 - ((161 / 44) : ℂ) * ζ ^ 38 - ((1141 / 8492) : ℂ) * ζ ^ 39 + ((1717 / 772) : ℂ) * ζ ^ 40 + ((22931 / 4246) : ℂ) * ζ ^ 41 + ((23633 / 8492) : ℂ) * ζ ^ 42 + ((3983 / 4246) : ℂ) * ζ ^ 43 + ((21533 / 8492) : ℂ) * ζ ^ 44 + ((53391 / 8492) : ℂ) * ζ ^ 45 + ((23633 / 8492) : ℂ) * ζ ^ 46 - ((64679 / 8492) : ℂ) * ζ ^ 47 - ((10883 / 8492) : ℂ) * ζ ^ 48 - ((4577 / 8492) : ℂ) * ζ ^ 49 - ((28631 / 8492) : ℂ) * ζ ^ 50 - ((64679 / 8492) : ℂ) * ζ ^ 51 - ((564 / 193) : ℂ) * ζ ^ 52 - ((33369 / 8492) : ℂ) * ζ ^ 53 + ((2499 / 4246) : ℂ) * ζ ^ 54 + ((1509 / 386) : ℂ) * ζ ^ 55 - ((564 / 193) : ℂ) * ζ ^ 56 - ((23669 / 8492) : ℂ) * ζ ^ 57 + ((8449 / 4246) : ℂ) * ζ ^ 58 + ((31481 / 8492) : ℂ) * ζ ^ 59 + ((564 / 193) : ℂ) * ζ ^ 60 + ((23669 / 8492) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_4_0 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        4 0 =
      alternatingSixAmbientRow13TransformedGeneratorA
        4 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((3419 / 772) : ℂ) + ((1274 / 193) : ℂ) * ζ ^ 3 - ((3419 / 772) : ℂ) * ζ ^ 4 + ((8767 / 1544) : ℂ) * ζ ^ 5 - ((1101 / 1544) : ℂ) * ζ ^ 6 + ((10865 / 1544) : ℂ) * ζ ^ 8 - ((1867 / 193) : ℂ) * ζ ^ 9 - ((4049 / 1544) : ℂ) * ζ ^ 10 + ((2631 / 1544) : ℂ) * ζ ^ 11 - ((5671 / 1544) : ℂ) * ζ ^ 13 + ((737 / 386) : ℂ) * ζ ^ 14 - ((3083 / 1544) : ℂ) * ζ ^ 15 - ((211 / 193) : ℂ) * ζ ^ 16 - ((6169 / 1544) : ℂ) * ζ ^ 17 - ((4301 / 1544) : ℂ) * ζ ^ 18 + ((2857 / 772) : ℂ) * ζ ^ 19 - ((1427 / 772) : ℂ) * ζ ^ 20 + ((1007 / 193) : ℂ) * ζ ^ 21 + ((1101 / 1544) : ℂ) * ζ ^ 22 - ((12215 / 1544) : ℂ) * ζ ^ 23 + ((583 / 772) : ℂ) * ζ ^ 24 + ((11579 / 772) : ℂ) * ζ ^ 25 - ((215 / 772) : ℂ) * ζ ^ 26 - ((2631 / 1544) : ℂ) * ζ ^ 27 - ((1419 / 386) : ℂ) * ζ ^ 28 + ((2739 / 193) : ℂ) * ζ ^ 29 - ((10089 / 1544) : ℂ) * ζ ^ 30 - ((6837 / 1544) : ℂ) * ζ ^ 31 + ((211 / 193) : ℂ) * ζ ^ 32 - ((5605 / 1544) : ℂ) * ζ ^ 33 + ((7457 / 1544) : ℂ) * ζ ^ 34 - ((1939 / 386) : ℂ) * ζ ^ 35 + ((1193 / 1544) : ℂ) * ζ ^ 36 - ((10197 / 772) : ℂ) * ζ ^ 37 + ((941 / 1544) : ℂ) * ζ ^ 38 + ((6181 / 1544) : ℂ) * ζ ^ 39 + ((262 / 193) : ℂ) * ζ ^ 40 - ((10197 / 772) : ℂ) * ζ ^ 41 + ((1531 / 1544) : ℂ) * ζ ^ 42 + ((11303 / 1544) : ℂ) * ζ ^ 43 - ((4279 / 1544) : ℂ) * ζ ^ 44 - ((4205 / 772) : ℂ) * ζ ^ 45 + ((1531 / 1544) : ℂ) * ζ ^ 46 + ((2103 / 772) : ℂ) * ζ ^ 47 + ((923 / 193) : ℂ) * ζ ^ 48 + ((516 / 193) : ℂ) * ζ ^ 49 + ((1193 / 772) : ℂ) * ζ ^ 50 + ((2103 / 772) : ℂ) * ζ ^ 51 + ((495 / 1544) : ℂ) * ζ ^ 52 + ((13395 / 1544) : ℂ) * ζ ^ 53 - ((3917 / 1544) : ℂ) * ζ ^ 54 + ((1101 / 1544) : ℂ) * ζ ^ 55 + ((495 / 1544) : ℂ) * ζ ^ 56 + ((6169 / 1544) : ℂ) * ζ ^ 57 - ((2229 / 1544) : ℂ) * ζ ^ 58 - ((5307 / 1544) : ℂ) * ζ ^ 59 - ((495 / 1544) : ℂ) * ζ ^ 60 - ((6169 / 1544) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_4_1 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        4 1 =
      alternatingSixAmbientRow13TransformedGeneratorA
        4 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((1303 / 1158) : ℂ) + ((1265 / 1158) : ℂ) * ζ ^ 3 - ((1303 / 1158) : ℂ) * ζ ^ 4 + ((5839 / 2316) : ℂ) * ζ ^ 5 - ζ ^ 6 + ((13019 / 2316) : ℂ) * ζ ^ 8 - ((1538 / 579) : ℂ) * ζ ^ 9 - ((12191 / 2316) : ℂ) * ζ ^ 10 + ((147 / 193) : ℂ) * ζ ^ 11 - ((1666 / 579) : ℂ) * ζ ^ 13 + ((9875 / 2316) : ℂ) * ζ ^ 14 + ((4885 / 2316) : ℂ) * ζ ^ 15 - ((6113 / 1158) : ℂ) * ζ ^ 16 - ((313 / 2316) : ℂ) * ζ ^ 17 + ((3121 / 2316) : ℂ) * ζ ^ 18 - ((3121 / 2316) : ℂ) * ζ ^ 19 - ((119 / 772) : ℂ) * ζ ^ 20 + ((667 / 386) : ℂ) * ζ ^ 21 + ζ ^ 22 - ((1467 / 386) : ℂ) * ζ ^ 23 - ((11869 / 2316) : ℂ) * ζ ^ 24 + ((2233 / 772) : ℂ) * ζ ^ 25 - ((4021 / 2316) : ℂ) * ζ ^ 26 - ((147 / 193) : ℂ) * ζ ^ 27 + ((5235 / 772) : ℂ) * ζ ^ 28 - ((273 / 772) : ℂ) * ζ ^ 29 - ((4001 / 772) : ℂ) * ζ ^ 30 + ((2233 / 2316) : ℂ) * ζ ^ 31 + ((6113 / 1158) : ℂ) * ζ ^ 32 + ((1089 / 772) : ℂ) * ζ ^ 33 + ((1675 / 1158) : ℂ) * ζ ^ 34 - ((4907 / 772) : ℂ) * ζ ^ 35 + ((6509 / 1158) : ℂ) * ζ ^ 36 - ((1157 / 579) : ℂ) * ζ ^ 37 - ((620 / 579) : ℂ) * ζ ^ 38 + ((10241 / 1158) : ℂ) * ζ ^ 39 - ((833 / 772) : ℂ) * ζ ^ 40 - ((1157 / 579) : ℂ) * ζ ^ 41 + ((6337 / 2316) : ℂ) * ζ ^ 42 - ((4361 / 1158) : ℂ) * ζ ^ 43 - ((8935 / 2316) : ℂ) * ζ ^ 44 + ((1349 / 193) : ℂ) * ζ ^ 45 + ((6337 / 2316) : ℂ) * ζ ^ 46 - ((3997 / 2316) : ℂ) * ζ ^ 47 - ((1143 / 772) : ℂ) * ζ ^ 48 - ((3203 / 579) : ℂ) * ζ ^ 49 - ((1304 / 579) : ℂ) * ζ ^ 50 - ((3997 / 2316) : ℂ) * ζ ^ 51 - ((66 / 193) : ℂ) * ζ ^ 52 + ((971 / 2316) : ℂ) * ζ ^ 53 - ((1121 / 2316) : ℂ) * ζ ^ 54 - ((1469 / 1158) : ℂ) * ζ ^ 55 - ((66 / 193) : ℂ) * ζ ^ 56 + ((313 / 2316) : ℂ) * ζ ^ 57 + ((353 / 2316) : ℂ) * ζ ^ 58 + ((6935 / 2316) : ℂ) * ζ ^ 59 + ((66 / 193) : ℂ) * ζ ^ 60 - ((313 / 2316) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_4_2 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        4 2 =
      alternatingSixAmbientRow13TransformedGeneratorA
        4 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((1755 / 386) : ℂ) - ((1379 / 772) : ℂ) * ζ ^ 3 - ((1755 / 386) : ℂ) * ζ ^ 4 + ((2237 / 1544) : ℂ) * ζ ^ 5 - ((9749 / 1544) : ℂ) * ζ ^ 6 + ((14319 / 1544) : ℂ) * ζ ^ 8 - ((3351 / 772) : ℂ) * ζ ^ 9 - ((8173 / 1544) : ℂ) * ζ ^ 10 - ((779 / 1544) : ℂ) * ζ ^ 11 - ((1913 / 1544) : ℂ) * ζ ^ 13 - ((197 / 193) : ℂ) * ζ ^ 14 - ((3403 / 1544) : ℂ) * ζ ^ 15 - ((839 / 386) : ℂ) * ζ ^ 16 - ((4465 / 1544) : ℂ) * ζ ^ 17 - ((1259 / 1544) : ℂ) * ζ ^ 18 + ((328 / 193) : ℂ) * ζ ^ 19 - ((1639 / 386) : ℂ) * ζ ^ 20 + ((1691 / 386) : ℂ) * ζ ^ 21 + ((9749 / 1544) : ℂ) * ζ ^ 22 - ((7727 / 1544) : ℂ) * ζ ^ 23 + ((400 / 193) : ℂ) * ζ ^ 24 + ((3167 / 193) : ℂ) * ζ ^ 25 + ((1230 / 193) : ℂ) * ζ ^ 26 + ((779 / 1544) : ℂ) * ζ ^ 27 + ((109 / 193) : ℂ) * ζ ^ 28 + ((4109 / 772) : ℂ) * ζ ^ 29 - ((5159 / 1544) : ℂ) * ζ ^ 30 - ((4481 / 1544) : ℂ) * ζ ^ 31 + ((839 / 386) : ℂ) * ζ ^ 32 - ((1451 / 1544) : ℂ) * ζ ^ 33 - ((4499 / 1544) : ℂ) * ζ ^ 34 - ((8107 / 772) : ℂ) * ζ ^ 35 + ((367 / 1544) : ℂ) * ζ ^ 36 - ((7847 / 772) : ℂ) * ζ ^ 37 - ((1843 / 1544) : ℂ) * ζ ^ 38 + ((10175 / 1544) : ℂ) * ζ ^ 39 - ((2679 / 772) : ℂ) * ζ ^ 40 - ((7847 / 772) : ℂ) * ζ ^ 41 - ((91 / 1544) : ℂ) * ζ ^ 42 + ((6143 / 1544) : ℂ) * ζ ^ 43 - ((987 / 1544) : ℂ) * ζ ^ 44 - ((1079 / 772) : ℂ) * ζ ^ 45 - ((91 / 1544) : ℂ) * ζ ^ 46 + ((1315 / 386) : ℂ) * ζ ^ 47 + ((975 / 386) : ℂ) * ζ ^ 48 - ((1 / 193) : ℂ) * ζ ^ 49 + ((1611 / 772) : ℂ) * ζ ^ 50 + ((1315 / 386) : ℂ) * ζ ^ 51 + ((2989 / 1544) : ℂ) * ζ ^ 52 + ((8739 / 1544) : ℂ) * ζ ^ 53 - ((3131 / 1544) : ℂ) * ζ ^ 54 + ((249 / 1544) : ℂ) * ζ ^ 55 + ((2989 / 1544) : ℂ) * ζ ^ 56 + ((4465 / 1544) : ℂ) * ζ ^ 57 - ((2229 / 1544) : ℂ) * ζ ^ 58 - ((5509 / 1544) : ℂ) * ζ ^ 59 - ((2989 / 1544) : ℂ) * ζ ^ 60 - ((4465 / 1544) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_4_3 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        4 3 =
      alternatingSixAmbientRow13TransformedGeneratorA
        4 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((2682 / 193) : ℂ) - ((10865 / 1544) : ℂ) * ζ ^ 3 - ((2682 / 193) : ℂ) * ζ ^ 4 + ((3619 / 386) : ℂ) * ζ ^ 5 - ((2983 / 386) : ℂ) * ζ ^ 6 + ((22039 / 1544) : ℂ) * ζ ^ 8 - ((9917 / 1544) : ℂ) * ζ ^ 9 - ((27061 / 1544) : ℂ) * ζ ^ 10 - ((1637 / 772) : ℂ) * ζ ^ 11 + ((16495 / 1544) : ℂ) * ζ ^ 13 + ((15129 / 1544) : ℂ) * ζ ^ 14 - ((803 / 193) : ℂ) * ζ ^ 15 - ((4323 / 1544) : ℂ) * ζ ^ 16 + ((4559 / 1544) : ℂ) * ζ ^ 17 + ((12893 / 772) : ℂ) * ζ ^ 18 + ((1575 / 772) : ℂ) * ζ ^ 19 - ((7491 / 772) : ℂ) * ζ ^ 20 - ((231 / 1544) : ℂ) * ζ ^ 21 + ((2983 / 386) : ℂ) * ζ ^ 22 - ((2001 / 386) : ℂ) * ζ ^ 23 + ((10659 / 1544) : ℂ) * ζ ^ 24 - ((13993 / 1544) : ℂ) * ζ ^ 25 + ((362 / 193) : ℂ) * ζ ^ 26 + ((1637 / 772) : ℂ) * ζ ^ 27 - ((5443 / 386) : ℂ) * ζ ^ 28 - ((1699 / 193) : ℂ) * ζ ^ 29 + ((3761 / 1544) : ℂ) * ζ ^ 30 + ((8933 / 1544) : ℂ) * ζ ^ 31 + ((4323 / 1544) : ℂ) * ζ ^ 32 - ((7925 / 772) : ℂ) * ζ ^ 33 - ((24729 / 1544) : ℂ) * ζ ^ 34 + ((1697 / 772) : ℂ) * ζ ^ 35 + ((3331 / 386) : ℂ) * ζ ^ 36 + ((9349 / 1544) : ℂ) * ζ ^ 37 - ((1532 / 193) : ℂ) * ζ ^ 38 - ((1009 / 1544) : ℂ) * ζ ^ 39 + ((3545 / 1544) : ℂ) * ζ ^ 40 + ((9349 / 1544) : ℂ) * ζ ^ 41 + ((2259 / 386) : ℂ) * ζ ^ 42 + ((3253 / 1544) : ℂ) * ζ ^ 43 + ((1133 / 1544) : ℂ) * ζ ^ 44 + ((7297 / 1544) : ℂ) * ζ ^ 45 + ((2259 / 386) : ℂ) * ζ ^ 46 - ((5659 / 1544) : ℂ) * ζ ^ 47 + ((8217 / 1544) : ℂ) * ζ ^ 48 + ((795 / 772) : ℂ) * ζ ^ 49 - ((14365 / 1544) : ℂ) * ζ ^ 50 - ((5659 / 1544) : ℂ) * ζ ^ 51 - ((9001 / 1544) : ℂ) * ζ ^ 52 - ((6545 / 1544) : ℂ) * ζ ^ 53 + ((5329 / 1544) : ℂ) * ζ ^ 54 + ((5561 / 1544) : ℂ) * ζ ^ 55 - ((9001 / 1544) : ℂ) * ζ ^ 56 - ((4559 / 1544) : ℂ) * ζ ^ 57 + ((121 / 1544) : ℂ) * ζ ^ 58 + ((49 / 772) : ℂ) * ζ ^ 59 + ((9001 / 1544) : ℂ) * ζ ^ 60 + ((4559 / 1544) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_4_4 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        4 4 =
      alternatingSixAmbientRow13TransformedGeneratorA
        4 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((9512 / 2123) : ℂ) + ((24085 / 8492) : ℂ) * ζ ^ 3 - ((9512 / 2123) : ℂ) * ζ ^ 4 - ((118265 / 16984) : ℂ) * ζ ^ 5 + ((26107 / 16984) : ℂ) * ζ ^ 6 + ((75177 / 16984) : ℂ) * ζ ^ 8 + ((28033 / 4246) : ℂ) * ζ ^ 9 - ((50045 / 16984) : ℂ) * ζ ^ 10 + ((1677 / 1544) : ℂ) * ζ ^ 11 - ((68097 / 16984) : ℂ) * ζ ^ 13 + ((9519 / 2123) : ℂ) * ζ ^ 14 + ((136369 / 16984) : ℂ) * ζ ^ 15 - ((67 / 8492) : ℂ) * ζ ^ 16 - ((6133 / 16984) : ℂ) * ζ ^ 17 - ((6267 / 1544) : ℂ) * ζ ^ 18 - ((58961 / 8492) : ℂ) * ζ ^ 19 + ((34033 / 8492) : ℂ) * ζ ^ 20 + ((4985 / 8492) : ℂ) * ζ ^ 21 - ((26107 / 16984) : ℂ) * ζ ^ 22 + ((1333 / 16984) : ℂ) * ζ ^ 23 - ((775 / 193) : ℂ) * ζ ^ 24 + ((16217 / 4246) : ℂ) * ζ ^ 25 - ((24979 / 8492) : ℂ) * ζ ^ 26 - ((1677 / 1544) : ℂ) * ζ ^ 27 + ((49153 / 8492) : ℂ) * ζ ^ 28 - ((4525 / 4246) : ℂ) * ζ ^ 29 - ((47389 / 16984) : ℂ) * ζ ^ 30 - ((4255 / 1544) : ℂ) * ζ ^ 31 + ((67 / 8492) : ℂ) * ζ ^ 32 + ((37965 / 16984) : ℂ) * ζ ^ 33 + ((49645 / 16984) : ℂ) * ζ ^ 34 - ((41641 / 4246) : ℂ) * ζ ^ 35 + ((5235 / 16984) : ℂ) * ζ ^ 36 - ((5559 / 4246) : ℂ) * ζ ^ 37 - ((2251 / 1544) : ℂ) * ζ ^ 38 + ((156653 / 16984) : ℂ) * ζ ^ 39 + ((22101 / 8492) : ℂ) * ζ ^ 40 - ((5559 / 4246) : ℂ) * ζ ^ 41 + ((23851 / 16984) : ℂ) * ζ ^ 42 - ((35403 / 16984) : ℂ) * ζ ^ 43 - ((39235 / 16984) : ℂ) * ζ ^ 44 + ((7432 / 2123) : ℂ) * ζ ^ 45 + ((23851 / 16984) : ℂ) * ζ ^ 46 + ((1289 / 772) : ℂ) * ζ ^ 47 - ((6981 / 8492) : ℂ) * ζ ^ 48 - ((7719 / 2123) : ℂ) * ζ ^ 49 - ((11217 / 4246) : ℂ) * ζ ^ 50 + ((1289 / 772) : ℂ) * ζ ^ 51 - ((5101 / 16984) : ℂ) * ζ ^ 52 + ((14679 / 16984) : ℂ) * ζ ^ 53 + ((21017 / 16984) : ℂ) * ζ ^ 54 - ((31257 / 16984) : ℂ) * ζ ^ 55 - ((5101 / 16984) : ℂ) * ζ ^ 56 + ((6133 / 16984) : ℂ) * ζ ^ 57 + ((569 / 16984) : ℂ) * ζ ^ 58 + ((2899 / 16984) : ℂ) * ζ ^ 59 + ((5101 / 16984) : ℂ) * ζ ^ 60 - ((6133 / 16984) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_4_5 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        4 5 =
      alternatingSixAmbientRow13TransformedGeneratorA
        4 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((10851 / 8492) : ℂ) + ((5645 / 4246) : ℂ) * ζ ^ 3 + ((10851 / 8492) : ℂ) * ζ ^ 4 - ((2542 / 2123) : ℂ) * ζ ^ 5 + ((37333 / 8492) : ℂ) * ζ ^ 6 - ((48127 / 8492) : ℂ) * ζ ^ 8 + ((7959 / 2123) : ℂ) * ζ ^ 9 + ((2775 / 772) : ℂ) * ζ ^ 10 - ((2855 / 4246) : ℂ) * ζ ^ 11 + ((34889 / 8492) : ℂ) * ζ ^ 13 + ((1702 / 2123) : ℂ) * ζ ^ 14 + ((31651 / 8492) : ℂ) * ζ ^ 15 + ((15991 / 8492) : ℂ) * ζ ^ 16 + ((5417 / 2123) : ℂ) * ζ ^ 17 + ((21887 / 4246) : ℂ) * ζ ^ 18 - ((37361 / 8492) : ℂ) * ζ ^ 19 + ((2215 / 8492) : ℂ) * ζ ^ 20 - ((6373 / 8492) : ℂ) * ζ ^ 21 - ((37333 / 8492) : ℂ) * ζ ^ 22 + ((655 / 8492) : ℂ) * ζ ^ 23 + ((3444 / 2123) : ℂ) * ζ ^ 24 - ((90775 / 8492) : ℂ) * ζ ^ 25 - ((16706 / 2123) : ℂ) * ζ ^ 26 + ((2855 / 4246) : ℂ) * ζ ^ 27 - ((11389 / 8492) : ℂ) * ζ ^ 28 - ((2073 / 386) : ℂ) * ζ ^ 29 - ((17257 / 8492) : ℂ) * ζ ^ 30 + ((22547 / 4246) : ℂ) * ζ ^ 31 - ((15991 / 8492) : ℂ) * ζ ^ 32 - ((25015 / 4246) : ℂ) * ζ ^ 33 + ((25099 / 8492) : ℂ) * ζ ^ 34 + ((26927 / 4246) : ℂ) * ζ ^ 35 + ((6475 / 8492) : ℂ) * ζ ^ 36 + ((4519 / 772) : ℂ) * ζ ^ 37 - ((15139 / 8492) : ℂ) * ζ ^ 38 - ((5045 / 2123) : ℂ) * ζ ^ 39 + ((47605 / 8492) : ℂ) * ζ ^ 40 + ((4519 / 772) : ℂ) * ζ ^ 41 + ((2681 / 772) : ℂ) * ζ ^ 42 + ((2229 / 2123) : ℂ) * ζ ^ 43 - ((2287 / 2123) : ℂ) * ζ ^ 44 + ((19157 / 4246) : ℂ) * ζ ^ 45 + ((2681 / 772) : ℂ) * ζ ^ 46 - ((9846 / 2123) : ℂ) * ζ ^ 47 + ((457 / 386) : ℂ) * ζ ^ 48 - ((7 / 44) : ℂ) * ζ ^ 49 - ((10278 / 2123) : ℂ) * ζ ^ 50 - ((9846 / 2123) : ℂ) * ζ ^ 51 - ((11233 / 4246) : ℂ) * ζ ^ 52 - ((40275 / 8492) : ℂ) * ζ ^ 53 + ((11621 / 8492) : ℂ) * ζ ^ 54 + ((21401 / 8492) : ℂ) * ζ ^ 55 - ((11233 / 4246) : ℂ) * ζ ^ 56 - ((5417 / 2123) : ℂ) * ζ ^ 57 - ((128 / 2123) : ℂ) * ζ ^ 58 + ((17983 / 8492) : ℂ) * ζ ^ 59 + ((11233 / 4246) : ℂ) * ζ ^ 60 + ((5417 / 2123) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_5_0 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        5 0 =
      alternatingSixAmbientRow13TransformedGeneratorA
        5 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((335 / 193) : ℂ) + ((105 / 386) : ℂ) * ζ ^ 3 + ((335 / 193) : ℂ) * ζ ^ 4 - ((3143 / 772) : ℂ) * ζ ^ 5 - ((1307 / 772) : ℂ) * ζ ^ 6 + ((2972 / 193) : ℂ) * ζ ^ 8 - ((2917 / 772) : ℂ) * ζ ^ 9 - ((771 / 193) : ℂ) * ζ ^ 10 + ((2829 / 386) : ℂ) * ζ ^ 11 - ((10893 / 772) : ℂ) * ζ ^ 13 + ((1777 / 772) : ℂ) * ζ ^ 14 + ((9489 / 772) : ℂ) * ζ ^ 15 - ((5483 / 386) : ℂ) * ζ ^ 16 - ((1515 / 193) : ℂ) * ζ ^ 17 - ((748 / 193) : ℂ) * ζ ^ 18 - ((3831 / 772) : ℂ) * ζ ^ 19 - ((3347 / 772) : ℂ) * ζ ^ 20 + ((1378 / 193) : ℂ) * ζ ^ 21 + ((1307 / 772) : ℂ) * ζ ^ 22 + ((1712 / 193) : ℂ) * ζ ^ 23 - ((7619 / 772) : ℂ) * ζ ^ 24 + ((5372 / 193) : ℂ) * ζ ^ 25 + ((1193 / 193) : ℂ) * ζ ^ 26 - ((2829 / 386) : ℂ) * ζ ^ 27 + ((521 / 772) : ℂ) * ζ ^ 28 + ((5096 / 193) : ℂ) * ζ ^ 29 + ((807 / 772) : ℂ) * ζ ^ 30 - ((13515 / 772) : ℂ) * ζ ^ 31 + ((5483 / 386) : ℂ) * ζ ^ 32 - ((1659 / 386) : ℂ) * ζ ^ 33 + ((7 / 4) : ℂ) * ζ ^ 34 - ((4819 / 386) : ℂ) * ζ ^ 35 + ((3370 / 193) : ℂ) * ζ ^ 36 - ((4408 / 193) : ℂ) * ζ ^ 37 - ((687 / 772) : ℂ) * ζ ^ 38 + ((7439 / 772) : ℂ) * ζ ^ 39 - ((4855 / 386) : ℂ) * ζ ^ 40 - ((4408 / 193) : ℂ) * ζ ^ 41 - ((3465 / 772) : ℂ) * ζ ^ 42 + ((3293 / 772) : ℂ) * ζ ^ 43 + ((629 / 386) : ℂ) * ζ ^ 44 - ((3891 / 193) : ℂ) * ζ ^ 45 - ((3465 / 772) : ℂ) * ζ ^ 46 + ((7857 / 772) : ℂ) * ζ ^ 47 - ((1073 / 193) : ℂ) * ζ ^ 48 + ((2239 / 193) : ℂ) * ζ ^ 49 + ((929 / 772) : ℂ) * ζ ^ 50 + ((7857 / 772) : ℂ) * ζ ^ 51 - ((1257 / 386) : ℂ) * ζ ^ 52 + ((12569 / 772) : ℂ) * ζ ^ 53 + ((634 / 193) : ℂ) * ζ ^ 54 - ((537 / 193) : ℂ) * ζ ^ 55 - ((1257 / 386) : ℂ) * ζ ^ 56 + ((1515 / 193) : ℂ) * ζ ^ 57 + ((2343 / 772) : ℂ) * ζ ^ 58 - ((5709 / 772) : ℂ) * ζ ^ 59 + ((1257 / 386) : ℂ) * ζ ^ 60 - ((1515 / 193) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_5_1 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        5 1 =
      alternatingSixAmbientRow13TransformedGeneratorA
        5 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((1753 / 1158) : ℂ) + ((198 / 193) : ℂ) * ζ ^ 3 + ((1753 / 1158) : ℂ) * ζ ^ 4 - ((863 / 1158) : ℂ) * ζ ^ 5 - ((2923 / 1158) : ℂ) * ζ ^ 6 + ((2206 / 579) : ℂ) * ζ ^ 8 + ((485 / 386) : ℂ) * ζ ^ 9 - ((131 / 386) : ℂ) * ζ ^ 10 + ((6 / 193) : ℂ) * ζ ^ 11 + ((1231 / 1158) : ℂ) * ζ ^ 13 - ((1265 / 579) : ℂ) * ζ ^ 14 + ((7001 / 1158) : ℂ) * ζ ^ 15 - ((2089 / 579) : ℂ) * ζ ^ 16 + ((296 / 579) : ℂ) * ζ ^ 17 + ((2308 / 579) : ℂ) * ζ ^ 18 - ((6965 / 1158) : ℂ) * ζ ^ 19 + ((127 / 1158) : ℂ) * ζ ^ 20 - ((3215 / 1158) : ℂ) * ζ ^ 21 + ((2923 / 1158) : ℂ) * ζ ^ 22 + ((2005 / 579) : ℂ) * ζ ^ 23 - ((1435 / 386) : ℂ) * ζ ^ 24 - ((583 / 386) : ℂ) * ζ ^ 25 - ((2200 / 579) : ℂ) * ζ ^ 26 - ((6 / 193) : ℂ) * ζ ^ 27 + ((13331 / 1158) : ℂ) * ζ ^ 28 - ((13 / 3) : ℂ) * ζ ^ 29 - ((6869 / 579) : ℂ) * ζ ^ 30 + ((392 / 193) : ℂ) * ζ ^ 31 + ((2089 / 579) : ℂ) * ζ ^ 32 - ((4177 / 1158) : ℂ) * ζ ^ 33 + ((582 / 193) : ℂ) * ζ ^ 34 + ((813 / 193) : ℂ) * ζ ^ 35 - ((2369 / 1158) : ℂ) * ζ ^ 36 + ((4399 / 1158) : ℂ) * ζ ^ 37 + ((1963 / 386) : ℂ) * ζ ^ 38 - ((409 / 193) : ℂ) * ζ ^ 39 + ((3419 / 1158) : ℂ) * ζ ^ 40 + ((4399 / 1158) : ℂ) * ζ ^ 41 + ((2441 / 386) : ℂ) * ζ ^ 42 - ((838 / 579) : ℂ) * ζ ^ 43 - ((7072 / 579) : ℂ) * ζ ^ 44 - ((5011 / 1158) : ℂ) * ζ ^ 45 + ((2441 / 386) : ℂ) * ζ ^ 46 - ((398 / 193) : ℂ) * ζ ^ 47 + ((1169 / 579) : ℂ) * ζ ^ 48 + ((1490 / 579) : ℂ) * ζ ^ 49 - ((1874 / 579) : ℂ) * ζ ^ 50 - ((398 / 193) : ℂ) * ζ ^ 51 + ((6547 / 1158) : ℂ) * ζ ^ 52 + ((1885 / 1158) : ℂ) * ζ ^ 53 - ((3575 / 1158) : ℂ) * ζ ^ 54 - ((487 / 1158) : ℂ) * ζ ^ 55 + ((6547 / 1158) : ℂ) * ζ ^ 56 - ((296 / 579) : ℂ) * ζ ^ 57 - ((1094 / 193) : ℂ) * ζ ^ 58 + ((2875 / 1158) : ℂ) * ζ ^ 59 - ((6547 / 1158) : ℂ) * ζ ^ 60 + ((296 / 579) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_5_2 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        5 2 =
      alternatingSixAmbientRow13TransformedGeneratorA
        5 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((398 / 193) : ℂ) + ((381 / 193) : ℂ) * ζ ^ 3 + ((398 / 193) : ℂ) * ζ ^ 4 + ((1781 / 772) : ℂ) * ζ ^ 5 - ((8409 / 772) : ℂ) * ζ ^ 6 + ((2499 / 193) : ℂ) * ζ ^ 8 - ((4119 / 772) : ℂ) * ζ ^ 9 - ((2062 / 193) : ℂ) * ζ ^ 10 + ((753 / 386) : ℂ) * ζ ^ 11 - ((9957 / 772) : ℂ) * ζ ^ 13 - ((161 / 772) : ℂ) * ζ ^ 14 + ((731 / 772) : ℂ) * ζ ^ 15 - ((1983 / 386) : ℂ) * ζ ^ 16 - ((1169 / 386) : ℂ) * ζ ^ 17 + ((2909 / 386) : ℂ) * ζ ^ 18 + ((775 / 772) : ℂ) * ζ ^ 19 + ((6673 / 772) : ℂ) * ζ ^ 20 - ((172 / 193) : ℂ) * ζ ^ 21 + ((8409 / 772) : ℂ) * ζ ^ 22 + ((2463 / 386) : ℂ) * ζ ^ 23 - ((10639 / 772) : ℂ) * ζ ^ 24 + ((2384 / 193) : ℂ) * ζ ^ 25 + ((2469 / 386) : ℂ) * ζ ^ 26 - ((753 / 386) : ℂ) * ζ ^ 27 - ((2189 / 772) : ℂ) * ζ ^ 28 + ((951 / 193) : ℂ) * ζ ^ 29 - ((8959 / 772) : ℂ) * ζ ^ 30 - ((4843 / 772) : ℂ) * ζ ^ 31 + ((1983 / 386) : ℂ) * ζ ^ 32 + ((88 / 193) : ℂ) * ζ ^ 33 - ((2921 / 772) : ℂ) * ζ ^ 34 - ((763 / 193) : ℂ) * ζ ^ 35 + ((2617 / 386) : ℂ) * ζ ^ 36 - ((997 / 193) : ℂ) * ζ ^ 37 - ((2253 / 772) : ℂ) * ζ ^ 38 + ((1221 / 772) : ℂ) * ζ ^ 39 - ((373 / 386) : ℂ) * ζ ^ 40 - ((997 / 193) : ℂ) * ζ ^ 41 + ((3471 / 772) : ℂ) * ζ ^ 42 + ((2663 / 772) : ℂ) * ζ ^ 43 - ((488 / 193) : ℂ) * ζ ^ 44 - ((3387 / 386) : ℂ) * ζ ^ 45 + ((3471 / 772) : ℂ) * ζ ^ 46 + ((3337 / 772) : ℂ) * ζ ^ 47 - ((1471 / 386) : ℂ) * ζ ^ 48 + ((705 / 386) : ℂ) * ζ ^ 49 - ((2857 / 772) : ℂ) * ζ ^ 50 + ((3337 / 772) : ℂ) * ζ ^ 51 - ((317 / 193) : ℂ) * ζ ^ 52 + ((3405 / 772) : ℂ) * ζ ^ 53 - ((307 / 386) : ℂ) * ζ ^ 54 - ((470 / 193) : ℂ) * ζ ^ 55 - ((317 / 193) : ℂ) * ζ ^ 56 + ((1169 / 386) : ℂ) * ζ ^ 57 + ((2343 / 772) : ℂ) * ζ ^ 58 - ((1457 / 772) : ℂ) * ζ ^ 59 + ((317 / 193) : ℂ) * ζ ^ 60 - ((1169 / 386) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_5_3 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        5 3 =
      alternatingSixAmbientRow13TransformedGeneratorA
        5 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((5819 / 772) : ℂ) + ((9091 / 772) : ℂ) * ζ ^ 3 + ((5819 / 772) : ℂ) * ζ ^ 4 - ((1545 / 772) : ℂ) * ζ ^ 5 - ((15169 / 772) : ℂ) * ζ ^ 6 + ((11023 / 386) : ℂ) * ζ ^ 8 + ((68 / 193) : ℂ) * ζ ^ 9 - ((13337 / 772) : ℂ) * ζ ^ 10 - ((2157 / 386) : ℂ) * ζ ^ 11 - ((3353 / 193) : ℂ) * ζ ^ 13 - ((458 / 193) : ℂ) * ζ ^ 14 + ((5109 / 386) : ℂ) * ζ ^ 15 - ((14601 / 772) : ℂ) * ζ ^ 16 - ((1273 / 772) : ℂ) * ζ ^ 17 + ((4351 / 193) : ℂ) * ζ ^ 18 - ((3633 / 193) : ℂ) * ζ ^ 19 + ((6037 / 386) : ℂ) * ζ ^ 20 + ((911 / 386) : ℂ) * ζ ^ 21 + ((15169 / 772) : ℂ) * ζ ^ 22 - ((1367 / 193) : ℂ) * ζ ^ 23 - ((26675 / 772) : ℂ) * ζ ^ 24 + ((4089 / 193) : ℂ) * ζ ^ 25 + ((9131 / 386) : ℂ) * ζ ^ 26 + ((2157 / 386) : ℂ) * ζ ^ 27 - ((9573 / 772) : ℂ) * ζ ^ 28 - ((1724 / 193) : ℂ) * ζ ^ 29 + ((3307 / 772) : ℂ) * ζ ^ 30 + ((1411 / 193) : ℂ) * ζ ^ 31 + ((14601 / 772) : ℂ) * ζ ^ 32 + ((7813 / 772) : ℂ) * ζ ^ 33 - ((15383 / 772) : ℂ) * ζ ^ 34 - ((2124 / 193) : ℂ) * ζ ^ 35 + ((10343 / 386) : ℂ) * ζ ^ 36 - ((1092 / 193) : ℂ) * ζ ^ 37 - ((2504 / 193) : ℂ) * ζ ^ 38 + ((1378 / 193) : ℂ) * ζ ^ 39 - ((17787 / 772) : ℂ) * ζ ^ 40 - ((1092 / 193) : ℂ) * ζ ^ 41 - ((3093 / 772) : ℂ) * ζ ^ 42 + ((2287 / 386) : ℂ) * ζ ^ 43 + ((9271 / 772) : ℂ) * ζ ^ 44 - ((11755 / 772) : ℂ) * ζ ^ 45 - ((3093 / 772) : ℂ) * ζ ^ 46 - ((665 / 386) : ℂ) * ζ ^ 47 - ((1755 / 772) : ℂ) * ζ ^ 48 + ((11031 / 772) : ℂ) * ζ ^ 49 - ((951 / 772) : ℂ) * ζ ^ 50 - ((665 / 386) : ℂ) * ζ ^ 51 - ((6085 / 772) : ℂ) * ζ ^ 52 + ((197 / 386) : ℂ) * ζ ^ 53 + ((1011 / 193) : ℂ) * ζ ^ 54 + ((1348 / 193) : ℂ) * ζ ^ 55 - ((6085 / 772) : ℂ) * ζ ^ 56 + ((1273 / 772) : ℂ) * ζ ^ 57 + ((1469 / 386) : ℂ) * ζ ^ 58 - ((2031 / 386) : ℂ) * ζ ^ 59 + ((6085 / 772) : ℂ) * ζ ^ 60 - ((1273 / 772) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_5_4 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        5 4 =
      alternatingSixAmbientRow13TransformedGeneratorA
        5 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (-((6683 / 4246) : ℂ) + ((19511 / 4246) : ℂ) * ζ ^ 3 + ((6683 / 4246) : ℂ) * ζ ^ 4 + ((16857 / 8492) : ℂ) * ζ ^ 5 - ((56495 / 8492) : ℂ) * ζ ^ 6 + ((11651 / 2123) : ℂ) * ζ ^ 8 - ((10709 / 8492) : ℂ) * ζ ^ 9 - ((10493 / 4246) : ℂ) * ζ ^ 10 + ((1844 / 2123) : ℂ) * ζ ^ 11 - ((48855 / 8492) : ℂ) * ζ ^ 13 - ((35509 / 8492) : ℂ) * ζ ^ 14 - ((29 / 8492) : ℂ) * ζ ^ 15 - ((1946 / 2123) : ℂ) * ζ ^ 16 + ((1537 / 2123) : ℂ) * ζ ^ 17 + ((295 / 22) : ℂ) * ζ ^ 18 + ((7405 / 8492) : ℂ) * ζ ^ 19 - ((13279 / 8492) : ℂ) * ζ ^ 20 - ((3169 / 4246) : ℂ) * ζ ^ 21 + ((56495 / 8492) : ℂ) * ζ ^ 22 + ((9632 / 2123) : ℂ) * ζ ^ 23 + ((5495 / 8492) : ℂ) * ζ ^ 24 - ((26517 / 4246) : ℂ) * ζ ^ 25 + ((9797 / 4246) : ℂ) * ζ ^ 26 - ((1844 / 2123) : ℂ) * ζ ^ 27 + ((8623 / 8492) : ℂ) * ζ ^ 28 + ((2452 / 2123) : ℂ) * ζ ^ 29 - ((81531 / 8492) : ℂ) * ζ ^ 30 - ((19827 / 8492) : ℂ) * ζ ^ 31 + ((1946 / 2123) : ℂ) * ζ ^ 32 + ((2396 / 2123) : ℂ) * ζ ^ 33 - ((11865 / 8492) : ℂ) * ζ ^ 34 + ((3585 / 4246) : ℂ) * ζ ^ 35 + ((215 / 386) : ℂ) * ζ ^ 36 + ((847 / 386) : ℂ) * ζ ^ 37 - ((68921 / 8492) : ℂ) * ζ ^ 38 - ((12245 / 8492) : ℂ) * ζ ^ 39 + ((34127 / 4246) : ℂ) * ζ ^ 40 + ((847 / 386) : ℂ) * ζ ^ 41 + ((36901 / 8492) : ℂ) * ζ ^ 42 + ((34295 / 8492) : ℂ) * ζ ^ 43 - ((19773 / 2123) : ℂ) * ζ ^ 44 + ((16993 / 4246) : ℂ) * ζ ^ 45 + ((36901 / 8492) : ℂ) * ζ ^ 46 + ((12451 / 8492) : ℂ) * ζ ^ 47 + ((6609 / 4246) : ℂ) * ζ ^ 48 - ((637 / 193) : ℂ) * ζ ^ 49 - ((50261 / 8492) : ℂ) * ζ ^ 50 + ((12451 / 8492) : ℂ) * ζ ^ 51 + ((1527 / 4246) : ℂ) * ζ ^ 52 - ((30733 / 8492) : ℂ) * ζ ^ 53 + ((3340 / 2123) : ℂ) * ζ ^ 54 - ((945 / 386) : ℂ) * ζ ^ 55 + ((1527 / 4246) : ℂ) * ζ ^ 56 - ((1537 / 2123) : ℂ) * ζ ^ 57 + ((1159 / 8492) : ℂ) * ζ ^ 58 + ((8339 / 8492) : ℂ) * ζ ^ 59 - ((1527 / 4246) : ℂ) * ζ ^ 60 + ((1537 / 2123) : ℂ) * ζ ^ 61)
private theorem row13_transformedGeneratorA_5_5 :
    (alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis)
        5 5 =
      alternatingSixAmbientRow13TransformedGeneratorA
        5 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow13Eigenbasis,
      alternatingSixAmbientRow13EigenbasisInverse,
      alternatingSixFiveAmbient_row13_matrixA,
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row13 (((1253 / 2123) : ℂ) - ((4042 / 2123) : ℂ) * ζ ^ 3 - ((1253 / 2123) : ℂ) * ζ ^ 4 - ((6887 / 4246) : ℂ) * ζ ^ 5 + ((11733 / 4246) : ℂ) * ζ ^ 6 - ((8221 / 4246) : ℂ) * ζ ^ 8 + ((4760 / 2123) : ℂ) * ζ ^ 9 + ((9905 / 4246) : ℂ) * ζ ^ 10 + ((6881 / 4246) : ℂ) * ζ ^ 11 + ((5922 / 2123) : ℂ) * ζ ^ 13 + ((914 / 2123) : ℂ) * ζ ^ 14 + ((400 / 193) : ℂ) * ζ ^ 15 + ((469 / 193) : ℂ) * ζ ^ 16 + ((2633 / 4246) : ℂ) * ζ ^ 17 - ((1367 / 4246) : ℂ) * ζ ^ 18 - ((1919 / 4246) : ℂ) * ζ ^ 19 - ((10795 / 4246) : ℂ) * ζ ^ 20 + ((1714 / 2123) : ℂ) * ζ ^ 21 - ((11733 / 4246) : ℂ) * ζ ^ 22 - ((769 / 4246) : ℂ) * ζ ^ 23 + ((21113 / 4246) : ℂ) * ζ ^ 24 - ((2922 / 2123) : ℂ) * ζ ^ 25 - ((2333 / 2123) : ℂ) * ζ ^ 26 - ((6881 / 4246) : ℂ) * ζ ^ 27 - ((13191 / 4246) : ℂ) * ζ ^ 28 - ((3263 / 2123) : ℂ) * ζ ^ 29 + ((6405 / 2123) : ℂ) * ζ ^ 30 - ((1324 / 2123) : ℂ) * ζ ^ 31 - ((469 / 193) : ℂ) * ζ ^ 32 - ((2866 / 2123) : ℂ) * ζ ^ 33 + ((2995 / 2123) : ℂ) * ζ ^ 34 + ((45 / 22) : ℂ) * ζ ^ 35 - ((5944 / 2123) : ℂ) * ζ ^ 36 + ((919 / 2123) : ℂ) * ζ ^ 37 + ((25329 / 4246) : ℂ) * ζ ^ 38 + ((2429 / 4246) : ℂ) * ζ ^ 39 - ((366 / 193) : ℂ) * ζ ^ 40 + ((919 / 2123) : ℂ) * ζ ^ 41 - ((7067 / 4246) : ℂ) * ζ ^ 42 + ((4975 / 4246) : ℂ) * ζ ^ 43 + ((8400 / 2123) : ℂ) * ζ ^ 44 - ((597 / 193) : ℂ) * ζ ^ 45 - ((7067 / 4246) : ℂ) * ζ ^ 46 - ((4233 / 4246) : ℂ) * ζ ^ 47 + ((6097 / 4246) : ℂ) * ζ ^ 48 + ((10914 / 2123) : ℂ) * ζ ^ 49 + ((283 / 193) : ℂ) * ζ ^ 50 - ((4233 / 4246) : ℂ) * ζ ^ 51 + ((785 / 2123) : ℂ) * ζ ^ 52 - ((9465 / 4246) : ℂ) * ζ ^ 53 + ((841 / 4246) : ℂ) * ζ ^ 54 + ((5218 / 2123) : ℂ) * ζ ^ 55 + ((785 / 2123) : ℂ) * ζ ^ 56 - ((2633 / 4246) : ℂ) * ζ ^ 57 - ((3626 / 2123) : ℂ) * ζ ^ 58 - ((6203 / 4246) : ℂ) * ζ ^ 59 - ((785 / 2123) : ℂ) * ζ ^ 60 + ((2633 / 4246) : ℂ) * ζ ^ 61)
/-- Exact conjugation formula for the row 13 first
generator. -/
theorem alternatingSixAmbientRow13TransformedGeneratorA_eq :
    alternatingSixAmbientRow13EigenbasisInverse *
        alternatingSixFiveAmbient_row13_matrixA *
        alternatingSixAmbientRow13Eigenbasis =
      alternatingSixAmbientRow13TransformedGeneratorA := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row13_transformedGeneratorA_0_0
  · exact row13_transformedGeneratorA_0_1
  · exact row13_transformedGeneratorA_0_2
  · exact row13_transformedGeneratorA_0_3
  · exact row13_transformedGeneratorA_0_4
  · exact row13_transformedGeneratorA_0_5
  · exact row13_transformedGeneratorA_1_0
  · exact row13_transformedGeneratorA_1_1
  · exact row13_transformedGeneratorA_1_2
  · exact row13_transformedGeneratorA_1_3
  · exact row13_transformedGeneratorA_1_4
  · exact row13_transformedGeneratorA_1_5
  · exact row13_transformedGeneratorA_2_0
  · exact row13_transformedGeneratorA_2_1
  · exact row13_transformedGeneratorA_2_2
  · exact row13_transformedGeneratorA_2_3
  · exact row13_transformedGeneratorA_2_4
  · exact row13_transformedGeneratorA_2_5
  · exact row13_transformedGeneratorA_3_0
  · exact row13_transformedGeneratorA_3_1
  · exact row13_transformedGeneratorA_3_2
  · exact row13_transformedGeneratorA_3_3
  · exact row13_transformedGeneratorA_3_4
  · exact row13_transformedGeneratorA_3_5
  · exact row13_transformedGeneratorA_4_0
  · exact row13_transformedGeneratorA_4_1
  · exact row13_transformedGeneratorA_4_2
  · exact row13_transformedGeneratorA_4_3
  · exact row13_transformedGeneratorA_4_4
  · exact row13_transformedGeneratorA_4_5
  · exact row13_transformedGeneratorA_5_0
  · exact row13_transformedGeneratorA_5_1
  · exact row13_transformedGeneratorA_5_2
  · exact row13_transformedGeneratorA_5_3
  · exact row13_transformedGeneratorA_5_4
  · exact row13_transformedGeneratorA_5_5


end InductiveMcKay
end McKayConjecture
