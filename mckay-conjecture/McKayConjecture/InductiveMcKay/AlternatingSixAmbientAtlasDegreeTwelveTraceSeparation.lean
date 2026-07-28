/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixDataDegreeTwelve
import McKayConjecture.InductiveMcKay.AlternatingSixCyclotomicNonzero

/-!
# Separating the paired ATLAS degree-twelve matrix rows

The ATLAS power-1 and power-7 models, and the power-2 and power-11 models,
are separated by their exact traces at `AB`.  The results are stated at the
matrix level so they do not depend on future scalar-commutant packaging.
-/

noncomputable section

open Polynomial

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

macro "close_atlas_degree_twelve_cyclotomic" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

theorem alternatingSixAmbientAtlas12Power1_matrixAB_trace :
    (alternatingSixFiveAmbient_atlas12Power1_matrixA *
          alternatingSixFiveAmbient_atlas12Power1_matrixB).trace =
      alternatingSixCyclotomicValue
        [(-1, 0), (-1, 4), (1, 8), (1, 12),
          (1, 16), (-1, 28)] := by
  change
    (∑ i : Fin 12,
      (alternatingSixFiveAmbient_atlas12Power1_matrixA *
        alternatingSixFiveAmbient_atlas12Power1_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_atlas12Power1_matrixA,
    alternatingSixFiveAmbient_atlas12Power1_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_atlas_degree_twelve_cyclotomic
    ((1 : ℂ) + ζ ^ 4 - 2 * ζ ^ 8 +
      2 * ζ ^ 12 - 2 * ζ ^ 16)

theorem alternatingSixAmbientAtlas12Power7_matrixAB_trace :
    (alternatingSixFiveAmbient_atlas12Power7_matrixA *
          alternatingSixFiveAmbient_atlas12Power7_matrixB).trace =
      alternatingSixCyclotomicValue
        [(1, 0), (1, 4), (-1, 8), (-1, 12),
          (-1, 16), (-1, 20), (1, 28)] := by
  change
    (∑ i : Fin 12,
      (alternatingSixFiveAmbient_atlas12Power7_matrixA *
        alternatingSixFiveAmbient_atlas12Power7_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_atlas12Power7_matrixA,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_atlas_degree_twelve_cyclotomic
    (-(2 : ℂ) + ζ ^ 8 - 2 * ζ ^ 12 + 2 * ζ ^ 16)

theorem alternatingSixAmbientAtlas12Power2_matrixAB_trace :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA *
          alternatingSixFiveAmbient_atlas12Power2_matrixB).trace =
      alternatingSixCyclotomicValue
        [(-1, 0), (-1, 4), (1, 16), (1, 20)] := by
  change
    (∑ i : Fin 12,
      (alternatingSixFiveAmbient_atlas12Power2_matrixA *
        alternatingSixFiveAmbient_atlas12Power2_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_atlas_degree_twelve_cyclotomic
    ((1 : ℂ) - 2 * ζ ^ 8 + ζ ^ 12 - ζ ^ 16)

theorem alternatingSixAmbientAtlas12Power11_matrixAB_trace :
    (alternatingSixFiveAmbient_atlas12Power11_matrixA *
          alternatingSixFiveAmbient_atlas12Power11_matrixB).trace =
      alternatingSixCyclotomicValue
        [(1, 4), (-1, 16)] := by
  change
    (∑ i : Fin 12,
      (alternatingSixFiveAmbient_atlas12Power11_matrixA *
        alternatingSixFiveAmbient_atlas12Power11_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_atlas12Power11_matrixA,
    alternatingSixFiveAmbient_atlas12Power11_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_atlas_degree_twelve_cyclotomic
    (-(2 : ℂ) + ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16)

/-! ### Certified nonzero trace differences -/

def alternatingSixAmbientAtlas12Power1Power7DifferencePolynomial : ℚ[X] :=
  Polynomial.C (-2) - 2 * X ^ 4 + 2 * X ^ 8 +
    2 * X ^ 12 + 2 * X ^ 16 + X ^ 20 - 2 * X ^ 28

theorem
    alternatingSixAmbientAtlas12Power1Power7DifferencePolynomial_ne_zero :
    Polynomial.eval₂ (algebraMap ℚ ℂ) ζ
        alternatingSixAmbientAtlas12Power1Power7DifferencePolynomial ≠ 0 := by
  apply alternatingSixComplexPolynomial_eval₂_ne_zero
  · intro hzero
    have hvalue :=
      congrArg (Polynomial.eval (2 : ℚ)) hzero
    norm_num [
      alternatingSixAmbientAtlas12Power1Power7DifferencePolynomial] at hvalue
  · dsimp [alternatingSixAmbientAtlas12Power1Power7DifferencePolynomial]
    compute_degree
    norm_num

/-- The ATLAS power-1 and power-7 exact `AB` traces differ. -/
theorem
    alternatingSixAmbientAtlas12Power1_matrixAB_trace_ne_power7_matrixAB_trace :
    (alternatingSixFiveAmbient_atlas12Power1_matrixA *
          alternatingSixFiveAmbient_atlas12Power1_matrixB).trace ≠
      (alternatingSixFiveAmbient_atlas12Power7_matrixA *
          alternatingSixFiveAmbient_atlas12Power7_matrixB).trace := by
  rw [alternatingSixAmbientAtlas12Power1_matrixAB_trace,
    alternatingSixAmbientAtlas12Power7_matrixAB_trace]
  intro hequal
  apply
    alternatingSixAmbientAtlas12Power1Power7DifferencePolynomial_ne_zero
  rw [← sub_eq_zero.mpr hequal]
  simp [
    alternatingSixAmbientAtlas12Power1Power7DifferencePolynomial,
    alternatingSixCyclotomicValue]
  ring

def alternatingSixAmbientAtlas12Power2Power11DifferencePolynomial : ℚ[X] :=
  Polynomial.C (-1) - 2 * X ^ 4 + 2 * X ^ 16 + X ^ 20

theorem
    alternatingSixAmbientAtlas12Power2Power11DifferencePolynomial_ne_zero :
    Polynomial.eval₂ (algebraMap ℚ ℂ) ζ
        alternatingSixAmbientAtlas12Power2Power11DifferencePolynomial ≠ 0 := by
  apply alternatingSixComplexPolynomial_eval₂_ne_zero
  · intro hzero
    have hvalue :=
      congrArg (Polynomial.eval (2 : ℚ)) hzero
    norm_num [
      alternatingSixAmbientAtlas12Power2Power11DifferencePolynomial] at hvalue
  · dsimp [alternatingSixAmbientAtlas12Power2Power11DifferencePolynomial]
    compute_degree
    norm_num

/-- The ATLAS power-2 and power-11 exact `AB` traces differ. -/
theorem
    alternatingSixAmbientAtlas12Power2_matrixAB_trace_ne_power11_matrixAB_trace :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA *
          alternatingSixFiveAmbient_atlas12Power2_matrixB).trace ≠
      (alternatingSixFiveAmbient_atlas12Power11_matrixA *
          alternatingSixFiveAmbient_atlas12Power11_matrixB).trace := by
  rw [alternatingSixAmbientAtlas12Power2_matrixAB_trace,
    alternatingSixAmbientAtlas12Power11_matrixAB_trace]
  intro hequal
  apply
    alternatingSixAmbientAtlas12Power2Power11DifferencePolynomial_ne_zero
  rw [← sub_eq_zero.mpr hequal]
  simp [
    alternatingSixAmbientAtlas12Power2Power11DifferencePolynomial,
    alternatingSixCyclotomicValue]
  ring

end InductiveMcKay
end McKayConjecture
