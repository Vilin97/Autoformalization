/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.ComputeDegree
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRelationTableDegreeFiveTenFifteen
import McKayConjecture.InductiveMcKay.AlternatingSixCyclotomicNonzero

/-!
# Separating the paired degree-ten ambient matrix rows

The exact traces of the canonical second generator distinguish the row-24
and row-25 matrix models.  This module records the distinction independently
of the still-missing scalar-commutant packaging for those rows.
-/

noncomputable section

open Polynomial

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

theorem alternatingSixAmbientRow24_matrixB_trace :
    alternatingSixFiveAmbient_row24_matrixB.trace =
      alternatingSixCyclotomicValue
        [(-1, 5), (-1, 15), (1, 25)] := by
  change
    (∑ i : Fin 10,
      alternatingSixFiveAmbient_row24_matrixB i i) = _
  simp [alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring_nf

theorem alternatingSixAmbientRow25_matrixB_trace :
    alternatingSixFiveAmbient_row25_matrixB.trace =
      alternatingSixCyclotomicValue
        [(1, 5), (1, 15), (-1, 25)] := by
  change
    (∑ i : Fin 10,
      alternatingSixFiveAmbient_row25_matrixB i i) = _
  simp [alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring_nf

def alternatingSixAmbientRow24Row25DifferencePolynomial : ℚ[X] :=
  -2 * X ^ 5 - 2 * X ^ 15 + 2 * X ^ 25

theorem alternatingSixAmbientRow24Row25DifferencePolynomial_ne_zero :
    Polynomial.eval₂ (algebraMap ℚ ℂ) ζ
        alternatingSixAmbientRow24Row25DifferencePolynomial ≠ 0 := by
  apply alternatingSixComplexPolynomial_eval₂_ne_zero
  · intro hzero
    have hvalue :=
      congrArg (Polynomial.eval (2 : ℚ)) hzero
    norm_num [
      alternatingSixAmbientRow24Row25DifferencePolynomial] at hvalue
  · dsimp [alternatingSixAmbientRow24Row25DifferencePolynomial]
    compute_degree
    norm_num

/-- The exact generator-`B` traces of rows 24 and 25 differ. -/
theorem alternatingSixAmbientRow24_matrixB_trace_ne_row25_matrixB_trace :
    alternatingSixFiveAmbient_row24_matrixB.trace ≠
      alternatingSixFiveAmbient_row25_matrixB.trace := by
  rw [alternatingSixAmbientRow24_matrixB_trace,
    alternatingSixAmbientRow25_matrixB_trace]
  intro hequal
  apply alternatingSixAmbientRow24Row25DifferencePolynomial_ne_zero
  rw [← sub_eq_zero.mpr hequal]
  simp [
    alternatingSixAmbientRow24Row25DifferencePolynomial,
    alternatingSixCyclotomicValue]
  ring

end InductiveMcKay
end McKayConjecture
