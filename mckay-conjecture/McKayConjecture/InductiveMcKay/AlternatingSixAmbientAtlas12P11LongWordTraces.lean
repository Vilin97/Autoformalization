/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P11LongWordProducts

/-!
# Exact traces of the two long positive ATLAS degree-12 power-eleven words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem alternatingSixAmbientAtlas12P11_longState77Reduced_trace :
    (alternatingSixAmbientAtlas12P11LongPrefix77 *
      alternatingSixAmbientAtlas12P11LongMatrixABBB).trace =
      0 := by
  change
    (∑ i : Fin 12,
      (alternatingSixAmbientAtlas12P11LongPrefix77 *
        alternatingSixAmbientAtlas12P11LongMatrixABBB) i i) =
      0
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixAmbientAtlas12P11LongMatrixABBB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(18 : ℂ)
          + (18 : ℂ) * ζ ^ 4
          - (4 : ℂ) * ζ ^ 8
          + (14 : ℂ) * ζ ^ 12
          - (12 : ℂ) * ζ ^ 16
          + (6 : ℂ) * ζ ^ 20
          - (6 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((
        -(18 : ℂ)
          + (18 : ℂ) * ζ ^ 4
          - (4 : ℂ) * ζ ^ 8
          + (14 : ℂ) * ζ ^ 12
          - (12 : ℂ) * ζ ^ 16
          + (6 : ℂ) * ζ ^ 20
          - (6 : ℂ) * ζ ^ 24
      ))) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem alternatingSixAmbientAtlas12P11_longState79Reduced_trace :
    (alternatingSixAmbientAtlas12P11LongPrefix79 *
      alternatingSixAmbientAtlas12P11LongMatrixABB).trace =
      0 := by
  change
    (∑ i : Fin 12,
      (alternatingSixAmbientAtlas12P11LongPrefix79 *
        alternatingSixAmbientAtlas12P11LongMatrixABB) i i) =
      0
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongPrefix79,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(21 : ℂ)
          + (7 : ℂ) * ζ ^ 4
          + (9 : ℂ) * ζ ^ 8
          + (12 : ℂ) * ζ ^ 12
          - (11 : ℂ) * ζ ^ 16
          + (12 : ℂ) * ζ ^ 20
          - (12 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((
        -(21 : ℂ)
          + (7 : ℂ) * ζ ^ 4
          + (9 : ℂ) * ζ ^ 8
          + (12 : ℂ) * ζ ^ 12
          - (11 : ℂ) * ζ ^ 16
          + (12 : ℂ) * ζ ^ 20
          - (12 : ℂ) * ζ ^ 24
      ))) *
        alternatingSixComplexCyclotomicRoot_relation

/-- Trace of the positive word `ababbabbb`. -/
theorem alternatingSixAmbientAtlas12P11_positiveState77_trace :
    (alternatingSixFiveAmbient_atlas12Power11_matrixA *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixA *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixA *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixB).trace =
      0 := by
  rw [show
    alternatingSixFiveAmbient_atlas12Power11_matrixA *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixA *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixA *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixB =
        (alternatingSixFiveAmbient_atlas12Power11_matrixA *
          alternatingSixFiveAmbient_atlas12Power11_matrixB) *
        ((alternatingSixFiveAmbient_atlas12Power11_matrixA *
            alternatingSixFiveAmbient_atlas12Power11_matrixB) *
          alternatingSixFiveAmbient_atlas12Power11_matrixB) *
        (((alternatingSixFiveAmbient_atlas12Power11_matrixA *
              alternatingSixFiveAmbient_atlas12Power11_matrixB) *
            alternatingSixFiveAmbient_atlas12Power11_matrixB) *
          alternatingSixFiveAmbient_atlas12Power11_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientAtlas12P11_longMatrixABBB_eq,
    alternatingSixAmbientAtlas12P11_longMatrixABB_eq,
    alternatingSixAmbientAtlas12P11_longMatrixAB_eq,
    alternatingSixAmbientAtlas12P11_longPrefix77_mul]
  exact alternatingSixAmbientAtlas12P11_longState77Reduced_trace

/-- Trace of the positive word `ababbbabb`. -/
theorem alternatingSixAmbientAtlas12P11_positiveState79_trace :
    (alternatingSixFiveAmbient_atlas12Power11_matrixA *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixA *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixA *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixB).trace =
      0 := by
  rw [show
    alternatingSixFiveAmbient_atlas12Power11_matrixA *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixA *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixA *
      alternatingSixFiveAmbient_atlas12Power11_matrixB *
      alternatingSixFiveAmbient_atlas12Power11_matrixB =
        (alternatingSixFiveAmbient_atlas12Power11_matrixA *
          alternatingSixFiveAmbient_atlas12Power11_matrixB) *
        (((alternatingSixFiveAmbient_atlas12Power11_matrixA *
              alternatingSixFiveAmbient_atlas12Power11_matrixB) *
            alternatingSixFiveAmbient_atlas12Power11_matrixB) *
          alternatingSixFiveAmbient_atlas12Power11_matrixB) *
        ((alternatingSixFiveAmbient_atlas12Power11_matrixA *
            alternatingSixFiveAmbient_atlas12Power11_matrixB) *
          alternatingSixFiveAmbient_atlas12Power11_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientAtlas12P11_longMatrixABBB_eq,
    alternatingSixAmbientAtlas12P11_longMatrixABB_eq,
    alternatingSixAmbientAtlas12P11_longMatrixAB_eq,
    alternatingSixAmbientAtlas12P11_longPrefix79_mul]
  exact alternatingSixAmbientAtlas12P11_longState79Reduced_trace

end InductiveMcKay
end McKayConjecture
