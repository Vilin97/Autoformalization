/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow21LongWordTraces
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow21ShortWordTraces

/-!
# Traces of the seven row-21 class-representative base words

The two normal forms containing `b⁻¹` are converted to positive words using
`b⁴ = 1`.  The resulting short- and long-word calculations give an exact
trace theorem for every base-word label used by the checked classes.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot
local notation "A" => alternatingSixFiveAmbient_row21_matrixA
local notation "B" => alternatingSixFiveAmbient_row21_matrixB

private abbrev row21Certificate :=
  alternatingSixAmbientRow21ClassMatrixCertificate

/-- The row-21 order-six relation for the twentieth power of the analytic root. -/
theorem alternatingSixAmbientRow21_orderSixRelation :
    ζ ^ 40 - ζ ^ 20 + 1 = 0 := by
  have h :=
    congrArg alternatingSixCyclotomicEmbedding
      alternatingSixCyclotomicRoot_orderSixRelation
  simpa only [map_sub, map_add, map_pow, map_one, map_zero,
    alternatingSixCyclotomicEmbedding_root] using h

/-- The row-21 central scalar `ζ⁸⁰` is `-ζ²⁰`. -/
theorem alternatingSixAmbientRow21_root_pow_eighty :
    ζ ^ 80 = -(ζ ^ 20) := by
  rw [show 80 = 20 * 4 by norm_num, pow_mul]
  linear_combination
    ((ζ ^ 20) ^ 2 + ζ ^ 20) *
      alternatingSixAmbientRow21_orderSixRelation

/-- The second named row-21 relator acts trivially. -/
theorem alternatingSixAmbientRow21_relatorGL_one :
    row21Certificate.relatorGL 1 = 1 := by
  apply Units.ext
  simp [row21Certificate,
    alternatingSixAmbientRow21ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate,
    AlternatingSixAmbientScalarPattern.exponent]

/-- In row 21, `b⁻¹ = b³`, as an equality of concrete matrices. -/
theorem alternatingSixAmbientRow21_matrixBGL_inv_val :
    (row21Certificate.matrixBGL⁻¹ :
        Matrix (Fin 9) (Fin 9) ℂ) =
      B ^ 3 := by
  have hfourth : row21Certificate.matrixBGL ^ 4 = 1 := by
    rw [row21Certificate.matrixBGL_fourth,
      alternatingSixAmbientRow21_relatorGL_one]
  have hinverse :
      row21Certificate.matrixBGL⁻¹ =
        row21Certificate.matrixBGL ^ 3 := by
    apply mul_left_cancel (a := row21Certificate.matrixBGL)
    rw [mul_inv_cancel, ← pow_succ', hfourth]
  simpa [row21Certificate,
    alternatingSixAmbientRow21ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate] using
      congrArg Units.val hinverse

/-- The state-77 normal word is the positive word `ababbabbb`. -/
theorem alternatingSixAmbientRow21_state77_word_matrix :
    (row21Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 9) (Fin 9) ℂ) =
      A * B * A * B * B * A * B * B * B := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row21Certificate.matrixB⁻¹ = B ^ 3 := by
    simpa [row21Certificate,
      alternatingSixAmbientRow21ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow21_matrixBGL_inv_val
  rw [hBinv]
  simp only [row21Certificate,
    alternatingSixAmbientRow21ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- The state-79 normal word is the positive word `ababbbabb`. -/
theorem alternatingSixAmbientRow21_state79_word_matrix :
    (row21Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 9) (Fin 9) ℂ) =
      A * B * A * B * B * B * A * B * B := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row21Certificate.matrixB⁻¹ = B ^ 3 := by
    simpa [row21Certificate,
      alternatingSixAmbientRow21ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow21_matrixBGL_inv_val
  rw [hBinv]
  simp only [row21Certificate,
    alternatingSixAmbientRow21ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- Trace of the state-77 normal word. -/
theorem alternatingSixAmbientRow21_state77_word_trace :
    (row21Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 9) (Fin 9) ℂ).trace = 0 := by
  rw [alternatingSixAmbientRow21_state77_word_matrix,
    alternatingSixAmbientRow21_positiveState77_trace]

/-- Trace of the state-79 normal word. -/
theorem alternatingSixAmbientRow21_state79_word_trace :
    (row21Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 9) (Fin 9) ℂ).trace = 0 := by
  rw [alternatingSixAmbientRow21_state79_word_matrix,
    alternatingSixAmbientRow21_positiveState79_trace]

/-- The primitive sixth root appearing in row-21 class values. -/
def alternatingSixAmbientRow21Eta : ℂ :=
  ζ ^ 20

/-- The seven row-21 values before multiplication by a central scalar. -/
def alternatingSixAmbientRow21BaseWordValue :
    AlternatingSixAmbientClassBaseWord → ℂ
  | .identity => 9
  | .generatorA => -1 + alternatingSixAmbientRow21Eta
  | .generatorB => 1
  | .generatorAB => alternatingSixAmbientRow21Eta
  | .generatorABSquared => 1 - alternatingSixAmbientRow21Eta
  | .state77 => 0
  | .state79 => 0

/-- Exact trace of every one of the seven row-21 base words. -/
theorem alternatingSixAmbientRow21_baseWord_trace
    (word : AlternatingSixAmbientClassBaseWord) :
    (row21Certificate.rewriteWordGL word.word :
        Matrix (Fin 9) (Fin 9) ℂ).trace =
      alternatingSixAmbientRow21BaseWordValue word := by
  cases word
  · simp [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      alternatingSixAmbientRow21BaseWordValue, Matrix.trace]
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow21BaseWordValue,
      alternatingSixAmbientRow21Eta,
      alternatingSixCyclotomicValue,
      row21Certificate,
      alternatingSixAmbientRow21ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow21_matrixA_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow21BaseWordValue,
      row21Certificate,
      alternatingSixAmbientRow21ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow21_matrixB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow21BaseWordValue,
      alternatingSixAmbientRow21Eta,
      alternatingSixCyclotomicValue,
      row21Certificate,
      alternatingSixAmbientRow21ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow21_matrixAB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow21BaseWordValue,
      alternatingSixAmbientRow21Eta,
      alternatingSixCyclotomicValue, pow_two,
      Matrix.mul_assoc, sub_eq_add_neg,
      row21Certificate,
      alternatingSixAmbientRow21ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow21_matrixABSquared_trace
  · exact alternatingSixAmbientRow21_state77_word_trace
  · exact alternatingSixAmbientRow21_state79_word_trace

end InductiveMcKay
end McKayConjecture
