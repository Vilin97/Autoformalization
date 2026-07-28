/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow30LongWordTraces
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow30ShortWordTraces

/-!
# Traces of the seven row-30 class-representative base words

The two normal forms containing `b⁻¹` are converted to positive words using
`b⁴ = 1`.  The resulting short- and long-word calculations give an exact
trace theorem for every base-word label used by the checked classes.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot
local notation "A" => alternatingSixFiveAmbient_row30_matrixA
local notation "B" => alternatingSixFiveAmbient_row30_matrixB

private abbrev row30Certificate :=
  alternatingSixAmbientRow30ClassMatrixCertificate

/-- The row-30 order-six relation for the twentieth power of the analytic root. -/
theorem alternatingSixAmbientRow30_orderSixRelation :
    ζ ^ 40 - ζ ^ 20 + 1 = 0 := by
  have h :=
    congrArg alternatingSixCyclotomicEmbedding
      alternatingSixCyclotomicRoot_orderSixRelation
  simpa only [map_sub, map_add, map_pow, map_one, map_zero,
    alternatingSixCyclotomicEmbedding_root] using h

/-- The row-30 central scalar `ζ⁸⁰` is `-ζ²⁰`. -/
theorem alternatingSixAmbientRow30_root_pow_eighty :
    ζ ^ 80 = -(ζ ^ 20) := by
  rw [show 80 = 20 * 4 by norm_num, pow_mul]
  linear_combination
    ((ζ ^ 20) ^ 2 + ζ ^ 20) *
      alternatingSixAmbientRow30_orderSixRelation

/-- The second named row-30 relator acts trivially. -/
theorem alternatingSixAmbientRow30_relatorGL_one :
    row30Certificate.relatorGL 1 = 1 := by
  apply Units.ext
  simp [row30Certificate,
    alternatingSixAmbientRow30ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate,
    AlternatingSixAmbientScalarPattern.exponent]

/-- In row 30, `b⁻¹ = b³`, as an equality of concrete matrices. -/
theorem alternatingSixAmbientRow30_matrixBGL_inv_val :
    (row30Certificate.matrixBGL⁻¹ :
        Matrix (Fin 15) (Fin 15) ℂ) =
      B ^ 3 := by
  have hfourth : row30Certificate.matrixBGL ^ 4 = 1 := by
    rw [row30Certificate.matrixBGL_fourth,
      alternatingSixAmbientRow30_relatorGL_one]
  have hinverse :
      row30Certificate.matrixBGL⁻¹ =
        row30Certificate.matrixBGL ^ 3 := by
    apply mul_left_cancel (a := row30Certificate.matrixBGL)
    rw [mul_inv_cancel, ← pow_succ', hfourth]
  simpa [row30Certificate,
    alternatingSixAmbientRow30ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate] using
      congrArg Units.val hinverse

/-- The state-77 normal word is the positive word `ababbabbb`. -/
theorem alternatingSixAmbientRow30_state77_word_matrix :
    (row30Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 15) (Fin 15) ℂ) =
      A * B * A * B * B * A * B * B * B := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row30Certificate.matrixB⁻¹ = B ^ 3 := by
    simpa [row30Certificate,
      alternatingSixAmbientRow30ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow30_matrixBGL_inv_val
  rw [hBinv]
  simp only [row30Certificate,
    alternatingSixAmbientRow30ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- The state-79 normal word is the positive word `ababbbabb`. -/
theorem alternatingSixAmbientRow30_state79_word_matrix :
    (row30Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 15) (Fin 15) ℂ) =
      A * B * A * B * B * B * A * B * B := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row30Certificate.matrixB⁻¹ = B ^ 3 := by
    simpa [row30Certificate,
      alternatingSixAmbientRow30ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow30_matrixBGL_inv_val
  rw [hBinv]
  simp only [row30Certificate,
    alternatingSixAmbientRow30ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- Trace of the state-77 normal word. -/
theorem alternatingSixAmbientRow30_state77_word_trace :
    (row30Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 15) (Fin 15) ℂ).trace = 0 := by
  rw [alternatingSixAmbientRow30_state77_word_matrix,
    alternatingSixAmbientRow30_positiveState77_trace]

/-- Trace of the state-79 normal word. -/
theorem alternatingSixAmbientRow30_state79_word_trace :
    (row30Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 15) (Fin 15) ℂ).trace = 0 := by
  rw [alternatingSixAmbientRow30_state79_word_matrix,
    alternatingSixAmbientRow30_positiveState79_trace]

/-- The primitive sixth root appearing in row-30 class values. -/
def alternatingSixAmbientRow30Eta : ℂ :=
  ζ ^ 20

/-- The seven row-30 values before multiplication by a central scalar. -/
def alternatingSixAmbientRow30BaseWordValue :
    AlternatingSixAmbientClassBaseWord → ℂ
  | .identity => 15
  | .generatorA => 1 - alternatingSixAmbientRow30Eta
  | .generatorB => -1
  | .generatorAB => 0
  | .generatorABSquared => 0
  | .state77 => 0
  | .state79 => 0

/-- Exact trace of every one of the seven row-30 base words. -/
theorem alternatingSixAmbientRow30_baseWord_trace
    (word : AlternatingSixAmbientClassBaseWord) :
    (row30Certificate.rewriteWordGL word.word :
        Matrix (Fin 15) (Fin 15) ℂ).trace =
      alternatingSixAmbientRow30BaseWordValue word := by
  cases word
  · simp [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      alternatingSixAmbientRow30BaseWordValue, Matrix.trace]
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow30BaseWordValue,
      alternatingSixAmbientRow30Eta,
      alternatingSixCyclotomicValue, sub_eq_add_neg,
      row30Certificate,
      alternatingSixAmbientRow30ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow30_matrixA_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow30BaseWordValue,
      row30Certificate,
      alternatingSixAmbientRow30ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow30_matrixB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow30BaseWordValue,
      row30Certificate,
      alternatingSixAmbientRow30ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow30_matrixAB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow30BaseWordValue,
      pow_two, Matrix.mul_assoc,
      row30Certificate,
      alternatingSixAmbientRow30ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow30_matrixABSquared_trace
  · exact alternatingSixAmbientRow30_state77_word_trace
  · exact alternatingSixAmbientRow30_state79_word_trace

end InductiveMcKay
end McKayConjecture
