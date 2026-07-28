/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow31LongWordTraces
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow31ShortWordTraces

/-!
# Traces of the seven row-31 class-representative base words

The two normal forms containing `b⁻¹` are converted to positive words using
`b⁴ = 1`. The resulting short- and long-word calculations give an exact
trace theorem for every base-word label used by the checked classes.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot
local notation "A" => alternatingSixFiveAmbient_row31_matrixA
local notation "B" => alternatingSixFiveAmbient_row31_matrixB

private abbrev row31Certificate :=
  alternatingSixAmbientRow31ClassMatrixCertificate

/-- The row-31 order-six relation for the twentieth power of the root. -/
theorem alternatingSixAmbientRow31_orderSixRelation :
    ζ ^ 40 - ζ ^ 20 + 1 = 0 := by
  have h :=
    congrArg alternatingSixCyclotomicEmbedding
      alternatingSixCyclotomicRoot_orderSixRelation
  simpa only [map_sub, map_add, map_pow, map_one, map_zero,
    alternatingSixCyclotomicEmbedding_root] using h

/-- The row-31 central scalar `ζ⁴⁰` is `ζ²⁰ - 1`. -/
theorem alternatingSixAmbientRow31_root_pow_forty :
    ζ ^ 40 = ζ ^ 20 - 1 := by
  linear_combination alternatingSixAmbientRow31_orderSixRelation

/-- The second named row-31 relator acts trivially. -/
theorem alternatingSixAmbientRow31_relatorGL_one :
    row31Certificate.relatorGL 1 = 1 := by
  apply Units.ext
  simp [row31Certificate,
    alternatingSixAmbientRow31ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate,
    AlternatingSixAmbientScalarPattern.exponent]

/-- In row 31, `b⁻¹ = b³`, as an equality of concrete matrices. -/
theorem alternatingSixAmbientRow31_matrixBGL_inv_val :
    (row31Certificate.matrixBGL⁻¹ :
        Matrix (Fin 15) (Fin 15) ℂ) =
      B ^ 3 := by
  have hfourth : row31Certificate.matrixBGL ^ 4 = 1 := by
    rw [row31Certificate.matrixBGL_fourth,
      alternatingSixAmbientRow31_relatorGL_one]
  have hinverse :
      row31Certificate.matrixBGL⁻¹ =
        row31Certificate.matrixBGL ^ 3 := by
    apply mul_left_cancel (a := row31Certificate.matrixBGL)
    rw [mul_inv_cancel, ← pow_succ', hfourth]
  simpa [row31Certificate,
    alternatingSixAmbientRow31ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate] using
      congrArg Units.val hinverse

/-- The state-77 normal word is the positive word `ababbabbb`. -/
theorem alternatingSixAmbientRow31_state77_word_matrix :
    (row31Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 15) (Fin 15) ℂ) =
      A * B * A * B * B * A * B * B * B := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row31Certificate.matrixB⁻¹ = B ^ 3 := by
    simpa [row31Certificate,
      alternatingSixAmbientRow31ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow31_matrixBGL_inv_val
  rw [hBinv]
  simp only [row31Certificate,
    alternatingSixAmbientRow31ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- The state-79 normal word is the positive word `ababbbabb`. -/
theorem alternatingSixAmbientRow31_state79_word_matrix :
    (row31Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 15) (Fin 15) ℂ) =
      A * B * A * B * B * B * A * B * B := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row31Certificate.matrixB⁻¹ = B ^ 3 := by
    simpa [row31Certificate,
      alternatingSixAmbientRow31ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow31_matrixBGL_inv_val
  rw [hBinv]
  simp only [row31Certificate,
    alternatingSixAmbientRow31ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- Trace of the state-77 normal word. -/
theorem alternatingSixAmbientRow31_state77_word_trace :
    (row31Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 15) (Fin 15) ℂ).trace = 0 := by
  rw [alternatingSixAmbientRow31_state77_word_matrix,
    alternatingSixAmbientRow31_positiveState77_trace]

/-- Trace of the state-79 normal word. -/
theorem alternatingSixAmbientRow31_state79_word_trace :
    (row31Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 15) (Fin 15) ℂ).trace = 0 := by
  rw [alternatingSixAmbientRow31_state79_word_matrix,
    alternatingSixAmbientRow31_positiveState79_trace]

/-- The primitive sixth root appearing in row-31 class values. -/
def alternatingSixAmbientRow31Eta : ℂ :=
  ζ ^ 20

/-- The seven row-31 values before multiplication by a central scalar. -/
def alternatingSixAmbientRow31BaseWordValue :
    AlternatingSixAmbientClassBaseWord → ℂ
  | .identity => 15
  | .generatorA => alternatingSixAmbientRow31Eta
  | .generatorB => -1
  | .generatorAB => 0
  | .generatorABSquared => 0
  | .state77 => 0
  | .state79 => 0

/-- Exact trace of every one of the seven row-31 base words. -/
theorem alternatingSixAmbientRow31_baseWord_trace
    (word : AlternatingSixAmbientClassBaseWord) :
    (row31Certificate.rewriteWordGL word.word :
        Matrix (Fin 15) (Fin 15) ℂ).trace =
      alternatingSixAmbientRow31BaseWordValue word := by
  cases word
  · simp [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      alternatingSixAmbientRow31BaseWordValue, Matrix.trace]
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow31BaseWordValue,
      alternatingSixAmbientRow31Eta,
      alternatingSixCyclotomicValue,
      row31Certificate,
      alternatingSixAmbientRow31ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow31_matrixA_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow31BaseWordValue,
      row31Certificate,
      alternatingSixAmbientRow31ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow31_matrixB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow31BaseWordValue,
      row31Certificate,
      alternatingSixAmbientRow31ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow31_matrixAB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow31BaseWordValue,
      pow_two, Matrix.mul_assoc,
      row31Certificate,
      alternatingSixAmbientRow31ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow31_matrixABSquared_trace
  · exact alternatingSixAmbientRow31_state77_word_trace
  · exact alternatingSixAmbientRow31_state79_word_trace

end InductiveMcKay
end McKayConjecture
