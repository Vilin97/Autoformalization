/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow22LongWordTraces
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow22ShortWordTraces

/-!
# Traces of the seven row-22 class-representative base words

The two normal forms containing `b⁻¹` are converted to positive words using
`b⁴ = 1`.  The resulting short- and long-word calculations give an exact
trace theorem for every base-word label used by the checked classes.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot
local notation "A" => alternatingSixFiveAmbient_row22_matrixA
local notation "B" => alternatingSixFiveAmbient_row22_matrixB

private abbrev row22Certificate :=
  alternatingSixAmbientRow22ClassMatrixCertificate

/-- The row-22 order-six relation for the twentieth power of the analytic root. -/
theorem alternatingSixAmbientRow22_orderSixRelation :
    ζ ^ 40 - ζ ^ 20 + 1 = 0 := by
  have h :=
    congrArg alternatingSixCyclotomicEmbedding
      alternatingSixCyclotomicRoot_orderSixRelation
  simpa only [map_sub, map_add, map_pow, map_one, map_zero,
    alternatingSixCyclotomicEmbedding_root] using h

/-- The row-22 central scalar `ζ⁴⁰` is `ζ²⁰ - 1`. -/
theorem alternatingSixAmbientRow22_root_pow_forty :
    ζ ^ 40 = ζ ^ 20 - 1 := by
  linear_combination alternatingSixAmbientRow22_orderSixRelation

/-- The second named row-22 relator acts trivially. -/
theorem alternatingSixAmbientRow22_relatorGL_one :
    row22Certificate.relatorGL 1 = 1 := by
  apply Units.ext
  simp [row22Certificate,
    alternatingSixAmbientRow22ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate,
    AlternatingSixAmbientScalarPattern.exponent]

/-- In row 22, `b⁻¹ = b³`, as an equality of concrete matrices. -/
theorem alternatingSixAmbientRow22_matrixBGL_inv_val :
    (row22Certificate.matrixBGL⁻¹ :
        Matrix (Fin 9) (Fin 9) ℂ) =
      B ^ 3 := by
  have hfourth : row22Certificate.matrixBGL ^ 4 = 1 := by
    rw [row22Certificate.matrixBGL_fourth,
      alternatingSixAmbientRow22_relatorGL_one]
  have hinverse :
      row22Certificate.matrixBGL⁻¹ =
        row22Certificate.matrixBGL ^ 3 := by
    apply mul_left_cancel (a := row22Certificate.matrixBGL)
    rw [mul_inv_cancel, ← pow_succ', hfourth]
  simpa [row22Certificate,
    alternatingSixAmbientRow22ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate] using
      congrArg Units.val hinverse

/-- The state-77 normal word is the positive word `ababbabbb`. -/
theorem alternatingSixAmbientRow22_state77_word_matrix :
    (row22Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 9) (Fin 9) ℂ) =
      A * B * A * B * B * A * B * B * B := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row22Certificate.matrixB⁻¹ = B ^ 3 := by
    simpa [row22Certificate,
      alternatingSixAmbientRow22ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow22_matrixBGL_inv_val
  rw [hBinv]
  simp only [row22Certificate,
    alternatingSixAmbientRow22ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- The state-79 normal word is the positive word `ababbbabb`. -/
theorem alternatingSixAmbientRow22_state79_word_matrix :
    (row22Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 9) (Fin 9) ℂ) =
      A * B * A * B * B * B * A * B * B := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row22Certificate.matrixB⁻¹ = B ^ 3 := by
    simpa [row22Certificate,
      alternatingSixAmbientRow22ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow22_matrixBGL_inv_val
  rw [hBinv]
  simp only [row22Certificate,
    alternatingSixAmbientRow22ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- Trace of the state-77 normal word. -/
theorem alternatingSixAmbientRow22_state77_word_trace :
    (row22Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 9) (Fin 9) ℂ).trace = 0 := by
  rw [alternatingSixAmbientRow22_state77_word_matrix,
    alternatingSixAmbientRow22_positiveState77_trace]

/-- Trace of the state-79 normal word. -/
theorem alternatingSixAmbientRow22_state79_word_trace :
    (row22Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 9) (Fin 9) ℂ).trace = 0 := by
  rw [alternatingSixAmbientRow22_state79_word_matrix,
    alternatingSixAmbientRow22_positiveState79_trace]

/-- The primitive sixth root appearing in row-22 class values. -/
def alternatingSixAmbientRow22Eta : ℂ :=
  ζ ^ 20

/-- The seven row-22 values before multiplication by a central scalar. -/
def alternatingSixAmbientRow22BaseWordValue :
    AlternatingSixAmbientClassBaseWord → ℂ
  | .identity => 9
  | .generatorA => -alternatingSixAmbientRow22Eta
  | .generatorB => 1
  | .generatorAB => 1 - alternatingSixAmbientRow22Eta
  | .generatorABSquared => alternatingSixAmbientRow22Eta
  | .state77 => 0
  | .state79 => 0

/-- Exact trace of every one of the seven row-22 base words. -/
theorem alternatingSixAmbientRow22_baseWord_trace
    (word : AlternatingSixAmbientClassBaseWord) :
    (row22Certificate.rewriteWordGL word.word :
        Matrix (Fin 9) (Fin 9) ℂ).trace =
      alternatingSixAmbientRow22BaseWordValue word := by
  cases word
  · simp [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      alternatingSixAmbientRow22BaseWordValue, Matrix.trace]
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow22BaseWordValue,
      alternatingSixAmbientRow22Eta,
      alternatingSixCyclotomicValue,
      row22Certificate,
      alternatingSixAmbientRow22ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow22_matrixA_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow22BaseWordValue,
      row22Certificate,
      alternatingSixAmbientRow22ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow22_matrixB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow22BaseWordValue,
      alternatingSixAmbientRow22Eta,
      alternatingSixCyclotomicValue,
      sub_eq_add_neg,
      row22Certificate,
      alternatingSixAmbientRow22ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow22_matrixAB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow22BaseWordValue,
      alternatingSixAmbientRow22Eta,
      alternatingSixCyclotomicValue, pow_two,
      Matrix.mul_assoc, sub_eq_add_neg,
      row22Certificate,
      alternatingSixAmbientRow22ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow22_matrixABSquared_trace
  · exact alternatingSixAmbientRow22_state77_word_trace
  · exact alternatingSixAmbientRow22_state79_word_trace

end InductiveMcKay
end McKayConjecture
