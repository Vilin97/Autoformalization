/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow25LongWordTraces
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow25ShortWordTraces

/-!
# Traces of the seven row-25 class-representative base words

The two normal forms containing `b⁻¹` are converted to positive words using
the central relation `b⁴ = -1`. Together with the short-word and long-word
calculations, this gives one trace theorem for each of the seven noncentral
base-word labels used by the thirty-one checked class representatives.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot
local notation "A" => alternatingSixFiveAmbient_row25_matrixA
local notation "B" => alternatingSixFiveAmbient_row25_matrixB

private abbrev row25Certificate :=
  alternatingSixAmbientRow25ClassMatrixCertificate

private theorem row25_root_pow_sixty :
    ζ ^ 60 = -1 := by
  rw [alternatingSixComplexCyclotomicRoot, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 1
  all_goals ring_nf

/-- Every named central relator in row 25 acts as negative identity. -/
theorem alternatingSixAmbientRow25_relatorGL_eq_negOne
    (i : Fin 4) :
    row25Certificate.relatorGL i = -1 := by
  fin_cases i <;>
    apply Units.ext <;>
    simp [row25Certificate,
      alternatingSixAmbientRow25ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate,
      AlternatingSixAmbientScalarPattern.exponent,
      row25_root_pow_sixty]

/-- In row 25, `b⁻¹ = -b³`, as an equality of concrete matrices. -/
theorem alternatingSixAmbientRow25_matrixBGL_inv_val :
    (row25Certificate.matrixBGL⁻¹ :
        Matrix (Fin 10) (Fin 10) ℂ) =
      -(B ^ 3) := by
  have hfourth : row25Certificate.matrixBGL ^ 4 = -1 := by
    rw [row25Certificate.matrixBGL_fourth,
      alternatingSixAmbientRow25_relatorGL_eq_negOne]
  have hinverse :
      row25Certificate.matrixBGL⁻¹ =
        -(row25Certificate.matrixBGL ^ 3) := by
    apply mul_left_cancel (a := row25Certificate.matrixBGL)
    rw [mul_inv_cancel, mul_neg, ← pow_succ', hfourth]
    simp
  simpa [row25Certificate,
    alternatingSixAmbientRow25ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate] using
      congrArg Units.val hinverse

/-- The signed state-77 word is the negative of `ababbabbb`. -/
theorem alternatingSixAmbientRow25_state77_word_matrix :
    (row25Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 10) (Fin 10) ℂ) =
      -(A * B * A * B * B * A * B * B * B) := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row25Certificate.matrixB⁻¹ = -(B ^ 3) := by
    simpa [row25Certificate,
      alternatingSixAmbientRow25ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow25_matrixBGL_inv_val
  rw [hBinv]
  simp only [row25Certificate,
    alternatingSixAmbientRow25ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero, mul_neg]
  noncomm_ring

/-- The signed state-79 word is the negative of `ababbbabb`. -/
theorem alternatingSixAmbientRow25_state79_word_matrix :
    (row25Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 10) (Fin 10) ℂ) =
      -(A * B * A * B * B * B * A * B * B) := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row25Certificate.matrixB⁻¹ = -(B ^ 3) := by
    simpa [row25Certificate,
      alternatingSixAmbientRow25ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow25_matrixBGL_inv_val
  rw [hBinv]
  simp only [row25Certificate,
    alternatingSixAmbientRow25ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- Trace of the signed state-77 normal word. -/
theorem alternatingSixAmbientRow25_state77_word_trace :
    (row25Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 10) (Fin 10) ℂ).trace = -1 := by
  rw [alternatingSixAmbientRow25_state77_word_matrix,
    Matrix.trace_neg,
    alternatingSixAmbientRow25_positiveState77_trace]

/-- Trace of the signed state-79 normal word. -/
theorem alternatingSixAmbientRow25_state79_word_trace :
    (row25Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 10) (Fin 10) ℂ).trace = -1 := by
  rw [alternatingSixAmbientRow25_state79_word_matrix,
    Matrix.trace_neg,
    alternatingSixAmbientRow25_positiveState79_trace]

/-- The row-25 trace at the base word `b`. -/
def alternatingSixAmbientRow25Gamma : ℂ :=
  alternatingSixCyclotomicValue [(1, 5), (1, 15), (-1, 25)]

/-- The seven row-25 values before multiplication by a central scalar. -/
def alternatingSixAmbientRow25BaseWordValue :
    AlternatingSixAmbientClassBaseWord → ℂ
  | .identity => 10
  | .generatorA => 0
  | .generatorB => alternatingSixAmbientRow25Gamma
  | .generatorAB => 0
  | .generatorABSquared => 0
  | .state77 => -1
  | .state79 => -1

/-- Exact trace of every one of the seven row-25 base words. -/
theorem alternatingSixAmbientRow25_baseWord_trace
    (word : AlternatingSixAmbientClassBaseWord) :
    (row25Certificate.rewriteWordGL word.word :
        Matrix (Fin 10) (Fin 10) ℂ).trace =
      alternatingSixAmbientRow25BaseWordValue word := by
  cases word
  · simp [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      alternatingSixAmbientRow25BaseWordValue, Matrix.trace]
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow25BaseWordValue,
      row25Certificate,
      alternatingSixAmbientRow25ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow25_matrixA_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow25BaseWordValue,
      alternatingSixAmbientRow25Gamma,
      row25Certificate,
      alternatingSixAmbientRow25ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow25_matrixB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow25BaseWordValue,
      row25Certificate,
      alternatingSixAmbientRow25ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow25_matrixAB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow25BaseWordValue,
      pow_two, Matrix.mul_assoc,
      row25Certificate,
      alternatingSixAmbientRow25ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow25_matrixABSquared_trace
  · exact alternatingSixAmbientRow25_state77_word_trace
  · exact alternatingSixAmbientRow25_state79_word_trace

end InductiveMcKay
end McKayConjecture
