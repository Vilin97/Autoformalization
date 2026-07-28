/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow19LongWordTraces
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow19ShortWordTraces

/-!
# Traces of the seven row-19 class-representative base words

The two normal forms containing `b⁻¹` are converted to positive words using
the central relation `b⁴ = -1`.  Together with the short-word and long-word
calculations, this gives one trace theorem for each of the seven noncentral
base-word labels used by the thirty-one checked class representatives.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot
local notation "A" => alternatingSixFiveAmbient_row19_matrixA
local notation "B" => alternatingSixFiveAmbient_row19_matrixB

private abbrev row19Certificate :=
  alternatingSixAmbientRow19ClassMatrixCertificate

private theorem row19_root_pow_sixty :
    ζ ^ 60 = -1 := by
  rw [alternatingSixComplexCyclotomicRoot, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 1
  all_goals ring_nf

/-- Every named central relator in row 19 acts as negative identity. -/
theorem alternatingSixAmbientRow19_relatorGL_eq_negOne
    (i : Fin 4) :
    row19Certificate.relatorGL i = -1 := by
  fin_cases i <;>
    apply Units.ext <;>
    simp [row19Certificate,
      alternatingSixAmbientRow19ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate,
      AlternatingSixAmbientScalarPattern.exponent,
      row19_root_pow_sixty]

/-- In row 19, `b⁻¹ = -b³`, as an equality of concrete matrices. -/
theorem alternatingSixAmbientRow19_matrixBGL_inv_val :
    (row19Certificate.matrixBGL⁻¹ :
        Matrix (Fin 8) (Fin 8) ℂ) =
      -(B ^ 3) := by
  have hfourth : row19Certificate.matrixBGL ^ 4 = -1 := by
    rw [row19Certificate.matrixBGL_fourth,
      alternatingSixAmbientRow19_relatorGL_eq_negOne]
  have hinverse :
      row19Certificate.matrixBGL⁻¹ =
        -(row19Certificate.matrixBGL ^ 3) := by
    apply mul_left_cancel (a := row19Certificate.matrixBGL)
    rw [mul_inv_cancel, mul_neg, ← pow_succ', hfourth]
    simp
  simpa [row19Certificate,
    alternatingSixAmbientRow19ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate] using
      congrArg Units.val hinverse

/-- The signed state-77 word is the negative of `ababbabbb`. -/
theorem alternatingSixAmbientRow19_state77_word_matrix :
    (row19Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 8) (Fin 8) ℂ) =
      -(A * B * A * B * B * A * B * B * B) := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row19Certificate.matrixB⁻¹ = -(B ^ 3) := by
    simpa [row19Certificate,
      alternatingSixAmbientRow19ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow19_matrixBGL_inv_val
  rw [hBinv]
  simp only [row19Certificate,
    alternatingSixAmbientRow19ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero, mul_neg]
  noncomm_ring

/-- The signed state-79 word is the negative of `ababbbabb`. -/
theorem alternatingSixAmbientRow19_state79_word_matrix :
    (row19Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 8) (Fin 8) ℂ) =
      -(A * B * A * B * B * B * A * B * B) := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row19Certificate.matrixB⁻¹ = -(B ^ 3) := by
    simpa [row19Certificate,
      alternatingSixAmbientRow19ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow19_matrixBGL_inv_val
  rw [hBinv]
  simp only [row19Certificate,
    alternatingSixAmbientRow19ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- Trace of the signed state-77 normal word. -/
theorem alternatingSixAmbientRow19_state77_word_trace :
    (row19Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 8) (Fin 8) ℂ).trace = 1 := by
  rw [alternatingSixAmbientRow19_state77_word_matrix,
    Matrix.trace_neg,
    alternatingSixAmbientRow19_positiveState77_trace]
  norm_num

/-- Trace of the signed state-79 normal word. -/
theorem alternatingSixAmbientRow19_state79_word_trace :
    (row19Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 8) (Fin 8) ℂ).trace = 1 := by
  rw [alternatingSixAmbientRow19_state79_word_matrix,
    Matrix.trace_neg,
    alternatingSixAmbientRow19_positiveState79_trace]
  norm_num

/-- The row-19 trace at the base word `ab`. -/
def alternatingSixAmbientRow19Alpha : ℂ :=
  alternatingSixCyclotomicValue
    [(-1, 8), (-1, 12), (1, 28)]

/-- The row-19 trace at the base word `ab²`. -/
def alternatingSixAmbientRow19Beta : ℂ :=
  alternatingSixCyclotomicValue
    [(-1, 0), (1, 8), (1, 12), (-1, 28)]

/-- The seven row-19 values before multiplication by a central scalar. -/
def alternatingSixAmbientRow19BaseWordValue :
    AlternatingSixAmbientClassBaseWord → ℂ
  | .identity => 8
  | .generatorA => 0
  | .generatorB => 0
  | .generatorAB => alternatingSixAmbientRow19Alpha
  | .generatorABSquared => alternatingSixAmbientRow19Beta
  | .state77 => 1
  | .state79 => 1

/-- Exact trace of every one of the seven row-19 base words. -/
theorem alternatingSixAmbientRow19_baseWord_trace
    (word : AlternatingSixAmbientClassBaseWord) :
    (row19Certificate.rewriteWordGL word.word :
        Matrix (Fin 8) (Fin 8) ℂ).trace =
      alternatingSixAmbientRow19BaseWordValue word := by
  cases word
  · simp [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      alternatingSixAmbientRow19BaseWordValue, Matrix.trace]
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow19BaseWordValue,
      row19Certificate,
      alternatingSixAmbientRow19ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow19_matrixA_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow19BaseWordValue,
      row19Certificate,
      alternatingSixAmbientRow19ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow19_matrixB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow19BaseWordValue,
      alternatingSixAmbientRow19Alpha,
      row19Certificate,
      alternatingSixAmbientRow19ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow19_matrixAB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow19BaseWordValue,
      alternatingSixAmbientRow19Beta, pow_two,
      Matrix.mul_assoc,
      row19Certificate,
      alternatingSixAmbientRow19ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow19_matrixABSquared_trace
  · exact alternatingSixAmbientRow19_state77_word_trace
  · exact alternatingSixAmbientRow19_state79_word_trace

end InductiveMcKay
end McKayConjecture
