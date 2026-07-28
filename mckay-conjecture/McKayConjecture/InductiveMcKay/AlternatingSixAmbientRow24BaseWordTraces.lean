/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow24LongWordTraces
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow24ShortWordTraces

/-!
# Traces of the seven row-24 class-representative base words

The two normal forms containing `b⁻¹` are converted to positive words using
the central relation `b⁴ = -1`. Together with the short-word and long-word
calculations, this gives one trace theorem for each of the seven noncentral
base-word labels used by the thirty-one checked class representatives.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot
local notation "A" => alternatingSixFiveAmbient_row24_matrixA
local notation "B" => alternatingSixFiveAmbient_row24_matrixB

private abbrev row24Certificate :=
  alternatingSixAmbientRow24ClassMatrixCertificate

private theorem row24_root_pow_sixty :
    ζ ^ 60 = -1 := by
  rw [alternatingSixComplexCyclotomicRoot, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 1
  all_goals ring_nf

/-- Every named central relator in row 24 acts as negative identity. -/
theorem alternatingSixAmbientRow24_relatorGL_eq_negOne
    (i : Fin 4) :
    row24Certificate.relatorGL i = -1 := by
  fin_cases i <;>
    apply Units.ext <;>
    simp [row24Certificate,
      alternatingSixAmbientRow24ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate,
      AlternatingSixAmbientScalarPattern.exponent,
      row24_root_pow_sixty]

/-- In row 24, `b⁻¹ = -b³`, as an equality of concrete matrices. -/
theorem alternatingSixAmbientRow24_matrixBGL_inv_val :
    (row24Certificate.matrixBGL⁻¹ :
        Matrix (Fin 10) (Fin 10) ℂ) =
      -(B ^ 3) := by
  have hfourth : row24Certificate.matrixBGL ^ 4 = -1 := by
    rw [row24Certificate.matrixBGL_fourth,
      alternatingSixAmbientRow24_relatorGL_eq_negOne]
  have hinverse :
      row24Certificate.matrixBGL⁻¹ =
        -(row24Certificate.matrixBGL ^ 3) := by
    apply mul_left_cancel (a := row24Certificate.matrixBGL)
    rw [mul_inv_cancel, mul_neg, ← pow_succ', hfourth]
    simp
  simpa [row24Certificate,
    alternatingSixAmbientRow24ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate] using
      congrArg Units.val hinverse

/-- The signed state-77 word is the negative of `ababbabbb`. -/
theorem alternatingSixAmbientRow24_state77_word_matrix :
    (row24Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 10) (Fin 10) ℂ) =
      -(A * B * A * B * B * A * B * B * B) := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row24Certificate.matrixB⁻¹ = -(B ^ 3) := by
    simpa [row24Certificate,
      alternatingSixAmbientRow24ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow24_matrixBGL_inv_val
  rw [hBinv]
  simp only [row24Certificate,
    alternatingSixAmbientRow24ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero, mul_neg]
  noncomm_ring

/-- The signed state-79 word is the negative of `ababbbabb`. -/
theorem alternatingSixAmbientRow24_state79_word_matrix :
    (row24Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 10) (Fin 10) ℂ) =
      -(A * B * A * B * B * B * A * B * B) := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row24Certificate.matrixB⁻¹ = -(B ^ 3) := by
    simpa [row24Certificate,
      alternatingSixAmbientRow24ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow24_matrixBGL_inv_val
  rw [hBinv]
  simp only [row24Certificate,
    alternatingSixAmbientRow24ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- Trace of the signed state-77 normal word. -/
theorem alternatingSixAmbientRow24_state77_word_trace :
    (row24Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 10) (Fin 10) ℂ).trace = -1 := by
  rw [alternatingSixAmbientRow24_state77_word_matrix,
    Matrix.trace_neg,
    alternatingSixAmbientRow24_positiveState77_trace]

/-- Trace of the signed state-79 normal word. -/
theorem alternatingSixAmbientRow24_state79_word_trace :
    (row24Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 10) (Fin 10) ℂ).trace = -1 := by
  rw [alternatingSixAmbientRow24_state79_word_matrix,
    Matrix.trace_neg,
    alternatingSixAmbientRow24_positiveState79_trace]

/-- The row-24 trace at the second generator. -/
def alternatingSixAmbientRow24Gamma : ℂ :=
  alternatingSixCyclotomicValue
    [(-1, 5), (-1, 15), (1, 25)]

/-- The seven row-24 values before multiplication by a central scalar. -/
def alternatingSixAmbientRow24BaseWordValue :
    AlternatingSixAmbientClassBaseWord → ℂ
  | .identity => 10
  | .generatorA => 0
  | .generatorB => alternatingSixAmbientRow24Gamma
  | .generatorAB => 0
  | .generatorABSquared => 0
  | .state77 => -1
  | .state79 => -1

/-- Exact trace of every one of the seven row-24 base words. -/
theorem alternatingSixAmbientRow24_baseWord_trace
    (word : AlternatingSixAmbientClassBaseWord) :
    (row24Certificate.rewriteWordGL word.word :
        Matrix (Fin 10) (Fin 10) ℂ).trace =
      alternatingSixAmbientRow24BaseWordValue word := by
  cases word
  · simp [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      alternatingSixAmbientRow24BaseWordValue, Matrix.trace]
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow24BaseWordValue,
      row24Certificate,
      alternatingSixAmbientRow24ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow24_matrixA_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow24BaseWordValue,
      alternatingSixAmbientRow24Gamma,
      row24Certificate,
      alternatingSixAmbientRow24ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow24_matrixB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow24BaseWordValue,
      row24Certificate,
      alternatingSixAmbientRow24ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow24_matrixAB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow24BaseWordValue, pow_two,
      Matrix.mul_assoc,
      row24Certificate,
      alternatingSixAmbientRow24ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow24_matrixABSquared_trace
  · exact alternatingSixAmbientRow24_state77_word_trace
  · exact alternatingSixAmbientRow24_state79_word_trace

end InductiveMcKay
end McKayConjecture
