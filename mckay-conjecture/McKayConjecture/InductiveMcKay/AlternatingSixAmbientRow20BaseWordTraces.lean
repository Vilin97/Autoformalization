/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow20LongWordTraces
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow20ShortWordTraces

/-!
# Traces of the seven row-20 class-representative base words

The two normal forms containing `b⁻¹` are converted to positive words using
the trivial central relation `b⁴ = 1`. Together with the short- and long-word
calculations, this gives the trace of every base word used by the thirty-one
checked class representatives.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "A" => alternatingSixFiveAmbient_row20_matrixA
local notation "B" => alternatingSixFiveAmbient_row20_matrixB

private abbrev row20Certificate :=
  alternatingSixAmbientRow20ClassMatrixCertificate

/-- Every named central relator acts trivially in row 20. -/
theorem alternatingSixAmbientRow20_relatorGL_eq_one
    (i : Fin 4) :
    row20Certificate.relatorGL i = 1 := by
  fin_cases i <;>
    apply Units.ext <;>
    simp [row20Certificate,
      alternatingSixAmbientRow20ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate,
      AlternatingSixAmbientScalarPattern.exponent]

/-- In row 20, `b⁻¹ = b³`, as an equality of concrete matrices. -/
theorem alternatingSixAmbientRow20_matrixBGL_inv_val :
    (row20Certificate.matrixBGL⁻¹ :
        Matrix (Fin 9) (Fin 9) ℂ) =
      B ^ 3 := by
  have hfourth : row20Certificate.matrixBGL ^ 4 = 1 := by
    rw [row20Certificate.matrixBGL_fourth,
      alternatingSixAmbientRow20_relatorGL_eq_one]
  have hinverse :
      row20Certificate.matrixBGL⁻¹ =
        row20Certificate.matrixBGL ^ 3 := by
    apply mul_left_cancel (a := row20Certificate.matrixBGL)
    rw [mul_inv_cancel, ← pow_succ', hfourth]
  simpa [row20Certificate,
    alternatingSixAmbientRow20ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate] using
      congrArg Units.val hinverse

/-- The signed state-77 normal word evaluates to `ababbabbb`. -/
theorem alternatingSixAmbientRow20_state77_word_matrix :
    (row20Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 9) (Fin 9) ℂ) =
      A * B * A * B * B * A * B * B * B := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row20Certificate.matrixB⁻¹ = B ^ 3 := by
    simpa [row20Certificate,
      alternatingSixAmbientRow20ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow20_matrixBGL_inv_val
  rw [hBinv]
  simp only [row20Certificate,
    alternatingSixAmbientRow20ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- The signed state-79 normal word evaluates to `ababbbabb`. -/
theorem alternatingSixAmbientRow20_state79_word_matrix :
    (row20Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 9) (Fin 9) ℂ) =
      A * B * A * B * B * B * A * B * B := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row20Certificate.matrixB⁻¹ = B ^ 3 := by
    simpa [row20Certificate,
      alternatingSixAmbientRow20ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow20_matrixBGL_inv_val
  rw [hBinv]
  simp only [row20Certificate,
    alternatingSixAmbientRow20ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- Trace of the state-77 normal word. -/
theorem alternatingSixAmbientRow20_state77_word_trace :
    (row20Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 9) (Fin 9) ℂ).trace = 0 := by
  rw [alternatingSixAmbientRow20_state77_word_matrix,
    alternatingSixAmbientRow20_positiveState77_trace]

/-- Trace of the state-79 normal word. -/
theorem alternatingSixAmbientRow20_state79_word_trace :
    (row20Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 9) (Fin 9) ℂ).trace = 0 := by
  rw [alternatingSixAmbientRow20_state79_word_matrix,
    alternatingSixAmbientRow20_positiveState79_trace]

/-- The seven row-20 values before multiplication by a central scalar. -/
def alternatingSixAmbientRow20BaseWordValue :
    AlternatingSixAmbientClassBaseWord → ℂ
  | .identity => 9
  | .generatorA => 1
  | .generatorB => 1
  | .generatorAB => -1
  | .generatorABSquared => -1
  | .state77 => 0
  | .state79 => 0

/-- Exact trace of every one of the seven row-20 base words. -/
theorem alternatingSixAmbientRow20_baseWord_trace
    (word : AlternatingSixAmbientClassBaseWord) :
    (row20Certificate.rewriteWordGL word.word :
        Matrix (Fin 9) (Fin 9) ℂ).trace =
      alternatingSixAmbientRow20BaseWordValue word := by
  cases word
  · simp [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      alternatingSixAmbientRow20BaseWordValue, Matrix.trace]
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow20BaseWordValue,
      row20Certificate,
      alternatingSixAmbientRow20ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow20_matrixA_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow20BaseWordValue,
      row20Certificate,
      alternatingSixAmbientRow20ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow20_matrixB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow20BaseWordValue,
      row20Certificate,
      alternatingSixAmbientRow20ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow20_matrixAB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow20BaseWordValue, pow_two,
      Matrix.mul_assoc,
      row20Certificate,
      alternatingSixAmbientRow20ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow20_matrixABSquared_trace
  · exact alternatingSixAmbientRow20_state77_word_trace
  · exact alternatingSixAmbientRow20_state79_word_trace

end InductiveMcKay
end McKayConjecture
