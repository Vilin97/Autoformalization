/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow23LongWordTraces
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow23ShortWordTraces

/-!
# Traces of the seven row-23 class-representative base words

The two normal forms containing `b⁻¹` are converted to positive words using
`b⁴ = 1`.  The resulting short- and long-word calculations give an exact
trace theorem for every base-word label used by the checked classes.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "A" => alternatingSixFiveAmbient_row23_matrixA
local notation "B" => alternatingSixFiveAmbient_row23_matrixB

private abbrev row23Certificate :=
  alternatingSixAmbientRow23ClassMatrixCertificate

/-- Every named central relator acts trivially in row 23. -/
theorem alternatingSixAmbientRow23_relatorGL_eq_one
    (i : Fin 4) :
    row23Certificate.relatorGL i = 1 := by
  fin_cases i <;>
    apply Units.ext <;>
    simp [row23Certificate,
      alternatingSixAmbientRow23ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate,
      AlternatingSixAmbientScalarPattern.exponent]

/-- In row 23, `b⁻¹ = b³`, as an equality of concrete matrices. -/
theorem alternatingSixAmbientRow23_matrixBGL_inv_val :
    (row23Certificate.matrixBGL⁻¹ :
        Matrix (Fin 10) (Fin 10) ℂ) =
      B ^ 3 := by
  have hfourth : row23Certificate.matrixBGL ^ 4 = 1 := by
    rw [row23Certificate.matrixBGL_fourth,
      alternatingSixAmbientRow23_relatorGL_eq_one]
  have hinverse :
      row23Certificate.matrixBGL⁻¹ =
        row23Certificate.matrixBGL ^ 3 := by
    apply mul_left_cancel (a := row23Certificate.matrixBGL)
    rw [mul_inv_cancel, ← pow_succ', hfourth]
  simpa [row23Certificate,
    alternatingSixAmbientRow23ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate] using
      congrArg Units.val hinverse

/-- The state-77 normal word is the positive word `ababbabbb`. -/
theorem alternatingSixAmbientRow23_state77_word_matrix :
    (row23Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 10) (Fin 10) ℂ) =
      A * B * A * B * B * A * B * B * B := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row23Certificate.matrixB⁻¹ = B ^ 3 := by
    simpa [row23Certificate,
      alternatingSixAmbientRow23ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow23_matrixBGL_inv_val
  rw [hBinv]
  simp only [row23Certificate,
    alternatingSixAmbientRow23ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- The state-79 normal word is the positive word `ababbbabb`. -/
theorem alternatingSixAmbientRow23_state79_word_matrix :
    (row23Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 10) (Fin 10) ℂ) =
      A * B * A * B * B * B * A * B * B := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      row23Certificate.matrixB⁻¹ = B ^ 3 := by
    simpa [row23Certificate,
      alternatingSixAmbientRow23ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow23_matrixBGL_inv_val
  rw [hBinv]
  simp only [row23Certificate,
    alternatingSixAmbientRow23ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- Trace of the state-77 normal word. -/
theorem alternatingSixAmbientRow23_state77_word_trace :
    (row23Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 10) (Fin 10) ℂ).trace = 1 := by
  rw [alternatingSixAmbientRow23_state77_word_matrix,
    alternatingSixAmbientRow23_positiveState77_trace]

/-- Trace of the state-79 normal word. -/
theorem alternatingSixAmbientRow23_state79_word_trace :
    (row23Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 10) (Fin 10) ℂ).trace = 1 := by
  rw [alternatingSixAmbientRow23_state79_word_matrix,
    alternatingSixAmbientRow23_positiveState79_trace]

/-- The seven row-23 values before the trivial central scalar. -/
def alternatingSixAmbientRow23BaseWordValue :
    AlternatingSixAmbientClassBaseWord → ℂ
  | .identity => 10
  | .generatorA => -2
  | .generatorB => 0
  | .generatorAB => 0
  | .generatorABSquared => 0
  | .state77 => 1
  | .state79 => 1

/-- Exact trace of every one of the seven row-23 base words. -/
theorem alternatingSixAmbientRow23_baseWord_trace
    (word : AlternatingSixAmbientClassBaseWord) :
    (row23Certificate.rewriteWordGL word.word :
        Matrix (Fin 10) (Fin 10) ℂ).trace =
      alternatingSixAmbientRow23BaseWordValue word := by
  cases word
  · simp [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      alternatingSixAmbientRow23BaseWordValue, Matrix.trace]
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow23BaseWordValue,
      row23Certificate,
      alternatingSixAmbientRow23ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow23_matrixA_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow23BaseWordValue,
      row23Certificate,
      alternatingSixAmbientRow23ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow23_matrixB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow23BaseWordValue,
      row23Certificate,
      alternatingSixAmbientRow23ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow23_matrixAB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientRow23BaseWordValue,
      pow_two, Matrix.mul_assoc,
      row23Certificate,
      alternatingSixAmbientRow23ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientRow23_matrixABSquared_trace
  · exact alternatingSixAmbientRow23_state77_word_trace
  · exact alternatingSixAmbientRow23_state79_word_trace

end InductiveMcKay
end McKayConjecture
