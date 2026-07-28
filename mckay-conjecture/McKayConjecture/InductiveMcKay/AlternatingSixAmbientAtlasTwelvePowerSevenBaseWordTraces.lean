/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerSevenLongWordTraces
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerSevenShortWordTraces

/-!
# Base-word traces for the ATLAS degree-12 power-seven row

The two normal forms containing `b⁻¹` use `b⁻¹ = ζ⁶⁰b³ = -b³`.
Together with the split short- and long-word calculations, this supplies an
exact trace theorem for every checked class-representative base word.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot
local notation "A" =>
  alternatingSixFiveAmbient_atlas12Power7_matrixA
local notation "B" =>
  alternatingSixFiveAmbient_atlas12Power7_matrixB

private abbrev atlasTwelvePowerSevenCertificate :=
  alternatingSixAmbientAtlasTwelvePowerSevenClassMatrixCertificate

private theorem atlasTwelvePowerSeven_root_pow_sixty :
    ζ ^ 60 = -1 := by
  rw [alternatingSixComplexCyclotomicRoot, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 1
  all_goals ring_nf

/-- The second named relator acts as negative identity. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_relatorGL_one_eq_negOne :
    atlasTwelvePowerSevenCertificate.relatorGL 1 = -1 := by
  apply Units.ext
  simp [atlasTwelvePowerSevenCertificate,
    alternatingSixAmbientAtlasTwelvePowerSevenClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate,
    AlternatingSixAmbientScalarPattern.exponent,
    atlasTwelvePowerSeven_root_pow_sixty]

/-- For the power-seven row, `b⁻¹ = -b³` as concrete matrices. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_matrixBGL_inv_val :
    (atlasTwelvePowerSevenCertificate.matrixBGL⁻¹ :
        Matrix (Fin 12) (Fin 12) ℂ) =
      -(B ^ 3) := by
  have hfourth :
      atlasTwelvePowerSevenCertificate.matrixBGL ^ 4 = -1 := by
    rw [atlasTwelvePowerSevenCertificate.matrixBGL_fourth,
      alternatingSixAmbientAtlasTwelvePowerSeven_relatorGL_one_eq_negOne]
  have hinverse :
      atlasTwelvePowerSevenCertificate.matrixBGL⁻¹ =
        -(atlasTwelvePowerSevenCertificate.matrixBGL ^ 3) := by
    apply mul_left_cancel
      (a := atlasTwelvePowerSevenCertificate.matrixBGL)
    rw [mul_inv_cancel, mul_neg, ← pow_succ', hfourth]
    simp
  simpa [atlasTwelvePowerSevenCertificate,
    alternatingSixAmbientAtlasTwelvePowerSevenClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate] using
      congrArg Units.val hinverse

/-- The state-77 normal word is negative `ababbabbb`. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_state77_word_matrix :
    (atlasTwelvePowerSevenCertificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 12) (Fin 12) ℂ) =
      -(A * B * A * B * B * A * B * B * B) := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      atlasTwelvePowerSevenCertificate.matrixB⁻¹ = -(B ^ 3) := by
    simpa [atlasTwelvePowerSevenCertificate,
      alternatingSixAmbientAtlasTwelvePowerSevenClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlasTwelvePowerSeven_matrixBGL_inv_val
  rw [hBinv]
  simp only [atlasTwelvePowerSevenCertificate,
    alternatingSixAmbientAtlasTwelvePowerSevenClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero, mul_neg]
  noncomm_ring

/-- The state-79 normal word is negative `ababbbabb`. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_state79_word_matrix :
    (atlasTwelvePowerSevenCertificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 12) (Fin 12) ℂ) =
      -(A * B * A * B * B * B * A * B * B) := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      atlasTwelvePowerSevenCertificate.matrixB⁻¹ = -(B ^ 3) := by
    simpa [atlasTwelvePowerSevenCertificate,
      alternatingSixAmbientAtlasTwelvePowerSevenClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlasTwelvePowerSeven_matrixBGL_inv_val
  rw [hBinv]
  simp only [atlasTwelvePowerSevenCertificate,
    alternatingSixAmbientAtlasTwelvePowerSevenClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- Trace of the state-77 normal word. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_state77_word_trace :
    (atlasTwelvePowerSevenCertificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 12) (Fin 12) ℂ).trace = 0 := by
  rw [alternatingSixAmbientAtlasTwelvePowerSeven_state77_word_matrix,
    Matrix.trace_neg,
    alternatingSixAmbientAtlasTwelvePowerSeven_positiveState77_trace]
  norm_num

/-- Trace of the state-79 normal word. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_state79_word_trace :
    (atlasTwelvePowerSevenCertificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 12) (Fin 12) ℂ).trace = 0 := by
  rw [alternatingSixAmbientAtlasTwelvePowerSeven_state79_word_matrix,
    Matrix.trace_neg,
    alternatingSixAmbientAtlasTwelvePowerSeven_positiveState79_trace]
  norm_num

/-- The primitive sixth root giving the power-seven central scalar. -/
def alternatingSixAmbientAtlasTwelvePowerSevenEta : ℂ :=
  ζ ^ 20

/-- The ATLAS power-seven trace at `ab`. -/
def alternatingSixAmbientAtlasTwelvePowerSevenAlpha : ℂ :=
  alternatingSixCyclotomicValue
    [(1, 0), (1, 4), (-1, 8), (-1, 12), (-1, 16),
      (-1, 20), (1, 28)]

/-- The ATLAS power-seven trace at `ab²`. -/
def alternatingSixAmbientAtlasTwelvePowerSevenBeta : ℂ :=
  alternatingSixCyclotomicValue [(1, 4), (-1, 16)]

/-- Values of the seven base words before multiplication by the center. -/
def alternatingSixAmbientAtlasTwelvePowerSevenBaseWordValue :
    AlternatingSixAmbientClassBaseWord → ℂ
  | .identity => 12
  | .generatorA => 0
  | .generatorB => 0
  | .generatorAB =>
      alternatingSixAmbientAtlasTwelvePowerSevenAlpha
  | .generatorABSquared =>
      alternatingSixAmbientAtlasTwelvePowerSevenBeta
  | .state77 => 0
  | .state79 => 0

/-- Exact trace of each power-seven base word. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_baseWord_trace
    (word : AlternatingSixAmbientClassBaseWord) :
    (atlasTwelvePowerSevenCertificate.rewriteWordGL word.word :
        Matrix (Fin 12) (Fin 12) ℂ).trace =
      alternatingSixAmbientAtlasTwelvePowerSevenBaseWordValue word := by
  cases word
  · simp [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      alternatingSixAmbientAtlasTwelvePowerSevenBaseWordValue,
      Matrix.trace]
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientAtlasTwelvePowerSevenBaseWordValue,
      atlasTwelvePowerSevenCertificate,
      alternatingSixAmbientAtlasTwelvePowerSevenClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlasTwelvePowerSeven_matrixA_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientAtlasTwelvePowerSevenBaseWordValue,
      atlasTwelvePowerSevenCertificate,
      alternatingSixAmbientAtlasTwelvePowerSevenClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlasTwelvePowerSeven_matrixB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientAtlasTwelvePowerSevenBaseWordValue,
      alternatingSixAmbientAtlasTwelvePowerSevenAlpha,
      atlasTwelvePowerSevenCertificate,
      alternatingSixAmbientAtlasTwelvePowerSevenClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlasTwelvePowerSeven_matrixAB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientAtlasTwelvePowerSevenBaseWordValue,
      alternatingSixAmbientAtlasTwelvePowerSevenBeta,
      pow_two, Matrix.mul_assoc,
      atlasTwelvePowerSevenCertificate,
      alternatingSixAmbientAtlasTwelvePowerSevenClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlasTwelvePowerSeven_matrixABSquared_trace
  · exact
      alternatingSixAmbientAtlasTwelvePowerSeven_state77_word_trace
  · exact
      alternatingSixAmbientAtlasTwelvePowerSeven_state79_word_trace

end InductiveMcKay
end McKayConjecture
