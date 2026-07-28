/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P11LongWordTraces
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P11ShortWordTraces

/-!
# Base-word traces for ATLAS degree 12, power 11

The two normal forms containing `b⁻¹` use `b⁻¹ = ζ⁶⁰b³ = -b³`.
Together with the split short- and long-word calculations, this supplies one
exact trace theorem for every checked class-representative base word.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot
local notation "A" => alternatingSixFiveAmbient_atlas12Power11_matrixA
local notation "B" => alternatingSixFiveAmbient_atlas12Power11_matrixB

private abbrev atlas12P11Certificate :=
  alternatingSixAmbientAtlas12P11ClassMatrixCertificate

/-- The primitive sixth root used to express the central scalar. -/
def alternatingSixAmbientAtlas12P11Eta : ℂ :=
  ζ ^ 20

/-- The central scalar `ζ¹⁰⁰`, expressed in the sixth-root basis. -/
def alternatingSixAmbientAtlas12P11Central : ℂ :=
  1 - alternatingSixAmbientAtlas12P11Eta

/-- The order-six relation for the twentieth power of the analytic root. -/
theorem alternatingSixAmbientAtlas12P11_orderSixRelation :
    ζ ^ 40 - ζ ^ 20 + 1 = 0 := by
  have h :=
    congrArg alternatingSixCyclotomicEmbedding
      alternatingSixCyclotomicRoot_orderSixRelation
  simpa only [map_sub, map_add, map_pow, map_one, map_zero,
    alternatingSixCyclotomicEmbedding_root] using h

/-- The power-eleven central scalar `ζ¹⁰⁰` is `1 - ζ²⁰`. -/
theorem alternatingSixAmbientAtlas12P11_root_pow_hundred :
    ζ ^ 100 = alternatingSixAmbientAtlas12P11Central := by
  change ζ ^ 100 = 1 - ζ ^ 20
  rw [show 100 = 20 * 5 by norm_num, pow_mul]
  linear_combination
    ((ζ ^ 20) ^ 3 + (ζ ^ 20) ^ 2 - 1) *
      alternatingSixAmbientAtlas12P11_orderSixRelation

private theorem atlas12P11_root_pow_sixty :
    ζ ^ 60 = -1 := by
  rw [alternatingSixComplexCyclotomicRoot, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 1
  all_goals ring_nf

/-- The second named relator acts as negative identity. -/
theorem alternatingSixAmbientAtlas12P11_relatorGL_one_eq_negOne :
    atlas12P11Certificate.relatorGL 1 = -1 := by
  apply Units.ext
  simp [atlas12P11Certificate,
    alternatingSixAmbientAtlas12P11ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate,
    AlternatingSixAmbientScalarPattern.exponent,
    atlas12P11_root_pow_sixty]

/-- For the power-eleven row, `b⁻¹ = -b³` as concrete matrices. -/
theorem alternatingSixAmbientAtlas12P11_matrixBGL_inv_val :
    (atlas12P11Certificate.matrixBGL⁻¹ :
        Matrix (Fin 12) (Fin 12) ℂ) =
      -(B ^ 3) := by
  have hfourth : atlas12P11Certificate.matrixBGL ^ 4 = -1 := by
    rw [atlas12P11Certificate.matrixBGL_fourth,
      alternatingSixAmbientAtlas12P11_relatorGL_one_eq_negOne]
  have hinverse :
      atlas12P11Certificate.matrixBGL⁻¹ =
        -(atlas12P11Certificate.matrixBGL ^ 3) := by
    apply mul_left_cancel (a := atlas12P11Certificate.matrixBGL)
    rw [mul_inv_cancel, mul_neg, ← pow_succ', hfourth]
    simp
  simpa [atlas12P11Certificate,
    alternatingSixAmbientAtlas12P11ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate] using
      congrArg Units.val hinverse

/-- The state-77 normal word is negative `ababbabbb`. -/
theorem alternatingSixAmbientAtlas12P11_state77_word_matrix :
    (atlas12P11Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 12) (Fin 12) ℂ) =
      -(A * B * A * B * B * A * B * B * B) := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      atlas12P11Certificate.matrixB⁻¹ = -(B ^ 3) := by
    simpa [atlas12P11Certificate,
      alternatingSixAmbientAtlas12P11ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlas12P11_matrixBGL_inv_val
  rw [hBinv]
  simp only [atlas12P11Certificate,
    alternatingSixAmbientAtlas12P11ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero, mul_neg]
  noncomm_ring

/-- The state-79 normal word is negative `ababbbabb`. -/
theorem alternatingSixAmbientAtlas12P11_state79_word_matrix :
    (atlas12P11Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 12) (Fin 12) ℂ) =
      -(A * B * A * B * B * B * A * B * B) := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      atlas12P11Certificate.matrixB⁻¹ = -(B ^ 3) := by
    simpa [atlas12P11Certificate,
      alternatingSixAmbientAtlas12P11ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlas12P11_matrixBGL_inv_val
  rw [hBinv]
  simp only [atlas12P11Certificate,
    alternatingSixAmbientAtlas12P11ClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- Trace of the state-77 normal word. -/
theorem alternatingSixAmbientAtlas12P11_state77_word_trace :
    (atlas12P11Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 12) (Fin 12) ℂ).trace = 0 := by
  rw [alternatingSixAmbientAtlas12P11_state77_word_matrix,
    Matrix.trace_neg,
    alternatingSixAmbientAtlas12P11_positiveState77_trace]
  norm_num

/-- Trace of the state-79 normal word. -/
theorem alternatingSixAmbientAtlas12P11_state79_word_trace :
    (atlas12P11Certificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 12) (Fin 12) ℂ).trace = 0 := by
  rw [alternatingSixAmbientAtlas12P11_state79_word_matrix,
    Matrix.trace_neg,
    alternatingSixAmbientAtlas12P11_positiveState79_trace]
  norm_num

/-- The ATLAS power-eleven trace at `ab`. -/
def alternatingSixAmbientAtlas12P11Alpha : ℂ :=
  alternatingSixCyclotomicValue [(1, 4), (-1, 16)]

/-- The ATLAS power-eleven trace at `ab²`. -/
def alternatingSixAmbientAtlas12P11Beta : ℂ :=
  alternatingSixCyclotomicValue
    [(1, 0), (1, 4), (-1, 8), (-1, 12),
      (-1, 16), (-1, 20), (1, 28)]

/-- Values of the seven base words before multiplication by the center. -/
def alternatingSixAmbientAtlas12P11BaseWordValue :
    AlternatingSixAmbientClassBaseWord → ℂ
  | .identity => 12
  | .generatorA => 0
  | .generatorB => 0
  | .generatorAB => alternatingSixAmbientAtlas12P11Alpha
  | .generatorABSquared => alternatingSixAmbientAtlas12P11Beta
  | .state77 => 0
  | .state79 => 0

/-- Exact trace of each power-eleven base word. -/
theorem alternatingSixAmbientAtlas12P11_baseWord_trace
    (word : AlternatingSixAmbientClassBaseWord) :
    (atlas12P11Certificate.rewriteWordGL word.word :
        Matrix (Fin 12) (Fin 12) ℂ).trace =
      alternatingSixAmbientAtlas12P11BaseWordValue word := by
  cases word
  · simp [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      alternatingSixAmbientAtlas12P11BaseWordValue, Matrix.trace]
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientAtlas12P11BaseWordValue,
      atlas12P11Certificate,
      alternatingSixAmbientAtlas12P11ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlas12P11_matrixA_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientAtlas12P11BaseWordValue,
      atlas12P11Certificate,
      alternatingSixAmbientAtlas12P11ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlas12P11_matrixB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientAtlas12P11BaseWordValue,
      alternatingSixAmbientAtlas12P11Alpha,
      atlas12P11Certificate,
      alternatingSixAmbientAtlas12P11ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlas12P11_matrixAB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientAtlas12P11BaseWordValue,
      alternatingSixAmbientAtlas12P11Beta,
      pow_two, Matrix.mul_assoc,
      atlas12P11Certificate,
      alternatingSixAmbientAtlas12P11ClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlas12P11_matrixABSquared_trace
  · exact alternatingSixAmbientAtlas12P11_state77_word_trace
  · exact alternatingSixAmbientAtlas12P11_state79_word_trace

end InductiveMcKay
end McKayConjecture
