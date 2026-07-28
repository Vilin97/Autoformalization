/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerTwoLongWordTraces
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerTwoShortWordTraces

/-!
# Base-word traces for the ATLAS degree-twelve power-2 row

The two normal forms containing `b⁻¹` use `b⁻¹ = ζ⁶⁰b³ = -b³`.
Together with the split short- and long-word calculations, this supplies one
exact trace theorem for every checked class-representative base word.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot
local notation "A" => alternatingSixFiveAmbient_atlas12Power2_matrixA
local notation "B" => alternatingSixFiveAmbient_atlas12Power2_matrixB

private abbrev atlasTwelvePowerTwoCertificate :=
  alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate

/-- The primitive sixth root used to express the central scalar. -/
def alternatingSixAmbientAtlasTwelvePowerTwoEta : ℂ :=
  ζ ^ 20

/-- The central scalar `ζ¹⁰⁰`, expressed in the sixth-root basis. -/
def alternatingSixAmbientAtlasTwelvePowerTwoCentral : ℂ :=
  1 - alternatingSixAmbientAtlasTwelvePowerTwoEta

/-- The order-six relation for the twentieth power of the analytic root. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_orderSixRelation :
    ζ ^ 40 - ζ ^ 20 + 1 = 0 := by
  have h :=
    congrArg alternatingSixCyclotomicEmbedding
      alternatingSixCyclotomicRoot_orderSixRelation
  simpa only [map_sub, map_add, map_pow, map_one, map_zero,
    alternatingSixCyclotomicEmbedding_root] using h

/-- The first central scalar `ζ¹⁰⁰` is `1 - ζ²⁰`. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_root_pow_hundred :
    ζ ^ 100 = alternatingSixAmbientAtlasTwelvePowerTwoCentral := by
  change ζ ^ 100 = 1 - ζ ^ 20
  rw [show 100 = 20 * 5 by norm_num, pow_mul]
  linear_combination
    ((ζ ^ 20) ^ 3 + (ζ ^ 20) ^ 2 - 1) *
      alternatingSixAmbientAtlasTwelvePowerTwo_orderSixRelation

private theorem atlasTwelvePowerTwo_root_pow_sixty :
    ζ ^ 60 = -1 := by
  rw [alternatingSixComplexCyclotomicRoot, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 1
  all_goals ring_nf

/-- The second named relator acts as negative identity. -/
theorem
    alternatingSixAmbientAtlasTwelvePowerTwo_relatorGL_one_eq_negOne :
    atlasTwelvePowerTwoCertificate.relatorGL 1 = -1 := by
  apply Units.ext
  simp [atlasTwelvePowerTwoCertificate,
    alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate,
    AlternatingSixAmbientScalarPattern.exponent,
    atlasTwelvePowerTwo_root_pow_sixty]

/-- For the power-2 row, `b⁻¹ = -b³` as concrete matrices. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_matrixBGL_inv_val :
    (atlasTwelvePowerTwoCertificate.matrixBGL⁻¹ :
        Matrix (Fin 12) (Fin 12) ℂ) =
      -(B ^ 3) := by
  have hfourth :
      atlasTwelvePowerTwoCertificate.matrixBGL ^ 4 = -1 := by
    rw [atlasTwelvePowerTwoCertificate.matrixBGL_fourth,
      alternatingSixAmbientAtlasTwelvePowerTwo_relatorGL_one_eq_negOne]
  have hinverse :
      atlasTwelvePowerTwoCertificate.matrixBGL⁻¹ =
        -(atlasTwelvePowerTwoCertificate.matrixBGL ^ 3) := by
    apply mul_left_cancel
      (a := atlasTwelvePowerTwoCertificate.matrixBGL)
    rw [mul_inv_cancel, mul_neg, ← pow_succ', hfourth]
    simp
  simpa [atlasTwelvePowerTwoCertificate,
    alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate] using
      congrArg Units.val hinverse

/-- The state-77 normal word is negative `ababbabbb`. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_state77_word_matrix :
    (atlasTwelvePowerTwoCertificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 12) (Fin 12) ℂ) =
      -(A * B * A * B * B * A * B * B * B) := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      atlasTwelvePowerTwoCertificate.matrixB⁻¹ = -(B ^ 3) := by
    simpa [atlasTwelvePowerTwoCertificate,
      alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlasTwelvePowerTwo_matrixBGL_inv_val
  rw [hBinv]
  simp only [atlasTwelvePowerTwoCertificate,
    alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero, mul_neg]
  noncomm_ring

/-- The state-79 normal word is negative `ababbbabb`. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_state79_word_matrix :
    (atlasTwelvePowerTwoCertificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 12) (Fin 12) ℂ) =
      -(A * B * A * B * B * B * A * B * B) := by
  simp [AlternatingSixAmbientClassBaseWord.word,
    AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
    AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL]
  have hBinv :
      atlasTwelvePowerTwoCertificate.matrixB⁻¹ = -(B ^ 3) := by
    simpa [atlasTwelvePowerTwoCertificate,
      alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlasTwelvePowerTwo_matrixBGL_inv_val
  rw [hBinv]
  simp only [atlasTwelvePowerTwoCertificate,
    alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate,
    alternatingSixAmbientMatrixRowCertificate]
  simp only [pow_succ, pow_zero]
  noncomm_ring

/-- Trace of the state-77 normal word. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_state77_word_trace :
    (atlasTwelvePowerTwoCertificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state77.word :
      Matrix (Fin 12) (Fin 12) ℂ).trace = 0 := by
  rw [alternatingSixAmbientAtlasTwelvePowerTwo_state77_word_matrix,
    Matrix.trace_neg,
    alternatingSixAmbientAtlasTwelvePowerTwo_positiveState77_trace]
  norm_num

/-- Trace of the state-79 normal word. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_state79_word_trace :
    (atlasTwelvePowerTwoCertificate.rewriteWordGL
        AlternatingSixAmbientClassBaseWord.state79.word :
      Matrix (Fin 12) (Fin 12) ℂ).trace = 0 := by
  rw [alternatingSixAmbientAtlasTwelvePowerTwo_state79_word_matrix,
    Matrix.trace_neg,
    alternatingSixAmbientAtlasTwelvePowerTwo_positiveState79_trace]
  norm_num

/-- The ATLAS power-2 trace at `ab`. -/
def alternatingSixAmbientAtlasTwelvePowerTwoAlpha : ℂ :=
  alternatingSixCyclotomicValue
    [(-1, 0), (-1, 4), (1, 16), (1, 20)]

/-- The ATLAS power-2 trace at `ab²`. -/
def alternatingSixAmbientAtlasTwelvePowerTwoBeta : ℂ :=
  alternatingSixCyclotomicValue
    [(-1, 0), (-1, 4), (1, 8), (1, 12),
      (1, 16), (-1, 28)]

/-- Values of the seven base words before multiplication by the center. -/
def alternatingSixAmbientAtlasTwelvePowerTwoBaseWordValue :
    AlternatingSixAmbientClassBaseWord → ℂ
  | .identity => 12
  | .generatorA => 0
  | .generatorB => 0
  | .generatorAB => alternatingSixAmbientAtlasTwelvePowerTwoAlpha
  | .generatorABSquared =>
      alternatingSixAmbientAtlasTwelvePowerTwoBeta
  | .state77 => 0
  | .state79 => 0

/-- Exact trace of each ATLAS power-2 base word. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_baseWord_trace
    (word : AlternatingSixAmbientClassBaseWord) :
    (atlasTwelvePowerTwoCertificate.rewriteWordGL word.word :
        Matrix (Fin 12) (Fin 12) ℂ).trace =
      alternatingSixAmbientAtlasTwelvePowerTwoBaseWordValue word := by
  cases word
  · simp [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      alternatingSixAmbientAtlasTwelvePowerTwoBaseWordValue,
      Matrix.trace]
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientAtlasTwelvePowerTwoBaseWordValue,
      atlasTwelvePowerTwoCertificate,
      alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlasTwelvePowerTwo_matrixA_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientAtlasTwelvePowerTwoBaseWordValue,
      atlasTwelvePowerTwoCertificate,
      alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlasTwelvePowerTwo_matrixB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientAtlasTwelvePowerTwoBaseWordValue,
      alternatingSixAmbientAtlasTwelvePowerTwoAlpha,
      atlasTwelvePowerTwoCertificate,
      alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlasTwelvePowerTwo_matrixAB_trace
  · simpa [AlternatingSixAmbientClassBaseWord.word,
      AlternatingSixSchurMatrixRowCertificate.rewriteWordGL,
      AlternatingSixSchurMatrixRowCertificate.rewriteLetterGL,
      alternatingSixAmbientAtlasTwelvePowerTwoBaseWordValue,
      alternatingSixAmbientAtlasTwelvePowerTwoBeta,
      pow_two, Matrix.mul_assoc,
      atlasTwelvePowerTwoCertificate,
      alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate,
      alternatingSixAmbientMatrixRowCertificate] using
        alternatingSixAmbientAtlasTwelvePowerTwo_matrixABSquared_trace
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_state77_word_trace
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_state79_word_trace

end InductiveMcKay
end McKayConjecture
