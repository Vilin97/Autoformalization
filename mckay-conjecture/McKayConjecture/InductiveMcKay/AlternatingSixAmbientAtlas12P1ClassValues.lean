/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P1BaseWordTraces

/-!
# Character values for ATLAS degree 12, power 1

Each displayed value is the appropriate base-word trace multiplied by a
power of the central scalar `η = ζ²⁰`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev atlas12P1Certificate :=
  alternatingSixAmbientAtlas12P1ClassMatrixCertificate

/-- Exact character values at the thirty-one checked representatives. -/
def alternatingSixAmbientAtlas12P1ClassValue : Fin 31 → ℂ :=
  let η := alternatingSixAmbientAtlas12P1Eta
  let α := alternatingSixAmbientAtlas12P1Alpha
  let β := alternatingSixAmbientAtlas12P1Beta
  ![12, η * 12, η ^ 2 * 12, η ^ 3 * 12,
    η ^ 4 * 12, η ^ 5 * 12,
    0, 0, 0,
    0, 0, 0, 0, 0, 0,
    α, η * α, η ^ 2 * α, η ^ 3 * α,
    η ^ 4 * α, η ^ 5 * α,
    β, η * β, η ^ 2 * β, η ^ 3 * β,
    η ^ 4 * β, η ^ 5 * β,
    0, 0, 0, 0]

/-- The displayed value is central scalar times the selected base trace. -/
theorem alternatingSixAmbientAtlas12P1ClassValue_eq_central_mul_base
    (i : Fin 31) :
    alternatingSixAmbientAtlas12P1ClassValue i =
      alternatingSixAmbientAtlas12P1Eta ^
          alternatingSixAmbientClassRepresentativeCentralExponent i *
        alternatingSixAmbientAtlas12P1BaseWordValue
          (alternatingSixAmbientClassRepresentativeBaseWord i) := by
  fin_cases i <;>
    simp [alternatingSixAmbientAtlas12P1ClassValue,
      alternatingSixAmbientClassRepresentativeCentralExponent,
      alternatingSixAmbientClassRepresentativeBaseWord,
      alternatingSixAmbientAtlas12P1BaseWordValue]

/-- Each checked representative has its displayed power-one trace. -/
theorem alternatingSixAmbientAtlas12P1_classRepresentative_trace
    (i : Fin 31) :
    (atlas12P1Certificate.classRepresentativeGL i :
        Matrix (Fin 12) (Fin 12) ℂ).trace =
      alternatingSixAmbientAtlas12P1ClassValue i := by
  rw [AlternatingSixSchurMatrixRowCertificate.classRepresentativeGL]
  change
    ((atlas12P1Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 12) (Fin 12) ℂ) *
      ((atlas12P1Certificate.relatorGL 0 :
          Matrix.GeneralLinearGroup (Fin 12) ℂ) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i :
        Matrix (Fin 12) (Fin 12) ℂ)).trace =
      _
  rw [atlas12P1Certificate.relatorGL_val]
  change
    ((atlas12P1Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 12) (Fin 12) ℂ) *
      ((alternatingSixAmbientAtlas12P1Eta) •
        (1 : Matrix (Fin 12) (Fin 12) ℂ)) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i).trace =
      _
  rw [show
    ((alternatingSixAmbientAtlas12P1Eta) •
          (1 : Matrix (Fin 12) (Fin 12) ℂ)) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i =
      (alternatingSixAmbientAtlas12P1Eta ^
          alternatingSixAmbientClassRepresentativeCentralExponent i) •
        (1 : Matrix (Fin 12) (Fin 12) ℂ) by
      rw [show
          ((alternatingSixAmbientAtlas12P1Eta) •
              (1 : Matrix (Fin 12) (Fin 12) ℂ)) =
            algebraMap ℂ (Matrix (Fin 12) (Fin 12) ℂ)
              alternatingSixAmbientAtlas12P1Eta by
            rw [Algebra.algebraMap_eq_smul_one],
        ← map_pow, Algebra.algebraMap_eq_smul_one]]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    alternatingSixAmbientAtlas12P1_baseWord_trace]
  exact
    (alternatingSixAmbientAtlas12P1ClassValue_eq_central_mul_base i).symm

/-- Character value of the isolated power-one representation. -/
theorem alternatingSixAmbientAtlas12P1_character_classRepresentative
    (i : Fin 31) :
    (FDRep.of atlas12P1Certificate.universalCoverRepresentation).character
        (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative i)) =
      alternatingSixAmbientAtlas12P1ClassValue i := by
  rw [
    atlas12P1Certificate
      |>.universalCoverRepresentation_character_classRepresentative
  ]
  exact alternatingSixAmbientAtlas12P1_classRepresentative_trace i

end InductiveMcKay
end McKayConjecture
