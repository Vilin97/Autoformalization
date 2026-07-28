/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P11BaseWordTraces

/-!
# Character values for ATLAS degree 12, power 11

Each displayed value is the appropriate base-word trace multiplied by a
power of the central scalar `ζ¹⁰⁰ = 1 - ζ²⁰`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev atlas12P11Certificate :=
  alternatingSixAmbientAtlas12P11ClassMatrixCertificate

/-- Exact character values at the thirty-one checked representatives. -/
def alternatingSixAmbientAtlas12P11ClassValue : Fin 31 → ℂ :=
  let central := alternatingSixAmbientAtlas12P11Central
  let α := alternatingSixAmbientAtlas12P11Alpha
  let β := alternatingSixAmbientAtlas12P11Beta
  ![12, central * 12, central ^ 2 * 12, central ^ 3 * 12,
    central ^ 4 * 12, central ^ 5 * 12,
    0, 0, 0,
    0, 0, 0, 0, 0, 0,
    α, central * α, central ^ 2 * α, central ^ 3 * α,
    central ^ 4 * α, central ^ 5 * α,
    β, central * β, central ^ 2 * β, central ^ 3 * β,
    central ^ 4 * β, central ^ 5 * β,
    0, 0, 0, 0]

/-- The displayed value is central scalar times the selected base trace. -/
theorem alternatingSixAmbientAtlas12P11ClassValue_eq_central_mul_base
    (i : Fin 31) :
    alternatingSixAmbientAtlas12P11ClassValue i =
      alternatingSixAmbientAtlas12P11Central ^
          alternatingSixAmbientClassRepresentativeCentralExponent i *
        alternatingSixAmbientAtlas12P11BaseWordValue
          (alternatingSixAmbientClassRepresentativeBaseWord i) := by
  fin_cases i <;>
    simp [alternatingSixAmbientAtlas12P11ClassValue,
      alternatingSixAmbientClassRepresentativeCentralExponent,
      alternatingSixAmbientClassRepresentativeBaseWord,
      alternatingSixAmbientAtlas12P11BaseWordValue]

/-- Each checked representative has its displayed power-eleven trace. -/
theorem alternatingSixAmbientAtlas12P11_classRepresentative_trace
    (i : Fin 31) :
    (atlas12P11Certificate.classRepresentativeGL i :
        Matrix (Fin 12) (Fin 12) ℂ).trace =
      alternatingSixAmbientAtlas12P11ClassValue i := by
  rw [AlternatingSixSchurMatrixRowCertificate.classRepresentativeGL]
  change
    ((atlas12P11Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 12) (Fin 12) ℂ) *
      ((atlas12P11Certificate.relatorGL 0 :
          Matrix.GeneralLinearGroup (Fin 12) ℂ) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i :
        Matrix (Fin 12) (Fin 12) ℂ)).trace =
      _
  rw [atlas12P11Certificate.relatorGL_val]
  change
    ((atlas12P11Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 12) (Fin 12) ℂ) *
      ((alternatingSixComplexCyclotomicRoot ^ 100) •
        (1 : Matrix (Fin 12) (Fin 12) ℂ)) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i).trace =
      _
  rw [alternatingSixAmbientAtlas12P11_root_pow_hundred]
  change
    ((atlas12P11Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 12) (Fin 12) ℂ) *
      (alternatingSixAmbientAtlas12P11Central •
        (1 : Matrix (Fin 12) (Fin 12) ℂ)) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i).trace =
      _
  rw [show
    (alternatingSixAmbientAtlas12P11Central •
          (1 : Matrix (Fin 12) (Fin 12) ℂ)) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i =
      (alternatingSixAmbientAtlas12P11Central ^
          alternatingSixAmbientClassRepresentativeCentralExponent i) •
        (1 : Matrix (Fin 12) (Fin 12) ℂ) by
      rw [show
          (alternatingSixAmbientAtlas12P11Central •
              (1 : Matrix (Fin 12) (Fin 12) ℂ)) =
            algebraMap ℂ (Matrix (Fin 12) (Fin 12) ℂ)
              alternatingSixAmbientAtlas12P11Central by
            rw [Algebra.algebraMap_eq_smul_one],
        ← map_pow, Algebra.algebraMap_eq_smul_one]]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    alternatingSixAmbientAtlas12P11_baseWord_trace]
  exact
    (alternatingSixAmbientAtlas12P11ClassValue_eq_central_mul_base i).symm

/-- Character value of the isolated power-eleven representation. -/
theorem alternatingSixAmbientAtlas12P11_character_classRepresentative
    (i : Fin 31) :
    (FDRep.of atlas12P11Certificate.universalCoverRepresentation).character
        (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative i)) =
      alternatingSixAmbientAtlas12P11ClassValue i := by
  rw [
    atlas12P11Certificate
      |>.universalCoverRepresentation_character_classRepresentative
  ]
  exact alternatingSixAmbientAtlas12P11_classRepresentative_trace i

end InductiveMcKay
end McKayConjecture
