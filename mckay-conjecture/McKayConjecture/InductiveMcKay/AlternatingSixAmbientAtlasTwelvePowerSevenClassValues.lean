/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerSevenBaseWordTraces

/-!
# Class values of the ATLAS degree-12 power-seven row

Each displayed value is the exact base-word trace multiplied by the
appropriate power of the central scalar `ζ²⁰`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev atlasTwelvePowerSevenCertificate :=
  alternatingSixAmbientAtlasTwelvePowerSevenClassMatrixCertificate

/-- Exact values at the 31 checked class representatives. -/
def alternatingSixAmbientAtlasTwelvePowerSevenClassValue :
    Fin 31 → ℂ :=
  let η := alternatingSixAmbientAtlasTwelvePowerSevenEta
  let α := alternatingSixAmbientAtlasTwelvePowerSevenAlpha
  let β := alternatingSixAmbientAtlasTwelvePowerSevenBeta
  ![12, η * 12, η ^ 2 * 12, η ^ 3 * 12, η ^ 4 * 12,
    η ^ 5 * 12,
    0, 0, 0,
    0, 0, 0, 0, 0, 0,
    α, η * α, η ^ 2 * α, η ^ 3 * α, η ^ 4 * α, η ^ 5 * α,
    β, η * β, η ^ 2 * β, η ^ 3 * β, η ^ 4 * β, η ^ 5 * β,
    0, 0, 0, 0]

/-- Each displayed value is a central scalar times its base trace. -/
theorem
    alternatingSixAmbientAtlasTwelvePowerSevenClassValue_eq_central_mul_base
    (i : Fin 31) :
    alternatingSixAmbientAtlasTwelvePowerSevenClassValue i =
      alternatingSixAmbientAtlasTwelvePowerSevenEta ^
          alternatingSixAmbientClassRepresentativeCentralExponent i *
        alternatingSixAmbientAtlasTwelvePowerSevenBaseWordValue
          (alternatingSixAmbientClassRepresentativeBaseWord i) := by
  fin_cases i <;>
    simp [alternatingSixAmbientAtlasTwelvePowerSevenClassValue,
      alternatingSixAmbientClassRepresentativeCentralExponent,
      alternatingSixAmbientClassRepresentativeBaseWord,
      alternatingSixAmbientAtlasTwelvePowerSevenBaseWordValue]

/-- The trace of each checked representative is its displayed value. -/
theorem
    alternatingSixAmbientAtlasTwelvePowerSeven_classRepresentative_trace
    (i : Fin 31) :
    (atlasTwelvePowerSevenCertificate.classRepresentativeGL i :
        Matrix (Fin 12) (Fin 12) ℂ).trace =
      alternatingSixAmbientAtlasTwelvePowerSevenClassValue i := by
  rw [AlternatingSixSchurMatrixRowCertificate.classRepresentativeGL]
  change
    ((atlasTwelvePowerSevenCertificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 12) (Fin 12) ℂ) *
      ((atlasTwelvePowerSevenCertificate.relatorGL 0 :
          Matrix.GeneralLinearGroup (Fin 12) ℂ) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i :
        Matrix (Fin 12) (Fin 12) ℂ)).trace =
      _
  rw [atlasTwelvePowerSevenCertificate.relatorGL_val]
  change
    ((atlasTwelvePowerSevenCertificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 12) (Fin 12) ℂ) *
      ((alternatingSixComplexCyclotomicRoot ^ 20) •
        (1 : Matrix (Fin 12) (Fin 12) ℂ)) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i).trace =
      _
  change
    ((atlasTwelvePowerSevenCertificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 12) (Fin 12) ℂ) *
      (alternatingSixAmbientAtlasTwelvePowerSevenEta •
        (1 : Matrix (Fin 12) (Fin 12) ℂ)) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i).trace =
      _
  rw [show
    (alternatingSixAmbientAtlasTwelvePowerSevenEta •
          (1 : Matrix (Fin 12) (Fin 12) ℂ)) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i =
      alternatingSixAmbientAtlasTwelvePowerSevenEta ^
          alternatingSixAmbientClassRepresentativeCentralExponent i •
        (1 : Matrix (Fin 12) (Fin 12) ℂ) by
      rw [show
          alternatingSixAmbientAtlasTwelvePowerSevenEta •
              (1 : Matrix (Fin 12) (Fin 12) ℂ) =
            algebraMap ℂ (Matrix (Fin 12) (Fin 12) ℂ)
              alternatingSixAmbientAtlasTwelvePowerSevenEta by
            rw [Algebra.algebraMap_eq_smul_one],
        ← map_pow, Algebra.algebraMap_eq_smul_one]]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    alternatingSixAmbientAtlasTwelvePowerSeven_baseWord_trace]
  exact
    (alternatingSixAmbientAtlasTwelvePowerSevenClassValue_eq_central_mul_base
      i).symm

/-- Character value of the isolated representation on each checked class. -/
theorem
    alternatingSixAmbientAtlasTwelvePowerSeven_character_classRepresentative
    (i : Fin 31) :
    (FDRep.of
        atlasTwelvePowerSevenCertificate.universalCoverRepresentation).character
        (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative i)) =
      alternatingSixAmbientAtlasTwelvePowerSevenClassValue i := by
  rw [
    atlasTwelvePowerSevenCertificate
      |>.universalCoverRepresentation_character_classRepresentative
  ]
  exact
    alternatingSixAmbientAtlasTwelvePowerSeven_classRepresentative_trace i

end InductiveMcKay
end McKayConjecture
