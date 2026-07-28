/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerTwoBaseWordTraces

/-!
# Character values of the ATLAS degree-twelve power-2 row

Each displayed value is the exact base-word trace multiplied by the
appropriate power of the central scalar `ζ¹⁰⁰ = 1 - ζ²⁰`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev atlasTwelvePowerTwoCertificate :=
  alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate

/-- Exact ATLAS power-2 values at the checked representatives. -/
def alternatingSixAmbientAtlasTwelvePowerTwoClassValue :
    Fin 31 → ℂ :=
  let central := alternatingSixAmbientAtlasTwelvePowerTwoCentral
  let α := alternatingSixAmbientAtlasTwelvePowerTwoAlpha
  let β := alternatingSixAmbientAtlasTwelvePowerTwoBeta
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
theorem
    alternatingSixAmbientAtlasTwelvePowerTwoClassValue_eq_central_mul_base
    (i : Fin 31) :
    alternatingSixAmbientAtlasTwelvePowerTwoClassValue i =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^
          alternatingSixAmbientClassRepresentativeCentralExponent i *
        alternatingSixAmbientAtlasTwelvePowerTwoBaseWordValue
          (alternatingSixAmbientClassRepresentativeBaseWord i) := by
  fin_cases i <;>
    simp [alternatingSixAmbientAtlasTwelvePowerTwoClassValue,
      alternatingSixAmbientClassRepresentativeCentralExponent,
      alternatingSixAmbientClassRepresentativeBaseWord,
      alternatingSixAmbientAtlasTwelvePowerTwoBaseWordValue]

/-- The trace of each checked representative is its exact power-2 value. -/
theorem
    alternatingSixAmbientAtlasTwelvePowerTwo_classRepresentative_trace
    (i : Fin 31) :
    (atlasTwelvePowerTwoCertificate.classRepresentativeGL i :
        Matrix (Fin 12) (Fin 12) ℂ).trace =
      alternatingSixAmbientAtlasTwelvePowerTwoClassValue i := by
  rw [AlternatingSixSchurMatrixRowCertificate.classRepresentativeGL]
  change
    ((atlasTwelvePowerTwoCertificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 12) (Fin 12) ℂ) *
      ((atlasTwelvePowerTwoCertificate.relatorGL 0 :
          Matrix.GeneralLinearGroup (Fin 12) ℂ) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i :
        Matrix (Fin 12) (Fin 12) ℂ)).trace =
      _
  rw [atlasTwelvePowerTwoCertificate.relatorGL_val]
  change
    ((atlasTwelvePowerTwoCertificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 12) (Fin 12) ℂ) *
      ((alternatingSixComplexCyclotomicRoot ^ 100) •
        (1 : Matrix (Fin 12) (Fin 12) ℂ)) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i).trace =
      _
  rw [alternatingSixAmbientAtlasTwelvePowerTwo_root_pow_hundred]
  rw [show
    (alternatingSixAmbientAtlasTwelvePowerTwoCentral •
          (1 : Matrix (Fin 12) (Fin 12) ℂ)) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i =
      (alternatingSixAmbientAtlasTwelvePowerTwoCentral ^
          alternatingSixAmbientClassRepresentativeCentralExponent i) •
        (1 : Matrix (Fin 12) (Fin 12) ℂ) by
      rw [show
          (alternatingSixAmbientAtlasTwelvePowerTwoCentral •
              (1 : Matrix (Fin 12) (Fin 12) ℂ)) =
            algebraMap ℂ (Matrix (Fin 12) (Fin 12) ℂ)
              alternatingSixAmbientAtlasTwelvePowerTwoCentral by
            rw [Algebra.algebraMap_eq_smul_one],
        ← map_pow, Algebra.algebraMap_eq_smul_one]]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    alternatingSixAmbientAtlasTwelvePowerTwo_baseWord_trace]
  exact
    (alternatingSixAmbientAtlasTwelvePowerTwoClassValue_eq_central_mul_base i)
      |>.symm

/-- Character value at each checked representative. -/
theorem
    alternatingSixAmbientAtlasTwelvePowerTwo_character_classRepresentative
    (i : Fin 31) :
    (FDRep.of
        atlasTwelvePowerTwoCertificate.universalCoverRepresentation).character
        (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative i)) =
      alternatingSixAmbientAtlasTwelvePowerTwoClassValue i := by
  rw [
    atlasTwelvePowerTwoCertificate
      |>.universalCoverRepresentation_character_classRepresentative
  ]
  exact
    alternatingSixAmbientAtlasTwelvePowerTwo_classRepresentative_trace i

end InductiveMcKay
end McKayConjecture
