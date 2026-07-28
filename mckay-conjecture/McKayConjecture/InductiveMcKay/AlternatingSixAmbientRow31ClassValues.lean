/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow31BaseWordTraces

/-!
# Character values of ambient row 31 on the 31 checked classes

Each displayed value is the exact base-word trace multiplied by the
appropriate power of the central scalar `ζ⁴⁰ = ζ²⁰ - 1`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev row31Certificate :=
  alternatingSixAmbientRow31ClassMatrixCertificate

/-- The exact row-31 character values at the checked representatives. -/
def alternatingSixAmbientRow31ClassValue : Fin 31 → ℂ :=
  let η := alternatingSixAmbientRow31Eta
  let central := η - 1
  ![15, central * 15, central ^ 2 * 15, central ^ 3 * 15,
    central ^ 4 * 15, central ^ 5 * 15,
    η, central * η, central ^ 2 * η,
    -1, central * (-1), central ^ 2 * (-1),
    central ^ 3 * (-1), central ^ 4 * (-1),
    central ^ 5 * (-1),
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0]

/-- The displayed value is central scalar times the selected base trace. -/
theorem alternatingSixAmbientRow31ClassValue_eq_central_mul_base
    (i : Fin 31) :
    alternatingSixAmbientRow31ClassValue i =
      (alternatingSixAmbientRow31Eta - 1) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i *
        alternatingSixAmbientRow31BaseWordValue
          (alternatingSixAmbientClassRepresentativeBaseWord i) := by
  fin_cases i <;>
    simp [alternatingSixAmbientRow31ClassValue,
      alternatingSixAmbientClassRepresentativeCentralExponent,
      alternatingSixAmbientClassRepresentativeBaseWord,
      alternatingSixAmbientRow31BaseWordValue]

/-- The trace of each checked representative is its exact row-31 value. -/
theorem alternatingSixAmbientRow31_classRepresentative_trace
    (i : Fin 31) :
    (row31Certificate.classRepresentativeGL i :
        Matrix (Fin 15) (Fin 15) ℂ).trace =
      alternatingSixAmbientRow31ClassValue i := by
  rw [AlternatingSixSchurMatrixRowCertificate.classRepresentativeGL]
  change
    ((row31Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 15) (Fin 15) ℂ) *
      ((row31Certificate.relatorGL 0 :
          Matrix.GeneralLinearGroup (Fin 15) ℂ) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i :
        Matrix (Fin 15) (Fin 15) ℂ)).trace =
      _
  rw [row31Certificate.relatorGL_val]
  change
    ((row31Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 15) (Fin 15) ℂ) *
      ((alternatingSixComplexCyclotomicRoot ^ 40) •
        (1 : Matrix (Fin 15) (Fin 15) ℂ)) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i).trace =
      _
  rw [alternatingSixAmbientRow31_root_pow_forty]
  change
    ((row31Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 15) (Fin 15) ℂ) *
      ((alternatingSixAmbientRow31Eta - 1) •
        (1 : Matrix (Fin 15) (Fin 15) ℂ)) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i).trace =
      _
  rw [show
    ((alternatingSixAmbientRow31Eta - 1) •
          (1 : Matrix (Fin 15) (Fin 15) ℂ)) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i =
      ((alternatingSixAmbientRow31Eta - 1) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i) •
        (1 : Matrix (Fin 15) (Fin 15) ℂ) by
      rw [show
          ((alternatingSixAmbientRow31Eta - 1) •
              (1 : Matrix (Fin 15) (Fin 15) ℂ)) =
            algebraMap ℂ (Matrix (Fin 15) (Fin 15) ℂ)
              (alternatingSixAmbientRow31Eta - 1) by
            rw [Algebra.algebraMap_eq_smul_one],
        ← map_pow, Algebra.algebraMap_eq_smul_one]]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    alternatingSixAmbientRow31_baseWord_trace]
  exact
    (alternatingSixAmbientRow31ClassValue_eq_central_mul_base i).symm

/-- Character value of the isolated row-31 representation at each checked
class representative. -/
theorem alternatingSixAmbientRow31_character_classRepresentative
    (i : Fin 31) :
    (FDRep.of row31Certificate.universalCoverRepresentation).character
        (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative i)) =
      alternatingSixAmbientRow31ClassValue i := by
  rw [
    row31Certificate.universalCoverRepresentation_character_classRepresentative
  ]
  exact alternatingSixAmbientRow31_classRepresentative_trace i

end InductiveMcKay
end McKayConjecture
