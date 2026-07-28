/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow22BaseWordTraces

/-!
# Character values of ambient row 22 on the 31 checked classes

Each displayed value is the exact base-word trace multiplied by the
appropriate power of the central scalar `ζ⁴⁰ = ζ²⁰ - 1`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev row22Certificate :=
  alternatingSixAmbientRow22ClassMatrixCertificate

/-- The exact row-22 character values at the checked representatives. -/
def alternatingSixAmbientRow22ClassValue : Fin 31 → ℂ :=
  let η := alternatingSixAmbientRow22Eta
  let central := η - 1
  ![9, central * 9, central ^ 2 * 9, central ^ 3 * 9,
    central ^ 4 * 9, central ^ 5 * 9,
    -η, central * (-η), central ^ 2 * (-η),
    1, central, central ^ 2, central ^ 3, central ^ 4, central ^ 5,
    1 - η, central * (1 - η), central ^ 2 * (1 - η),
    central ^ 3 * (1 - η), central ^ 4 * (1 - η),
    central ^ 5 * (1 - η),
    η, central * η, central ^ 2 * η, central ^ 3 * η,
    central ^ 4 * η, central ^ 5 * η,
    0, 0, 0, 0]

/-- The displayed value is central scalar times the selected base trace. -/
theorem alternatingSixAmbientRow22ClassValue_eq_central_mul_base
    (i : Fin 31) :
    alternatingSixAmbientRow22ClassValue i =
      (alternatingSixAmbientRow22Eta - 1) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i *
        alternatingSixAmbientRow22BaseWordValue
          (alternatingSixAmbientClassRepresentativeBaseWord i) := by
  fin_cases i <;>
    simp [alternatingSixAmbientRow22ClassValue,
      alternatingSixAmbientClassRepresentativeCentralExponent,
      alternatingSixAmbientClassRepresentativeBaseWord,
      alternatingSixAmbientRow22BaseWordValue]

/-- The trace of each checked representative is its exact row-22 value. -/
theorem alternatingSixAmbientRow22_classRepresentative_trace
    (i : Fin 31) :
    (row22Certificate.classRepresentativeGL i :
        Matrix (Fin 9) (Fin 9) ℂ).trace =
      alternatingSixAmbientRow22ClassValue i := by
  rw [AlternatingSixSchurMatrixRowCertificate.classRepresentativeGL]
  change
    ((row22Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 9) (Fin 9) ℂ) *
      ((row22Certificate.relatorGL 0 :
          Matrix.GeneralLinearGroup (Fin 9) ℂ) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i :
        Matrix (Fin 9) (Fin 9) ℂ)).trace =
      _
  rw [row22Certificate.relatorGL_val]
  change
    ((row22Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 9) (Fin 9) ℂ) *
      ((alternatingSixComplexCyclotomicRoot ^ 40) •
        (1 : Matrix (Fin 9) (Fin 9) ℂ)) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i).trace =
      _
  rw [alternatingSixAmbientRow22_root_pow_forty]
  change
    ((row22Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 9) (Fin 9) ℂ) *
      ((alternatingSixAmbientRow22Eta - 1) •
        (1 : Matrix (Fin 9) (Fin 9) ℂ)) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i).trace =
      _
  rw [show
    ((alternatingSixAmbientRow22Eta - 1) •
          (1 : Matrix (Fin 9) (Fin 9) ℂ)) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i =
      ((alternatingSixAmbientRow22Eta - 1) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i) •
        (1 : Matrix (Fin 9) (Fin 9) ℂ) by
      rw [show
          ((alternatingSixAmbientRow22Eta - 1) •
              (1 : Matrix (Fin 9) (Fin 9) ℂ)) =
            algebraMap ℂ (Matrix (Fin 9) (Fin 9) ℂ)
              (alternatingSixAmbientRow22Eta - 1) by
            rw [Algebra.algebraMap_eq_smul_one],
        ← map_pow, Algebra.algebraMap_eq_smul_one]]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    alternatingSixAmbientRow22_baseWord_trace]
  exact
    (alternatingSixAmbientRow22ClassValue_eq_central_mul_base i).symm

/-- Character value of the isolated row-22 representation at each checked
class representative. -/
theorem alternatingSixAmbientRow22_character_classRepresentative
    (i : Fin 31) :
    (FDRep.of row22Certificate.universalCoverRepresentation).character
        (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative i)) =
      alternatingSixAmbientRow22ClassValue i := by
  rw [
    row22Certificate.universalCoverRepresentation_character_classRepresentative
  ]
  exact alternatingSixAmbientRow22_classRepresentative_trace i

end InductiveMcKay
end McKayConjecture
