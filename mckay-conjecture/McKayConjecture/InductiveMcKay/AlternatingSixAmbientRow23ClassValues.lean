/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow23BaseWordTraces

/-!
# Character values of ambient row 23 on the 31 checked classes

All four central relators act trivially in row 23. Its class-value table is
therefore obtained by repeating the seven base-word values according to the
checked representative table, with no additional central scalar.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev row23Certificate :=
  alternatingSixAmbientRow23ClassMatrixCertificate

/-- The exact row-23 character values at the checked representatives. -/
def alternatingSixAmbientRow23ClassValue : Fin 31 → ℂ :=
  ![10, 10, 10, 10, 10, 10,
    -2, -2, -2,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    1, 1, 1, 1]

/-- The displayed value is the selected base-word value; the central scalar
is one. -/
theorem alternatingSixAmbientRow23ClassValue_eq_central_mul_base
    (i : Fin 31) :
    alternatingSixAmbientRow23ClassValue i =
      (1 : ℂ) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i *
        alternatingSixAmbientRow23BaseWordValue
          (alternatingSixAmbientClassRepresentativeBaseWord i) := by
  fin_cases i <;>
    simp [alternatingSixAmbientRow23ClassValue,
      alternatingSixAmbientClassRepresentativeCentralExponent,
      alternatingSixAmbientClassRepresentativeBaseWord,
      alternatingSixAmbientRow23BaseWordValue]

/-- The trace of each checked representative is its exact row-23 value. -/
theorem alternatingSixAmbientRow23_classRepresentative_trace
    (i : Fin 31) :
    (row23Certificate.classRepresentativeGL i :
        Matrix (Fin 10) (Fin 10) ℂ).trace =
      alternatingSixAmbientRow23ClassValue i := by
  rw [AlternatingSixSchurMatrixRowCertificate.classRepresentativeGL,
    alternatingSixAmbientRow23_relatorGL_eq_one]
  change
    ((row23Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 10) (Fin 10) ℂ) *
      ((1 : Matrix (Fin 10) (Fin 10) ℂ) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i)).trace =
      _
  rw [one_pow, Matrix.mul_one,
    alternatingSixAmbientRow23_baseWord_trace,
    alternatingSixAmbientRow23ClassValue_eq_central_mul_base]
  simp

/-- Character value of the isolated row-23 representation at each checked
class representative. -/
theorem alternatingSixAmbientRow23_character_classRepresentative
    (i : Fin 31) :
    (FDRep.of row23Certificate.universalCoverRepresentation).character
        (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative i)) =
      alternatingSixAmbientRow23ClassValue i := by
  rw [
    row23Certificate.universalCoverRepresentation_character_classRepresentative
  ]
  exact alternatingSixAmbientRow23_classRepresentative_trace i

end InductiveMcKay
end McKayConjecture
