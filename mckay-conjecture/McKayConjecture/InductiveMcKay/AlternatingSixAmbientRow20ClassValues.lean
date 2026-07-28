/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow20BaseWordTraces

/-!
# Character values of ambient row 20 on the 31 checked classes

All four central relators act trivially in row 20. Its class-value table is
therefore obtained by repeating the seven base-word values according to the
checked representative table, with no additional central scalar.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev row20Certificate :=
  alternatingSixAmbientRow20ClassMatrixCertificate

/-- The explicit row-20 character values at the checked representatives. -/
def alternatingSixAmbientRow20ClassValue : Fin 31 → ℂ :=
  ![9, 9, 9, 9, 9, 9,
    1, 1, 1, 1, 1, 1, 1, 1, 1,
    -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1,
    0, 0, 0, 0]

/-- The displayed value is the selected base-word value; the central scalar
is one. -/
theorem alternatingSixAmbientRow20ClassValue_eq_central_mul_base
    (i : Fin 31) :
    alternatingSixAmbientRow20ClassValue i =
      (1 : ℂ) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i *
        alternatingSixAmbientRow20BaseWordValue
          (alternatingSixAmbientClassRepresentativeBaseWord i) := by
  fin_cases i <;>
    simp [alternatingSixAmbientRow20ClassValue,
      alternatingSixAmbientClassRepresentativeCentralExponent,
      alternatingSixAmbientClassRepresentativeBaseWord,
      alternatingSixAmbientRow20BaseWordValue]

/-- The trace of each checked representative is its displayed row-20 value. -/
theorem alternatingSixAmbientRow20_classRepresentative_trace
    (i : Fin 31) :
    (row20Certificate.classRepresentativeGL i :
        Matrix (Fin 9) (Fin 9) ℂ).trace =
      alternatingSixAmbientRow20ClassValue i := by
  rw [AlternatingSixSchurMatrixRowCertificate.classRepresentativeGL,
    alternatingSixAmbientRow20_relatorGL_eq_one]
  change
    ((row20Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 9) (Fin 9) ℂ) *
      ((1 : Matrix (Fin 9) (Fin 9) ℂ) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i)).trace =
      _
  rw [one_pow, Matrix.mul_one,
    alternatingSixAmbientRow20_baseWord_trace,
    alternatingSixAmbientRow20ClassValue_eq_central_mul_base]
  simp

/-- Character value of the isolated row-20 representation at each checked
class representative. -/
theorem alternatingSixAmbientRow20_character_classRepresentative
    (i : Fin 31) :
    (FDRep.of row20Certificate.universalCoverRepresentation).character
        (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative i)) =
      alternatingSixAmbientRow20ClassValue i := by
  rw [
    row20Certificate.universalCoverRepresentation_character_classRepresentative
  ]
  exact alternatingSixAmbientRow20_classRepresentative_trace i

end InductiveMcKay
end McKayConjecture
