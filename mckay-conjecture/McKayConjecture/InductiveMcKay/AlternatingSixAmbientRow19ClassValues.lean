/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow19BaseWordTraces

/-!
# Character values of ambient row 19 on the 31 checked classes

The table below is obtained from the seven base-word traces by multiplying
with the alternating sign of the first central relator.  The proof keeps the
compact central/base-word formula as an intermediate theorem and then checks
the displayed 31-entry table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev row19Certificate :=
  alternatingSixAmbientRow19ClassMatrixCertificate

/-- The explicit row-19 character values at the checked representatives. -/
def alternatingSixAmbientRow19ClassValue : Fin 31 → ℂ :=
  ![8, -8, 8, -8, 8, -8,
    0, 0, 0, 0, 0, 0, 0, 0, 0,
    alternatingSixAmbientRow19Alpha,
    -alternatingSixAmbientRow19Alpha,
    alternatingSixAmbientRow19Alpha,
    -alternatingSixAmbientRow19Alpha,
    alternatingSixAmbientRow19Alpha,
    -alternatingSixAmbientRow19Alpha,
    alternatingSixAmbientRow19Beta,
    -alternatingSixAmbientRow19Beta,
    alternatingSixAmbientRow19Beta,
    -alternatingSixAmbientRow19Beta,
    alternatingSixAmbientRow19Beta,
    -alternatingSixAmbientRow19Beta,
    1, -1, 1, -1]

/-- The displayed value is central sign times the selected base-word value. -/
theorem alternatingSixAmbientRow19ClassValue_eq_central_mul_base
    (i : Fin 31) :
    alternatingSixAmbientRow19ClassValue i =
      (-1 : ℂ) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i *
        alternatingSixAmbientRow19BaseWordValue
          (alternatingSixAmbientClassRepresentativeBaseWord i) := by
  fin_cases i <;>
    simp [alternatingSixAmbientRow19ClassValue,
      alternatingSixAmbientClassRepresentativeCentralExponent,
      alternatingSixAmbientClassRepresentativeBaseWord,
      alternatingSixAmbientRow19BaseWordValue] <;>
    norm_num

/-- The trace of each checked representative is its displayed row-19 value. -/
theorem alternatingSixAmbientRow19_classRepresentative_trace
    (i : Fin 31) :
    (row19Certificate.classRepresentativeGL i :
        Matrix (Fin 8) (Fin 8) ℂ).trace =
      alternatingSixAmbientRow19ClassValue i := by
  rw [AlternatingSixSchurMatrixRowCertificate.classRepresentativeGL,
    alternatingSixAmbientRow19_relatorGL_eq_negOne]
  change
    ((row19Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 8) (Fin 8) ℂ) *
      ((-1 : Matrix (Fin 8) (Fin 8) ℂ) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i)).trace =
      _
  rw [show
    ((-1 : Matrix (Fin 8) (Fin 8) ℂ) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i) =
      ((-1 : ℂ) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i) •
        (1 : Matrix (Fin 8) (Fin 8) ℂ) by
      rw [show
          (-1 : Matrix (Fin 8) (Fin 8) ℂ) =
            algebraMap ℂ (Matrix (Fin 8) (Fin 8) ℂ) (-1) by
            simp,
        ← map_pow, Algebra.algebraMap_eq_smul_one]]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    alternatingSixAmbientRow19_baseWord_trace]
  exact
    (alternatingSixAmbientRow19ClassValue_eq_central_mul_base i).symm

/-- Character value of the isolated row-19 representation at each checked
class representative. -/
theorem alternatingSixAmbientRow19_character_classRepresentative
    (i : Fin 31) :
    (FDRep.of row19Certificate.universalCoverRepresentation).character
        (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative i)) =
      alternatingSixAmbientRow19ClassValue i := by
  rw [
    row19Certificate.universalCoverRepresentation_character_classRepresentative
  ]
  exact alternatingSixAmbientRow19_classRepresentative_trace i

end InductiveMcKay
end McKayConjecture
