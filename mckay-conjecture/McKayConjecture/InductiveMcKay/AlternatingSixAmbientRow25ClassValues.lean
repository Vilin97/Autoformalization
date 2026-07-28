/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow25BaseWordTraces

/-!
# Character values of ambient row 25 on the 31 checked classes

The table below is obtained from the seven base-word traces by multiplying
with the alternating sign of the first central relator. The proof keeps the
compact central/base-word formula as an intermediate theorem and then checks
the displayed 31-entry table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev row25Certificate :=
  alternatingSixAmbientRow25ClassMatrixCertificate

/-- The explicit row-25 character values at the checked representatives. -/
def alternatingSixAmbientRow25ClassValue : Fin 31 → ℂ :=
  ![10, -10, 10, -10, 10, -10,
    0, 0, 0,
    alternatingSixAmbientRow25Gamma,
    -alternatingSixAmbientRow25Gamma,
    alternatingSixAmbientRow25Gamma,
    -alternatingSixAmbientRow25Gamma,
    alternatingSixAmbientRow25Gamma,
    -alternatingSixAmbientRow25Gamma,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    -1, 1, -1, 1]

/-- The displayed value is central sign times the selected base-word value. -/
theorem alternatingSixAmbientRow25ClassValue_eq_central_mul_base
    (i : Fin 31) :
    alternatingSixAmbientRow25ClassValue i =
      (-1 : ℂ) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i *
        alternatingSixAmbientRow25BaseWordValue
          (alternatingSixAmbientClassRepresentativeBaseWord i) := by
  fin_cases i <;>
    simp [alternatingSixAmbientRow25ClassValue,
      alternatingSixAmbientClassRepresentativeCentralExponent,
      alternatingSixAmbientClassRepresentativeBaseWord,
      alternatingSixAmbientRow25BaseWordValue] <;>
    norm_num

/-- The trace of each checked representative is its displayed row-25 value. -/
theorem alternatingSixAmbientRow25_classRepresentative_trace
    (i : Fin 31) :
    (row25Certificate.classRepresentativeGL i :
        Matrix (Fin 10) (Fin 10) ℂ).trace =
      alternatingSixAmbientRow25ClassValue i := by
  rw [AlternatingSixSchurMatrixRowCertificate.classRepresentativeGL,
    alternatingSixAmbientRow25_relatorGL_eq_negOne]
  change
    ((row25Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 10) (Fin 10) ℂ) *
      ((-1 : Matrix (Fin 10) (Fin 10) ℂ) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i)).trace =
      _
  rw [show
    ((-1 : Matrix (Fin 10) (Fin 10) ℂ) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i) =
      ((-1 : ℂ) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i) •
        (1 : Matrix (Fin 10) (Fin 10) ℂ) by
      rw [show
          (-1 : Matrix (Fin 10) (Fin 10) ℂ) =
            algebraMap ℂ (Matrix (Fin 10) (Fin 10) ℂ) (-1) by
            simp,
        ← map_pow, Algebra.algebraMap_eq_smul_one]]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    alternatingSixAmbientRow25_baseWord_trace]
  exact
    (alternatingSixAmbientRow25ClassValue_eq_central_mul_base i).symm

/-- Character value of the isolated row-25 representation at each checked
class representative. -/
theorem alternatingSixAmbientRow25_character_classRepresentative
    (i : Fin 31) :
    (FDRep.of row25Certificate.universalCoverRepresentation).character
        (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative i)) =
      alternatingSixAmbientRow25ClassValue i := by
  rw [
    row25Certificate.universalCoverRepresentation_character_classRepresentative
  ]
  exact alternatingSixAmbientRow25_classRepresentative_trace i

end InductiveMcKay
end McKayConjecture
