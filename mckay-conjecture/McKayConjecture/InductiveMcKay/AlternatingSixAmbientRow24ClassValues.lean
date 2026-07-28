/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow24BaseWordTraces

/-!
# Character values of ambient row 24 on the 31 checked classes

The table below is obtained from the seven base-word traces by multiplying
with the alternating sign of the first central relator. The proof keeps the
compact central/base-word formula as an intermediate theorem and then checks
the displayed 31-entry table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev row24Certificate :=
  alternatingSixAmbientRow24ClassMatrixCertificate

/-- The explicit row-24 character values at the checked representatives. -/
def alternatingSixAmbientRow24ClassValue : Fin 31 → ℂ :=
  ![10, -10, 10, -10, 10, -10,
    0, 0, 0,
    alternatingSixAmbientRow24Gamma,
    -alternatingSixAmbientRow24Gamma,
    alternatingSixAmbientRow24Gamma,
    -alternatingSixAmbientRow24Gamma,
    alternatingSixAmbientRow24Gamma,
    -alternatingSixAmbientRow24Gamma,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    -1, 1, -1, 1]

/-- The displayed value is central sign times the selected base-word value. -/
theorem alternatingSixAmbientRow24ClassValue_eq_central_mul_base
    (i : Fin 31) :
    alternatingSixAmbientRow24ClassValue i =
      (-1 : ℂ) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i *
        alternatingSixAmbientRow24BaseWordValue
          (alternatingSixAmbientClassRepresentativeBaseWord i) := by
  fin_cases i <;>
    simp [alternatingSixAmbientRow24ClassValue,
      alternatingSixAmbientClassRepresentativeCentralExponent,
      alternatingSixAmbientClassRepresentativeBaseWord,
      alternatingSixAmbientRow24BaseWordValue] <;>
    norm_num

/-- The trace of each checked representative is its displayed row-24 value. -/
theorem alternatingSixAmbientRow24_classRepresentative_trace
    (i : Fin 31) :
    (row24Certificate.classRepresentativeGL i :
        Matrix (Fin 10) (Fin 10) ℂ).trace =
      alternatingSixAmbientRow24ClassValue i := by
  rw [AlternatingSixSchurMatrixRowCertificate.classRepresentativeGL,
    alternatingSixAmbientRow24_relatorGL_eq_negOne]
  change
    ((row24Certificate.rewriteWordGL
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
    alternatingSixAmbientRow24_baseWord_trace]
  exact
    (alternatingSixAmbientRow24ClassValue_eq_central_mul_base i).symm

/-- Character value of the isolated row-24 representation at each checked
class representative. -/
theorem alternatingSixAmbientRow24_character_classRepresentative
    (i : Fin 31) :
    (FDRep.of row24Certificate.universalCoverRepresentation).character
        (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative i)) =
      alternatingSixAmbientRow24ClassValue i := by
  rw [
    row24Certificate.universalCoverRepresentation_character_classRepresentative
  ]
  exact alternatingSixAmbientRow24_classRepresentative_trace i

end InductiveMcKay
end McKayConjecture
