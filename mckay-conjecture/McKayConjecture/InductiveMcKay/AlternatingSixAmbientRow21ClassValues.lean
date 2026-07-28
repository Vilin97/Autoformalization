/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow21BaseWordTraces

/-!
# Character values of ambient row 21 on the 31 checked classes

Each displayed value is the exact base-word trace multiplied by the
appropriate power of the central scalar `ζ⁸⁰ = -ζ²⁰`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev row21Certificate :=
  alternatingSixAmbientRow21ClassMatrixCertificate

/-- The exact row-21 character values at the checked representatives. -/
def alternatingSixAmbientRow21ClassValue : Fin 31 → ℂ :=
  let η := alternatingSixAmbientRow21Eta
  ![9, (-η) * 9, (-η) ^ 2 * 9, (-η) ^ 3 * 9,
    (-η) ^ 4 * 9, (-η) ^ 5 * 9,
    -1 + η, (-η) * (-1 + η), (-η) ^ 2 * (-1 + η),
    1, -η, (-η) ^ 2, (-η) ^ 3, (-η) ^ 4, (-η) ^ 5,
    η, (-η) * η, (-η) ^ 2 * η, (-η) ^ 3 * η,
    (-η) ^ 4 * η, (-η) ^ 5 * η,
    1 - η, (-η) * (1 - η), (-η) ^ 2 * (1 - η),
    (-η) ^ 3 * (1 - η), (-η) ^ 4 * (1 - η),
    (-η) ^ 5 * (1 - η),
    0, 0, 0, 0]

/-- The displayed value is central scalar times the selected base trace. -/
theorem alternatingSixAmbientRow21ClassValue_eq_central_mul_base
    (i : Fin 31) :
    alternatingSixAmbientRow21ClassValue i =
      (-alternatingSixAmbientRow21Eta) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i *
        alternatingSixAmbientRow21BaseWordValue
          (alternatingSixAmbientClassRepresentativeBaseWord i) := by
  fin_cases i <;>
    simp [alternatingSixAmbientRow21ClassValue,
      alternatingSixAmbientClassRepresentativeCentralExponent,
      alternatingSixAmbientClassRepresentativeBaseWord,
      alternatingSixAmbientRow21BaseWordValue]

/-- The trace of each checked representative is its exact row-21 value. -/
theorem alternatingSixAmbientRow21_classRepresentative_trace
    (i : Fin 31) :
    (row21Certificate.classRepresentativeGL i :
        Matrix (Fin 9) (Fin 9) ℂ).trace =
      alternatingSixAmbientRow21ClassValue i := by
  rw [AlternatingSixSchurMatrixRowCertificate.classRepresentativeGL]
  change
    ((row21Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 9) (Fin 9) ℂ) *
      ((row21Certificate.relatorGL 0 :
          Matrix.GeneralLinearGroup (Fin 9) ℂ) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i :
        Matrix (Fin 9) (Fin 9) ℂ)).trace =
      _
  rw [row21Certificate.relatorGL_val]
  change
    ((row21Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 9) (Fin 9) ℂ) *
      ((alternatingSixComplexCyclotomicRoot ^ 80) •
        (1 : Matrix (Fin 9) (Fin 9) ℂ)) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i).trace =
      _
  rw [alternatingSixAmbientRow21_root_pow_eighty]
  change
    ((row21Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 9) (Fin 9) ℂ) *
      ((-alternatingSixAmbientRow21Eta) •
        (1 : Matrix (Fin 9) (Fin 9) ℂ)) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i).trace =
      _
  rw [show
    ((-alternatingSixAmbientRow21Eta) •
          (1 : Matrix (Fin 9) (Fin 9) ℂ)) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i =
      ((-alternatingSixAmbientRow21Eta) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i) •
        (1 : Matrix (Fin 9) (Fin 9) ℂ) by
      rw [show
          ((-alternatingSixAmbientRow21Eta) •
              (1 : Matrix (Fin 9) (Fin 9) ℂ)) =
            algebraMap ℂ (Matrix (Fin 9) (Fin 9) ℂ)
              (-alternatingSixAmbientRow21Eta) by
            rw [Algebra.algebraMap_eq_smul_one],
        ← map_pow, Algebra.algebraMap_eq_smul_one]]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    alternatingSixAmbientRow21_baseWord_trace]
  exact
    (alternatingSixAmbientRow21ClassValue_eq_central_mul_base i).symm

/-- Character value of the isolated row-21 representation at each checked
class representative. -/
theorem alternatingSixAmbientRow21_character_classRepresentative
    (i : Fin 31) :
    (FDRep.of row21Certificate.universalCoverRepresentation).character
        (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative i)) =
      alternatingSixAmbientRow21ClassValue i := by
  rw [
    row21Certificate.universalCoverRepresentation_character_classRepresentative
  ]
  exact alternatingSixAmbientRow21_classRepresentative_trace i

end InductiveMcKay
end McKayConjecture
