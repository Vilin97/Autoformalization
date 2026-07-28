/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow30BaseWordTraces

/-!
# Character values of ambient row 30 on the 31 checked classes

Each displayed value is the exact base-word trace multiplied by the
appropriate power of the central scalar `ζ⁸⁰ = -ζ²⁰`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev row30Certificate :=
  alternatingSixAmbientRow30ClassMatrixCertificate

/-- The exact row-30 character values at the checked representatives. -/
def alternatingSixAmbientRow30ClassValue : Fin 31 → ℂ :=
  let η := alternatingSixAmbientRow30Eta
  ![15, (-η) * 15, (-η) ^ 2 * 15, (-η) ^ 3 * 15,
    (-η) ^ 4 * 15, (-η) ^ 5 * 15,
    1 - η, (-η) * (1 - η), (-η) ^ 2 * (1 - η),
    -1, (-η) * (-1), (-η) ^ 2 * (-1), (-η) ^ 3 * (-1),
    (-η) ^ 4 * (-1), (-η) ^ 5 * (-1),
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0]

/-- The displayed value is central scalar times the selected base trace. -/
theorem alternatingSixAmbientRow30ClassValue_eq_central_mul_base
    (i : Fin 31) :
    alternatingSixAmbientRow30ClassValue i =
      (-alternatingSixAmbientRow30Eta) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i *
        alternatingSixAmbientRow30BaseWordValue
          (alternatingSixAmbientClassRepresentativeBaseWord i) := by
  fin_cases i <;>
    simp [alternatingSixAmbientRow30ClassValue,
      alternatingSixAmbientClassRepresentativeCentralExponent,
      alternatingSixAmbientClassRepresentativeBaseWord,
      alternatingSixAmbientRow30BaseWordValue]

/-- The trace of each checked representative is its exact row-30 value. -/
theorem alternatingSixAmbientRow30_classRepresentative_trace
    (i : Fin 31) :
    (row30Certificate.classRepresentativeGL i :
        Matrix (Fin 15) (Fin 15) ℂ).trace =
      alternatingSixAmbientRow30ClassValue i := by
  rw [AlternatingSixSchurMatrixRowCertificate.classRepresentativeGL]
  change
    ((row30Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 15) (Fin 15) ℂ) *
      ((row30Certificate.relatorGL 0 :
          Matrix.GeneralLinearGroup (Fin 15) ℂ) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i :
        Matrix (Fin 15) (Fin 15) ℂ)).trace =
      _
  rw [row30Certificate.relatorGL_val]
  change
    ((row30Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 15) (Fin 15) ℂ) *
      ((alternatingSixComplexCyclotomicRoot ^ 80) •
        (1 : Matrix (Fin 15) (Fin 15) ℂ)) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i).trace =
      _
  rw [alternatingSixAmbientRow30_root_pow_eighty]
  change
    ((row30Certificate.rewriteWordGL
          (alternatingSixAmbientClassRepresentativeBaseWord i).word :
        Matrix (Fin 15) (Fin 15) ℂ) *
      ((-alternatingSixAmbientRow30Eta) •
        (1 : Matrix (Fin 15) (Fin 15) ℂ)) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i).trace =
      _
  rw [show
    ((-alternatingSixAmbientRow30Eta) •
          (1 : Matrix (Fin 15) (Fin 15) ℂ)) ^
        alternatingSixAmbientClassRepresentativeCentralExponent i =
      ((-alternatingSixAmbientRow30Eta) ^
          alternatingSixAmbientClassRepresentativeCentralExponent i) •
        (1 : Matrix (Fin 15) (Fin 15) ℂ) by
      rw [show
          ((-alternatingSixAmbientRow30Eta) •
              (1 : Matrix (Fin 15) (Fin 15) ℂ)) =
            algebraMap ℂ (Matrix (Fin 15) (Fin 15) ℂ)
              (-alternatingSixAmbientRow30Eta) by
            rw [Algebra.algebraMap_eq_smul_one],
        ← map_pow, Algebra.algebraMap_eq_smul_one]]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    alternatingSixAmbientRow30_baseWord_trace]
  exact
    (alternatingSixAmbientRow30ClassValue_eq_central_mul_base i).symm

/-- Character value of the isolated row-30 representation at each checked
class representative. -/
theorem alternatingSixAmbientRow30_character_classRepresentative
    (i : Fin 31) :
    (FDRep.of row30Certificate.universalCoverRepresentation).character
        (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative i)) =
      alternatingSixAmbientRow30ClassValue i := by
  rw [
    row30Certificate.universalCoverRepresentation_character_classRepresentative
  ]
  exact alternatingSixAmbientRow30_classRepresentative_trace i

end InductiveMcKay
end McKayConjecture
