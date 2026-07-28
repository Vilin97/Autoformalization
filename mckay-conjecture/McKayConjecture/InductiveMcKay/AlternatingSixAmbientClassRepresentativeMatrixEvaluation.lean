/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientCoordinateMatrixEvaluation

/-!
# Matrix words for the 31 conjugacy-class representatives of `6.A₆`

The thirty-one checked representatives use only seven noncentral normal
words.  This module names those words and reduces evaluation of every class
representative to one of the seven corresponding matrix products, followed
by a power of the first central scalar.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The seven noncentral words occurring among the thirty-one checked class
representatives. -/
inductive AlternatingSixAmbientClassBaseWord
  | identity
  | generatorA
  | generatorB
  | generatorAB
  | generatorABSquared
  | state77
  | state79
  deriving DecidableEq

namespace AlternatingSixAmbientClassBaseWord

/-- The explicit signed word represented by one of the seven base labels. -/
def word :
    AlternatingSixAmbientClassBaseWord →
      AlternatingSixRewriteWord
  | .identity => []
  | .generatorA => [(0, true)]
  | .generatorB => [(1, true)]
  | .generatorAB => [(0, true), (1, true)]
  | .generatorABSquared =>
      [(0, true), (1, true), (1, true)]
  | .state77 =>
      [(0, true), (1, true), (0, true), (1, true),
        (1, true), (0, true), (1, false)]
  | .state79 =>
      [(0, true), (1, true), (0, true), (1, false),
        (0, true), (1, true), (1, true)]

end AlternatingSixAmbientClassBaseWord

/-- Select the noncentral base word of a checked class representative. -/
def alternatingSixAmbientClassRepresentativeBaseWord :
    Fin 31 → AlternatingSixAmbientClassBaseWord :=
  fun i =>
    match i.val with
    | 0 | 1 | 2 | 3 | 4 | 5 => .identity
    | 6 | 7 | 8 => .generatorA
    | 9 | 10 | 11 | 12 | 13 | 14 => .generatorB
    | 15 | 16 | 17 | 18 | 19 | 20 => .generatorAB
    | 21 | 22 | 23 | 24 | 25 | 26 => .generatorABSquared
    | 27 | 28 => .state77
    | _ => .state79

/-- The exponent of the first central scalar in a checked representative. -/
def alternatingSixAmbientClassRepresentativeCentralExponent :
    Fin 31 → ℕ :=
  fun i =>
    match i.val with
    | 0 | 6 | 9 | 15 | 21 | 27 | 29 => 0
    | 1 | 7 | 10 | 16 | 22 | 28 | 30 => 1
    | 2 | 8 | 11 | 17 | 23 => 2
    | 3 | 12 | 18 | 24 => 3
    | 4 | 13 | 19 | 25 => 4
    | _ => 5

/-- The normal word stored by each representative is its selected explicit
base word. -/
theorem alternatingSixAmbientClassRepresentative_normalWord
    (i : Fin 31) :
    alternatingSixRewriteNormalWords
        (alternatingSixSchurClassRepresentative i).state =
      (alternatingSixAmbientClassRepresentativeBaseWord i).word := by
  fin_cases i <;> rfl

/-- The stored central coordinate is the advertised exponent from zero to
five. -/
theorem alternatingSixAmbientClassRepresentative_centralExponent
    (i : Fin 31) :
    (alternatingSixSchurClassRepresentative i).central.val =
      alternatingSixAmbientClassRepresentativeCentralExponent i := by
  fin_cases i <;> rfl

namespace AlternatingSixSchurMatrixRowCertificate

variable {n : Type} [Fintype n] [DecidableEq n]
variable (C : AlternatingSixSchurMatrixRowCertificate n)

/-- The exact `GL` word assigned to one checked class representative. -/
def classRepresentativeGL
    (i : Fin 31) :
    Matrix.GeneralLinearGroup n ℂ :=
  C.rewriteWordGL
      (alternatingSixAmbientClassRepresentativeBaseWord i).word *
    C.relatorGL 0 ^
      alternatingSixAmbientClassRepresentativeCentralExponent i

/-- The general coordinate matrix specializes to the explicit seven-word
class-representative table. -/
theorem coordinateGL_classRepresentative
    (i : Fin 31) :
    C.coordinateGL (alternatingSixSchurClassRepresentative i) =
      C.classRepresentativeGL i := by
  unfold coordinateGL classRepresentativeGL
  rw [alternatingSixAmbientClassRepresentative_normalWord,
    alternatingSixAmbientClassRepresentative_centralExponent]

/-- Action of a checked class representative in the transported canonical
cover representation. -/
theorem universalCoverRepresentation_classRepresentative
    (i : Fin 31) :
    C.universalCoverRepresentation
        (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative i)) =
      Matrix.toLin' (C.classRepresentativeGL i : Matrix n n ℂ) := by
  rw [C.universalCoverRepresentation_coordinate,
    C.coordinateGL_classRepresentative]

/-- Character value at a checked class representative, reduced to the trace
of one of seven explicit matrix words times a central scalar. -/
theorem universalCoverRepresentation_character_classRepresentative
    [Nonempty n]
    (i : Fin 31) :
    (FDRep.of C.universalCoverRepresentation).character
        (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative i)) =
      (C.classRepresentativeGL i : Matrix n n ℂ).trace := by
  rw [C.universalCoverRepresentation_character_coordinate,
    C.coordinateGL_classRepresentative]

end AlternatingSixSchurMatrixRowCertificate
end InductiveMcKay
end McKayConjecture
