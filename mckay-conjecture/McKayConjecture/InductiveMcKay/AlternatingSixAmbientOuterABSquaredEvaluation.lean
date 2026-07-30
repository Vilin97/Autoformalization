/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientTwoGeneratorCharacterRow

/-!
# Character evaluation at the canonical `AB²` word

The first canonical outer automorphism exchanges the `AB` and `AB²` class
families.  This module supplies the common matrix bridge used by the few
paired rows that need this value.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The positive presentation word `a b²` in the canonical universal
cover. -/
def alternatingSixAmbientCanonicalGeneratorABSquared :
    AlternatingSixUniversalCover :=
  alternatingSixAmbientCanonicalGeneratorA *
    alternatingSixAmbientCanonicalGeneratorB *
    alternatingSixAmbientCanonicalGeneratorB

namespace AlternatingSixSchurMatrixRowCertificate

variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
variable (C : AlternatingSixSchurMatrixRowCertificate n)

/-- The canonical `AB²` word acts by `matrixA * matrixB * matrixB`. -/
theorem universalCoverRepresentation_generatorABSquared :
    C.universalCoverRepresentation
        alternatingSixAmbientCanonicalGeneratorABSquared =
      Matrix.toLin' (C.matrixA * C.matrixB * C.matrixB) := by
  simp only [alternatingSixAmbientCanonicalGeneratorABSquared,
    map_mul, C.universalCoverRepresentation_generatorA,
    C.universalCoverRepresentation_generatorB,
    Module.End.mul_eq_comp, Matrix.toLin'_mul]

/-- Character value at the canonical `AB²` word as an exact matrix trace. -/
theorem universalCoverRepresentation_character_generatorABSquared :
    (FDRep.of C.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalGeneratorABSquared =
      (C.matrixA * C.matrixB * C.matrixB).trace :=
  C.universalCoverRepresentation_character_eq_trace_of_action_eq
    alternatingSixAmbientCanonicalGeneratorABSquared
    (C.matrixA * C.matrixB * C.matrixB)
    C.universalCoverRepresentation_generatorABSquared

end AlternatingSixSchurMatrixRowCertificate
end InductiveMcKay
end McKayConjecture
