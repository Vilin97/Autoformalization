/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyClasses
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterAutomorphismChecks

/-!
# Outer automorphisms on the canonical universal cover of `A₆`

The two proved automorphisms of the computable Schur-coordinate model are
transported across the established multiplicative equivalence with the
canonical universal cover.  This file also transports the checked class
representatives and their class-index function.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

private abbrev coordinateEquiv :=
  alternatingSixSchurCoordinatesEquivUniversalCover

/-- The first audited coordinate automorphism, transported to the canonical
universal cover. -/
def alternatingSixUniversalCoverAlphaOneAutomorphism :
    AlternatingSixUniversalCover ≃*
      AlternatingSixUniversalCover :=
  coordinateEquiv.symm.trans
    (alternatingSixSchurAlphaOneAutomorphism.trans coordinateEquiv)

/-- The second audited coordinate automorphism, transported to the canonical
universal cover.  The chosen representative has order eight. -/
def alternatingSixUniversalCoverAlphaTwoAutomorphism :
    AlternatingSixUniversalCover ≃*
      AlternatingSixUniversalCover :=
  coordinateEquiv.symm.trans
    (alternatingSixSchurAlphaTwoAutomorphism.trans coordinateEquiv)

/-- The transported first automorphism agrees with the coordinate
automorphism under the bridge equivalence. -/
@[simp]
theorem alternatingSixUniversalCoverAlphaOneAutomorphism_apply_coordinate
    (coordinate : AlternatingSixSchurCoordinates) :
    alternatingSixUniversalCoverAlphaOneAutomorphism
        (coordinateEquiv coordinate) =
      coordinateEquiv
        (alternatingSixSchurAlphaOneAutomorphism coordinate) := by
  simp [alternatingSixUniversalCoverAlphaOneAutomorphism]

/-- The transported second automorphism agrees with the coordinate
automorphism under the bridge equivalence. -/
@[simp]
theorem alternatingSixUniversalCoverAlphaTwoAutomorphism_apply_coordinate
    (coordinate : AlternatingSixSchurCoordinates) :
    alternatingSixUniversalCoverAlphaTwoAutomorphism
        (coordinateEquiv coordinate) =
      coordinateEquiv
        (alternatingSixSchurAlphaTwoAutomorphism coordinate) := by
  simp [alternatingSixUniversalCoverAlphaTwoAutomorphism]

/-- The canonical universal-cover representative corresponding to a checked
Schur-coordinate class index. -/
def alternatingSixUniversalCoverClassRepresentative
    (index : Fin 31) :
    AlternatingSixUniversalCover :=
  coordinateEquiv
    (alternatingSixSchurClassRepresentative index)

/-- The checked coordinate class index transported to the canonical
universal cover. -/
def alternatingSixUniversalCoverClassIndex
    (element : AlternatingSixUniversalCover) :
    Fin 31 :=
  alternatingSixSchurClassIndex
    (coordinateEquiv.symm element)

/-- Every transported representative has its advertised class index. -/
@[simp]
theorem alternatingSixUniversalCoverClassIndex_representative
    (index : Fin 31) :
    alternatingSixUniversalCoverClassIndex
        (alternatingSixUniversalCoverClassRepresentative index) =
      index := by
  simp [alternatingSixUniversalCoverClassIndex,
    alternatingSixUniversalCoverClassRepresentative,
    alternatingSixSchurClassIndex_representative]

end GroupTheory
end McKayConjecture
