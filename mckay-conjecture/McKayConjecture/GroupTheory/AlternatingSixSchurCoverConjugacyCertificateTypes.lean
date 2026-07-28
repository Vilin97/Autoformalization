/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverCoordinateModel

/-!
# Certificate records for sixfold-cover conjugacy

A compact generated record stores the class label and the short factors used to check one orbit witness.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- One row entry in the finite conjugacy certificate. -/
structure AlternatingSixSchurConjugacyDatum where
  classIndex : Fin 31
  conjugatorState : Fin 360
  orbitMiddleState : Fin 360
  orbitMiddleCentral : Fin 6
  conjugatorInverseState : Fin 360
  conjugatorInverseCentral : Fin 6
  inverseFactorLeftState : Fin 360
  inverseFactorLeftCentral : Fin 6
  inverseFactorRightState : Fin 360
  inverseFactorRightCentral : Fin 6
  orbitPenultimateState : Fin 360
  orbitPenultimateCentral : Fin 6
deriving DecidableEq


end GroupTheory
end McKayConjecture
