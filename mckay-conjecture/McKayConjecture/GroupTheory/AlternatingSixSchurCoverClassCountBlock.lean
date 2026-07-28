/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData

/-!
# Blocks for counting classes in the sixfold cover of `A₆`

The 360 normal-word states are split as `36 × 10`.  Consequently a class
fiber can be counted in 36 independent blocks of only sixty coordinates.
This keeps all finite checks within Lean's default recursion limits.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Reassemble a normal-word state from a ten-state block and an offset. -/
def alternatingSixSchurClassCountBlockCoordinate
    (block : Fin 36) (coordinate : Fin 10 × Fin 6) :
    AlternatingSixSchurCoordinates :=
  { state :=
      (finProdFinEquiv : Fin 36 × Fin 10 ≃ Fin 360)
        (block, coordinate.1)
    central := (ZMod.finEquiv 6) coordinate.2 }

/-- The part of a checked class-label fiber lying over one ten-state block. -/
abbrev AlternatingSixSchurClassCountBlockFiber
    (block : Fin 36) (i : Fin 31) :=
  {coordinate : Fin 10 × Fin 6 //
    alternatingSixSchurClassIndex
        (alternatingSixSchurClassCountBlockCoordinate block coordinate) = i}


end GroupTheory
end McKayConjecture
