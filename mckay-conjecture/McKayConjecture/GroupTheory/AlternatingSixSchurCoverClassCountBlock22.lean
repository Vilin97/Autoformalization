/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock

/-!
# Class counts in states 220–229 of the sixfold cover of `A₆`

This generated certificate counts the checked class labels in one block of
ten normal-word states and six central coordinates.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- The class-label histogram in normal-word states 220–229. -/
def alternatingSixSchurClassCountBlock22 :
    Fin 31 → Nat :=
  ![
    0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 4, 4, 4, 4, 3,
    3, 3, 3, 3, 3, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3
  ]

/-- Kernel-checked cardinality of every label fiber in states 220–229. -/
theorem alternatingSixSchurClassCountBlockFiber_card_22 (i : Fin 31) :
    Fintype.card (AlternatingSixSchurClassCountBlockFiber 22 i) =
      alternatingSixSchurClassCountBlock22 i := by
  fin_cases i <;> decide


end GroupTheory
end McKayConjecture
