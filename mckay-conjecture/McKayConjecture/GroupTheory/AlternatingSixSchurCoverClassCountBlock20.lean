/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock

/-!
# Class counts in states 200–209 of the sixfold cover of `A₆`

This generated certificate counts the checked class labels in one block of
ten normal-word states and six central coordinates.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- The class-label histogram in normal-word states 200–209. -/
def alternatingSixSchurClassCountBlock20 :
    Fin 31 → Nat :=
  ![
    0, 0, 0, 0, 0, 0, 2, 2, 2, 3, 3, 3, 3, 3, 3, 0,
    0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 6, 6, 6, 6
  ]

/-- Kernel-checked cardinality of every label fiber in states 200–209. -/
theorem alternatingSixSchurClassCountBlockFiber_card_20 (i : Fin 31) :
    Fintype.card (AlternatingSixSchurClassCountBlockFiber 20 i) =
      alternatingSixSchurClassCountBlock20 i := by
  fin_cases i <;> decide


end GroupTheory
end McKayConjecture
