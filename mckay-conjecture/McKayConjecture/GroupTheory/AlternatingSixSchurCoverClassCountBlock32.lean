/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock

/-!
# Class counts in states 320–329 of the sixfold cover of `A₆`

This generated certificate counts the checked class labels in one block of
ten normal-word states and six central coordinates.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- The class-label histogram in normal-word states 320–329. -/
def alternatingSixSchurClassCountBlock32 :
    Fin 31 → Nat :=
  ![
    0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 6,
    6, 6, 6, 6, 6, 0, 0, 0, 0, 0, 0, 3, 3, 3, 3
  ]

/-- Kernel-checked cardinality of every label fiber in states 320–329. -/
theorem alternatingSixSchurClassCountBlockFiber_card_32 (i : Fin 31) :
    Fintype.card (AlternatingSixSchurClassCountBlockFiber 32 i) =
      alternatingSixSchurClassCountBlock32 i := by
  fin_cases i <;> decide


end GroupTheory
end McKayConjecture
