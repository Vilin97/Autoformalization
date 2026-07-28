/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock

/-!
# Class counts in states 40–49 of the sixfold cover of `A₆`

This generated certificate counts the checked class labels in one block of
ten normal-word states and six central coordinates.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- The class-label histogram in normal-word states 40–49. -/
def alternatingSixSchurClassCountBlock04 :
    Fin 31 → Nat :=
  ![
    0, 0, 0, 0, 0, 0, 2, 2, 2, 4, 4, 4, 4, 4, 4, 0,
    0, 0, 0, 0, 0, 5, 5, 5, 5, 5, 5, 0, 0, 0, 0
  ]

/-- Kernel-checked cardinality of every label fiber in states 40–49. -/
theorem alternatingSixSchurClassCountBlockFiber_card_04 (i : Fin 31) :
    Fintype.card (AlternatingSixSchurClassCountBlockFiber 4 i) =
      alternatingSixSchurClassCountBlock04 i := by
  fin_cases i <;> decide


end GroupTheory
end McKayConjecture
