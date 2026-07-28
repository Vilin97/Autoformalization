/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock

/-!
# Class counts in states 350–359 of the sixfold cover of `A₆`

This generated certificate counts the checked class labels in one block of
ten normal-word states and six central coordinates.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- The class-label histogram in normal-word states 350–359. -/
def alternatingSixSchurClassCountBlock35 :
    Fin 31 → Nat :=
  ![
    0, 0, 0, 0, 0, 0, 12, 12, 12, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  ]

/-- Kernel-checked cardinality of every label fiber in states 350–359. -/
theorem alternatingSixSchurClassCountBlockFiber_card_35 (i : Fin 31) :
    Fintype.card (AlternatingSixSchurClassCountBlockFiber 35 i) =
      alternatingSixSchurClassCountBlock35 i := by
  fin_cases i <;> decide


end GroupTheory
end McKayConjecture
