/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock00
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock01
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock02
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock03
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock04
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock05
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock06
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock07
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock08
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock09
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock10
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock11
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock12
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock13
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock14
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock15
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock16
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock17
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock18
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock19
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock20
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock21
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock22
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock23
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock24
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock25
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock26
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock27
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock28
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock29
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock30
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock31
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock32
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock33
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock34
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCountBlock35

/-!
# Checked class counts in the sixfold cover of `A₆`

The blockwise histograms are assembled into a count of every checked
class-label fiber.  All computational proofs enumerate at most sixty group
coordinates or thirty-six small natural numbers.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- The checked class-label histogram of a ten-state block. -/
def alternatingSixSchurClassCountBlock
    (block : Fin 36) : Fin 31 → Nat :=
  match block.val with
  | 0 => alternatingSixSchurClassCountBlock00
  | 1 => alternatingSixSchurClassCountBlock01
  | 2 => alternatingSixSchurClassCountBlock02
  | 3 => alternatingSixSchurClassCountBlock03
  | 4 => alternatingSixSchurClassCountBlock04
  | 5 => alternatingSixSchurClassCountBlock05
  | 6 => alternatingSixSchurClassCountBlock06
  | 7 => alternatingSixSchurClassCountBlock07
  | 8 => alternatingSixSchurClassCountBlock08
  | 9 => alternatingSixSchurClassCountBlock09
  | 10 => alternatingSixSchurClassCountBlock10
  | 11 => alternatingSixSchurClassCountBlock11
  | 12 => alternatingSixSchurClassCountBlock12
  | 13 => alternatingSixSchurClassCountBlock13
  | 14 => alternatingSixSchurClassCountBlock14
  | 15 => alternatingSixSchurClassCountBlock15
  | 16 => alternatingSixSchurClassCountBlock16
  | 17 => alternatingSixSchurClassCountBlock17
  | 18 => alternatingSixSchurClassCountBlock18
  | 19 => alternatingSixSchurClassCountBlock19
  | 20 => alternatingSixSchurClassCountBlock20
  | 21 => alternatingSixSchurClassCountBlock21
  | 22 => alternatingSixSchurClassCountBlock22
  | 23 => alternatingSixSchurClassCountBlock23
  | 24 => alternatingSixSchurClassCountBlock24
  | 25 => alternatingSixSchurClassCountBlock25
  | 26 => alternatingSixSchurClassCountBlock26
  | 27 => alternatingSixSchurClassCountBlock27
  | 28 => alternatingSixSchurClassCountBlock28
  | 29 => alternatingSixSchurClassCountBlock29
  | 30 => alternatingSixSchurClassCountBlock30
  | 31 => alternatingSixSchurClassCountBlock31
  | 32 => alternatingSixSchurClassCountBlock32
  | 33 => alternatingSixSchurClassCountBlock33
  | 34 => alternatingSixSchurClassCountBlock34
  | _ => alternatingSixSchurClassCountBlock35

/-- Every block fiber has the corresponding checked histogram entry. -/
theorem alternatingSixSchurClassCountBlockFiber_card
    (block : Fin 36) (i : Fin 31) :
    Fintype.card
        (AlternatingSixSchurClassCountBlockFiber block i) =
      alternatingSixSchurClassCountBlock block i := by
  fin_cases block
  · exact alternatingSixSchurClassCountBlockFiber_card_00 i
  · exact alternatingSixSchurClassCountBlockFiber_card_01 i
  · exact alternatingSixSchurClassCountBlockFiber_card_02 i
  · exact alternatingSixSchurClassCountBlockFiber_card_03 i
  · exact alternatingSixSchurClassCountBlockFiber_card_04 i
  · exact alternatingSixSchurClassCountBlockFiber_card_05 i
  · exact alternatingSixSchurClassCountBlockFiber_card_06 i
  · exact alternatingSixSchurClassCountBlockFiber_card_07 i
  · exact alternatingSixSchurClassCountBlockFiber_card_08 i
  · exact alternatingSixSchurClassCountBlockFiber_card_09 i
  · exact alternatingSixSchurClassCountBlockFiber_card_10 i
  · exact alternatingSixSchurClassCountBlockFiber_card_11 i
  · exact alternatingSixSchurClassCountBlockFiber_card_12 i
  · exact alternatingSixSchurClassCountBlockFiber_card_13 i
  · exact alternatingSixSchurClassCountBlockFiber_card_14 i
  · exact alternatingSixSchurClassCountBlockFiber_card_15 i
  · exact alternatingSixSchurClassCountBlockFiber_card_16 i
  · exact alternatingSixSchurClassCountBlockFiber_card_17 i
  · exact alternatingSixSchurClassCountBlockFiber_card_18 i
  · exact alternatingSixSchurClassCountBlockFiber_card_19 i
  · exact alternatingSixSchurClassCountBlockFiber_card_20 i
  · exact alternatingSixSchurClassCountBlockFiber_card_21 i
  · exact alternatingSixSchurClassCountBlockFiber_card_22 i
  · exact alternatingSixSchurClassCountBlockFiber_card_23 i
  · exact alternatingSixSchurClassCountBlockFiber_card_24 i
  · exact alternatingSixSchurClassCountBlockFiber_card_25 i
  · exact alternatingSixSchurClassCountBlockFiber_card_26 i
  · exact alternatingSixSchurClassCountBlockFiber_card_27 i
  · exact alternatingSixSchurClassCountBlockFiber_card_28 i
  · exact alternatingSixSchurClassCountBlockFiber_card_29 i
  · exact alternatingSixSchurClassCountBlockFiber_card_30 i
  · exact alternatingSixSchurClassCountBlockFiber_card_31 i
  · exact alternatingSixSchurClassCountBlockFiber_card_32 i
  · exact alternatingSixSchurClassCountBlockFiber_card_33 i
  · exact alternatingSixSchurClassCountBlockFiber_card_34 i
  · exact alternatingSixSchurClassCountBlockFiber_card_35 i

/-- The 36 checked block histograms add to the advertised class size. -/
theorem alternatingSixSchurClassCountBlock_sum (i : Fin 31) :
    ∑ block : Fin 36, alternatingSixSchurClassCountBlock block i =
      alternatingSixSchurClassSize i := by
  fin_cases i <;> decide


end GroupTheory
end McKayConjecture
