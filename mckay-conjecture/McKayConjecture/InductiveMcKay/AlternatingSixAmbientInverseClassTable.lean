/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassCharacterCertificate

/-!
# Inverse permutation of the checked ambient classes

This shared table records which of the thirty-one checked class labels
contains the inverse of each representative.
-/

namespace McKayConjecture
namespace InductiveMcKay

/-- Explicit inverse permutation on the thirty-one checked class labels. -/
def alternatingSixAmbientInverseClassIndexTable : Fin 31 → Fin 31 :=
  ![0, 5, 4, 3, 2, 1, 8, 7, 6, 9, 14, 13, 12, 11, 10, 19,
    18, 17, 16, 15, 20, 23, 22, 21, 26, 25, 24, 27, 28, 29, 30]

/-- The checked coordinate inverse has the displayed class label. -/
theorem alternatingSixSchurInverseClassIndex_eq_table
    (i : Fin 31) :
    alternatingSixSchurInverseClassIndex i =
      alternatingSixAmbientInverseClassIndexTable i := by
  fin_cases i <;> decide

end InductiveMcKay
end McKayConjecture
