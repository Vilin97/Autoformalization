/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalForm
import McKayConjecture.GroupTheory.BinaryIcosahedralPresentationCentralClosed
import McKayConjecture.GroupTheory.CentrallyClosedEquivalence
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveAlternatingEquiv

/-!
# The universal binary cover of `A₅`

The balanced binary-icosahedral presentation is centrally closed and is
certifiably equivalent to `SL(2, 𝔽₅)`.  Since the latter is perfect, its
central quotient is therefore a universal central extension.  Transporting
the target across the exceptional isomorphism `PSL(2, 𝔽₅) ≃ A₅` gives the
concrete universal cover used by the finite character tables.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- `SL(2, 𝔽₅)` is centrally closed, transported from the certified
binary-icosahedral presentation. -/
theorem specialLinearTwoFive_isCentrallyClosed :
    IsCentrallyClosed SpecialLinearTwoFive :=
  binaryIcosahedralPresentedGroup_isCentrallyClosed.of_mulEquiv
    binaryIcosahedralPresentedGroupEquivSpecialLinearTwoFive

/-- The central quotient `SL(2, 𝔽₅) → PSL(2, 𝔽₅)` is universal. -/
def specialLinearTwoFiveUniversalCentralExtensionProjective :
    UniversalCentralExtension
      SpecialLinearTwoFive ProjectiveSpecialLinearTwoFive :=
  universalCentralExtensionOfIsCentrallyClosed
    specialLinearTwoFiveCentralExtension
    (inferInstance : Group.IsPerfect SpecialLinearTwoFive)
    specialLinearTwoFive_isCentrallyClosed

/-- The concrete universal central extension
`SL(2, 𝔽₅) → A₅`. -/
def specialLinearTwoFiveUniversalCentralExtensionAlternatingFive :
    UniversalCentralExtension
      SpecialLinearTwoFive (alternatingGroup (Fin 5)) :=
  specialLinearTwoFiveUniversalCentralExtensionProjective.targetEquiv
    projectiveSpecialLinearTwoFiveEquivAlternatingGroup

/-- The projection of the certified universal cover is the concrete
five-point alternating action. -/
@[simp]
theorem specialLinearTwoFiveUniversalCentralExtensionAlternatingFive_projection :
    specialLinearTwoFiveUniversalCentralExtensionAlternatingFive.toCentralExtension.projection =
      specialLinearTwoFiveAlternatingAction := by
  ext g
  rfl

end GroupTheory
end McKayConjecture
