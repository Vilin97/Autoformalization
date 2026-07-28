/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedGeneralExistence
import McKayConjecture.CharacterTriple.AssociatedQuotientFactorUniqueness

/-!
# The projective obstruction class of a character triple

An invariant irreducible character of a normal subgroup determines an
intrinsic class in the second cohomology of the outer quotient.  Concretely,
choose any associated projective representation and take the class of its
descended factor set.  Uniqueness of associated lifts shows that the result
is independent of every choice.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple

variable {A : Type} [Finite A] [Group A]

/-- The intrinsic projective extension obstruction of a finite character
triple, represented using the canonical associated lift. -/
def projectiveObstructionClass (T : CharacterTriple A) :
    letI :=
      trivialMulDistribMulAction
        (A ⧸ T.normalSubgroup) ℂˣ
    groupCohomology.H2
      (Rep.ofMulDistribMulAction
        (A ⧸ T.normalSubgroup) ℂˣ) :=
  (AssociatedGeneralExistence.associated T
    ).quotientFactorSet.h2Class

namespace AssociatedProjectiveRepresentation

variable {T : CharacterTriple A}
variable {V : Type}
  [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- Every associated projective lift represents the intrinsic obstruction
class of its character triple. -/
theorem quotientFactorSet_h2Class_eq_projectiveObstructionClass
    (R : AssociatedProjectiveRepresentation T V P) :
    letI :=
      trivialMulDistribMulAction
        (A ⧸ T.normalSubgroup) ℂˣ
    R.quotientFactorSet.h2Class =
      T.projectiveObstructionClass := by
  exact
    R.quotientFactorSet_h2Class_eq
      (AssociatedGeneralExistence.associated T)

end AssociatedProjectiveRepresentation

end CharacterTriple
end McKayConjecture
