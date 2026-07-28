/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionBernsteinSeparation
import McKayConjecture.Character.BrauerInductionIdealGeneration

/-!
# Brauer induction and the elementary-local character criterion

Bernstein's regular-fibre construction produces the constant-one class
function inside the cyclotomic elementary-induction ideal.  Ideal generation
and additive cyclotomic descent then give denominator-one Brauer induction
for every finite group.

Combining this unconditional induction theorem with the character-theoretic
reduction proves Brauer's local criterion: a complex class function is an
integral generalized character exactly when all of its restrictions to
elementary direct products are integral generalized characters.
-/

noncomputable section

namespace McKayConjecture
namespace ClassFunction

variable {G : Type} [Group G] [Finite G]

/-- **Brauer induction.** Every irreducible character of a finite group is
an integral linear combination of characters induced from elementary
subgroups. -/
theorem hasElementaryBrauerInduction :
    HasElementaryBrauerInduction (G := G) := by
  obtain ⟨q, hq, hqone⟩ :=
    exists_bernsteinIdeal_member_eq_one G
  exact
    hasElementaryBrauerInduction_of_cyclotomicIdeal_member_eq_one
      q hq hqone

/-- Unconditional forward form of Brauer's elementary-local criterion. -/
theorem isGeneralizedCharacter_of_elementary_local_unconditional
    {f : ClassFunction G}
    (hlocal :
      ∀ (p : ℕ), p.Prime →
        ∀ (S : Subgroup G)
          (D : PElementaryDecomposition p S),
          IsGeneralizedCharacter
            (restrictToPElementaryProduct S D f)) :
    IsGeneralizedCharacter f :=
  isGeneralizedCharacter_of_elementary_local
    hasElementaryBrauerInduction hlocal

/-- **Brauer's elementary-local generalized-character criterion.** A
complex class function on a finite group is an integral generalized
character if and only if its restriction to every elementary direct
product is one. -/
theorem isGeneralizedCharacter_iff_elementary_local_unconditional
    (f : ClassFunction G) :
    IsGeneralizedCharacter f ↔
      ∀ (p : ℕ), p.Prime →
        ∀ (S : Subgroup G)
          (D : PElementaryDecomposition p S),
          IsGeneralizedCharacter
            (restrictToPElementaryProduct S D f) :=
  isGeneralizedCharacter_iff_elementary_local
    hasElementaryBrauerInduction f

end ClassFunction
end McKayConjecture
