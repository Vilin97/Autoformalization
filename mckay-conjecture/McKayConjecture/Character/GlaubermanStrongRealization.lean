/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanActionStrongUniqueness
import McKayConjecture.Character.GlaubermanCorrespondenceUniqueness
import McKayConjecture.Character.GlaubermanCyclicAction

/-!
# Strong realizations of ambient Glauberman correspondences

For a normal `p′`-subgroup acted on by a `p`-subgroup, the proved cyclic
action theorem constructs a strong action correspondence.  Its ambient
transport is the unique ordinary Glauberman correspondence.  Hence every
value of the ordinary interface admits a strong realization, retaining
the uniqueness statement against all irreducible fixed-point characters.
-/

noncomputable section

namespace McKayConjecture

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K P : Subgroup G) [K.Normal]

local instance conjugationAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K P

namespace GlaubermanCorrespondence

/-- A cyclic strong-action input realizes every ordinary ambient
Glauberman correspondence. -/
theorem exists_strongActionRealization_of_cyclic
    (cyclic : CyclicStrongActionGlaubermanHypothesis p)
    (hP : IsPGroup p P)
    (hK : GroupTheory.IsPPrimeGroup p K)
    (g : GlaubermanCorrespondence K P p) :
    ∃ d : StrongActionGlaubermanCorrespondence P K p,
      glaubermanCorrespondenceOfStrongConjugationAction
          K P d =
        g := by
  obtain ⟨d⟩ :=
    strongActionGlaubermanCorrespondenceOfPGroup
      cyclic P K hP hK
  exact ⟨d, Subsingleton.elim _ _⟩

/-- Every ordinary ambient Glauberman correspondence in the coprime
`p`-group setting has an unconditional strong realization. -/
theorem exists_strongActionRealization
    (hP : IsPGroup p P)
    (hK : GroupTheory.IsPPrimeGroup p K)
    (g : GlaubermanCorrespondence K P p) :
    ∃ d : StrongActionGlaubermanCorrespondence P K p,
      glaubermanCorrespondenceOfStrongConjugationAction
          K P d =
        g :=
  exists_strongActionRealization_of_cyclic
    K P cyclicStrongActionGlaubermanHypothesis hP hK g

end GlaubermanCorrespondence
end McKayConjecture
