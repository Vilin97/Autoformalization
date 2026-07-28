/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ElementaryBrauerInductionAutomatic

/-!
# The p-group base case of elementary Brauer induction

A finite `p`-group is itself `p`-elementary: its cyclic prime-to-`p`
factor is trivial and its `p`-factor is the whole group.  Induction from
the top subgroup therefore proves denominator-one Brauer induction
immediately.
-/

noncomputable section

namespace McKayConjecture
namespace ClassFunction

variable {p : ℕ}
variable {G : Type} [Group G] [Finite G]

/-- The top subgroup of a `p`-group has the elementary decomposition
`1 × G`. -/
def topPElementaryDecompositionOfIsPGroup
    (hG : IsPGroup p G) :
    PElementaryDecomposition p (⊤ : Subgroup G) where
  cyclicPart := ⊥
  pPart := ⊤
  cyclic := inferInstance
  cyclicPart_coprime := by simp
  isPGroup :=
    (hG.to_subgroup (⊤ : Subgroup G)).to_subgroup
      (⊤ : Subgroup (⊤ : Subgroup G))
  cyclicPart_normal := inferInstance
  pPart_normal := inferInstance
  complementary := Subgroup.isComplement'_bot_top

/-- Denominator-one elementary Brauer induction holds for every finite
`p`-group. -/
theorem hasElementaryBrauerInduction_of_isPGroup
    [Fact p.Prime] (hG : IsPGroup p G) :
    HasElementaryBrauerInduction (G := G) :=
  hasElementaryBrauerInduction_of_top_decomposition
    p Fact.out
    (topPElementaryDecompositionOfIsPGroup hG)

end ClassFunction
end McKayConjecture
