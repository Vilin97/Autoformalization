/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Data.Nat.Prime.Infinite
import McKayConjecture.Character.ElementaryBrauerInductionAutomatic

/-!
# The cyclic base case of elementary Brauer induction

A finite cyclic group is `q`-elementary for any prime `q` which is larger
than its order: take the whole group as the cyclic prime-to-`q` factor and
the trivial subgroup as the `q`-group factor.  This file constructs that
decomposition and obtains denominator-one Brauer induction from induction
at the top subgroup.
-/

noncomputable section

namespace McKayConjecture
namespace ClassFunction

variable {G : Type} [Group G] [Finite G] [IsCyclic G]

/-- A finite cyclic group admits a `q`-elementary decomposition for some
prime `q`: choose `q` larger than the order of its top subgroup. -/
theorem exists_prime_top_pElementaryDecomposition :
    ∃ q : ℕ, q.Prime ∧
      Nonempty
        (PElementaryDecomposition q (⊤ : Subgroup G)) := by
  obtain ⟨q, hq_card, hq⟩ :=
    Nat.exists_infinite_primes
      (Nat.card (⊤ : Subgroup (⊤ : Subgroup G)) + 1)
  have hcard_lt :
      Nat.card (⊤ : Subgroup (⊤ : Subgroup G)) < q := by
    omega
  refine ⟨q, hq, ⟨{
    cyclicPart := ⊤
    pPart := ⊥
    cyclic := inferInstance
    cyclicPart_coprime :=
      Nat.coprime_of_lt_prime
        Nat.card_pos.ne' hcard_lt hq
    isPGroup := IsPGroup.of_bot
    cyclicPart_normal := inferInstance
    pPart_normal := inferInstance
    complementary := Subgroup.isComplement'_top_bot
  }⟩⟩

/-- Denominator-one elementary Brauer induction holds for finite cyclic
groups. -/
theorem hasElementaryBrauerInduction_of_isCyclic :
    HasElementaryBrauerInduction (G := G) := by
  obtain ⟨q, hq, ⟨D⟩⟩ :=
    exists_prime_top_pElementaryDecomposition (G := G)
  exact
    hasElementaryBrauerInduction_of_top_decomposition
      q hq D

end ClassFunction
end McKayConjecture
