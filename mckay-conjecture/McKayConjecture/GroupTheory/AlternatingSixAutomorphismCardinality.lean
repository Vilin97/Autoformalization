/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixAutomorphismImagePairs
import McKayConjecture.GroupTheory.UniversalCentralExtensionAutomorphismEquiv

/-!
# A cardinality upper bound for the automorphism group of `A₆`

An automorphism of `A₆` is determined by the images of the two standard
generators.  `AlternatingSixAutomorphismImagePairs` injects the automorphism
group into the finite type of pairs satisfying the four presentation
relations.  This file computes that candidate type in six blocks, according
to the image of `0` under the first generator image.

The split keeps every executable certificate within the default heartbeat
budget.  The resulting upper bound

`|Aut(A₆)| ≤ 1440`

is the cardinality half of the eventual classification of automorphisms of
`A₆` by its inner automorphisms and two audited outer generators.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

open scoped BigOperators

/-- The block in which the first generator image fixes `0` has size `480`. -/
theorem alternatingSixAutomorphismImagePairBlockCard_zero :
    alternatingSixAutomorphismImagePairBlockCard 0 = 480 := by
  native_decide

/-- The block in which the first generator image sends `0` to `1` has size
`192`. -/
theorem alternatingSixAutomorphismImagePairBlockCard_one :
    alternatingSixAutomorphismImagePairBlockCard 1 = 192 := by
  native_decide

/-- The block in which the first generator image sends `0` to `2` has size
`192`. -/
theorem alternatingSixAutomorphismImagePairBlockCard_two :
    alternatingSixAutomorphismImagePairBlockCard 2 = 192 := by
  native_decide

/-- The block in which the first generator image sends `0` to `3` has size
`192`. -/
theorem alternatingSixAutomorphismImagePairBlockCard_three :
    alternatingSixAutomorphismImagePairBlockCard 3 = 192 := by
  native_decide

/-- The block in which the first generator image sends `0` to `4` has size
`192`. -/
theorem alternatingSixAutomorphismImagePairBlockCard_four :
    alternatingSixAutomorphismImagePairBlockCard 4 = 192 := by
  native_decide

/-- The block in which the first generator image sends `0` to `5` has size
`192`. -/
theorem alternatingSixAutomorphismImagePairBlockCard_five :
    alternatingSixAutomorphismImagePairBlockCard 5 = 192 := by
  native_decide

/-- Summing the six first-image blocks recovers the nested candidate-pair
count. -/
theorem sum_alternatingSixAutomorphismImagePairBlockCard :
    (∑ i : Fin 6,
      alternatingSixAutomorphismImagePairBlockCard i) =
      ∑ x : AlternatingSix,
        alternatingSixAutomorphismSecondImageCard x := by
  simp only [alternatingSixAutomorphismImagePairBlockCard]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

/-- Exactly `1440` pairs satisfy the necessary generator-image relations for
an automorphism of `A₆`. -/
theorem natCard_alternatingSixAutomorphismImagePair_eq_1440 :
    Nat.card AlternatingSixAutomorphismImagePair = 1440 := by
  rw [natCard_alternatingSixAutomorphismImagePair]
  rw [← sum_alternatingSixAutomorphismImagePairBlockCard]
  native_decide

/-- The automorphism group of `A₆` has order at most `1440`. -/
theorem natCard_mulAut_alternatingSix_le_1440 :
    Nat.card (MulAut AlternatingSix) ≤ 1440 := by
  calc
    Nat.card (MulAut AlternatingSix) ≤
        Nat.card AlternatingSixAutomorphismImagePair :=
      Nat.card_le_card_of_injective
        alternatingSixMulAutToImagePair
        alternatingSixMulAutToImagePair_injective
    _ = 1440 :=
      natCard_alternatingSixAutomorphismImagePair_eq_1440

/-- Automorphisms of the canonical universal cover descend uniquely to
automorphisms of `A₆`. -/
def alternatingSixUniversalCoverAutomorphismMulEquiv :
    MulAut AlternatingSixUniversalCover ≃*
      MulAut AlternatingSix :=
  alternatingSixUniversalCentralExtension
    |>.sourceAutomorphismMulEquivTarget
      (inferInstance : IsSimpleGroup AlternatingSix)
      alternatingSix_not_isMulCommutative

/-- The automorphism group of the canonical universal cover of `A₆` also
has order at most `1440`. -/
theorem natCard_mulAut_alternatingSixUniversalCover_le_1440 :
    Nat.card (MulAut AlternatingSixUniversalCover) ≤ 1440 := by
  rw [
    Nat.card_congr
      alternatingSixUniversalCoverAutomorphismMulEquiv.toEquiv
  ]
  exact natCard_mulAut_alternatingSix_le_1440

end GroupTheory
end McKayConjecture
