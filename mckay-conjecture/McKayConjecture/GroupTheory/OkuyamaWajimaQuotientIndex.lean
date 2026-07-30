/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.OkuyamaWajimaQuotient

/-!
# Index transport for the Okuyama--Wajima quotient equivalence

The second-isomorphism equivalence used in the Okuyama--Wajima
argument immediately identifies the two subgroup indices which occur
in the full fixed-point branch:

`[U : K ∩ C_A(S)] = [U ⊔ K : K]`.

Keeping this as a separate character-free lemma avoids carrying an
otherwise redundant numerical hypothesis through the character
extension argument.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {A : Type u} [Group A] [Finite A]
variable {p : ℕ}

/-- The Okuyama--Wajima quotient equivalence identifies the index of
the fixed-point kernel in `U` with the index of `K` in `U ⊔ K`. -/
theorem okuyamaWajima_fixedPoints_index_eq_kernel_index
    (K S : Subgroup A) [K.Normal]
    (hS : IsPGroup p S)
    (hK : IsPPrimeGroup p K)
    (U : Subgroup A)
    (hU : U ≤ Subgroup.normalizer (S : Set A))
    (hfixedU :
      K ⊓ Subgroup.centralizer (S : Set A) ≤ U) :
    ((K ⊓ Subgroup.centralizer (S : Set A)).subgroupOf U).index =
      (K.subgroupOf (U ⊔ K)).index := by
  letI :
      ((K ⊓ Subgroup.centralizer (S : Set A)).subgroupOf U).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hU.trans
        (normalizer_le_normalizer_inf_centralizer K S))
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  exact
    Nat.card_congr
      (okuyamaWajimaQuotientEquiv
        K S hS hK U hU hfixedU).toEquiv

/-- Reverse-oriented form of
`okuyamaWajima_fixedPoints_index_eq_kernel_index`. -/
theorem okuyamaWajima_kernel_index_eq_fixedPoints_index
    (K S : Subgroup A) [K.Normal]
    (hS : IsPGroup p S)
    (hK : IsPPrimeGroup p K)
    (U : Subgroup A)
    (hU : U ≤ Subgroup.normalizer (S : Set A))
    (hfixedU :
      K ⊓ Subgroup.centralizer (S : Set A) ≤ U) :
    (K.subgroupOf (U ⊔ K)).index =
      ((K ⊓ Subgroup.centralizer (S : Set A)).subgroupOf U).index :=
  (okuyamaWajima_fixedPoints_index_eq_kernel_index
    K S hS hK U hU hfixedU).symm

end GroupTheory
end McKayConjecture
