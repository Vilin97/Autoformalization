/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerFixedPointCongruence
import McKayConjecture.Character.BrauerInductionCosetFormula

/-!
# Fixed-coset values of induced class functions

This file packages the final counting calculation in Bernstein's local
construction.  If the coset summands of an induced class function are a
constant on the fixed cosets of a `p`-element and zero elsewhere, then its
value is that constant times the number of fixed cosets.  When the subgroup
contains a Sylow `p`-subgroup, that value is prime to `p`.

The remaining group-specific work in Brauer induction is therefore reduced
to proving the concrete support identity for the regular-fibre class
function on the elementary subgroup of a centralizer.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

open MulAction

variable {p : ℕ}
variable {G : Type*} [Group G]

noncomputable local instance brauerFixedValueQuotientFintype
    [Fintype G] (S : Subgroup G) :
    Fintype (G ⧸ S) :=
  Fintype.ofFinite _

/-- The function on `G ⧸ S` which has value `m` on the cosets fixed by
`t` and vanishes on all other cosets. -/
noncomputable def fixedCosetIndicator
    (S : Subgroup G) (t : G) (m : ℕ) (q : G ⧸ S) :
    ℂ := by
  classical
  exact
    if q ∈ fixedBy (G ⧸ S) t
    then (m : ℂ) else 0

/-- If the induction summands are `m` precisely on the fixed cosets of
`t`, the induced value is `m` times the number of those fixed cosets. -/
theorem induce_apply_eq_card_fixedBy_mul
    [Fintype G]
    (S : Subgroup G) (θ : ClassFunction S)
    (x t : G) (m : ℕ)
    (hterm :
      ∀ q : G ⧸ S,
        inductionTerm S θ q.out x =
          fixedCosetIndicator S t m q) :
    induce S θ x =
      (Nat.card (fixedBy (G ⧸ S) t) : ℂ) *
        (m : ℂ) := by
  classical
  rw [induce_apply_eq_sum_quotient]
  simp_rw [hterm, fixedCosetIndicator]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul,
    Nat.card_eq_fintype_card,
    Fintype.card_subtype]

/-- The prime-to-`p` conclusion of Bernstein's fixed-point calculation.
The natural number furnishing the induced value is explicitly the product
of the regular-fibre constant and the number of fixed cosets. -/
theorem exists_coprime_nat_induced_value_of_fixedBy_indicator
    [Fintype G] [Fact p.Prime]
    (P : Sylow p G) (S : Subgroup G)
    (hPS : (P : Subgroup G) ≤ S)
    (θ : ClassFunction S)
    (x t : G) (ht : IsPElement p t)
    (m : ℕ) (hm : p.Coprime m)
    (hterm :
      ∀ q : G ⧸ S,
        inductionTerm S θ q.out x =
          fixedCosetIndicator S t m q) :
    ∃ k : ℕ, p.Coprime k ∧
      induce S θ x = (k : ℂ) := by
  let fixedCard : ℕ :=
    Nat.card (fixedBy (G ⧸ S) t)
  have hfixed :
      p.Coprime fixedCard := by
    exact
      coprime_card_fixedBy_quotient_of_sylow_le
        P S hPS ht
  refine
    ⟨fixedCard * m,
      Nat.coprime_mul_iff_right.mpr ⟨hfixed, hm⟩,
      ?_⟩
  rw [induce_apply_eq_card_fixedBy_mul
    S θ x t m hterm]
  simp [fixedCard, Nat.cast_mul]

end ClassFunction
end McKayConjecture
