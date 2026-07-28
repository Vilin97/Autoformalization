/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Proof.NormalSylow

/-!
# The McKay statement when the prime does not divide the group order

If `p ∤ |G|`, the Sylow `p`-subgroup is trivial.  It is therefore normal,
so the normal-Sylow correspondence proves McKay immediately.
-/

noncomputable section

universe u

namespace McKayConjecture

variable {G : Type u} [Group G] [Finite G]
  {p : ℕ} [Fact p.Prime]

/-- A Sylow subgroup is trivial when its prime does not divide the ambient
group order. -/
theorem Sylow.eq_bot_of_not_dvd_card
    (P : Sylow p G) (hp : ¬p ∣ Nat.card G) :
    (P : Subgroup G) = ⊥ := by
  rw [Subgroup.eq_bot_iff_card, P.card_eq_multiplicity,
    Nat.factorization_eq_zero_of_not_dvd hp, pow_zero]

/-- McKay holds whenever `p` does not divide the group order. -/
theorem Statement.of_not_dvd_group_order
    (P : Sylow p G) (hp : ¬p ∣ Nat.card G) :
    Statement G p P := by
  have hP : (P : Subgroup G) = ⊥ :=
    McKayConjecture.Sylow.eq_bot_of_not_dvd_card P hp
  haveI : (P : Subgroup G).Normal := by
    rw [hP]
    infer_instance
  exact Statement.of_normal_sylow P

/-- Coprimality is a convenient sufficient form of the preceding result. -/
theorem Statement.of_coprime_group_order
    (P : Sylow p G) (hp : p.Coprime (Nat.card G)) :
    Statement G p P := by
  apply Statement.of_not_dvd_group_order P
  intro hdvd
  exact (Fact.out : p.Prime).ne_one
    (Nat.eq_one_of_dvd_coprimes hp dvd_rfl hdvd)

end McKayConjecture
