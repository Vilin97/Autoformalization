/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.PGroup

/-!
# Coprimality for finite fields and finite p-groups

If `K` is a finite field of characteristic `p`, then `|Kˣ|` is
prime to the order of every finite `p`-group.  This is the arithmetic
input for splitting projective factor sets over `K`.
-/

namespace McKayConjecture
namespace CharacterTriple

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} {P : Type v}
variable [Field K] [Finite K] [CharP K p]
variable [Group P] [Finite P]

/-- The multiplicative group of a finite field of characteristic `p`
has order coprime to every finite `p`-group. -/
theorem finiteField_units_card_coprime_pGroup
    (hP : IsPGroup p P) :
    Nat.Coprime (Nat.card Kˣ) (Nat.card P) := by
  letI := Fintype.ofFinite K
  obtain ⟨n, hp, hK⟩ :=
    FiniteField.card K p
  obtain ⟨m, hPcard⟩ :=
    IsPGroup.iff_card.mp hP
  rw [Nat.card_units, Nat.card_eq_fintype_card,
    hK, hPcard]
  have hpow_coprime :
      Nat.Coprime (p ^ (n : ℕ) - 1) (p ^ (n : ℕ)) := by
    rw [Nat.coprime_self_sub_left]
    · exact Nat.coprime_one_left _
    · exact Nat.one_le_pow _ _ hp.pos
  have hp_coprime :
      Nat.Coprime (p ^ (n : ℕ) - 1) p :=
    hpow_coprime.of_dvd_right
      (dvd_pow_self p n.ne_zero)
  exact hp_coprime.pow_right m

end CharacterTriple
end McKayConjecture
