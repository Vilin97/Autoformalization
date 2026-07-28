/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryRows

/-!
# Prime-to-`p` rows in the ordinary table of `6.A₆`

The thirty-one ordinary rows have dimensions recorded independently of their
irreducibility proofs.  This file filters those indices arithmetically and
checks the three relevant cardinalities.
-/

namespace McKayConjecture
namespace InductiveMcKay

/-- Ordinary ambient rows whose matrix dimension is prime to `p`. -/
abbrev AlternatingSixAmbientPPrimeRow (p : ℕ) :=
  {row : AlternatingSixAmbientOrdinaryRow //
    ¬p ∣ row.dimension}

/-- There are twelve odd-degree ambient rows. -/
theorem natCard_alternatingSixAmbientPPrimeRow_two :
    Nat.card (AlternatingSixAmbientPPrimeRow 2) = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- There are twelve ambient rows of degree prime to three. -/
theorem natCard_alternatingSixAmbientPPrimeRow_three :
    Nat.card (AlternatingSixAmbientPPrimeRow 3) = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- There are twenty-four ambient rows of degree prime to five. -/
theorem natCard_alternatingSixAmbientPPrimeRow_five :
    Nat.card (AlternatingSixAmbientPPrimeRow 5) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide

end InductiveMcKay
end McKayConjecture
