/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Finiteness
import McKayConjecture.Statement

/-!
# Finite-cardinality form of the McKay statement

The public statement deliberately uses `Cardinal.mk` so it remains meaningful
before finiteness is established.  Once Schur orthogonality supplies
finiteness, it is equivalent to the familiar equality of natural-number
cardinalities.
-/

noncomputable section

universe u

namespace McKayConjecture.Statement

variable {G : Type u} [Finite G] [Group G] {p : ℕ} [Fact p.Prime]
variable (P : Sylow p G)

/-- The cardinal-valued statement is equivalent to equality of finite natural
cardinalities. -/
theorem iff_natCard_eq :
    Statement G p P ↔
      Nat.card (PPrimeIrreducibleCharacter G p) =
        Nat.card
          (PPrimeIrreducibleCharacter (SylowNormalizer P) p) := by
  letI : Fintype (PPrimeIrreducibleCharacter G p) :=
    Fintype.ofFinite _
  letI : Fintype
      (PPrimeIrreducibleCharacter (SylowNormalizer P) p) :=
    Fintype.ofFinite _
  simp only [Statement, Cardinal.mk_fintype, Nat.card_eq_fintype_card]
  norm_cast

end McKayConjecture.Statement
