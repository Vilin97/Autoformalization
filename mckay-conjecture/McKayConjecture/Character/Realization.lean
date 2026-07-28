/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.IrreducibleCharacter

/-!
# Realizations and degrees of ordinary irreducible characters

An `IrreducibleCharacter` only remembers its values and natural-number degree.
This file chooses one realizing simple representation when a representation is
needed, while keeping equality of characters independent of that choice.
-/

noncomputable section

open CategoryTheory

universe u

namespace McKayConjecture.IrreducibleCharacter

variable {G : Type u} [Group G]

/-- A chosen simple finite-dimensional representation realizing `χ`. -/
def realization (χ : IrreducibleCharacter G) : FDRep ℂ G :=
  χ.isIrreducible.choose

/-- The chosen realization of an irreducible character is simple. -/
instance realizationSimple (χ : IrreducibleCharacter G) : Simple χ.realization :=
  χ.isIrreducible.choose_spec.1

/-- The character of the chosen realization is the given character. -/
@[simp]
theorem realization_character (χ : IrreducibleCharacter G) :
    χ.realization.character = χ.values :=
  χ.isIrreducible.choose_spec.2.1

/-- The dimension of the chosen realization is the certified degree. -/
@[simp]
theorem realization_finrank (χ : IrreducibleCharacter G) :
    Module.finrank ℂ χ.realization = χ.degree :=
  χ.isIrreducible.choose_spec.2.2

/-- The degree of an ordinary irreducible character is positive. -/
theorem degree_pos (χ : IrreducibleCharacter G) : 0 < χ.degree := by
  rw [← χ.realization_finrank]
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  by_contra h
  push Not at h
  exact id_nonzero χ.realization (by
    apply ConcreteCategory.hom_ext
    intro x
    change x = 0
    exact h x)

/-- The degree of an ordinary irreducible character is nonzero. -/
theorem degree_ne_zero (χ : IrreducibleCharacter G) : χ.degree ≠ 0 :=
  χ.degree_pos.ne'

/-- The value of an ordinary irreducible character at the identity is nonzero. -/
theorem value_one_ne_zero (χ : IrreducibleCharacter G) : χ.values 1 ≠ 0 := by
  rw [χ.value_one, Nat.cast_ne_zero]
  exact χ.degree_ne_zero

end McKayConjecture.IrreducibleCharacter
