/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Data.Complex.Basic
import Mathlib.RepresentationTheory.Character

/-!
# Ordinary irreducible complex characters

This file packages an ordinary irreducible complex character together with its
(natural-number-valued) degree.  The witness field ensures that the values and
degree come from one simple finite-dimensional complex representation.
-/

noncomputable section

open CategoryTheory

universe u

namespace McKayConjecture

variable (G : Type u) [Group G]

/-- An ordinary irreducible complex character of `G`.

Equality is equality of the character values and degree, rather than equality
of a chosen representation.  Thus isomorphic representations, and more
generally any representations with the same character, determine the same
element of this type.
-/
structure IrreducibleCharacter where
  /-- The values of the character on elements of the group. -/
  values : G → ℂ
  /-- The character degree, equivalently the dimension of a realizing representation. -/
  degree : ℕ
  /-- A simple finite-dimensional complex representation realizing the data. -/
  isIrreducible :
    ∃ V : FDRep ℂ G,
      Simple V ∧
        V.character = values ∧
          Module.finrank ℂ V = degree

namespace IrreducibleCharacter

variable {G}

/-- Evaluating an irreducible character at the identity gives its degree. -/
@[simp]
theorem value_one (χ : IrreducibleCharacter G) : χ.values 1 = (χ.degree : ℂ) := by
  obtain ⟨V, _, hvalues, hdegree⟩ := χ.isIrreducible
  rw [← hvalues, FDRep.char_one, hdegree]

/-- The character values determine the certified degree. -/
theorem degree_eq_of_values_eq {χ ψ : IrreducibleCharacter G}
    (hvalues : χ.values = ψ.values) : χ.degree = ψ.degree := by
  apply Nat.cast_injective (R := ℂ)
  rw [← χ.value_one, ← ψ.value_one, hvalues]

/-- Irreducible characters are equal when their character functions are equal. -/
@[ext]
theorem ext {χ ψ : IrreducibleCharacter G} (hvalues : χ.values = ψ.values) : χ = ψ := by
  have hdegree := degree_eq_of_values_eq hvalues
  cases χ
  cases ψ
  simp_all

/-- An irreducible character has `p'`-degree when `p` does not divide its degree. -/
def IsPPrimeDegree (p : ℕ) (χ : IrreducibleCharacter G) : Prop :=
  ¬p ∣ χ.degree

end IrreducibleCharacter

/-- The type denoted `Irr_{p'}(G)` in the McKay conjecture. -/
def PPrimeIrreducibleCharacter (p : ℕ) :=
  {χ : IrreducibleCharacter G // χ.IsPPrimeDegree p}

end McKayConjecture
