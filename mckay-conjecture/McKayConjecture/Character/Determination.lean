/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Finiteness

/-!
# Irreducible representations are determined by their characters

Over the complex numbers, two irreducible finite-dimensional
representations of a finite group are isomorphic exactly when their
characters agree.  Mathlib contains the forward implication and Schur
orthogonality; this file records the converse in the form needed to choose
intertwining operators for invariant characters.
-/

noncomputable section

open CategoryTheory

universe u

namespace McKayConjecture

variable {G : Type u} [Group G]

/-- Two simple finite-dimensional complex representations with equal
characters are isomorphic. -/
theorem FDRep.nonempty_iso_of_character_eq
    [Finite G] (V W : FDRep ℂ G) [Simple V] [Simple W]
    (hchar : V.character = W.character) :
    Nonempty (V ≅ W) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  classical
  by_contra hno
  have hVW := FDRep.char_orthonormal V W
  have hVV := FDRep.char_orthonormal V V
  simp only [hno, ↓reduceIte] at hVW
  have hself : Nonempty (V ≅ V) := ⟨Iso.refl V⟩
  simp only [hself, ↓reduceIte] at hVV
  rw [hchar] at hVW
  rw [hchar] at hVV
  exact one_ne_zero (hVV.symm.trans hVW)

/-- Equality of irreducible characters is equivalent to isomorphism of their
chosen realizations. -/
theorem IrreducibleCharacter.realization_nonempty_iso_iff
    (χ ψ : IrreducibleCharacter G) :
    Nonempty (χ.realization ≅ ψ.realization) ↔ χ = ψ := by
  constructor
  · rintro ⟨i⟩
    apply IrreducibleCharacter.ext
    rw [← χ.realization_character, ← ψ.realization_character]
    exact FDRep.char_iso i
  · intro h
    subst ψ
    exact ⟨Iso.refl _⟩

end McKayConjecture
