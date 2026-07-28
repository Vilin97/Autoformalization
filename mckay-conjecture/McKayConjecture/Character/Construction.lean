/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Realization

/-!
# Constructing irreducible characters from simple representations

This is the inverse-facing companion to `IrreducibleCharacter.realization`.
It lets representation-theoretic constructions return an element of `Irr`.
-/

noncomputable section

open CategoryTheory

universe u

namespace McKayConjecture.IrreducibleCharacter

variable {G : Type u} [Group G]

/-- The irreducible character afforded by a simple finite-dimensional
complex representation. -/
def ofSimple (V : FDRep ℂ G) [Simple V] :
    IrreducibleCharacter G where
  values := V.character
  degree := Module.finrank ℂ V
  isIrreducible := ⟨V, inferInstance, rfl, rfl⟩

@[simp]
theorem ofSimple_values (V : FDRep ℂ G) [Simple V] :
    (ofSimple V).values = V.character :=
  rfl

@[simp]
theorem ofSimple_values_apply (V : FDRep ℂ G) [Simple V]
    (g : G) :
    (ofSimple V).values g = V.character g :=
  rfl

@[simp]
theorem ofSimple_degree (V : FDRep ℂ G) [Simple V] :
    (ofSimple V).degree = Module.finrank ℂ V :=
  rfl

/-- Isomorphic simple representations afford the same irreducible
character. -/
theorem ofSimple_eq_of_iso
    (V W : FDRep ℂ G) [Simple V] [Simple W]
    (i : V ≅ W) :
    ofSimple V = ofSimple W := by
  apply IrreducibleCharacter.ext
  exact FDRep.char_iso i

/-- Recovering the character from its chosen realization changes nothing. -/
@[simp]
theorem ofSimple_realization
    (χ : IrreducibleCharacter G) :
    ofSimple χ.realization = χ := by
  apply IrreducibleCharacter.ext
  exact χ.realization_character

/-- Package a simple representation whose dimension is prime to `p` as a
`p'`-degree irreducible character. -/
def pPrimeOfSimple (p : ℕ) (V : FDRep ℂ G) [Simple V]
    (hV : ¬p ∣ Module.finrank ℂ V) :
    PPrimeIrreducibleCharacter G p :=
  ⟨ofSimple V, hV⟩

@[simp]
theorem pPrimeOfSimple_degree
    (p : ℕ) (V : FDRep ℂ G) [Simple V]
    (hV : ¬p ∣ Module.finrank ℂ V) :
    (pPrimeOfSimple p V hV).1.degree =
      Module.finrank ℂ V :=
  rfl

end McKayConjecture.IrreducibleCharacter
