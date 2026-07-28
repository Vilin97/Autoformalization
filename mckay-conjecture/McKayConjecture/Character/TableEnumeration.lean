/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.IrreducibleCharacterBasis

/-!
# Completing explicit finite character tables

This file packages two recurring bookkeeping steps for concrete character
tables.

* An injective list of irreducible characters is complete once its number
  of rows equals the number of conjugacy classes.
* A complete ordinary table restricts canonically to the rows whose degrees
  are prime to a specified prime.

The representation-specific work therefore remains exactly where it
belongs: constructing the rows, proving irreducibility and distinctness,
and computing their degrees.
-/

noncomputable section

namespace McKayConjecture

variable {G I : Type} [Group G] [Finite G] [Finite I]

/-- An injective family of irreducible characters with one row per
conjugacy class is a complete character table. -/
def irreducibleCharacterEquivOfInjective
    (χ : I → IrreducibleCharacter G)
    (hinj : Function.Injective χ)
    (hcard :
      Nat.card I = Nat.card (ConjClasses G)) :
    I ≃ IrreducibleCharacter G :=
  Equiv.ofBijective χ <| by
    apply hinj.bijective_of_nat_card_le
    rw [ClassFunction.natCard_irreducibleCharacter_eq_conjClasses]
    exact hcard.ge

omit [Finite I] in
@[simp]
theorem irreducibleCharacterEquivOfInjective_apply
    (χ : I → IrreducibleCharacter G)
    (hinj : Function.Injective χ)
    (hcard :
      Nat.card I = Nat.card (ConjClasses G))
    (i : I) :
    irreducibleCharacterEquivOfInjective χ hinj hcard i = χ i :=
  rfl

/-- Row indices of an ordinary table whose corresponding degrees are
prime to `p`. -/
def PPrimeCharacterRow
    (p : ℕ) (e : I ≃ IrreducibleCharacter G) :=
  {i : I // ¬p ∣ (e i).degree}

/-- Restrict a complete ordinary character table to its `p'`-degree rows. -/
def pPrimeCharacterEquivOfIrreducibleCharacterEquiv
    (p : ℕ) (e : I ≃ IrreducibleCharacter G) :
    PPrimeCharacterRow p e ≃
      PPrimeIrreducibleCharacter G p where
  toFun i := ⟨e i.1, i.2⟩
  invFun χ :=
    ⟨e.symm χ.1, by
      have hp := χ.2
      rw [IrreducibleCharacter.IsPPrimeDegree] at hp
      simpa using hp⟩
  left_inv i := by
    apply Subtype.ext
    exact e.symm_apply_apply i.1
  right_inv χ := by
    apply Subtype.ext
    exact e.apply_symm_apply χ.1

omit [Finite G] [Finite I] in
@[simp]
theorem pPrimeCharacterEquivOfIrreducibleCharacterEquiv_apply
    (p : ℕ) (e : I ≃ IrreducibleCharacter G)
    (i : PPrimeCharacterRow p e) :
    (pPrimeCharacterEquivOfIrreducibleCharacterEquiv p e i).1 =
      e i.1 :=
  rfl

omit [Finite G] [Finite I] in
/-- The number of `p'`-degree irreducible characters can be counted on any
complete ordinary table. -/
theorem natCard_pPrimeIrreducibleCharacter_eq_tableRows
    (p : ℕ) (e : I ≃ IrreducibleCharacter G) :
    Nat.card (PPrimeIrreducibleCharacter G p) =
      Nat.card (PPrimeCharacterRow p e) :=
  Nat.card_congr
    (pPrimeCharacterEquivOfIrreducibleCharacterEquiv p e).symm

end McKayConjecture
