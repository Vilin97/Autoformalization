/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.NormalizedCharacterCertificate
import McKayConjecture.Character.TableEnumeration

/-!
# Certificates for complete explicit finite character tables

This file assembles individually certified rows into a complete ordinary
character table.  The only remaining inputs are:

* distinct row indices give distinct irreducible characters; and
* the number of rows is the number of conjugacy classes.

Completeness then follows from the existing theorem that a finite group has as
many irreducible complex characters as conjugacy classes.  The resulting
equivalence also restricts canonically to the rows of `p'` degree.
-/

noncomputable section

namespace McKayConjecture

variable {G I : Type} [Group G] [Finite G] [Finite I]

/-- A kernel-checked certificate for a complete ordinary character table.

The family `row` contains the representation and norm-one proof for each row.
`row_injective` is the pairwise-distinctness check, and `row_count` is the
conjugacy-class count. -/
structure FiniteCharacterTableCertificate
    (G I : Type) [Group G] [Finite G] [Finite I] where
  /-- The individually certified table rows. -/
  row : I → CharacterRowCertificate G
  /-- Distinct indices afford distinct characters. -/
  row_injective :
    Function.Injective
      (fun i ↦ (row i).irreducibleCharacter)
  /-- The table has one row per conjugacy class. -/
  row_count :
    Nat.card I = Nat.card (ConjClasses G)

namespace FiniteCharacterTableCertificate

variable (T : FiniteCharacterTableCertificate G I)

/-- The irreducible character attached to a table row. -/
def character (i : I) : IrreducibleCharacter G :=
  (T.row i).irreducibleCharacter

@[simp]
theorem character_values (i : I) :
    (T.character i).values =
      (T.row i).representation.character :=
  (T.row i).irreducibleCharacter_values

@[simp]
theorem character_values_apply (i : I) (g : G) :
    (T.character i).values g =
      (T.row i).representation.character g :=
  (T.row i).irreducibleCharacter_values_apply g

@[simp]
theorem character_degree (i : I) :
    (T.character i).degree =
      Module.finrank ℂ (T.row i).representation :=
  (T.row i).irreducibleCharacter_degree

/-- A certified complete table enumerates all ordinary irreducible
characters. -/
def irreducibleCharacterEquiv :
    I ≃ IrreducibleCharacter G :=
  irreducibleCharacterEquivOfInjective
    T.character
    (by
      intro i j hij
      exact T.row_injective hij)
    T.row_count

@[simp]
theorem irreducibleCharacterEquiv_apply (i : I) :
    T.irreducibleCharacterEquiv i = T.character i :=
  rfl

/-- The row indices whose certified character degrees are prime to `p`. -/
abbrev PPrimeRow (p : ℕ) :=
  PPrimeCharacterRow p T.irreducibleCharacterEquiv

/-- Restrict a certified complete ordinary table to its `p'`-degree rows. -/
def pPrimeIrreducibleCharacterEquiv (p : ℕ) :
    T.PPrimeRow p ≃ PPrimeIrreducibleCharacter G p :=
  pPrimeCharacterEquivOfIrreducibleCharacterEquiv
    p T.irreducibleCharacterEquiv

@[simp]
theorem pPrimeIrreducibleCharacterEquiv_apply
    (p : ℕ) (i : T.PPrimeRow p) :
    (T.pPrimeIrreducibleCharacterEquiv p i).1 =
      T.character i.1 :=
  rfl

/-- Membership in the filtered row type can be checked on the dimension of
the explicit representation rather than on the packaged character. -/
theorem mem_pPrimeRow_iff
    (p : ℕ) (i : I) :
    (¬p ∣ (T.irreducibleCharacterEquiv i).degree) ↔
      ¬p ∣ Module.finrank ℂ (T.row i).representation := by
  rw [T.irreducibleCharacterEquiv_apply,
    T.character_degree]

/-- Count `p'`-degree irreducible characters using the filtered certified
table rows. -/
theorem natCard_pPrimeIrreducibleCharacter_eq_rows
    (p : ℕ) :
    Nat.card (PPrimeIrreducibleCharacter G p) =
      Nat.card (T.PPrimeRow p) :=
  natCard_pPrimeIrreducibleCharacter_eq_tableRows
    p T.irreducibleCharacterEquiv

end FiniteCharacterTableCertificate
end McKayConjecture
