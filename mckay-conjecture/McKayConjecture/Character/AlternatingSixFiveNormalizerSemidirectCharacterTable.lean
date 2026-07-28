/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CyclicFiveInversionSemidirectCharacterTable
import McKayConjecture.Character.CyclicThreeCharacterTable
import McKayConjecture.Character.DirectProductCorrespondence

/-!
# The 24-row character enumeration of `C₃ × (C₅ ⋊ C₄)`

The normalizer model used for the five-local `A₆` calculation is a direct
product.  Its complete ordinary and `5'`-character row enumerations are
therefore the external tensor products of the three explicit cyclic rows
and the eight explicit inversion semidirect-product rows.

This file supplies:

* 24 explicit finite-dimensional representations;
* complete ordinary and `5'`-character enumerations;
* factorized character-value formulas and exact degree formulas; and
* a `FiniteCharacterTableCertificate` for the whole table.

There are twelve degree-one rows and twelve degree-two rows, so every
ordinary irreducible row has degree prime to five.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace AlternatingSixFiveNormalizerSemidirectCharacterTable

/-- The concrete order-sixty normalizer model. -/
abbrev Group :=
  CyclicThree.Group × CyclicFiveInversionSemidirect.Group

/-- The 24 row indices: three cyclic twists of each of the eight
dicyclic rows. -/
abbrev CharacterRow :=
  Fin 3 × CyclicFiveInversionSemidirect.CharacterRow

/-- The explicit representation attached to a product row. -/
def rowFDRep (r : CharacterRow) : FDRep ℂ Group :=
  FDRep.externalTensor
    (CyclicThree.linearFDRep r.1)
    (CyclicFiveInversionSemidirect.rowFDRep r.2)

theorem rowFDRep_simple (r : CharacterRow) :
    Simple (rowFDRep r) := by
  letI : Simple (CyclicThree.linearFDRep r.1) :=
    CyclicThree.linearFDRep_simple r.1
  letI :
      Simple
        (CyclicFiveInversionSemidirect.rowFDRep r.2) :=
    CyclicFiveInversionSemidirect.rowFDRep_simple r.2
  exact
    FDRep.externalTensor_simple
      (CyclicThree.linearFDRep r.1)
      (CyclicFiveInversionSemidirect.rowFDRep r.2)

@[simp]
theorem rowFDRep_character
    (r : CharacterRow)
    (z : CyclicThree.Group)
    (g : CyclicFiveInversionSemidirect.Group) :
    (rowFDRep r).character (z, g) =
      (CyclicThree.linearHom r.1 z : ℂ) *
        (CyclicFiveInversionSemidirect.rowFDRep r.2).character g := by
  rw [rowFDRep, FDRep.externalTensor_character,
    CyclicThree.linearFDRep_character]

@[simp]
theorem rowFDRep_finrank_linear
    (j : Fin 3) (k : Fin 4) :
    Module.finrank ℂ
        (rowFDRep
          (j,
            CyclicFiveInversionSemidirect.CharacterRow.linear k)) =
      1 := by
  rw [rowFDRep, FDRep.externalTensor_finrank,
    CyclicThree.linearFDRep_finrank,
    CyclicFiveInversionSemidirect.rowFDRep_finrank_linear]

@[simp]
theorem rowFDRep_finrank_twoDimensional
    (j : Fin 3) (k : Fin 4) :
    Module.finrank ℂ
        (rowFDRep
          (j,
            CyclicFiveInversionSemidirect.CharacterRow.twoDimensional k)) =
      2 := by
  rw [rowFDRep, FDRep.externalTensor_finrank,
    CyclicThree.linearFDRep_finrank,
    CyclicFiveInversionSemidirect.rowFDRep_finrank_twoDimensional]

/-- Complete ordinary character enumeration, obtained from the two factor
tables and the direct-product classification theorem. -/
def irreducibleCharacterEquiv :
    CharacterRow ≃ IrreducibleCharacter Group :=
  (Equiv.prodCongr
      CyclicThree.irreducibleCharacterEquiv
      CyclicFiveInversionSemidirect.irreducibleCharacterEquiv).trans
    IrreducibleCharacter.directProductEquiv

@[simp]
theorem irreducibleCharacterEquiv_apply
    (r : CharacterRow) :
    irreducibleCharacterEquiv r =
      IrreducibleCharacter.externalTensor
        (CyclicThree.irreducibleCharacterEquiv r.1)
        (CyclicFiveInversionSemidirect.irreducibleCharacterEquiv
          r.2) :=
  rfl

local instance alternatingSixFiveNormalizerTableFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- Complete `5'`-degree enumeration of all 24 rows. -/
def pPrimeCharacterEquiv :
    CharacterRow ≃ PPrimeIrreducibleCharacter Group 5 :=
  (Equiv.prodCongr
      CyclicThree.pPrimeCharacterEquiv
      CyclicFiveInversionSemidirect.pPrimeCharacterEquiv).trans
    (IrreducibleCharacter.directProductPPrimeEquiv 5)

@[simp]
theorem pPrimeCharacterEquiv_apply
    (r : CharacterRow) :
    pPrimeCharacterEquiv r =
      IrreducibleCharacter.externalTensorPPrime 5
        (CyclicThree.pPrimeCharacterEquiv r.1)
        (CyclicFiveInversionSemidirect.pPrimeCharacterEquiv
          r.2) :=
  rfl

@[simp]
theorem pPrimeCharacterEquiv_values
    (r : CharacterRow)
    (z : CyclicThree.Group)
    (g : CyclicFiveInversionSemidirect.Group) :
    (pPrimeCharacterEquiv r).1.values (z, g) =
      (CyclicThree.pPrimeCharacterEquiv r.1).1.values z *
        (CyclicFiveInversionSemidirect.pPrimeCharacterEquiv
          r.2).1.values g := by
  rw [pPrimeCharacterEquiv_apply,
    IrreducibleCharacter.externalTensorPPrime_coe,
    IrreducibleCharacter.externalTensor_values]

@[simp]
theorem pPrimeCharacterEquiv_degree_linear
    (j : Fin 3) (k : Fin 4) :
    (pPrimeCharacterEquiv
        (j,
          CyclicFiveInversionSemidirect.CharacterRow.linear k)).1.degree =
      1 := by
  rw [pPrimeCharacterEquiv_apply,
    IrreducibleCharacter.externalTensorPPrime_coe,
    IrreducibleCharacter.externalTensor_degree,
    CyclicThree.pPrimeCharacterEquiv_degree,
    CyclicFiveInversionSemidirect.pPrimeCharacterEquiv_degree_linear]

@[simp]
theorem pPrimeCharacterEquiv_degree_twoDimensional
    (j : Fin 3) (k : Fin 4) :
    (pPrimeCharacterEquiv
        (j,
          CyclicFiveInversionSemidirect.CharacterRow.twoDimensional k)).1.degree =
      2 := by
  rw [pPrimeCharacterEquiv_apply,
    IrreducibleCharacter.externalTensorPPrime_coe,
    IrreducibleCharacter.externalTensor_degree,
    CyclicThree.pPrimeCharacterEquiv_degree,
    CyclicFiveInversionSemidirect.pPrimeCharacterEquiv_degree_twoDimensional]

/-- The normalized certificate attached to an explicit product row. -/
def rowCertificate (r : CharacterRow) :
    CharacterRowCertificate Group := by
  letI : Simple (rowFDRep r) := rowFDRep_simple r
  exact CharacterRowCertificate.ofSimple (rowFDRep r)

theorem rowCertificate_irreducibleCharacter
    (r : CharacterRow) :
    (rowCertificate r).irreducibleCharacter =
      irreducibleCharacterEquiv r := by
  apply IrreducibleCharacter.ext
  funext x
  obtain ⟨z, g⟩ := x
  rw [(rowCertificate r).irreducibleCharacter_values_apply]
  change
    (rowFDRep r).character (z, g) =
      (irreducibleCharacterEquiv r).values (z, g)
  rw [rowFDRep, FDRep.externalTensor_character]
  rw [irreducibleCharacterEquiv_apply,
    IrreducibleCharacter.externalTensor_values]
  rw [CyclicThree.irreducibleCharacterEquiv_apply,
    ← CyclicFiveInversionSemidirect.rowCertificate_irreducibleCharacter,
    (CyclicFiveInversionSemidirect.rowCertificate
      r.2).irreducibleCharacter_values_apply]
  change
    (CyclicThree.linearFDRep r.1).character z *
        (CyclicFiveInversionSemidirect.rowFDRep r.2).character g =
      (CyclicThree.linearCharacter r.1).values z *
        (CyclicFiveInversionSemidirect.rowFDRep r.2).character g
  rw [CyclicThree.linearFDRep_character]
  change
    (CyclicThree.linearHom r.1 z : ℂ) *
        (CyclicFiveInversionSemidirect.rowFDRep r.2).character g =
      (IrreducibleCharacter.linear
          (CyclicThree.linearHom r.1)).values z *
        (CyclicFiveInversionSemidirect.rowFDRep r.2).character g
  rw [IrreducibleCharacter.linear_values]

/-- The complete generic finite-table certificate for all 24 product
representations. -/
def finiteCharacterTableCertificate :
    FiniteCharacterTableCertificate Group CharacterRow where
  row := rowCertificate
  row_injective := by
    intro r s hrs
    change
      (rowCertificate r).irreducibleCharacter =
        (rowCertificate s).irreducibleCharacter at hrs
    apply irreducibleCharacterEquiv.injective
    rw [← rowCertificate_irreducibleCharacter r,
      ← rowCertificate_irreducibleCharacter s]
    exact hrs
  row_count := by
    calc
      Nat.card CharacterRow =
          Nat.card (IrreducibleCharacter Group) :=
        Nat.card_congr irreducibleCharacterEquiv
      _ = Nat.card (ConjClasses Group) :=
        ClassFunction.natCard_irreducibleCharacter_eq_conjClasses

/-- The model normalizer has exactly 24 ordinary irreducible characters. -/
@[simp]
theorem natCard_irreducibleCharacter :
    Nat.card (IrreducibleCharacter Group) = 24 := by
  calc
    Nat.card (IrreducibleCharacter Group) =
        Nat.card CharacterRow :=
      Nat.card_congr irreducibleCharacterEquiv.symm
    _ = 24 := by
      rw [Nat.card_eq_fintype_card]
      decide

/-- All 24 ordinary rows have `5'` degree. -/
@[simp]
theorem natCard_pPrimeIrreducibleCharacter :
    Nat.card (PPrimeIrreducibleCharacter Group 5) = 24 := by
  calc
    Nat.card (PPrimeIrreducibleCharacter Group 5) =
        Nat.card CharacterRow :=
      Nat.card_congr pPrimeCharacterEquiv.symm
    _ = 24 := by
      rw [Nat.card_eq_fintype_card]
      decide

end AlternatingSixFiveNormalizerSemidirectCharacterTable
end McKayConjecture
