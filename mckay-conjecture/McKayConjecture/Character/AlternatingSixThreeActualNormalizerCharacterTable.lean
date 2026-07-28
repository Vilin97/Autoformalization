/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.AlternatingSixThreeNormalizerCharacterTable
import McKayConjecture.Character.Transport

/-!
# Complete character table of the actual three-normalizer

The coordinate table is transported across the proved equivalence with
the fixed Sylow-three normalizer in the canonical universal cover.  This
gives both a complete finite table certificate and the explicit
twelve-row prime-to-three equivalence for the actual local subgroup.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace AlternatingSixThreeNormalizer

open GroupTheory

/-- Transport a displayed coordinate row to the actual fixed
three-normalizer. -/
def actualNormalizerRowCharacter (r : CharacterRow) :
    IrreducibleCharacter
      AlternatingSixUniversalCoverThreeNormalizer :=
  (rowCharacter r).comap
    alternatingSixThreeNormalizerCoordinatesEquivUniversalCoverNormalizer.symm

@[simp]
theorem actualNormalizerRowCharacter_degree (r : CharacterRow) :
    (actualNormalizerRowCharacter r).degree =
      (rowCharacter r).degree := by
  rw [actualNormalizerRowCharacter,
    IrreducibleCharacter.comap_degree]

theorem actualNormalizerRowCharacter_injective :
    Function.Injective actualNormalizerRowCharacter :=
  (IrreducibleCharacter.comapEquiv
      alternatingSixThreeNormalizerCoordinatesEquivUniversalCoverNormalizer.symm).injective.comp
    rowCharacter_injective

/-- Certified row on the actual normalizer, using the transported
character's simple realization. -/
def actualNormalizerRowCertificate (r : CharacterRow) :
    CharacterRowCertificate
      AlternatingSixUniversalCoverThreeNormalizer :=
  CharacterRowCertificate.ofSimple
    (actualNormalizerRowCharacter r).realization

@[simp]
theorem actualNormalizerRowCertificate_irreducibleCharacter
    (r : CharacterRow) :
    (actualNormalizerRowCertificate r).irreducibleCharacter =
      actualNormalizerRowCharacter r := by
  change
    IrreducibleCharacter.ofSimple
        (actualNormalizerRowCharacter r).realization =
      actualNormalizerRowCharacter r
  exact
    IrreducibleCharacter.ofSimple_realization
      (actualNormalizerRowCharacter r)

/-- Complete finite character-table certificate for the actual local
normalizer. -/
def actualNormalizerFiniteCharacterTableCertificate :
    FiniteCharacterTableCertificate
      AlternatingSixUniversalCoverThreeNormalizer CharacterRow where
  row := actualNormalizerRowCertificate
  row_injective := by
    intro r s hrs
    apply actualNormalizerRowCharacter_injective
    rw [← actualNormalizerRowCertificate_irreducibleCharacter r,
      ← actualNormalizerRowCertificate_irreducibleCharacter s]
    exact hrs
  row_count := by
    calc
      Nat.card CharacterRow = 28 := by
        rw [Nat.card_sum, Nat.card_sum,
          Nat.card_prod, Nat.card_prod]
        simp
      _ =
          Nat.card
            (ConjClasses
              AlternatingSixUniversalCoverThreeNormalizer) :=
        natCard_conjClasses_alternatingSixUniversalCoverThreeNormalizer.symm

/-- Complete ordinary irreducible-character enumeration of the actual
normalizer. -/
def actualNormalizerIrreducibleCharacterEquiv :
    CharacterRow ≃
      IrreducibleCharacter
        AlternatingSixUniversalCoverThreeNormalizer :=
  actualNormalizerFiniteCharacterTableCertificate.irreducibleCharacterEquiv

@[simp]
theorem actualNormalizerIrreducibleCharacterEquiv_apply
    (r : CharacterRow) :
    actualNormalizerIrreducibleCharacterEquiv r =
      actualNormalizerRowCharacter r := by
  rw [actualNormalizerIrreducibleCharacterEquiv,
    FiniteCharacterTableCertificate.irreducibleCharacterEquiv_apply,
    FiniteCharacterTableCertificate.character]
  change
    (actualNormalizerRowCertificate r).irreducibleCharacter =
      actualNormalizerRowCharacter r
  exact
    actualNormalizerRowCertificate_irreducibleCharacter r

/-- The twelve explicit coordinate `3'` rows transported to the actual
normalizer. -/
def actualNormalizerPPrimeIrreducibleCharacterEquiv :
    CoordinatePPrimeCharacterRow ≃
      PPrimeIrreducibleCharacter
        AlternatingSixUniversalCoverThreeNormalizer 3 :=
  pPrimeIrreducibleCharacterEquiv.trans
    (IrreducibleCharacter.pPrimeComapEquiv 3
      alternatingSixThreeNormalizerCoordinatesEquivUniversalCoverNormalizer.symm)

@[simp]
theorem actualNormalizerPPrimeIrreducibleCharacterEquiv_degree
    (r : CoordinatePPrimeCharacterRow) :
    (actualNormalizerPPrimeIrreducibleCharacterEquiv r).1.degree =
      (pPrimeIrreducibleCharacterEquiv r).1.degree :=
  rfl

@[simp]
theorem actualNormalizerPPrimeIrreducibleCharacterEquiv_values
    (r : CoordinatePPrimeCharacterRow)
    (g : AlternatingSixThreeNormalizerCoordinates) :
    (actualNormalizerPPrimeIrreducibleCharacterEquiv r).1.values
        (alternatingSixThreeNormalizerCoordinatesEquivUniversalCoverNormalizer g) =
      (pPrimeIrreducibleCharacterEquiv r).1.values g := by
  change
    ((pPrimeIrreducibleCharacterEquiv r).1.comap
      alternatingSixThreeNormalizerCoordinatesEquivUniversalCoverNormalizer.symm).values
        (alternatingSixThreeNormalizerCoordinatesEquivUniversalCoverNormalizer g) =
      _
  rw [IrreducibleCharacter.comap_values,
    MulEquiv.symm_apply_apply]

/-- The actual local normalizer has exactly twelve irreducible
characters of degree prime to three. -/
@[simp]
theorem natCard_pPrimeIrreducibleCharacter_actualNormalizer :
    Nat.card
        (PPrimeIrreducibleCharacter
          AlternatingSixUniversalCoverThreeNormalizer 3) =
      12 := by
  calc
    Nat.card
        (PPrimeIrreducibleCharacter
          AlternatingSixUniversalCoverThreeNormalizer 3) =
        Nat.card CoordinatePPrimeCharacterRow :=
      Nat.card_congr
        actualNormalizerPPrimeIrreducibleCharacterEquiv.symm
    _ = 12 := by
      rw [Nat.card_sum, Nat.card_prod]
      simp

end AlternatingSixThreeNormalizer
end McKayConjecture
