/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.QuaternionGroupFiveCharacterTable
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveSylowFiveNormalizer
import McKayConjecture.InductiveMcKay.FiniteIndexProjectiveTable

/-!
# The `5'`-character table of the Sylow-five normalizer in `SL(2, 𝔽₅)`

This file transports the complete eight-row character table of
`QuaternionGroup 5` across its explicit equivalence with the exact
Sylow-five normalizer.  It also specializes the finite-index certificate
interface so that later work only has to fill the ambient table,
equivariance, and projective comparison rows.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory
open QuaternionGroupFive

local instance factPrimeFiveForNormalizerTable :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- Complete enumeration of the `5'`-degree irreducible characters of the
exact Sylow-five normalizer. -/
def specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv :
    CharacterRow ≃
      PPrimeIrreducibleCharacter
        (SylowNormalizer specialLinearTwoFiveSylowFive) 5 :=
  pPrimeCharacterEquiv.trans
    (IrreducibleCharacter.pPrimeComapEquiv 5
      quaternionFiveEquivSylowFiveNormalizer.symm)

@[simp]
theorem specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv_degree
    (r : CharacterRow) :
    (specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv r).1.degree =
      (pPrimeCharacterEquiv r).1.degree :=
  rfl

@[simp]
theorem
    specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv_degree_linear
    (j : Fin 4) :
    (specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
      (.linear j)).1.degree = 1 := by
  simp [specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv]

@[simp]
theorem
    specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv_degree_twoDimensional
    (k : Fin 4) :
    (specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
      (.twoDimensional k)).1.degree = 2 := by
  simp [specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv]

@[simp]
theorem specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv_values
    (r : CharacterRow)
    (g : QuaternionGroup 5) :
    (specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv r).1.values
        (quaternionFiveEquivSylowFiveNormalizer g) =
      (pPrimeCharacterEquiv r).1.values g := by
  change
    ((pPrimeCharacterEquiv r).1.comap
      quaternionFiveEquivSylowFiveNormalizer.symm).values
        (quaternionFiveEquivSylowFiveNormalizer g) = _
  rw [IrreducibleCharacter.comap_values,
    MulEquiv.symm_apply_apply]

/-- There are exactly eight `5'`-degree irreducible characters of the exact
Sylow-five normalizer. -/
theorem natCard_specialLinearTwoFiveFiveNormalizerPPrimeCharacter :
    Nat.card
        (PPrimeIrreducibleCharacter
          (SylowNormalizer specialLinearTwoFiveSylowFive) 5) =
      8 := by
  calc
    Nat.card
          (PPrimeIrreducibleCharacter
            (SylowNormalizer specialLinearTwoFiveSylowFive) 5) =
        Nat.card CharacterRow :=
      Nat.card_congr
        specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv.symm
    _ = 8 := by
      rw [Nat.card_eq_fintype_card]
      native_decide

/-- Remaining ordinary-table data after fixing the complete normalizer
enumeration. -/
structure SpecialLinearTwoFiveFiveCharacterTableCompletion
    (AmbientIndex : Type) [Fintype AmbientIndex] where
  /-- Enumeration of the ambient `5'`-degree rows. -/
  ambientEnumeration :
    AmbientIndex ≃
      PPrimeIrreducibleCharacter SpecialLinearTwoFive 5
  /-- Matching of ambient rows with the eight normalizer rows. -/
  indexEquiv :
    AmbientIndex ≃ CharacterRow
  /-- Equivariance checked at row-index level. -/
  indexEquivariance :
    ∀ (a :
        SylowAutStabilizer specialLinearTwoFiveSylowFive)
      (i : AmbientIndex),
      indexEquiv
          (ambientEnumeration.symm
            (a • ambientEnumeration i)) =
        specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv.symm
          (a •
            specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
              (indexEquiv i))

namespace SpecialLinearTwoFiveFiveCharacterTableCompletion

variable {AmbientIndex : Type} [Fintype AmbientIndex]

def toFiniteIndexMcKayEquivCertificate
    (d :
      SpecialLinearTwoFiveFiveCharacterTableCompletion AmbientIndex) :
    FiniteIndexMcKayEquivCertificate
      specialLinearTwoFiveSylowFive
      AmbientIndex CharacterRow where
  ambientEnumeration := d.ambientEnumeration
  normalizerEnumeration :=
    specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
  indexEquiv := d.indexEquiv
  indexEquivariance := d.indexEquivariance

def toEquivariantMcKayEquiv
    (d :
      SpecialLinearTwoFiveFiveCharacterTableCompletion AmbientIndex) :
    EquivariantMcKayEquiv specialLinearTwoFiveSylowFive :=
  d.toFiniteIndexMcKayEquivCertificate.toEquivariantMcKayEquiv

@[simp]
theorem toEquivariantMcKayEquiv_apply_enumerated
    (d :
      SpecialLinearTwoFiveFiveCharacterTableCompletion AmbientIndex)
    (i : AmbientIndex) :
    d.toEquivariantMcKayEquiv (d.ambientEnumeration i) =
      specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
        (d.indexEquiv i) :=
  d.toFiniteIndexMcKayEquivCertificate
    |>.toEquivariantMcKayEquiv_apply_enumerated i

end SpecialLinearTwoFiveFiveCharacterTableCompletion

/-- Remaining projective rows after the ordinary table is fixed. -/
structure SpecialLinearTwoFiveFiveProjectiveTableCompletion
    (AmbientIndex : Type) [Fintype AmbientIndex] where
  characterTable :
    SpecialLinearTwoFiveFiveCharacterTableCompletion AmbientIndex
  projectiveRow :
    ∀ i : AmbientIndex,
      ExactNormalizerProjectiveRowData
        characterTable.toEquivariantMcKayEquiv
        (characterTable.ambientEnumeration i)

namespace SpecialLinearTwoFiveFiveProjectiveTableCompletion

variable {AmbientIndex : Type} [Fintype AmbientIndex]

def toFiniteIndexExactNormalizerProjectiveTableCertificate
    (d :
      SpecialLinearTwoFiveFiveProjectiveTableCompletion AmbientIndex) :
    FiniteIndexExactNormalizerProjectiveTableCertificate
      specialLinearTwoFiveSylowFive
      AmbientIndex CharacterRow where
  characterCertificate :=
    d.characterTable.toFiniteIndexMcKayEquivCertificate
  projectiveRow := d.projectiveRow

def toLocalInductiveMcKayData
    (d :
      SpecialLinearTwoFiveFiveProjectiveTableCompletion AmbientIndex) :
    LocalInductiveMcKayData specialLinearTwoFiveSylowFive :=
  d.toFiniteIndexExactNormalizerProjectiveTableCertificate
    |>.toLocalInductiveMcKayData

end SpecialLinearTwoFiveFiveProjectiveTableCompletion

end InductiveMcKay
end McKayConjecture
