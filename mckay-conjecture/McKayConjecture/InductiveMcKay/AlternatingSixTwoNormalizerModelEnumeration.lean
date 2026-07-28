/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.AlternatingSixTwoNormalizerModelCharacterTable
import McKayConjecture.InductiveMcKay.AlternatingSixTwoNormalizerModelTable

/-!
# Complete row enumeration of the `6.A₆` two-normalizer

The concrete normalizer model `C₃ × Q₁₆` has 21 ordinary irreducible
characters and 12 odd-degree irreducible characters.  This file transports
both complete enumerations through the proved equivalence with the actual
fixed Sylow-two normalizer.

The 12-row odd-degree enumeration is also inserted into the model-facing
finite-table interface.  A later ambient calculation therefore only needs
to enumerate and match the ambient rows and prove transported equivariance.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixTwoNormalizerModelEnumerationFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The 21 ordinary model-normalizer rows. -/
abbrev AlternatingSixTwoModelNormalizerOrdinaryCharacterRow :=
  AlternatingSixTwoNormalizerModelCharacterTable.OrdinaryCharacterRow

/-- Pull ordinary characters of the actual normalizer back to the concrete
model. -/
def alternatingSixTwoActualNormalizerIrreducibleCharacterEquivModel :
    IrreducibleCharacter
        (SylowNormalizer (alternatingSixUniversalCoverSylow 2)) ≃
      IrreducibleCharacter AlternatingSixTwoNormalizerModel :=
  IrreducibleCharacter.comapEquiv
    alternatingSixTwoNormalizerModelEquivUniversalCoverNormalizer

/-- Complete ordinary enumeration of the concrete model. -/
def alternatingSixTwoModelNormalizerIrreducibleCharacterEquiv :
    AlternatingSixTwoModelNormalizerOrdinaryCharacterRow ≃
      IrreducibleCharacter AlternatingSixTwoNormalizerModel :=
  AlternatingSixTwoNormalizerModelCharacterTable.irreducibleCharacterEquiv

/-- Complete ordinary enumeration transported to the actual fixed
normalizer. -/
def alternatingSixTwoActualNormalizerIrreducibleCharacterEquiv :
    AlternatingSixTwoModelNormalizerOrdinaryCharacterRow ≃
      IrreducibleCharacter
        (SylowNormalizer (alternatingSixUniversalCoverSylow 2)) :=
  alternatingSixTwoModelNormalizerIrreducibleCharacterEquiv.trans
    alternatingSixTwoActualNormalizerIrreducibleCharacterEquivModel.symm

@[simp]
theorem
    alternatingSixTwoActualNormalizerIrreducibleCharacterEquivModel_apply_enumerated
    (r : AlternatingSixTwoModelNormalizerOrdinaryCharacterRow) :
    alternatingSixTwoActualNormalizerIrreducibleCharacterEquivModel
        (alternatingSixTwoActualNormalizerIrreducibleCharacterEquiv r) =
      alternatingSixTwoModelNormalizerIrreducibleCharacterEquiv r := by
  simp [alternatingSixTwoActualNormalizerIrreducibleCharacterEquiv,
    alternatingSixTwoActualNormalizerIrreducibleCharacterEquivModel]

/-- Values of the transported ordinary rows on elements written through the
concrete normalizer equivalence. -/
@[simp]
theorem alternatingSixTwoActualNormalizerIrreducibleCharacterEquiv_values
    (r : AlternatingSixTwoModelNormalizerOrdinaryCharacterRow)
    (g : AlternatingSixTwoNormalizerModel) :
    (alternatingSixTwoActualNormalizerIrreducibleCharacterEquiv r).values
        (alternatingSixTwoNormalizerModelEquivUniversalCoverNormalizer g) =
      (alternatingSixTwoModelNormalizerIrreducibleCharacterEquiv r).values
        g := by
  change
    ((alternatingSixTwoModelNormalizerIrreducibleCharacterEquiv r).comap
        alternatingSixTwoNormalizerModelEquivUniversalCoverNormalizer.symm).values
        (alternatingSixTwoNormalizerModelEquivUniversalCoverNormalizer g) =
      (alternatingSixTwoModelNormalizerIrreducibleCharacterEquiv r).values g
  simp

/-- There are exactly 21 ordinary irreducible characters of the actual
fixed two-normalizer. -/
@[simp]
theorem natCard_alternatingSixTwoActualNormalizerIrreducibleCharacter :
    Nat.card
        (IrreducibleCharacter
          (SylowNormalizer (alternatingSixUniversalCoverSylow 2))) =
      21 := by
  calc
    Nat.card
        (IrreducibleCharacter
          (SylowNormalizer (alternatingSixUniversalCoverSylow 2))) =
        Nat.card
          (IrreducibleCharacter
            AlternatingSixTwoNormalizerModel) :=
      Nat.card_congr
        alternatingSixTwoActualNormalizerIrreducibleCharacterEquivModel
    _ = 21 :=
      AlternatingSixTwoNormalizerModelCharacterTable.natCard_irreducibleCharacter

/-- The 12 explicit odd-degree row indices. -/
abbrev AlternatingSixTwoModelNormalizerCharacterRow :=
  AlternatingSixTwoNormalizerModelCharacterTable.CharacterRow

/-- Complete odd-degree enumeration of the concrete normalizer model. -/
def alternatingSixTwoModelNormalizerPPrimeCharacterEquiv :
    AlternatingSixTwoModelNormalizerCharacterRow ≃
      AlternatingSixTwoModelNormalizerCharacter :=
  AlternatingSixTwoNormalizerModelCharacterTable.pPrimeCharacterEquiv

/-- Complete odd-degree enumeration transported to the actual fixed
normalizer. -/
def alternatingSixTwoActualNormalizerPPrimeCharacterEquiv :
    AlternatingSixTwoModelNormalizerCharacterRow ≃
      PPrimeIrreducibleCharacter
        (SylowNormalizer (alternatingSixUniversalCoverSylow 2)) 2 :=
  alternatingSixTwoModelNormalizerPPrimeCharacterEquiv.trans
    alternatingSixTwoActualNormalizerCharacterEquivModel.symm

@[simp]
theorem
    alternatingSixTwoActualNormalizerCharacterEquivModel_apply_enumerated
    (r : AlternatingSixTwoModelNormalizerCharacterRow) :
    alternatingSixTwoActualNormalizerCharacterEquivModel
        (alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r) =
      alternatingSixTwoModelNormalizerPPrimeCharacterEquiv r := by
  simp [alternatingSixTwoActualNormalizerPPrimeCharacterEquiv]

/-- Values of the transported odd-degree rows on elements written through
the concrete normalizer equivalence. -/
@[simp]
theorem alternatingSixTwoActualNormalizerPPrimeCharacterEquiv_values
    (r : AlternatingSixTwoModelNormalizerCharacterRow)
    (g : AlternatingSixTwoNormalizerModel) :
    (alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r).1.values
        (alternatingSixTwoNormalizerModelEquivUniversalCoverNormalizer g) =
      (alternatingSixTwoModelNormalizerPPrimeCharacterEquiv r).1.values
        g := by
  change
    ((alternatingSixTwoModelNormalizerPPrimeCharacterEquiv r).1.comap
        alternatingSixTwoNormalizerModelEquivUniversalCoverNormalizer.symm).values
        (alternatingSixTwoNormalizerModelEquivUniversalCoverNormalizer g) =
      (alternatingSixTwoModelNormalizerPPrimeCharacterEquiv r).1.values g
  simp

@[simp]
theorem alternatingSixTwoModelNormalizerPPrimeCharacterEquiv_degree
    (r : AlternatingSixTwoModelNormalizerCharacterRow) :
    (alternatingSixTwoModelNormalizerPPrimeCharacterEquiv r).1.degree =
      1 :=
  AlternatingSixTwoNormalizerModelCharacterTable.pPrimeCharacterEquiv_degree r

@[simp]
theorem alternatingSixTwoActualNormalizerPPrimeCharacterEquiv_degree
    (r : AlternatingSixTwoModelNormalizerCharacterRow) :
    (alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r).1.degree =
      1 := by
  change
    (alternatingSixTwoModelNormalizerPPrimeCharacterEquiv r).1.degree = 1
  exact alternatingSixTwoModelNormalizerPPrimeCharacterEquiv_degree r

@[simp]
theorem alternatingSixTwoModelNormalizerPPrimeCharacterEquiv_values_a
    (r : AlternatingSixTwoModelNormalizerCharacterRow)
    (z : Multiplicative (ZMod 3)) (m : ℕ) :
    (alternatingSixTwoModelNormalizerPPrimeCharacterEquiv r).1.values
        (z, QuaternionGroup.a (m : ZMod 8)) =
      (CyclicThree.linearHom r.1 z : ℂ) *
        (QuaternionGroupFour.signParameter r.2.1 ^ m : ℂˣ) :=
  AlternatingSixTwoNormalizerModelCharacterTable.pPrimeCharacterEquiv_values_a
    r z m

@[simp]
theorem alternatingSixTwoModelNormalizerPPrimeCharacterEquiv_values_xa
    (r : AlternatingSixTwoModelNormalizerCharacterRow)
    (z : Multiplicative (ZMod 3)) (m : ℕ) :
    (alternatingSixTwoModelNormalizerPPrimeCharacterEquiv r).1.values
        (z, QuaternionGroup.xa (m : ZMod 8)) =
      (CyclicThree.linearHom r.1 z : ℂ) *
        (QuaternionGroupFour.signParameter r.2.2 *
          QuaternionGroupFour.signParameter r.2.1 ^ m : ℂˣ) :=
  AlternatingSixTwoNormalizerModelCharacterTable.pPrimeCharacterEquiv_values_xa
    r z m

/-- There are exactly 12 odd-degree irreducible characters of the concrete
model. -/
@[simp]
theorem natCard_alternatingSixTwoModelNormalizerCharacter :
    Nat.card AlternatingSixTwoModelNormalizerCharacter = 12 :=
  AlternatingSixTwoNormalizerModelCharacterTable.natCard_pPrimeIrreducibleCharacter

/-- There are exactly 12 odd-degree irreducible characters of the actual
fixed two-normalizer. -/
@[simp]
theorem natCard_alternatingSixTwoActualNormalizerCharacter :
    Nat.card
        (PPrimeIrreducibleCharacter
          (SylowNormalizer (alternatingSixUniversalCoverSylow 2)) 2) =
      12 := by
  calc
    Nat.card
        (PPrimeIrreducibleCharacter
          (SylowNormalizer (alternatingSixUniversalCoverSylow 2)) 2) =
        Nat.card AlternatingSixTwoModelNormalizerCharacter :=
      Nat.card_congr
        alternatingSixTwoActualNormalizerCharacterEquivModel
    _ = 12 :=
      natCard_alternatingSixTwoModelNormalizerCharacter

/-- Remaining ordinary character-table data after fixing the complete
12-row normalizer enumeration. -/
structure AlternatingSixTwoModelCharacterTableCompletion
    (AmbientIndex : Type) [Fintype AmbientIndex] where
  /-- Complete enumeration of the ambient odd-degree rows. -/
  ambientEnumeration :
    AmbientIndex ≃ AlternatingSixTwoModelAmbientCharacter
  /-- Matching of ambient rows with the 12 fixed normalizer rows. -/
  indexEquiv :
    AmbientIndex ≃ AlternatingSixTwoModelNormalizerCharacterRow
  /-- Equivariance for the actual action transported to the model. -/
  indexEquivariance :
    ∀ (a :
        SylowAutStabilizer
          (alternatingSixUniversalCoverSylow 2))
      (i : AmbientIndex),
      indexEquiv
          (ambientEnumeration.symm
            (a • ambientEnumeration i)) =
        alternatingSixTwoModelNormalizerPPrimeCharacterEquiv.symm
          (alternatingSixTwoModelNormalizerCharacterAction a
            (alternatingSixTwoModelNormalizerPPrimeCharacterEquiv
              (indexEquiv i)))

namespace AlternatingSixTwoModelCharacterTableCompletion

variable {AmbientIndex : Type} [Fintype AmbientIndex]

/-- Insert the complete 12-row model enumeration into the finite
character-table certificate. -/
def toModelCharacterTableCertificate
    (d : AlternatingSixTwoModelCharacterTableCompletion AmbientIndex) :
    AlternatingSixTwoModelCharacterTableCertificate
      AmbientIndex AlternatingSixTwoModelNormalizerCharacterRow where
  ambientEnumeration := d.ambientEnumeration
  normalizerModelEnumeration :=
    alternatingSixTwoModelNormalizerPPrimeCharacterEquiv
  indexEquiv := d.indexEquiv
  indexEquivariance := d.indexEquivariance

/-- The generic finite-index certificate at the actual exact normalizer. -/
def toFiniteIndexMcKayEquivCertificate
    (d : AlternatingSixTwoModelCharacterTableCompletion AmbientIndex) :
    FiniteIndexMcKayEquivCertificate
      (alternatingSixUniversalCoverSylow 2)
      AmbientIndex AlternatingSixTwoModelNormalizerCharacterRow :=
  d.toModelCharacterTableCertificate
    |>.toFiniteIndexMcKayEquivCertificate

/-- The equivariant McKay equivalence obtained after supplying the ambient
enumeration, matching, and equivariance proof. -/
def toEquivariantMcKayEquiv
    (d : AlternatingSixTwoModelCharacterTableCompletion AmbientIndex) :
    EquivariantMcKayEquiv
      (alternatingSixUniversalCoverSylow 2) :=
  d.toFiniteIndexMcKayEquivCertificate.toEquivariantMcKayEquiv

@[simp]
theorem toEquivariantMcKayEquiv_apply_enumerated
    (d : AlternatingSixTwoModelCharacterTableCompletion AmbientIndex)
    (i : AmbientIndex) :
    d.toEquivariantMcKayEquiv (d.ambientEnumeration i) =
      alternatingSixTwoActualNormalizerPPrimeCharacterEquiv
        (d.indexEquiv i) :=
  d.toFiniteIndexMcKayEquivCertificate
    |>.toEquivariantMcKayEquiv_apply_enumerated i

end AlternatingSixTwoModelCharacterTableCompletion

end InductiveMcKay
end McKayConjecture
