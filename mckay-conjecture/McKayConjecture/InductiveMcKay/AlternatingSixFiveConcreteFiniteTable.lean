/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixFiveNormalizerSemidirectEnumeration

/-!
# Five-local `A₆` tables with the concrete normalizer enumeration fixed

The proved character table of the concrete normalizer model
`C₃ × (C₅ ⋊ C₄)` supplies all twenty-four `5'`-degree rows of the actual
fixed Sylow-five normalizer.  This file inserts that transported
enumeration into the finite-table interface used by the exact-normalizer
reduction.

The ambient enumeration, the finite row matching, and its equivariance
under the genuine Sylow-stabilizer action remain explicit inputs.  Thus the
conversion below removes exactly the local enumeration obligation and no
ambient or equivariance obligation.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveConcreteFiniteTableFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The fixed twenty-four-row index for the proved actual-normalizer
`5'`-character table. -/
abbrev AlternatingSixFiveConcreteNormalizerRow :=
  AlternatingSixFiveSemidirectNormalizerCharacterRow

/-- Complete `5'`-character enumeration of the actual fixed Sylow-five
normalizer, transported from its proved semidirect-product table. -/
def alternatingSixFiveActualNormalizerPPrimeCharacterEquiv :
    AlternatingSixFiveConcreteNormalizerRow ≃
      PPrimeIrreducibleCharacter
        (SylowNormalizer (alternatingSixUniversalCoverSylow 5)) 5 :=
  alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv.trans
    alternatingSixFiveActualNormalizerCharacterEquivSemidirect.symm

@[simp]
theorem
    alternatingSixFiveActualNormalizerCharacterEquivSemidirect_apply_enumerated
    (r : AlternatingSixFiveConcreteNormalizerRow) :
    alternatingSixFiveActualNormalizerCharacterEquivSemidirect
        (alternatingSixFiveActualNormalizerPPrimeCharacterEquiv r) =
      alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv r := by
  simp [alternatingSixFiveActualNormalizerPPrimeCharacterEquiv]

/-- There are exactly twenty-four `5'`-characters of the actual fixed
Sylow-five normalizer. -/
@[simp]
theorem natCard_alternatingSixFiveActualNormalizerCharacter :
    Nat.card
        (PPrimeIrreducibleCharacter
          (SylowNormalizer (alternatingSixUniversalCoverSylow 5)) 5) =
      24 := by
  calc
    Nat.card
        (PPrimeIrreducibleCharacter
          (SylowNormalizer (alternatingSixUniversalCoverSylow 5)) 5) =
        Nat.card AlternatingSixFiveSemidirectNormalizerCharacter :=
      Nat.card_congr
        alternatingSixFiveActualNormalizerCharacterEquivSemidirect
    _ = 24 :=
      natCard_alternatingSixFiveSemidirectNormalizerCharacter

/-- Finite `5'`-table data after fixing the proved local enumeration.

The ambient enumeration, row matching, and genuine stabilizer
equivariance are deliberately retained as fields. -/
structure AlternatingSixFiveConcreteCharacterTableCertificate
    (AmbientIndex : Type) [Fintype AmbientIndex] where
  /-- Complete finite enumeration of the ambient `5'`-rows. -/
  ambientEnumeration :
    AmbientIndex ≃ AlternatingSixFiveSemidirectAmbientCharacter
  /-- The proposed matching with the twenty-four concrete local rows. -/
  indexEquiv :
    AmbientIndex ≃ AlternatingSixFiveConcreteNormalizerRow
  /-- Equivariance under the actual Sylow-stabilizer action on ambient
  and actual-normalizer characters. -/
  indexEquivariance :
    ∀ (a :
        SylowAutStabilizer
          (alternatingSixUniversalCoverSylow 5))
      (i : AmbientIndex),
      indexEquiv
          (ambientEnumeration.symm
            (a • ambientEnumeration i)) =
        alternatingSixFiveActualNormalizerPPrimeCharacterEquiv.symm
          (a •
            alternatingSixFiveActualNormalizerPPrimeCharacterEquiv
              (indexEquiv i))

namespace AlternatingSixFiveConcreteCharacterTableCertificate

variable {AmbientIndex : Type} [Fintype AmbientIndex]

/-- Re-express the actual-normalizer equivariance field through the proved
`C₃ × (C₅ ⋊ C₄)` model equivalence.

This bridge identifies the concrete actual-normalizer-facing facade with
the pre-existing semidirect-model completion API; it does not discharge
any additional table obligation. -/
def toSemidirectCharacterTableCompletion
    (d :
      AlternatingSixFiveConcreteCharacterTableCertificate
        AmbientIndex) :
    AlternatingSixFiveSemidirectCharacterTableCompletion AmbientIndex where
  ambientEnumeration := d.ambientEnumeration
  indexEquiv := d.indexEquiv
  indexEquivariance := by
    intro a i
    simpa [
      alternatingSixFiveActualNormalizerPPrimeCharacterEquiv,
      alternatingSixFiveSemidirectNormalizerCharacterAction
    ] using d.indexEquivariance a i

/-- Re-express the semidirect-model completion through the actual fixed
normalizer enumeration. -/
def ofSemidirectCharacterTableCompletion
    (d :
      AlternatingSixFiveSemidirectCharacterTableCompletion AmbientIndex) :
    AlternatingSixFiveConcreteCharacterTableCertificate AmbientIndex where
  ambientEnumeration := d.ambientEnumeration
  indexEquiv := d.indexEquiv
  indexEquivariance := by
    intro a i
    simpa [
      alternatingSixFiveActualNormalizerPPrimeCharacterEquiv,
      alternatingSixFiveSemidirectNormalizerCharacterAction
    ] using d.indexEquivariance a i

/-- The actual-normalizer and semidirect-model completion records carry
equivalent data. -/
def equivSemidirectCharacterTableCompletion :
    AlternatingSixFiveConcreteCharacterTableCertificate AmbientIndex ≃
      AlternatingSixFiveSemidirectCharacterTableCompletion AmbientIndex where
  toFun := toSemidirectCharacterTableCompletion
  invFun := ofSemidirectCharacterTableCompletion
  left_inv := by
    intro d
    cases d
    rfl
  right_inv := by
    intro d
    cases d
    rfl

/-- Insert the proved twenty-four-row local enumeration into the generic
finite-index equivariant McKay certificate. -/
def toFiniteIndexMcKayEquivCertificate
    (d :
      AlternatingSixFiveConcreteCharacterTableCertificate
        AmbientIndex) :
    FiniteIndexMcKayEquivCertificate
      (alternatingSixUniversalCoverSylow 5)
      AmbientIndex AlternatingSixFiveConcreteNormalizerRow where
  ambientEnumeration := d.ambientEnumeration
  normalizerEnumeration :=
    alternatingSixFiveActualNormalizerPPrimeCharacterEquiv
  indexEquiv := d.indexEquiv
  indexEquivariance := d.indexEquivariance

@[simp]
theorem toFiniteIndexMcKayEquivCertificate_ambientEnumeration
    (d :
      AlternatingSixFiveConcreteCharacterTableCertificate
        AmbientIndex) :
    d.toFiniteIndexMcKayEquivCertificate.ambientEnumeration =
      d.ambientEnumeration :=
  rfl

@[simp]
theorem toFiniteIndexMcKayEquivCertificate_normalizerEnumeration
    (d :
      AlternatingSixFiveConcreteCharacterTableCertificate
        AmbientIndex) :
    d.toFiniteIndexMcKayEquivCertificate.normalizerEnumeration =
      alternatingSixFiveActualNormalizerPPrimeCharacterEquiv :=
  rfl

@[simp]
theorem toFiniteIndexMcKayEquivCertificate_indexEquiv
    (d :
      AlternatingSixFiveConcreteCharacterTableCertificate
        AmbientIndex) :
    d.toFiniteIndexMcKayEquivCertificate.indexEquiv =
      d.indexEquiv :=
  rfl

/-- The genuine equivariant character equivalence obtained from the
remaining ambient enumeration, matching, and equivariance proof. -/
def toEquivariantMcKayEquiv
    (d :
      AlternatingSixFiveConcreteCharacterTableCertificate
        AmbientIndex) :
    EquivariantMcKayEquiv
      (alternatingSixUniversalCoverSylow 5) :=
  d.toFiniteIndexMcKayEquivCertificate.toEquivariantMcKayEquiv

@[simp]
theorem toEquivariantMcKayEquiv_apply_enumerated
    (d :
      AlternatingSixFiveConcreteCharacterTableCertificate
        AmbientIndex)
    (i : AmbientIndex) :
    d.toEquivariantMcKayEquiv (d.ambientEnumeration i) =
      alternatingSixFiveActualNormalizerPPrimeCharacterEquiv
        (d.indexEquiv i) :=
  d.toFiniteIndexMcKayEquivCertificate
    |>.toEquivariantMcKayEquiv_apply_enumerated i

end AlternatingSixFiveConcreteCharacterTableCertificate

end InductiveMcKay
end McKayConjecture
