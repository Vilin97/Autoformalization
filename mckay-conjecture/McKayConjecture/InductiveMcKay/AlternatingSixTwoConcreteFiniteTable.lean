/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixTwoNormalizerModelEnumeration

/-!
# Two-local `A₆` tables with the concrete normalizer enumeration fixed

The proved character table of the concrete normalizer model
`C₃ × Q₁₆` supplies all twelve `2'`-degree rows of the actual fixed
Sylow-two normalizer.  This file inserts that transported enumeration into
the finite-table interface used by the exact-normalizer reduction.

The ambient enumeration, the finite row matching, and its equivariance
under the genuine Sylow-stabilizer action remain explicit inputs.  Thus the
conversion below removes exactly the local enumeration obligation and no
ambient or equivariance obligation.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixTwoConcreteFiniteTableFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The fixed twelve-row index for the proved actual-normalizer
`2'`-character table. -/
abbrev AlternatingSixTwoConcreteNormalizerRow :=
  AlternatingSixTwoModelNormalizerCharacterRow

/-- Finite `2'`-table data after fixing the proved local enumeration.

The ambient enumeration, row matching, and genuine stabilizer
equivariance are deliberately retained as fields. -/
structure AlternatingSixTwoConcreteCharacterTableCertificate
    (AmbientIndex : Type) [Fintype AmbientIndex] where
  /-- Complete finite enumeration of the ambient `2'`-rows. -/
  ambientEnumeration :
    AmbientIndex ≃ AlternatingSixTwoModelAmbientCharacter
  /-- The proposed matching with the twelve concrete local rows. -/
  indexEquiv :
    AmbientIndex ≃ AlternatingSixTwoConcreteNormalizerRow
  /-- Equivariance under the actual Sylow-stabilizer action on ambient
  and actual-normalizer characters. -/
  indexEquivariance :
    ∀ (a :
        SylowAutStabilizer
          (alternatingSixUniversalCoverSylow 2))
      (i : AmbientIndex),
      indexEquiv
          (ambientEnumeration.symm
            (a • ambientEnumeration i)) =
        alternatingSixTwoActualNormalizerPPrimeCharacterEquiv.symm
          (a •
            alternatingSixTwoActualNormalizerPPrimeCharacterEquiv
              (indexEquiv i))

namespace AlternatingSixTwoConcreteCharacterTableCertificate

variable {AmbientIndex : Type} [Fintype AmbientIndex]

/-- Re-express the actual-normalizer equivariance field through the proved
`C₃ × Q₁₆` model equivalence.

This bridge identifies the concrete actual-normalizer-facing facade with
the pre-existing model-facing completion API; it does not discharge any
additional table obligation. -/
def toModelCharacterTableCompletion
    (d :
      AlternatingSixTwoConcreteCharacterTableCertificate
        AmbientIndex) :
    AlternatingSixTwoModelCharacterTableCompletion AmbientIndex where
  ambientEnumeration := d.ambientEnumeration
  indexEquiv := d.indexEquiv
  indexEquivariance := by
    intro a i
    simpa [
      alternatingSixTwoActualNormalizerPPrimeCharacterEquiv,
      alternatingSixTwoModelNormalizerCharacterAction
    ] using d.indexEquivariance a i

/-- Re-express the model-facing completion through the actual fixed
normalizer enumeration. -/
def ofModelCharacterTableCompletion
    (d : AlternatingSixTwoModelCharacterTableCompletion AmbientIndex) :
    AlternatingSixTwoConcreteCharacterTableCertificate AmbientIndex where
  ambientEnumeration := d.ambientEnumeration
  indexEquiv := d.indexEquiv
  indexEquivariance := by
    intro a i
    simpa [
      alternatingSixTwoActualNormalizerPPrimeCharacterEquiv,
      alternatingSixTwoModelNormalizerCharacterAction
    ] using d.indexEquivariance a i

/-- The actual-normalizer and model-facing completion records carry
equivalent data. -/
def equivModelCharacterTableCompletion :
    AlternatingSixTwoConcreteCharacterTableCertificate AmbientIndex ≃
      AlternatingSixTwoModelCharacterTableCompletion AmbientIndex where
  toFun := toModelCharacterTableCompletion
  invFun := ofModelCharacterTableCompletion
  left_inv := by
    intro d
    cases d
    rfl
  right_inv := by
    intro d
    cases d
    rfl

/-- Insert the proved twelve-row local enumeration into the generic
finite-index equivariant McKay certificate. -/
def toFiniteIndexMcKayEquivCertificate
    (d :
      AlternatingSixTwoConcreteCharacterTableCertificate
        AmbientIndex) :
    FiniteIndexMcKayEquivCertificate
      (alternatingSixUniversalCoverSylow 2)
      AmbientIndex AlternatingSixTwoConcreteNormalizerRow where
  ambientEnumeration := d.ambientEnumeration
  normalizerEnumeration :=
    alternatingSixTwoActualNormalizerPPrimeCharacterEquiv
  indexEquiv := d.indexEquiv
  indexEquivariance := d.indexEquivariance

@[simp]
theorem toFiniteIndexMcKayEquivCertificate_ambientEnumeration
    (d :
      AlternatingSixTwoConcreteCharacterTableCertificate
        AmbientIndex) :
    d.toFiniteIndexMcKayEquivCertificate.ambientEnumeration =
      d.ambientEnumeration :=
  rfl

@[simp]
theorem toFiniteIndexMcKayEquivCertificate_normalizerEnumeration
    (d :
      AlternatingSixTwoConcreteCharacterTableCertificate
        AmbientIndex) :
    d.toFiniteIndexMcKayEquivCertificate.normalizerEnumeration =
      alternatingSixTwoActualNormalizerPPrimeCharacterEquiv :=
  rfl

@[simp]
theorem toFiniteIndexMcKayEquivCertificate_indexEquiv
    (d :
      AlternatingSixTwoConcreteCharacterTableCertificate
        AmbientIndex) :
    d.toFiniteIndexMcKayEquivCertificate.indexEquiv =
      d.indexEquiv :=
  rfl

/-- The genuine equivariant character equivalence obtained from the
remaining ambient enumeration, matching, and equivariance proof. -/
def toEquivariantMcKayEquiv
    (d :
      AlternatingSixTwoConcreteCharacterTableCertificate
        AmbientIndex) :
    EquivariantMcKayEquiv
      (alternatingSixUniversalCoverSylow 2) :=
  d.toFiniteIndexMcKayEquivCertificate.toEquivariantMcKayEquiv

@[simp]
theorem toEquivariantMcKayEquiv_apply_enumerated
    (d :
      AlternatingSixTwoConcreteCharacterTableCertificate
        AmbientIndex)
    (i : AmbientIndex) :
    d.toEquivariantMcKayEquiv (d.ambientEnumeration i) =
      alternatingSixTwoActualNormalizerPPrimeCharacterEquiv
        (d.indexEquiv i) :=
  d.toFiniteIndexMcKayEquivCertificate
    |>.toEquivariantMcKayEquiv_apply_enumerated i

end AlternatingSixTwoConcreteCharacterTableCertificate

end InductiveMcKay
end McKayConjecture
