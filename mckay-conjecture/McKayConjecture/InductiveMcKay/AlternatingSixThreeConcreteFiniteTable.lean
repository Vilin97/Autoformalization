/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.AlternatingSixThreeActualNormalizerCharacterTable
import McKayConjecture.InductiveMcKay.AlternatingSixThreeFiniteTable

/-!
# Three-local `A₆` tables with the concrete normalizer enumeration fixed

The complete ordinary character table of the fixed Sylow-three normalizer
supplies its twelve `3'`-degree rows.  This file inserts that proved
enumeration into the finite-table interface used by the inductive McKay
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

local instance alternatingSixThreeConcreteFiniteTableFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- The fixed twelve-row index for the proved actual-normalizer
`3'`-character table. -/
abbrev AlternatingSixThreeConcreteNormalizerRow :=
  AlternatingSixThreeNormalizer.CoordinatePPrimeCharacterRow

/-- Finite ordinary-table data after fixing the proved local enumeration.

The ambient enumeration, row matching, and genuine stabilizer
equivariance are deliberately retained as fields. -/
structure AlternatingSixThreeConcreteCharacterTableCertificate
    (AmbientIndex : Type) [Fintype AmbientIndex] where
  /-- Complete finite enumeration of the ambient `3'`-rows. -/
  ambientEnumeration :
    AmbientIndex ≃ AlternatingSixThreeAmbientCharacter
  /-- The proposed matching with the twelve concrete local rows. -/
  indexEquiv :
    AmbientIndex ≃ AlternatingSixThreeConcreteNormalizerRow
  /-- Equivariance under the actual Sylow-stabilizer action on ambient
  and actual-normalizer characters. -/
  indexEquivariance :
    ∀ (a :
        SylowAutStabilizer
          (alternatingSixUniversalCoverSylow 3))
      (i : AmbientIndex),
      indexEquiv
          (ambientEnumeration.symm
            (a • ambientEnumeration i)) =
        AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv.symm
          (a •
            AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
              (indexEquiv i))

namespace AlternatingSixThreeConcreteCharacterTableCertificate

variable {AmbientIndex : Type} [Fintype AmbientIndex]

/-- Insert the proved twelve-row local enumeration into the existing
three-local ordinary-table certificate. -/
def toAlternatingSixThreeCharacterTableCertificate
    (d :
      AlternatingSixThreeConcreteCharacterTableCertificate
        AmbientIndex) :
    AlternatingSixThreeCharacterTableCertificate
      AmbientIndex AlternatingSixThreeConcreteNormalizerRow where
  ambientEnumeration := d.ambientEnumeration
  normalizerEnumeration :=
    AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
  indexEquiv := d.indexEquiv
  indexEquivariance := d.indexEquivariance

@[simp]
theorem toAlternatingSixThreeCharacterTableCertificate_ambientEnumeration
    (d :
      AlternatingSixThreeConcreteCharacterTableCertificate
        AmbientIndex) :
    (d.toAlternatingSixThreeCharacterTableCertificate
        |>.ambientEnumeration) =
      d.ambientEnumeration :=
  rfl

@[simp]
theorem toAlternatingSixThreeCharacterTableCertificate_normalizerEnumeration
    (d :
      AlternatingSixThreeConcreteCharacterTableCertificate
        AmbientIndex) :
    (d.toAlternatingSixThreeCharacterTableCertificate
        |>.normalizerEnumeration) =
      AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv :=
  rfl

@[simp]
theorem toAlternatingSixThreeCharacterTableCertificate_indexEquiv
    (d :
      AlternatingSixThreeConcreteCharacterTableCertificate
        AmbientIndex) :
    d.toAlternatingSixThreeCharacterTableCertificate.indexEquiv =
      d.indexEquiv :=
  rfl

/-- The generic finite-index equivariant McKay certificate with the local
enumeration fixed to the proved concrete table. -/
def toFiniteIndexMcKayEquivCertificate
    (d :
      AlternatingSixThreeConcreteCharacterTableCertificate
        AmbientIndex) :
    FiniteIndexMcKayEquivCertificate
      (alternatingSixUniversalCoverSylow 3)
      AmbientIndex AlternatingSixThreeConcreteNormalizerRow :=
  d.toAlternatingSixThreeCharacterTableCertificate
    |>.toFiniteIndexMcKayEquivCertificate

/-- The genuine equivariant character equivalence obtained from the
remaining ambient enumeration, matching, and equivariance proof. -/
def toEquivariantMcKayEquiv
    (d :
      AlternatingSixThreeConcreteCharacterTableCertificate
        AmbientIndex) :
    EquivariantMcKayEquiv
      (alternatingSixUniversalCoverSylow 3) :=
  d.toAlternatingSixThreeCharacterTableCertificate
    |>.toEquivariantMcKayEquiv

@[simp]
theorem toEquivariantMcKayEquiv_apply_enumerated
    (d :
      AlternatingSixThreeConcreteCharacterTableCertificate
        AmbientIndex)
    (i : AmbientIndex) :
    d.toEquivariantMcKayEquiv (d.ambientEnumeration i) =
      AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
        (d.indexEquiv i) :=
  d.toAlternatingSixThreeCharacterTableCertificate
    |>.toEquivariantMcKayEquiv_apply_enumerated i

end AlternatingSixThreeConcreteCharacterTableCertificate

end InductiveMcKay
end McKayConjecture
