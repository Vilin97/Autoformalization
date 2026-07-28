/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverThreeNormalizerSemidirect
import McKayConjecture.InductiveMcKay.FiniteIndexMcKayEquiv

/-!
# Three-local character tables through the `3^{1+2} ⋊ C₈` model

The fixed order-216 Sylow-three normalizer of the canonical universal
cover of `A₆` is now identified with an explicit semidirect product.
This file makes that identification usable by finite character-table
computations.

A model-facing certificate enumerates local `3'`-rows in the semidirect
product and transports them to the actual fixed normalizer through the
proved group equivalence.  The stabilizer action is transported in the
same way, so the finite equivariance condition remains the genuine one
required by inductive McKay.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixThreeNormalizerSemidirectTableFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- The ambient `3'`-irreducible characters of the canonical cover. -/
abbrev AlternatingSixThreeSemidirectAmbientCharacter :=
  PPrimeIrreducibleCharacter AlternatingSixUniversalCover 3

/-- The `3'`-irreducible characters of the explicit
`3^{1+2} ⋊ C₈` normalizer model. -/
abbrev AlternatingSixThreeSemidirectNormalizerCharacter :=
  PPrimeIrreducibleCharacter
    AlternatingSixThreeHeisenbergCyclicEightSemidirect 3

/-- Pull characters of the actual fixed normalizer back to the explicit
semidirect-product model. -/
def alternatingSixThreeActualNormalizerCharacterEquivSemidirect :
    PPrimeIrreducibleCharacter
        AlternatingSixUniversalCoverThreeNormalizer 3 ≃
      AlternatingSixThreeSemidirectNormalizerCharacter :=
  IrreducibleCharacter.pPrimeComapEquiv 3
    alternatingSixThreeHeisenbergCyclicEightEquivUniversalCoverNormalizer

/-- The genuine ambient-stabilizer action transported to model
characters. -/
def alternatingSixThreeSemidirectNormalizerCharacterAction
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3))
    (ψ : AlternatingSixThreeSemidirectNormalizerCharacter) :
    AlternatingSixThreeSemidirectNormalizerCharacter :=
  alternatingSixThreeActualNormalizerCharacterEquivSemidirect
    (a •
      alternatingSixThreeActualNormalizerCharacterEquivSemidirect.symm ψ)

@[simp]
theorem alternatingSixThreeSemidirectNormalizerCharacterAction_transported
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3))
    (ψ :
      PPrimeIrreducibleCharacter
        AlternatingSixUniversalCoverThreeNormalizer 3) :
    alternatingSixThreeSemidirectNormalizerCharacterAction a
        (alternatingSixThreeActualNormalizerCharacterEquivSemidirect ψ) =
      alternatingSixThreeActualNormalizerCharacterEquivSemidirect
        (a • ψ) := by
  simp [alternatingSixThreeSemidirectNormalizerCharacterAction]

/-- Finite table data with local rows written in the explicit semidirect
model. -/
structure AlternatingSixThreeSemidirectCharacterTableCertificate
    (AmbientIndex NormalizerIndex : Type)
    [Fintype AmbientIndex]
    [Fintype NormalizerIndex] where
  /-- Complete enumeration of the ambient `3'`-rows. -/
  ambientEnumeration :
    AmbientIndex ≃ AlternatingSixThreeSemidirectAmbientCharacter
  /-- Complete enumeration of the semidirect-model `3'`-rows. -/
  normalizerModelEnumeration :
    NormalizerIndex ≃
      AlternatingSixThreeSemidirectNormalizerCharacter
  /-- The proposed row matching. -/
  indexEquiv : AmbientIndex ≃ NormalizerIndex
  /-- Equivariance checked against the transported genuine normalizer
  action. -/
  indexEquivariance :
    ∀ (a :
        SylowAutStabilizer
          (alternatingSixUniversalCoverSylow 3))
      (i : AmbientIndex),
      indexEquiv
          (ambientEnumeration.symm
            (a • ambientEnumeration i)) =
        normalizerModelEnumeration.symm
          (alternatingSixThreeSemidirectNormalizerCharacterAction a
            (normalizerModelEnumeration (indexEquiv i)))

namespace AlternatingSixThreeSemidirectCharacterTableCertificate

variable
  {AmbientIndex NormalizerIndex : Type}
  [Fintype AmbientIndex]
  [Fintype NormalizerIndex]

/-- Transport a model-row enumeration to the actual fixed normalizer. -/
def normalizerEnumeration
    (d :
      AlternatingSixThreeSemidirectCharacterTableCertificate
        AmbientIndex NormalizerIndex) :
    NormalizerIndex ≃
      PPrimeIrreducibleCharacter
        AlternatingSixUniversalCoverThreeNormalizer 3 :=
  d.normalizerModelEnumeration.trans
    alternatingSixThreeActualNormalizerCharacterEquivSemidirect.symm

@[simp]
theorem actualNormalizerCharacterEquiv_apply_normalizerEnumeration
    (d :
      AlternatingSixThreeSemidirectCharacterTableCertificate
        AmbientIndex NormalizerIndex)
    (j : NormalizerIndex) :
    alternatingSixThreeActualNormalizerCharacterEquivSemidirect
        (d.normalizerEnumeration j) =
      d.normalizerModelEnumeration j := by
  simp [normalizerEnumeration]

/-- Convert the model-facing data to the generic finite-index
equivariant McKay certificate at the actual normalizer. -/
def toFiniteIndexMcKayEquivCertificate
    (d :
      AlternatingSixThreeSemidirectCharacterTableCertificate
        AmbientIndex NormalizerIndex) :
    FiniteIndexMcKayEquivCertificate
      (alternatingSixUniversalCoverSylow 3)
      AmbientIndex NormalizerIndex where
  ambientEnumeration := d.ambientEnumeration
  normalizerEnumeration := d.normalizerEnumeration
  indexEquiv := d.indexEquiv
  indexEquivariance := by
    intro a i
    simpa [
      normalizerEnumeration,
      alternatingSixThreeSemidirectNormalizerCharacterAction
    ] using d.indexEquivariance a i

/-- The genuine equivariant character equivalence obtained from the
finite ambient and semidirect-model tables. -/
def toEquivariantMcKayEquiv
    (d :
      AlternatingSixThreeSemidirectCharacterTableCertificate
        AmbientIndex NormalizerIndex) :
    EquivariantMcKayEquiv
      (alternatingSixUniversalCoverSylow 3) :=
  d.toFiniteIndexMcKayEquivCertificate.toEquivariantMcKayEquiv

@[simp]
theorem toEquivariantMcKayEquiv_apply_enumerated
    (d :
      AlternatingSixThreeSemidirectCharacterTableCertificate
        AmbientIndex NormalizerIndex)
    (i : AmbientIndex) :
    d.toEquivariantMcKayEquiv (d.ambientEnumeration i) =
      d.normalizerEnumeration (d.indexEquiv i) :=
  d.toFiniteIndexMcKayEquivCertificate
    |>.toEquivariantMcKayEquiv_apply_enumerated i

/-- Pulling a matched actual-normalizer row back to the semidirect model
recovers exactly the enumerated model row. -/
theorem actualNormalizerCharacterEquiv_apply_matchedRow
    (d :
      AlternatingSixThreeSemidirectCharacterTableCertificate
        AmbientIndex NormalizerIndex)
    (i : AmbientIndex) :
    alternatingSixThreeActualNormalizerCharacterEquivSemidirect
        (d.toEquivariantMcKayEquiv
          (d.ambientEnumeration i)) =
      d.normalizerModelEnumeration (d.indexEquiv i) := by
  rw [d.toEquivariantMcKayEquiv_apply_enumerated]
  exact
    d.actualNormalizerCharacterEquiv_apply_normalizerEnumeration
      (d.indexEquiv i)

end AlternatingSixThreeSemidirectCharacterTableCertificate

end InductiveMcKay
end McKayConjecture
