/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverTwoNormalizerModel
import McKayConjecture.InductiveMcKay.FiniteIndexMcKayEquiv

/-!
# Finite two-local character tables through the direct-product normalizer model

The fixed Sylow-two normalizer of the canonical universal cover of `A₆` is
identified with the concrete group `C₃ × Q₁₆`.  This file makes that group
identification usable by a finite character-table computation.

A certificate enumerates ambient rows directly, enumerates local rows in
the concrete product model, and checks equivariance on row indices.  The
model rows are transported to the actual fixed normalizer by the proved
group equivalence.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixTwoNormalizerModelTableFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The ambient `2'`-irreducible characters of the canonical cover. -/
abbrev AlternatingSixTwoModelAmbientCharacter :=
  PPrimeIrreducibleCharacter AlternatingSixUniversalCover 2

/-- The `2'`-irreducible characters of the concrete `C₃ × Q₁₆`
normalizer model. -/
abbrev AlternatingSixTwoModelNormalizerCharacter :=
  PPrimeIrreducibleCharacter AlternatingSixTwoNormalizerModel 2

/-- Pull characters of the actual fixed normalizer back to the concrete
direct-product model. -/
def alternatingSixTwoActualNormalizerCharacterEquivModel :
    PPrimeIrreducibleCharacter
        (SylowNormalizer (alternatingSixUniversalCoverSylow 2)) 2 ≃
      AlternatingSixTwoModelNormalizerCharacter :=
  IrreducibleCharacter.pPrimeComapEquiv 2
    alternatingSixTwoNormalizerModelEquivUniversalCoverNormalizer

/-- The action of an ambient Sylow stabilizer on model characters, defined
by transport through the proved normalizer equivalence. -/
def alternatingSixTwoModelNormalizerCharacterAction
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 2))
    (ψ : AlternatingSixTwoModelNormalizerCharacter) :
    AlternatingSixTwoModelNormalizerCharacter :=
  alternatingSixTwoActualNormalizerCharacterEquivModel
    (a • alternatingSixTwoActualNormalizerCharacterEquivModel.symm ψ)

@[simp]
theorem alternatingSixTwoModelNormalizerCharacterAction_transported
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 2))
    (ψ :
      PPrimeIrreducibleCharacter
        (SylowNormalizer (alternatingSixUniversalCoverSylow 2)) 2) :
    alternatingSixTwoModelNormalizerCharacterAction a
        (alternatingSixTwoActualNormalizerCharacterEquivModel ψ) =
      alternatingSixTwoActualNormalizerCharacterEquivModel (a • ψ) := by
  simp [alternatingSixTwoModelNormalizerCharacterAction]

/-- Finite character-table data with local rows written in the concrete
`C₃ × Q₁₆` model.

The equivariance field uses the actual ambient-stabilizer action transported
through the normalizer isomorphism. -/
structure AlternatingSixTwoModelCharacterTableCertificate
    (AmbientIndex NormalizerIndex : Type)
    [Fintype AmbientIndex]
    [Fintype NormalizerIndex] where
  /-- Complete enumeration of the ambient `2'`-rows. -/
  ambientEnumeration :
    AmbientIndex ≃ AlternatingSixTwoModelAmbientCharacter
  /-- Complete enumeration of the model-normalizer `2'`-rows. -/
  normalizerModelEnumeration :
    NormalizerIndex ≃ AlternatingSixTwoModelNormalizerCharacter
  /-- The proposed finite row matching. -/
  indexEquiv : AmbientIndex ≃ NormalizerIndex
  /-- Equivariance of the proposed matching after transporting the actual
  normalizer action to the concrete model. -/
  indexEquivariance :
    ∀ (a :
        SylowAutStabilizer
          (alternatingSixUniversalCoverSylow 2))
      (i : AmbientIndex),
      indexEquiv
          (ambientEnumeration.symm
            (a • ambientEnumeration i)) =
        normalizerModelEnumeration.symm
          (alternatingSixTwoModelNormalizerCharacterAction a
            (normalizerModelEnumeration (indexEquiv i)))

namespace AlternatingSixTwoModelCharacterTableCertificate

variable
  {AmbientIndex NormalizerIndex : Type}
  [Fintype AmbientIndex]
  [Fintype NormalizerIndex]

/-- Transport the model-normalizer row enumeration to the actual fixed
normalizer. -/
def normalizerEnumeration
    (d :
      AlternatingSixTwoModelCharacterTableCertificate
        AmbientIndex NormalizerIndex) :
    NormalizerIndex ≃
      PPrimeIrreducibleCharacter
        (SylowNormalizer (alternatingSixUniversalCoverSylow 2)) 2 :=
  d.normalizerModelEnumeration.trans
    alternatingSixTwoActualNormalizerCharacterEquivModel.symm

@[simp]
theorem actualNormalizerCharacterEquiv_apply_normalizerEnumeration
    (d :
      AlternatingSixTwoModelCharacterTableCertificate
        AmbientIndex NormalizerIndex)
    (j : NormalizerIndex) :
    alternatingSixTwoActualNormalizerCharacterEquivModel
        (d.normalizerEnumeration j) =
      d.normalizerModelEnumeration j := by
  simp [normalizerEnumeration]

/-- Convert the model-facing certificate to the generic finite-index
equivariant McKay certificate at the actual exact normalizer. -/
def toFiniteIndexMcKayEquivCertificate
    (d :
      AlternatingSixTwoModelCharacterTableCertificate
        AmbientIndex NormalizerIndex) :
    FiniteIndexMcKayEquivCertificate
      (alternatingSixUniversalCoverSylow 2)
      AmbientIndex NormalizerIndex where
  ambientEnumeration := d.ambientEnumeration
  normalizerEnumeration := d.normalizerEnumeration
  indexEquiv := d.indexEquiv
  indexEquivariance := by
    intro a i
    simpa [
      normalizerEnumeration,
      alternatingSixTwoModelNormalizerCharacterAction
    ] using d.indexEquivariance a i

/-- The equivariant character equivalence certified by the finite ambient
and model-normalizer tables. -/
def toEquivariantMcKayEquiv
    (d :
      AlternatingSixTwoModelCharacterTableCertificate
        AmbientIndex NormalizerIndex) :
    EquivariantMcKayEquiv
      (alternatingSixUniversalCoverSylow 2) :=
  d.toFiniteIndexMcKayEquivCertificate.toEquivariantMcKayEquiv

@[simp]
theorem toEquivariantMcKayEquiv_apply_enumerated
    (d :
      AlternatingSixTwoModelCharacterTableCertificate
        AmbientIndex NormalizerIndex)
    (i : AmbientIndex) :
    d.toEquivariantMcKayEquiv (d.ambientEnumeration i) =
      d.normalizerEnumeration (d.indexEquiv i) :=
  d.toFiniteIndexMcKayEquivCertificate
    |>.toEquivariantMcKayEquiv_apply_enumerated i

/-- Pulling the matched actual-normalizer row back to the concrete model
recovers exactly the enumerated model row. -/
theorem actualNormalizerCharacterEquiv_apply_matchedRow
    (d :
      AlternatingSixTwoModelCharacterTableCertificate
        AmbientIndex NormalizerIndex)
    (i : AmbientIndex) :
    alternatingSixTwoActualNormalizerCharacterEquivModel
        (d.toEquivariantMcKayEquiv
          (d.ambientEnumeration i)) =
      d.normalizerModelEnumeration (d.indexEquiv i) := by
  rw [d.toEquivariantMcKayEquiv_apply_enumerated]
  exact
    d.actualNormalizerCharacterEquiv_apply_normalizerEnumeration
      (d.indexEquiv i)

end AlternatingSixTwoModelCharacterTableCertificate

end InductiveMcKay
end McKayConjecture
