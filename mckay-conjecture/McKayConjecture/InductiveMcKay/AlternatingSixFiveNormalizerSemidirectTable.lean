/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverFiveNormalizerSemidirect
import McKayConjecture.InductiveMcKay.FiniteIndexMcKayEquiv

/-!
# Finite five-local character tables through the semidirect normalizer model

The fixed five-normalizer of the canonical universal cover of `A₆` is
identified with the concrete group `C₃ × (C₅ ⋊ C₄)`.  This file makes that
identification usable by a finite character-table computation.

A certificate enumerates ambient rows directly, enumerates local rows in
the concrete semidirect-product model, and checks equivariance on row
indices.  The model rows are transported to the actual fixed normalizer by
the proved group equivalence; no normalizer character or matching is
postulated by the conversion.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveNormalizerSemidirectTableFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The ambient `5'`-irreducible characters of the canonical cover. -/
abbrev AlternatingSixFiveSemidirectAmbientCharacter :=
  PPrimeIrreducibleCharacter AlternatingSixUniversalCover 5

/-- The `5'`-irreducible characters of the concrete
`C₃ × (C₅ ⋊ C₄)` normalizer model. -/
abbrev AlternatingSixFiveSemidirectNormalizerCharacter :=
  PPrimeIrreducibleCharacter
    AlternatingSixFiveNormalizerSemidirect 5

/-- Pull characters of the actual fixed normalizer back to the concrete
semidirect-product model. -/
def alternatingSixFiveActualNormalizerCharacterEquivSemidirect :
    PPrimeIrreducibleCharacter
        (SylowNormalizer (alternatingSixUniversalCoverSylow 5)) 5 ≃
      AlternatingSixFiveSemidirectNormalizerCharacter :=
  IrreducibleCharacter.pPrimeComapEquiv 5
    alternatingSixFiveNormalizerSemidirectEquivUniversalCoverNormalizer

/-- The action of an ambient Sylow stabilizer on model characters, defined
by transport through the proved normalizer equivalence.  This is the action
that a model character table must use when checking equivariance. -/
def alternatingSixFiveSemidirectNormalizerCharacterAction
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5))
    (ψ : AlternatingSixFiveSemidirectNormalizerCharacter) :
    AlternatingSixFiveSemidirectNormalizerCharacter :=
  alternatingSixFiveActualNormalizerCharacterEquivSemidirect
    (a •
      alternatingSixFiveActualNormalizerCharacterEquivSemidirect.symm ψ)

@[simp]
theorem alternatingSixFiveSemidirectNormalizerCharacterAction_transported
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5))
    (ψ :
      PPrimeIrreducibleCharacter
        (SylowNormalizer (alternatingSixUniversalCoverSylow 5)) 5) :
    alternatingSixFiveSemidirectNormalizerCharacterAction a
        (alternatingSixFiveActualNormalizerCharacterEquivSemidirect ψ) =
      alternatingSixFiveActualNormalizerCharacterEquivSemidirect
        (a • ψ) := by
  simp [alternatingSixFiveSemidirectNormalizerCharacterAction]

/-- Finite ordinary-table data with local rows written in the concrete
semidirect-product model.

The final field is the genuine ambient-stabilizer equivariance condition:
the local action is transported from the actual normalizer, rather than
replaced by an unrelated automorphism action on the abstract model. -/
structure AlternatingSixFiveSemidirectCharacterTableCertificate
    (AmbientIndex NormalizerIndex : Type)
    [Fintype AmbientIndex]
    [Fintype NormalizerIndex] where
  /-- Complete enumeration of the ambient `5'`-rows. -/
  ambientEnumeration :
    AmbientIndex ≃ AlternatingSixFiveSemidirectAmbientCharacter
  /-- Complete enumeration of the model-normalizer `5'`-rows. -/
  normalizerModelEnumeration :
    NormalizerIndex ≃
      AlternatingSixFiveSemidirectNormalizerCharacter
  /-- The proposed finite row matching. -/
  indexEquiv : AmbientIndex ≃ NormalizerIndex
  /-- Equivariance of the proposed matching, checked on finite row
  indices after transporting the normalizer action to the model. -/
  indexEquivariance :
    ∀ (a :
        SylowAutStabilizer
          (alternatingSixUniversalCoverSylow 5))
      (i : AmbientIndex),
      indexEquiv
          (ambientEnumeration.symm
            (a • ambientEnumeration i)) =
        normalizerModelEnumeration.symm
          (alternatingSixFiveSemidirectNormalizerCharacterAction a
            (normalizerModelEnumeration (indexEquiv i)))

namespace AlternatingSixFiveSemidirectCharacterTableCertificate

variable
  {AmbientIndex NormalizerIndex : Type}
  [Fintype AmbientIndex]
  [Fintype NormalizerIndex]

/-- Transport the model-normalizer row enumeration to the actual fixed
normalizer. -/
def normalizerEnumeration
    (d :
      AlternatingSixFiveSemidirectCharacterTableCertificate
        AmbientIndex NormalizerIndex) :
    NormalizerIndex ≃
      PPrimeIrreducibleCharacter
        (SylowNormalizer (alternatingSixUniversalCoverSylow 5)) 5 :=
  d.normalizerModelEnumeration.trans
    alternatingSixFiveActualNormalizerCharacterEquivSemidirect.symm

@[simp]
theorem actualNormalizerCharacterEquiv_apply_normalizerEnumeration
    (d :
      AlternatingSixFiveSemidirectCharacterTableCertificate
        AmbientIndex NormalizerIndex)
    (j : NormalizerIndex) :
    alternatingSixFiveActualNormalizerCharacterEquivSemidirect
        (d.normalizerEnumeration j) =
      d.normalizerModelEnumeration j := by
  simp [normalizerEnumeration]

/-- Convert the model-facing certificate to the generic finite-index
equivariant McKay certificate at the actual exact normalizer. -/
def toFiniteIndexMcKayEquivCertificate
    (d :
      AlternatingSixFiveSemidirectCharacterTableCertificate
        AmbientIndex NormalizerIndex) :
    FiniteIndexMcKayEquivCertificate
      (alternatingSixUniversalCoverSylow 5)
      AmbientIndex NormalizerIndex where
  ambientEnumeration := d.ambientEnumeration
  normalizerEnumeration := d.normalizerEnumeration
  indexEquiv := d.indexEquiv
  indexEquivariance := by
    intro a i
    simpa [
      normalizerEnumeration,
      alternatingSixFiveSemidirectNormalizerCharacterAction
    ] using d.indexEquivariance a i

/-- The equivariant character equivalence certified by the finite ambient
and model-normalizer tables. -/
def toEquivariantMcKayEquiv
    (d :
      AlternatingSixFiveSemidirectCharacterTableCertificate
        AmbientIndex NormalizerIndex) :
    EquivariantMcKayEquiv
      (alternatingSixUniversalCoverSylow 5) :=
  d.toFiniteIndexMcKayEquivCertificate.toEquivariantMcKayEquiv

@[simp]
theorem toEquivariantMcKayEquiv_apply_enumerated
    (d :
      AlternatingSixFiveSemidirectCharacterTableCertificate
        AmbientIndex NormalizerIndex)
    (i : AmbientIndex) :
    d.toEquivariantMcKayEquiv (d.ambientEnumeration i) =
      d.normalizerEnumeration (d.indexEquiv i) :=
  d.toFiniteIndexMcKayEquivCertificate
    |>.toEquivariantMcKayEquiv_apply_enumerated i

/-- The matched local row, pulled back to the concrete normalizer model, is
exactly the enumerated model row. -/
theorem actualNormalizerCharacterEquiv_apply_matchedRow
    (d :
      AlternatingSixFiveSemidirectCharacterTableCertificate
        AmbientIndex NormalizerIndex)
    (i : AmbientIndex) :
    alternatingSixFiveActualNormalizerCharacterEquivSemidirect
        (d.toEquivariantMcKayEquiv
          (d.ambientEnumeration i)) =
      d.normalizerModelEnumeration (d.indexEquiv i) := by
  rw [d.toEquivariantMcKayEquiv_apply_enumerated]
  exact
    d.actualNormalizerCharacterEquiv_apply_normalizerEnumeration
      (d.indexEquiv i)

end AlternatingSixFiveSemidirectCharacterTableCertificate

end InductiveMcKay
end McKayConjecture
