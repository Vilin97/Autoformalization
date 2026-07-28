/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.AlternatingSixFiveNormalizerSemidirectCharacterTable
import McKayConjecture.InductiveMcKay.AlternatingSixFiveNormalizerSemidirectTable

/-!
# The complete five-normalizer row enumeration for `6.A₆`

The concrete five-normalizer model is
`C₃ × (C₅ ⋊ C₄)`.  Its 24 explicit product representations give every
ordinary irreducible character, and all have degree one or two.  This file
inserts that complete `5'`-enumeration into the model-facing inductive-McKay
interface.

Consequently, a later character-table calculation only has to enumerate
the ambient rows, match them with these 24 fixed normalizer rows, and check
equivariance for the transported stabilizer action.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveNormalizerEnumerationFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The 24 explicit row indices for the five-normalizer model. -/
abbrev AlternatingSixFiveSemidirectNormalizerCharacterRow :=
  AlternatingSixFiveNormalizerSemidirectCharacterTable.CharacterRow

/-- Complete enumeration of the `5'`-degree irreducible characters of
the concrete five-normalizer model. -/
def alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv :
    AlternatingSixFiveSemidirectNormalizerCharacterRow ≃
      AlternatingSixFiveSemidirectNormalizerCharacter :=
  AlternatingSixFiveNormalizerSemidirectCharacterTable.pPrimeCharacterEquiv

@[simp]
theorem alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv_values
    (r : AlternatingSixFiveSemidirectNormalizerCharacterRow)
    (z : Multiplicative (ZMod 3))
    (g : CyclicFiveInversionSemidirect) :
    (alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv r).1.values
        (z, g) =
      (CyclicThree.pPrimeCharacterEquiv r.1).1.values z *
        (CyclicFiveInversionSemidirect.pPrimeCharacterEquiv r.2).1.values g :=
  AlternatingSixFiveNormalizerSemidirectCharacterTable.pPrimeCharacterEquiv_values
    r z g

@[simp]
theorem
    alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv_degree_linear
    (j : Fin 3) (k : Fin 4) :
    (alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv
      (j, CyclicFiveInversionSemidirect.CharacterRow.linear k)).1.degree =
        1 :=
  AlternatingSixFiveNormalizerSemidirectCharacterTable.pPrimeCharacterEquiv_degree_linear
    j k

@[simp]
theorem
    alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv_degree_twoDimensional
    (j : Fin 3) (k : Fin 4) :
    (alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv
      (j,
        CyclicFiveInversionSemidirect.CharacterRow.twoDimensional k)).1.degree =
        2 :=
  AlternatingSixFiveNormalizerSemidirectCharacterTable.pPrimeCharacterEquiv_degree_twoDimensional
    j k

/-- There are exactly 24 `5'`-degree irreducible characters of the concrete
five-normalizer model. -/
@[simp]
theorem natCard_alternatingSixFiveSemidirectNormalizerCharacter :
    Nat.card AlternatingSixFiveSemidirectNormalizerCharacter = 24 :=
  AlternatingSixFiveNormalizerSemidirectCharacterTable.natCard_pPrimeIrreducibleCharacter

/-- The remaining ordinary character-table data after the complete
normalizer-model enumeration has been fixed. -/
structure AlternatingSixFiveSemidirectCharacterTableCompletion
    (AmbientIndex : Type) [Fintype AmbientIndex] where
  /-- Complete enumeration of the ambient `5'`-degree rows. -/
  ambientEnumeration :
    AmbientIndex ≃ AlternatingSixFiveSemidirectAmbientCharacter
  /-- Matching of the ambient rows with the 24 fixed normalizer rows. -/
  indexEquiv :
    AmbientIndex ≃ AlternatingSixFiveSemidirectNormalizerCharacterRow
  /-- Equivariance of the matching for the transported stabilizer action. -/
  indexEquivariance :
    ∀ (a :
        SylowAutStabilizer
          (alternatingSixUniversalCoverSylow 5))
      (i : AmbientIndex),
      indexEquiv
          (ambientEnumeration.symm
            (a • ambientEnumeration i)) =
        alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv.symm
          (alternatingSixFiveSemidirectNormalizerCharacterAction a
            (alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv
              (indexEquiv i)))

namespace AlternatingSixFiveSemidirectCharacterTableCompletion

variable {AmbientIndex : Type} [Fintype AmbientIndex]

/-- Insert the verified 24-row normalizer enumeration into the
model-facing finite character-table certificate. -/
def toSemidirectCharacterTableCertificate
    (d :
      AlternatingSixFiveSemidirectCharacterTableCompletion AmbientIndex) :
    AlternatingSixFiveSemidirectCharacterTableCertificate
      AmbientIndex AlternatingSixFiveSemidirectNormalizerCharacterRow where
  ambientEnumeration := d.ambientEnumeration
  normalizerModelEnumeration :=
    alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv
  indexEquiv := d.indexEquiv
  indexEquivariance := d.indexEquivariance

/-- The generic finite-index certificate at the actual exact normalizer. -/
def toFiniteIndexMcKayEquivCertificate
    (d :
      AlternatingSixFiveSemidirectCharacterTableCompletion AmbientIndex) :
    FiniteIndexMcKayEquivCertificate
      (alternatingSixUniversalCoverSylow 5)
      AmbientIndex AlternatingSixFiveSemidirectNormalizerCharacterRow :=
  d.toSemidirectCharacterTableCertificate
    |>.toFiniteIndexMcKayEquivCertificate

/-- The equivariant McKay equivalence obtained after supplying the remaining
ambient enumeration, row matching, and equivariance proof. -/
def toEquivariantMcKayEquiv
    (d :
      AlternatingSixFiveSemidirectCharacterTableCompletion AmbientIndex) :
    EquivariantMcKayEquiv
      (alternatingSixUniversalCoverSylow 5) :=
  d.toFiniteIndexMcKayEquivCertificate.toEquivariantMcKayEquiv

@[simp]
theorem toEquivariantMcKayEquiv_apply_enumerated
    (d :
      AlternatingSixFiveSemidirectCharacterTableCompletion AmbientIndex)
    (i : AmbientIndex) :
    d.toEquivariantMcKayEquiv (d.ambientEnumeration i) =
      alternatingSixFiveActualNormalizerCharacterEquivSemidirect.symm
        (alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv
          (d.indexEquiv i)) :=
  d.toFiniteIndexMcKayEquivCertificate
    |>.toEquivariantMcKayEquiv_apply_enumerated i

end AlternatingSixFiveSemidirectCharacterTableCompletion

end InductiveMcKay
end McKayConjecture
