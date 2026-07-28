/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.AlternatingSixThreeNormalizerLinearRows
import McKayConjecture.InductiveMcKay.AlternatingSixThreeNormalizerSemidirectTable

/-!
# Finite three-normalizer row enumeration for `6.A₆`

The exact Sylow-three normalizer has been proved isomorphic to
`3^{1+2} ⋊ C₈`.  Eight of its `3'`-degree rows are the explicit linear
characters inflated from `C₈`.  A
`AlternatingSixThreeNormalizer.DegreeFourCompletion` supplies the exact
remaining local calculation: four degree-four rows and a proof that the
twelve rows are complete.

This file inserts such a completion into the model-facing
inductive-McKay interface and transports the resulting enumeration to the
actual fixed normalizer.  Thus the remaining global data are a finite
ambient enumeration, a matching with these twelve fixed rows, and the
transported equivariance check.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixThreeNormalizerEnumerationFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- The twelve-row index shape: eight proved linear rows and four
degree-four rows supplied by a completion. -/
abbrev AlternatingSixThreeSemidirectNormalizerCharacterRow :=
  AlternatingSixThreeNormalizer.PPrimeCharacterRow

/-- Complete local `3'`-row enumeration obtained from a certified
degree-four completion. -/
def alternatingSixThreeSemidirectNormalizerPPrimeCharacterEquiv
    (d : AlternatingSixThreeNormalizer.DegreeFourCompletion) :
    AlternatingSixThreeSemidirectNormalizerCharacterRow ≃
      AlternatingSixThreeSemidirectNormalizerCharacter :=
  AlternatingSixThreeNormalizer.DegreeFourCompletion.pPrimeCharacterEquiv d

@[simp]
theorem
    alternatingSixThreeSemidirectNormalizerPPrimeCharacterEquiv_linear
    (d : AlternatingSixThreeNormalizer.DegreeFourCompletion)
    (j : Fin 8) :
    alternatingSixThreeSemidirectNormalizerPPrimeCharacterEquiv d
        (Sum.inl j) =
      AlternatingSixThreeNormalizer.linearPPrimeCharacter j :=
  rfl

@[simp]
theorem
    alternatingSixThreeSemidirectNormalizerPPrimeCharacterEquiv_degree_linear
    (d : AlternatingSixThreeNormalizer.DegreeFourCompletion)
    (j : Fin 8) :
    (alternatingSixThreeSemidirectNormalizerPPrimeCharacterEquiv d
      (Sum.inl j)).1.degree = 1 :=
  AlternatingSixThreeNormalizer.linearPPrimeCharacter_degree j

@[simp]
theorem
    alternatingSixThreeSemidirectNormalizerPPrimeCharacterEquiv_degree_four
    (d : AlternatingSixThreeNormalizer.DegreeFourCompletion)
    (j : Fin 4) :
    (alternatingSixThreeSemidirectNormalizerPPrimeCharacterEquiv d
      (Sum.inr j)).1.degree = 4 :=
  d.degree_four j

/-- The completed twelve-row enumeration transported to the actual
canonical-cover Sylow-three normalizer. -/
def alternatingSixThreeActualNormalizerPPrimeCharacterEquiv
    (d : AlternatingSixThreeNormalizer.DegreeFourCompletion) :
    AlternatingSixThreeSemidirectNormalizerCharacterRow ≃
      PPrimeIrreducibleCharacter
        AlternatingSixUniversalCoverThreeNormalizer 3 :=
  (alternatingSixThreeSemidirectNormalizerPPrimeCharacterEquiv d).trans
    alternatingSixThreeActualNormalizerCharacterEquivSemidirect.symm

@[simp]
theorem
    alternatingSixThreeActualNormalizerCharacterEquiv_apply_enumerated
    (d : AlternatingSixThreeNormalizer.DegreeFourCompletion)
    (r : AlternatingSixThreeSemidirectNormalizerCharacterRow) :
    alternatingSixThreeActualNormalizerCharacterEquivSemidirect
        (alternatingSixThreeActualNormalizerPPrimeCharacterEquiv d r) =
      alternatingSixThreeSemidirectNormalizerPPrimeCharacterEquiv d r := by
  simp [
    alternatingSixThreeActualNormalizerPPrimeCharacterEquiv
  ]

/-- A certified local completion proves that the actual exact normalizer
has exactly twelve `3'`-degree irreducible characters. -/
theorem natCard_alternatingSixThreeActualNormalizerCharacter
    (d : AlternatingSixThreeNormalizer.DegreeFourCompletion) :
    Nat.card
        (PPrimeIrreducibleCharacter
          AlternatingSixUniversalCoverThreeNormalizer 3) =
      12 := by
  calc
    Nat.card
        (PPrimeIrreducibleCharacter
          AlternatingSixUniversalCoverThreeNormalizer 3) =
        Nat.card AlternatingSixThreeSemidirectNormalizerCharacterRow :=
      Nat.card_congr
        (alternatingSixThreeActualNormalizerPPrimeCharacterEquiv d).symm
    _ = 12 := by
      rw [Nat.card_sum, Nat.card_fin, Nat.card_fin]

/-- The remaining ordinary character-table data after fixing the exact
four-row completion of the concrete normalizer.

The normalizer field contains no ambient or equivariance assumptions; it
is precisely the missing finite local character calculation. -/
structure AlternatingSixThreeSemidirectCharacterTableCompletion
    (AmbientIndex : Type) [Fintype AmbientIndex] where
  /-- Four degree-four local rows completing the eight proved linear
  rows. -/
  normalizerDegreeFourCompletion :
    AlternatingSixThreeNormalizer.DegreeFourCompletion
  /-- Complete enumeration of ambient `3'`-degree rows. -/
  ambientEnumeration :
    AmbientIndex ≃ AlternatingSixThreeSemidirectAmbientCharacter
  /-- Matching of ambient rows with the twelve fixed normalizer rows. -/
  indexEquiv :
    AmbientIndex ≃ AlternatingSixThreeSemidirectNormalizerCharacterRow
  /-- Equivariance for the genuine stabilizer action transported to the
  concrete normalizer model. -/
  indexEquivariance :
    ∀ (a :
        SylowAutStabilizer
          (alternatingSixUniversalCoverSylow 3))
      (i : AmbientIndex),
      indexEquiv
          (ambientEnumeration.symm
            (a • ambientEnumeration i)) =
        (alternatingSixThreeSemidirectNormalizerPPrimeCharacterEquiv
            normalizerDegreeFourCompletion).symm
          (alternatingSixThreeSemidirectNormalizerCharacterAction a
            (alternatingSixThreeSemidirectNormalizerPPrimeCharacterEquiv
              normalizerDegreeFourCompletion
              (indexEquiv i)))

namespace AlternatingSixThreeSemidirectCharacterTableCompletion

variable {AmbientIndex : Type} [Fintype AmbientIndex]

/-- Insert the certified twelve-row local enumeration into the generic
model-facing table certificate. -/
def toSemidirectCharacterTableCertificate
    (d :
      AlternatingSixThreeSemidirectCharacterTableCompletion AmbientIndex) :
    AlternatingSixThreeSemidirectCharacterTableCertificate
      AmbientIndex AlternatingSixThreeSemidirectNormalizerCharacterRow where
  ambientEnumeration := d.ambientEnumeration
  normalizerModelEnumeration :=
    alternatingSixThreeSemidirectNormalizerPPrimeCharacterEquiv
      d.normalizerDegreeFourCompletion
  indexEquiv := d.indexEquiv
  indexEquivariance := d.indexEquivariance

/-- The generic finite-index certificate at the actual exact
normalizer. -/
def toFiniteIndexMcKayEquivCertificate
    (d :
      AlternatingSixThreeSemidirectCharacterTableCompletion AmbientIndex) :
    FiniteIndexMcKayEquivCertificate
      (alternatingSixUniversalCoverSylow 3)
      AmbientIndex AlternatingSixThreeSemidirectNormalizerCharacterRow :=
  d.toSemidirectCharacterTableCertificate
    |>.toFiniteIndexMcKayEquivCertificate

/-- The genuine equivariant McKay equivalence obtained after supplying
the local completion and remaining ambient table data. -/
def toEquivariantMcKayEquiv
    (d :
      AlternatingSixThreeSemidirectCharacterTableCompletion AmbientIndex) :
    EquivariantMcKayEquiv
      (alternatingSixUniversalCoverSylow 3) :=
  d.toFiniteIndexMcKayEquivCertificate.toEquivariantMcKayEquiv

@[simp]
theorem toEquivariantMcKayEquiv_apply_enumerated
    (d :
      AlternatingSixThreeSemidirectCharacterTableCompletion AmbientIndex)
    (i : AmbientIndex) :
    d.toEquivariantMcKayEquiv (d.ambientEnumeration i) =
      alternatingSixThreeActualNormalizerPPrimeCharacterEquiv
        d.normalizerDegreeFourCompletion (d.indexEquiv i) :=
  d.toFiniteIndexMcKayEquivCertificate
    |>.toEquivariantMcKayEquiv_apply_enumerated i

end AlternatingSixThreeSemidirectCharacterTableCompletion

end InductiveMcKay
end McKayConjecture
