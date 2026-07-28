/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverThreeNormalizerQuotientModel
import McKayConjecture.InductiveMcKay.FiniteIndexMcKayEquiv

/-!
# Finite ordinary-table certificates for the three-local `A₆` case

This file isolates the ordinary character-table part of the fixed-cover
calculation at `p = 3`.  A certificate contains honest finite
enumerations of

* the ambient `3'`-degree irreducible characters of the canonical cover;
* the `3'`-degree irreducible characters of the actual order-`216`
  Sylow normalizer;
* a matching of the two finite row sets; and
* equivariance of that matching under the actual Sylow-stabilizer action.

The proved order-`36` action-range/target-normalizer quotient model is
available from the imported group-theory file, but it is not substituted
for the actual normalizer here.  Characters of a central extension are not
characters of its quotient, and no splitting of the order-six center has
been proved.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixThreeFiniteTableFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- The ambient `3'`-degree irreducible characters of the canonical cover. -/
abbrev AlternatingSixThreeAmbientCharacter :=
  PPrimeIrreducibleCharacter AlternatingSixUniversalCover 3

/-- The local `3'`-degree irreducible characters of the actual fixed
Sylow-three normalizer. -/
abbrev AlternatingSixThreeNormalizerCharacter :=
  PPrimeIrreducibleCharacter
    AlternatingSixUniversalCoverThreeNormalizer 3

/-- Honest finite ordinary-table data for the fixed three-local
calculation. -/
structure AlternatingSixThreeCharacterTableCertificate
    (AmbientIndex NormalizerIndex : Type)
    [Fintype AmbientIndex]
    [Fintype NormalizerIndex] where
  /-- Complete finite enumeration of the ambient `3'`-rows. -/
  ambientEnumeration :
    AmbientIndex ≃ AlternatingSixThreeAmbientCharacter
  /-- Complete finite enumeration of the actual-normalizer `3'`-rows. -/
  normalizerEnumeration :
    NormalizerIndex ≃ AlternatingSixThreeNormalizerCharacter
  /-- The proposed finite row matching. -/
  indexEquiv : AmbientIndex ≃ NormalizerIndex
  /-- Equivariance of the proposed matching under the genuine action of
  the ambient Sylow stabilizer on both character sets. -/
  indexEquivariance :
    ∀ (a :
        SylowAutStabilizer
          (alternatingSixUniversalCoverSylow 3))
      (i : AmbientIndex),
      indexEquiv
          (ambientEnumeration.symm
            (a • ambientEnumeration i)) =
        normalizerEnumeration.symm
          (a • normalizerEnumeration (indexEquiv i))

namespace AlternatingSixThreeCharacterTableCertificate

variable
  {AmbientIndex NormalizerIndex : Type}
  [Fintype AmbientIndex]
  [Fintype NormalizerIndex]

/-- Convert the explicitly split fields to the generic finite-index
equivariant McKay certificate. -/
def toFiniteIndexMcKayEquivCertificate
    (d :
      AlternatingSixThreeCharacterTableCertificate
        AmbientIndex NormalizerIndex) :
    FiniteIndexMcKayEquivCertificate
      (alternatingSixUniversalCoverSylow 3)
      AmbientIndex NormalizerIndex where
  ambientEnumeration := d.ambientEnumeration
  normalizerEnumeration := d.normalizerEnumeration
  indexEquiv := d.indexEquiv
  indexEquivariance := d.indexEquivariance

/-- The genuine character-level equivariant McKay equivalence certified by
the finite tables. -/
def toEquivariantMcKayEquiv
    (d :
      AlternatingSixThreeCharacterTableCertificate
        AmbientIndex NormalizerIndex) :
    EquivariantMcKayEquiv
      (alternatingSixUniversalCoverSylow 3) :=
  d.toFiniteIndexMcKayEquivCertificate.toEquivariantMcKayEquiv

@[simp]
theorem toEquivariantMcKayEquiv_apply_enumerated
    (d :
      AlternatingSixThreeCharacterTableCertificate
        AmbientIndex NormalizerIndex)
    (i : AmbientIndex) :
    d.toEquivariantMcKayEquiv (d.ambientEnumeration i) =
      d.normalizerEnumeration (d.indexEquiv i) :=
  d.toFiniteIndexMcKayEquivCertificate
    |>.toEquivariantMcKayEquiv_apply_enumerated i

end AlternatingSixThreeCharacterTableCertificate

end InductiveMcKay
end McKayConjecture
