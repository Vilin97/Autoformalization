/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingFiveSpecialLinearReduction
import McKayConjecture.InductiveMcKay.FiniteIndexProjectiveTable

/-!
# Finite-index projective-table obligations for `SL(2, 𝔽₅)`

This file specializes the reusable finite-index certificate interface to
the fixed Sylow subgroups of `SpecialLinearTwoFive`.  It does not add any
character-table assumptions beyond the three finite certificates.

After supplying those certificates, the only non-table input needed by the
existing `A₅` reduction is the proof that the concrete central cover is the
universal central extension.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The three finite exact-normalizer table certificates for the fixed
`2`-, `3`-, and `5`-Sylow subgroups of `SL(2, 𝔽₅)`.

Each pair of index types may be chosen independently, allowing a concrete
table verifier to use the row numbering native to each table. -/
structure SpecialLinearTwoFiveFiniteIndexProjectiveTableData where
  /-- Ambient row indices for the `2`-local table. -/
  twoAmbientIndex : Type
  /-- Normalizer row indices for the `2`-local table. -/
  twoNormalizerIndex : Type
  [twoAmbientFintype : Fintype twoAmbientIndex]
  [twoNormalizerFintype : Fintype twoNormalizerIndex]
  /-- Complete finite-index certificate at `p = 2`. -/
  atTwo :
    FiniteIndexExactNormalizerProjectiveTableCertificate
      specialLinearTwoFiveSylowTwo
      twoAmbientIndex twoNormalizerIndex
  /-- Ambient row indices for the `3`-local table. -/
  threeAmbientIndex : Type
  /-- Normalizer row indices for the `3`-local table. -/
  threeNormalizerIndex : Type
  [threeAmbientFintype : Fintype threeAmbientIndex]
  [threeNormalizerFintype : Fintype threeNormalizerIndex]
  /-- Complete finite-index certificate at `p = 3`. -/
  atThree :
    FiniteIndexExactNormalizerProjectiveTableCertificate
      specialLinearTwoFiveSylowThree
      threeAmbientIndex threeNormalizerIndex
  /-- Ambient row indices for the `5`-local table. -/
  fiveAmbientIndex : Type
  /-- Normalizer row indices for the `5`-local table. -/
  fiveNormalizerIndex : Type
  [fiveAmbientFintype : Fintype fiveAmbientIndex]
  [fiveNormalizerFintype : Fintype fiveNormalizerIndex]
  /-- Complete finite-index certificate at `p = 5`. -/
  atFive :
    FiniteIndexExactNormalizerProjectiveTableCertificate
      specialLinearTwoFiveSylowFive
      fiveAmbientIndex fiveNormalizerIndex

namespace SpecialLinearTwoFiveFiniteIndexProjectiveTableData

/-- The ordinary exact-normalizer table datum reconstructed at `p = 2`. -/
def twoExactNormalizerTableData
    (d : SpecialLinearTwoFiveFiniteIndexProjectiveTableData) :
    ExactNormalizerProjectiveTableData
      specialLinearTwoFiveSylowTwo := by
  letI := d.twoAmbientFintype
  letI := d.twoNormalizerFintype
  exact d.atTwo.toExactNormalizerProjectiveTableData

/-- The ordinary exact-normalizer table datum reconstructed at `p = 3`. -/
def threeExactNormalizerTableData
    (d : SpecialLinearTwoFiveFiniteIndexProjectiveTableData) :
    ExactNormalizerProjectiveTableData
      specialLinearTwoFiveSylowThree := by
  letI := d.threeAmbientFintype
  letI := d.threeNormalizerFintype
  exact d.atThree.toExactNormalizerProjectiveTableData

/-- The ordinary exact-normalizer table datum reconstructed at `p = 5`. -/
def fiveExactNormalizerTableData
    (d : SpecialLinearTwoFiveFiniteIndexProjectiveTableData) :
    ExactNormalizerProjectiveTableData
      specialLinearTwoFiveSylowFive := by
  letI := d.fiveAmbientFintype
  letI := d.fiveNormalizerFintype
  exact d.atFive.toExactNormalizerProjectiveTableData

/-- Install all three finite certificates in the existing exceptional-prime
`A₅` reduction. -/
def toAlternatingFiveExceptionalPrimeData
    (d : SpecialLinearTwoFiveFiniteIndexProjectiveTableData)
    (E :
      UniversalCentralExtension
        SpecialLinearTwoFive (alternatingGroup (Fin 5))) :
    AlternatingFiveExceptionalPrimeProjectiveTableData :=
  alternatingFiveExceptionalPrimeDataOfSpecialLinear
    E
    d.twoExactNormalizerTableData
    d.threeExactNormalizerTableData
    d.fiveExactNormalizerTableData

/-- The finite `2`-local certificate settles the `A₅` family at `2`, once
the fixed central cover is known to be universal. -/
theorem twoFamilyVerification
    (d : SpecialLinearTwoFiveFiniteIndexProjectiveTableData)
    (E :
      UniversalCentralExtension
        SpecialLinearTwoFive (alternatingGroup (Fin 5))) :
    OneUniversalCoverOneSylowFamilyVerification
      2 alternatingFiveSimpleGroupFamily :=
  (d.toAlternatingFiveExceptionalPrimeData E).twoFamilyVerification

/-- The finite `3`-local certificate settles the `A₅` family at `3`. -/
theorem threeFamilyVerification
    (d : SpecialLinearTwoFiveFiniteIndexProjectiveTableData)
    (E :
      UniversalCentralExtension
        SpecialLinearTwoFive (alternatingGroup (Fin 5))) :
    OneUniversalCoverOneSylowFamilyVerification
      3 alternatingFiveSimpleGroupFamily :=
  (d.toAlternatingFiveExceptionalPrimeData E).threeFamilyVerification

/-- The finite `5`-local certificate settles the `A₅` family at `5`. -/
theorem fiveFamilyVerification
    (d : SpecialLinearTwoFiveFiniteIndexProjectiveTableData)
    (E :
      UniversalCentralExtension
        SpecialLinearTwoFive (alternatingGroup (Fin 5))) :
    OneUniversalCoverOneSylowFamilyVerification
      5 alternatingFiveSimpleGroupFamily :=
  (d.toAlternatingFiveExceptionalPrimeData E).fiveFamilyVerification

end SpecialLinearTwoFiveFiniteIndexProjectiveTableData

end InductiveMcKay
end McKayConjecture
