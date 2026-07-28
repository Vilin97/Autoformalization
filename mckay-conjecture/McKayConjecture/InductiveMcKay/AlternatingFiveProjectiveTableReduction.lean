/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingBoundedDegreeAutomatic
import McKayConjecture.InductiveMcKay.ExactNormalizerProjectiveTableData

/-!
# Reducing the `A₅` cases to concrete projective character tables

The universal central extension of `A₅` is the first alternating-family case
whose local McKay datum is not automatic at the primes `2`, `3`, and `5`.
The current mathlib character API does not contain an enumerated character
table for `A₅` or its binary cover.  This file therefore isolates the
smallest direct-computation interface needed to add those tables.

For one chosen universal cover and one chosen Sylow subgroup, the input is
`ExactNormalizerProjectiveTableData`: an equivariant bijection of the two
finite `p'`-character tables and checked projective factor/scalar identities
for every paired row.  All family transport, all other universal covers and
Sylow subgroups, and all ordinary semidirect-product subgroup conditions are
then automatic.

In particular, `AlternatingFiveExceptionalPrimeProjectiveTableData` consists
of three finite computations, one at each of `2`, `3`, and `5`; it is not a
restatement of a family-wide inductive McKay hypothesis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- One concrete universal cover of `A₅`, one concrete Sylow `p`-subgroup,
and the projective character-table calculation at its exact normalizer. -/
structure AlternatingFiveProjectiveTableData (p : ℕ) where
  /-- The chosen finite model of the universal cover. -/
  cover : Type
  [coverGroup : Group cover]
  [coverFinite : Finite cover]
  /-- The checked universal central extension onto `A₅`. -/
  extension :
    UniversalCentralExtension
      cover (alternatingGroup (Fin 5))
  /-- The chosen Sylow subgroup used in the local table. -/
  sylow : Sylow p cover
  /-- The exact-normalizer character and projective table calculation. -/
  tableData : ExactNormalizerProjectiveTableData sylow

namespace AlternatingFiveProjectiveTableData

variable {p : ℕ}

/-- Extract the full local inductive McKay datum computed by the tables. -/
def localData
    (d : AlternatingFiveProjectiveTableData p) :
    letI := d.coverGroup
    letI := d.coverFinite
    LocalInductiveMcKayData d.sylow := by
  letI := d.coverGroup
  letI := d.coverFinite
  exact d.tableData.toLocalInductiveMcKayData

/-- A single checked cover/Sylow table transports to the full abstract
`A₅` family verification at `p`. -/
theorem toFamilyVerification
    (d : AlternatingFiveProjectiveTableData p) :
    OneUniversalCoverOneSylowFamilyVerification
      p alternatingFiveSimpleGroupFamily := by
  intro S _ _ hmember _ _
  obtain ⟨e⟩ :=
    (alternatingFiveSimpleGroupFamily_contains_iff S).mp hmember
  letI : Group d.cover := d.coverGroup
  letI : Finite d.cover := d.coverFinite
  exact
    ⟨d.cover, inferInstance, inferInstance,
      d.extension.targetEquiv e.symm, d.sylow, ⟨d.localData⟩⟩

end AlternatingFiveProjectiveTableData

/-- The three genuinely nonautomatic `A₅` computations.  Each field is a
finite character/projective table calculation for one explicitly chosen
cover and Sylow subgroup. -/
structure AlternatingFiveExceptionalPrimeProjectiveTableData where
  /-- The `2`-local projective table. -/
  atTwo : AlternatingFiveProjectiveTableData 2
  /-- The `3`-local projective table. -/
  atThree : AlternatingFiveProjectiveTableData 3
  /-- The `5`-local projective table. -/
  atFive : AlternatingFiveProjectiveTableData 5

namespace AlternatingFiveExceptionalPrimeProjectiveTableData

/-- The bundled exceptional tables settle the `A₅` family at `p = 2`. -/
theorem twoFamilyVerification
    (d : AlternatingFiveExceptionalPrimeProjectiveTableData) :
    OneUniversalCoverOneSylowFamilyVerification
      2 alternatingFiveSimpleGroupFamily :=
  d.atTwo.toFamilyVerification

/-- The bundled exceptional tables settle the `A₅` family at `p = 3`. -/
theorem threeFamilyVerification
    (d : AlternatingFiveExceptionalPrimeProjectiveTableData) :
    OneUniversalCoverOneSylowFamilyVerification
      3 alternatingFiveSimpleGroupFamily :=
  d.atThree.toFamilyVerification

/-- The bundled exceptional tables settle the `A₅` family at `p = 5`. -/
theorem fiveFamilyVerification
    (d : AlternatingFiveExceptionalPrimeProjectiveTableData) :
    OneUniversalCoverOneSylowFamilyVerification
      5 alternatingFiveSimpleGroupFamily :=
  d.atFive.toFamilyVerification

end AlternatingFiveExceptionalPrimeProjectiveTableData

/-- Split the full alternating-family verification into the first simple
group `A₅` and the residual family of degrees at least six. -/
theorem alternatingSimpleGroupFamily_verification_of_five_and_atLeastSix
    {p : ℕ}
    (hfive :
      OneUniversalCoverOneSylowFamilyVerification
        p alternatingFiveSimpleGroupFamily)
    (hlarge :
      OneUniversalCoverOneSylowFamilyVerification
        p (alternatingSimpleGroupFamilyAtLeast 6)) :
    OneUniversalCoverOneSylowFamilyVerification
      p alternatingSimpleGroupFamily.{0} := by
  intro S _ _ hmember hsimple hnoncomm
  obtain ⟨n, hn⟩ := hmember
  by_cases hzero : n = 0
  · apply hfive S
      (show alternatingFiveSimpleGroupFamily.Contains S from
        ⟨n, by omega, hn⟩)
      hsimple hnoncomm
  · apply hlarge S
      (show (alternatingSimpleGroupFamilyAtLeast 6).Contains S from
        ⟨n, by omega, hn⟩)
      hsimple hnoncomm

end InductiveMcKay
end McKayConjecture
