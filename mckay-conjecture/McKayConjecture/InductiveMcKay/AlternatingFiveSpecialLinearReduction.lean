/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveCentralCover
import McKayConjecture.InductiveMcKay.AlternatingFiveProjectiveTableReduction

/-!
# Installing concrete `SL(2, 𝔽₅)` tables in the `A₅` reduction

`SpecialLinearTwoFive` now has fixed, literal Sylow subgroups at the three
exceptional primes.  Consequently an `A₅` table computation no longer has
to choose a cover type, group structure, finiteness instance, or Sylow
subgroup at each prime.

The constructors below take only:

* the still-missing proof that the concrete map from `SL(2, 𝔽₅)` to `A₅`
  is a universal central extension; and
* the actual equivariant character/projective tables for the three fixed
  exact normalizers of orders `24`, `12`, and `20`.

No family-verification proposition is added here.  The functions construct
the existing `AlternatingFiveProjectiveTableData` with all finite-group
choice fields filled by the explicit matrix model.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- Install the concrete `2`-local `SL(2, 𝔽₅)` table in the existing
`A₅` reduction datum. -/
def alternatingFiveProjectiveTableDataOfSpecialLinearTwo
    (E :
      UniversalCentralExtension
        SpecialLinearTwoFive (alternatingGroup (Fin 5)))
    (d :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowTwo) :
    AlternatingFiveProjectiveTableData 2 where
  cover := SpecialLinearTwoFive
  extension := E
  sylow := specialLinearTwoFiveSylowTwo
  tableData := d

/-- Install the concrete `3`-local `SL(2, 𝔽₅)` table. -/
def alternatingFiveProjectiveTableDataOfSpecialLinearThree
    (E :
      UniversalCentralExtension
        SpecialLinearTwoFive (alternatingGroup (Fin 5)))
    (d :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowThree) :
    AlternatingFiveProjectiveTableData 3 where
  cover := SpecialLinearTwoFive
  extension := E
  sylow := specialLinearTwoFiveSylowThree
  tableData := d

/-- Install the concrete `5`-local `SL(2, 𝔽₅)` table. -/
def alternatingFiveProjectiveTableDataOfSpecialLinearFive
    (E :
      UniversalCentralExtension
        SpecialLinearTwoFive (alternatingGroup (Fin 5)))
    (d :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowFive) :
    AlternatingFiveProjectiveTableData 5 where
  cover := SpecialLinearTwoFive
  extension := E
  sylow := specialLinearTwoFiveSylowFive
  tableData := d

/-- The three concrete tables fill every finite-group choice in the bundled
exceptional-prime datum. -/
def alternatingFiveExceptionalPrimeDataOfSpecialLinear
    (E :
      UniversalCentralExtension
        SpecialLinearTwoFive (alternatingGroup (Fin 5)))
    (d₂ :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowTwo)
    (d₃ :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowThree)
    (d₅ :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowFive) :
    AlternatingFiveExceptionalPrimeProjectiveTableData where
  atTwo :=
    alternatingFiveProjectiveTableDataOfSpecialLinearTwo E d₂
  atThree :=
    alternatingFiveProjectiveTableDataOfSpecialLinearThree E d₃
  atFive :=
    alternatingFiveProjectiveTableDataOfSpecialLinearFive E d₅

/-- The concrete `2`-local table proves the full `A₅` family verification
at `2`. -/
theorem alternatingFive_twoFamilyVerification_of_specialLinearTable
    (E :
      UniversalCentralExtension
        SpecialLinearTwoFive (alternatingGroup (Fin 5)))
    (d :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowTwo) :
    OneUniversalCoverOneSylowFamilyVerification
      2 alternatingFiveSimpleGroupFamily :=
  (alternatingFiveProjectiveTableDataOfSpecialLinearTwo E d)
    |>.toFamilyVerification

/-- The concrete `3`-local table proves the full `A₅` family verification
at `3`. -/
theorem alternatingFive_threeFamilyVerification_of_specialLinearTable
    (E :
      UniversalCentralExtension
        SpecialLinearTwoFive (alternatingGroup (Fin 5)))
    (d :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowThree) :
    OneUniversalCoverOneSylowFamilyVerification
      3 alternatingFiveSimpleGroupFamily :=
  (alternatingFiveProjectiveTableDataOfSpecialLinearThree E d)
    |>.toFamilyVerification

/-- The concrete `5`-local table proves the full `A₅` family verification
at `5`. -/
theorem alternatingFive_fiveFamilyVerification_of_specialLinearTable
    (E :
      UniversalCentralExtension
        SpecialLinearTwoFive (alternatingGroup (Fin 5)))
    (d :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowFive) :
    OneUniversalCoverOneSylowFamilyVerification
      5 alternatingFiveSimpleGroupFamily :=
  (alternatingFiveProjectiveTableDataOfSpecialLinearFive E d)
    |>.toFamilyVerification

end InductiveMcKay
end McKayConjecture
