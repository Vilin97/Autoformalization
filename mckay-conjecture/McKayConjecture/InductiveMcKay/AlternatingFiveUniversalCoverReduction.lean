/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveUniversalCover
import McKayConjecture.InductiveMcKay.AlternatingFiveSpecialLinearReduction

/-!
# The unconditional universal-cover input for `A₅`

The binary-icosahedral presentation proves that the fixed matrix group
`SL(2, 𝔽₅)` is a universal central cover of `A₅`.  Thus each exceptional
prime now requires only its exact normalizer projective table; no
group-theoretic cover witness remains.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- Install the exact `2`-local table in the certified universal cover. -/
def alternatingFiveProjectiveTableDataAtTwo
    (d :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowTwo) :
    AlternatingFiveProjectiveTableData 2 :=
  alternatingFiveProjectiveTableDataOfSpecialLinearTwo
    specialLinearTwoFiveUniversalCentralExtensionAlternatingFive d

/-- Install the exact `3`-local table in the certified universal cover. -/
def alternatingFiveProjectiveTableDataAtThree
    (d :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowThree) :
    AlternatingFiveProjectiveTableData 3 :=
  alternatingFiveProjectiveTableDataOfSpecialLinearThree
    specialLinearTwoFiveUniversalCentralExtensionAlternatingFive d

/-- Install the exact `5`-local table in the certified universal cover. -/
def alternatingFiveProjectiveTableDataAtFive
    (d :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowFive) :
    AlternatingFiveProjectiveTableData 5 :=
  alternatingFiveProjectiveTableDataOfSpecialLinearFive
    specialLinearTwoFiveUniversalCentralExtensionAlternatingFive d

/-- The three exact tables provide all exceptional-prime data for `A₅`. -/
def alternatingFiveExceptionalPrimeData
    (d₂ :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowTwo)
    (d₃ :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowThree)
    (d₅ :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowFive) :
    AlternatingFiveExceptionalPrimeProjectiveTableData :=
  alternatingFiveExceptionalPrimeDataOfSpecialLinear
    specialLinearTwoFiveUniversalCentralExtensionAlternatingFive
    d₂ d₃ d₅

/-- The exact `2`-local table is the only remaining input for the `A₅`
family verification at two. -/
theorem alternatingFive_twoFamilyVerification
    (d :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowTwo) :
    OneUniversalCoverOneSylowFamilyVerification
      2 alternatingFiveSimpleGroupFamily :=
  (alternatingFiveProjectiveTableDataAtTwo d).toFamilyVerification

/-- The exact `3`-local table is the only remaining input for the `A₅`
family verification at three. -/
theorem alternatingFive_threeFamilyVerification
    (d :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowThree) :
    OneUniversalCoverOneSylowFamilyVerification
      3 alternatingFiveSimpleGroupFamily :=
  (alternatingFiveProjectiveTableDataAtThree d).toFamilyVerification

/-- The exact `5`-local table is the only remaining input for the `A₅`
family verification at five. -/
theorem alternatingFive_fiveFamilyVerification
    (d :
      ExactNormalizerProjectiveTableData
        specialLinearTwoFiveSylowFive) :
    OneUniversalCoverOneSylowFamilyVerification
      5 alternatingFiveSimpleGroupFamily :=
  (alternatingFiveProjectiveTableDataAtFive d).toFamilyVerification

end InductiveMcKay
end McKayConjecture
