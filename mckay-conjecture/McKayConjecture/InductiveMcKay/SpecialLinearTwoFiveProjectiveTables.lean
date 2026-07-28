/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingFiveUniversalCoverReduction
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveFiveFixedProjectiveRows
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveThreeFixedProjectiveRows
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveTwoProjectiveTable

/-!
# Complete projective tables for the binary icosahedral cover

This file packages the checked `p = 2,3,5` tables as the generic
exact-normalizer data consumed by the universal-cover reduction.  Together
with the automatic prime-absent construction, they verify the `A₅` family
at every prime.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- Exact-normalizer projective data for `SL(2, 𝔽₅)` at `p = 2`. -/
def specialLinearTwoFiveTwoExactNormalizerProjectiveTableData :
    ExactNormalizerProjectiveTableData
      specialLinearTwoFiveSylowTwo :=
  specialLinearTwoFiveTwoProjectiveTableCompletion
    |>.toFiniteIndexExactNormalizerProjectiveTableCertificate
    |>.toExactNormalizerProjectiveTableData

/-- Exact-normalizer projective data for `SL(2, 𝔽₅)` at `p = 3`. -/
def specialLinearTwoFiveThreeExactNormalizerProjectiveTableData :
    ExactNormalizerProjectiveTableData
      specialLinearTwoFiveSylowThree :=
  specialLinearTwoFiveThreeProjectiveTableCompletion
    |>.toFiniteIndexExactNormalizerProjectiveTableCertificate
    |>.toExactNormalizerProjectiveTableData

/-- Exact-normalizer projective data for `SL(2, 𝔽₅)` at `p = 5`. -/
def specialLinearTwoFiveFiveExactNormalizerProjectiveTableData :
    ExactNormalizerProjectiveTableData
      specialLinearTwoFiveSylowFive :=
  specialLinearTwoFiveFiveProjectiveTableCompletion
    |>.toFiniteIndexExactNormalizerProjectiveTableCertificate
    |>.toExactNormalizerProjectiveTableData

/-- The complete `A₅` universal-cover verification at `p = 2`. -/
theorem alternatingFiveFamilyVerification_two :
    OneUniversalCoverOneSylowFamilyVerification
      2 alternatingFiveSimpleGroupFamily :=
  alternatingFive_twoFamilyVerification
    specialLinearTwoFiveTwoExactNormalizerProjectiveTableData

/-- The complete `A₅` universal-cover verification at `p = 3`. -/
theorem alternatingFiveFamilyVerification_three :
    OneUniversalCoverOneSylowFamilyVerification
      3 alternatingFiveSimpleGroupFamily :=
  alternatingFive_threeFamilyVerification
    specialLinearTwoFiveThreeExactNormalizerProjectiveTableData

/-- The complete `A₅` universal-cover verification at `p = 5`. -/
theorem alternatingFiveFamilyVerification_five :
    OneUniversalCoverOneSylowFamilyVerification
      5 alternatingFiveSimpleGroupFamily :=
  alternatingFive_fiveFamilyVerification
    specialLinearTwoFiveFiveExactNormalizerProjectiveTableData

/-- The binary-icosahedral tables settle the exceptional primes, while
the prime-absent construction settles every prime greater than five. -/
theorem alternatingFiveFamilyVerification
    (p : ℕ) [Fact p.Prime] :
    OneUniversalCoverOneSylowFamilyVerification
      p alternatingFiveSimpleGroupFamily := by
  by_cases hpTwo : p = 2
  · subst p
    exact alternatingFiveFamilyVerification_two
  by_cases hpThree : p = 3
  · subst p
    exact alternatingFiveFamilyVerification_three
  by_cases hpFive : p = 5
  · subst p
    exact alternatingFiveFamilyVerification_five
  apply alternatingFiveSimpleGroupFamily_verification
  have hpPrime : p.Prime := Fact.out
  have hpTwoLe : 2 ≤ p := hpPrime.two_le
  by_contra hpNotGreater
  have hpLeFive : p ≤ 5 := Nat.le_of_not_gt hpNotGreater
  have hpFour : p ≠ 4 := by
    rintro rfl
    norm_num at hpPrime
  omega

end InductiveMcKay
end McKayConjecture
