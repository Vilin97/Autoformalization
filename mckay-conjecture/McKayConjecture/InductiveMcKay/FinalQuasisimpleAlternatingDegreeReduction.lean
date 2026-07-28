/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingBoundedDegreeAutomatic
import McKayConjecture.InductiveMcKay.FinalQuasisimplePrimeSupportReduction

/-!
# Final reduction with automatic small alternating degrees

This file connects the unconditional bounded-degree alternating result to
the final CFSG interface.  At the fixed prime `p`, the alternating input is
now requested only for groups `A_m` with `p ≤ m`.  All smaller alternating
targets are discharged by the prime-absent universal-cover construction.

The Lie-type and sporadic inputs remain prime-supported family
verifications, and CFSG coverage and the central-intersection reduction
remain explicit.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Final numerical reduction with the alternating family restricted to
degrees at least the fixed prime. -/
theorem centralScalarNumericalInductiveMcKay_of_centralIntersection_cfsgAlternatingAtLeastPrime
    {p : ℕ} [Fact p.Prime]
    {lieType sporadic : FiniteGroupFamily.{0}}
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (coverage :
      CFSGFamilyCoverage
        alternatingSimpleGroupFamily lieType sporadic)
    (alternatingVerified :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p (alternatingSimpleGroupFamilyAtLeast p))
    (lieTypeVerified :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p lieType)
    (sporadicVerified :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p sporadic) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_centralIntersection_primeSupportedCFSG
    centralIntersection coverage
    ⟨alternatingVerified.of_alternatingAtLeastPrime,
      lieTypeVerified, sporadicVerified⟩

/-- Public McKay equality with the automatic small-degree alternating
branch removed from the remaining CFSG input. -/
theorem statement_of_centralIntersection_cfsgAlternatingAtLeastPrime
    {p : ℕ} [Fact p.Prime]
    {lieType sporadic : FiniteGroupFamily.{0}}
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (coverage :
      CFSGFamilyCoverage
        alternatingSimpleGroupFamily lieType sporadic)
    (alternatingVerified :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p (alternatingSimpleGroupFamilyAtLeast p))
    (lieTypeVerified :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p lieType)
    (sporadicVerified :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p sporadic)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (centralScalarNumericalInductiveMcKay_of_centralIntersection_cfsgAlternatingAtLeastPrime
    centralIntersection coverage alternatingVerified
    lieTypeVerified sporadicVerified).statement G P

end InductiveMcKay
end McKayConjecture
