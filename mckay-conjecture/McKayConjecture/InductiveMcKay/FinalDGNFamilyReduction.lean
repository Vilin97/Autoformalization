/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.FinalQuasisimpleAlternatingDegreeReduction
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionFactorMatchedFibreEquivalence

/-!
# Final reduction from DGN transport and prime-supported families

This is the narrowest current public boundary of the proof.  The
central-intersection hypothesis is discharged from the
Dade--Glauberman--Nagao projective obstruction agreement.  The alternating
family has already been reduced to degrees at least the fixed prime.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open NormalSubgroupCentralIntersectionReduction

/-- DGN obstruction agreement and the prime-supported CFSG family inputs
imply the strengthened numerical inductive-McKay condition. -/
theorem centralScalarNumericalInductiveMcKay_of_dgn_cfsgAlternatingAtLeastPrime
    {p : ℕ} [Fact p.Prime]
    {lieType sporadic : FiniteGroupFamily.{0}}
    (dgn :
      ProductAmbientGlaubermanProjectiveObstructionClassAgreementHypothesis
        p)
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
  centralScalarNumericalInductiveMcKay_of_centralIntersection_cfsgAlternatingAtLeastPrime
    (centralScalarCentralIntersectionReductionHypothesis_of_projectiveObstructionClassAgreement
      dgn)
    coverage alternatingVerified lieTypeVerified sporadicVerified

/-- Public McKay equality from the DGN obstruction agreement and the
remaining prime-supported CFSG family verifications. -/
theorem statement_of_dgn_cfsgAlternatingAtLeastPrime
    {p : ℕ} [Fact p.Prime]
    {lieType sporadic : FiniteGroupFamily.{0}}
    (dgn :
      ProductAmbientGlaubermanProjectiveObstructionClassAgreementHypothesis
        p)
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
  (centralScalarNumericalInductiveMcKay_of_dgn_cfsgAlternatingAtLeastPrime
    dgn coverage alternatingVerified lieTypeVerified
    sporadicVerified).statement G P

end InductiveMcKay
end McKayConjecture
