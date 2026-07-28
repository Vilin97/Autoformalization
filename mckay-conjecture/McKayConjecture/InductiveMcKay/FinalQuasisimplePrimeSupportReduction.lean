/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingUniversalCoverPrimeSupport
import McKayConjecture.InductiveMcKay.FinalReduction
import McKayConjecture.InductiveMcKay.QuasisimpleSimpleQuotientPrimeSupport

/-!
# Final reduction with the prime-supported quasisimple residual

This file plugs the exact simple-quotient prime-support reductions into the
final central-scalar theorem.  It provides three progressively more
classification-oriented entry points:

1. the combined simple-quotient/structural residual on arbitrary
   quasisimple groups;
2. a three-family CFSG split with verification only at primes dividing the
   simple target; and
3. the same split with the alternating family reduced concretely to
   `A_{n+5}` and the numerical condition `p ≤ n+5`.

The central-intersection input remains independent and explicit.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- The central-intersection reduction and the exact prime-supported
structural residual imply the numerical inductive-McKay condition. -/
theorem centralScalarNumericalInductiveMcKay_of_centralIntersection_simpleQuotientStructural
    {p : ℕ} [Fact p.Prime]
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (covers :
      SimpleQuotientStructuralResidualHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_centralIntersection_quasisimple
    centralIntersection covers.toQuasisimple

/-- Public McKay equality from the central-intersection input and the exact
simple-quotient/structural quasisimple residual. -/
theorem statement_of_centralIntersection_simpleQuotientStructural
    {p : ℕ} [Fact p.Prime]
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (covers :
      SimpleQuotientStructuralResidualHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (centralScalarNumericalInductiveMcKay_of_centralIntersection_simpleQuotientStructural
    centralIntersection covers).statement G P

/-- Final numerical reduction through a prime-supported three-family CFSG
interface. -/
theorem centralScalarNumericalInductiveMcKay_of_centralIntersection_primeSupportedCFSG
    {p : ℕ} [Fact p.Prime]
    {alternating lieType sporadic :
      FiniteGroupFamily.{0}}
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (coverage :
      CFSGFamilyCoverage alternating lieType sporadic)
    (verified :
      PrimeSupportedCFSGFamilyVerification
        p alternating lieType sporadic) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_centralIntersection_quasisimple
    centralIntersection
    (coverage.toQuasisimple_of_primeSupported verified)

/-- Public McKay equality through prime-supported CFSG coverage and
family verification. -/
theorem statement_of_centralIntersection_primeSupportedCFSG
    {p : ℕ} [Fact p.Prime]
    {alternating lieType sporadic :
      FiniteGroupFamily.{0}}
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (coverage :
      CFSGFamilyCoverage alternating lieType sporadic)
    (verified :
      PrimeSupportedCFSGFamilyVerification
        p alternating lieType sporadic)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (centralScalarNumericalInductiveMcKay_of_centralIntersection_primeSupportedCFSG
    centralIntersection coverage verified).statement G P

/-- Final numerical reduction in which mathlib's concrete alternating
family is reduced to the exact parameter range `p ≤ n+5`. -/
theorem centralScalarNumericalInductiveMcKay_of_centralIntersection_cfsgAlternatingRepresentatives
    {p : ℕ} [Fact p.Prime]
    {lieType sporadic : FiniteGroupFamily.{0}}
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (coverage :
      CFSGFamilyCoverage
        alternatingSimpleGroupFamily lieType sporadic)
    (alternatingVerified :
      AlternatingUniversalCoverPrimeSupportedVerification p)
    (lieTypeVerified :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p lieType)
    (sporadicVerified :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p sporadic) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_centralIntersection_quasisimple
    centralIntersection
    (coverage.toQuasisimple_of_alternatingRepresentatives
      alternatingVerified lieTypeVerified sporadicVerified)

/-- Public McKay equality with the concrete alternating residual and
prime-supported Lie-type/sporadic residuals exposed. -/
theorem statement_of_centralIntersection_cfsgAlternatingRepresentatives
    {p : ℕ} [Fact p.Prime]
    {lieType sporadic : FiniteGroupFamily.{0}}
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (coverage :
      CFSGFamilyCoverage
        alternatingSimpleGroupFamily lieType sporadic)
    (alternatingVerified :
      AlternatingUniversalCoverPrimeSupportedVerification p)
    (lieTypeVerified :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p lieType)
    (sporadicVerified :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p sporadic)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (centralScalarNumericalInductiveMcKay_of_centralIntersection_cfsgAlternatingRepresentatives
    centralIntersection coverage alternatingVerified
    lieTypeVerified sporadicVerified).statement G P

end InductiveMcKay
end McKayConjecture
