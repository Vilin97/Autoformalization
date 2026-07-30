/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.FinalCardinalityAutomatic
import McKayConjecture.InductiveMcKay.FinalQuasisimpleAlternatingDegreeReduction

/-!
# Final classification-oriented reduction with automatic cardinalities

The central-intersection inertia-fibre cardinality input is now automatic.
This file inserts the existing quasisimple and prime-supported CFSG coverage
adapters into the covers-only final endpoint.  The public McKay statements
retain arbitrary finite-group universes, while the classification data stays
in universe zero.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

/-- The exact simple-quotient structural residual implies the final
central-scalar numerical condition. -/
theorem centralScalarNumericalInductiveMcKay_of_simpleQuotientStructural
    {p : ℕ} [Fact p.Prime]
    (covers : SimpleQuotientStructuralResidualHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_quasisimple
    covers.toQuasisimple

/-- Public McKay equality from the exact simple-quotient structural
residual. -/
theorem statement_of_simpleQuotientStructural
    {p : ℕ} [Fact p.Prime]
    (covers : SimpleQuotientStructuralResidualHypothesis.{0} p)
    (G : Type u) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  statement_of_quasisimple
    covers.toQuasisimple G P

/-- Prime-supported three-family CFSG coverage and verification imply the
final central-scalar numerical condition. -/
theorem centralScalarNumericalInductiveMcKay_of_primeSupportedCFSG
    {p : ℕ} [Fact p.Prime]
    {alternating lieType sporadic : FiniteGroupFamily.{0}}
    (coverage :
      CFSGFamilyCoverage alternating lieType sporadic)
    (verified :
      PrimeSupportedCFSGFamilyVerification
        p alternating lieType sporadic) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_quasisimple
    (coverage.toQuasisimple_of_primeSupported verified)

/-- Public McKay equality from prime-supported three-family CFSG coverage
and verification. -/
theorem statement_of_primeSupportedCFSG
    {p : ℕ} [Fact p.Prime]
    {alternating lieType sporadic : FiniteGroupFamily.{0}}
    (coverage :
      CFSGFamilyCoverage alternating lieType sporadic)
    (verified :
      PrimeSupportedCFSGFamilyVerification
        p alternating lieType sporadic)
    (G : Type u) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  statement_of_quasisimple
    (coverage.toQuasisimple_of_primeSupported verified) G P

/-- CFSG coverage with the concrete alternating representatives and
prime-supported family verifications implies the final numerical
condition. -/
theorem
    centralScalarNumericalInductiveMcKay_of_cfsgAlternatingRepresentatives
    {p : ℕ} [Fact p.Prime]
    {lieType sporadic : FiniteGroupFamily.{0}}
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
  centralScalarNumericalInductiveMcKay_of_quasisimple
    (coverage.toQuasisimple_of_alternatingRepresentatives
      alternatingVerified lieTypeVerified sporadicVerified)

/-- Public McKay equality with concrete alternating representatives and
prime-supported Lie-type and sporadic residuals. -/
theorem statement_of_cfsgAlternatingRepresentatives
    {p : ℕ} [Fact p.Prime]
    {lieType sporadic : FiniteGroupFamily.{0}}
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
    (G : Type u) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  statement_of_quasisimple
    (coverage.toQuasisimple_of_alternatingRepresentatives
      alternatingVerified lieTypeVerified sporadicVerified)
    G P

/-- After the automatic small-degree alternating cases, verification of the
alternating family in degrees at least `p`, together with the prime-supported
Lie-type and sporadic inputs, implies the final numerical condition. -/
theorem
    centralScalarNumericalInductiveMcKay_of_cfsgAlternatingAtLeastPrime
    {p : ℕ} [Fact p.Prime]
    {lieType sporadic : FiniteGroupFamily.{0}}
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
  centralScalarNumericalInductiveMcKay_of_quasisimple
    (coverage.toQuasisimple_of_primeSupported
      ⟨alternatingVerified.of_alternatingAtLeastPrime,
        lieTypeVerified, sporadicVerified⟩)

/-- Public McKay equality with only the at-least-`p` alternating branch and
the prime-supported Lie-type and sporadic family verifications remaining. -/
theorem statement_of_cfsgAlternatingAtLeastPrime
    {p : ℕ} [Fact p.Prime]
    {lieType sporadic : FiniteGroupFamily.{0}}
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
    (G : Type u) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  statement_of_quasisimple
    (coverage.toQuasisimple_of_primeSupported
      ⟨alternatingVerified.of_alternatingAtLeastPrime,
        lieTypeVerified, sporadicVerified⟩)
    G P

end InductiveMcKay
end McKayConjecture
