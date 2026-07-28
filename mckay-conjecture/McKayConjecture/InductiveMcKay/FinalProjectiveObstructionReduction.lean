/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.FinalReduction
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionFactorMatchedFibreEquivalence

/-!
# Final reduction from the Dade--Glauberman--Nagao obstruction

The canonical tensor-permutation realization is already unconditional.
After the factor-matched character-triple construction, the
central-intersection branch needs only equality of the canonical quotient
projective obstruction classes.  This file composes that equality with the
final Rossi reduction.

Consequently, the two mathematical inputs visible at the public theorem
boundary are precisely:

* the Dade--Glauberman--Nagao projective obstruction transport;
* the inductive McKay correspondences for finite quasisimple groups.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open NormalSubgroupCentralIntersectionReduction

/-- Dade--Glauberman--Nagao obstruction agreement and the quasisimple
condition imply the strengthened numerical inductive-McKay condition. -/
theorem centralScalarNumericalInductiveMcKay_of_projectiveObstruction_quasisimple
    {p : ℕ} [Fact p.Prime]
    (dgn :
      ProductAmbientGlaubermanProjectiveObstructionClassAgreementHypothesis
        p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_centralIntersection_quasisimple
    (centralScalarCentralIntersectionReductionHypothesis_of_projectiveObstructionClassAgreement
      dgn)
    covers

/-- Public McKay equality from the Dade--Glauberman--Nagao obstruction
transport and the quasisimple condition. -/
theorem statement_of_projectiveObstruction_quasisimple
    {p : ℕ} [Fact p.Prime]
    (dgn :
      ProductAmbientGlaubermanProjectiveObstructionClassAgreementHypothesis
        p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (centralScalarNumericalInductiveMcKay_of_projectiveObstruction_quasisimple
    dgn covers).statement G P

/-- Universal-cover form of the final projective-obstruction reduction. -/
theorem centralScalarNumericalInductiveMcKay_of_projectiveObstruction_universalCover
    {p : ℕ} [Fact p.Prime]
    (dgn :
      ProductAmbientGlaubermanProjectiveObstructionClassAgreementHypothesis
        p)
    (covers :
      UniversalCoverInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_projectiveObstruction_quasisimple
    dgn covers.toQuasisimple

/-- Public McKay equality in the universal-cover formulation. -/
theorem statement_of_projectiveObstruction_universalCover
    {p : ℕ} [Fact p.Prime]
    (dgn :
      ProductAmbientGlaubermanProjectiveObstructionClassAgreementHypothesis
        p)
    (covers :
      UniversalCoverInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (centralScalarNumericalInductiveMcKay_of_projectiveObstruction_universalCover
    dgn covers).statement G P

end InductiveMcKay
end McKayConjecture
