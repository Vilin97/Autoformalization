/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.FinalProjectiveObstructionReduction
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanReducedDadeFactor

/-!
# Final reduction from explicit reduced Dade factors

This file composes the operator-level cross-characteristic input with the
existing final reduction.  The exposed DGN hypothesis now consists of concrete
primitive Dade algebras, Brauer-normalizer extensions, and equality with the
explicit residue-field factors.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open NormalSubgroupCentralIntersectionReduction

/-- Explicit reduced Dade factors and the quasisimple condition imply the
strengthened numerical inductive-McKay condition. -/
theorem centralScalarNumericalInductiveMcKay_of_reducedDadeFactor_quasisimple
    {p : ℕ} [Fact p.Prime]
    (dgn :
      ProductAmbientGlaubermanReducedDadeFactorHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_projectiveObstruction_quasisimple
    (productAmbientGlaubermanProjectiveObstructionClassAgreementHypothesis_of_reducedDadeFactor
      dgn)
    covers

/-- Public McKay equality from explicit reduced Dade factors and the
quasisimple condition. -/
theorem statement_of_reducedDadeFactor_quasisimple
    {p : ℕ} [Fact p.Prime]
    (dgn :
      ProductAmbientGlaubermanReducedDadeFactorHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (centralScalarNumericalInductiveMcKay_of_reducedDadeFactor_quasisimple
    dgn covers).statement G P

/-- Explicit reduced Dade factors and the universal-cover condition imply
the strengthened numerical inductive-McKay condition. -/
theorem
    centralScalarNumericalInductiveMcKay_of_reducedDadeFactor_universalCover
    {p : ℕ} [Fact p.Prime]
    (dgn :
      ProductAmbientGlaubermanReducedDadeFactorHypothesis p)
    (covers :
      UniversalCoverInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_projectiveObstruction_universalCover
    (productAmbientGlaubermanProjectiveObstructionClassAgreementHypothesis_of_reducedDadeFactor
      dgn)
    covers

/-- Public McKay equality in the universal-cover formulation, with the DGN
input exposed at the reduced operator-factor level. -/
theorem statement_of_reducedDadeFactor_universalCover
    {p : ℕ} [Fact p.Prime]
    (dgn :
      ProductAmbientGlaubermanReducedDadeFactorHypothesis p)
    (covers :
      UniversalCoverInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (centralScalarNumericalInductiveMcKay_of_reducedDadeFactor_universalCover
    dgn covers).statement G P

end InductiveMcKay
end McKayConjecture
