/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.FinalReduction
import
  McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionAutomaticDegree
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionOrdinaryCardinalityReduction
import McKayConjecture.Proof.SmallModel

/-!
# Final reduction from Okuyama--Wajima inertia-fibre counts

The normal-subgroup branch of the numerical Rossi reduction only needs
equality of the finite matched inertia-fibre cardinalities.  This file
composes that optimized boundary with the already formalized layer and
central-index reductions.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open NormalSubgroupCentralIntersectionReduction

/-- The inertia-fibre counting theorem and the quasisimple condition imply
the central-scalar numerical inductive-McKay condition. -/
theorem
    centralScalarNumericalInductiveMcKay_of_inertiaFibreCardinality_quasisimple
    {p : ℕ} [Fact p.Prime]
    (counts :
      CentralScalarCentralIntersectionInertiaFibreCardinalityHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_centralIntersection_quasisimple
    (centralScalarCentralIntersectionReductionHypothesis_of_cardinality
      counts)
    covers

/-- Public McKay equality from the inertia-fibre counting theorem and the
quasisimple condition. -/
theorem statement_of_inertiaFibreCardinality_quasisimple
    {p : ℕ} [Fact p.Prime]
    (counts :
      CentralScalarCentralIntersectionInertiaFibreCardinalityHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type u) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P := by
  apply McKayConjecture.Statement.of_universeZero
  intro H _ _ Q
  exact
    (centralScalarNumericalInductiveMcKay_of_inertiaFibreCardinality_quasisimple
      counts covers).statement H Q

/-- Universal-cover form of the final inertia-fibre cardinality
reduction. -/
theorem
    centralScalarNumericalInductiveMcKay_of_inertiaFibreCardinality_universalCover
    {p : ℕ} [Fact p.Prime]
    (counts :
      CentralScalarCentralIntersectionInertiaFibreCardinalityHypothesis p)
    (covers :
      UniversalCoverInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_inertiaFibreCardinality_quasisimple
    counts covers.toQuasisimple

/-- Public McKay equality in the universal-cover formulation of the
inertia-fibre cardinality reduction. -/
theorem statement_of_inertiaFibreCardinality_universalCover
    {p : ℕ} [Fact p.Prime]
    (counts :
      CentralScalarCentralIntersectionInertiaFibreCardinalityHypothesis p)
    (covers :
      UniversalCoverInductiveMcKayHypothesis.{0} p)
    (G : Type u) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P := by
  apply McKayConjecture.Statement.of_universeZero
  intro H _ _ Q
  exact
    (centralScalarNumericalInductiveMcKay_of_inertiaFibreCardinality_universalCover
      counts covers).statement H Q

/-- The ordinary inertia-fibre count, its relative-degree theorem, and
the quasisimple condition imply the central-scalar numerical
inductive-McKay condition. -/
theorem
    centralScalarNumericalInductiveMcKay_of_ordinaryInertiaFibreCardinality_quasisimple
    {p : ℕ} [Fact p.Prime]
    (counts :
      CentralScalarCentralIntersectionOrdinaryInertiaFibreCardinalityHypothesis
        p)
    (degrees :
      CentralScalarCentralIntersectionInertiaFibrePPrimeDegreeHypothesis
        p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_inertiaFibreCardinality_quasisimple
    (centralScalarCentralIntersectionInertiaFibreCardinalityHypothesis_of_ordinary
      counts degrees)
    covers

/-- Public McKay equality from the ordinary inertia-fibre count, its
relative-degree theorem, and the quasisimple condition. -/
theorem statement_of_ordinaryInertiaFibreCardinality_quasisimple
    {p : ℕ} [Fact p.Prime]
    (counts :
      CentralScalarCentralIntersectionOrdinaryInertiaFibreCardinalityHypothesis
        p)
    (degrees :
      CentralScalarCentralIntersectionInertiaFibrePPrimeDegreeHypothesis
        p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type u) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  statement_of_inertiaFibreCardinality_quasisimple
    (centralScalarCentralIntersectionInertiaFibreCardinalityHypothesis_of_ordinary
      counts degrees)
    covers G P

/-- Universal-cover form of the final ordinary inertia-fibre counting
reduction. -/
theorem
    centralScalarNumericalInductiveMcKay_of_ordinaryInertiaFibreCardinality_universalCover
    {p : ℕ} [Fact p.Prime]
    (counts :
      CentralScalarCentralIntersectionOrdinaryInertiaFibreCardinalityHypothesis
        p)
    (degrees :
      CentralScalarCentralIntersectionInertiaFibrePPrimeDegreeHypothesis
        p)
    (covers :
      UniversalCoverInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_ordinaryInertiaFibreCardinality_quasisimple
    counts degrees covers.toQuasisimple

/-- Public McKay equality in the universal-cover formulation of the
ordinary inertia-fibre counting reduction. -/
theorem statement_of_ordinaryInertiaFibreCardinality_universalCover
    {p : ℕ} [Fact p.Prime]
    (counts :
      CentralScalarCentralIntersectionOrdinaryInertiaFibreCardinalityHypothesis
        p)
    (degrees :
      CentralScalarCentralIntersectionInertiaFibrePPrimeDegreeHypothesis
        p)
    (covers :
      UniversalCoverInductiveMcKayHypothesis.{0} p)
    (G : Type u) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  statement_of_inertiaFibreCardinality_universalCover
    (centralScalarCentralIntersectionInertiaFibreCardinalityHypothesis_of_ordinary
      counts degrees)
    covers G P

/-! ### Ordinary-count endpoints with automatic relative degrees -/

/-- The ordinary inertia-fibre count and the quasisimple condition suffice:
Navarro relative-degree divisibility supplies the prime-to-degree premise
automatically. -/
theorem
    centralScalarNumericalInductiveMcKay_of_ordinaryCount_quasisimple
    {p : ℕ} [Fact p.Prime]
    (counts :
      CentralScalarCentralIntersectionOrdinaryInertiaFibreCardinalityHypothesis
        p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_inertiaFibreCardinality_quasisimple
    (centralScalarCentralIntersectionCardinality_of_ordinary counts)
    covers

/-- Public McKay equality from the ordinary inertia-fibre count and the
quasisimple condition, with relative degrees discharged internally. -/
theorem
    statement_of_ordinaryCount_quasisimple
    {p : ℕ} [Fact p.Prime]
    (counts :
      CentralScalarCentralIntersectionOrdinaryInertiaFibreCardinalityHypothesis
        p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type u) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  statement_of_inertiaFibreCardinality_quasisimple
    (centralScalarCentralIntersectionCardinality_of_ordinary counts)
    covers G P

/-- Universal-cover form of the ordinary-count reduction with relative
degrees discharged internally. -/
theorem
    centralScalarNumericalInductiveMcKay_of_ordinaryCount_universalCover
    {p : ℕ} [Fact p.Prime]
    (counts :
      CentralScalarCentralIntersectionOrdinaryInertiaFibreCardinalityHypothesis
        p)
    (covers :
      UniversalCoverInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_ordinaryCount_quasisimple
    counts covers.toQuasisimple

/-- Public McKay equality in the universal-cover formulation, requiring
only the ordinary inertia-fibre count. -/
theorem
    statement_of_ordinaryCount_universalCover
    {p : ℕ} [Fact p.Prime]
    (counts :
      CentralScalarCentralIntersectionOrdinaryInertiaFibreCardinalityHypothesis
        p)
    (covers :
      UniversalCoverInductiveMcKayHypothesis.{0} p)
    (G : Type u) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  statement_of_inertiaFibreCardinality_universalCover
    (centralScalarCentralIntersectionCardinality_of_ordinary counts)
    covers G P

end InductiveMcKay
end McKayConjecture
