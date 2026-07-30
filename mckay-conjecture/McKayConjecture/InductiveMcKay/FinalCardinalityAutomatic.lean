/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.FinalCardinalityReduction
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionCardinalityAutomatic

/-!
# Final reduction with automatic inertia-fibre cardinalities

The ordinary Okuyama--Wajima count and the relative-degree bridge discharge
the complete central-intersection cardinality input.  Thus the final
numerical condition and the public McKay equality depend only on the
remaining quasisimple, equivalently universal-cover, input.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open NormalSubgroupCentralIntersectionReduction

/-- The quasisimple input alone implies the central-scalar numerical
inductive-McKay condition; the inertia-fibre cardinalities are automatic. -/
theorem centralScalarNumericalInductiveMcKay_of_quasisimple
    {p : ℕ} [Fact p.Prime]
    (covers : QuasisimpleInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_inertiaFibreCardinality_quasisimple
    (centralScalarCentralIntersectionInertiaFibreCardinalityHypothesis_automatic
      p)
    covers

/-- Public McKay equality from the quasisimple input alone.  The
universe-zero reduction is transported to an arbitrary finite-group
universe by the existing cardinality endpoint. -/
theorem statement_of_quasisimple
    {p : ℕ} [Fact p.Prime]
    (covers : QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type u) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  statement_of_inertiaFibreCardinality_quasisimple
    (centralScalarCentralIntersectionInertiaFibreCardinalityHypothesis_automatic
      p)
    covers G P

/-- Universal-cover form of the final numerical condition, with the
inertia-fibre cardinalities discharged automatically. -/
theorem centralScalarNumericalInductiveMcKay_of_universalCover
    {p : ℕ} [Fact p.Prime]
    (covers : UniversalCoverInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_inertiaFibreCardinality_universalCover
    (centralScalarCentralIntersectionInertiaFibreCardinalityHypothesis_automatic
      p)
    covers

/-- Public McKay equality in the universal-cover formulation. -/
theorem statement_of_universalCover
    {p : ℕ} [Fact p.Prime]
    (covers : UniversalCoverInductiveMcKayHypothesis.{0} p)
    (G : Type u) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  statement_of_inertiaFibreCardinality_universalCover
    (centralScalarCentralIntersectionInertiaFibreCardinalityHypothesis_automatic
      p)
    covers G P

end InductiveMcKay
end McKayConjecture
