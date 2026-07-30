/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionAutomaticDegree
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionOrdinaryInertiaFibreCardinalityAutomatic

/-!
# Automatic central-intersection inertia-fibre cardinalities

The unconditional ordinary Okuyama--Wajima count and the automatic
prime-to-degree bridge together discharge the inertia-fibre cardinality
hypothesis used by the central-intersection reduction.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction

/-- The prime-to-`q` matched inertia-fibre cardinality hypothesis required
by the central-intersection reduction is unconditional. -/
theorem
    centralScalarCentralIntersectionInertiaFibreCardinalityHypothesis_automatic
    (q : ℕ) [Fact q.Prime] :
    CentralScalarCentralIntersectionInertiaFibreCardinalityHypothesis q :=
  centralScalarCentralIntersectionCardinality_of_ordinary
    (centralScalarCentralIntersectionOrdinaryInertiaFibreCardinalityHypothesis
      q)

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
