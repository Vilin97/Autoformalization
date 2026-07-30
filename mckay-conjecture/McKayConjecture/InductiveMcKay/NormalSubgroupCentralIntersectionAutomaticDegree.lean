/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.NavarroRelativeDegreeDivisibility
import
  McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionOrdinaryCardinalityReduction
import
  McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45OuterQuotients

/-!
# Automatic prime-to-degree in the central-intersection inertia fibres

The two exact inertia quotients occurring in the central-intersection
reduction were already proved to have prime-to-`q` order.  This file connects
those concrete group-theoretic results to the arithmetic adapter for
Navarro's relative-degree theorem.

The reusable relative-degree divisibility theorem is now formalized, so the
complete pointwise prime-to-degree hypothesis used by the final
ordinary-to-prime-to-`q` bridge follows without any remaining
group-specific or character-theoretic premise.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction

open CliffordCorrespondence
open ComplementReduction
open Proposition45

/-- The exact automatic-degree hypothesis for the central-intersection
reduction follows from the general inertia relative-degree divisibility
theorem. -/
theorem
    centralScalarCentralIntersectionInertiaFibrePPrimeDegreeHypothesis_of_relativeDegreeDivisibility
    {q : ℕ} [Fact q.Prime]
    (hdiv :
      ∀ (G : Type) [Group G] [Finite G]
        (N : Subgroup G) [N.Normal]
        (θ : IrreducibleCharacter N),
          InertiaRelativeDegreeDivisibility N θ) :
    CentralScalarCentralIntersectionInertiaFibrePPrimeDegreeHypothesis
      q := by
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  intro g
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  intro theta
  let phi :=
    internalTheorem44CharacterEquiv
      S C
      (complementCharacterEquivOfGlauberman
        S C hcentral g) theta
  refine ⟨?_, ?_⟩
  · exact
      forall_isPPrimeDegree_overInertia_of_relativeDegreeDivisibility
        Fact.out
        (product S C) theta.1
        (hdiv X (product S C) theta.1)
        theta.2
        (productAmbientGlaubermanLeftOuterQuotient_isPPrimeGroup
          S C hgenerate theta)
  · exact
      forall_isPPrimeDegree_overInertia_of_relativeDegreeDivisibility
        Fact.out
        (internalProductNormalizer S C) phi.1
        (hdiv (ambientNormalizer S)
          (internalProductNormalizer S C) phi.1)
        phi.2
        (productAmbientGlaubermanRightOuterQuotient_isPPrimeGroup
          S C hcentral hgenerate g theta)

/-- The exact automatic prime-to-degree hypothesis required by the
central-intersection reduction. -/
theorem
    centralScalarCentralIntersectionInertiaFibrePPrimeDegreeHypothesis
    {q : ℕ} [Fact q.Prime] :
    CentralScalarCentralIntersectionInertiaFibrePPrimeDegreeHypothesis
      q := by
  apply
    centralScalarCentralIntersectionInertiaFibrePPrimeDegreeHypothesis_of_relativeDegreeDivisibility
  intro G _ _ N _ θ
  exact inertiaRelativeDegreeDivisibility N θ

/-- Combining the ordinary matched-fibre count with the universal
relative-degree divisor gives the exact prime-to-`q` cardinality hypothesis
consumed by the existing numerical reduction. -/
theorem
    centralScalarCentralIntersectionCardinality_of_ordinary_of_relativeDegreeDivisibility
    {q : ℕ} [Fact q.Prime]
    (hcard :
      CentralScalarCentralIntersectionOrdinaryInertiaFibreCardinalityHypothesis
        q)
    (hdiv :
      ∀ (G : Type) [Group G] [Finite G]
        (N : Subgroup G) [N.Normal]
        (θ : IrreducibleCharacter N),
          InertiaRelativeDegreeDivisibility N θ) :
    CentralScalarCentralIntersectionInertiaFibreCardinalityHypothesis q := by
  have hdegree :
      CentralScalarCentralIntersectionInertiaFibrePPrimeDegreeHypothesis q :=
    centralScalarCentralIntersectionInertiaFibrePPrimeDegreeHypothesis_of_relativeDegreeDivisibility
      (q := q)
      hdiv
  exact
    centralScalarCentralIntersectionInertiaFibreCardinalityHypothesis_of_ordinary
      hcard hdegree

/-- Any ordinary matched-inertia-fibre count now supplies the exact
prime-to-`q` cardinality hypothesis consumed by the numerical reduction. -/
theorem
    centralScalarCentralIntersectionCardinality_of_ordinary
    {q : ℕ} [Fact q.Prime]
    (hcard :
      CentralScalarCentralIntersectionOrdinaryInertiaFibreCardinalityHypothesis
        q) :
    CentralScalarCentralIntersectionInertiaFibreCardinalityHypothesis q :=
  centralScalarCentralIntersectionInertiaFibreCardinalityHypothesis_of_ordinary
    hcard
    centralScalarCentralIntersectionInertiaFibrePPrimeDegreeHypothesis

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
