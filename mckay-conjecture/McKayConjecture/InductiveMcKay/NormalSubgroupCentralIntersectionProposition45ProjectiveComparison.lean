/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionAmbientProjectiveComparison
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45CentralTriples

/-!
# Proposition 4.5 from projective comparisons

This file states the residual central-intersection theorem at its narrowest
standard character-triple strength.  For the explicitly constructed
Glauberman--Okuyama--Wajima equivalence, one asks for normalizer equivariance
and compatible independent associated projective representations on every
matched inertia pair.

The product group conditions, complete central witnesses, exact inertia
fibre equivalences, and central-action intertwiners are all constructed from
that input.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction

open GroupTheory

/-- The exact unresolved projective-comparison statement in the
central-intersection branch.  This is the factor-set and central-scalar
content of the central character-triple form of Theorem 4.4, not the desired
ambient McKay conclusion. -/
def CentralScalarCentralIntersectionProjectiveComparisonHypothesis
    (q : ℕ) [Fact q.Prime] : Prop :=
  ∀ (X : Type) [Group X] [Finite X]
    (S : Sylow q X) (C : Subgroup X)
    (hCnormal : C.Normal)
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤),
      letI : C.Normal := hCnormal
      ∀ g :
          ComplementReduction.ProductGlaubermanCorrespondence
            S C hcentral,
        Nonempty
          (Proposition45.ProductAmbientGlaubermanProjectiveComparisonData
            S C hcentral hgenerate g)

/-- Projective comparisons construct the canonical complete central inertia
triples used in the central-triple formulation. -/
theorem centralScalarCentralIntersectionCentralTripleHypothesis_of_projectiveComparisons
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionProjectiveComparisonHypothesis q) :
    CentralScalarCentralIntersectionCentralTripleHypothesis q := by
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  intro g
  obtain ⟨d⟩ :=
    h X S C hCnormal hcentral hgenerate g
  exact
    ⟨d.toCentralTripleLiftData
      S C hgenerate
      (Proposition45.complementCharacterEquivOfGlauberman
        S C hcentral g)⟩

/-- The projective-comparison theorem discharges the isolated ambient lift
hypothesis. -/
theorem centralScalarCentralIntersectionAmbientLiftHypothesis_of_projectiveComparisons
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionProjectiveComparisonHypothesis q) :
    CentralScalarCentralIntersectionAmbientLiftHypothesis q :=
  centralScalarCentralIntersectionAmbientLiftHypothesis_of_centralTriples
    (centralScalarCentralIntersectionCentralTripleHypothesis_of_projectiveComparisons
      h)

/-- The constructed Glauberman correspondence and the projective-comparison
theorem supply the complete central-intersection reduction hypothesis. -/
theorem centralScalarCentralIntersectionReductionHypothesis_of_projectiveComparisons
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionProjectiveComparisonHypothesis q) :
    CentralScalarCentralIntersectionReductionHypothesis q :=
  centralScalarCentralIntersectionReductionHypothesis_of_centralTriples
    (centralScalarCentralIntersectionCentralTripleHypothesis_of_projectiveComparisons
      h)

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
