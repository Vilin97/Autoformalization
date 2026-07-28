/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionAmbientCentralTriples
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanExistence

/-!
# The remaining Proposition 4.5 theorem at central-triple strength

The classical Glauberman correspondence and the full numerical
Okuyama--Wajima construction are already theorems.  The remaining ambient
input can therefore be stated in the standard form used by Theorem 4.4:
the transported character equivalence is normalizer-equivariant and its
matched ambient inertia triples are centrally isomorphic through the
canonical inertia embedding.

The results below prove that this one standard central-triple assertion
discharges the formerly separate ambient equivariance, inertia-fibre, and
central-action hypotheses.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction

open GroupTheory

/-- The exact unresolved ambient character-theoretic statement in the
central-intersection branch, expressed as canonical central isomorphisms
of matched inertia triples rather than as the desired ambient McKay
correspondence. -/
def CentralScalarCentralIntersectionCentralTripleHypothesis
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
          (Proposition45.ProductAmbientGlaubermanCentralTripleLiftData
            S C hcentral hgenerate g)

/-- Canonical central inertia triples imply the previously isolated
ambient numerical Proposition-4.5 hypothesis. -/
theorem centralScalarCentralIntersectionAmbientLiftHypothesis_of_centralTriples
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionCentralTripleHypothesis q) :
    CentralScalarCentralIntersectionAmbientLiftHypothesis q := by
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  intro g
  obtain ⟨d⟩ :=
    h X S C hCnormal hcentral hgenerate g
  exact
    ⟨d.toProductAmbientGlaubermanLiftData
      S C hcentral hgenerate g⟩

/-- Since the Glauberman correspondence itself is now constructed, the
standard central-triple form of Proposition 4.5 supplies the complete
central-intersection reduction hypothesis. -/
theorem centralScalarCentralIntersectionReductionHypothesis_of_centralTriples
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionCentralTripleHypothesis q) :
    CentralScalarCentralIntersectionReductionHypothesis q := by
  apply
    centralScalarCentralIntersectionReductionHypothesis_of_glaubermanLift
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  obtain ⟨g⟩ :=
    ComplementReduction.exists_productGlaubermanCorrespondence
      S C hcentral
  obtain ⟨d⟩ :=
    h X S C hCnormal hcentral hgenerate g
  exact
    ⟨g,
      ⟨d.toProductAmbientGlaubermanLiftData
        S C hcentral hgenerate g⟩⟩

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
