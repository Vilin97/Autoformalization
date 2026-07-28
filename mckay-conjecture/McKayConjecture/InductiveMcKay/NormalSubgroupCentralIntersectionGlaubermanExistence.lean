/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanActionConjugation
import McKayConjecture.Character.GlaubermanCyclicAction
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanLift

/-!
# The Glauberman input for the central-intersection subgroup

The canonical normal `q'`-kernel of `CS` is acted on by the restricted
Sylow subgroup.  Consequently the cyclic action theorem, together with
the proved induction on finite `q`-groups, supplies the exact classical
Glauberman correspondence used by the Okuyama--Wajima construction.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace ComplementReduction

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The cyclic strong action theorem supplies the Glauberman
correspondence for the canonical normal `q'`-kernel of `CS`. -/
theorem exists_productGlaubermanCorrespondence_of_cyclicStrongAction
    (cyclic : CyclicStrongActionGlaubermanHypothesis q)
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    Nonempty
      (ProductGlaubermanCorrespondence
        S C hcentral) :=
  exists_glaubermanCorrespondence_of_cyclicStrongAction
    (productPPrimeKernel S C hcentral)
    (productSylow S C :
      Subgroup (product S C))
    cyclic
    (productSylow S C).isPGroup'
    (productPPrimeKernel_isPPrimeGroup
      S C hcentral)

/-- The fully proved cyclic action theorem supplies the product
Glauberman correspondence without any remaining character-theoretic
hypothesis. -/
theorem exists_productGlaubermanCorrespondence
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    Nonempty
      (ProductGlaubermanCorrespondence
        S C hcentral) :=
  exists_productGlaubermanCorrespondence_of_cyclicStrongAction
    S C cyclicStrongActionGlaubermanHypothesis hcentral

end ComplementReduction

/-- The remaining ambient Proposition-4.5 assertion, separated from
existence of the classical Glauberman correspondence. -/
def CentralScalarCentralIntersectionAmbientLiftHypothesis
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
          (Proposition45.ProductAmbientGlaubermanLiftData
            S C hcentral hgenerate g)

/-- The cyclic strong action theorem and the ambient Proposition-4.5
assertion supply the full central-intersection Glauberman-lift input. -/
theorem centralScalarCentralIntersectionGlaubermanLiftHypothesis_of_cyclicStrongAction
    {q : ℕ} [Fact q.Prime]
    (cyclic : CyclicStrongActionGlaubermanHypothesis q)
    (ambient :
      CentralScalarCentralIntersectionAmbientLiftHypothesis q) :
    CentralScalarCentralIntersectionGlaubermanLiftHypothesis q := by
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  obtain ⟨g⟩ :=
    ComplementReduction.exists_productGlaubermanCorrespondence_of_cyclicStrongAction
      S C cyclic hcentral
  exact ⟨g, ambient X S C hCnormal hcentral hgenerate g⟩

/-- Hence the cyclic strong action theorem and Proposition 4.5 discharge
the central-scalar central-intersection reduction used in the final
normal-subgroup induction. -/
theorem centralScalarCentralIntersectionReductionHypothesis_of_cyclicStrongAction
    {q : ℕ} [Fact q.Prime]
    (cyclic : CyclicStrongActionGlaubermanHypothesis q)
    (ambient :
      CentralScalarCentralIntersectionAmbientLiftHypothesis q) :
    CentralScalarCentralIntersectionReductionHypothesis q :=
  centralScalarCentralIntersectionReductionHypothesis_of_glaubermanLift
    (centralScalarCentralIntersectionGlaubermanLiftHypothesis_of_cyclicStrongAction
      cyclic ambient)

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
