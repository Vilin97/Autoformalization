/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalSelectedSummandProjective

/-!
# Quotient action on the canonical Glauberman summand

The corrected selected-summand action descends through the matched normal
copy.  Its quotient action is strictly conjugate to the final projective
mismatch action.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The canonical selected-summand action after inverse-ratio correction
and exact descent to the right outer quotient. -/
def productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    [Nontrivial
      (ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta))] :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ProjectiveRepresentation ℂ
      (productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta)
      (ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta)) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    productAmbientGlaubermanKernelSylowScalarQuotientProjective
      S C hcentral hgenerate g theta
      (productAmbientGlaubermanCanonicalSelectedSylowScalar
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanCanonicalSelectedSummand_isStable
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanFullInertiaCorrectionCochain
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanCanonicalSelectedSummand_isQuotientCompatible
        S C hcentral hgenerate g theta)

/-- The direct selected-summand equivalence strictly intertwines the
descended canonical action and the final quotient mismatch action. -/
theorem
    productAmbientGlaubermanCanonicalSelectedSummand_quotient_intertwines
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    [Nontrivial
      (ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta))]
    (u :
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta)
    (z :
      ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta)) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
        S C hcentral hgenerate g theta
        ((productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
          S C hcentral hgenerate g theta).operator u z) =
      (ProductAmbientGlaubermanFinalMismatchQuotientProjective
        S C hcentral hgenerate g theta).operator u
        (productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
          S C hcentral hgenerate g theta z) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    ProjectiveRepresentation.quotientDescent_intertwines
      ((productAmbientGlaubermanCanonicalSelectedSummandInertiaProjective
        S C hcentral hgenerate g theta).rescale
          (productAmbientGlaubermanFullInertiaCorrectionCochain
            S C hcentral hgenerate g theta))
      (ProductAmbientGlaubermanInertiaMismatchProjective
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanCanonicalSelectedSummand_isQuotientCompatible
        S C hcentral hgenerate g theta)
      (ProjectiveMultiplicityMismatch.isQuotientCompatible
        (productAmbientGlaubermanLeftAssociated
          S C hgenerate theta)
        (productAmbientGlaubermanRightAssociated
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanInertiaRestrictionGroupData
          S C hcentral hgenerate g theta))
      (productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanCanonicalSelectedSummand_rescaled_intertwines
        S C hcentral hgenerate g theta)
      u z

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
