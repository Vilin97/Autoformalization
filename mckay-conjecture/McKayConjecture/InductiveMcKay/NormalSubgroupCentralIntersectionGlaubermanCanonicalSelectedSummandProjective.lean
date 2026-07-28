/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveRescaleIntertwining
import McKayConjecture.CharacterTriple.ProjectiveQuotientCompatibilityTransport
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalSelectedSummandFullInertia

/-!
# Projective transport on the canonical Glauberman summand

The full-inertia pointwise calculation is assembled here into an equality
of projective operators.  Rescaling the inherited selected-summand action
by the inverse source/target comparison ratio then makes the canonical
linear equivalence strictly equivariant with the final mismatch action.
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

/-- The direct selected-summand equivalence intertwines the inherited
operator with the final mismatch operator up to the explicit full-inertia
scalar ratio. -/
theorem
    productAmbientGlaubermanCanonicalSelectedSummand_fullInertia_intertwines
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
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
        ((productAmbientGlaubermanCanonicalSelectedSummandInertiaProjective
          S C hcentral hgenerate g theta).operator b z) =
      (productAmbientGlaubermanFullInertiaScalarRatio
        S C hcentral hgenerate g theta b : ℂ) •
        (ProductAmbientGlaubermanInertiaMismatchProjective
          S C hcentral hgenerate g theta).operator b
          (productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
            S C hcentral hgenerate g theta z) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  let targetEquiv :=
    productAmbientGlaubermanFixedPointKernelProductRepresentationEquiv
      S C hcentral hgenerate g theta
  let w := targetEquiv.symm x
  have hpoint :=
    productAmbientGlaubermanCanonicalSelectedSummand_fullInertia_pointwise
      S C hcentral hgenerate g theta b z w
  have htransport :=
    productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect_transportPoint
      S C hcentral hgenerate g theta
      ((productAmbientGlaubermanCanonicalSelectedSummandInertiaProjective
        S C hcentral hgenerate g theta).operator b z)
      w
  change
    productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
        S C hcentral hgenerate g theta
        ((productAmbientGlaubermanCanonicalSelectedSummandInertiaProjective
          S C hcentral hgenerate g theta).operator b z) x =
      (productAmbientGlaubermanFullInertiaScalarRatio
        S C hcentral hgenerate g theta b : ℂ) •
        (ProductAmbientGlaubermanInertiaMismatchProjective
          S C hcentral hgenerate g theta).operator b
          (productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
            S C hcentral hgenerate g theta z) x
  rw [show x = targetEquiv w by
    exact (targetEquiv.apply_symm_apply x).symm]
  exact htransport.trans hpoint

/-- The cochain which removes the full-inertia comparison ratio. -/
def productAmbientGlaubermanFullInertiaCorrectionCochain
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta) :
    ℂˣ :=
  (productAmbientGlaubermanFullInertiaScalarRatio
    S C hcentral hgenerate g theta b)⁻¹

/-- After the canonical correction, the selected-summand action is
strictly conjugate to the final mismatch action. -/
theorem
    productAmbientGlaubermanCanonicalSelectedSummand_rescaled_intertwines
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
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
        (((productAmbientGlaubermanCanonicalSelectedSummandInertiaProjective
          S C hcentral hgenerate g theta).rescale
            (productAmbientGlaubermanFullInertiaCorrectionCochain
              S C hcentral hgenerate g theta)).operator b z) =
      (ProductAmbientGlaubermanInertiaMismatchProjective
        S C hcentral hgenerate g theta).operator b
        (productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
          S C hcentral hgenerate g theta z) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    ProjectiveRepresentation.rescale_inverse_intertwines
      (productAmbientGlaubermanCanonicalSelectedSummandInertiaProjective
        S C hcentral hgenerate g theta)
      (ProductAmbientGlaubermanInertiaMismatchProjective
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanFullInertiaScalarRatio
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanCanonicalSelectedSummand_fullInertia_intertwines
        S C hcentral hgenerate g theta)
      b z

/-- Whenever the selected summand is nonzero, strict conjugacy with the
final mismatch action transports its exact normal-copy quotient
compatibility. -/
theorem
    productAmbientGlaubermanCanonicalSelectedSummand_isQuotientCompatible
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
    ((productAmbientGlaubermanCanonicalSelectedSummandInertiaProjective
        S C hcentral hgenerate g theta).rescale
          (productAmbientGlaubermanFullInertiaCorrectionCochain
            S C hcentral hgenerate g theta)).IsQuotientCompatible
      (ProductAmbientGlaubermanRightNormalCopy
        S C hcentral hgenerate g theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    ProjectiveRepresentation.IsQuotientCompatible.of_linearEquiv_operator_eq
        ((productAmbientGlaubermanCanonicalSelectedSummandInertiaProjective
          S C hcentral hgenerate g theta).rescale
            (productAmbientGlaubermanFullInertiaCorrectionCochain
              S C hcentral hgenerate g theta))
        (ProductAmbientGlaubermanInertiaMismatchProjective
          S C hcentral hgenerate g theta)
        (ProductAmbientGlaubermanRightNormalCopy
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

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
