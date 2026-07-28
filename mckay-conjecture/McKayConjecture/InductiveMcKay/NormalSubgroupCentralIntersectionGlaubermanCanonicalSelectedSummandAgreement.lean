/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalSelectedSummandQuotient
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanSelectedSummandObstruction

/-!
# Obstruction agreement from the canonical Glauberman summand

The canonical selected summand is strictly conjugate to the final
restriction-multiplicity projective representation after quotient descent.
Consequently their factor sets agree literally, rather than merely up to a
gauge.  This file packages that observation into the final intrinsic
obstruction agreement.

The only representation-theoretic residue is now the nonvanishing of the
canonical summand and the vanishing of the factor class of its quotient
action.
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

/-- Strict quotient conjugacy identifies the final mismatch factor set with
the factor set on the canonical selected summand. -/
theorem
    productAmbientGlaubermanFinalMismatch_factorSet_eq_canonicalSelectedSummand
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
    [Nontrivial
      (ProductAmbientGlaubermanMultiplicityMismatchSpace
        S C hcentral hgenerate g theta)] :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (ProductAmbientGlaubermanFinalMismatchQuotientProjective
        S C hcentral hgenerate g theta).factorSet =
      (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
        S C hcentral hgenerate g theta).factorSet := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  apply FactorSet.ext
  intro u v
  exact
    (ProjectiveRepresentation.factor_eq_of_linearEquiv_operator_eq
      (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
        S C hcentral hgenerate g theta)
      (ProductAmbientGlaubermanFinalMismatchQuotientProjective
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanCanonicalSelectedSummand_quotient_intertwines
        S C hcentral hgenerate g theta)
      u v).symm

/-- Vanishing of the quotient factor class on the nonzero canonical
selected summand proves the exact projective obstruction agreement in
Proposition 4.5.  Nontriviality of the final mismatch space is transported
automatically through the canonical linear equivalence. -/
theorem
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_canonicalSelectedSummand
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
    (hselected :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      letI :=
        trivialMulDistribMulAction
          (productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta) ℂˣ
      (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
        S C hcentral hgenerate g theta).factorSet.h2Class = 0) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let E :=
    productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
      S C hcentral hgenerate g theta
  letI :
      Nontrivial
        (ProductAmbientGlaubermanMultiplicityMismatchSpace
          S C hcentral hgenerate g theta) :=
    E.injective.nontrivial
  have hmismatchZero :
      letI :=
        trivialMulDistribMulAction
          (productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta) ℂˣ
      (productAmbientGlaubermanQuotientMismatchFactorSet
        S C hcentral hgenerate g theta).h2Class = 0 := by
    have hfinalFactor :
        (ProductAmbientGlaubermanFinalMismatchQuotientProjective
          S C hcentral hgenerate g theta).factorSet =
          productAmbientGlaubermanQuotientMismatchFactorSet
            S C hcentral hgenerate g theta :=
      ProjectiveMultiplicityMismatch.quotientProjective_factorSet
        (productAmbientGlaubermanLeftAssociated
          S C hgenerate theta)
        (productAmbientGlaubermanRightAssociated
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanInertiaRestrictionGroupData
          S C hcentral hgenerate g theta)
    rw [← hfinalFactor,
      productAmbientGlaubermanFinalMismatch_factorSet_eq_canonicalSelectedSummand
        S C hcentral hgenerate g theta]
    exact hselected
  have hfactorAgreement :
      (productAmbientGlaubermanLeftAssociated
        S C hgenerate theta).QuotientFactorH2ClassAgreement
          (productAmbientGlaubermanRightAssociated
            S C hcentral hgenerate g theta)
          (productAmbientGlaubermanInertiaRestrictionGroupData
            S C hcentral hgenerate g theta) :=
    ProjectiveMultiplicityMismatch.quotientFactorH2ClassAgreement_of_mismatch_eq_zero
      (productAmbientGlaubermanLeftAssociated
        S C hgenerate theta)
      (productAmbientGlaubermanRightAssociated
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta)
      hmismatchZero
  exact
    ((productAmbientGlaubermanLeftAssociated
      S C hgenerate theta
      ).quotientFactorH2ClassAgreement_iff_projectiveObstructionClass
        (productAmbientGlaubermanRightAssociated
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanInertiaRestrictionGroupData
          S C hcentral hgenerate g theta)).mp hfactorAgreement

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
