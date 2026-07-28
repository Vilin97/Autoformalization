/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalOperatorComparison

/-!
# The selected Glauberman summand and the final obstruction class

This file packages the operator comparison on the selected Sylow-scalar
summand into the exact intrinsic `H²` equality used by the final DGN
reduction.

There are two genuinely representation-theoretic inputs:

* the selected, cochain-normalized kernel summand has trivial quotient
  factor class; and
* it is equivariantly equivalent, up to a scalar cochain, to the final
  restriction-multiplicity space.

No equality of the dimensions of the full kernel Hom-space and the final
Hom-space is assumed.
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

/-- Vanishing of the quotient factor class on the selected, normalized
Sylow-scalar summand.  This is the exact cohomological residue left after
constructing that summand and descending its projective action. -/
def ProductAmbientGlaubermanSelectedKernelQuotientH2ClassVanishes
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (mu :
      internalNormalizerSylow (productSylow S C) → ℂˣ)
    (hstable :
      (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
        S C hcentral hgenerate g theta).IsStable
          (ProductAmbientGlaubermanKernelSylowScalarSubspace
            S C hcentral hgenerate g theta mu))
    (c :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta → ℂˣ)
    (hquotient :
      (((productAmbientGlaubermanRestrictedKernelMultiplicityProjective
            S C hcentral hgenerate g theta).restrictStable
              (ProductAmbientGlaubermanKernelSylowScalarSubspace
                S C hcentral hgenerate g theta mu)
              hstable).rescale c).IsQuotientCompatible
        (ProductAmbientGlaubermanRightNormalCopy
          S C hcentral hgenerate g theta))
    [Nontrivial
      (ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta mu)] : Prop :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  letI :=
    trivialMulDistribMulAction
      (productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta) ℂˣ
  (productAmbientGlaubermanKernelSylowScalarQuotientProjective
      S C hcentral hgenerate g theta mu hstable c hquotient
      ).factorSet.h2Class = 0

/-- Triviality of the selected quotient factor, together with the faithful
operator equivalence to the final mismatch space, proves the intrinsic
projective obstruction-class agreement required by the DGN reduction. -/
theorem productAmbientGlaubermanProjectiveObstructionClassAgreement_of_selectedSummand
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (mu :
      internalNormalizerSylow (productSylow S C) → ℂˣ)
    (hstable :
      (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
        S C hcentral hgenerate g theta).IsStable
          (ProductAmbientGlaubermanKernelSylowScalarSubspace
            S C hcentral hgenerate g theta mu))
    (c :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta → ℂˣ)
    (hquotient :
      (((productAmbientGlaubermanRestrictedKernelMultiplicityProjective
            S C hcentral hgenerate g theta).restrictStable
              (ProductAmbientGlaubermanKernelSylowScalarSubspace
                S C hcentral hgenerate g theta mu)
              hstable).rescale c).IsQuotientCompatible
        (ProductAmbientGlaubermanRightNormalCopy
          S C hcentral hgenerate g theta))
    [Nontrivial
      (ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta mu)]
    [Nontrivial
      (ProductAmbientGlaubermanMultiplicityMismatchSpace
        S C hcentral hgenerate g theta)]
    (hselected :
      ProductAmbientGlaubermanSelectedKernelQuotientH2ClassVanishes
        S C hcentral hgenerate g theta mu hstable c hquotient)
    (E :
      ProductAmbientGlaubermanKernelSylowScalarSubspace
          S C hcentral hgenerate g theta mu ≃ₗ[ℂ]
        ProductAmbientGlaubermanMultiplicityMismatchSpace
          S C hcentral hgenerate g theta)
    (a :
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta → ℂˣ)
    (hoperator :
      ProductAmbientGlaubermanSelectedSummandOperatorIntertwining
        S C hcentral hgenerate g theta mu hstable c hquotient E a) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let selectedProjective :=
    productAmbientGlaubermanKernelSylowScalarQuotientProjective
      S C hcentral hgenerate g theta mu hstable c hquotient
  let finalProjective :=
    ProductAmbientGlaubermanFinalMismatchQuotientProjective
      S C hcentral hgenerate g theta
  have hfactor :
      finalProjective.factorSet =
        selectedProjective.factorSet.gauge a :=
    productAmbientGlaubermanFinalMismatch_factorSet_eq_selectedKernel_gauge
      S C hcentral hgenerate g theta mu hstable c hquotient E a hoperator
  have hfinalFactor :
      finalProjective.factorSet =
        productAmbientGlaubermanQuotientMismatchFactorSet
          S C hcentral hgenerate g theta :=
    ProjectiveMultiplicityMismatch.quotientProjective_factorSet
      (productAmbientGlaubermanLeftAssociated
        S C hgenerate theta)
      (productAmbientGlaubermanRightAssociated
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta)
  have hmismatchZero :
      letI :=
        trivialMulDistribMulAction
          (productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta) ℂˣ
      (productAmbientGlaubermanQuotientMismatchFactorSet
        S C hcentral hgenerate g theta).h2Class = 0 := by
    have hselected' :
        selectedProjective.factorSet.h2Class = 0 := by
      simpa only
        [ProductAmbientGlaubermanSelectedKernelQuotientH2ClassVanishes,
          selectedProjective] using hselected
    rw [← hfinalFactor, hfactor]
    exact
      (FactorSet.h2Class_gauge
        selectedProjective.factorSet a).trans hselected'
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
