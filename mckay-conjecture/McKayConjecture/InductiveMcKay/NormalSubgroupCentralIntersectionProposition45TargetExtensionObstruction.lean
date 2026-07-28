/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import
  McKayConjecture.InductiveMcKay.CentralTripleTargetFactorExtensionObstruction
import
  McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45LiftedFactorCorrespondence
import
  McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45OuterQuotients
import
  McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45QuotientFactorRestriction

/-!
# The target-extension obstruction in Proposition 4.5

For a concrete matched Glauberman--Okuyama--Wajima inertia pair, this file
specializes the generic target factor-extension obstruction theorem.

It proves that an irreducible coefficient character on the pulled-back
target factor extension restricts to the matched normal character if and
only if the two inertia triples have the same intrinsic projective
obstruction class.  This is the exact character-extension part of the
Dade--Glauberman--Nagao refinement.  In particular, it is automatic when
the ambient quotient `X / CS` is cyclic, while the general case still
requires the projective-obstruction theorem proved block-theoretically in
Navarro--Späth, Proposition 5.12.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CharacterTriple.AssociatedProjectiveRepresentation
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- For one concrete Proposition-4.5 inertia pair, the existence of the
required target factor-extension character is equivalent to the intrinsic
projective-obstruction equality. -/
theorem exists_productAmbientGlaubermanTargetFactorExtensionCharacter_iff
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    let R :=
      productAmbientGlaubermanLeftAssociated
        S C hgenerate theta
    let F :=
      productAmbientGlaubermanLeftFiniteFactorNormalization
        S C hgenerate theta
    let data :=
      productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta
    (∃ psi :
        IrreducibleCharacter
          (LiftedFactorCorrespondence.TargetFactorCentralExtensionGroup
            R F data),
      FactorSet.CentralExtensionGroup.HasCoefficientCharacter
          (LiftedFactorCorrespondence.targetFactorSet R F data)
          (LiftedFactorCorrespondence.targetFactorSet_isNormalized
            R F data)
          (LiftedFactorCorrespondence.coefficientHom R F data) psi ∧
        IrreducibleCharacter.IsExtensionAlong
          (LiftedFactorCorrespondence.targetNormalLift R F data)
          (productAmbientGlaubermanRightInertiaTriple
            S C hcentral hgenerate g theta).character psi) ↔
      ProductAmbientGlaubermanProjectiveObstructionClassAgreement
        S C hcentral hgenerate g theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    LiftedFactorCorrespondence.targetNormalExtensionClaim_iff_projectiveObstructionClassAgreement
      (productAmbientGlaubermanLeftAssociated
        S C hgenerate theta)
      (productAmbientGlaubermanLeftFiniteFactorNormalization
        S C hgenerate theta)
      (productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta)

/-- The named separated restriction claim used by the quotient-factor
induction is therefore exactly the intrinsic projective-obstruction
equality. -/
theorem productAmbientGlaubermanTargetNormalExtensionClaim_iff
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    ProductAmbientGlaubermanTargetNormalExtensionClaim
        S C hcentral hgenerate g theta ↔
      ProductAmbientGlaubermanProjectiveObstructionClassAgreement
        S C hcentral hgenerate g theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  change
    (∃ psi :
        IrreducibleCharacter
          (LiftedFactorCorrespondence.TargetFactorCentralExtensionGroup
            (productAmbientGlaubermanLeftAssociated
              S C hgenerate theta)
            (productAmbientGlaubermanLeftFiniteFactorNormalization
              S C hgenerate theta)
            (productAmbientGlaubermanInertiaRestrictionGroupData
              S C hcentral hgenerate g theta)),
      FactorSet.CentralExtensionGroup.HasCoefficientCharacter
          (LiftedFactorCorrespondence.targetFactorSet
            (productAmbientGlaubermanLeftAssociated
              S C hgenerate theta)
            (productAmbientGlaubermanLeftFiniteFactorNormalization
              S C hgenerate theta)
            (productAmbientGlaubermanInertiaRestrictionGroupData
              S C hcentral hgenerate g theta))
          (LiftedFactorCorrespondence.targetFactorSet_isNormalized
            (productAmbientGlaubermanLeftAssociated
              S C hgenerate theta)
            (productAmbientGlaubermanLeftFiniteFactorNormalization
              S C hgenerate theta)
            (productAmbientGlaubermanInertiaRestrictionGroupData
              S C hcentral hgenerate g theta))
          (LiftedFactorCorrespondence.coefficientHom
            (productAmbientGlaubermanLeftAssociated
              S C hgenerate theta)
            (productAmbientGlaubermanLeftFiniteFactorNormalization
              S C hgenerate theta)
            (productAmbientGlaubermanInertiaRestrictionGroupData
              S C hcentral hgenerate g theta)) psi ∧
        IrreducibleCharacter.IsExtensionAlong
          (LiftedFactorCorrespondence.targetNormalLift
            (productAmbientGlaubermanLeftAssociated
              S C hgenerate theta)
            (productAmbientGlaubermanLeftFiniteFactorNormalization
              S C hgenerate theta)
            (productAmbientGlaubermanInertiaRestrictionGroupData
              S C hcentral hgenerate g theta))
          (productAmbientGlaubermanRightInertiaTriple
            S C hcentral hgenerate g theta).character psi) ↔
      ProductAmbientGlaubermanProjectiveObstructionClassAgreement
        S C hcentral hgenerate g theta
  exact
    exists_productAmbientGlaubermanTargetFactorExtensionCharacter_iff
      S C hcentral hgenerate g theta

/-- A cyclic ambient quotient supplies the target factor-extension
character and its exact matched-normal restriction constructively. -/
theorem exists_productAmbientGlaubermanTargetFactorExtensionCharacter_of_cyclic
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hcyclic :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      IsCyclic (X ⧸ product S C)) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    let R :=
      productAmbientGlaubermanLeftAssociated
        S C hgenerate theta
    let F :=
      productAmbientGlaubermanLeftFiniteFactorNormalization
        S C hgenerate theta
    let data :=
      productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta
    ∃ psi :
        IrreducibleCharacter
          (LiftedFactorCorrespondence.TargetFactorCentralExtensionGroup
            R F data),
      FactorSet.CentralExtensionGroup.HasCoefficientCharacter
          (LiftedFactorCorrespondence.targetFactorSet R F data)
          (LiftedFactorCorrespondence.targetFactorSet_isNormalized
            R F data)
          (LiftedFactorCorrespondence.coefficientHom R F data) psi ∧
        IrreducibleCharacter.IsExtensionAlong
          (LiftedFactorCorrespondence.targetNormalLift R F data)
          (productAmbientGlaubermanRightInertiaTriple
            S C hcentral hgenerate g theta).character psi := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  apply
    (exists_productAmbientGlaubermanTargetFactorExtensionCharacter_iff
      S C hcentral hgenerate g theta).mpr
  exact
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_cyclic
      S C hcentral hgenerate g theta hcyclic

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
