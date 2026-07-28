/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetSquarefreeOrderVanishing
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45OuterQuotients

/-!
# Squarefree outer quotients in Proposition 4.5

Squarefreeness of the ambient quotient `X / CS` passes to both concrete
inertia quotients.  The pinned `Z`-group classification therefore writes each
outer quotient as a coprime cyclic-by-cyclic semidirect product, and the
canonical associated factor set restricts to a coboundary on both cyclic
factors.

This is the strongest unconditional squarefree-order conclusion currently
available from the pinned cohomology API.  Passing from the two cyclic
restrictions to global `H²`-vanishing needs cohomological corestriction and the
formula `cor ∘ res = [G : H]`; those are not present in the pinned mathlib.

For a commutative squarefree ambient quotient, the `Z`-group theorem does
imply cyclicity.  In that specialization the existing cyclic-quotient results
make intrinsic `H²` agreement and scalar correction completely automatic.
-/

noncomputable section

open scoped IsMulCommutative

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CharacterTriple.AssociatedProjectiveRepresentation
open CliffordEquivalence
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The canonical left quotient factor set has split restrictions to both
cyclic factors in the squarefree-order `Z`-group decomposition. -/
theorem productAmbientGlaubermanLeftSquarefreeFactorRestrictions
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hsquarefree :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      Squarefree (Nat.card (X ⧸ product S C))) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    ((productAmbientGlaubermanLeftAssociated
      S C hgenerate theta).quotientFactorSet
        ).HasCyclicCoprimeCoboundaryRestrictions := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta
      ).quotientFactorSet.hasCyclicCoprimeCoboundaryRestrictions_of_squarefree_card
        (productAmbientGlaubermanLeftAssociated
          S C hgenerate theta).quotientFactorSet_isNormalized
        (productAmbientGlaubermanLeftOuterQuotient_card_squarefree
          S C hgenerate theta hsquarefree)

/-- The canonical right quotient factor set has split restrictions to both
cyclic factors in the squarefree-order `Z`-group decomposition. -/
theorem productAmbientGlaubermanRightSquarefreeFactorRestrictions
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hsquarefree :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      Squarefree (Nat.card (X ⧸ product S C))) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ((productAmbientGlaubermanRightAssociated
      S C hcentral hgenerate g theta).quotientFactorSet
        ).HasCyclicCoprimeCoboundaryRestrictions := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    (productAmbientGlaubermanRightAssociated
      S C hcentral hgenerate g theta
      ).quotientFactorSet.hasCyclicCoprimeCoboundaryRestrictions_of_squarefree_card
        (productAmbientGlaubermanRightAssociated
          S C hcentral hgenerate g theta).quotientFactorSet_isNormalized
        (productAmbientGlaubermanRightOuterQuotient_card_squarefree
          S C hcentral hgenerate g theta hsquarefree)

omit [Fact q.Prime] in
/-- A commutative squarefree ambient quotient is cyclic. -/
theorem productQuotient_isCyclic_of_squarefree_of_isMulCommutative
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (hsquarefree :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      Squarefree (Nat.card (X ⧸ product S C)))
    (hcommutative :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      IsMulCommutative (X ⧸ product S C)) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    IsCyclic (X ⧸ product S C) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    FactorSet.isCyclic_of_squarefree_card_of_isMulCommutative
      hsquarefree hcommutative

/-- The canonical left quotient factor class vanishes when the ambient
product quotient is squarefree and commutative. -/
theorem productAmbientGlaubermanLeftFactorH2Class_eq_zero_of_squarefree_commutative
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hsquarefree :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      Squarefree (Nat.card (X ⧸ product S C)))
    (hcommutative :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      IsMulCommutative (X ⧸ product S C)) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :=
      trivialMulDistribMulAction
        (productAmbientGlaubermanLeftOuterQuotient
          S C hgenerate theta) ℂˣ
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta).quotientFactorSet.h2Class = 0 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  have hcyclicOuter :
      IsCyclic
        (productAmbientGlaubermanLeftOuterQuotient
          S C hgenerate theta) :=
    productAmbientGlaubermanLeftOuterQuotient_isCyclic
      S C hgenerate theta
      (productQuotient_isCyclic_of_squarefree_of_isMulCommutative
        S C hgenerate hsquarefree hcommutative)
  let T :=
    productAmbientGlaubermanLeftInertiaTriple
      S C hgenerate theta
  have hcyclicFactor :
      IsCyclic
        (IrreducibleCharacter.inertia
            (product S C) theta.1 ⧸
          T.normalSubgroup) := by
    change
      IsCyclic
        (productAmbientGlaubermanLeftOuterQuotient
          S C hgenerate theta)
    exact hcyclicOuter
  letI :
      IsCyclic
        (IrreducibleCharacter.inertia
            (product S C) theta.1 ⧸
          T.normalSubgroup) :=
    hcyclicFactor
  exact
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta
      ).quotientFactorSet.h2Class_eq_zero_of_isCyclic
        (productAmbientGlaubermanLeftAssociated
          S C hgenerate theta).quotientFactorSet_isNormalized

/-- The canonical right quotient factor class vanishes when the ambient
product quotient is squarefree and commutative. -/
theorem productAmbientGlaubermanRightFactorH2Class_eq_zero_of_squarefree_commutative
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hsquarefree :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      Squarefree (Nat.card (X ⧸ product S C)))
    (hcommutative :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      IsMulCommutative (X ⧸ product S C)) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    letI :=
      trivialMulDistribMulAction
        (productAmbientGlaubermanRightOuterQuotient
          S C hcentral hgenerate g theta) ℂˣ
    (productAmbientGlaubermanRightAssociated
      S C hcentral hgenerate g theta
      ).quotientFactorSet.h2Class = 0 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  have hcyclicOuter :
      IsCyclic
        (productAmbientGlaubermanRightOuterQuotient
          S C hcentral hgenerate g theta) :=
    productAmbientGlaubermanRightOuterQuotient_isCyclic
      S C hcentral hgenerate g theta
      (productQuotient_isCyclic_of_squarefree_of_isMulCommutative
        S C hgenerate hsquarefree hcommutative)
  let T :=
    productAmbientGlaubermanRightInertiaTriple
      S C hcentral hgenerate g theta
  have hcyclicFactor :
      IsCyclic
        (IrreducibleCharacter.inertia
            (internalProductNormalizer S C)
            (productAmbientGlaubermanRightCharacter
              S C hcentral g theta) ⧸
          T.normalSubgroup) := by
    change
      IsCyclic
        (productAmbientGlaubermanRightOuterQuotient
          S C hcentral hgenerate g theta)
    exact hcyclicOuter
  letI :
      IsCyclic
        (IrreducibleCharacter.inertia
            (internalProductNormalizer S C)
            (productAmbientGlaubermanRightCharacter
              S C hcentral g theta) ⧸
          T.normalSubgroup) :=
    hcyclicFactor
  exact
    (productAmbientGlaubermanRightAssociated
      S C hcentral hgenerate g theta
      ).quotientFactorSet.h2Class_eq_zero_of_isCyclic
        (productAmbientGlaubermanRightAssociated
          S C hcentral hgenerate g theta).quotientFactorSet_isNormalized

/-- Squarefreeness and commutativity of `X / CS` make the intrinsic
projective-obstruction agreement automatic for one matched inertia pair. -/
theorem productAmbientGlaubermanObstructionAgreement_of_squarefree_commutative
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hsquarefree :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      Squarefree (Nat.card (X ⧸ product S C)))
    (hcommutative :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      IsMulCommutative (X ⧸ product S C)) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta :=
  productAmbientGlaubermanProjectiveObstructionClassAgreement_of_cyclic
    S C hcentral hgenerate g theta
    (productQuotient_isCyclic_of_squarefree_of_isMulCommutative
      S C hgenerate hsquarefree hcommutative)

/-- Squarefreeness and commutativity of `X / CS` discharge both intrinsic
`H²` agreement and scalar correction for one matched inertia pair. -/
def productAmbientGlaubermanScalarCorrectionOfSquarefreeCommutativeQuotient
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hsquarefree :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      Squarefree (Nat.card (X ⧸ product S C)))
    (hcommutative :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      IsMulCommutative (X ⧸ product S C)) :
    H2ScalarCorrectableProjectiveComparisonData
      (productAmbientGlaubermanLeftInertiaTriple
        S C hgenerate theta)
      (productAmbientGlaubermanRightInertiaTriple
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInertiaEmbedding
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta) :=
  productAmbientGlaubermanScalarCorrectionOfCyclicQuotient
    S C hcentral hgenerate g theta
    (productQuotient_isCyclic_of_squarefree_of_isMulCommutative
      S C hgenerate hsquarefree hcommutative)

/-- Package the squarefree-and-commutative construction for every matched
character in one Proposition-4.5 comparison. -/
def productAmbientGlaubermanScalarCorrectionDataOfSquarefreeCommutativeQuotient
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (hsquarefree :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      Squarefree (Nat.card (X ⧸ product S C)))
    (hcommutative :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      IsMulCommutative (X ⧸ product S C)) :
    ProductAmbientGlaubermanProjectiveScalarCorrectionData
      S C hcentral hgenerate g :=
  productAmbientGlaubermanProjectiveScalarCorrectionDataOfCyclicQuotient
    S C hcentral hgenerate g
    (productQuotient_isCyclic_of_squarefree_of_isMulCommutative
      S C hgenerate hsquarefree hcommutative)

end Proposition45

/-- Global conditional branch in which every ambient product quotient is
both squarefree and commutative. -/
def CentralScalarCentralIntersectionSquarefreeCommutativeProductQuotientHypothesis
    (q : ℕ) [Fact q.Prime] : Prop :=
  ∀ (X : Type) [Group X] [Finite X]
    (S : Sylow q X) (C : Subgroup X)
    (hCnormal : C.Normal)
    (_hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤),
      letI : C.Normal := hCnormal
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      Squarefree (Nat.card (X ⧸ product S C)) ∧
        IsMulCommutative (X ⧸ product S C)

/-- Squarefree commutative ambient quotients supply the complete
projective scalar-correction hypothesis. -/
theorem projectiveScalarCorrectionHypothesis_of_squarefreeCommutativeProductQuotient
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionSquarefreeCommutativeProductQuotientHypothesis
        q) :
    CentralScalarCentralIntersectionProjectiveScalarCorrectionHypothesis
      q := by
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  obtain ⟨hsquarefree, hcommutative⟩ :=
    h X S C hCnormal hcentral hgenerate
  intro g
  exact
    ⟨Proposition45.productAmbientGlaubermanScalarCorrectionDataOfSquarefreeCommutativeQuotient
      S C hcentral hgenerate g hsquarefree hcommutative⟩

/-- The squarefree-and-commutative ambient quotient condition implies the
full Proposition-4.5 central-intersection reduction. -/
theorem centralScalarCentralIntersectionReductionHypothesis_of_squarefreeCommutativeProductQuotient
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionSquarefreeCommutativeProductQuotientHypothesis
        q) :
    CentralScalarCentralIntersectionReductionHypothesis q :=
  centralScalarCentralIntersectionReductionHypothesis_of_scalarCorrection
    (projectiveScalarCorrectionHypothesis_of_squarefreeCommutativeProductQuotient
      h)

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
