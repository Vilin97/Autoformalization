/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InertiaQuotientEmbedding
import McKayConjecture.GroupTheory.SylowContainingQuotient
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveObstructionAutomatic
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45AutomaticScalarCorrection

/-!
# Outer quotients in the concrete Proposition 4.5 comparison

Let `N = CS` and `H = N_X(S)`.  Under the usual generation hypothesis,
`N` is normal in `X`.  Since it contains the chosen Sylow `q`-subgroup,
`X / N` has order prime to `q`.

For every character occurring in the concrete Glauberman comparison:

* the left inertia quotient injects into `X / N`;
* the ordinary restriction-group data canonically identifies the right
  inertia quotient with the left one;
* consequently both inertia quotients have order prime to `q`.

The cyclic and commutative specializations record exactly what these group
facts discharge.  A cyclic ambient quotient makes both the intrinsic
projective obstruction and the scalar correction automatic.  A merely
commutative ambient quotient makes the scalar correction automatic only
after intrinsic `H²` agreement has been supplied.
-/

noncomputable section

open scoped IsMulCommutative

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CliffordEquivalence
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The left outer quotient in the concrete Proposition-4.5 inertia
comparison. -/
abbrev productAmbientGlaubermanLeftOuterQuotient
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  IrreducibleCharacter.inertia (product S C) theta.1 ⧸
    inertiaNormalCopy (product S C) theta.1

/-- The matched target character used in the right inertia quotient. -/
abbrev productAmbientGlaubermanRightCharacter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    IrreducibleCharacter
      (internalProductNormalizer S C) :=
  (internalTheorem44CharacterEquiv
    S C
    (complementCharacterEquivOfGlauberman
      S C hcentral g) theta).1

/-- The right outer quotient in the concrete Proposition-4.5 inertia
comparison. -/
abbrev productAmbientGlaubermanRightOuterQuotient
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  IrreducibleCharacter.inertia
      (internalProductNormalizer S C)
      (productAmbientGlaubermanRightCharacter
        S C hcentral g theta) ⧸
    inertiaNormalCopy
      (internalProductNormalizer S C)
      (productAmbientGlaubermanRightCharacter
        S C hcentral g theta)

/-- The ambient quotient `X / CS` has order prime to `q`. -/
theorem productQuotient_isPPrimeGroup
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    IsPPrimeGroup q (X ⧸ product S C) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    quotient_isPPrimeGroup_of_sylow_le
      S (product S C) le_sup_right

/-- The canonical embedding of the left inertia quotient into `X / CS`. -/
def productAmbientGlaubermanLeftOuterEmbedding
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    productAmbientGlaubermanLeftOuterQuotient
          S C hgenerate theta →*
        X ⧸ product S C := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    inertiaQuotientEmbedding
      (product S C) theta.1

/-- The left outer embedding is injective. -/
theorem productAmbientGlaubermanLeftOuterEmbedding_injective
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    Function.Injective
      (productAmbientGlaubermanLeftOuterEmbedding
        S C hgenerate theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    inertiaQuotientEmbedding_injective
      (product S C) theta.1

/-- The ordinary concrete restriction data canonically identifies the
right and left outer quotients. -/
def productAmbientGlaubermanOuterQuotientEquiv
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
    productAmbientGlaubermanRightOuterQuotient
          S C hcentral hgenerate g theta ≃*
        productAmbientGlaubermanLeftOuterQuotient
          S C hgenerate theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    (productAmbientGlaubermanInertiaRestrictionGroupData
      S C hcentral hgenerate g theta).quotientEquiv

/-- The right outer quotient embeds in the same ambient quotient, through
the canonical comparison with the left outer quotient. -/
def productAmbientGlaubermanRightOuterEmbedding
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
    productAmbientGlaubermanRightOuterQuotient
          S C hcentral hgenerate g theta →*
        X ⧸ product S C := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    (productAmbientGlaubermanLeftOuterEmbedding
      S C hgenerate theta).comp
        (productAmbientGlaubermanOuterQuotientEquiv
          S C hcentral hgenerate g theta).toMonoidHom

/-- The right outer embedding is injective. -/
theorem productAmbientGlaubermanRightOuterEmbedding_injective
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
    Function.Injective
      (productAmbientGlaubermanRightOuterEmbedding
        S C hcentral hgenerate g theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    (productAmbientGlaubermanLeftOuterEmbedding_injective
      S C hgenerate theta).comp
        (productAmbientGlaubermanOuterQuotientEquiv
          S C hcentral hgenerate g theta).injective

/-- Every concrete left inertia quotient has order prime to `q`. -/
theorem productAmbientGlaubermanLeftOuterQuotient_isPPrimeGroup
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    IsPPrimeGroup q
      (productAmbientGlaubermanLeftOuterQuotient
        S C hgenerate theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    inertiaQuotient_isPPrimeGroup
      (product S C) theta.1
      (productQuotient_isPPrimeGroup
        S C hgenerate)

/-- Every concrete right inertia quotient has order prime to `q`. -/
theorem productAmbientGlaubermanRightOuterQuotient_isPPrimeGroup
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
    IsPPrimeGroup q
      (productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    (productAmbientGlaubermanLeftOuterQuotient_isPPrimeGroup
      S C hgenerate theta).of_equiv
        (productAmbientGlaubermanOuterQuotientEquiv
          S C hcentral hgenerate g theta).symm

/-- The left outer quotient order divides the ambient quotient order. -/
theorem productAmbientGlaubermanLeftOuterQuotient_card_dvd
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    Nat.card
        (productAmbientGlaubermanLeftOuterQuotient
          S C hgenerate theta) ∣
      Nat.card (X ⧸ product S C) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    card_inertiaQuotient_dvd_card_ambientQuotient
      (product S C) theta.1

/-- The two matched outer quotients have equal order. -/
theorem productAmbientGlaubermanOuterQuotient_card_eq
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
    Nat.card
        (productAmbientGlaubermanRightOuterQuotient
          S C hcentral hgenerate g theta) =
      Nat.card
        (productAmbientGlaubermanLeftOuterQuotient
          S C hgenerate theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    Nat.card_congr
      (productAmbientGlaubermanOuterQuotientEquiv
        S C hcentral hgenerate g theta).toEquiv

/-- The right outer quotient order also divides the ambient quotient
order. -/
theorem productAmbientGlaubermanRightOuterQuotient_card_dvd
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
    Nat.card
        (productAmbientGlaubermanRightOuterQuotient
          S C hcentral hgenerate g theta) ∣
      Nat.card (X ⧸ product S C) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  rw [productAmbientGlaubermanOuterQuotient_card_eq
    S C hcentral hgenerate g theta]
  exact
    productAmbientGlaubermanLeftOuterQuotient_card_dvd
      S C hgenerate theta

/-- Squarefreeness of `|X / CS|` passes to the left inertia quotient. -/
theorem productAmbientGlaubermanLeftOuterQuotient_card_squarefree
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
    Squarefree
      (Nat.card
        (productAmbientGlaubermanLeftOuterQuotient
          S C hgenerate theta)) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    inertiaQuotient_card_squarefree
      (product S C) theta.1 hsquarefree

/-- Squarefreeness of `|X / CS|` passes to the right inertia quotient. -/
theorem productAmbientGlaubermanRightOuterQuotient_card_squarefree
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
    Squarefree
      (Nat.card
        (productAmbientGlaubermanRightOuterQuotient
          S C hcentral hgenerate g theta)) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  rw [productAmbientGlaubermanOuterQuotient_card_eq
    S C hcentral hgenerate g theta]
  exact
    productAmbientGlaubermanLeftOuterQuotient_card_squarefree
      S C hgenerate theta hsquarefree

/-- Cyclicity of `X / CS` passes to the left inertia quotient. -/
theorem productAmbientGlaubermanLeftOuterQuotient_isCyclic
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hcyclic :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      IsCyclic (X ⧸ product S C)) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    IsCyclic
      (productAmbientGlaubermanLeftOuterQuotient
        S C hgenerate theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    inertiaQuotient_isCyclic
      (product S C) theta.1 hcyclic

/-- Cyclicity of `X / CS` passes to the matched right inertia quotient. -/
theorem productAmbientGlaubermanRightOuterQuotient_isCyclic
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
    IsCyclic
      (productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    (productAmbientGlaubermanOuterQuotientEquiv
      S C hcentral hgenerate g theta).isCyclic.mpr
        (productAmbientGlaubermanLeftOuterQuotient_isCyclic
          S C hgenerate theta hcyclic)

/-- If `X / CS` is commutative, the right inertia quotient is
commutative. -/
theorem productAmbientGlaubermanRightOuterQuotient_isMulCommutative
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hcommutative :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      IsMulCommutative (X ⧸ product S C)) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    IsMulCommutative
      (productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  letI : IsMulCommutative (X ⧸ product S C) :=
    hcommutative
  apply isMulCommutative_iff.mpr
  intro a b
  apply
    productAmbientGlaubermanRightOuterEmbedding_injective
      S C hcentral hgenerate g theta
  simp only [map_mul]
  exact mul_comm _ _

/-- Commutativity of `X / CS` is exactly enough to force the concrete
right-inertia commutator into its normal copy. -/
theorem productAmbientGlaubermanRightInertiaCommutatorLeNormal_of_commutative
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hcommutative :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      IsMulCommutative (X ⧸ product S C)) :
    ProductAmbientGlaubermanRightInertiaCommutatorLeNormal
      S C hcentral hgenerate g theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  letI :
      IsMulCommutative
        (productAmbientGlaubermanRightOuterQuotient
          S C hcentral hgenerate g theta) :=
    productAmbientGlaubermanRightOuterQuotient_isMulCommutative
      S C hcentral hgenerate g theta hcommutative
  exact
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (inferInstance :
        IsMulCommutative
          (productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta))

/-- A cyclic ambient quotient makes the intrinsic projective obstruction
agreement automatic. -/
theorem productAmbientGlaubermanProjectiveObstructionClassAgreement_of_cyclic
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
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta
      ).quotientFactorH2ClassAgreement_of_isCyclic_leftQuotient
        (productAmbientGlaubermanRightAssociated
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanInertiaRestrictionGroupData
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanLeftOuterQuotient_isCyclic
          S C hgenerate theta hcyclic)

/-- With a commutative ambient quotient, intrinsic `H²` agreement is the
only remaining premise for scalar-correctable projective comparison. -/
def productAmbientGlaubermanScalarCorrectionOfCommutativeQuotient
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hH2 :
      ProductAmbientGlaubermanProjectiveObstructionClassAgreement
        S C hcentral hgenerate g theta)
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
  productAmbientGlaubermanScalarCorrectionOfCommutatorLeNormal
    S C hcentral hgenerate g theta hH2
    (productAmbientGlaubermanRightInertiaCommutatorLeNormal_of_commutative
      S C hcentral hgenerate g theta hcommutative)

/-- A cyclic ambient quotient discharges both intrinsic `H²` agreement
and the scalar correction for one concrete inertia pair. -/
def productAmbientGlaubermanScalarCorrectionOfCyclicQuotient
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
    H2ScalarCorrectableProjectiveComparisonData
      (productAmbientGlaubermanLeftInertiaTriple
        S C hgenerate theta)
      (productAmbientGlaubermanRightInertiaTriple
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInertiaEmbedding
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : IsCyclic (X ⧸ product S C) :=
    hcyclic
  exact
    productAmbientGlaubermanScalarCorrectionOfCommutativeQuotient
      S C hcentral hgenerate g theta
      (productAmbientGlaubermanProjectiveObstructionClassAgreement_of_cyclic
        S C hcentral hgenerate g theta hcyclic)
      (inferInstance : IsMulCommutative
        (X ⧸ product S C))

/-- Package the cyclic ambient-quotient construction simultaneously for
all matched inertia pairs. -/
def productAmbientGlaubermanProjectiveScalarCorrectionDataOfCyclicQuotient
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (hcyclic :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      IsCyclic (X ⧸ product S C)) :
    ProductAmbientGlaubermanProjectiveScalarCorrectionData
      S C hcentral hgenerate g := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    { comparison := fun theta ↦
        productAmbientGlaubermanScalarCorrectionOfCyclicQuotient
          S C hcentral hgenerate g theta hcyclic }

end Proposition45

/-- Conditional cyclic-outer-quotient case of the central-intersection
branch.  This is deliberately a separate hypothesis: `hcentral` and
`hgenerate` force the quotient order to be prime to `q`, but do not force
the quotient itself to be cyclic. -/
def CentralScalarCentralIntersectionCyclicProductQuotientHypothesis
    (q : ℕ) [Fact q.Prime] : Prop :=
  ∀ (X : Type) [Group X] [Finite X]
    (S : Sylow q X) (C : Subgroup X)
    (hCnormal : C.Normal)
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤),
      letI : C.Normal := hCnormal
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      IsCyclic (X ⧸ product S C)

/-- Cyclicity of every ambient quotient `X / CS` supplies the complete
projective scalar-correction hypothesis. -/
theorem projectiveScalarCorrectionHypothesis_of_cyclicProductQuotient
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionCyclicProductQuotientHypothesis
        q) :
    CentralScalarCentralIntersectionProjectiveScalarCorrectionHypothesis
      q := by
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  intro g
  exact
    ⟨Proposition45.productAmbientGlaubermanProjectiveScalarCorrectionDataOfCyclicQuotient
      S C hcentral hgenerate g
      (h X S C hCnormal hcentral hgenerate)⟩

/-- The cyclic ambient-quotient case implies the full Proposition-4.5
central-intersection reduction. -/
theorem centralScalarCentralIntersectionReductionHypothesis_of_cyclicProductQuotient
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionCyclicProductQuotientHypothesis
        q) :
    CentralScalarCentralIntersectionReductionHypothesis q :=
  centralScalarCentralIntersectionReductionHypothesis_of_scalarCorrection
    (projectiveScalarCorrectionHypothesis_of_cyclicProductQuotient h)

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
