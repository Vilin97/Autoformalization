/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedProjectiveObstructionCoprimeExtension
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45OuterQuotients

/-!
# Coprime projective obstructions in Proposition 4.5

For each concrete Proposition-4.5 inertia pair, the canonical associated
projective representations have possibly different association-preserving
factor exponents.  If both exponents are coprime to the common order of the
two outer quotients, both intrinsic projective obstruction classes vanish.
They therefore agree under the canonical quotient equivalence.

The two coprimality assumptions are kept separate and explicit.  Equality
of the quotient orders alone does not identify the two obstruction classes,
so a one-sided coprimality assumption would not suffice.

When `X / CS` is commutative, the existing conjugation-invariant scalar
correction construction then supplies the full projective comparison.  The
last definitions package this first for every character in one concrete
comparison and then as a global conditional central-intersection reduction.
-/

noncomputable section

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

/-- The association-preserving exponent of the canonical left associated
projective representation. -/
abbrev productAmbientGlaubermanLeftCanonicalAssociatedFactorExponent
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  associatedFactorExponent
    (productAmbientGlaubermanLeftInertiaTriple
      S C hgenerate theta)
    (productAmbientGlaubermanLeftInertiaTriple
      S C hgenerate theta).character.realization

/-- The association-preserving exponent of the canonical right associated
projective representation. -/
abbrev productAmbientGlaubermanRightCanonicalAssociatedFactorExponent
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  associatedFactorExponent
    (productAmbientGlaubermanRightInertiaTriple
      S C hcentral hgenerate g theta)
    (productAmbientGlaubermanRightInertiaTriple
      S C hcentral hgenerate g theta).character.realization

/-- The common outer quotient order, represented by the left quotient.
The canonical quotient equivalence proves that the right quotient has this
same order. -/
abbrev productAmbientGlaubermanCommonOuterQuotientOrder
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  Nat.card
    (productAmbientGlaubermanLeftOuterQuotient
      S C hgenerate theta)

/-- Both canonical association-preserving factor exponents are coprime to
the common outer quotient order. -/
def ProductAmbientGlaubermanCanonicalFactorExponentsCoprime
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) : Prop :=
  Nat.Coprime
      (productAmbientGlaubermanLeftCanonicalAssociatedFactorExponent
        S C hgenerate theta)
      (productAmbientGlaubermanCommonOuterQuotientOrder
        S C hgenerate theta) ∧
    Nat.Coprime
      (productAmbientGlaubermanRightCanonicalAssociatedFactorExponent
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanCommonOuterQuotientOrder
        S C hgenerate theta)

/-- The left intrinsic obstruction vanishes under the left half of the
canonical coprimality condition. -/
theorem productAmbientGlaubermanLeftProjectiveObstructionClass_eq_zero_of_coprime
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hcoprime :
      ProductAmbientGlaubermanCanonicalFactorExponentsCoprime
        S C hcentral hgenerate g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    let T :=
      productAmbientGlaubermanLeftInertiaTriple
        S C hgenerate theta
    letI :=
      trivialMulDistribMulAction
        (productAmbientGlaubermanLeftOuterQuotient
          S C hgenerate theta) ℂˣ
    T.projectiveObstructionClass = 0 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta
      ).projectiveObstructionClass_eq_zero_of_associatedFactorExponent_coprime
        hcoprime.1

/-- The right intrinsic obstruction vanishes under the right half of the
canonical coprimality condition.  The quotient equivalence is used only to
transport the group order appearing in that condition. -/
theorem productAmbientGlaubermanRightProjectiveObstructionClass_eq_zero_of_coprime
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hcoprime :
      ProductAmbientGlaubermanCanonicalFactorExponentsCoprime
        S C hcentral hgenerate g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    let U :=
      productAmbientGlaubermanRightInertiaTriple
        S C hcentral hgenerate g theta
    letI :=
      trivialMulDistribMulAction
        (productAmbientGlaubermanRightOuterQuotient
          S C hcentral hgenerate g theta) ℂˣ
    U.projectiveObstructionClass = 0 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  have hrightCoprime :
      Nat.Coprime
        (productAmbientGlaubermanRightCanonicalAssociatedFactorExponent
          S C hcentral hgenerate g theta)
        (Nat.card
          (productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta)) := by
    rw [productAmbientGlaubermanOuterQuotient_card_eq
      S C hcentral hgenerate g theta]
    exact hcoprime.2
  exact
    (productAmbientGlaubermanRightAssociated
      S C hcentral hgenerate g theta
      ).projectiveObstructionClass_eq_zero_of_associatedFactorExponent_coprime
        hrightCoprime

/-- The left coprime criterion produces an honest irreducible extension of
the left inertia-normal character. -/
theorem productAmbientGlaubermanLeftExistsExtension_of_coprime
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hcoprime :
      ProductAmbientGlaubermanCanonicalFactorExponentsCoprime
        S C hcentral hgenerate g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    let T :=
      productAmbientGlaubermanLeftInertiaTriple
        S C hgenerate theta
    ∃ psi :
        IrreducibleCharacter
          (IrreducibleCharacter.inertia
            (product S C) theta.1),
      IrreducibleCharacter.IsExtensionAlong
        T.normalSubgroup.subtype T.character psi := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta
      ).exists_extension_of_associatedFactorExponent_coprime
        hcoprime.1

/-- The right coprime criterion produces an honest irreducible extension of
the matched right inertia-normal character. -/
theorem productAmbientGlaubermanRightExistsExtension_of_coprime
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hcoprime :
      ProductAmbientGlaubermanCanonicalFactorExponentsCoprime
        S C hcentral hgenerate g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    let U :=
      productAmbientGlaubermanRightInertiaTriple
        S C hcentral hgenerate g theta
    ∃ psi :
        IrreducibleCharacter
          (IrreducibleCharacter.inertia
            (internalProductNormalizer S C)
            (productAmbientGlaubermanRightCharacter
              S C hcentral g theta)),
      IrreducibleCharacter.IsExtensionAlong
        U.normalSubgroup.subtype U.character psi := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  have hrightCoprime :
      Nat.Coprime
        (productAmbientGlaubermanRightCanonicalAssociatedFactorExponent
          S C hcentral hgenerate g theta)
        (Nat.card
          (productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta)) := by
    rw [productAmbientGlaubermanOuterQuotient_card_eq
      S C hcentral hgenerate g theta]
    exact hcoprime.2
  exact
    (productAmbientGlaubermanRightAssociated
      S C hcentral hgenerate g theta
      ).exists_extension_of_associatedFactorExponent_coprime
        hrightCoprime

/-- Per-character intrinsic `H²` agreement obtained by killing both
canonical obstruction classes with their coprime exponent bounds. -/
theorem productAmbientGlaubermanProjectiveObstructionClassAgreement_of_coprime
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hcoprime :
      ProductAmbientGlaubermanCanonicalFactorExponentsCoprime
        S C hcentral hgenerate g theta) :
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
      ).quotientFactorH2ClassAgreement_of_both_obstructions_eq_zero
        (productAmbientGlaubermanRightAssociated
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanInertiaRestrictionGroupData
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanLeftProjectiveObstructionClass_eq_zero_of_coprime
          S C hcentral hgenerate g theta hcoprime)
        (productAmbientGlaubermanRightProjectiveObstructionClass_eq_zero_of_coprime
          S C hcentral hgenerate g theta hcoprime)

/-- For one character, the two coprime exponent conditions and
commutativity of `X / CS` construct scalar-correctable projective comparison
data. -/
def productAmbientGlaubermanScalarCorrectionOfCoprimeOfCommutativeQuotient
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hcoprime :
      ProductAmbientGlaubermanCanonicalFactorExponentsCoprime
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
  productAmbientGlaubermanScalarCorrectionOfCommutativeQuotient
    S C hcentral hgenerate g theta
    (productAmbientGlaubermanProjectiveObstructionClassAgreement_of_coprime
      S C hcentral hgenerate g theta hcoprime)
    hcommutative

/-- The concrete coprime exponent condition for every matched character in
one Proposition-4.5 comparison. -/
def ProductAmbientGlaubermanCanonicalFactorExponentsCoprimeForAll
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral) : Prop :=
  ∀ theta :
      PPrimeIrreducibleCharacter
        (product S C) q,
    ProductAmbientGlaubermanCanonicalFactorExponentsCoprime
      S C hcentral hgenerate g theta

/-- Package the per-character coprime construction simultaneously for all
matched inertia pairs in one concrete comparison. -/
def productAmbientGlaubermanProjectiveScalarCorrectionDataOfCoprimeOfCommutativeQuotient
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (hcoprime :
      ProductAmbientGlaubermanCanonicalFactorExponentsCoprimeForAll
        S C hcentral hgenerate g)
    (hcommutative :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      IsMulCommutative (X ⧸ product S C)) :
    ProductAmbientGlaubermanProjectiveScalarCorrectionData
      S C hcentral hgenerate g := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    { comparison := fun theta ↦
        productAmbientGlaubermanScalarCorrectionOfCoprimeOfCommutativeQuotient
          S C hcentral hgenerate g theta
          (hcoprime theta) hcommutative }

end Proposition45

open Proposition45

/-- Global conditional input: every ambient product quotient is
commutative, and both canonical association-preserving exponents are
coprime to the common inertia-quotient order for every correspondence and
every matched character. -/
def CentralScalarCentralIntersectionCommutativeCoprimeFactorExponentHypothesis
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
      IsMulCommutative (X ⧸ product S C) ∧
        ∀ g :
            ComplementReduction.ProductGlaubermanCorrespondence
              S C hcentral,
          Proposition45.ProductAmbientGlaubermanCanonicalFactorExponentsCoprimeForAll
            S C hcentral hgenerate g

/-- The global commutative-and-coprime condition supplies the complete
projective scalar-correction hypothesis. -/
theorem projectiveScalarCorrectionHypothesis_of_commutativeCoprimeFactorExponents
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionCommutativeCoprimeFactorExponentHypothesis
        q) :
    CentralScalarCentralIntersectionProjectiveScalarCorrectionHypothesis
      q := by
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  intro g
  obtain ⟨hcommutative, hcoprime⟩ :=
    h X S C hCnormal hcentral hgenerate
  exact
    ⟨productAmbientGlaubermanProjectiveScalarCorrectionDataOfCoprimeOfCommutativeQuotient
      S C hcentral hgenerate g
      (hcoprime g) hcommutative⟩

/-- The global commutative-and-coprime condition implies the full
Proposition-4.5 central-intersection reduction. -/
theorem centralScalarCentralIntersectionReductionHypothesis_of_commutativeCoprimeFactorExponents
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionCommutativeCoprimeFactorExponentHypothesis
        q) :
    CentralScalarCentralIntersectionReductionHypothesis q :=
  centralScalarCentralIntersectionReductionHypothesis_of_scalarCorrection
    (projectiveScalarCorrectionHypothesis_of_commutativeCoprimeFactorExponents
      h)

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
