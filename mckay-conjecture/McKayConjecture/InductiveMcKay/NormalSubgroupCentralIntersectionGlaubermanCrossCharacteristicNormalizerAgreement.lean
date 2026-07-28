/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebraBrauerDimensionCriterion
import McKayConjecture.CharacterTriple.ProjectiveCrossCharacteristicSplitting
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalSelectedSummandArithmetic
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCrossCharacteristicCoefficients

/-!
# Glauberman obstruction agreement from a reduced normalizer factor

The canonical selected-summand multiplicity is prime to `q`.  Its
dimension therefore annihilates the complex projective obstruction by
an integer coprime to every power of `q`.

Cross-characteristic coefficient reduction isolates the complementary
power-of-`q` annihilator.  If the explicit reduced factor is realized
by a Brauer-normalizer lift, the normalizer extension splits that
reduced factor.  The two coprime annihilators then make the original
canonical factor class vanish, which is exactly the remaining
Proposition-4.5 obstruction agreement.

Thus the only input exposed by this file is operator-level: a modular
normalizer lift whose factor is the already constructed finite-field
reduction.
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

variable {P A : Type}
variable [Group P] [Fintype P]
variable [Ring A]

/-- The concrete finite field used to reduce the factor of the
canonical selected-summand quotient action. -/
abbrev ProductAmbientGlaubermanCanonicalReducedField
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :=
  _root_.Representation.PrimeToCoefficientField q
    (Module.finrank ℂ
      (ProductAmbientGlaubermanCanonicalSelectedSummand
        S C hcentral hgenerate g theta))

/-- A Brauer-normalizer realization of the concrete finite-field
reduction proves the intrinsic projective-obstruction agreement for
one canonical matched Glauberman pair. -/
theorem
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_reducedNormalizerFactor
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (hmultiplicity :
      ProductAmbientGlaubermanNormalRestrictionMultiplicityIsPPrime
        S C hcentral hgenerate g theta)
    [Algebra
      (ProductAmbientGlaubermanCanonicalReducedField
        S C hcentral hgenerate g theta) A]
    [MulSemiringAction P A]
    [SMulCommClass P
      (ProductAmbientGlaubermanCanonicalReducedField
        S C hcentral hgenerate g theta) A]
    (I : _root_.Representation.InteriorAction (P := P) (A := A))
    (T :
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      _root_.Representation.ProjectiveNormalizerLift
        (k := ProductAmbientGlaubermanCanonicalReducedField
          S C hcentral hgenerate g theta)
        (H :=
          productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta)
        I)
    (E :
      _root_.Representation.BrauerNormalizerExtension
        (k := ProductAmbientGlaubermanCanonicalReducedField
          S C hcentral hgenerate g theta)
        I)
    (Z :
      _root_.Representation.BrauerScalarIdentification
        (k := ProductAmbientGlaubermanCanonicalReducedField
          S C hcentral hgenerate g theta)
        (P := P) (A := A))
    (hfactor :
      letI : Nontrivial
          (ProductAmbientGlaubermanCanonicalSelectedSummand
            S C hcentral hgenerate g theta) :=
        productAmbientGlaubermanCanonicalSelectedSummand_nontrivial
          S C hcentral hgenerate g theta hmultiplicity
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      ∀ u v,
        T.factor u v =
          (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
            S C hcentral hgenerate g theta
            ).finiteFactorCrossCharacteristicReduction q u v) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta := by
  let V :=
    ProductAmbientGlaubermanCanonicalSelectedSummand
      S C hcentral hgenerate g theta
  letI : Nontrivial V :=
    productAmbientGlaubermanCanonicalSelectedSummand_nontrivial
      S C hcentral hgenerate g theta hmultiplicity
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let Q :=
    productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
      S C hcentral hgenerate g theta
  have hdegree :
      ¬q ∣ Module.finrank ℂ V := by
    rw [
      productAmbientGlaubermanCanonicalSelectedSummand_finrank
        S C hcentral hgenerate g theta]
    exact hmultiplicity
  have hzero :
      letI :=
        trivialMulDistribMulAction
          (productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta) ℂˣ
      Q.factorSet.h2Class = 0 :=
    Q.factorSet_h2Class_eq_zero_of_crossCharacteristicNormalizerFactor
      q hdegree T E Z hfactor
  exact
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_canonicalSelectedSummand
      S C hcentral hgenerate g theta hzero

/-- Dade-algebra form of the reduced-normalizer theorem.
Brauer-primitivity constructs the scalar identification, so callers
only supply the primitive Dade algebra, its normalizer extension, and
the operator-level reduced-factor equality. -/
theorem
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_reducedDadeFactor
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (hmultiplicity :
      ProductAmbientGlaubermanNormalRestrictionMultiplicityIsPPrime
        S C hcentral hgenerate g theta)
    [Algebra
      (ProductAmbientGlaubermanCanonicalReducedField
        S C hcentral hgenerate g theta) A]
    [MulSemiringAction P A]
    [SMulCommClass P
      (ProductAmbientGlaubermanCanonicalReducedField
        S C hcentral hgenerate g theta) A]
    (D :
      _root_.Representation.DadeAlgebra q
        (ProductAmbientGlaubermanCanonicalReducedField
          S C hcentral hgenerate g theta) P A)
    (hprimitive : D.IsBrauerPrimitive)
    (I : _root_.Representation.InteriorAction (P := P) (A := A))
    (T :
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      _root_.Representation.ProjectiveNormalizerLift
        (k := ProductAmbientGlaubermanCanonicalReducedField
          S C hcentral hgenerate g theta)
        (H :=
          productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta)
        I)
    (E :
      _root_.Representation.BrauerNormalizerExtension
        (k := ProductAmbientGlaubermanCanonicalReducedField
          S C hcentral hgenerate g theta)
        I)
    (hfactor :
      letI : Nontrivial
          (ProductAmbientGlaubermanCanonicalSelectedSummand
            S C hcentral hgenerate g theta) :=
        productAmbientGlaubermanCanonicalSelectedSummand_nontrivial
          S C hcentral hgenerate g theta hmultiplicity
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      ∀ u v,
        T.factor u v =
          (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
            S C hcentral hgenerate g theta
            ).finiteFactorCrossCharacteristicReduction q u v) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta := by
  apply
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_reducedNormalizerFactor
      S C hcentral hgenerate g theta hmultiplicity I T E
      (_root_.Representation.brauerScalarIdentificationOfFinrankOne
        ((D.finrank_brauerQuotientAlgebra_eq_one_iff_isBrauerPrimitive).2
          hprimitive))
  exact hfactor

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
