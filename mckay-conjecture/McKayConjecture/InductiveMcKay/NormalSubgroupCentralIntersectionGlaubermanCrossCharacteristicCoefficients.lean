/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveCrossCharacteristicCoefficientReduction
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalNormalizerLift

/-!
# Cross-characteristic coefficients for the canonical Glauberman quotient

This file specializes the constructive finite-root coefficient reduction
to the canonical selected-summand quotient action in Proposition 4.5.
Determinant normalization first places its factor in a finite roots-of-unity
group.  The CRT projection then removes exactly the `q`-primary part and
maps the retained factor to a concrete Galois field of characteristic `q`.

Consequently there is no remaining scalar-existence problem.  If a modular
normalizer construction splits the explicitly reduced factor, the original
canonical complex quotient obstruction is `q`-primary.  What remains outside
this file is operator-level: constructing a stable integral lattice whose
reduction realizes that finite-field factor in the required primitive Dade
algebra.
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

/-- The concrete finite-field factor obtained from the
determinant-normalized canonical selected-summand quotient action. -/
def
    productAmbientGlaubermanCanonicalSelectedSummandCrossCharacteristicFactor
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    [Nontrivial
      (ProductAmbientGlaubermanCanonicalSelectedSummand
        S C hcentral hgenerate g theta)] :
    let V :=
      ProductAmbientGlaubermanCanonicalSelectedSummand
        S C hcentral hgenerate g theta
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    FactorSet
      (productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta)
      (_root_.Representation.PrimeToCoefficientField
        q (Module.finrank ℂ V))ˣ := by
  let V :=
    ProductAmbientGlaubermanCanonicalSelectedSummand
      S C hcentral hgenerate g theta
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
      S C hcentral hgenerate g theta
      ).finiteFactorCrossCharacteristicReduction q

/-- Once the explicitly reduced finite-field factor is split after the
chosen complex unit embedding, the original canonical quotient factor
class is `q`-primary. -/
theorem
    canonicalSelectedSummand_factorSet_isQPrimary_of_coefficientReduction
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    [Nontrivial
      (ProductAmbientGlaubermanCanonicalSelectedSummand
        S C hcentral hgenerate g theta)]
    (hreduced :
      let V :=
        ProductAmbientGlaubermanCanonicalSelectedSummand
          S C hcentral hgenerate g theta
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      letI :=
        trivialMulDistribMulAction
          (productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta) ℂˣ
      ((productAmbientGlaubermanCanonicalSelectedSummandCrossCharacteristicFactor
          S C hcentral hgenerate g theta).map
        (_root_.Representation.finiteFieldUnitsToComplexUnits
          (_root_.Representation.PrimeToCoefficientField
            q (Module.finrank ℂ V)))).h2Class =
        0) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ∃ k : ℕ,
      letI :=
        trivialMulDistribMulAction
          (productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta) ℂˣ
      q ^ k •
          (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
            S C hcentral hgenerate g theta).factorSet.h2Class =
        0 := by
  let V :=
    ProductAmbientGlaubermanCanonicalSelectedSummand
      S C hcentral hgenerate g theta
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let Q :=
    productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
      S C hcentral hgenerate g theta
  exact
    Q.exists_pow_nsmul_factorSet_h2Class_eq_zero_of_reduction
      q hreduced

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
