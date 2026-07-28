/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveMappedCrossCharacteristicSplitting
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalSelectedSummandArithmetic
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCrossCharacteristicNormalizerAgreement

/-!
# Glauberman obstruction agreement from a mapped reduced Dade factor

The modular Dade algebra and its normalizer lift may be constructed over an
arbitrary residue field of characteristic `q`.  There is no need to extend
the algebra to the project's explicit Galois field: a unit homomorphism into
that field and pointwise equality of the mapped factors already split the
retained cross-characteristic obstruction.
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

variable {k P A : Type}
variable [Field k] [CharP k q]
variable [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- A primitive Dade normalizer over any characteristic-`q` field proves
the canonical projective-obstruction agreement when its factor maps to the
explicit cross-characteristic reduction. -/
theorem
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_mappedReducedDadeFactor
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
    (D : _root_.Representation.DadeAlgebra q k P A)
    (hprimitive : D.IsBrauerPrimitive)
    (I : _root_.Representation.InteriorAction (P := P) (A := A))
    (T :
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      _root_.Representation.ProjectiveNormalizerLift
        (k := k)
        (H :=
          productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta)
        I)
    (E : _root_.Representation.BrauerNormalizerExtension (k := k) I)
    (ι :
      kˣ →*
        (ProductAmbientGlaubermanCanonicalReducedField
          S C hcentral hgenerate g theta)ˣ)
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
        ι (T.factor u v) =
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
    Q.factorSet_h2Class_eq_zero_of_mappedCrossCharacteristicDadeFactor
      q hdegree D hprimitive I T E ι hfactor
  exact
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_canonicalSelectedSummand
      S C hcentral hgenerate g theta hzero

/-- Proposition-valued normalizer-extension form of the mapped reduced
Dade-factor theorem. -/
theorem
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_mappedReducedDadeHasExtension
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
    (D : _root_.Representation.DadeAlgebra q k P A)
    (hprimitive : D.IsBrauerPrimitive)
    (I : _root_.Representation.InteriorAction (P := P) (A := A))
    (T :
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      _root_.Representation.ProjectiveNormalizerLift
        (k := k)
        (H :=
          productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta)
        I)
    (hE : _root_.Representation.HasBrauerNormalizerExtension (k := k) I)
    (ι :
      kˣ →*
        (ProductAmbientGlaubermanCanonicalReducedField
          S C hcentral hgenerate g theta)ˣ)
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
        ι (T.factor u v) =
          (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
            S C hcentral hgenerate g theta
            ).finiteFactorCrossCharacteristicReduction q u v) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta :=
  productAmbientGlaubermanProjectiveObstructionClassAgreement_of_mappedReducedDadeFactor
    S C hcentral hgenerate g theta hmultiplicity
    D hprimitive I T (Classical.choice hE) ι hfactor

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
