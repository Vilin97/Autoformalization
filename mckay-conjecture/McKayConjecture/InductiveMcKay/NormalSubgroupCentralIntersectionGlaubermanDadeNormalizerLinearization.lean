/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.FiniteFieldUnitsComplexEmbedding
import McKayConjecture.CharacterTriple.MagicLinearizationFromMappedNormalizer
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalNormalizerLift
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanMagicLinearization

/-!
# Dade-normalizer input for the canonical Glauberman summand

This file connects the modular Brauer-normalizer construction directly
to the canonical selected-summand path in Proposition 4.5.

The preceding canonical-normalizer file proves automatically that the
canonical quotient projective action is normalized and packages its
complex operators as a projective lift in the normalizer of the actual
Sylow action on the invariant summand.

Here, let `T` instead be a modular projective lift into the interior normalizer of a
Brauer-primitive Dade algebra over a field `k` of characteristic `q`.
The normalizer extension produces a scalar cochain in `kˣ`.  If a unit
homomorphism `kˣ → ℂˣ` identifies the factor of `T` with the factor of
the canonical complex selected-summand action, the mapped cochain
magic-linearizes that action.  The existing selected-summand theorem
then gives the required projective-obstruction agreement.

This formulation exposes the remaining cross-characteristic theorem:
an integral modular model must reduce the canonical complex lift to
`T`, including its projective multiplication scalars.  It does not hide
that comparison inside a new magic-linearization hypothesis.
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
variable [CommGroup P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- A mapped Brauer-normalizer factor for a Brauer-primitive abelian
Dade algebra supplies the Proposition-4.5 obstruction agreement on the
canonical selected summand. -/
theorem
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_mappedDadeNormalizer
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
    (ι : kˣ →* ℂˣ)
    (factor_compatibility :
      letI : Nontrivial
          (ProductAmbientGlaubermanKernelSylowScalarSubspace
            S C hcentral hgenerate g theta
            (productAmbientGlaubermanCanonicalSelectedSylowScalar
              S C hcentral hgenerate g theta)) :=
        productAmbientGlaubermanCanonicalSelectedSummand_nontrivial
          S C hcentral hgenerate g theta hmultiplicity
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      ∀ u v,
        ι (T.factor u v) =
          (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
            S C hcentral hgenerate g theta).factor u v) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta := by
  letI : Nontrivial
      (ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta)) :=
    productAmbientGlaubermanCanonicalSelectedSummand_nontrivial
      S C hcentral hgenerate g theta hmultiplicity
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let Q :=
    productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
      S C hcentral hgenerate g theta
  have hQ : Q.IsNormalized :=
    productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective_isNormalized
      S C hcentral hgenerate g theta
  have hmagic :
      ProjectiveRepresentation.MagicLinearization Q :=
    ProjectiveRepresentation.magicLinearizationOfMappedPrimitiveDadeNormalizer
      Q hQ D hprimitive I T E ι factor_compatibility
  exact
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_magicLinearization
      S C hcentral hgenerate g theta hmultiplicity hmagic

/-- Proposition-valued version: existence of a Brauer-normalizer
extension is enough; no choice of extension data is exposed to the
caller. -/
theorem
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_mappedDadeHasNormalizerExtension
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
    (ι : kˣ →* ℂˣ)
    (factor_compatibility :
      letI : Nontrivial
          (ProductAmbientGlaubermanKernelSylowScalarSubspace
            S C hcentral hgenerate g theta
            (productAmbientGlaubermanCanonicalSelectedSylowScalar
              S C hcentral hgenerate g theta)) :=
        productAmbientGlaubermanCanonicalSelectedSummand_nontrivial
          S C hcentral hgenerate g theta hmultiplicity
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      ∀ u v,
        ι (T.factor u v) =
          (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
            S C hcentral hgenerate g theta).factor u v) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta :=
  productAmbientGlaubermanProjectiveObstructionClassAgreement_of_mappedDadeNormalizer
    S C hcentral hgenerate g theta hmultiplicity
      D hprimitive I T (Classical.choice hE)
      ι factor_compatibility

/-- Finite-field specialization using the canonical chosen embedding
`kˣ →* ℂˣ`.  After this specialization, the sole coefficient-change
obligation is the pointwise comparison between the modular
normalizer-lift factor and the canonical complex selected-summand
factor. -/
theorem
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_finiteFieldDadeNormalizer
    [Finite k]
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
    (factor_compatibility :
      letI : Nontrivial
          (ProductAmbientGlaubermanKernelSylowScalarSubspace
            S C hcentral hgenerate g theta
            (productAmbientGlaubermanCanonicalSelectedSylowScalar
              S C hcentral hgenerate g theta)) :=
        productAmbientGlaubermanCanonicalSelectedSummand_nontrivial
          S C hcentral hgenerate g theta hmultiplicity
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      ∀ u v,
        _root_.Representation.finiteFieldUnitsToComplexUnits k
            (T.factor u v) =
          (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
            S C hcentral hgenerate g theta).factor u v) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta :=
  productAmbientGlaubermanProjectiveObstructionClassAgreement_of_mappedDadeHasNormalizerExtension
    S C hcentral hgenerate g theta hmultiplicity
      D hprimitive I T hE
      (_root_.Representation.finiteFieldUnitsToComplexUnits k)
      factor_compatibility

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
