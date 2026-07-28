/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCorrespondenceUniqueness
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCrossCharacteristicNormalizerAgreement

/-!
# Global reduced Dade-factor input

The cross-characteristic normalizer theorem reduces the remaining
Dade--Glauberman--Nagao comparison to concrete data attached to each canonical
matched pair.  This file packages exactly that data: a prime-to-`q`
multiplicity, a primitive Dade algebra, a Brauer-normalizer extension, and
pointwise equality with the explicit reduced factor.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open ComplementReduction
open GroupTheory

/-- A finite group and interior algebra over a coefficient field, packaged
with the instances required by the Dade-normalizer construction. -/
structure ReducedDadeAlgebraModel (k : Type) [CommSemiring k] where
  /-- The group acting on the interior algebra. -/
  P : Type
  /-- The interior algebra. -/
  A : Type
  [groupP : Group P]
  [fintypeP : Fintype P]
  [ringA : Ring A]
  [algebraA : Algebra k A]
  [actionA : MulSemiringAction P A]
  [smulCommA : SMulCommClass P k A]

attribute [instance]
  ReducedDadeAlgebraModel.groupP
  ReducedDadeAlgebraModel.fintypeP
  ReducedDadeAlgebraModel.ringA
  ReducedDadeAlgebraModel.algebraA
  ReducedDadeAlgebraModel.actionA
  ReducedDadeAlgebraModel.smulCommA

/-- Primitive Dade-algebra and interior-action data, independent of any
particular character triple. -/
structure PrimitiveDadeInteriorData
    (q : ℕ) (k : Type)
    [Fact q.Prime] [Field k] [CharP k q]
    (M : ReducedDadeAlgebraModel k) where
  /-- The Dade algebra. -/
  dade : _root_.Representation.DadeAlgebra q k M.P M.A
  /-- Its Brauer quotient is one-dimensional. -/
  primitive : dade.IsBrauerPrimitive
  /-- The interior action used by the normalizer construction. -/
  interior :
    _root_.Representation.InteriorAction (P := M.P) (A := M.A)

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The operator-level equality left after reducing the canonical complex
factor to the explicit residue field. -/
def ProductAmbientGlaubermanReducedFactorMatches
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
    (M :
      ReducedDadeAlgebraModel
        (ProductAmbientGlaubermanCanonicalReducedField
          S C hcentral hgenerate g theta))
    (d :
      PrimitiveDadeInteriorData q
        (ProductAmbientGlaubermanCanonicalReducedField
          S C hcentral hgenerate g theta) M)
    (T :
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      _root_.Representation.ProjectiveNormalizerLift
        (k :=
          ProductAmbientGlaubermanCanonicalReducedField
            S C hcentral hgenerate g theta)
        (H :=
          productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta)
        d.interior) : Prop :=
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
        ).finiteFactorCrossCharacteristicReduction q u v

/-- Existence of all reduced Dade-factor data for one canonical matched pair. -/
def ProductAmbientGlaubermanHasReducedDadeFactor
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) : Prop :=
  ∃ hmultiplicity :
      ProductAmbientGlaubermanNormalRestrictionMultiplicityIsPPrime
        S C hcentral hgenerate g theta,
    ∃ M :
        ReducedDadeAlgebraModel
          (ProductAmbientGlaubermanCanonicalReducedField
            S C hcentral hgenerate g theta),
      ∃ d :
          PrimitiveDadeInteriorData q
            (ProductAmbientGlaubermanCanonicalReducedField
              S C hcentral hgenerate g theta) M,
        ∃ T :
            letI : (internalProductNormalizer S C).Normal :=
              internalProductNormalizer_normal S C hgenerate
            _root_.Representation.ProjectiveNormalizerLift
              (k :=
                ProductAmbientGlaubermanCanonicalReducedField
                  S C hcentral hgenerate g theta)
              (H :=
                productAmbientGlaubermanRightOuterQuotient
                  S C hcentral hgenerate g theta)
              d.interior,
          _root_.Representation.HasBrauerNormalizerExtension
                (k :=
                  ProductAmbientGlaubermanCanonicalReducedField
                    S C hcentral hgenerate g theta)
                d.interior ∧
            ProductAmbientGlaubermanReducedFactorMatches
              S C hcentral hgenerate g theta
              hmultiplicity M d T

/-- A reduced Dade-factor witness proves obstruction agreement for its matched
pair. -/
theorem
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_hasReducedDadeFactor
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (h :
      ProductAmbientGlaubermanHasReducedDadeFactor
        S C hcentral hgenerate g theta) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta := by
  obtain ⟨hmultiplicity, M, d, T, hE, hfactor⟩ := h
  exact
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_reducedDadeFactor
      S C hcentral hgenerate g theta hmultiplicity
      d.dade d.primitive d.interior T (Classical.choice hE) hfactor

end Proposition45

open Proposition45

/-- The remaining global DGN input, expressed as reduced Dade-factor
realizations for the canonical correspondence. -/
def ProductAmbientGlaubermanReducedDadeFactorHypothesis
    (q : ℕ) [Fact q.Prime] : Prop :=
  ∀ (X : Type) [Group X] [Finite X]
    (S : Sylow q X) (C : Subgroup X)
    (hCnormal : C.Normal)
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤),
      letI : C.Normal := hCnormal
      ∀ theta :
          PPrimeIrreducibleCharacter (product S C) q,
        ProductAmbientGlaubermanHasReducedDadeFactor
          S C hcentral hgenerate
          (canonicalProductGlaubermanCorrespondence
            S C hcentral)
          theta

/-- Canonical reduced Dade-factor realizations imply the global intrinsic
projective-obstruction agreement. -/
theorem
    productAmbientGlaubermanProjectiveObstructionClassAgreementHypothesis_of_reducedDadeFactor
    {q : ℕ} [Fact q.Prime]
    (h : ProductAmbientGlaubermanReducedDadeFactorHypothesis q) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreementHypothesis
      q := by
  apply
    productAmbientGlaubermanProjectiveObstructionClassAgreementHypothesis_of_canonical
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  intro theta
  exact
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_hasReducedDadeFactor
      S C hcentral hgenerate
      (canonicalProductGlaubermanCorrespondence S C hcentral)
      theta
      (h X S C hCnormal hcentral hgenerate theta)

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
