/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveH2NormalCentralMismatch
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45H2Mismatch

/-!
# Proposition 4.5 after quotienting the scalar obstruction

This file specializes the intrinsic projective obstruction package to the
matched inertia triples in the central-intersection branch.  In addition to
normalizer equivariance, it asks for:

* equality of the two outer-quotient factor classes in `H²`;
* equality of normalized values on the matched normal-central subgroup; and
* triviality of the remaining scalar character on the corresponding
  centralizer quotient.

These premises imply the complete projective comparison used by
Proposition 4.5.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The ambient Proposition-4.5 seam after both the factor obstruction and
the normal-central part of the scalar obstruction have been isolated. -/
structure ProductAmbientTheorem44ProjectiveH2NormalCentralMismatchData
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q) where
  characterEquiv_smul :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ∀ (h : ambientNormalizer S)
      (theta :
        PPrimeIrreducibleCharacter
          (product S C) q),
      internalTheorem44CharacterEquiv
          S C theorem44Equiv (h • theta) =
        h • internalTheorem44CharacterEquiv
          S C theorem44Equiv theta
  h2NormalCentralMismatchComparison :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ∀ theta :
        PPrimeIrreducibleCharacter
          (product S C) q,
      H2NormalCentralMismatchProjectiveComparisonData
        (ofInertia (product S C) theta.1)
        (ofInertia
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C theorem44Equiv theta).1)
        (MatchedInertiaRestriction.embedding
          (product S C)
          (ambientNormalizer S)
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C theorem44Equiv)
          characterEquiv_smul theta)
        (productAmbientInertiaRestrictionGroupData
          S C hgenerate theorem44Equiv
          characterEquiv_smul theta)

namespace ProductAmbientTheorem44ProjectiveH2NormalCentralMismatchData

/-- Quotienting the scalar mismatch supplies the full `H²`-mismatch
interface. -/
def toProductAmbientTheorem44ProjectiveH2MismatchData
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (d :
      ProductAmbientTheorem44ProjectiveH2NormalCentralMismatchData
        S C hgenerate theorem44Equiv) :
    ProductAmbientTheorem44ProjectiveH2MismatchData
      S C hgenerate theorem44Equiv := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    { characterEquiv_smul := d.characterEquiv_smul
      h2MismatchComparison := fun theta ↦
        (d.h2NormalCentralMismatchComparison theta
          ).toH2MismatchProjectiveComparisonData }

/-- The refined obstruction package supplies the original complete ambient
projective comparison. -/
def toProductAmbientTheorem44ProjectiveComparisonData
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (d :
      ProductAmbientTheorem44ProjectiveH2NormalCentralMismatchData
        S C hgenerate theorem44Equiv) :
    ProductAmbientTheorem44ProjectiveComparisonData
      S C hgenerate theorem44Equiv :=
  (d.toProductAmbientTheorem44ProjectiveH2MismatchData
    S C hgenerate theorem44Equiv
    ).toProductAmbientTheorem44ProjectiveComparisonData
      S C hgenerate theorem44Equiv

end ProductAmbientTheorem44ProjectiveH2NormalCentralMismatchData

open ComplementReduction

/-- Refined obstruction data for the concrete
Glauberman--Okuyama--Wajima equivalence. -/
abbrev ProductAmbientGlaubermanProjectiveH2NormalCentralMismatchData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral) :=
  ProductAmbientTheorem44ProjectiveH2NormalCentralMismatchData
    S C hgenerate
    (complementCharacterEquivOfGlauberman
      S C hcentral g)

namespace ProductAmbientGlaubermanProjectiveH2NormalCentralMismatchData

/-- The refined obstruction data discharge the original Glauberman
projective-comparison interface. -/
def toProductAmbientGlaubermanProjectiveComparisonData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (d :
      ProductAmbientGlaubermanProjectiveH2NormalCentralMismatchData
        S C hcentral hgenerate g) :
    ProductAmbientGlaubermanProjectiveComparisonData
      S C hcentral hgenerate g :=
  d.toProductAmbientTheorem44ProjectiveComparisonData
    S C hgenerate
    (complementCharacterEquivOfGlauberman
      S C hcentral g)

end ProductAmbientGlaubermanProjectiveH2NormalCentralMismatchData

end Proposition45

/-- The exact refined obstruction statement in the central-intersection
branch. -/
def CentralScalarCentralIntersectionProjectiveH2NormalCentralMismatchHypothesis
    (q : ℕ) [Fact q.Prime] : Prop :=
  ∀ (X : Type) [Group X] [Finite X]
    (S : Sylow q X) (C : Subgroup X)
    (hCnormal : C.Normal)
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤),
      letI : C.Normal := hCnormal
      ∀ g :
          ComplementReduction.ProductGlaubermanCorrespondence
            S C hcentral,
        Nonempty
          (Proposition45.ProductAmbientGlaubermanProjectiveH2NormalCentralMismatchData
            S C hcentral hgenerate g)

/-- The refined obstruction statement implies the intrinsic `H²`
formulation. -/
theorem centralScalarCentralIntersectionProjectiveH2MismatchHypothesis_of_h2NormalCentralMismatch
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionProjectiveH2NormalCentralMismatchHypothesis
        q) :
    CentralScalarCentralIntersectionProjectiveH2MismatchHypothesis q := by
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  intro g
  obtain ⟨d⟩ :=
    h X S C hCnormal hcentral hgenerate g
  exact
    ⟨d.toProductAmbientTheorem44ProjectiveH2MismatchData
      S C hgenerate
      (Proposition45.complementCharacterEquivOfGlauberman
        S C hcentral g)⟩

/-- Equality of factor classes and triviality of the residual quotient
character discharge the full central-intersection reduction. -/
theorem centralScalarCentralIntersectionReductionHypothesis_of_projectiveH2NormalCentralMismatch
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionProjectiveH2NormalCentralMismatchHypothesis
        q) :
    CentralScalarCentralIntersectionReductionHypothesis q :=
  centralScalarCentralIntersectionReductionHypothesis_of_projectiveH2Mismatch
    (centralScalarCentralIntersectionProjectiveH2MismatchHypothesis_of_h2NormalCentralMismatch
      h)

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
