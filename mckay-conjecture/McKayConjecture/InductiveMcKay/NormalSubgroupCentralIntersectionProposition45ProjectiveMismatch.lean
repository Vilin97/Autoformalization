/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveCohomologyMismatch
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45ProjectiveComparison

/-!
# Proposition 4.5 via factor matching and a scalar-mismatch character

This file refines the remaining projective-representation seam in the
central-intersection branch.  For each matched pair of ambient inertia
triples it records:

* independently associated projective lifts;
* literal equality of their factor sets along the canonical inertia
  embedding; and
* triviality of the induced scalar-mismatch character on the full matched
  centralizer.

The last clause is deliberately on the full centralizer, not only on the
ambient center of `CP`.  The generic obstruction theorem turns these fields
into the standard complete projective comparison used by Proposition 4.5.
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

/-- The exact ambient projective seam, split into factor agreement and
triviality of the resulting centralizer scalar mismatch. -/
structure ProductAmbientTheorem44ProjectiveMismatchData
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
  factorMatchedComparison :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ∀ theta :
        PPrimeIrreducibleCharacter
          (product S C) q,
      FactorMatchedAssociatedProjectiveComparisonData
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

namespace ProductAmbientTheorem44ProjectiveMismatchData

/-- Factor matching and trivial scalar mismatch construct the standard
ambient projective-comparison package. -/
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
      ProductAmbientTheorem44ProjectiveMismatchData
        S C hgenerate theorem44Equiv) :
    ProductAmbientTheorem44ProjectiveComparisonData
      S C hgenerate theorem44Equiv := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    { characterEquiv_smul := d.characterEquiv_smul
      projectiveComparison := fun theta ↦
        (d.factorMatchedComparison theta
          ).toCompleteCentralProjectiveComparisonData }

end ProductAmbientTheorem44ProjectiveMismatchData

/-- The narrowest obstruction-theoretic ambient seam for Proposition 4.5.
For each inertia pair it asks only for independently associated lifts,
cohomology of their quotient factor sets, and triviality of the scalar
mismatch after the canonical factor-matching rescaling. -/
structure ProductAmbientTheorem44ProjectiveCohomologyMismatchData
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
  cohomologyMismatchComparison :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ∀ theta :
        PPrimeIrreducibleCharacter
          (product S C) q,
      CohomologyMismatchProjectiveComparisonData
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

namespace ProductAmbientTheorem44ProjectiveCohomologyMismatchData

/-- The quotient cohomology and post-rescaling mismatch claims give the
factor-matched obstruction package. -/
def toProductAmbientTheorem44ProjectiveMismatchData
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (d :
      ProductAmbientTheorem44ProjectiveCohomologyMismatchData
        S C hgenerate theorem44Equiv) :
    ProductAmbientTheorem44ProjectiveMismatchData
      S C hgenerate theorem44Equiv := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    { characterEquiv_smul := d.characterEquiv_smul
      factorMatchedComparison := fun theta ↦
        (d.cohomologyMismatchComparison theta
          ).toFactorMatchedAssociatedProjectiveComparisonData }

/-- The two obstruction claims discharge the original ambient projective
comparison interface. -/
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
      ProductAmbientTheorem44ProjectiveCohomologyMismatchData
        S C hgenerate theorem44Equiv) :
    ProductAmbientTheorem44ProjectiveComparisonData
      S C hgenerate theorem44Equiv :=
  (d.toProductAmbientTheorem44ProjectiveMismatchData
    S C hgenerate theorem44Equiv
    ).toProductAmbientTheorem44ProjectiveComparisonData
      S C hgenerate theorem44Equiv

end ProductAmbientTheorem44ProjectiveCohomologyMismatchData

open ComplementReduction

/-- Mismatch-character form of the remaining projective data for the
constructed Glauberman--Okuyama--Wajima equivalence. -/
abbrev ProductAmbientGlaubermanProjectiveMismatchData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral) :=
  ProductAmbientTheorem44ProjectiveMismatchData
    S C hgenerate
    (complementCharacterEquivOfGlauberman
      S C hcentral g)

namespace ProductAmbientGlaubermanProjectiveMismatchData

/-- The mismatch-character form discharges the original projective
comparison interface. -/
def toProductAmbientGlaubermanProjectiveComparisonData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (d :
      ProductAmbientGlaubermanProjectiveMismatchData
        S C hcentral hgenerate g) :
    ProductAmbientGlaubermanProjectiveComparisonData
      S C hcentral hgenerate g :=
  d.toProductAmbientTheorem44ProjectiveComparisonData
    S C hgenerate
    (complementCharacterEquivOfGlauberman
      S C hcentral g)

end ProductAmbientGlaubermanProjectiveMismatchData

/-- Cohomological-obstruction form of the remaining projective data for the
constructed Glauberman--Okuyama--Wajima equivalence. -/
abbrev ProductAmbientGlaubermanProjectiveCohomologyMismatchData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral) :=
  ProductAmbientTheorem44ProjectiveCohomologyMismatchData
    S C hgenerate
    (complementCharacterEquivOfGlauberman
      S C hcentral g)

namespace ProductAmbientGlaubermanProjectiveCohomologyMismatchData

/-- Quotient factor cohomology and trivial post-rescaling mismatch discharge
the original Glauberman projective-comparison interface. -/
def toProductAmbientGlaubermanProjectiveComparisonData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (d :
      ProductAmbientGlaubermanProjectiveCohomologyMismatchData
        S C hcentral hgenerate g) :
    ProductAmbientGlaubermanProjectiveComparisonData
      S C hcentral hgenerate g :=
  d.toProductAmbientTheorem44ProjectiveComparisonData
    S C hgenerate
    (complementCharacterEquivOfGlauberman
      S C hcentral g)

end ProductAmbientGlaubermanProjectiveCohomologyMismatchData

end Proposition45

/-- The exact two-obstruction statement still required in the
central-intersection branch: equivariance of the constructed character
equivalence, quotient-factor cohomology for every matched inertia pair, and
triviality of the post-rescaling full-centralizer scalar mismatch. -/
def CentralScalarCentralIntersectionProjectiveCohomologyMismatchHypothesis
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
          (Proposition45.ProductAmbientGlaubermanProjectiveCohomologyMismatchData
            S C hcentral hgenerate g)

/-- The two obstruction claims imply the original projective-comparison
hypothesis for Proposition 4.5. -/
theorem centralScalarCentralIntersectionProjectiveComparisonHypothesis_of_cohomologyMismatch
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionProjectiveCohomologyMismatchHypothesis
        q) :
    CentralScalarCentralIntersectionProjectiveComparisonHypothesis q := by
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  intro g
  obtain ⟨d⟩ :=
    h X S C hCnormal hcentral hgenerate g
  exact
    ⟨d.toProductAmbientGlaubermanProjectiveComparisonData
      S C hcentral hgenerate g⟩

/-- The two obstruction claims therefore discharge the full
central-intersection reduction hypothesis. -/
theorem centralScalarCentralIntersectionReductionHypothesis_of_projectiveCohomologyMismatch
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionProjectiveCohomologyMismatchHypothesis
        q) :
    CentralScalarCentralIntersectionReductionHypothesis q :=
  centralScalarCentralIntersectionReductionHypothesis_of_projectiveComparisons
    (centralScalarCentralIntersectionProjectiveComparisonHypothesis_of_cohomologyMismatch
      h)

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
