/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveH2Mismatch
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45ProjectiveMismatch

/-!
# Proposition 4.5 via an `H²` equality and a scalar mismatch

For each matched ambient inertia pair in the central-intersection branch,
the projective factor obstruction is an equality in the second cohomology of
the canonically identified outer quotients.  After that equality selects a
factor-matching rescaling, the remaining obstruction is the resulting
character on the full matched centralizer.

This is the intrinsic `H²` formulation of the last projective seam in
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

/-- The exact ambient projective seam stated intrinsically using equality
of quotient factor classes in `H²`. -/
structure ProductAmbientTheorem44ProjectiveH2MismatchData
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
  h2MismatchComparison :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ∀ theta :
        PPrimeIrreducibleCharacter
          (product S C) q,
      H2MismatchProjectiveComparisonData
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

namespace ProductAmbientTheorem44ProjectiveH2MismatchData

/-- The `H²` equality selects the cochain required by the existing
cohomology-mismatch interface. -/
def toProductAmbientTheorem44ProjectiveCohomologyMismatchData
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (d :
      ProductAmbientTheorem44ProjectiveH2MismatchData
        S C hgenerate theorem44Equiv) :
    ProductAmbientTheorem44ProjectiveCohomologyMismatchData
      S C hgenerate theorem44Equiv := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    { characterEquiv_smul := d.characterEquiv_smul
      cohomologyMismatchComparison := fun theta ↦
        (d.h2MismatchComparison theta
          ).toCohomologyMismatchProjectiveComparisonData }

/-- The intrinsic two-obstruction package supplies the complete ambient
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
      ProductAmbientTheorem44ProjectiveH2MismatchData
        S C hgenerate theorem44Equiv) :
    ProductAmbientTheorem44ProjectiveComparisonData
      S C hgenerate theorem44Equiv :=
  (d.toProductAmbientTheorem44ProjectiveCohomologyMismatchData
    S C hgenerate theorem44Equiv
    ).toProductAmbientTheorem44ProjectiveComparisonData
      S C hgenerate theorem44Equiv

end ProductAmbientTheorem44ProjectiveH2MismatchData

open ComplementReduction

/-- `H²`-and-mismatch form for the constructed
Glauberman--Okuyama--Wajima equivalence. -/
abbrev ProductAmbientGlaubermanProjectiveH2MismatchData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral) :=
  ProductAmbientTheorem44ProjectiveH2MismatchData
    S C hgenerate
    (complementCharacterEquivOfGlauberman
      S C hcentral g)

namespace ProductAmbientGlaubermanProjectiveH2MismatchData

/-- The intrinsic obstruction package discharges the original Glauberman
projective-comparison interface. -/
def toProductAmbientGlaubermanProjectiveComparisonData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (d :
      ProductAmbientGlaubermanProjectiveH2MismatchData
        S C hcentral hgenerate g) :
    ProductAmbientGlaubermanProjectiveComparisonData
      S C hcentral hgenerate g :=
  d.toProductAmbientTheorem44ProjectiveComparisonData
    S C hgenerate
    (complementCharacterEquivOfGlauberman
      S C hcentral g)

end ProductAmbientGlaubermanProjectiveH2MismatchData

end Proposition45

/-- The intrinsic two-obstruction statement for the central-intersection
branch: normalizer equivariance, equality of quotient factor classes in
`H²`, and triviality of the post-rescaling full-centralizer mismatch. -/
def CentralScalarCentralIntersectionProjectiveH2MismatchHypothesis
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
          (Proposition45.ProductAmbientGlaubermanProjectiveH2MismatchData
            S C hcentral hgenerate g)

/-- Equality in `H²` and triviality of the scalar mismatch imply the
cohomological projective-comparison hypothesis. -/
theorem centralScalarCentralIntersectionProjectiveCohomologyMismatchHypothesis_of_h2Mismatch
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionProjectiveH2MismatchHypothesis q) :
    CentralScalarCentralIntersectionProjectiveCohomologyMismatchHypothesis
      q := by
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  intro g
  obtain ⟨d⟩ :=
    h X S C hCnormal hcentral hgenerate g
  exact
    ⟨d.toProductAmbientTheorem44ProjectiveCohomologyMismatchData
      S C hgenerate
      (Proposition45.complementCharacterEquivOfGlauberman
        S C hcentral g)⟩

/-- The two intrinsic obstruction claims discharge the full
central-intersection reduction hypothesis. -/
theorem centralScalarCentralIntersectionReductionHypothesis_of_projectiveH2Mismatch
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionProjectiveH2MismatchHypothesis q) :
    CentralScalarCentralIntersectionReductionHypothesis q :=
  centralScalarCentralIntersectionReductionHypothesis_of_projectiveCohomologyMismatch
    (centralScalarCentralIntersectionProjectiveCohomologyMismatchHypothesis_of_h2Mismatch
      h)

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
