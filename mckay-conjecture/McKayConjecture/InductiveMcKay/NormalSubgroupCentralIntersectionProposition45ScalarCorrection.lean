/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveScalarCorrection
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizerAssemblyNaturality
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45ProjectiveComparison

/-!
# Proposition 4.5 from scalar-correction characters

For the concrete Glauberman--Okuyama--Wajima correspondence, ambient
normalizer equivariance is already a theorem.  The remaining DGN-style
projective input can be stated as follows for every matched inertia pair:

* the intrinsic quotient factor classes agree in `H²`; and
* after matching those factors, the scalar mismatch extends to the right
  inertia group and is trivial on its distinguished normal subgroup.

The extending character is then used to rescale the right projective lift.
This is strictly more flexible than demanding that the mismatch of an
arbitrary initial choice already be trivial.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open GroupTheory
open ComplementReduction

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The projective correction input for all matched inertia pairs in the
concrete Proposition-4.5 construction. -/
structure ProductAmbientGlaubermanProjectiveScalarCorrectionData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral) where
  comparison :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ∀ theta :
        PPrimeIrreducibleCharacter
          (product S C) q,
      H2ScalarCorrectableProjectiveComparisonData
        (ofInertia (product S C) theta.1)
        (ofInertia
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C
            (complementCharacterEquivOfGlauberman
              S C hcentral g) theta).1)
        (MatchedInertiaRestriction.embedding
          (product S C)
          (ambientNormalizer S)
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C
            (complementCharacterEquivOfGlauberman
              S C hcentral g))
          (complementCharacterEquivOfGlauberman_internal_smul
            S C hcentral hgenerate g)
          theta)
        (productAmbientInertiaRestrictionGroupData
          S C hgenerate
          (complementCharacterEquivOfGlauberman
            S C hcentral g)
          (complementCharacterEquivOfGlauberman_internal_smul
            S C hcentral hgenerate g)
          theta)

namespace ProductAmbientGlaubermanProjectiveScalarCorrectionData

/-- Scalar-correctable projective lifts provide the complete projective
comparison package, with equivariance supplied by the proved covariance
theorem. -/
def toProductAmbientGlaubermanProjectiveComparisonData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (d :
      ProductAmbientGlaubermanProjectiveScalarCorrectionData
        S C hcentral hgenerate g) :
    ProductAmbientGlaubermanProjectiveComparisonData
      S C hcentral hgenerate g := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    { characterEquiv_smul :=
        complementCharacterEquivOfGlauberman_internal_smul
          S C hcentral hgenerate g
      projectiveComparison := fun theta ↦
        (d.comparison theta
          ).toCompleteCentralProjectiveComparisonData }

end ProductAmbientGlaubermanProjectiveScalarCorrectionData

end Proposition45

/-- Global DGN-style scalar-correction statement for the
central-intersection branch. -/
def CentralScalarCentralIntersectionProjectiveScalarCorrectionHypothesis
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
          (Proposition45.ProductAmbientGlaubermanProjectiveScalarCorrectionData
            S C hcentral hgenerate g)

/-- Extending and applying the post-factor scalar correction discharges the
complete projective-comparison hypothesis. -/
theorem centralScalarCentralIntersectionProjectiveComparisonHypothesis_of_scalarCorrection
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionProjectiveScalarCorrectionHypothesis
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

/-- The scalar-correction formulation supplies the complete
central-intersection reduction. -/
theorem centralScalarCentralIntersectionReductionHypothesis_of_scalarCorrection
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionProjectiveScalarCorrectionHypothesis
        q) :
    CentralScalarCentralIntersectionReductionHypothesis q :=
  centralScalarCentralIntersectionReductionHypothesis_of_projectiveComparisons
    (centralScalarCentralIntersectionProjectiveComparisonHypothesis_of_scalarCorrection
      h)

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
