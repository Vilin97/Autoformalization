/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleLiftedFactorCorrespondence
import
  McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45IntrinsicObstructions

/-!
# Proposition 4.5 from a lifted factor-extension correspondence

For each concrete Glauberman--Okuyama--Wajima inertia pair, fix the canonical
left associated projective representation and its canonical
association-preserving finite-factor normalization.  This produces an honest
irreducible character on the corresponding factor-set central extension.

The remaining Dade--Glauberman--Nagao input in this file is stated only as an
ordinary-character image on the pulled-back right factor extension:

* the coefficient subgroup has its defining scalar character;
* restriction along the lifted right normal subgroup is the matched right
  character; and
* normalized character values agree at the matched centralizer base lifts.

The generic factor-extension bridge turns this image into the complete
projective comparison for that inertia pair.  Requiring such an image for
every `theta` therefore implies the existing Proposition-4.5 projective
comparison hypothesis and the global central-intersection reduction
hypothesis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CharacterTriple.AssociatedProjectiveRepresentation
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The fixed finite-factor normalization used for the left member of one
concrete Proposition-4.5 inertia pair. -/
abbrev productAmbientGlaubermanLeftFiniteFactorNormalization
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  (productAmbientGlaubermanLeftAssociated
    S C hgenerate theta).finiteFactorNormalization

/-- The exact honest lifted-DGN image required for one concrete inertia
pair.

This is `LiftedFactorCorrespondence.ImageData` specialized to the canonical
left associated lift, its fixed finite-factor normalization, the canonical
right inertia triple, and the canonical inertia embedding. -/
abbrev ProductAmbientGlaubermanLiftedDGNImageData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  LiftedFactorCorrespondence.ImageData
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta)
    (productAmbientGlaubermanLeftFiniteFactorNormalization
      S C hgenerate theta)
    (productAmbientGlaubermanInertiaRestrictionGroupData
      S C hcentral hgenerate g theta)

/-- One honest lifted-DGN image produces the complete projective comparison
for its concrete inertia pair. -/
def completeProjectiveComparisonOfLiftedDGNImage
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (d :
      ProductAmbientGlaubermanLiftedDGNImageData
        S C hcentral hgenerate g theta) :
    CompleteCentralProjectiveComparisonData
      (productAmbientGlaubermanLeftInertiaTriple
        S C hgenerate theta)
      (productAmbientGlaubermanRightInertiaTriple
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInertiaEmbedding
        S C hcentral hgenerate g theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    d.toCompleteCentralProjectiveComparisonData
      (productAmbientGlaubermanLeftAssociated
        S C hgenerate theta)
      (productAmbientGlaubermanLeftFiniteFactorNormalization
        S C hgenerate theta)
      (productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta)

/-- Honest lifted-DGN image data for every character in the concrete
Proposition-4.5 family. -/
structure ProductAmbientGlaubermanLiftedDGNData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral) where
  imageData :
    ∀ theta :
        PPrimeIrreducibleCharacter
          (product S C) q,
      ProductAmbientGlaubermanLiftedDGNImageData
        S C hcentral hgenerate g theta

namespace ProductAmbientGlaubermanLiftedDGNData

/-- Every-theta honest lifted-DGN images give the general
Theorem-4.4 projective-comparison package for the concrete character
equivalence. -/
def toProductAmbientTheorem44ProjectiveComparisonData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (d :
      ProductAmbientGlaubermanLiftedDGNData
        S C hcentral hgenerate g) :
    ProductAmbientTheorem44ProjectiveComparisonData
      S C hgenerate
      (complementCharacterEquivOfGlauberman
        S C hcentral g) := by
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
        completeProjectiveComparisonOfLiftedDGNImage
          S C hcentral hgenerate g theta
          (d.imageData theta) }

/-- Every-theta honest lifted-DGN images give the existing concrete
Proposition-4.5 projective-comparison package. -/
def toProductAmbientGlaubermanProjectiveComparisonData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (d :
      ProductAmbientGlaubermanLiftedDGNData
        S C hcentral hgenerate g) :
    ProductAmbientGlaubermanProjectiveComparisonData
      S C hcentral hgenerate g :=
  d.toProductAmbientTheorem44ProjectiveComparisonData
    S C hcentral hgenerate g

end ProductAmbientGlaubermanLiftedDGNData
end Proposition45

/-- The global central-intersection premise stated solely as existence of
honest lifted-DGN image characters for every concrete matched inertia pair.
-/
def CentralScalarCentralIntersectionLiftedDGNImageHypothesis
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
          (Proposition45.ProductAmbientGlaubermanLiftedDGNData
            S C hcentral hgenerate g)

/-- The ordinary-character lifted-DGN hypothesis implies the existing
global projective-comparison hypothesis. -/
theorem centralScalarCentralIntersectionProjectiveComparisonHypothesis_of_liftedDGNImages
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionLiftedDGNImageHypothesis q) :
    CentralScalarCentralIntersectionProjectiveComparisonHypothesis q := by
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  intro g
  obtain ⟨d⟩ :=
    h X S C hCnormal hcentral hgenerate g
  exact
    ⟨d.toProductAmbientGlaubermanProjectiveComparisonData
      S C hcentral hgenerate g⟩

/-- Honest lifted-DGN image characters for all concrete inertia pairs
discharge the complete central-intersection reduction hypothesis. -/
theorem centralScalarCentralIntersectionReductionHypothesis_of_liftedDGNImages
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionLiftedDGNImageHypothesis q) :
    CentralScalarCentralIntersectionReductionHypothesis q :=
  centralScalarCentralIntersectionReductionHypothesis_of_projectiveComparisons
    (centralScalarCentralIntersectionProjectiveComparisonHypothesis_of_liftedDGNImages
      h)

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
