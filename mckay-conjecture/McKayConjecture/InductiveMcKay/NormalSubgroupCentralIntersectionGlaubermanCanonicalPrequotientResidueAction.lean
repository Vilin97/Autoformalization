/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteFieldPGroupScalarNormalization
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalResidueSylowAction

/-!
# The pre-quotient canonical residue action

The corrected selected-summand projective representation is defined on the
full right inertia group before descent to the right outer quotient.  On the
Sylow direct factor of the right normal copy its chosen complex operators
are already the identity.  Determinant normalization and residue reduction
preserve this identity.

This file proves the resulting sharp no-go statement.  Every honest action
obtained by scalar-normalizing that pre-quotient residue restriction is
trivial, independently of the chosen scalar correction.  Consequently such
an action is faithful exactly when the internal Sylow factor is trivial.

Thus passing to pre-quotient operators does not supply the missing faithful
Dade interior action.  That action must come from additional modular data
which is not merely a scalar correction of the canonical selected-summand
restriction.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CharacterTriple.ProjectiveRepresentation
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The canonical selected-summand projective action on the full right
inertia group, after the correction which makes it descend through the
right normal copy. -/
def productAmbientGlaubermanCanonicalCorrectedInertiaProjective
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    ProjectiveRepresentation ℂ
      (ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta)
      (ProductAmbientGlaubermanCanonicalSelectedSummand
        S C hcentral hgenerate g theta) :=
  (productAmbientGlaubermanCanonicalSelectedSummandInertiaProjective
      S C hcentral hgenerate g theta).rescale
    (productAmbientGlaubermanFullInertiaCorrectionCochain
      S C hcentral hgenerate g theta)

/-- Before quotient descent, every corrected operator on the embedded
Sylow factor of the right normal copy is already the identity. -/
theorem
    productAmbientGlaubermanCanonicalCorrectedInertiaProjective_operator_sylow_eq_one
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
    (r : internalNormalizerSylow (productSylow S C)) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (productAmbientGlaubermanCanonicalCorrectedInertiaProjective
        S C hcentral hgenerate g theta).operator
        (productAmbientGlaubermanRightNormalSylowToInertia
          S C hcentral hgenerate g theta r) =
      1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    (productAmbientGlaubermanCanonicalSelectedSummand_isQuotientCompatible
      S C hcentral hgenerate g theta).operator_normal
        (productAmbientGlaubermanRightNormalCopySylowHom
          S C hcentral hgenerate g theta r)

/-- The corrected pre-quotient selected-summand action is normalized. -/
theorem
    productAmbientGlaubermanCanonicalCorrectedInertiaProjective_isNormalized
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
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (productAmbientGlaubermanCanonicalCorrectedInertiaProjective
      S C hcentral hgenerate g theta).IsNormalized := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    (productAmbientGlaubermanCanonicalSelectedSummand_isQuotientCompatible
      S C hcentral hgenerate g theta).isNormalized

variable {ι : Type} [Finite ι]

/-- No faithful honest action can be obtained by scalar-normalizing the
canonical pre-quotient residue restriction unless the internal Sylow factor
is trivial.  The scalar correction is completely arbitrary. -/
theorem
    productAmbientGlaubermanCanonicalPrequotient_onlyTrivialGroupHasFaithfulScalarNormalization
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
    (b :
      Module.Basis ι ℂ
        (ProductAmbientGlaubermanCanonicalSelectedSummand
          S C hcentral hgenerate g theta)) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    OnlyTrivialGroupHasFaithfulResidueScalarNormalization
      (p := q)
      (productAmbientGlaubermanCanonicalCorrectedInertiaProjective
        S C hcentral hgenerate g theta)
      b
      (productAmbientGlaubermanRightNormalSylowToInertia
        S C hcentral hgenerate g theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    onlyTrivialGroupHasFaithfulResidueScalarNormalization_of_operator_eq_one
      (P :=
        productAmbientGlaubermanCanonicalCorrectedInertiaProjective
          S C hcentral hgenerate g theta)
      (b := b)
      (i :=
        productAmbientGlaubermanRightNormalSylowToInertia
          S C hcentral hgenerate g theta)
      (productAmbientGlaubermanCanonicalCorrectedInertiaProjective_isNormalized
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInternalNormalizerSylow_isPGroup S C)
      (productAmbientGlaubermanCanonicalCorrectedInertiaProjective_operator_sylow_eq_one
        S C hcentral hgenerate g theta)

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
