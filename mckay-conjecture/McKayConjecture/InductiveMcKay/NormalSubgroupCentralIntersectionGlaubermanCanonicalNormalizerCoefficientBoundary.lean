/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.FiniteFieldUnitsComplexEmbedding
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalNormalizerLift

/-!
# Coefficient boundary for the canonical Glauberman normalizer lift

The canonical selected-summand construction supplies a complex
`ProjectiveNormalizerLift` with exactly the desired quotient factor.
For a finite field `k`, a complex scalar can be the image of a modular
scalar under `finiteFieldUnitsToComplexUnits k` exactly when its
`|kˣ|`-th power is one.  The theorems below specialize that exact image
criterion to every value of the canonical quotient factor.

This scalar criterion does not itself construct a modular projective
normalizer lift.  The generic development now supplies a stable integral
lattice, its residue projective representation, and an unconditional
complex character of residue-field units with the required scalar values.
The remaining canonical input is therefore operator-theoretic: construct
the honest residue action normalized by those projective operators,
identify its endomorphism algebra as Brauer-primitive Dade, and extend the
fixed-unit Brauer character to the unit normalizer.
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
variable (k : Type) [Field k] [Finite k]

/-- Exact pointwise criterion for a canonical complex quotient-factor
value to have a unique modular scalar preimage. -/
theorem
    productAmbientGlaubermanCanonicalSelectedSummand_factor_hasUniqueFiniteFieldPreimage_iff
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
    (u v :
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (∃! a : kˣ,
        _root_.Representation.finiteFieldUnitsToComplexUnits k a =
          (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
            S C hcentral hgenerate g theta).factor u v) ↔
      (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
          S C hcentral hgenerate g theta).factor u v ^
        Nat.card kˣ =
      1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    _root_.Representation.existsUnique_finiteFieldUnitsToComplexUnits_eq_iff
      k
      ((productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
        S C hcentral hgenerate g theta).factor u v)

/-- Simultaneous version of the scalar image criterion.  It precisely
separates existence of modular scalar values from the still-absent
modular operator and Dade-algebra realization. -/
theorem
    productAmbientGlaubermanCanonicalSelectedSummand_factor_hasUniqueFiniteFieldPreimages_iff
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
    (∀ u v :
        productAmbientGlaubermanRightOuterQuotient
          S C hcentral hgenerate g theta,
      ∃! a : kˣ,
        _root_.Representation.finiteFieldUnitsToComplexUnits k a =
          (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
            S C hcentral hgenerate g theta).factor u v) ↔
      ∀ u v :
        productAmbientGlaubermanRightOuterQuotient
          S C hcentral hgenerate g theta,
        (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
            S C hcentral hgenerate g theta).factor u v ^
          Nat.card kˣ =
        1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  constructor
  · intro h u v
    exact
      (productAmbientGlaubermanCanonicalSelectedSummand_factor_hasUniqueFiniteFieldPreimage_iff
        S C k hcentral hgenerate g theta u v).1
        (h u v)
  · intro h u v
    exact
      (productAmbientGlaubermanCanonicalSelectedSummand_factor_hasUniqueFiniteFieldPreimage_iff
        S C k hcentral hgenerate g theta u v).2
        (h u v)

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
