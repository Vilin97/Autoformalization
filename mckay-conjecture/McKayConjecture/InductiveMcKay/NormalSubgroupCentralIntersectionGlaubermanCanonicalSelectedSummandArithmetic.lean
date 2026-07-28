/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalSelectedSummandAgreement

/-!
# Arithmetic of the canonical Glauberman summand

The canonical selected summand is linearly equivalent to the final
normal-restriction multiplicity space.  Its dimension is therefore the
ordinary restriction multiplicity in Proposition 4.5.  In particular, a
prime-to-`q` canonical-extension multiplicity makes the selected summand
nonzero automatically.

This file keeps that elementary dimension argument separate from the
remaining Dade input, namely the prime-to-`q` canonical-extension
multiplicity and the vanishing of the descended factor class.
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

/-- The dimension of the canonical selected summand is exactly the
ordinary matched-normal restriction multiplicity. -/
theorem productAmbientGlaubermanCanonicalSelectedSummand_finrank
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    Module.finrank ℂ
        (ProductAmbientGlaubermanKernelSylowScalarSubspace
          S C hcentral hgenerate g theta
          (productAmbientGlaubermanCanonicalSelectedSylowScalar
            S C hcentral hgenerate g theta)) =
      productAmbientGlaubermanNormalRestrictionMultiplicity
        S C hcentral hgenerate g theta := by
  rw [
    productAmbientGlaubermanCanonicalSelectedSummand_finrank_eq_mismatch
      S C hcentral hgenerate g theta,
    productAmbientGlaubermanMultiplicityMismatch_finrank
      S C hcentral hgenerate g theta]

/-- A prime-to-`q` canonical selected multiplicity is positive. -/
theorem productAmbientGlaubermanCanonicalSelectedSummand_finrank_pos
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (hmultiplicity :
      ProductAmbientGlaubermanNormalRestrictionMultiplicityIsPPrime
        S C hcentral hgenerate g theta) :
    0 <
      Module.finrank ℂ
        (ProductAmbientGlaubermanKernelSylowScalarSubspace
          S C hcentral hgenerate g theta
          (productAmbientGlaubermanCanonicalSelectedSylowScalar
            S C hcentral hgenerate g theta)) := by
  apply Nat.pos_of_ne_zero
  intro hzero
  apply hmultiplicity
  rw [←
    productAmbientGlaubermanCanonicalSelectedSummand_finrank
      S C hcentral hgenerate g theta]
  exact hzero ▸ dvd_zero q

/-- The prime-to-`q` canonical-extension multiplicity supplies the
`Nontrivial` instance needed to form the descended selected-summand
projective representation. -/
theorem productAmbientGlaubermanCanonicalSelectedSummand_nontrivial
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (hmultiplicity :
      ProductAmbientGlaubermanNormalRestrictionMultiplicityIsPPrime
        S C hcentral hgenerate g theta) :
    Nontrivial
      (ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta)) :=
  Module.nontrivial_of_finrank_pos
    (productAmbientGlaubermanCanonicalSelectedSummand_finrank_pos
      S C hcentral hgenerate g theta hmultiplicity)

/-- Arithmetic wrapper for the canonical-summand obstruction argument.
The explicit nontriviality premise has disappeared: it follows from the
prime-to-`q` restriction multiplicity. -/
theorem
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_selectedSummandArithmetic
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
    (hselected :
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
      letI :=
        trivialMulDistribMulAction
          (productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta) ℂˣ
      (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
        S C hcentral hgenerate g theta).factorSet.h2Class = 0) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta := by
  letI : Nontrivial
      (ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta)) :=
    productAmbientGlaubermanCanonicalSelectedSummand_nontrivial
      S C hcentral hgenerate g theta hmultiplicity
  exact
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_canonicalSelectedSummand
      S C hcentral hgenerate g theta hselected

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
