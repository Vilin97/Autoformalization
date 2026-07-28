/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.MagicLinearization
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalSelectedSummandArithmetic

/-!
# The magic-linearization interface for the Glauberman summand

The Dade--Glauberman--Nagao input constructs a genuine action on the
canonical selected multiplicity summand and compares that action with the
descended projective operators up to scalars.  In the terminology of the
generic projective API, this is a `MagicLinearization`.

This file proves that such a construction, together with the prime-to-`q`
canonical-extension multiplicity, gives the projective obstruction
agreement required in Proposition 4.5.  Thus the remaining local theorem
has a concrete output: an honest operator homomorphism, a scalar cochain,
and their pointwise comparison.
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

/-- A magic linearization of the canonical selected summand kills its
factor class and hence proves the required projective obstruction
agreement. -/
theorem
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_magicLinearization
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
    (hmagic :
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
      ProjectiveRepresentation.MagicLinearization
        (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
          S C hcentral hgenerate g theta)) :
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
  apply
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_selectedSummandArithmetic
      S C hcentral hgenerate g theta hmultiplicity
  exact hmagic.factorSet_h2Class_eq_zero

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
