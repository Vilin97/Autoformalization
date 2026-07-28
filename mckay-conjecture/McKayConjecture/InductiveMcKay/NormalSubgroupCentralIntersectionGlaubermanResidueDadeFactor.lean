/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteProjectiveResidueDadeFactor
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalNormalizerLift
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalSelectedSummandArithmetic

/-!
# The canonical residue-field Dade-factor boundary

The generic residue-Dade package constructs the normalizer lift and compares
its factor through the unconditional complex character of residue-field
units.  This file specializes that result to the canonical Glauberman
selected-summand quotient and feeds the resulting vanishing class into
Proposition 4.5.
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
variable {ι : Type} [Finite ι]

/-- Primitive Dade data on the actual residue lattice of the canonical
selected-summand projective representation prove obstruction agreement.
The normalizer lift, residue-unit character, and factor comparison are
internal to `ResidueDadeFactorData`. -/
theorem
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_residueDadeFactor
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
    (b :
      Module.Basis ι ℂ
        (ProductAmbientGlaubermanCanonicalSelectedSummand
          S C hcentral hgenerate g theta))
    (d :
      letI : Nontrivial
          (ProductAmbientGlaubermanCanonicalSelectedSummand
            S C hcentral hgenerate g theta) :=
        productAmbientGlaubermanCanonicalSelectedSummand_nontrivial
          S C hcentral hgenerate g theta hmultiplicity
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
        S C hcentral hgenerate g theta
        ).ResidueDadeFactorData b q) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta := by
  let V :=
    ProductAmbientGlaubermanCanonicalSelectedSummand
      S C hcentral hgenerate g theta
  letI : Nontrivial V :=
    productAmbientGlaubermanCanonicalSelectedSummand_nontrivial
      S C hcentral hgenerate g theta hmultiplicity
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let Q :=
    productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
      S C hcentral hgenerate g theta
  have hdegree :
      ¬q ∣ Module.finrank ℂ V := by
    rw [
      productAmbientGlaubermanCanonicalSelectedSummand_finrank
        S C hcentral hgenerate g theta]
    exact hmultiplicity
  exact
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_canonicalSelectedSummand
      S C hcentral hgenerate g theta
      (CharacterTriple.ProjectiveRepresentation.ResidueDadeFactorData.factorSet_h2Class_eq_zero
        Q b q d hdegree)

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
