/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleMultiplicityObstruction
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45IntrinsicObstructions

/-!
# Proposition 4.5 through the projective multiplicity mismatch

This file specializes the projective multiplicity-space construction to the
concrete matched Glauberman--Okuyama--Wajima inertia triples in Proposition
4.5.

The determinant of that action reduces the intrinsic obstruction equality
to two sharply stated claims:

* the matched right normal character occurs in the restriction of the left
  normal character with multiplicity prime to `q`; and
* the resulting quotient-factor mismatch class is `q`-primary.

The first multiplicity is displayed both as an ordinary character
restriction multiplicity and as the dimension of the projective mismatch
space.  Thus there is no representation-model ambiguity in the criterion.

This is only an abstract final-normal-character criterion.  The classical
Glauberman prime-to-`q` multiplicity concerns the kernel character and its
fixed-point correspondent, not these independently Gallagher-normalized
ambient characters.  The kernel-level construction is therefore the
mathematically relevant route; it still requires the Dade--Glauberman--Nagao
transport identifying its factor mismatch with the inertia-quotient
obstruction below.
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

/-- The projective normal-restriction multiplicity space for one concrete
matched Proposition-4.5 inertia pair. -/
abbrev ProductAmbientGlaubermanMultiplicityMismatchSpace
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
  ProjectiveMultiplicityMismatch.Space
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta)
    (productAmbientGlaubermanRightAssociated
      S C hcentral hgenerate g theta)
    (productAmbientGlaubermanInertiaRestrictionGroupData
      S C hcentral hgenerate g theta)

/-- The ordinary restriction multiplicity measured by the projective
mismatch space. -/
abbrev productAmbientGlaubermanNormalRestrictionMultiplicity
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
  CliffordCorrespondence.restrictionMultiplicity
    (ProjectiveMultiplicityMismatch.normalHom
      (productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta))
    (productAmbientGlaubermanRightInertiaTriple
      S C hcentral hgenerate g theta).character
    (productAmbientGlaubermanLeftInertiaTriple
      S C hgenerate theta).character

/-- The projective mismatch dimension is exactly the displayed ordinary
restriction multiplicity. -/
theorem productAmbientGlaubermanMultiplicityMismatch_finrank
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    Module.finrank ℂ
        (ProductAmbientGlaubermanMultiplicityMismatchSpace
          S C hcentral hgenerate g theta) =
      productAmbientGlaubermanNormalRestrictionMultiplicity
        S C hcentral hgenerate g theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    ProjectiveMultiplicityMismatch.finrank_space_eq_restrictionMultiplicity
      (productAmbientGlaubermanLeftAssociated
        S C hgenerate theta)
      (productAmbientGlaubermanRightAssociated
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta)

/-- The exact prime-to-`q` multiplicity assertion needed by the determinant
route at the final matched normal-character level. -/
def ProductAmbientGlaubermanNormalRestrictionMultiplicityIsPPrime
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) : Prop :=
  ¬q ∣
    productAmbientGlaubermanNormalRestrictionMultiplicity
      S C hcentral hgenerate g theta

/-- The exact `q`-primary factor-mismatch assertion needed by the
multiplicity route. -/
def ProductAmbientGlaubermanMultiplicityMismatchIsQPrimary
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) : Prop :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  (productAmbientGlaubermanInertiaRestrictionGroupData
    S C hcentral hgenerate g theta
    ).MultiplicityMismatchIsQPrimary
      (productAmbientGlaubermanLeftAssociated
        S C hgenerate theta)
      (productAmbientGlaubermanRightAssociated
        S C hcentral hgenerate g theta)
      q

/-- A prime-to-`q` matched-normal restriction multiplicity and a
`q`-primary mismatch prove the exact remaining intrinsic obstruction
agreement in Proposition 4.5. -/
theorem productAmbientGlaubermanProjectiveObstructionClassAgreement_of_multiplicity
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hmultiplicity :
      ProductAmbientGlaubermanNormalRestrictionMultiplicityIsPPrime
        S C hcentral hgenerate g theta)
    (hprimary :
      ProductAmbientGlaubermanMultiplicityMismatchIsQPrimary
        S C hcentral hgenerate g theta) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  apply
    (productAmbientGlaubermanInertiaRestrictionGroupData
      S C hcentral hgenerate g theta
      ).projectiveObstructionClassAgreement_of_multiplicity_prime_to_of_mismatch_qPrimary
        (productAmbientGlaubermanLeftAssociated
          S C hgenerate theta)
        (productAmbientGlaubermanRightAssociated
          S C hcentral hgenerate g theta)
        q
  · rw [
      productAmbientGlaubermanMultiplicityMismatch_finrank
        S C hcentral hgenerate g theta]
    exact hmultiplicity
  · exact hprimary

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
