/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteProjectiveResidueComapNormalization
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalNormalizerLift
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalSelectedSummandArithmetic

/-!
# The residue Sylow action in the canonical Glauberman quotient

The finite `q`-group naturally attached to the canonical selected summand is
the Sylow direct factor of the right inertia normal copy.  Its map to the
right outer quotient is the composite

`P → I_right → I_right / N_right`.

Because the first map lands in `N_right`, this composite is identically one.
Consequently the residue-field projective action restricted along it has a
canonical constant-one linearization.  The constant-one scalar correction is
conjugation-stable, so the resulting honest action is normalized by every
ambient projective operator.

This also records an important limitation of this construction: the
canonical quotient action only sees the trivial action of this `q`-group.
Thus this honest action cannot be the faithful interior action required by a
nontrivial primitive Dade model.
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

/-- The Sylow direct factor of the right inertia normal copy, mapped to the
right outer quotient. -/
def productAmbientGlaubermanRightNormalSylowToOuterQuotient
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    internalNormalizerSylow (productSylow S C) →*
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    (QuotientGroup.mk'
      (ProductAmbientGlaubermanRightNormalCopy
        S C hcentral hgenerate g theta)).comp
      (productAmbientGlaubermanRightNormalSylowToInertia
        S C hcentral hgenerate g theta)

omit [Finite X] [Fact q.Prime] [C.Normal] in
/-- The internal Sylow factor is a finite `q`-group. -/
theorem productAmbientGlaubermanInternalNormalizerSylow_isPGroup :
    IsPGroup q
      (internalNormalizerSylow (productSylow S C)) := by
  exact
    (productSylow S C).isPGroup'.of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (show
          (productSylow S C :
              Subgroup (product S C)) ≤
            Subgroup.normalizer
              (productSylow S C :
                Set (product S C)) from
          Subgroup.le_normalizer)).symm

/-- The canonical Sylow-to-outer-quotient homomorphism is trivial, since it
factors through the subgroup killed by the quotient. -/
theorem
    productAmbientGlaubermanRightNormalSylowToOuterQuotient_eq_one
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    productAmbientGlaubermanRightNormalSylowToOuterQuotient
        S C hcentral hgenerate g theta =
      1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  ext r
  change
    QuotientGroup.mk'
        (ProductAmbientGlaubermanRightNormalCopy
          S C hcentral hgenerate g theta)
        ((ProductAmbientGlaubermanRightNormalCopy
          S C hcentral hgenerate g theta).subtype
          (productAmbientGlaubermanRightNormalCopySylowHom
            S C hcentral hgenerate g theta r)) =
      1
  simpa only [QuotientGroup.mk'_apply] using
    (QuotientGroup.eq_one_iff
      ((ProductAmbientGlaubermanRightNormalCopy
        S C hcentral hgenerate g theta).subtype
        (productAmbientGlaubermanRightNormalCopySylowHom
          S C hcentral hgenerate g theta r))).2
      (productAmbientGlaubermanRightNormalCopySylowHom
        S C hcentral hgenerate g theta r).property

/-- More generally, every homomorphism from a `q`-group to the canonical
right outer quotient is trivial: the latter has order prime to `q`. -/
theorem productAmbientGlauberman_qGroupHom_rightOuterQuotient_eq_one
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    {R : Type} [Group R]
    (hR : IsPGroup q R)
    (i :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      R →*
        productAmbientGlaubermanRightOuterQuotient
          S C hcentral hgenerate g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    i = 1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let houter :=
    productAmbientGlaubermanRightOuterQuotient_isPPrimeGroup
      S C hcentral hgenerate g theta
  ext r
  obtain ⟨k, hk⟩ := hR r
  have hpow :
      orderOf (i r) ∣ q ^ k :=
    (orderOf_map_dvd i r).trans
      (orderOf_dvd_of_pow_eq_one hk)
  have hcard :
      orderOf (i r) ∣
        Nat.card
          (productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta) :=
    orderOf_dvd_natCard (i r)
  have hone : orderOf (i r) = 1 :=
    Nat.eq_one_of_dvd_coprimes
      (houter.pow_left k) hpow hcard
  exact orderOf_eq_one_iff.mp hone

variable {ι : Type} [Finite ι]

/-- The constant-one correction for the canonical Sylow composite is
conjugation-stable on the actual selected-summand residue representation.
Thus scalar-correction stability is not an additional Dade input in the
canonical outer quotient. -/
theorem productAmbientGlaubermanCanonicalResidueSylowCorrection_isStable
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
          S C hcentral hgenerate g theta)) :
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
    (Q.residueFieldProjectiveRepresentation b q
      ).ScalarCorrectionIsConjugationStable
        (productAmbientGlaubermanRightNormalSylowToOuterQuotient
          S C hcentral hgenerate g theta)
        (fun _ ↦ 1) := by
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
  exact
    (Q.residueFieldProjectiveRepresentation b q
      ).scalarCorrectionIsConjugationStable_constOne_of_hom_eq_one
      (Q.residueFieldProjectiveRepresentation_factor_right_one b q)
      (productAmbientGlaubermanRightNormalSylowToOuterQuotient
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanRightNormalSylowToOuterQuotient_eq_one
        S C hcentral hgenerate g theta)

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
