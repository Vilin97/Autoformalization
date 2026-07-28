/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveObstructionClass
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizerAssemblyNaturality
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProjectiveCenterMismatch
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45H2Mismatch

/-!
# The two intrinsic obstructions left in Proposition 4.5

The concrete Glauberman--Okuyama--Wajima character equivalence is already
equivariant under the ambient normalizer.  Moreover, its normalized-value
identity kills the projective scalar mismatch on the image of `Z(CP)`.

Consequently the remaining Proposition-4.5 input consists of exactly two
claims for each matched inertia pair:

* equality of the intrinsic projective obstruction classes in `H²`; and
* triviality of the sharp scalar character on the comparison centralizer
  modulo the image of `Z(CP)`.

This file packages those two claims using canonical associated projective
representations and proves that they imply the full central-intersection
reduction.  In particular, no equivariance premise remains in the public
hypothesis.
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

/-- The left inertia triple in the concrete Proposition-4.5 comparison. -/
abbrev productAmbientGlaubermanLeftInertiaTriple
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  ofInertia (product S C) theta.1

/-- The right inertia triple in the concrete Proposition-4.5 comparison. -/
abbrev productAmbientGlaubermanRightInertiaTriple
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
  ofInertia
    (internalProductNormalizer S C)
    (internalTheorem44CharacterEquiv
      S C
      (complementCharacterEquivOfGlauberman
        S C hcentral g) theta).1

/-- The canonical embedding between the matched inertia groups.  Its
equivariance input is the unconditional covariance theorem for the
Glauberman--Okuyama--Wajima construction. -/
abbrev productAmbientGlaubermanInertiaEmbedding
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
  MatchedInertiaRestriction.embedding
    (product S C)
    (ambientNormalizer S)
    (internalProductNormalizer S C)
    (internalTheorem44CharacterEquiv
      S C
      (complementCharacterEquivOfGlauberman
        S C hcentral g))
    (complementCharacterEquivOfGlauberman_internal_smul
      S C hcentral hgenerate g)
    theta

/-- The ordinary central-restriction group data for the concrete inertia
pair, specialized to the now-proved equivariance theorem. -/
abbrev productAmbientGlaubermanInertiaRestrictionGroupData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  productAmbientInertiaRestrictionGroupData
    S C hgenerate
    (complementCharacterEquivOfGlauberman
      S C hcentral g)
    (complementCharacterEquivOfGlauberman_internal_smul
      S C hcentral hgenerate g)
    theta

/-- The intrinsic `H²` obstruction for one concrete matched inertia pair. -/
def ProductAmbientGlaubermanProjectiveObstructionClassAgreement
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) : Prop :=
  (productAmbientGlaubermanInertiaRestrictionGroupData
    S C hcentral hgenerate g theta
    ).ProjectiveObstructionClassAgreement

/-- The canonical left associated projective representation used to state
the sharp residual scalar obstruction. -/
abbrev productAmbientGlaubermanLeftAssociated
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  AssociatedGeneralExistence.associated
    (productAmbientGlaubermanLeftInertiaTriple
      S C hgenerate theta)

/-- The canonical right associated projective representation used to state
the sharp residual scalar obstruction. -/
abbrev productAmbientGlaubermanRightAssociated
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  AssociatedGeneralExistence.associated
    (productAmbientGlaubermanRightInertiaTriple
      S C hcentral hgenerate g theta)

/-- Intrinsic obstruction-class agreement gives factor-class agreement for
the canonical associated lifts. -/
theorem productAmbientGlaubermanCanonicalFactorH2Agreement
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (h :
      ProductAmbientGlaubermanProjectiveObstructionClassAgreement
        S C hcentral hgenerate g theta) :
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta).QuotientFactorH2ClassAgreement
        (productAmbientGlaubermanRightAssociated
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanInertiaRestrictionGroupData
          S C hcentral hgenerate g theta) :=
  ((productAmbientGlaubermanLeftAssociated
      S C hgenerate theta
      ).quotientFactorH2ClassAgreement_iff_projectiveObstructionClass
        (productAmbientGlaubermanRightAssociated
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanInertiaRestrictionGroupData
          S C hcentral hgenerate g theta)).mpr h

/-- The factor-matching gauge selected canonically from intrinsic `H²`
agreement. -/
theorem productAmbientGlaubermanCanonicalFactorAgreement
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (h :
      ProductAmbientGlaubermanProjectiveObstructionClassAgreement
        S C hcentral hgenerate g theta) :
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta).QuotientFactorCohomologyAgreement
        (productAmbientGlaubermanRightAssociated
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanInertiaRestrictionGroupData
          S C hcentral hgenerate g theta) :=
  (productAmbientGlaubermanLeftAssociated
    S C hgenerate theta).quotientFactorCohomologyAgreement_of_h2Class
      (productAmbientGlaubermanRightAssociated
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanCanonicalFactorH2Agreement
        S C hcentral hgenerate g theta h)

/-- The sharp residual scalar claim: after matching factors using intrinsic
`H²`, the scalar mismatch is trivial on the comparison centralizer modulo
the image of `Z(CP)`. -/
def ProductAmbientGlaubermanSharpResidualScalarTrivial
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (h :
      ProductAmbientGlaubermanProjectiveObstructionClassAgreement
        S C hcentral hgenerate g theta) : Prop :=
  postFactorMatchingScalarMismatchProductAmbientCenterQuotient
      S C hcentral hgenerate g
      (complementCharacterEquivOfGlauberman_internal_smul
        S C hcentral hgenerate g)
      theta
      (productAmbientGlaubermanLeftAssociated
        S C hgenerate theta)
      (productAmbientGlaubermanRightAssociated
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanCanonicalFactorAgreement
        S C hcentral hgenerate g theta h) =
    1

/-- The two and only two unresolved projective claims for one inertia pair:
intrinsic `H²` agreement and triviality of the sharp residual scalar
character. -/
structure ProductAmbientGlaubermanIntrinsicObstructionClaims
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) : Prop where
  projectiveObstructionClassAgreement :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta
  sharpResidualScalar_trivial :
    ProductAmbientGlaubermanSharpResidualScalarTrivial
      S C hcentral hgenerate g theta
      projectiveObstructionClassAgreement

namespace ProductAmbientGlaubermanIntrinsicObstructionClaims

/-- Triviality of the sharp quotient character implies triviality of its
unquotiented scalar mismatch. -/
theorem postRescalingMismatch_trivial
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (d :
      ProductAmbientGlaubermanIntrinsicObstructionClaims
        S C hcentral hgenerate g theta) :
    let groupData :=
      productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta
    let leftAssociated :=
      productAmbientGlaubermanLeftAssociated
        S C hgenerate theta
    let rightAssociated :=
      productAmbientGlaubermanRightAssociated
        S C hcentral hgenerate g theta
    let factorAgreement :=
      productAmbientGlaubermanCanonicalFactorAgreement
        S C hcentral hgenerate g theta
        d.projectiveObstructionClassAgreement
    leftAssociated.comparisonCentralScalarMismatch
        (leftAssociated.factorMatchedRightAssociated
          rightAssociated groupData factorAgreement)
        groupData.projectiveComparisonCentralizer_le_rightCentralizer
        (leftAssociated.factorMatchedRightAssociated_factor_agreement
          rightAssociated groupData factorAgreement) =
      1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let theorem44Equiv :=
    complementCharacterEquivOfGlauberman
      S C hcentral g
  let characterEquiv_smul :=
    complementCharacterEquivOfGlauberman_internal_smul
      S C hcentral hgenerate g
  let groupData :=
    productAmbientGlaubermanInertiaRestrictionGroupData
      S C hcentral hgenerate g theta
  let leftAssociated :=
    productAmbientGlaubermanLeftAssociated
      S C hgenerate theta
  let rightAssociated :=
    productAmbientGlaubermanRightAssociated
      S C hcentral hgenerate g theta
  let factorAgreement :=
    productAmbientGlaubermanCanonicalFactorAgreement
      S C hcentral hgenerate g theta
      d.projectiveObstructionClassAgreement
  let scalarMismatch :=
    leftAssociated.comparisonCentralScalarMismatch
      (leftAssociated.factorMatchedRightAssociated
        rightAssociated groupData factorAgreement)
      groupData.projectiveComparisonCentralizer_le_rightCentralizer
      (leftAssociated.factorMatchedRightAssociated_factor_agreement
        rightAssociated groupData factorAgreement)
  let centerRange :=
    MonoidHom.range
      (productAmbientCenterProjectiveComparisonHom
        S C hgenerate theorem44Equiv
        characterEquiv_smul theta)
  letI : centerRange.Normal :=
    productAmbientCenterProjectiveComparisonHom_range_normal
      S C hgenerate theorem44Equiv
      characterEquiv_smul theta
  have hkernel :
      centerRange ≤ scalarMismatch.ker := by
    intro c hc
    obtain ⟨z, rfl⟩ := hc
    apply MonoidHom.mem_ker.mpr
    exact
      postFactorMatchingScalarMismatch_productAmbientCenter_eq_one
        S C hcentral hgenerate g
        characterEquiv_smul theta
        leftAssociated rightAssociated factorAgreement z
  let quotientMismatch :=
    QuotientGroup.lift
      centerRange scalarMismatch hkernel
  have hquotient :
      quotientMismatch = 1 := by
    exact d.sharpResidualScalar_trivial
  have hcomp :
      quotientMismatch.comp
          (QuotientGroup.mk' centerRange) =
        scalarMismatch := by
    exact
      QuotientGroup.lift_comp_mk'
        centerRange scalarMismatch hkernel
  change scalarMismatch = 1
  rw [← hcomp, hquotient]
  simp

/-- The two intrinsic claims provide the existing `H²`-mismatch interface
for this inertia pair. -/
def toH2MismatchProjectiveComparisonData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (d :
      ProductAmbientGlaubermanIntrinsicObstructionClaims
        S C hcentral hgenerate g theta) :
    H2MismatchProjectiveComparisonData
      (productAmbientGlaubermanLeftInertiaTriple
        S C hgenerate theta)
      (productAmbientGlaubermanRightInertiaTriple
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInertiaEmbedding
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    { leftSpace :=
        (productAmbientGlaubermanLeftInertiaTriple
          S C hgenerate theta).character.realization
      rightSpace :=
        (productAmbientGlaubermanRightInertiaTriple
          S C hcentral hgenerate g theta).character.realization
      leftProjective :=
        AssociatedGeneralExistence.projectiveRepresentation
          (productAmbientGlaubermanLeftInertiaTriple
            S C hgenerate theta)
      leftAssociated :=
        productAmbientGlaubermanLeftAssociated
          S C hgenerate theta
      rightProjective :=
        AssociatedGeneralExistence.projectiveRepresentation
          (productAmbientGlaubermanRightInertiaTriple
            S C hcentral hgenerate g theta)
      rightAssociated :=
        productAmbientGlaubermanRightAssociated
          S C hcentral hgenerate g theta
      quotientFactorH2ClassAgreement :=
        productAmbientGlaubermanCanonicalFactorH2Agreement
          S C hcentral hgenerate g theta
          d.projectiveObstructionClassAgreement
      postRescalingMismatch_trivial :=
        d.postRescalingMismatch_trivial
          S C hcentral hgenerate g theta }

end ProductAmbientGlaubermanIntrinsicObstructionClaims

/-- The intrinsic two-claim package for every inertia pair.  Equivariance
does not appear as a field because it is a theorem of the concrete
Glauberman--Okuyama--Wajima construction. -/
structure ProductAmbientGlaubermanIntrinsicObstructionData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral) : Prop where
  comparison :
    ∀ theta :
        PPrimeIrreducibleCharacter
          (product S C) q,
      ProductAmbientGlaubermanIntrinsicObstructionClaims
        S C hcentral hgenerate g theta

namespace ProductAmbientGlaubermanIntrinsicObstructionData

/-- The intrinsic obstruction package, together with proved equivariance,
supplies the earlier Proposition-4.5 `H²`-mismatch data. -/
def toProductAmbientGlaubermanProjectiveH2MismatchData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (d :
      ProductAmbientGlaubermanIntrinsicObstructionData
        S C hcentral hgenerate g) :
    ProductAmbientGlaubermanProjectiveH2MismatchData
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
      h2MismatchComparison := fun theta ↦
        (d.comparison theta
          ).toH2MismatchProjectiveComparisonData
            S C hcentral hgenerate g theta }

end ProductAmbientGlaubermanIntrinsicObstructionData

end Proposition45

/-- The central-intersection hypothesis with every already-proved
construction removed.  Its only fields are the intrinsic `H²` obstruction
and the sharp residual quotient-scalar obstruction for each inertia pair. -/
def CentralScalarCentralIntersectionIntrinsicProjectiveObstructionHypothesis
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
          (Proposition45.ProductAmbientGlaubermanIntrinsicObstructionData
            S C hcentral hgenerate g)

/-- The intrinsic `H²` and sharp residual quotient-scalar claims imply the
full central-intersection reduction. -/
theorem centralScalarCentralIntersectionReductionHypothesis_of_intrinsicProjectiveObstructions
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionIntrinsicProjectiveObstructionHypothesis
        q) :
    CentralScalarCentralIntersectionReductionHypothesis q := by
  apply
    centralScalarCentralIntersectionReductionHypothesis_of_projectiveH2Mismatch
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  intro g
  obtain ⟨d⟩ :=
    h X S C hCnormal hcentral hgenerate g
  exact
    ⟨d.toProductAmbientGlaubermanProjectiveH2MismatchData
      S C hcentral hgenerate g⟩

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
