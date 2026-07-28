/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.TrivialEndomorphismInteriorAction
import McKayConjecture.CharacterTriple.ProjectiveNormalizerLift
import McKayConjecture.CharacterTriple.ProjectiveQuotientNormalization
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalSelectedSummandQuotient

/-!
# The canonical Glauberman projective normalizer lift

The canonical selected summand was identified with the invariant maps
for the honest fixed-point-times-Sylow kernel action.  This file records
the resulting interior-algebra structure and constructs the projective
normalizer lift of the canonical quotient action.

The honest Sylow action on the kernel Hom-space is literally trivial
on the selected summand.  Consequently its image in the units of the
endomorphism algebra is trivial, so every canonical quotient operator
belongs to the interior normalizer.  The resulting lift has exactly (not merely
cohomologically) the factor of the canonical complex quotient
projective representation.

This is the strongest characteristic-zero normalizer construction
available from the canonical kernel operators alone.  Passing it to a
finite field still requires a cross-characteristic integral model of
the selected summand and its projective operators.
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

/-- The selected canonical kernel summand, given a short name for the
normalizer-lift construction. -/
abbrev ProductAmbientGlaubermanCanonicalSelectedSummand
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :=
  ProductAmbientGlaubermanKernelSylowScalarSubspace
    S C hcentral hgenerate g theta
    (productAmbientGlaubermanCanonicalSelectedSylowScalar
      S C hcentral hgenerate g theta)

/-- The honest Sylow action induced on the invariant selected
summand.  It is definitionally the trivial linear action; the following
theorem relates this compact presentation to the original kernel
`linHom` operators. -/
def productAmbientGlaubermanCanonicalSelectedSummandSylowAction
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    internalNormalizerSylow (productSylow S C) →*
      (ProductAmbientGlaubermanCanonicalSelectedSummand
        S C hcentral hgenerate g theta ≃ₗ[ℂ]
       ProductAmbientGlaubermanCanonicalSelectedSummand
        S C hcentral hgenerate g theta) :=
  _root_.Representation.trivialLinearAction

@[simp]
theorem
    productAmbientGlaubermanCanonicalSelectedSummandSylowAction_apply
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b : internalNormalizerSylow (productSylow S C))
    (z :
      ProductAmbientGlaubermanCanonicalSelectedSummand
        S C hcentral hgenerate g theta) :
    productAmbientGlaubermanCanonicalSelectedSummandSylowAction
        S C hcentral hgenerate g theta b z =
      z :=
  rfl

/-- The compact trivial action is the actual restriction of the honest
kernel `linHom` action: after forgetting the selected-summand subtype,
both sides are literally the same linear map. -/
theorem
    productAmbientGlaubermanCanonicalSelectedSummandSylowAction_val
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b : internalNormalizerSylow (productSylow S C))
    (z :
      ProductAmbientGlaubermanCanonicalSelectedSummand
        S C hcentral hgenerate g theta) :
    ((productAmbientGlaubermanCanonicalSelectedSummandSylowAction
        S C hcentral hgenerate g theta b z).1 :
      _ →ₗ[ℂ] _) =
      _root_.Representation.linHom
        (ProductAmbientGlaubermanFixedPointKernelSylowFDRep
          S C hcentral g theta).ρ
        (ProductAmbientGlaubermanSourceKernelSylowFDRep
          S C hcentral theta).ρ b (z.1 : _ →ₗ[ℂ] _) := by
  rw [
    productAmbientGlaubermanCanonicalSelectedSummandSylowAction_apply]
  exact
    (productAmbientGlaubermanCanonicalSelectedSummand_sylow_fixed
      S C hcentral hgenerate g theta z b).symm

/-- The final mismatch quotient is normalized because its pre-descent
action is exactly quotient-compatible. -/
theorem productAmbientGlaubermanFinalMismatchQuotientProjective_isNormalized
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
    (ProductAmbientGlaubermanFinalMismatchQuotientProjective
      S C hcentral hgenerate g theta).IsNormalized := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    ProjectiveRepresentation.quotientDescent_isNormalized
      (ProjectiveMultiplicityMismatch.isQuotientCompatible
        (productAmbientGlaubermanLeftAssociated
          S C hgenerate theta)
        (productAmbientGlaubermanRightAssociated
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanInertiaRestrictionGroupData
          S C hcentral hgenerate g theta))

/-- The canonical selected-summand quotient action is normalized.  This
is transported from the final mismatch quotient through their strict
operator intertwining. -/
theorem
    productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective_isNormalized
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
    (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
      S C hcentral hgenerate g theta).IsNormalized := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let E :=
    productAmbientGlaubermanCanonicalSelectedSummandEquivMismatchSpaceDirect
      S C hcentral hgenerate g theta
  have hfinal :
      (ProductAmbientGlaubermanFinalMismatchQuotientProjective
        S C hcentral hgenerate g theta).operator 1 = 1 :=
    productAmbientGlaubermanFinalMismatchQuotientProjective_isNormalized
      S C hcentral hgenerate g theta
  apply LinearEquiv.ext
  intro z
  apply E.injective
  calc
    E
        ((productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
          S C hcentral hgenerate g theta).operator 1 z) =
      (ProductAmbientGlaubermanFinalMismatchQuotientProjective
        S C hcentral hgenerate g theta).operator 1 (E z) :=
      productAmbientGlaubermanCanonicalSelectedSummand_quotient_intertwines
        S C hcentral hgenerate g theta 1 z
    _ = E z := by
      exact DFunLike.congr_fun hfinal (E z)

/-- The canonical complex selected-summand quotient operators, placed
in the normalizer of the genuine (trivial-on-invariants) kernel
interior action. -/
def productAmbientGlaubermanCanonicalSelectedSummandProjectiveNormalizerLift
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
    let P := internalNormalizerSylow (productSylow S C)
    let V :=
      ProductAmbientGlaubermanCanonicalSelectedSummand
        S C hcentral hgenerate g theta
    letI : Fintype P := Fintype.ofFinite P
    letI : MulSemiringAction P (Module.End ℂ V) :=
      _root_.Representation.endomorphismConjugationMulSemiringAction
        (_root_.Representation.trivialLinearAction
          (k := ℂ) (P := P) (V := V))
    letI : SMulCommClass P ℂ (Module.End ℂ V) :=
      _root_.Representation.endomorphismConjugation_smulCommClass
        (_root_.Representation.trivialLinearAction
          (k := ℂ) (P := P) (V := V))
    let I :=
      _root_.Representation.trivialEndomorphismInteriorAction
        (k := ℂ) (P := P) (V := V)
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    _root_.Representation.ProjectiveNormalizerLift
      (k := ℂ)
      (H :=
        productAmbientGlaubermanRightOuterQuotient
          S C hcentral hgenerate g theta)
      I := by
  let P := internalNormalizerSylow (productSylow S C)
  let V :=
    ProductAmbientGlaubermanCanonicalSelectedSummand
      S C hcentral hgenerate g theta
  letI : Fintype P := Fintype.ofFinite P
  letI : MulSemiringAction P (Module.End ℂ V) :=
    _root_.Representation.endomorphismConjugationMulSemiringAction
      (_root_.Representation.trivialLinearAction
        (k := ℂ) (P := P) (V := V))
  letI : SMulCommClass P ℂ (Module.End ℂ V) :=
    _root_.Representation.endomorphismConjugation_smulCommClass
      (_root_.Representation.trivialLinearAction
        (k := ℂ) (P := P) (V := V))
  let I :=
    _root_.Representation.trivialEndomorphismInteriorAction
      (k := ℂ) (P := P) (V := V)
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let Q :=
    productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
      S C hcentral hgenerate g theta
  exact
    ProjectiveRepresentation.toProjectiveNormalizerLift Q I
      (fun u ↦
        _root_.Representation.mem_trivialEndomorphismInteriorAction_unitNormalizer
          (ProjectiveRepresentation.operatorUnit (Q.operator u)))
      (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective_isNormalized
        S C hcentral hgenerate g theta)

/-- Forgetting the normalizer packaging recovers each canonical
selected-summand quotient operator literally. -/
theorem
    productAmbientGlaubermanCanonicalSelectedSummandProjectiveNormalizerLift_operator
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
    (u :
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta) :
    let P := internalNormalizerSylow (productSylow S C)
    let V :=
      ProductAmbientGlaubermanCanonicalSelectedSummand
        S C hcentral hgenerate g theta
    letI : Fintype P := Fintype.ofFinite P
    letI : MulSemiringAction P (Module.End ℂ V) :=
      _root_.Representation.endomorphismConjugationMulSemiringAction
        (_root_.Representation.trivialLinearAction
          (k := ℂ) (P := P) (V := V))
    letI : SMulCommClass P ℂ (Module.End ℂ V) :=
      _root_.Representation.endomorphismConjugation_smulCommClass
        (_root_.Representation.trivialLinearAction
          (k := ℂ) (P := P) (V := V))
    let I :=
      _root_.Representation.trivialEndomorphismInteriorAction
        (k := ℂ) (P := P) (V := V)
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    I.normalizerLinearEquiv
        ((productAmbientGlaubermanCanonicalSelectedSummandProjectiveNormalizerLift
          S C hcentral hgenerate g theta).operator u) =
      (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
        S C hcentral hgenerate g theta).operator u := by
  let P := internalNormalizerSylow (productSylow S C)
  let V :=
    ProductAmbientGlaubermanCanonicalSelectedSummand
      S C hcentral hgenerate g theta
  letI : Fintype P := Fintype.ofFinite P
  letI : MulSemiringAction P (Module.End ℂ V) :=
    _root_.Representation.endomorphismConjugationMulSemiringAction
      (_root_.Representation.trivialLinearAction
        (k := ℂ) (P := P) (V := V))
  letI : SMulCommClass P ℂ (Module.End ℂ V) :=
    _root_.Representation.endomorphismConjugation_smulCommClass
      (_root_.Representation.trivialLinearAction
        (k := ℂ) (P := P) (V := V))
  let I :=
    _root_.Representation.trivialEndomorphismInteriorAction
      (k := ℂ) (P := P) (V := V)
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let Q :=
    productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
      S C hcentral hgenerate g theta
  dsimp only [
    productAmbientGlaubermanCanonicalSelectedSummandProjectiveNormalizerLift]
  exact
    ProjectiveRepresentation.normalizerLinearEquiv_normalizerOperator
      Q I
      (fun a ↦
        _root_.Representation.mem_trivialEndomorphismInteriorAction_unitNormalizer
          (ProjectiveRepresentation.operatorUnit (Q.operator a)))
      u

/-- The projective normalizer lift has the canonical quotient factor
literally.  Thus no factor-comparison hypothesis is needed in
characteristic zero. -/
@[simp]
theorem
    productAmbientGlaubermanCanonicalSelectedSummandProjectiveNormalizerLift_factor
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
    let P := internalNormalizerSylow (productSylow S C)
    let V :=
      ProductAmbientGlaubermanCanonicalSelectedSummand
        S C hcentral hgenerate g theta
    letI : Fintype P := Fintype.ofFinite P
    letI : MulSemiringAction P (Module.End ℂ V) :=
      _root_.Representation.endomorphismConjugationMulSemiringAction
        (_root_.Representation.trivialLinearAction
          (k := ℂ) (P := P) (V := V))
    letI : SMulCommClass P ℂ (Module.End ℂ V) :=
      _root_.Representation.endomorphismConjugation_smulCommClass
        (_root_.Representation.trivialLinearAction
          (k := ℂ) (P := P) (V := V))
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (productAmbientGlaubermanCanonicalSelectedSummandProjectiveNormalizerLift
        S C hcentral hgenerate g theta).factor u v =
      (productAmbientGlaubermanCanonicalSelectedSummandQuotientProjective
        S C hcentral hgenerate g theta).factor u v :=
  rfl

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
