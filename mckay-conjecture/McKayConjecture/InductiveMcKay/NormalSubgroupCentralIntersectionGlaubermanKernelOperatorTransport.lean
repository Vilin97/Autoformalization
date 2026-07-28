/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedUniqueness
import McKayConjecture.CharacterTriple.ProjectiveRestriction
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanKernelQuotientObstructionTransport
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45MultiplicityObstruction

/-!
# Operator-level transport of the kernel Glauberman obstruction

This file isolates the operator comparison behind the remaining
Dade--Glauberman--Nagao transport.

First, a general lemma turns conjugacy of one projective action with a
scalar-rescaling of another into the corresponding gauge equality of factor
sets.  In the concrete Proposition-4.5 setting this removes the opaque
factor-level `htransport` premise: it is enough to give a linear equivalence
between the descended kernel multiplicity space and the final quotient
multiplicity space and verify one pointwise operator identity.

The Sylow descent premise is also reduced to operators.  If the scalar
measuring the proposed obstruction is faithful and the two normalized
operator families already agree on the Sylow factor, then the canonical
Sylow obstruction homomorphism is trivial.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple

variable {G : Type} [Group G]
variable {V : Type} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
variable {W : Type} [AddCommGroup W] [Module ℂ W] [Nontrivial W]

/-- A scalar-rescaled operator equivalence gives exactly the associated
gauge transformation of projective factor sets. -/
theorem ProjectiveRepresentation.factorSet_eq_gauge_of_rescaled_equiv
    (P : ProjectiveRepresentation ℂ G V)
    (Q : ProjectiveRepresentation ℂ G W)
    (E : V ≃ₗ[ℂ] W)
    (a : G → ℂˣ)
    (hoperator :
      ∀ (g : G) (v : V),
        E ((P.rescale a).operator g v) =
          Q.operator g (E v)) :
    Q.factorSet = P.factorSet.gauge a := by
  calc
    Q.factorSet = (P.rescale a).factorSet := by
      apply FactorSet.ext
      intro g h
      exact
        (AssociatedProjectiveRepresentation.factor_eq_of_equiv_operator_eq
          (P := P.rescale a) (Q := Q)
          E hoperator g h).symm
    _ = P.factorSet.gauge a :=
      P.rescale_factorSet a

/-- If an operator equivalence differs pointwise by a nonzero scalar, then
rescaling by the inverse scalar gives an exact operator equivalence and hence
the corresponding inverse gauge transformation of factor sets. -/
theorem ProjectiveRepresentation.factorSet_eq_gauge_inverse_of_scalar_equiv
    (P : ProjectiveRepresentation ℂ G V)
    (Q : ProjectiveRepresentation ℂ G W)
    (E : V ≃ₗ[ℂ] W)
    (c : G → ℂˣ)
    (hoperator :
      ∀ (g : G) (v : V),
        E (P.operator g v) =
          (c g : ℂ) • Q.operator g (E v)) :
    Q.factorSet = P.factorSet.gauge (fun g ↦ (c g)⁻¹) := by
  apply
    ProjectiveRepresentation.factorSet_eq_gauge_of_rescaled_equiv
      P Q E (fun g ↦ (c g)⁻¹)
  intro g v
  rw [ProjectiveRepresentation.rescale_operator,
    LinearEquiv.mul_apply, scalarLinearEquiv_apply, map_smul,
    hoperator g v]
  simp only [Units.val_inv_eq_inv_val,
    inv_smul_smul₀ (c g).ne_zero]

end CharacterTriple

namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CliffordEquivalence
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- Exact operator criterion for the canonical Sylow obstruction to vanish.
The scalar comparison says that `leftOperator` differs from
`rightOperator` by the proposed obstruction scalar.  If the normalized
operators already agree and the scalar realization is faithful, that
obstruction scalar is one. -/
theorem productAmbientGlaubermanRightNormalSylowObstructionHom_eq_one_of_operatorAgreement
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (D : Type) [Group D]
    (rho :
      ProductGlaubermanKernelCharacterStabilizer
          S C hcentral
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta) →* D)
    (ι : D →* ℂˣ)
    (hι : Function.Injective ι)
    (Z : Type) [AddCommGroup Z] [Module ℂ Z] [Nontrivial Z]
    (leftOperator rightOperator :
      internalNormalizerSylow (productSylow S C) →
        Z ≃ₗ[ℂ] Z)
    (hscalar :
      ∀ b,
        leftOperator b =
          scalarLinearEquiv ℂ Z
              (ι
                (productAmbientGlaubermanRightNormalSylowObstructionHom
                  S C hcentral hgenerate g theta D rho b)) *
            rightOperator b)
    (hagrees :
      ∀ b, leftOperator b = rightOperator b) :
    productAmbientGlaubermanRightNormalSylowObstructionHom
        S C hcentral hgenerate g theta D rho =
      1 := by
  apply MonoidHom.ext
  intro b
  change
    productAmbientGlaubermanRightNormalSylowObstructionHom
        S C hcentral hgenerate g theta D rho b =
      1
  apply hι
  rw [map_one]
  apply scalarLinearEquiv_injective ℂ Z
  rw [map_one]
  apply mul_right_cancel (b := rightOperator b)
  calc
    scalarLinearEquiv ℂ Z
          (ι
            (productAmbientGlaubermanRightNormalSylowObstructionHom
              S C hcentral hgenerate g theta D rho b)) *
        rightOperator b =
      leftOperator b :=
        (hscalar b).symm
    _ = rightOperator b :=
      hagrees b
    _ = 1 * rightOperator b := by
      rw [one_mul]

/-- The final quotient projective action on the canonical matched
normal-restriction multiplicity space. -/
abbrev ProductAmbientGlaubermanFinalMismatchQuotientProjective
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  ProjectiveMultiplicityMismatch.quotientProjective
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta)
    (productAmbientGlaubermanRightAssociated
      S C hcentral hgenerate g theta)
    (productAmbientGlaubermanInertiaRestrictionGroupData
      S C hcentral hgenerate g theta)

/-- Pull a projective realization of the kernel mismatch back along the
canonical descended obstruction homomorphism. -/
def productAmbientGlaubermanKernelDescendedProjective
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (D : Type) [Group D]
    (hD : IsPGroup q D)
    (rho :
      ProductGlaubermanKernelCharacterStabilizer
          S C hcentral
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta) →* D)
    (hsylow :
      productAmbientGlaubermanRightNormalSylowObstructionHom
          S C hcentral hgenerate g theta D rho =
        1)
    (Z : Type) [AddCommGroup Z] [Module ℂ Z]
    (P : ProjectiveRepresentation ℂ D Z) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ProjectiveRepresentation ℂ
      (productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta) Z := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    P.comap
      (productAmbientGlaubermanRightOuterToKernelObstructionHom
        S C hcentral hgenerate g theta D rho
        (productAmbientGlaubermanRightNormalCopy_le_kernel_of_sylow
          S C hcentral hgenerate g theta D hD rho hsylow))

/-- A normalized kernel projective realization has identity operators after
descent, because the descended homomorphism from the `q'` outer quotient to
the `q`-group is trivial. -/
theorem productAmbientGlaubermanKernelDescendedProjective_operator_eq_one
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (D : Type) [Group D]
    (hD : IsPGroup q D)
    (rho :
      ProductGlaubermanKernelCharacterStabilizer
          S C hcentral
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta) →* D)
    (hsylow :
      productAmbientGlaubermanRightNormalSylowObstructionHom
          S C hcentral hgenerate g theta D rho =
        1)
    (Z : Type) [AddCommGroup Z] [Module ℂ Z]
    (P : ProjectiveRepresentation ℂ D Z)
    (hP : P.IsNormalized)
    (u :
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (productAmbientGlaubermanKernelDescendedProjective
      S C hcentral hgenerate g theta D hD rho hsylow Z P).operator u =
        1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let hkill :=
    productAmbientGlaubermanRightNormalCopy_le_kernel_of_sylow
      S C hcentral hgenerate g theta D hD rho hsylow
  have hdescended :=
    productAmbientGlaubermanRightOuterToKernelObstructionHom_eq_one
      S C hcentral hgenerate g theta D hD rho hkill
  have hu :=
    congrArg
      (fun f :
        productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta →* D ↦
        f u)
      hdescended
  change
    P.operator
      (productAmbientGlaubermanRightOuterToKernelObstructionHom
        S C hcentral hgenerate g theta D rho hkill u) =
      1
  rw [hu]
  exact hP

/-- The factor set of the descended kernel projective realization is the
pullback of its original factor set along the descended obstruction
homomorphism. -/
theorem productAmbientGlaubermanKernelDescendedProjective_factorSet
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (D : Type) [Group D]
    (hD : IsPGroup q D)
    (rho :
      ProductGlaubermanKernelCharacterStabilizer
          S C hcentral
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta) →* D)
    (hsylow :
      productAmbientGlaubermanRightNormalSylowObstructionHom
          S C hcentral hgenerate g theta D rho =
        1)
    (Z : Type) [AddCommGroup Z] [Module ℂ Z] [Nontrivial Z]
    (P : ProjectiveRepresentation ℂ D Z) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (productAmbientGlaubermanKernelDescendedProjective
        S C hcentral hgenerate g theta D hD rho hsylow Z P).factorSet =
      P.factorSet.comap
        (productAmbientGlaubermanRightOuterToKernelObstructionHom
          S C hcentral hgenerate g theta D rho
          (productAmbientGlaubermanRightNormalCopy_le_kernel_of_sylow
            S C hcentral hgenerate g theta D hD rho hsylow)) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  apply FactorSet.ext
  intro u v
  rfl

/-- Pointwise form of the descended normalized operator after a scalar
rescaling. -/
theorem productAmbientGlaubermanKernelDescendedProjective_rescale_operator
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (D : Type) [Group D]
    (hD : IsPGroup q D)
    (rho :
      ProductGlaubermanKernelCharacterStabilizer
          S C hcentral
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta) →* D)
    (hsylow :
      productAmbientGlaubermanRightNormalSylowObstructionHom
          S C hcentral hgenerate g theta D rho =
        1)
    (Z : Type) [AddCommGroup Z] [Module ℂ Z]
    (P : ProjectiveRepresentation ℂ D Z)
    (hP : P.IsNormalized)
    (a :
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta → ℂˣ)
    (u :
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta)
    (z : Z) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ((productAmbientGlaubermanKernelDescendedProjective
      S C hcentral hgenerate g theta D hD rho hsylow Z P).rescale a
        ).operator u z =
      (a u : ℂ) • z := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  change
    scalarLinearEquiv ℂ Z (a u)
        ((productAmbientGlaubermanKernelDescendedProjective
          S C hcentral hgenerate g theta D hD rho hsylow Z P).operator u z) =
      (a u : ℂ) • z
  rw [productAmbientGlaubermanKernelDescendedProjective_operator_eq_one
      S C hcentral hgenerate g theta D hD rho hsylow Z P hP u]
  rfl

/-- The remaining DGN operator comparison, stated without an opaque
factor-level transport premise.

The kernel mismatch must be the pullback of the factor of a normalized
projective realization on a finite `q`-group.  After the canonical Sylow
descent, a linear equivalence `E` identifies its space with the final
quotient multiplicity space.  It remains only to check that every final
quotient operator acts through `E` by the displayed scalar `a u`.  The
general rescaled-operator lemma then constructs the exact gauge equality
and proves the intrinsic obstruction agreement. -/
theorem productAmbientGlaubermanProjectiveObstructionClassAgreement_of_kernelOperatorTransport
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (D : Type) [Group D] [Finite D]
    (hD : IsPGroup q D)
    (rho :
      ProductGlaubermanKernelCharacterStabilizer
          S C hcentral
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta) →* D)
    (Z : Type) [AddCommGroup Z] [Module ℂ Z] [Nontrivial Z]
    (P : ProjectiveRepresentation ℂ D Z)
    (hP : P.IsNormalized)
    (hkernel :
      productGlaubermanKernelProjectiveMultiplicityFactorSet
          S C hcentral g
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta) =
        P.factorSet.comap rho)
    (hsylow :
      productAmbientGlaubermanRightNormalSylowObstructionHom
          S C hcentral hgenerate g theta D rho =
        1)
    [Nontrivial
      (ProductAmbientGlaubermanMultiplicityMismatchSpace
        S C hcentral hgenerate g theta)]
    (E :
      Z ≃ₗ[ℂ]
        ProductAmbientGlaubermanMultiplicityMismatchSpace
          S C hcentral hgenerate g theta)
    (a :
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta → ℂˣ)
    (hoperator :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      ∀ (u :
          productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta)
        (z : Z),
        (ProductAmbientGlaubermanFinalMismatchQuotientProjective
            S C hcentral hgenerate g theta).operator u (E z) =
          (a u : ℂ) • E z) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let kernelProjective :=
    productAmbientGlaubermanKernelDescendedProjective
      S C hcentral hgenerate g theta D hD rho hsylow Z P
  let finalProjective :=
    ProductAmbientGlaubermanFinalMismatchQuotientProjective
      S C hcentral hgenerate g theta
  have hrescaledOperator :
      ∀ (u :
          productAmbientGlaubermanRightOuterQuotient
            S C hcentral hgenerate g theta)
        (z : Z),
        E ((kernelProjective.rescale a).operator u z) =
          finalProjective.operator u (E z) := by
    intro u z
    have hz :
        (kernelProjective.rescale a).operator u z =
          (a u : ℂ) • z :=
      productAmbientGlaubermanKernelDescendedProjective_rescale_operator
        S C hcentral hgenerate g theta D hD rho hsylow Z P hP a u z
    calc
      E ((kernelProjective.rescale a).operator u z) =
          E ((a u : ℂ) • z) :=
        congrArg E hz
      _ = (a u : ℂ) • E z :=
        map_smul E (a u : ℂ) z
      _ = finalProjective.operator u (E z) :=
        (hoperator u z).symm
  have hfactor :
      finalProjective.factorSet =
        kernelProjective.factorSet.gauge a :=
    ProjectiveRepresentation.factorSet_eq_gauge_of_rescaled_equiv
      kernelProjective finalProjective E a hrescaledOperator
  have hfinalFactor :
      finalProjective.factorSet =
        productAmbientGlaubermanQuotientMismatchFactorSet
          S C hcentral hgenerate g theta :=
    ProjectiveMultiplicityMismatch.quotientProjective_factorSet
      (productAmbientGlaubermanLeftAssociated
        S C hgenerate theta)
      (productAmbientGlaubermanRightAssociated
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta)
  have hkernelFactor :
      kernelProjective.factorSet =
        P.factorSet.comap
          (productAmbientGlaubermanRightOuterToKernelObstructionHom
            S C hcentral hgenerate g theta D rho
            (productAmbientGlaubermanRightNormalCopy_le_kernel_of_sylow
              S C hcentral hgenerate g theta D hD rho hsylow)) :=
    productAmbientGlaubermanKernelDescendedProjective_factorSet
      S C hcentral hgenerate g theta D hD rho hsylow Z P
  have htransport :
      productAmbientGlaubermanQuotientMismatchFactorSet
          S C hcentral hgenerate g theta =
        (P.factorSet.comap
          (productAmbientGlaubermanRightOuterToKernelObstructionHom
            S C hcentral hgenerate g theta D rho
            (productAmbientGlaubermanRightNormalCopy_le_kernel_of_sylow
              S C hcentral hgenerate g theta D hD rho hsylow))).gauge a := by
    rw [← hfinalFactor, hfactor, hkernelFactor]
  exact
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_kernelSylowTransport
      S C hcentral hgenerate g theta D hD rho P.factorSet
      hkernel hsylow a htransport

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
