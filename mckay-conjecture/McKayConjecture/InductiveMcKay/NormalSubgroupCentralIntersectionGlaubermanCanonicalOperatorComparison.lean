/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveStableSubspace
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanKernelOperatorTransport

/-!
# Canonical operators in the kernel Glauberman comparison

This file instantiates the abstract kernel operator in the preceding
transport file with the actual projective action on the Glauberman
restriction-multiplicity space.

The construction supplies, without additional hypotheses:

* the canonical kernel multiplicity space;
* its canonical projective representation;
* literal equality of its factor set with the kernel mismatch;
* normalization of its identity operator; and
* the explicit pointwise formula for every chosen operator.

The final ambient multiplicity space is not, in general, the entire kernel
Hom-space.  It is the summand on which the Sylow factor acts through the
linear parameter selected by the normalized extensions.  Accordingly this
file defines that simultaneous scalar eigenspace, restricts the canonical
kernel projective action to it, and proves that the restriction has exactly
the kernel mismatch factor.  The remaining comparison is then one concrete
operator equivalence between this selected summand and the final quotient
multiplicity representation.
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

/-- The actual Hom-space occurring in the kernel Glauberman
multiplicity theorem, specialized to the active kernel constituent selected
by the ambient character. -/
abbrev ProductAmbientGlaubermanKernelMultiplicitySpace
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :=
  g.ProjectiveMultiplicitySpace
    (productAmbientGlaubermanSourceKernelCharacter
      S C hcentral theta)

/-- The canonical external projective action on the kernel Glauberman
multiplicity space. -/
def productAmbientGlaubermanKernelMultiplicityProjective
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    ProjectiveRepresentation ℂ
      (ProductGlaubermanKernelCharacterStabilizer
        S C hcentral
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta))
      (ProductAmbientGlaubermanKernelMultiplicitySpace
        S C hcentral g theta) :=
  let kernelTheta :=
    productAmbientGlaubermanSourceKernelCharacter
      S C hcentral theta
  EquivariantMultiplicityMismatch.projective
    (productGlaubermanKernelStabilizerAction
      S C hcentral kernelTheta)
    (productGlaubermanFixedPointsStabilizerAction
      S C hcentral kernelTheta)
    (coprimeFixedPointsInclusion
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C)))
    (productGlaubermanStabilizerActions_inclusion_commutes
      S C hcentral kernelTheta)
    kernelTheta.1.1
    (g.characterEquiv kernelTheta).1
    (productGlaubermanKernelCharacter_isInvariant
      S C hcentral kernelTheta)
    (productGlaubermanFixedPointCharacter_isInvariant
      S C hcentral g kernelTheta)

/-- The kernel multiplicity space is nonzero.  This is a consequence of
the defining Glauberman multiplicity being prime to `q`, rather than an
extra representation-model assumption. -/
noncomputable instance productAmbientGlaubermanKernelMultiplicitySpace_nontrivial
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    Nontrivial
      (ProductAmbientGlaubermanKernelMultiplicitySpace
        S C hcentral g theta) := by
  let V :=
    ProductAmbientGlaubermanKernelMultiplicitySpace
      S C hcentral g theta
  have hpositive : 0 < Module.finrank ℂ V := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hprime :=
      g.projectiveMultiplicitySpace_finrank_isPPrime
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)
    exact hprime (hzero ▸ dvd_zero q)
  exact
    Module.nontrivial_of_finrank_pos
      (R := ℂ) hpositive

/-- The factor set of the actual kernel multiplicity action is literally
the previously named kernel mismatch factor set. -/
theorem productAmbientGlaubermanKernelMultiplicityProjective_factorSet
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    (productAmbientGlaubermanKernelMultiplicityProjective
      S C hcentral g theta).factorSet =
      productGlaubermanKernelProjectiveMultiplicityFactorSet
        S C hcentral g
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta) := by
  let kernelTheta :=
    productAmbientGlaubermanSourceKernelCharacter
      S C hcentral theta
  letI :
      Nontrivial (g.ProjectiveMultiplicitySpace kernelTheta) := by
    dsimp only [kernelTheta]
    infer_instance
  exact
    EquivariantMultiplicityMismatch.projective_factorSet
      (productGlaubermanKernelStabilizerAction
        S C hcentral kernelTheta)
      (productGlaubermanFixedPointsStabilizerAction
        S C hcentral kernelTheta)
      (coprimeFixedPointsInclusion
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)))
      (productGlaubermanStabilizerActions_inclusion_commutes
        S C hcentral kernelTheta)
      kernelTheta.1.1
      (g.characterEquiv kernelTheta).1
      (productGlaubermanKernelCharacter_isInvariant
        S C hcentral kernelTheta)
      (productGlaubermanFixedPointCharacter_isInvariant
        S C hcentral g kernelTheta)

/-- The actual kernel multiplicity action is normalized at the identity. -/
theorem productAmbientGlaubermanKernelMultiplicityProjective_isNormalized
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    (productAmbientGlaubermanKernelMultiplicityProjective
      S C hcentral g theta).IsNormalized := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro f
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro w
  change
    AssociatedExistence.intertwiner
        (productGlaubermanKernelStabilizerAction
          S C hcentral
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta))
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1.1
        (productGlaubermanKernelCharacter_isInvariant
          S C hcentral
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta))
        1
        (f
          ((AssociatedExistence.intertwiner
            (productGlaubermanFixedPointsStabilizerAction
              S C hcentral
              (productAmbientGlaubermanSourceKernelCharacter
                S C hcentral theta))
            (g.characterEquiv
              (productAmbientGlaubermanSourceKernelCharacter
                S C hcentral theta)).1
            (productGlaubermanFixedPointCharacter_isInvariant
              S C hcentral g
              (productAmbientGlaubermanSourceKernelCharacter
                S C hcentral theta))
            1).symm w)) =
      f w
  rw [AssociatedExistence.intertwiner_one,
    AssociatedExistence.intertwiner_one]
  rfl

/-- Pointwise formula for the actual kernel multiplicity operator. -/
theorem productAmbientGlaubermanKernelMultiplicityProjective_operator_apply
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (gamma :
      ProductGlaubermanKernelCharacterStabilizer
        S C hcentral
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta))
    (f :
      ProductAmbientGlaubermanKernelMultiplicitySpace
        S C hcentral g theta)
    (w :
      (g.characterEquiv
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).1.realization) :
    (productAmbientGlaubermanKernelMultiplicityProjective
        S C hcentral g theta).operator gamma f w =
      AssociatedExistence.intertwiner
          (productGlaubermanKernelStabilizerAction
            S C hcentral
            (productAmbientGlaubermanSourceKernelCharacter
              S C hcentral theta))
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta).1.1
          (productGlaubermanKernelCharacter_isInvariant
            S C hcentral
            (productAmbientGlaubermanSourceKernelCharacter
              S C hcentral theta))
          gamma
          (f
            ((AssociatedExistence.intertwiner
              (productGlaubermanFixedPointsStabilizerAction
                S C hcentral
                (productAmbientGlaubermanSourceKernelCharacter
                  S C hcentral theta))
              (g.characterEquiv
                (productAmbientGlaubermanSourceKernelCharacter
                  S C hcentral theta)).1
              (productGlaubermanFixedPointCharacter_isInvariant
                S C hcentral g
                (productAmbientGlaubermanSourceKernelCharacter
                  S C hcentral theta))
              gamma).symm w)) :=
  rfl

/-- The kernel multiplicity action restricted to the matched right inertia
group. -/
def productAmbientGlaubermanRestrictedKernelMultiplicityProjective
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
      (ProductAmbientGlaubermanKernelMultiplicitySpace
        S C hcentral g theta) :=
  (productAmbientGlaubermanKernelMultiplicityProjective
    S C hcentral g theta).comap
      (productAmbientGlaubermanRightInertiaToKernelStabilizer
        S C hcentral hgenerate g theta)

/-- Inclusion of the Sylow direct factor of the right normal copy into the
matched right inertia group. -/
def productAmbientGlaubermanRightNormalSylowToInertia
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    internalNormalizerSylow (productSylow S C) →*
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta :=
  ((ProductAmbientGlaubermanRightNormalCopy
      S C hcentral hgenerate g theta).subtype).comp
    (productAmbientGlaubermanRightNormalCopySylowHom
      S C hcentral hgenerate g theta)

/-- The selected Sylow-linear summand of the kernel Glauberman Hom-space.
The scalar function is deliberately not required to be a homomorphism:
with the canonical chosen intertwiners it is a one-dimensional projective
cochain carrying the restricted factor. -/
abbrev ProductAmbientGlaubermanKernelSylowScalarSubspace
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (mu :
      internalNormalizerSylow (productSylow S C) → ℂˣ) :=
  ProjectiveRepresentation.scalarRestrictionSubmodule
    (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
      S C hcentral hgenerate g theta)
    (productAmbientGlaubermanRightNormalSylowToInertia
      S C hcentral hgenerate g theta)
    mu

/-- Membership in the selected summand is exactly the simultaneous
Sylow-scalar operator identity. -/
theorem productAmbientGlauberman_mem_kernelSylowScalarSubspace_iff
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (mu :
      internalNormalizerSylow (productSylow S C) → ℂˣ)
    (f :
      ProductAmbientGlaubermanKernelMultiplicitySpace
        S C hcentral g theta) :
    f ∈ ProductAmbientGlaubermanKernelSylowScalarSubspace
          S C hcentral hgenerate g theta mu ↔
      ∀ b : internalNormalizerSylow (productSylow S C),
        (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
          S C hcentral hgenerate g theta).operator
            (productAmbientGlaubermanRightNormalSylowToInertia
              S C hcentral hgenerate g theta b) f =
          (mu b : ℂ) • f :=
  Iff.rfl

/-- Restricting the canonical kernel action to a stable selected
Sylow-linear summand preserves the restricted kernel mismatch factor
literally. -/
theorem productAmbientGlaubermanKernelSylowScalarProjective_factorSet
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (mu :
      internalNormalizerSylow (productSylow S C) → ℂˣ)
    (hstable :
      (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
        S C hcentral hgenerate g theta).IsStable
          (ProductAmbientGlaubermanKernelSylowScalarSubspace
            S C hcentral hgenerate g theta mu))
    [Nontrivial
      (ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta mu)] :
    ((productAmbientGlaubermanRestrictedKernelMultiplicityProjective
        S C hcentral hgenerate g theta).restrictStable
          (ProductAmbientGlaubermanKernelSylowScalarSubspace
            S C hcentral hgenerate g theta mu)
          hstable).factorSet =
      (productGlaubermanKernelProjectiveMultiplicityFactorSet
        S C hcentral g
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta)).comap
            (productAmbientGlaubermanRightInertiaToKernelStabilizer
              S C hcentral hgenerate g theta) := by
  calc
    _ =
        (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
          S C hcentral hgenerate g theta).factorSet :=
      ProjectiveRepresentation.restrictStable_factorSet
        (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
          S C hcentral hgenerate g theta)
        (ProductAmbientGlaubermanKernelSylowScalarSubspace
          S C hcentral hgenerate g theta mu)
        hstable
    _ = _ := by
      rw [←
      productAmbientGlaubermanKernelMultiplicityProjective_factorSet
        S C hcentral g theta]
      apply FactorSet.ext
      intro b d
      rfl

/-- The exact normalization equation on the Sylow factor.  On a nonzero
selected summand, its rescaled operator is the identity precisely when the
inertia cochain restricts to the inverse selected scalar.

This deliberately records the rescaling needed before quotient descent;
omitting it would force `mu b = 1` for every Sylow element. -/
theorem productAmbientGlauberman_rescaledKernelSylow_operator_eq_one_iff
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (mu :
      internalNormalizerSylow (productSylow S C) → ℂˣ)
    (hstable :
      (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
        S C hcentral hgenerate g theta).IsStable
          (ProductAmbientGlaubermanKernelSylowScalarSubspace
            S C hcentral hgenerate g theta mu))
    (c :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta → ℂˣ)
    [Nontrivial
      (ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta mu)]
    (b : internalNormalizerSylow (productSylow S C)) :
    ((((productAmbientGlaubermanRestrictedKernelMultiplicityProjective
            S C hcentral hgenerate g theta).restrictStable
              (ProductAmbientGlaubermanKernelSylowScalarSubspace
                S C hcentral hgenerate g theta mu)
              hstable).rescale c).operator
          (productAmbientGlaubermanRightNormalSylowToInertia
            S C hcentral hgenerate g theta b) = 1) ↔
      c
          (productAmbientGlaubermanRightNormalSylowToInertia
            S C hcentral hgenerate g theta b) =
        (mu b)⁻¹ :=
  ProjectiveRepresentation.rescale_restrictStable_operator_image_eq_one_iff
      (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanRightNormalSylowToInertia
        S C hcentral hgenerate g theta)
      mu hstable c b

/-- The selected kernel action after normalization and exact descent through
the right normal copy.

The inertia cochain is essential: on the selected summand the Sylow factor
acts by the prescribed scalar `mu`, which need not be trivial.  Rescaling by
a cochain whose restriction cancels those normal-copy scalars is what makes
exact quotient descent possible. -/
def productAmbientGlaubermanKernelSylowScalarQuotientProjective
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (mu :
      internalNormalizerSylow (productSylow S C) → ℂˣ)
    (hstable :
      (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
        S C hcentral hgenerate g theta).IsStable
          (ProductAmbientGlaubermanKernelSylowScalarSubspace
            S C hcentral hgenerate g theta mu))
    (c :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta → ℂˣ)
    (hquotient :
      (((productAmbientGlaubermanRestrictedKernelMultiplicityProjective
            S C hcentral hgenerate g theta).restrictStable
              (ProductAmbientGlaubermanKernelSylowScalarSubspace
                S C hcentral hgenerate g theta mu)
              hstable).rescale c).IsQuotientCompatible
        (ProductAmbientGlaubermanRightNormalCopy
          S C hcentral hgenerate g theta)) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ProjectiveRepresentation ℂ
        (productAmbientGlaubermanRightOuterQuotient
          S C hcentral hgenerate g theta)
        (ProductAmbientGlaubermanKernelSylowScalarSubspace
          S C hcentral hgenerate g theta mu) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
  (((productAmbientGlaubermanRestrictedKernelMultiplicityProjective
        S C hcentral hgenerate g theta).restrictStable
          (ProductAmbientGlaubermanKernelSylowScalarSubspace
            S C hcentral hgenerate g theta mu)
          hstable).rescale c).quotientDescent
          (ProductAmbientGlaubermanRightNormalCopy
            S C hcentral hgenerate g theta)
          hquotient

/-- The exact operator-intertwining equation between the normalized
selected kernel summand and the final quotient mismatch representation.
Naming this equation keeps the remaining DGN realization obligation
separate from the automatic factor-set and `H²` consequences. -/
def ProductAmbientGlaubermanSelectedSummandOperatorIntertwining
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (mu :
      internalNormalizerSylow (productSylow S C) → ℂˣ)
    (hstable :
      (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
        S C hcentral hgenerate g theta).IsStable
          (ProductAmbientGlaubermanKernelSylowScalarSubspace
            S C hcentral hgenerate g theta mu))
    (c :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta → ℂˣ)
    (hquotient :
      (((productAmbientGlaubermanRestrictedKernelMultiplicityProjective
            S C hcentral hgenerate g theta).restrictStable
              (ProductAmbientGlaubermanKernelSylowScalarSubspace
                S C hcentral hgenerate g theta mu)
              hstable).rescale c).IsQuotientCompatible
        (ProductAmbientGlaubermanRightNormalCopy
          S C hcentral hgenerate g theta))
    (E :
      ProductAmbientGlaubermanKernelSylowScalarSubspace
          S C hcentral hgenerate g theta mu ≃ₗ[ℂ]
        ProductAmbientGlaubermanMultiplicityMismatchSpace
          S C hcentral hgenerate g theta)
    (a :
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta → ℂˣ) : Prop :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  ∀ (u :
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta)
    (z :
      ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta mu),
    E
        (((productAmbientGlaubermanKernelSylowScalarQuotientProjective
          S C hcentral hgenerate g theta mu hstable c hquotient
          ).rescale a).operator u z) =
      (ProductAmbientGlaubermanFinalMismatchQuotientProjective
        S C hcentral hgenerate g theta).operator u (E z)

/-- Pointwise form of the named selected-summand operator
intertwining condition. -/
theorem productAmbientGlaubermanSelectedSummand_operator_intertwines
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (mu :
      internalNormalizerSylow (productSylow S C) → ℂˣ)
    (hstable :
      (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
        S C hcentral hgenerate g theta).IsStable
          (ProductAmbientGlaubermanKernelSylowScalarSubspace
            S C hcentral hgenerate g theta mu))
    (c :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta → ℂˣ)
    (hquotient :
      (((productAmbientGlaubermanRestrictedKernelMultiplicityProjective
            S C hcentral hgenerate g theta).restrictStable
              (ProductAmbientGlaubermanKernelSylowScalarSubspace
                S C hcentral hgenerate g theta mu)
              hstable).rescale c).IsQuotientCompatible
        (ProductAmbientGlaubermanRightNormalCopy
          S C hcentral hgenerate g theta))
    (E :
      ProductAmbientGlaubermanKernelSylowScalarSubspace
          S C hcentral hgenerate g theta mu ≃ₗ[ℂ]
        ProductAmbientGlaubermanMultiplicityMismatchSpace
          S C hcentral hgenerate g theta)
    (a :
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta → ℂˣ)
    (hoperator :
      ProductAmbientGlaubermanSelectedSummandOperatorIntertwining
        S C hcentral hgenerate g theta mu hstable c hquotient E a) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ∀ (u :
        productAmbientGlaubermanRightOuterQuotient
          S C hcentral hgenerate g theta)
      (z :
        ProductAmbientGlaubermanKernelSylowScalarSubspace
          S C hcentral hgenerate g theta mu),
      E
          (((productAmbientGlaubermanKernelSylowScalarQuotientProjective
            S C hcentral hgenerate g theta mu hstable c hquotient
            ).rescale a).operator u z) =
        (ProductAmbientGlaubermanFinalMismatchQuotientProjective
          S C hcentral hgenerate g theta).operator u (E z) :=
  hoperator

/-- The faithful remaining operator comparison.  Unlike the whole-space
criterion, this compares the final quotient multiplicity representation
with only the selected Sylow-linear summand of the kernel Hom-space.

Every other factor-level assertion is then automatic: conjugacy with a
scalar rescaling gives the exact gauge equality of the two canonical
quotient factors. -/
theorem productAmbientGlaubermanFinalMismatch_factorSet_eq_selectedKernel_gauge
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (mu :
      internalNormalizerSylow (productSylow S C) → ℂˣ)
    (hstable :
      (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
        S C hcentral hgenerate g theta).IsStable
          (ProductAmbientGlaubermanKernelSylowScalarSubspace
            S C hcentral hgenerate g theta mu))
    (c :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta → ℂˣ)
    (hquotient :
      (((productAmbientGlaubermanRestrictedKernelMultiplicityProjective
            S C hcentral hgenerate g theta).restrictStable
              (ProductAmbientGlaubermanKernelSylowScalarSubspace
                S C hcentral hgenerate g theta mu)
              hstable).rescale c).IsQuotientCompatible
        (ProductAmbientGlaubermanRightNormalCopy
          S C hcentral hgenerate g theta))
    [Nontrivial
      (ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta mu)]
    [Nontrivial
      (ProductAmbientGlaubermanMultiplicityMismatchSpace
        S C hcentral hgenerate g theta)]
    (E :
      ProductAmbientGlaubermanKernelSylowScalarSubspace
          S C hcentral hgenerate g theta mu ≃ₗ[ℂ]
        ProductAmbientGlaubermanMultiplicityMismatchSpace
          S C hcentral hgenerate g theta)
    (a :
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta → ℂˣ)
    (hoperator :
      ProductAmbientGlaubermanSelectedSummandOperatorIntertwining
        S C hcentral hgenerate g theta mu hstable c hquotient E a) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (ProductAmbientGlaubermanFinalMismatchQuotientProjective
        S C hcentral hgenerate g theta).factorSet =
      (productAmbientGlaubermanKernelSylowScalarQuotientProjective
        S C hcentral hgenerate g theta mu hstable c hquotient
        ).factorSet.gauge a := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    ProjectiveRepresentation.factorSet_eq_gauge_of_rescaled_equiv
      (productAmbientGlaubermanKernelSylowScalarQuotientProjective
        S C hcentral hgenerate g theta mu hstable c hquotient)
      (ProductAmbientGlaubermanFinalMismatchQuotientProjective
        S C hcentral hgenerate g theta)
      E a
      (productAmbientGlaubermanSelectedSummand_operator_intertwines
        S C hcentral hgenerate g theta mu hstable c hquotient
        E a hoperator)

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
