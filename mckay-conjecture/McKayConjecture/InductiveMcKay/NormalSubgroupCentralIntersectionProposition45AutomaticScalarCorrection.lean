/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveScalarCorrectionExtension
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizedNormalCentralValues
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45IntrinsicObstructions
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45ScalarCorrection

/-!
# Automatic scalar correction in Proposition 4.5

For the concrete Glauberman--Okuyama--Wajima inertia comparison, normalized
normal-central values agree unconditionally.  Thus intrinsic projective
obstruction-class agreement and commutativity of the right inertia outer
quotient construct the scalar correction; normalized values are no longer a
premise.

We state commutativity as containment of the right inertia commutator in its
canonical normal copy.  The sharper alternative is the exact
intersection-with-normal-and-commutator kernel condition.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CliffordEquivalence
open GroupTheory
open ComplementReduction

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The concrete right inertia outer quotient is abelian, stated without
installing an auxiliary quotient `CommGroup` instance. -/
def ProductAmbientGlaubermanRightInertiaCommutatorLeNormal
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
  let phi :=
    internalTheorem44CharacterEquiv
      S C
      (complementCharacterEquivOfGlauberman
        S C hcentral g) theta
  _root_.commutator
      (IrreducibleCharacter.inertia
        (internalProductNormalizer S C) phi.1) ≤
    inertiaNormalCopy
      (internalProductNormalizer S C) phi.1

/-- The exact post-factor-matching scalar-correction kernel condition for
one concrete inertia pair. -/
def ProductAmbientGlaubermanScalarCorrectionKernelCondition
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
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  H2ScalarCorrectableProjectiveComparisonData.KernelCondition
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta)
    (productAmbientGlaubermanRightAssociated
      S C hcentral hgenerate g theta)
    (productAmbientGlaubermanInertiaRestrictionGroupData
      S C hcentral hgenerate g theta)
    (productAmbientGlaubermanCanonicalFactorH2Agreement
      S C hcentral hgenerate g theta h)

/-- Intrinsic obstruction-class agreement plus the exact sharp kernel
condition constructs scalar-correctable projective comparison data for one
concrete inertia pair. -/
def productAmbientGlaubermanScalarCorrectionOfKernelCondition
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
        S C hcentral hgenerate g theta)
    (hkernel :
      ProductAmbientGlaubermanScalarCorrectionKernelCondition
        S C hcentral hgenerate g theta h) :
    H2ScalarCorrectableProjectiveComparisonData
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
    H2ScalarCorrectableProjectiveComparisonData.ofAssociatedOfKernelCondition
      (productAmbientGlaubermanLeftAssociated
        S C hgenerate theta)
      (productAmbientGlaubermanRightAssociated
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanCanonicalFactorH2Agreement
        S C hcentral hgenerate g theta h)
      hkernel

/-- Intrinsic obstruction-class agreement and an abelian right inertia
outer quotient construct scalar-correctable comparison data.  The
normalized-value input is discharged by the unconditional concrete
Okuyama--Wajima theorem. -/
def productAmbientGlaubermanScalarCorrectionOfCommutatorLeNormal
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
        S C hcentral hgenerate g theta)
    (hcommutator :
      ProductAmbientGlaubermanRightInertiaCommutatorLeNormal
        S C hcentral hgenerate g theta) :
    H2ScalarCorrectableProjectiveComparisonData
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
    H2ScalarCorrectableProjectiveComparisonData.ofAssociatedOfNormalizedValuesOfCommutatorLeNormal
      (productAmbientGlaubermanLeftAssociated
        S C hgenerate theta)
      (productAmbientGlaubermanRightAssociated
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanCanonicalFactorH2Agreement
        S C hcentral hgenerate g theta h)
      (productAmbientGlauberman_normalizedNormalCentralValuesAgree
        S C hcentral hgenerate g theta)
      hcommutator

/-- The remaining every-inertia-pair input after normalized values and
equivariance have been proved: intrinsic factor-obstruction agreement and
abelianity of the concrete right inertia outer quotient. -/
structure ProductAmbientGlaubermanObstructionCommutatorData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral) : Prop where
  projectiveObstructionClassAgreement :
    ∀ theta :
        PPrimeIrreducibleCharacter
          (product S C) q,
      ProductAmbientGlaubermanProjectiveObstructionClassAgreement
        S C hcentral hgenerate g theta
  rightInertia_commutator_le_normal :
    ∀ theta :
        PPrimeIrreducibleCharacter
          (product S C) q,
      ProductAmbientGlaubermanRightInertiaCommutatorLeNormal
        S C hcentral hgenerate g theta

namespace ProductAmbientGlaubermanObstructionCommutatorData

/-- Convert the two remaining every-pair claims into the existing
scalar-correction package. -/
def toProductAmbientGlaubermanProjectiveScalarCorrectionData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (d :
      ProductAmbientGlaubermanObstructionCommutatorData
        S C hcentral hgenerate g) :
    ProductAmbientGlaubermanProjectiveScalarCorrectionData
      S C hcentral hgenerate g := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    { comparison := fun theta ↦
        productAmbientGlaubermanScalarCorrectionOfCommutatorLeNormal
          S C hcentral hgenerate g theta
          (d.projectiveObstructionClassAgreement theta)
          (d.rightInertia_commutator_le_normal theta) }

end ProductAmbientGlaubermanObstructionCommutatorData

end Proposition45

/-- Global Proposition-4.5 input with normalized values removed: only
intrinsic projective obstruction agreement and abelianity of each concrete
right inertia outer quotient remain. -/
def CentralScalarCentralIntersectionObstructionCommutatorHypothesis
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
          (Proposition45.ProductAmbientGlaubermanObstructionCommutatorData
            S C hcentral hgenerate g)

/-- The obstruction-and-commutator formulation supplies the existing
scalar-correction hypothesis. -/
theorem projectiveScalarCorrectionHypothesis_of_obstructionCommutator
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionObstructionCommutatorHypothesis
        q) :
    CentralScalarCentralIntersectionProjectiveScalarCorrectionHypothesis
      q := by
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  intro g
  obtain ⟨d⟩ :=
    h X S C hCnormal hcentral hgenerate g
  exact
    ⟨d.toProductAmbientGlaubermanProjectiveScalarCorrectionData
      S C hcentral hgenerate g⟩

/-- Intrinsic obstruction agreement plus the concrete right-inertia
commutator containment implies the full central-intersection reduction. -/
theorem centralScalarCentralIntersectionReductionHypothesis_of_obstructionCommutator
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionObstructionCommutatorHypothesis
        q) :
    CentralScalarCentralIntersectionReductionHypothesis q :=
  centralScalarCentralIntersectionReductionHypothesis_of_scalarCorrection
    (projectiveScalarCorrectionHypothesis_of_obstructionCommutator
      h)

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
