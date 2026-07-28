/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetCentralExtensionNormalizer
import McKayConjecture.InductiveMcKay.CentralTripleLiftedFactorCorrespondence
import McKayConjecture.InductiveMcKay.MatchedInertiaSylowNormalizer
import
  McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45IntrinsicObstructions

/-!
# The Proposition-4.5 target factor extension as a Sylow-lift normalizer

Fix a concrete Glauberman--Okuyama--Wajima inertia pair for a character
`theta` of `CP`.  The ambient Sylow subgroup `S` lies in `I_X(theta)`,
because `S ≤ CP` and every element of `CP` stabilizes `theta`.  It therefore
induces a Sylow subgroup of the left inertia group.

The proved equivariance of the concrete character equivalence identifies the
right inertia group with the normalizer of this induced Sylow subgroup inside
the left inertia group.  Applying the generic normalizer theorem for a
factor-set central extension then identifies the pulled-back target factor
extension with the normalizer of the Sylow lift in the canonical left ambient
factor extension.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CharacterTriple.AssociatedProjectiveRepresentation
open CharacterTriple.FactorSet
open CharacterTriple.FactorSet.CentralExtensionGroup
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The underlying left inertia group, with the normality proof determined
by the concrete generation hypothesis. -/
abbrev ProductAmbientGlaubermanLeftInertiaGroup
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  IrreducibleCharacter.inertia
    (product S C) theta.1

/-- The underlying right inertia group in the concrete matched pair. -/
abbrev ProductAmbientGlaubermanRightInertiaGroup
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
  IrreducibleCharacter.inertia
    (internalProductNormalizer S C)
    (internalTheorem44CharacterEquiv
      S C
      (complementCharacterEquivOfGlauberman
        S C hcentral g) theta).1

omit [Finite X] [Fact q.Prime] in
/-- The ambient Sylow subgroup lies in the inertia group of every character
of `CP`. -/
theorem sylow_le_productAmbientLeftInertia
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    (S : Subgroup X) ≤
      IrreducibleCharacter.inertia
        (product S C) theta.1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
  (show
      (S : Subgroup X) ≤ product S C from
    le_sup_right).trans
    (IrreducibleCharacter.subgroup_le_inertia
      (product S C) theta.1)

/-- The Sylow subgroup of the left inertia group induced by the ambient
Sylow subgroup `S`. -/
abbrev productAmbientGlaubermanLeftInertiaSylow
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    Sylow q
      (ProductAmbientGlaubermanLeftInertiaGroup
        S C hgenerate theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    sylowIn S
      (IrreducibleCharacter.inertia
        (product S C) theta.1)
      (sylow_le_productAmbientLeftInertia
        S C hgenerate theta)

/-- The concrete right inertia group is canonically the normalizer of the
induced Sylow subgroup inside the left inertia group. -/
def productAmbientGlaubermanRightInertiaEquivLeftSylowNormalizer
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta ≃*
      Subgroup.normalizer
        (productAmbientGlaubermanLeftInertiaSylow
          S C hgenerate theta :
          Set
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    MatchedInertiaRestriction.targetInertiaEquivSourceSylowNormalizer
      (product S C) S
      (internalProductNormalizer S C)
      (internalTheorem44CharacterEquiv
        S C
        (complementCharacterEquivOfGlauberman
          S C hcentral g))
      (complementCharacterEquivOfGlauberman_internal_smul
        S C hcentral hgenerate g)
      theta
      (sylow_le_productAmbientLeftInertia
        S C hgenerate theta)

@[simp]
theorem productAmbientGlaubermanRightInertiaEquivLeftSylowNormalizer_apply
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta) :
    ((productAmbientGlaubermanRightInertiaEquivLeftSylowNormalizer
        S C hcentral hgenerate g theta b :
      Subgroup.normalizer
        (productAmbientGlaubermanLeftInertiaSylow
          S C hgenerate theta :
          Set
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta))) :
      ProductAmbientGlaubermanLeftInertiaGroup
        S C hgenerate theta) =
      productAmbientGlaubermanInertiaEmbedding
        S C hcentral hgenerate g theta b := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  rfl

/-- The base homomorphism induced by the inertia-normalizer equivalence is
literally the canonical matched-inertia embedding. -/
theorem productAmbientGlaubermanSylowNormalizerBaseHom_eq_inertiaEmbedding
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    CentralExtensionGroup.sylowNormalizerBaseHom
        (productAmbientGlaubermanLeftInertiaSylow
          S C hgenerate theta)
        (productAmbientGlaubermanRightInertiaEquivLeftSylowNormalizer
          S C hcentral hgenerate g theta) =
      productAmbientGlaubermanInertiaEmbedding
        S C hcentral hgenerate g theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  ext b
  rfl

/-- The underlying canonical left ambient factor-extension group. -/
abbrev ProductAmbientGlaubermanLeftFactorExtensionGroup
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let R :=
    productAmbientGlaubermanLeftAssociated
      S C hgenerate theta
  let F :=
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta).finiteFactorNormalization
  F.AmbientFactorCentralExtensionGroup R

/-- The underlying pulled-back target factor-extension group. -/
abbrev ProductAmbientGlaubermanTargetFactorExtensionGroup
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
  let R :=
    productAmbientGlaubermanLeftAssociated
      S C hgenerate theta
  let F :=
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta).finiteFactorNormalization
  let data :=
    productAmbientGlaubermanInertiaRestrictionGroupData
      S C hcentral hgenerate g theta
  LiftedFactorCorrespondence.TargetFactorCentralExtensionGroup
    R F data

/-- The target factor set is definitionally the Sylow-normalizer pullback of
the fixed left factor set through the concrete inertia equivalence. -/
theorem productAmbientGlaubermanTargetFactorSet_eq_sylowNormalizerFactorSet
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    let R :=
      productAmbientGlaubermanLeftAssociated
        S C hgenerate theta
    let F := R.finiteFactorNormalization
    let data :=
      productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta
    LiftedFactorCorrespondence.targetFactorSet R F data =
      CentralExtensionGroup.sylowNormalizerFactorSet
        F.factorSet
        (productAmbientGlaubermanLeftInertiaSylow
          S C hgenerate theta)
        (productAmbientGlaubermanRightInertiaEquivLeftSylowNormalizer
          S C hcentral hgenerate g theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  apply FactorSet.ext
  intro b c
  rfl

/-- The canonical central-extension structure on the left ambient
finite-factor extension. -/
def productAmbientGlaubermanLeftFactorCentralExtension
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    CentralExtension
      (ProductAmbientGlaubermanLeftFactorExtensionGroup
        S C hgenerate theta)
      (ProductAmbientGlaubermanLeftInertiaGroup
        S C hgenerate theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let R :=
    productAmbientGlaubermanLeftAssociated
      S C hgenerate theta
  let F :=
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta).finiteFactorNormalization
  exact
    CentralExtensionGroup.centralExtension
      F.factorSet (F.factorSet_isNormalized R)

/-- The Sylow lift of the induced left-inertia Sylow subgroup in the
canonical left ambient factor extension. -/
abbrev productAmbientGlaubermanLeftFactorExtensionSylow
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    Sylow q
      (ProductAmbientGlaubermanLeftFactorExtensionGroup
        S C hgenerate theta) :=
  (productAmbientGlaubermanLeftFactorCentralExtension
    S C hgenerate theta).sylowLift
      (productAmbientGlaubermanLeftInertiaSylow
        S C hgenerate theta)

/-- The pulled-back target factor extension is canonically the normalizer of
the Sylow lift in the left ambient factor extension. -/
def productAmbientGlaubermanTargetFactorExtensionEquivLeftSylowLiftNormalizer
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    ProductAmbientGlaubermanTargetFactorExtensionGroup
          S C hcentral hgenerate g theta ≃*
      Subgroup.normalizer
        (productAmbientGlaubermanLeftFactorExtensionSylow
          S C hgenerate theta :
          Set
            (ProductAmbientGlaubermanLeftFactorExtensionGroup
              S C hgenerate theta)) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let R :=
    productAmbientGlaubermanLeftAssociated
      S C hgenerate theta
  let F :=
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta).finiteFactorNormalization
  let data :=
    productAmbientGlaubermanInertiaRestrictionGroupData
      S C hcentral hgenerate g theta
  exact
    (CentralExtensionGroup.sylowLiftNormalizerEquivComap
      F.factorSet (F.factorSet_isNormalized R)
      (productAmbientGlaubermanLeftInertiaSylow
        S C hgenerate theta)
      (productAmbientGlaubermanRightInertiaEquivLeftSylowNormalizer
        S C hcentral hgenerate g theta)).symm

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
