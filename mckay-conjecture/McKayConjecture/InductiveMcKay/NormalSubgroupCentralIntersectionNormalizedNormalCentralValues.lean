/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizerAssemblyNaturality
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProjectiveCenterMismatch

/-!
# Normal-central values in the ambient central-intersection comparison

For the canonical inertia embedding in Proposition 4.5, every matched
normal-central element comes from the center of `CS`.  Consequently the
normalized Okuyama--Wajima center identity is exactly the generic
`NormalizedNormalCentralValuesAgree` condition; it is not an additional
hypothesis.
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

/-- Every matched normal-central element in the canonical ambient inertia
comparison is represented by a unique element of `Z(CS)`. -/
theorem productAmbientCenterComparisonHom_surjective
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (characterEquiv_smul :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      ∀ (h : ambientNormalizer S)
        (theta :
          PPrimeIrreducibleCharacter
            (product S C) q),
        internalTheorem44CharacterEquiv
            S C theorem44Equiv (h • theta) =
          h • internalTheorem44CharacterEquiv
            S C theorem44Equiv theta)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    Function.Surjective
      (productAmbientCenterComparisonHom
        S C hgenerate theorem44Equiv
        characterEquiv_smul theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  intro b
  let phi :=
    internalTheorem44CharacterEquiv
      S C theorem44Equiv theta
  let embedding :=
    MatchedInertiaRestriction.embedding
      (product S C)
      (ambientNormalizer S)
      (internalProductNormalizer S C)
      (internalTheorem44CharacterEquiv
        S C theorem44Equiv)
      characterEquiv_smul theta
  have hbInternal :
      (((b.1.1 :
          IrreducibleCharacter.inertia
            (internalProductNormalizer S C) phi.1) :
          ambientNormalizer S)) ∈
        internalProductNormalizer S C := by
    exact b.2
  let zProduct : product S C :=
    ⟨((((b.1.1 :
          IrreducibleCharacter.inertia
            (internalProductNormalizer S C) phi.1) :
          ambientNormalizer S)) : X),
      hbInternal⟩
  have hzCenter :
      zProduct ∈ Subgroup.center (product S C) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    let yInertia :
        IrreducibleCharacter.inertia
          (product S C) theta.1 :=
      IrreducibleCharacter.inertiaInclusion
        (product S C) theta.1 y
    let yCopy :
        inertiaNormalCopy (product S C) theta.1 :=
      ⟨yInertia, y.2⟩
    have hcomm :=
      (Subgroup.mem_centralizer_iff.mp b.1.2)
        (yCopy :
          IrreducibleCharacter.inertia
            (product S C) theta.1)
        yCopy.property
    exact
      congrArg
        (fun a :
          IrreducibleCharacter.inertia
            (product S C) theta.1 ↦ (a : X))
        hcomm
  let z : Subgroup.center (product S C) :=
    ⟨zProduct, hzCenter⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The normalized Okuyama--Wajima center identity supplies normalized
value agreement on the entire matched normal-central subgroup. -/
theorem productAmbientGlauberman_normalizedNormalCentralValuesAgree
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
    (productAmbientInertiaRestrictionGroupData
      S C hgenerate
      (complementCharacterEquivOfGlauberman
        S C hcentral g)
      (complementCharacterEquivOfGlauberman_internal_smul
        S C hcentral hgenerate g)
      theta).NormalizedNormalCentralValuesAgree := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  intro b
  obtain ⟨z, rfl⟩ :=
    productAmbientCenterComparisonHom_surjective
      S C hgenerate
      (complementCharacterEquivOfGlauberman
        S C hcentral g)
      (complementCharacterEquivOfGlauberman_internal_smul
        S C hcentral hgenerate g)
      theta b
  exact
    productAmbientCenterComparisonElement_normalizedValues
      S C hcentral hgenerate g
      (complementCharacterEquivOfGlauberman_internal_smul
        S C hcentral hgenerate g)
      theta z

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
