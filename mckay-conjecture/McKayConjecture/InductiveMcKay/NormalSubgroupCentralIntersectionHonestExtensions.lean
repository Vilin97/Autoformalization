/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.HonestExtensionCentralWitness
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionAmbientProjectiveComparison

/-!
# The factor-one case of the ambient Theorem 4.4 comparison

The ambient central-intersection reduction asks for projective comparison
data on the matched inertia triples of characters of `CP` and
`N_{CP}(P)`.  This file records the honest-extension special case.

If both canonical inertia-copy characters have honest irreducible
extensions, their associated projective representations have factor one.
The group conditions are the automatic conditions already proved for the
canonical ambient inertia embedding.  Consequently the only remaining
comparison law is equality of normalized character values on the source
centralizer; the generic Schur-scalar constructor converts that identity
to projective scalar agreement.

This does not assert that the required honest extensions always exist.
In the general Dade--Glauberman--Nagao theorem nontrivial projective factor
sets are essential.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CliffordEquivalence
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- Construct the ambient Theorem-4.4 projective comparison in the special
case where both matched inertia-copy characters have honest extensions.

Both projective factor sets are then one.  The cross-multiplied character
identity is exactly the remaining scalar condition, at the correct source
centralizer rather than merely at the ambient center. -/
def productAmbientTheorem44ProjectiveComparisonDataOfInertiaExtensions
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
        internalProductNormalizer_normal
          S C hgenerate
      ∀ (h : ambientNormalizer S)
        (theta :
          PPrimeIrreducibleCharacter
            (product S C) q),
        internalTheorem44CharacterEquiv
            S C theorem44Equiv (h • theta) =
          h • internalTheorem44CharacterEquiv
            S C theorem44Equiv theta)
    (sourceExtension :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      ∀ theta :
          PPrimeIrreducibleCharacter
            (product S C) q,
        IrreducibleCharacter
          (IrreducibleCharacter.inertia
            (product S C) theta.1))
    (targetExtension :
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal
          S C hgenerate
      ∀ theta :
          PPrimeIrreducibleCharacter
            (product S C) q,
        IrreducibleCharacter
          (IrreducibleCharacter.inertia
            (internalProductNormalizer S C)
            (internalTheorem44CharacterEquiv
              S C theorem44Equiv theta).1))
    (source_isExtension :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      ∀ theta :
          PPrimeIrreducibleCharacter
            (product S C) q,
        IrreducibleCharacter.IsExtensionAlong
          (inertiaNormalCopy
            (product S C) theta.1).subtype
          (inertiaCopyCharacter
            (product S C) theta.1)
          (sourceExtension theta))
    (target_isExtension :
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal
          S C hgenerate
      ∀ theta :
          PPrimeIrreducibleCharacter
            (product S C) q,
        IrreducibleCharacter.IsExtensionAlong
          (inertiaNormalCopy
            (internalProductNormalizer S C)
            (internalTheorem44CharacterEquiv
              S C theorem44Equiv theta).1).subtype
          (inertiaCopyCharacter
            (internalProductNormalizer S C)
            (internalTheorem44CharacterEquiv
              S C theorem44Equiv theta).1)
          (targetExtension theta))
    (centralizer_cross :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal
          S C hgenerate
      ∀ (theta :
          PPrimeIrreducibleCharacter
            (product S C) q)
        (b :
          IrreducibleCharacter.inertia
            (internalProductNormalizer S C)
            (internalTheorem44CharacterEquiv
              S C theorem44Equiv theta).1),
        let e :=
          MatchedInertiaRestriction.embedding
            (product S C)
            (ambientNormalizer S)
            (internalProductNormalizer S C)
            (internalTheorem44CharacterEquiv
              S C theorem44Equiv)
            characterEquiv_smul theta
        e b ∈
            Subgroup.centralizer
              (inertiaNormalCopy
                (product S C) theta.1 :
                Set
                  (IrreducibleCharacter.inertia
                    (product S C) theta.1)) →
          (sourceExtension theta).values (e b) *
              ((targetExtension theta).degree : ℂ) =
            (targetExtension theta).values b *
              ((sourceExtension theta).degree : ℂ)) :
    ProductAmbientTheorem44ProjectiveComparisonData
      S C hgenerate theorem44Equiv := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal
      S C hgenerate
  refine
    { characterEquiv_smul := characterEquiv_smul
      projectiveComparison := ?_ }
  intro theta
  let phi :=
    internalTheorem44CharacterEquiv
      S C theorem44Equiv theta
  let e :=
    MatchedInertiaRestriction.embedding
      (product S C)
      (ambientNormalizer S)
      (internalProductNormalizer S C)
      (internalTheorem44CharacterEquiv
        S C theorem44Equiv)
      characterEquiv_smul theta
  let groupData :=
    productAmbientInertiaRestrictionGroupData
      S C hgenerate theorem44Equiv
      characterEquiv_smul theta
  let complete :=
    completeCentralIsomorphismWitnessOfInertiaExtensions
      (product S C)
      (internalProductNormalizer S C)
      theta.1 phi.1
      (sourceExtension theta)
      (targetExtension theta)
      (source_isExtension theta)
      (target_isExtension theta)
      e groupData
      (centralizer_cross theta)
  have hembedding :
      complete.embedding = e := by
    rfl
  change
    CompleteCentralProjectiveComparisonData
      (ofInertia (product S C) theta.1)
      (ofInertia
        (internalProductNormalizer S C)
        (internalTheorem44CharacterEquiv
          S C theorem44Equiv theta).1)
      e
  rw [← hembedding]
  exact
    complete.toCompleteCentralProjectiveComparisonData

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
