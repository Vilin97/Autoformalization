/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveComparison
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionAmbientCentralTriples

/-!
# Projective comparison input for the ambient central-intersection step

For `N = CP`, `H = N_X(P)`, and `M = N ∩ H`, the ordinary group conditions
in every matched inertia central isomorphism are automatic.  This file proves
those conditions once and reduces the remaining Theorem-4.4 input to:

* equivariance of the character equivalence under `H`; and
* independent associated projective representations on each matched pair of
  inertia triples, with equal factor sets and equal centralizer scalars.

In particular, no degree-preserving literal restriction is assumed.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction

open CharacterTriple
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

omit [Finite X] [Fact q.Prime] [C.Normal] in
/-- The centralizer of `CP` lies in the ambient Sylow normalizer. -/
theorem centralizer_product_le_ambientNormalizer :
    Subgroup.centralizer
        (product S C : Set X) ≤
      ambientNormalizer S :=
  (Subgroup.centralizer_le
      (show
        (S : Set X) ⊆
          (product S C : Set X) from
        fun _ hx ↦
          (show
            (S : Subgroup X) ≤ product S C from
            le_sup_right) hx)).trans
    (Subgroup.centralizer_le_normalizer
      (S : Set X))

omit [Finite X] [Fact q.Prime] [C.Normal] in
/-- The internal target subgroup is exactly `CP ∩ N_X(P)` after mapping it
back to `X`. -/
theorem product_inf_ambientNormalizer_eq_internalProductNormalizer_map :
    product S C ⊓ ambientNormalizer S =
      (internalProductNormalizer S C).map
        (ambientNormalizer S).subtype := by
  rw [Subgroup.subgroupOf_map_subtype, inf_comm]

omit [Fact q.Prime] in
/-- All ordinary group conditions for the canonical inclusion between a
matched pair of ambient inertia triples. -/
theorem productAmbientInertiaRestrictionGroupData
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
        (θ :
          PPrimeIrreducibleCharacter
            (product S C) q),
        internalTheorem44CharacterEquiv
            S C theorem44Equiv (h • θ) =
          h • internalTheorem44CharacterEquiv
            S C theorem44Equiv θ)
    (θ :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    CentralRestrictionGroupData
      (ofInertia (product S C) θ.1)
      (ofInertia
        (internalProductNormalizer S C)
        (internalTheorem44CharacterEquiv
          S C theorem44Equiv θ).1)
      (MatchedInertiaRestriction.embedding
        (product S C)
        (ambientNormalizer S)
        (internalProductNormalizer S C)
        (internalTheorem44CharacterEquiv
          S C theorem44Equiv)
        characterEquiv_smul θ) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    MatchedInertiaRestriction.centralRestrictionGroupData
      (product S C)
      (ambientNormalizer S)
      (internalProductNormalizer S C)
      (internalTheorem44CharacterEquiv
        S C theorem44Equiv)
      characterEquiv_smul
      (product_sup_normalizer_eq_top
        S C hgenerate)
      (centralizer_product_le_ambientNormalizer S C)
      (product_inf_ambientNormalizer_eq_internalProductNormalizer_map
        S C)
      θ

namespace Proposition45

/-- The exact projective-representation content remaining in the ambient
central-triple form of Theorem 4.4.

All injectivity, centralizer, product, and intersection conditions of the
central witnesses are theorems in this file. -/
structure ProductAmbientTheorem44ProjectiveComparisonData
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q) where
  /-- Equivariance of the chosen Theorem-4.4 equivalence. -/
  characterEquiv_smul :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ∀ (h : ambientNormalizer S)
      (θ :
        PPrimeIrreducibleCharacter
          (product S C) q),
      internalTheorem44CharacterEquiv
          S C theorem44Equiv (h • θ) =
        h • internalTheorem44CharacterEquiv
          S C theorem44Equiv θ
  /-- Associated projective representations with the two exact comparison
  laws from a central character-triple isomorphism. -/
  projectiveComparison :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ∀ θ :
        PPrimeIrreducibleCharacter
          (product S C) q,
      CompleteCentralProjectiveComparisonData
        (ofInertia (product S C) θ.1)
        (ofInertia
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C theorem44Equiv θ).1)
        (MatchedInertiaRestriction.embedding
          (product S C)
          (ambientNormalizer S)
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C theorem44Equiv)
          characterEquiv_smul θ)

namespace ProductAmbientTheorem44ProjectiveComparisonData

/-- Projective comparison data, together with the automatic product group
conditions, gives the standard central-triple input used by the numerical
ambient lift. -/
def toCentralTripleLiftData
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (d :
      ProductAmbientTheorem44ProjectiveComparisonData
        S C hgenerate theorem44Equiv) :
    ProductAmbientTheorem44CentralTripleLiftData
      S C hgenerate theorem44Equiv := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let centralWitness :=
    fun θ ↦
      (d.projectiveComparison θ).toCompleteCentralIsomorphismWitness
        (productAmbientInertiaRestrictionGroupData
          S C hgenerate theorem44Equiv
          d.characterEquiv_smul θ)
  refine
    { characterEquiv_smul :=
        d.characterEquiv_smul
      centralWitness := centralWitness
      usesCanonicalInertiaEmbeddings := ?_ }
  unfold
    Theorem44CharacterDataConsequences.UsesCanonicalInertiaEmbeddings
    MatchedCentralTripleCliffordAssemblyData.UsesCanonicalInertiaEmbeddings
  intro θ
  dsimp only
    [Theorem44CharacterDataConsequences.toMatchedCentralTripleCliffordAssemblyData,
      theorem44CharacterDataOfComponents, centralWitness]
  exact
    CompleteCentralProjectiveComparisonData.toCompleteCentralIsomorphismWitness_embedding
      (d.projectiveComparison θ)
      (productAmbientInertiaRestrictionGroupData
        S C hgenerate theorem44Equiv
        d.characterEquiv_smul θ)

end ProductAmbientTheorem44ProjectiveComparisonData

open ComplementReduction

/-- The remaining projective comparison data for the explicitly constructed
Glauberman--Okuyama--Wajima equivalence. -/
abbrev ProductAmbientGlaubermanProjectiveComparisonData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral) :=
  ProductAmbientTheorem44ProjectiveComparisonData
    S C hgenerate
    (complementCharacterEquivOfGlauberman
      S C hcentral g)

namespace ProductAmbientGlaubermanProjectiveComparisonData

/-- The projective comparison form of Theorem 4.4 constructs all ambient
lift data required in Proposition 4.5. -/
def toProductAmbientGlaubermanLiftData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (d :
      ProductAmbientGlaubermanProjectiveComparisonData
        S C hcentral hgenerate g) :
    ProductAmbientGlaubermanLiftData
      S C hcentral hgenerate g :=
  ProductAmbientGlaubermanCentralTripleLiftData.toProductAmbientGlaubermanLiftData
      S C hcentral hgenerate g
      (d.toCentralTripleLiftData
        S C hgenerate
        (complementCharacterEquivOfGlauberman
          S C hcentral g))

end ProductAmbientGlaubermanProjectiveComparisonData

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
