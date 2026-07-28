/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.MatchedCentralTripleFibreCoherence
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanLift

/-!
# Ambient Proposition 4.5 data from central inertia triples

The standard character-theoretic conclusion of Theorem 4.4 is not merely a
cardinality equality on `CP`: it is an equivariant character equivalence
whose matched ambient inertia triples are centrally isomorphic.  This file
proves that this standard central-triple conclusion constructs all the
numerical ambient data isolated in the Proposition-4.5 interface.

The only element-level coherence required is the usual one: the embedding
of a matched central-triple witness is the canonical inclusion of the
target inertia group into the source inertia group.  From that equality,
the central-triple scalar theorem supplies the central-action intertwiners
automatically.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CliffordCorrespondence
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

namespace Theorem44CharacterDataConsequences

/-- Regard exact Theorem-4.4 character data as matched central-triple
Clifford-assembly data in the ambient group. -/
def toMatchedCentralTripleCliffordAssemblyData
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (d :
      Theorem44CharacterData S C hgenerate) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    MatchedCentralTripleCliffordAssemblyData
      (product S C)
      (ambientNormalizer S)
      (internalProductNormalizer S C) q := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    { sup_eq_top :=
        product_sup_normalizer_eq_top S C hgenerate
      characterEquiv :=
        internalTheorem44CharacterEquiv
          S C d.characterEquiv
      characterEquiv_smul :=
        d.characterEquiv_smul
      centralWitness :=
        d.centralWitness }

/-- Canonical-embedding coherence for the complete central inertia triples
stored by exact Theorem-4.4 data. -/
def UsesCanonicalInertiaEmbeddings
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (d :
      Theorem44CharacterData S C hgenerate) : Prop := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    (toMatchedCentralTripleCliffordAssemblyData
      S C hgenerate d).UsesCanonicalInertiaEmbeddings

/-- The complete central inertia triples in Theorem-4.4 data construct the
generic numerical ambient coherence package. -/
def toProductAmbientTheorem44Coherence
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (d :
      Theorem44CharacterData S C hgenerate) :
    ProductAmbientTheorem44Coherence
      S C hgenerate d.characterEquiv := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let t :=
    toMatchedCentralTripleCliffordAssemblyData
      S C hgenerate d
  let f :=
    t.toMatchedCentralFibreCliffordAssemblyData
  exact
    { characterEquiv_smul :=
        d.characterEquiv_smul
      inertiaFibreEquiv :=
        f.inertiaFibreEquiv }

/-- The numerical assembly data obtained through the ambient-coherence
wrapper is definitionally the data obtained by forgetting the central
triple witnesses. -/
theorem toProductAmbientTheorem44Coherence_toMatchedCentralFibre_eq
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (d :
      Theorem44CharacterData S C hgenerate) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (toProductAmbientTheorem44Coherence
        S C hgenerate d).toMatchedCentralFibreCliffordAssemblyData
          S C hgenerate d.characterEquiv =
      (toMatchedCentralTripleCliffordAssemblyData
        S C hgenerate d).toMatchedCentralFibreCliffordAssemblyData := by
  rfl

/-- Canonically embedded central inertia triples supply all of the
central-action intertwiners required by the generic ambient lift. -/
theorem hasCentralActionIntertwiners
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (d :
      Theorem44CharacterData S C hgenerate)
    (hcanonical :
      UsesCanonicalInertiaEmbeddings
        S C hgenerate d) :
    (toProductAmbientTheorem44Coherence
      S C hgenerate d).HasCentralActionIntertwiners
        S C hgenerate d.characterEquiv := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  change
    ((toProductAmbientTheorem44Coherence
        S C hgenerate d).toMatchedCentralFibreCliffordAssemblyData
      S C hgenerate d.characterEquiv).HasCentralActionIntertwiners
  rw [toProductAmbientTheorem44Coherence_toMatchedCentralFibre_eq
      S C hgenerate d]
  exact
    (toMatchedCentralTripleCliffordAssemblyData
      S C hgenerate d)
      |>.toMatchedCentralFibreCliffordAssemblyData_hasCentralActionIntertwiners
        hcanonical

end Theorem44CharacterDataConsequences

/-- Build exact Theorem-4.4 character data from its three standard
components.  This helper lets the canonical-embedding condition below refer
to one fixed matched central-triple assembly. -/
def theorem44CharacterDataOfComponents
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
    (centralWitness :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      ∀ θ :
          PPrimeIrreducibleCharacter
            (product S C) q,
        CompleteCentralIsomorphismWitness
          (ofInertia (product S C) θ.1)
          (ofInertia
            (internalProductNormalizer S C)
            (internalTheorem44CharacterEquiv
              S C theorem44Equiv θ).1)) :
    Theorem44CharacterData S C hgenerate where
  characterEquiv := theorem44Equiv
  characterEquiv_smul := characterEquiv_smul
  centralWitness := centralWitness

/-- Generic ambient lift data at the standard central-triple strength of
Theorem 4.4. -/
structure ProductAmbientTheorem44CentralTripleLiftData
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q) where
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
  centralWitness :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ∀ θ :
        PPrimeIrreducibleCharacter
          (product S C) q,
      CompleteCentralIsomorphismWitness
        (ofInertia (product S C) θ.1)
        (ofInertia
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C theorem44Equiv θ).1)
  usesCanonicalInertiaEmbeddings :
    Theorem44CharacterDataConsequences.UsesCanonicalInertiaEmbeddings
      S C hgenerate
      (theorem44CharacterDataOfComponents
        S C hgenerate theorem44Equiv
        characterEquiv_smul centralWitness)

/-- The generic numerical output constructed from standard Theorem-4.4
central-triple data. -/
structure ProductAmbientTheorem44LiftData
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q) where
  ambientCoherence :
    ProductAmbientTheorem44Coherence
      S C hgenerate theorem44Equiv
  centralActionIntertwiners :
    ambientCoherence.HasCentralActionIntertwiners
      S C hgenerate theorem44Equiv

namespace ProductAmbientTheorem44CentralTripleLiftData

/-- Exact Theorem-4.4 central-triple data constructs the numerical ambient
coherence and central-action intertwiners. -/
def toAmbientLiftData
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (d :
      ProductAmbientTheorem44CentralTripleLiftData
        S C hgenerate theorem44Equiv) :
    ProductAmbientTheorem44LiftData
      S C hgenerate theorem44Equiv := by
  let theorem44Data :=
    theorem44CharacterDataOfComponents
      S C hgenerate theorem44Equiv
      d.characterEquiv_smul d.centralWitness
  refine
    { ambientCoherence :=
        Theorem44CharacterDataConsequences.toProductAmbientTheorem44Coherence
          S C hgenerate theorem44Data
      centralActionIntertwiners := ?_ }
  exact
    Theorem44CharacterDataConsequences.hasCentralActionIntertwiners
      S C hgenerate theorem44Data
      d.usesCanonicalInertiaEmbeddings

end ProductAmbientTheorem44CentralTripleLiftData

open ComplementReduction

/-- The precise standard central-triple input remaining above the
constructed Glauberman--Okuyama--Wajima character equivalence. -/
abbrev ProductAmbientGlaubermanCentralTripleLiftData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral) :=
  ProductAmbientTheorem44CentralTripleLiftData
    S C hgenerate
    (complementCharacterEquivOfGlauberman
      S C hcentral g)

namespace ProductAmbientGlaubermanCentralTripleLiftData

/-- The standard equivariant central-triple form of Theorem 4.4
constructs the previously isolated `ProductAmbientGlaubermanLiftData`. -/
def toProductAmbientGlaubermanLiftData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (d :
      ProductAmbientGlaubermanCentralTripleLiftData
        S C hcentral hgenerate g) :
    ProductAmbientGlaubermanLiftData
      S C hcentral hgenerate g := by
  let lift :=
    d.toAmbientLiftData
      S C hgenerate
      (complementCharacterEquivOfGlauberman
        S C hcentral g)
  exact
    { ambientCoherence := lift.ambientCoherence
      centralActionIntertwiners :=
        lift.centralActionIntertwiners }

end ProductAmbientGlaubermanCentralTripleLiftData

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
