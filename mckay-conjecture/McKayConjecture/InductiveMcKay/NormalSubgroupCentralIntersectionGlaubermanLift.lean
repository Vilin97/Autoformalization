/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionOkuyamaWajima
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45

/-!
# Proposition 4.5 above the Glauberman--Okuyama--Wajima correspondence

The proved Okuyama--Wajima construction for `CP` works through its canonical
normal `q′`-kernel.  Proposition 4.5 only depends on the resulting
character equivalence, not on which internal kernel produced it.  This file
therefore states the ambient Clifford lift for an arbitrary Theorem-4.4
equivalence and specializes it to the constructed Glauberman
correspondence.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CliffordCorrespondence
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The exact ambient numerical coherence over an arbitrary Theorem-4.4
character equivalence on `CP`. -/
structure ProductAmbientTheorem44Coherence
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q) where
  /-- The transported `CP` equivalence is equivariant under `N_X(S)`. -/
  characterEquiv_smul :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal
        S C hgenerate
    ∀ (h : ambientNormalizer S)
      (θ :
        PPrimeIrreducibleCharacter
          (product S C) q),
      internalTheorem44CharacterEquiv
          S C theorem44Equiv (h • θ) =
        h • internalTheorem44CharacterEquiv
          S C theorem44Equiv θ
  /-- Exactly matched ambient inertia fibres are equivalent. -/
  inertiaFibreEquiv :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal
        S C hgenerate
    ∀ θ :
        PPrimeIrreducibleCharacter
          (product S C) q,
      PPrimeIrreducibleCharactersOverInertia
          (product S C) θ.1 q ≃
        PPrimeIrreducibleCharactersOverInertia
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C theorem44Equiv θ).1 q

namespace ProductAmbientTheorem44Coherence

/-- Package the generic Proposition-4.5 coherence for matched numerical
Clifford assembly. -/
def toMatchedCentralFibreCliffordAssemblyData
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (d :
      ProductAmbientTheorem44Coherence
        S C hgenerate theorem44Equiv) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal
        S C hgenerate
    MatchedCentralFibreCliffordAssemblyData
      (product S C)
      (ambientNormalizer S)
      (internalProductNormalizer S C) q := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal
      S C hgenerate
  exact
    { sup_eq_top :=
        product_sup_normalizer_eq_top
          S C hgenerate
      characterEquiv :=
        internalTheorem44CharacterEquiv
          S C theorem44Equiv
      characterEquiv_smul :=
        d.characterEquiv_smul
      inertiaFibreEquiv :=
        d.inertiaFibreEquiv }

/-- The remaining representation-level condition over the generic
Theorem-4.4 equivalence. -/
def HasCentralActionIntertwiners
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (d :
      ProductAmbientTheorem44Coherence
        S C hgenerate theorem44Equiv) : Prop := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal
      S C hgenerate
  exact
    (d.toMatchedCentralFibreCliffordAssemblyData
      S C hgenerate theorem44Equiv).HasCentralActionIntertwiners

/-- The equivalent scalar-level formulation of the remaining ambient
coherence. -/
def PreservesCentralScalars
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (d :
      ProductAmbientTheorem44Coherence
        S C hgenerate theorem44Equiv) : Prop := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal
      S C hgenerate
  exact
    (d.toMatchedCentralFibreCliffordAssemblyData
      S C hgenerate theorem44Equiv).PreservesCentralScalars

/-- The operator and scalar versions of generic Proposition-4.5 central
coherence are equivalent. -/
theorem hasCentralActionIntertwiners_iff_preservesCentralScalars
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (d :
      ProductAmbientTheorem44Coherence
        S C hgenerate theorem44Equiv) :
    d.HasCentralActionIntertwiners
        S C hgenerate theorem44Equiv ↔
      d.PreservesCentralScalars
        S C hgenerate theorem44Equiv := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal
      S C hgenerate
  exact
    MatchedCentralFibreCliffordAssemblyData.hasCentralActionIntertwiners_iff_preservesCentralScalars
      (d.toMatchedCentralFibreCliffordAssemblyData
        S C hgenerate theorem44Equiv)

/-- Generic numerical Proposition 4.5: ambient coherence and central-action
intertwiners lift any Theorem-4.4 equivalence to the required
central-scalar local correspondence on `X`. -/
def toCentralScalarLocalCorrespondence
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (d :
      ProductAmbientTheorem44Coherence
        S C hgenerate theorem44Equiv)
    (haction :
      d.HasCentralActionIntertwiners
        S C hgenerate theorem44Equiv) :
    CentralScalarLocalCorrespondence S := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal
      S C hgenerate
  let a :=
    d.toMatchedCentralFibreCliffordAssemblyData
      S C hgenerate theorem44Equiv
  exact
    { toLocalCorrespondence :=
        { intermediate := ambientNormalizer S
          normalizer_le := le_rfl
          proper_of_normalizer_ne_top := fun hne =>
            lt_top_iff_ne_top.mpr hne
          correspondence := a.assembledPPrimeEquiv }
      correspondence_central_cross := by
        intro χ z hzcentral hzintermediate
        exact
          a.assembledPPrimeEquiv_central_cross_of_hasCentralActionIntertwiners
            haction χ z hzcentral hzintermediate }

end ProductAmbientTheorem44Coherence

open ComplementReduction

/-- The concrete Theorem-4.4 character equivalence supplied by the proved
Okuyama--Wajima fibres over a classical Glauberman correspondence. -/
def complementCharacterEquivOfGlauberman
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral) :
    PPrimeIrreducibleCharacter (product S C) q ≃
      PPrimeIrreducibleCharacter
        (Subgroup.normalizer
          (productSylow S C :
            Set (product S C))) q :=
  (complementCentralScalarLocalCorrespondenceOfGlauberman
    S C hcentral g).correspondence

/-- The exact remaining Proposition-4.5 data after the full numerical
Okuyama--Wajima construction has been discharged. -/
structure ProductAmbientGlaubermanLiftData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral) where
  ambientCoherence :
    ProductAmbientTheorem44Coherence
      S C hgenerate
      (complementCharacterEquivOfGlauberman
        S C hcentral g)
  centralActionIntertwiners :
    ambientCoherence.HasCentralActionIntertwiners
      S C hgenerate
      (complementCharacterEquivOfGlauberman
        S C hcentral g)

namespace ProductAmbientGlaubermanLiftData

/-- Construct the ambient Glauberman lift from the equivalent scalar-level
central coherence. -/
def of_preservesCentralScalars
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (ambientCoherence :
      ProductAmbientTheorem44Coherence
        S C hgenerate
        (complementCharacterEquivOfGlauberman
          S C hcentral g))
    (hscalar :
      ambientCoherence.PreservesCentralScalars
        S C hgenerate
        (complementCharacterEquivOfGlauberman
          S C hcentral g)) :
    ProductAmbientGlaubermanLiftData
      S C hcentral hgenerate g where
  ambientCoherence := ambientCoherence
  centralActionIntertwiners :=
    (ProductAmbientTheorem44Coherence.hasCentralActionIntertwiners_iff_preservesCentralScalars
      S C hgenerate
      (complementCharacterEquivOfGlauberman
        S C hcentral g)
      ambientCoherence).mpr hscalar

/-- The Glauberman and ambient Proposition-4.5 data construct the
central-scalar local correspondence for the original ambient group. -/
def toCentralScalarLocalCorrespondence
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (d :
      ProductAmbientGlaubermanLiftData
        S C hcentral hgenerate g) :
    CentralScalarLocalCorrespondence S :=
  d.ambientCoherence.toCentralScalarLocalCorrespondence
    S C hgenerate
    (complementCharacterEquivOfGlauberman
      S C hcentral g)
    d.centralActionIntertwiners

end ProductAmbientGlaubermanLiftData
end Proposition45

/-- The remaining central-intersection input after Okuyama--Wajima has
been reduced to Glauberman and the exact ambient Proposition-4.5 lift. -/
def CentralScalarCentralIntersectionGlaubermanLiftHypothesis
    (q : ℕ) [Fact q.Prime] : Prop :=
  ∀ (X : Type) [Group X] [Finite X]
    (S : Sylow q X) (C : Subgroup X)
    (hCnormal : C.Normal)
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤),
      letI : C.Normal := hCnormal
      ∃ g :
          ComplementReduction.ProductGlaubermanCorrespondence
            S C hcentral,
        Nonempty
          (Proposition45.ProductAmbientGlaubermanLiftData
            S C hcentral hgenerate g)

/-- The Glauberman/Proposition-4.5 input discharges the shared
central-intersection reduction hypothesis. -/
theorem centralScalarCentralIntersectionReductionHypothesis_of_glaubermanLift
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionGlaubermanLiftHypothesis q) :
    CentralScalarCentralIntersectionReductionHypothesis q := by
  intro X _ _ S C hCnormal hcentral _hCnoncentral hgenerate
  letI : C.Normal := hCnormal
  obtain ⟨g, ⟨d⟩⟩ :=
    h X S C hCnormal hcentral hgenerate
  exact
    ⟨d.toCentralScalarLocalCorrespondence
      S C hcentral hgenerate g⟩

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
