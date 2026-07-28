/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.ComponentOrbitCorrespondenceTransport
import McKayConjecture.InductiveMcKay.LayerIntermediateCorrespondenceEquivariance
import McKayConjecture.InductiveMcKay.RossiNumericalReduction

/-!
# Factorization of the layer reduction

The quasisimple inductive-McKay hypothesis canonically supplies coherent
local data on the component orbits of the layer.  The remaining passage from
those component data to a local correspondence for the ambient group first
requires equivariance and then matched inertia-triple witnesses.

Orbit-coherent transport proves the exact coordinate naturality law.
Generation by the component-local subgroup and the ambient layer-Sylow
normalizer then proves full layer-intermediate equivariance.  Thus only the
complete matched central-isomorphism witnesses remain as a hypothesis in
this file; the projective/permutation assembly still to be proved is visible
without retaining a redundant equivariance assumption.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple
open GroupTheory

/-- The canonical coordinate lift of the Sylow subgroup obtained by
intersecting an ambient Sylow subgroup with the layer. -/
abbrev canonicalLayerSylowCoordinateData
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) :
    LayerSylowCoordinateData G p
      (layerSylowIntersection P) :=
  layerSylowCoordinateData G p
    (layerSylowIntersection P)

/-- Coherent component-orbit local data canonically chosen from a
quasisimple inductive-McKay hypothesis. -/
abbrev canonicalComponentOrbitLocalData
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (covers : QuasisimpleInductiveMcKayHypothesis.{0} p)
    (P : Sylow p G) :
    ComponentOrbitLocalData
      (canonicalLayerSylowCoordinateData P) :=
  ComponentOrbitLocalData.ofQuasisimpleHypothesis
    covers

/-- Full layer-intermediate equivariance of the canonical componentwise
character correspondence. -/
def CanonicalLayerIntermediateEquivarianceHypothesis
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G),
    let d :=
      canonicalComponentOrbitLocalData covers P
    ∀ (h : d.ambientIntermediate)
      (θ : PPrimeIrreducibleCharacter
        (layer G) p),
      d.intermediateComponentLocalPPrimeCharacterEquiv
          (h • θ) =
        h •
          d.intermediateComponentLocalPPrimeCharacterEquiv
            θ

/-- The canonical component-orbit construction satisfies full
layer-intermediate equivariance. -/
theorem canonicalLayerIntermediateEquivariance
    {p : ℕ} [Fact p.Prime] :
    CanonicalLayerIntermediateEquivarianceHypothesis p := by
  intro covers G _ _ P
  let d :=
    canonicalComponentOrbitLocalData covers P
  exact
    d.intermediateComponentLocalPPrimeCharacterEquiv_map_smul
      (ComponentOrbitLocalData.ofQuasisimpleHypothesis_isCoordinateCorrespondenceEquivariant
        (D := canonicalLayerSylowCoordinateData P)
        covers)

/-- Complete central-triple compatibility for every exactly matched pair
produced by the canonical componentwise correspondence. -/
def CanonicalLayerIntermediateCentralWitnessHypothesis
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G),
    let d :=
      canonicalComponentOrbitLocalData covers P
    ∀ θ : PPrimeIrreducibleCharacter
        (layer G) p,
      Nonempty
        (CompleteCentralIsomorphismWitness
          (ofInertia (layer G) θ.1)
          (ofInertia
            d.intermediateComponentLocal
            (d.intermediateComponentLocalPPrimeCharacterEquiv
              θ).1))

/-- The two canonical layer assertions assemble into the exact Clifford
reduction datum. -/
def canonicalLayerIntermediateCliffordReductionData
    {p : ℕ} [Fact p.Prime]
    (centralWitness :
      CanonicalLayerIntermediateCentralWitnessHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    LayerIntermediateCliffordReductionData
      (canonicalComponentOrbitLocalData covers P) :=
  LayerIntermediateCliffordReductionData.ofCoordinateEquivariance
    (canonicalComponentOrbitLocalData covers P)
    (ComponentOrbitLocalData.ofQuasisimpleHypothesis_isCoordinateCorrespondenceEquivariant
      (D := canonicalLayerSylowCoordinateData P)
      covers)
    (fun θ ↦
      Classical.choice
        (centralWitness covers G P θ))

/-- Complete matched central witnesses for the canonical layer construction
imply the layer half of the numerical Rossi reduction.  Equivariance is now
a theorem of the coherent component construction. -/
theorem layerReductionHypothesis_of_canonicalLayerCentralWitness
    {p : ℕ} [Fact p.Prime]
    (centralWitness :
      CanonicalLayerIntermediateCentralWitnessHypothesis p) :
    LayerReductionHypothesis p := by
  intro covers G _ _ P hminimal
  exact
    ⟨(canonicalLayerIntermediateCliffordReductionData
        centralWitness covers G P).toLocalCorrespondence
      hminimal⟩

end InductiveMcKay
end McKayConjecture
