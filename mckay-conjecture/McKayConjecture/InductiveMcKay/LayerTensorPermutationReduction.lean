/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.LayerReductionFactorization
import McKayConjecture.InductiveMcKay.LayerTensorPermutationCentralWitnessAssembly
import McKayConjecture.InductiveMcKay.MatchedCentralTripleCentralScalarAssembly
import McKayConjecture.InductiveMcKay.RossiCentralScalarReduction

/-!
# Tensor-permutation layer reduction

The ordinary group-theoretic conditions for the canonical layer inertia
embedding, in particular containment of the layer centralizer, are available
under `MinimalCounterexampleStructure`.  This file therefore states the
tensor-permutation construction obligation in exactly that context and shows
that it implies the numerical layer-reduction hypothesis.

Unlike `CanonicalLayerIntermediateCentralWitnessHypothesis`, the hypothesis
below does not ask for central witnesses for arbitrary finite groups where
the canonical centralizer containment is not known.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory
open LayerProjectiveRestrictionAssembly

/-- The remaining constructive layer obligation after replacing chart
coverage by orbitwise tensor-permutation cocycles. -/
def CanonicalMinimalLayerTensorPermutationAssemblyHypothesis
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G),
    MinimalCounterexampleStructure P →
      let d :=
        canonicalComponentOrbitLocalData covers P
      let hcoordinate :=
        ComponentOrbitLocalData.ofQuasisimpleHypothesis_isCoordinateCorrespondenceEquivariant
          (D := canonicalLayerSylowCoordinateData P)
          covers
      ∀ θ : PPrimeIrreducibleCharacter (layer G) p,
        Nonempty
          (LayerTensorPermutationCentralWitnessAssembly
            d hcoordinate θ)

/-- Tensor-permutation assemblies in a fixed minimal counterexample produce
the exact Clifford-reduction data. -/
def canonicalLayerIntermediateCliffordReductionData_of_tensorPermutation
    {p : ℕ} [Fact p.Prime]
    (assembly :
      CanonicalMinimalLayerTensorPermutationAssemblyHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G)
    (hminimal : MinimalCounterexampleStructure P) :
    LayerIntermediateCliffordReductionData
      (canonicalComponentOrbitLocalData covers P) := by
  let d :=
    canonicalComponentOrbitLocalData covers P
  let hcoordinate :=
    ComponentOrbitLocalData.ofQuasisimpleHypothesis_isCoordinateCorrespondenceEquivariant
      (D := canonicalLayerSylowCoordinateData P)
      covers
  apply
    LayerIntermediateCliffordReductionData.ofCoordinateEquivariance
      d hcoordinate
  intro θ
  let C :=
    Classical.choice
      (assembly covers G P hminimal θ)
  exact
    C.toCompleteCentralIsomorphismWitness_of_minimalCounterexample
      hminimal

/-- The complete witnesses produced by tensor-permutation assembly use the
canonical target-to-source inertia embeddings.  This is the exact coherence
needed to compare the same ambient central element through Clifford
assembly. -/
theorem canonicalLayerCliffordData_usesCanonicalInertiaEmbeddings
    {p : ℕ} [Fact p.Prime]
    (assembly :
      CanonicalMinimalLayerTensorPermutationAssemblyHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G)
    (hminimal : MinimalCounterexampleStructure P) :
    let r :=
      canonicalLayerIntermediateCliffordReductionData_of_tensorPermutation
        assembly covers G P hminimal
    r.toMatchedCentralTripleCliffordAssemblyData
      |>.UsesCanonicalInertiaEmbeddings := by
  dsimp only
  unfold
    MatchedCentralTripleCliffordAssemblyData.UsesCanonicalInertiaEmbeddings
  intro θ
  let d :=
    canonicalComponentOrbitLocalData covers P
  let hcoordinate :=
    ComponentOrbitLocalData.ofQuasisimpleHypothesis_isCoordinateCorrespondenceEquivariant
      (D := canonicalLayerSylowCoordinateData P)
      covers
  let C :=
    Classical.choice
      (assembly covers G P hminimal θ)
  let W :=
    C.toCompleteCentralIsomorphismWitness_of_minimalCounterexample
      hminimal
  letI := W.leftAddCommGroup
  letI := W.leftModule
  letI := W.leftModuleFinite
  letI := W.leftNontrivial
  letI := W.rightAddCommGroup
  letI := W.rightModule
  letI := W.rightModuleFinite
  letI := W.rightNontrivial
  apply MonoidHom.ext
  intro b
  apply Subtype.ext
  rfl

/-- Tensor-permutation layer assembly in a minimal counterexample produces
the central-scalar local correspondence required by the numerical
reduction. -/
def centralScalarLocalCorrespondence_of_tensorPermutation
    {p : ℕ} [Fact p.Prime]
    (assembly :
      CanonicalMinimalLayerTensorPermutationAssemblyHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G)
    (hminimal : MinimalCounterexampleStructure P) :
    CentralScalarLocalCorrespondence P := by
  let r :=
    canonicalLayerIntermediateCliffordReductionData_of_tensorPermutation
      assembly covers G P hminimal
  refine
    { toLocalCorrespondence :=
        r.toLocalCorrespondence hminimal
      correspondence_central_cross := ?_ }
  intro χ z hzcentral hzintermediate
  exact
    r.toMatchedCentralTripleCliffordAssemblyData
      |>.assembledPPrimeEquiv_central_cross
        (canonicalLayerCliffordData_usesCanonicalInertiaEmbeddings
          assembly covers G P hminimal)
        χ z hzcentral hzintermediate

/-- The sound tensor-permutation construction obligation implies the layer
half of the numerical Rossi reduction. -/
theorem layerReductionHypothesis_of_tensorPermutationAssembly
    {p : ℕ} [Fact p.Prime]
    (assembly :
      CanonicalMinimalLayerTensorPermutationAssemblyHypothesis p) :
    LayerReductionHypothesis p := by
  intro covers G _ _ P hminimal
  exact
    ⟨(canonicalLayerIntermediateCliffordReductionData_of_tensorPermutation
        assembly covers G P hminimal).toLocalCorrespondence
      hminimal⟩

/-- The sound tensor-permutation construction obligation implies the layer
half of the central-scalar Rossi reduction. -/
theorem centralScalarLayerReductionHypothesis_of_tensorPermutationAssembly
    {p : ℕ} [Fact p.Prime]
    (assembly :
      CanonicalMinimalLayerTensorPermutationAssemblyHypothesis p) :
    CentralScalarLayerReductionHypothesis p := by
  intro covers G _ _ P hminimal
  exact
    ⟨centralScalarLocalCorrespondence_of_tensorPermutation
      assembly covers G P hminimal⟩

end InductiveMcKay
end McKayConjecture
